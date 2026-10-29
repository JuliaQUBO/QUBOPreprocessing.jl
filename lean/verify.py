#!/usr/bin/env python3
"""Snapshot-build every project module and audit compiler-enumerated declarations.

Dependencies are imported from the pinned local cache, never rebuilt or updated.
Only this project's captured sources are compiled, into an isolated directory.
The Lean helper is verification infrastructure; its IO importer is not a proof.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXCLUDED_DIRS = {".lake", ".git", "verification", "test", "__pycache__"}
BANNED_WORDS = {
    "sorry", "admit", "sorryAx", "native_decide", "ofReduceBool", "skipKernelTC",
    "axiom", "unsafe", "partial", "opaque", "extern", "implemented_by", "unsafeCast",
}
# Native evaluation itself is not a proof certificate. Ordinary `decide +kernel` is allowed.
BANNED_REFERENCES = {"sorryAx", "ofReduceBool", "ofReduceNat", "ofReduceInt"}


class VerificationError(RuntimeError):
    pass


def atomic_json(path: Path, value: object) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
    temporary.replace(path)


def proof_files(root: Path) -> list[Path]:
    """All Lean library sources, regardless of directory or declaration namespace."""
    return sorted(p for p in root.rglob("*.lean")
                  if not any(part in EXCLUDED_DIRS or part.startswith(".")
                             for part in p.relative_to(root).parts[:-1]))


def evidence_files(root: Path) -> list[Path]:
    files = set(proof_files(root))
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "verify.py", "verify.sh"):
        files.add(root / name)
    files.update(p for p in (root / "test").rglob("*")
                 if p.is_file() and p.suffix in {".lean", ".py"} and "__pycache__" not in p.parts)
    return sorted(files)


@dataclass(frozen=True)
class FileState:
    digest: str
    stat: tuple[int, ...]
    data: bytes


def read_stable(path: Path) -> FileState:
    before = path.stat()
    data = path.read_bytes()
    after = path.stat()
    def signature(st):
        return (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)
    if signature(before) != signature(after):
        raise VerificationError(f"Source changed while reading: {path}")
    return FileState(hashlib.sha256(data).hexdigest(), signature(after), data)


def snapshot(root: Path) -> dict[str, FileState]:
    return {str(p.relative_to(root)): read_stable(p) for p in evidence_files(root)}


def assert_unchanged(root: Path, initial: dict[str, FileState]) -> None:
    current = snapshot(root)
    changed = set(initial) ^ set(current)
    changed.update(p for p in initial.keys() & current.keys()
                   if initial[p].digest != current[p].digest or initial[p].stat != current[p].stat)
    if changed:
        raise VerificationError("Concurrent source change detected; verification rejected: "
                                + ", ".join(sorted(changed)))


def lean_tokens(source: str) -> list[str]:
    """Lex code tokens, ignoring nested comments and strings, preserving quoted names.

    This is only the additional source-policy check, never declaration enumeration
    or import parsing. Those use Lean's compiled environment and header parser.
    """
    tokens = []
    i, length = 0, len(source)
    while i < length:
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = length if end == -1 else end + 1
        elif source.startswith("/-", i):
            depth, i = 1, i + 2
            while i < length and depth:
                if source.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise VerificationError("Unterminated Lean comment")
        elif source[i] == '"':
            i += 1
            while i < length:
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise VerificationError("Unterminated Lean string")
        elif source[i] == "«":
            end = source.find("»", i + 1)
            if end == -1:
                raise VerificationError("Unterminated quoted Lean identifier")
            tokens.append(source[i + 1:end])
            i = end + 1
        elif source[i].isalpha() or source[i] == "_":
            start = i
            i += 1
            while i < length and (source[i].isalnum() or source[i] in "_'′"):
                i += 1
            tokens.append(source[start:i])
        else:
            if not source[i].isspace():
                tokens.append(source[i])
            i += 1
    return tokens


def check_source_policy(source: str, path: str = "<source>") -> None:
    tokens = lean_tokens(source)
    disallowed = set(tokens) & BANNED_WORDS
    native_decision = any(tokens[i:i + 3] == ["decide", "+", "native"]
                          for i in range(max(0, len(tokens) - 2)))
    if disallowed or native_decision:
        raise VerificationError(f"Disallowed proof shortcut in {path}: "
                                + ", ".join(sorted(disallowed | ({"decide +native"} if native_decision else set()))))


def module_name(path: str) -> str:
    return str(Path(path).with_suffix("")).replace(os.sep, ".")


def reachable_order(root_module: str, graph: dict[str, list[str]]) -> list[str]:
    """Topological project build order, rejecting all project-source orphans."""
    if root_module not in graph:
        raise VerificationError(f"Missing root source: {root_module}")
    visited, active, order = set(), set(), []
    def visit(module):
        if module in active:
            raise VerificationError(f"Cyclic project import: {module}")
        if module in visited:
            return
        active.add(module)
        for child in graph[module]:
            if child in graph:
                visit(child)
        active.remove(module)
        visited.add(module)
        order.append(module)
    visit(root_module)
    orphaned = set(graph) - visited
    if orphaned:
        raise VerificationError("Project modules unreachable from root: " + ", ".join(sorted(orphaned)))
    return order


def source_slice(source: str, start: dict, end: dict) -> str:
    # Lean Position columns count Unicode codepoints, unlike its separate UTF-16 fields.
    lines = source.splitlines(keepends=True)
    def offset(p):
        return sum(map(len, lines[:p["line"] - 1])) + p["column"]
    return source[offset(start):offset(end)]


def public_source_theorems(declarations: list[dict], sources: dict[str, str]) -> list[str]:
    """Human-facing count, separate from all-constant coverage.

    A compiler theorem needs a source name-selection range matching its actual
    name and a theorem/lemma command prefix. Generated equations are not silently
    counted as user-stated research lemmas. Names/namespaces never come from regex.
    """
    result = []
    for decl in declarations:
        if decl["kind"] != "theorem" or decl["private"]:
            continue
        selection, span = decl.get("selection"), decl.get("range")
        if not selection or not span:
            continue
        source = sources[decl["module"]]
        spelling = source_slice(source, selection["start"], selection["end"]).strip()
        spelling = spelling.removeprefix("_root_.").replace("«", "").replace("»", "")
        if not spelling or not (decl["name"] == spelling or decl["name"].endswith("." + spelling)):
            continue
        prefix = source_slice(source, span["start"], selection["start"])
        if {"theorem", "lemma"} & set(lean_tokens(prefix)):
            result.append(decl["name"])
    return sorted(result)


def validate_environment(report: dict, expected: set[str]) -> tuple[list[dict], set[str]]:
    if report.get("schema_version") != 1 or report.get("visibility") != "private":
        raise VerificationError("Unexpected compiler audit schema or visibility")
    missing = expected - set(report["imported_modules"])
    if missing:
        raise VerificationError("Compiled root omits project modules: " + ", ".join(sorted(missing)))
    names, used = set(), set()
    declarations = report["declarations"]
    by_name = {d["name"]: d for d in declarations}
    generated_partial = set()
    for d in declarations:
        if d["partial"]:
            parent = by_name.get(d["name"].removesuffix("._unsafe_rec"))
            if (d["name"].endswith("._unsafe_rec") and d["internal"] and
                    not d.get("range") and parent and parent["module"] == d["module"] and
                    parent["kind"] == "definition" and not parent["partial"] and not parent["unsafe"]):
                generated_partial.add(d["name"])
    if not declarations:
        raise VerificationError("Compiler audit returned no project declarations")
    for decl in declarations:
        if decl["module"] not in expected or decl["name"] in names:
            raise VerificationError(f"Invalid declaration provenance/duplicate: {decl['name']}")
        names.add(decl["name"])
        used.update(decl["axioms"])
        if decl["kind"] in {"axiom", "opaque"} or decl["unsafe"] or (decl["partial"] and decl["name"] not in generated_partial) or decl["extern"] or decl["implemented_by"]:
            raise VerificationError(f"Disallowed compiled declaration: {decl['name']} ({decl['kind']})")
        # Lean emits partial runtime implementations for total recursive defs.
        # Audit them too, but forbid any kernel-facing project declaration from
        # using those generated execution helpers as a logical dependency.
        if not decl["partial"] and generated_partial & set(decl["references"]):
            raise VerificationError(f"Kernel declaration refers to runtime recursion helper: {decl['name']}")
        forbidden = {name for name in decl["references"] if name.split(".")[-1] in BANNED_REFERENCES}
        if forbidden:
            raise VerificationError(f"Disallowed compiled dependency in {decl['name']}: {sorted(forbidden)}")
    if not used <= ALLOWED_AXIOMS:
        raise VerificationError("Unexpected axiom dependencies: " + ", ".join(sorted(used - ALLOWED_AXIOMS)))
    return declarations, used


def command(args: list[str], *, cwd: Path, env: dict | None = None,
            log: Path | None = None, append: bool = False) -> str:
    result = subprocess.run(args, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    if log:
        with log.open("a" if append else "w") as stream:
            stream.write(result.stdout)
    if result.stdout:
        print(result.stdout, end="", flush=True)
    if result.returncode:
        raise VerificationError(f"Command failed ({result.returncode}): {' '.join(args)}")
    return result.stdout


def verify(root: Path, lake: str, root_module: str = "QUBOPreprocessing") -> dict:
    logdir = root / "verification"
    logdir.mkdir(exist_ok=True)
    initial = snapshot(root)
    source_paths = [str(p.relative_to(root)) for p in proof_files(root)]
    sources = {module_name(p): initial[p].data.decode() for p in source_paths}
    for p in source_paths:
        check_source_policy(initial[p].data.decode(), p)
    atomic_json(logdir / "sources.before.json", {p: s.digest for p, s in initial.items()})
    # `lake env` only resolves the pinned environment. No Lake build/cache/update
    # command runs, so shared dependency caches are never modified by the driver.
    prefix = command([lake, "env", "lean", "--print-prefix"], cwd=root).strip()
    lean = str(Path(prefix) / "bin" / "lean")
    dependencies = command([lake, "env", "printenv", "LEAN_PATH"], cwd=root).strip()
    version = command([lean, "--version"], cwd=root).strip()
    assert_unchanged(root, initial)
    with tempfile.TemporaryDirectory(prefix="qubo-preprocessing-verify-") as temporary:
        stage = Path(temporary)
        source_root, build_root = stage / "source", stage / "build"
        for p, state in initial.items():
            target = source_root / p
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(state.data)
        build_root.mkdir()
        # Exclude the ordinary project build from fallback imports: a missing
        # snapshot module must fail rather than silently load a stale local olean.
        ordinary_build = (root / ".lake/build/lib/lean").resolve()
        dependency_paths = [str((root / p).resolve()) for p in dependencies.split(os.pathsep)
                            if p and (root / p).resolve() != ordinary_build]
        env = os.environ.copy()
        env["PATH"] = str(Path(prefix) / "bin") + os.pathsep + env.get("PATH", "")
        env["LEAN_PATH"] = os.pathsep.join([str(build_root), *dependency_paths])
        manifest = [{"module": module_name(p), "path": str(source_root / p)} for p in source_paths]
        manifest_path = stage / "modules.json"
        atomic_json(manifest_path, manifest)
        helper = source_root / "test/AxiomAudit.lean"
        imports_path = stage / "imports.json"
        command([lean, "--run", str(helper), "imports", str(manifest_path), str(imports_path)],
                cwd=source_root, env=env, log=logdir / "imports.log")
        graph = {x["module"]: x["imports"] for x in json.loads(imports_path.read_text())}
        order = reachable_order(root_module, graph)
        atomic_json(logdir / "imports.json", graph)
        assert_unchanged(root, initial)
        (logdir / "build.log").write_text("")
        for module in order:
            relative = Path(*module.split(".")).with_suffix(".lean")
            target = (build_root / relative).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            print(f"Kernel compiling {module}", flush=True)
            command([lean, "-DautoImplicit=false", "-o", str(target), "-i", str(target.with_suffix(".ilean")),
                     str(relative)], cwd=source_root, env=env, log=logdir / "build.log", append=True)
            assert_unchanged(root, initial)
        report_path = stage / "environment.json"
        command([lean, "--run", str(helper), "audit", root_module, str(manifest_path), str(report_path)],
                cwd=source_root, env=env, log=logdir / "audit.log")
        report = json.loads(report_path.read_text())
        if report.get("root") != root_module:
            raise VerificationError("Compiler audit imported a different root module")
        declarations, used = validate_environment(report, set(sources))
        public = public_source_theorems(declarations, sources)
        if not public:
            raise VerificationError("No source-declared public theorem metadata; do not publish a misleading count")
        report["public_source_theorems"] = public
        atomic_json(logdir / "environment.json", report)
        with (logdir / "axioms.log").open("w") as stream:
            for d in declarations:
                stream.write(f"{d['module']} | {d['kind']} | {d['name']} | axioms: {', '.join(d['axioms'])}\n")
        # The audit and artifacts correspond to these exact captured bytes.
        assert_unchanged(root, initial)
        artifact_hashes = {str(p.relative_to(build_root)): hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in sorted(build_root.rglob("*.olean"))}
    final = snapshot(root)
    assert_unchanged(root, initial)
    record = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version,
        "status": "build_and_axiom_audit_passed",
        "build_method": "isolated source snapshot; every project module recompiled by Lean; dependency cache read-only",
        "audit_method": "compiler environment, private visibility, defining-module provenance, all constant kinds",
        "root_module": root_module,
        "project_module_count": len(sources),
        "project_modules": sorted(sources),
        "all_project_constant_count": len(declarations),
        "constant_kinds": dict(sorted(Counter(d["kind"] for d in declarations).items())),
        "private_constant_count": sum(d["private"] for d in declarations),
        "compiler_generated_partial_runtime_helpers": sorted(d["name"] for d in declarations if d["partial"]),
        "public_theorem_count": len(public),
        "public_theorem_count_method": "compiler theorem metadata matched to theorem/lemma source name-selection ranges; generated declarations counted separately",
        "axioms": sorted(used),
        "source_snapshot_unchanged": True,
        "sha256": {p: s.digest for p, s in initial.items()},
        "sha256_after": {p: s.digest for p, s in final.items()},
        "compiled_olean_sha256": artifact_hashes,
        "dependency_boundary": "Pinned Mathlib/Lean oleans are trusted imports, not rebuilt or independently kernel-replayed",
    }
    atomic_json(logdir / "sources.after.json", record["sha256_after"])
    atomic_json(logdir / "result.json", record)
    print(f"Verified {len(public)} public source theorems and {len(declarations)} total project constants "
          f"across {len(sources)} modules; allowed axioms: {', '.join(sorted(used))}.")
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--root-module", default="QUBOPreprocessing")
    args = parser.parse_args()
    root = args.root.resolve()
    logdir = root / "verification"
    logdir.mkdir(exist_ok=True)
    default_lake = (
        "/tmp/lean-theleodynamics-elan/bin/lake"
        if Path("/tmp/lean-theleodynamics-elan/bin/lake").exists()
        else "lake"
    )
    lake_cmd = os.environ.get("QUBO_LAKE", os.environ.get("FERMIONIC_LAKE", default_lake))
    with (logdir / "verify.lock").open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            print("Another verification is running; refusing concurrent output writes.")
            return 1
        atomic_json(logdir / "result.json", {"status": "verification_running"})
        try:
            verify(root, lake_cmd, args.root_module)
        except (VerificationError, OSError, ValueError, KeyError) as error:
            atomic_json(logdir / "result.json", {"status": "verification_failed", "error": str(error),
                "checked_at_utc": datetime.now(timezone.utc).isoformat()})
            print(f"Verification failed: {error}", flush=True)
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
