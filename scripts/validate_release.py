# SPDX-License-Identifier: MPL-2.0
"""Read-only provenance gate for main-dispatched release documentation."""
import json
import os
import re
import subprocess
import tomllib

REPOSITORY = "JuliaQUBO/QUBOPreprocessing.jl"
UUID = "ce9b04da-6a94-4a97-978a-34bf3f916ed2"


def git(*args):
    return subprocess.check_output(["git", *args], text=True).strip()


def gh(path):
    return subprocess.check_output(
        ["gh", "api", path, "-H", "Accept: application/vnd.github.raw"], text=True
    )


def validate(tag, commit, package, versions, release):
    if not re.fullmatch(r"v[0-9]+\.[0-9]+\.[0-9]+", tag):
        raise ValueError("expected exact vMAJOR.MINOR.PATCH release tag")
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("expected full lowercase commit SHA")
    if git("rev-parse", f"refs/tags/{tag}^{{commit}}") != commit:
        raise ValueError("tag does not dereference to verified release commit")
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], check=True)
    project = tomllib.loads(git("show", f"{commit}:Project.toml"))
    if (project["name"], project["uuid"], project["version"]) != (
        "QUBOPreprocessing", UUID, tag[1:]
    ):
        raise ValueError("release package identity/version mismatch")
    if (package["name"], package["uuid"], package["repo"]) != (
        "QUBOPreprocessing", UUID, f"https://github.com/{REPOSITORY}.git"
    ):
        raise ValueError("General package identity/repository mismatch")
    tree = git("rev-parse", f"{commit}^{{tree}}")
    if versions[tag[1:]]["git-tree-sha1"] != tree:
        raise ValueError("General tree does not match release source")
    if release["tag_name"] != tag or release["draft"] or release["prerelease"]:
        raise ValueError("expected published, non-prerelease GitHub release")
    return tree


def main():
    if (os.environ.get("GITHUB_REPOSITORY") != REPOSITORY
            or os.environ.get("GITHUB_REF") != "refs/heads/main"
            or os.environ.get("GITHUB_EVENT_NAME") not in ("push", "workflow_dispatch")):
        raise ValueError("publisher requires trusted upstream main event")
    tag, commit = os.environ.get("RELEASE_TAG", ""), os.environ.get("RELEASE_COMMIT", "")
    if not tag and not commit:
        return  # ordinary development publication
    if os.environ["GITHUB_EVENT_NAME"] != "workflow_dispatch":
        raise ValueError("release refresh requires workflow_dispatch")
    # Validate syntax before constructing ref names or API paths.
    if not re.fullmatch(r"v[0-9]+\.[0-9]+\.[0-9]+", tag) or not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("both an exact release tag and full SHA are required")
    path = "repos/JuliaRegistries/General/contents/Q/QUBOPreprocessing"
    package = tomllib.loads(gh(f"{path}/Package.toml"))
    versions = tomllib.loads(gh(f"{path}/Versions.toml"))
    release = json.loads(gh(f"repos/{REPOSITORY}/releases/tags/{tag}"))
    tree = validate(tag, commit, package, versions, release)
    print(json.dumps({"tag": tag, "commit": commit, "tree": tree, "release": release["html_url"]}))
    with open(os.environ["GITHUB_OUTPUT"], "a") as output:
        output.write(f"tag={tag}\ncommit={commit}\ntree={tree}\n")


if __name__ == "__main__":
    main()
