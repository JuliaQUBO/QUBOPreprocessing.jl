# SPDX-License-Identifier: MPL-2.0
import importlib.util
import pathlib
import subprocess
import tempfile
import unittest
import os
from unittest.mock import patch

spec = importlib.util.spec_from_file_location("gate", pathlib.Path(__file__).parents[2] / "scripts/validate_release.py")
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


class Provenance(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.previous = os.getcwd()
        os.chdir(self.directory.name)
        self.addCleanup(os.chdir, self.previous)
        self.addCleanup(self.directory.cleanup)
        subprocess.run(["git", "init", "-q"], check=True)
        for key, value in (("user.email", "fixture@example.invalid"), ("user.name", "Fixture")):
            subprocess.run(["git", "config", key, value], check=True)
        pathlib.Path("Project.toml").write_text(f'name = "QUBOPreprocessing"\nuuid = "{gate.UUID}"\nversion = "0.1.0"\n')
        subprocess.run(["git", "add", "Project.toml"], check=True)
        subprocess.run(["git", "commit", "-qm", "fixture"], check=True)
        self.commit = gate.git("rev-parse", "HEAD")
        self.tree = gate.git("rev-parse", "HEAD^{tree}")
        subprocess.run(["git", "tag", "-a", "v0.1.0", "-m", "fixture"], check=True)
        self.package = dict(name="QUBOPreprocessing", uuid=gate.UUID, repo=f"https://github.com/{gate.REPOSITORY}.git")
        self.versions = {"0.1.0": {"git-tree-sha1": self.tree}}
        self.release = dict(tag_name="v0.1.0", draft=False, prerelease=False)

    def validate(self, **overrides):
        data = dict(tag="v0.1.0", commit=self.commit, package=self.package, versions=self.versions, release=self.release)
        data.update(overrides)
        return gate.validate(**data)

    def test_annotated_tag_and_tree(self):
        self.assertEqual(self.validate(), self.tree)
        self.assertNotEqual(gate.git("rev-parse", "v0.1.0"), self.commit)

    def test_wrong_source_tree(self):
        with self.assertRaises(ValueError):
            self.validate(versions={"0.1.0": {"git-tree-sha1": "0" * 40}})

    def test_wrong_commit(self):
        with self.assertRaises(ValueError):
            self.validate(commit="0" * 40)

    def test_unreviewed_source(self):
        subprocess.run(["git", "checkout", "-qb", "other"], check=True)
        pathlib.Path("other").write_text("unreviewed")
        subprocess.run(["git", "add", "other"], check=True)
        subprocess.run(["git", "commit", "-qm", "other"], check=True)
        other = gate.git("rev-parse", "HEAD")
        subprocess.run(["git", "tag", "-f", "v0.1.0", other], check=True, stdout=subprocess.DEVNULL)
        subprocess.run(["git", "checkout", "-q", self.commit], check=True)
        with self.assertRaises(subprocess.CalledProcessError):
            self.validate(commit=other)

    def test_unpublished_or_wrong_identity(self):
        for field in ("draft", "prerelease"):
            with self.assertRaises(ValueError):
                self.validate(release=dict(self.release, **{field: True}))
        with self.assertRaises(ValueError):
            self.validate(package=dict(self.package, uuid="wrong"))

    def test_event_and_input_gates(self):
        env = dict(GITHUB_REPOSITORY=gate.REPOSITORY, GITHUB_REF="refs/heads/main", GITHUB_EVENT_NAME="push")
        with patch.dict(os.environ, env, clear=True):
            gate.main()
        for override in (dict(GITHUB_REF="refs/tags/v0.1.0"), dict(GITHUB_EVENT_NAME="pull_request"), dict(RELEASE_COMMIT=self.commit), dict(RELEASE_TAG="v0.1.0")):
            with patch.dict(os.environ, dict(env, **override), clear=True), self.assertRaises(ValueError):
                gate.main()

    def test_dispatch_inputs_and_complete_output(self):
        env = dict(GITHUB_REPOSITORY=gate.REPOSITORY, GITHUB_REF="refs/heads/main", GITHUB_EVENT_NAME="workflow_dispatch")
        for inputs in (dict(RELEASE_TAG="v0.1.0"), dict(RELEASE_COMMIT=self.commit), dict(RELEASE_TAG="v0.1.0", RELEASE_COMMIT="bad-sha")):
            with patch.dict(os.environ, dict(env, **inputs), clear=True), self.assertRaises(ValueError):
                gate.main()
        output = pathlib.Path("output.txt")
        env.update(RELEASE_TAG="v0.1.0", RELEASE_COMMIT=self.commit, GITHUB_OUTPUT=str(output))
        package = f'name = "QUBOPreprocessing"\nuuid = "{gate.UUID}"\nrepo = "https://github.com/{gate.REPOSITORY}.git"\n'
        versions = f'["0.1.0"]\ngit-tree-sha1 = "{self.tree}"\n'
        release = dict(self.release, html_url=f"https://github.com/{gate.REPOSITORY}/releases/tag/v0.1.0")
        import json
        with patch.dict(os.environ, env, clear=True), patch.object(gate, "gh", side_effect=[package, versions, json.dumps(release)]) as api:
            gate.main()
        self.assertEqual(api.call_count, 3)
        self.assertEqual(output.read_text(), f"tag=v0.1.0\ncommit={self.commit}\ntree={self.tree}\n")


if __name__ == "__main__":
    unittest.main()
