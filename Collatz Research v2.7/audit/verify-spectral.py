#!/usr/bin/env python3
"""Compile and jointly audit the canonical CRF spectral modules."""

import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "Collatz Research v2.7"

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

PACKAGES = [
    (
        "GeometricSpectral",
        "CollatzGeometricSpectralStage1To6.generated.lean",
        "CRFGeometricSpectral",
        "04a5a51a967e030f7a6da3eccdfded19c39f93ff8fc02b6db148669dfd02034b",
        138,
    ),
    (
        "LeptonModular",
        "LeptonModularStage1To9.generated.lean",
        "CRFLeptonModular",
        "98bd3767cb0ab260f51f015d61d5f9013925d32c18c6981925bec82c089301ba",
        358,
    ),
]

AX = re.compile(
    r"'([^']+)'\s+(?:depends on axioms:\s*"
    r"\[([^\]]*)\]|does not depend on any axioms)"
)

BAD = re.compile(
    r"\berror:|sorryAx|declaration uses .sorry.",
    re.I,
)


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, log, env):
    result = subprocess.run(
        args,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        env=env,
        text=True,
        encoding="utf-8",
        errors="replace",
    )

    log.write_text(result.stdout, encoding="utf-8")

    require(
        result.returncode == 0 and not BAD.search(result.stdout),
        f"Verification failed: {log}",
    )

    print(f"PASS: {log.name}", flush=True)
    return result.stdout


def parse_axioms(text, expected):
    entries = AX.findall(text)
    names = [name for name, _ in entries]

    require(len(entries) == expected, "Incorrect audit count")
    require(len(set(names)) == expected, "Duplicate audit names")

    result = {}

    for name, axioms in entries:
        dependencies = sorted(
            a.strip() for a in axioms.split(",") if a.strip()
        )

        require(
            set(dependencies) <= ALLOWED,
            f"Unexpected axiom in {name}: {dependencies}",
        )

        result[name] = dependencies

    return result


def main():
    require(
        len(sys.argv) == 2,
        "Usage: verify-spectral.py OUTPUT_DIRECTORY",
    )

    out = Path(sys.argv[1]).resolve()
    out.mkdir(parents=True, exist_ok=False)

    env = os.environ.copy()

    require(
        bool(env.get("LEAN_PATH")),
        "Run this script through lake env",
    )

    version = run(
        ["lean", "--version"],
        out / "lean-version.txt",
        env,
    )

    require(
        "version 4.19.0" in version,
        "Unexpected Lean version",
    )

    expected_names = {
        name.strip()
        for name in (
            SRC / "audited-declarations.txt"
        ).read_text(encoding="utf-8-sig").splitlines()
        if name.strip()
    }

    require(
        len(expected_names) == 496,
        "Incorrect expected declaration inventory",
    )

    all_names = {}
    records = []

    with tempfile.TemporaryDirectory(prefix="crf-v27-") as tmp:

        root = Path(tmp)
        build = root / "build"
        build.mkdir()

        env["LEAN_PATH"] = (
            str(build) + os.pathsep + env["LEAN_PATH"]
        )

        for folder, filename, module, expected_hash, count in PACKAGES:

            original = SRC / folder / filename

            require(
                sha256(original) == expected_hash,
                f"Source checksum mismatch: {original}",
            )

            # Valid Lean module filename; identical source bytes.
            source = root / f"{module}.lean"
            source.write_bytes(original.read_bytes())

            output = build / f"{module}.olean"

            log = run(
                [
                    "lean",
                    f"--root={root}",
                    "-o",
                    str(output),
                    str(source),
                ],
                out / f"{module}-compile.txt",
                env,
            )

            require(output.is_file(), f"Missing object: {output}")
            require(sha256(source) == expected_hash, "Source changed")

            names = parse_axioms(log, count)

            require(
                not (set(names) & set(all_names)),
                "Cross-module duplicate declaration",
            )

            all_names.update(names)

            records.append({
                "module": module,
                "source": str(original.relative_to(ROOT)),
                "sha256": expected_hash,
                "declarations": count,
            })

        require(
            set(all_names) == expected_names,
            "Compiled declarations differ from archived inventory",
        )

        # Import both fresh object files into one environment.
        driver = root / "CRFSpectralAudit.lean"

        driver.write_text(
            "import CRFGeometricSpectral\n"
            "import CRFLeptonModular\n\n"
            + "\n".join(
                f"#print axioms {name}"
                for name in sorted(all_names)
            )
            + "\n",
            encoding="utf-8",
        )

        joint_log = run(
            ["lean", f"--root={root}", str(driver)],
            out / "joint-axiom-audit.txt",
            env,
        )

        joint = parse_axioms(joint_log, 496)

        require(
            joint == all_names,
            "Joint axiom inventory differs from individual audits",
        )

    inventory = {
        "status": "passed",
        "lean": version.strip(),
        "modules": records,
        "distinct_audited_names": len(joint),
        "axioms": joint,
    }

    (out / "declaration-inventory.json").write_text(
        json.dumps(inventory, indent=2) + "\n",
        encoding="utf-8",
    )

    print("PASS: Both spectral modules compiled and imported together")
    print("PASS: 496 distinct theorem axiom reports")
    print("PASS: Zero unexpected axioms")
    print(f"Audit evidence: {out}")


if __name__ == "__main__":
    main()
