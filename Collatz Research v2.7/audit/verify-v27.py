#!/usr/bin/env python3
"""Repository-wide CRF v2.7 verification."""

import hashlib
import json
import os
import re
import runpy
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASELINE = "178a78f09608c1a2158e6a7ce64868ec4207b909"

helpers = runpy.run_path(
    str(Path(__file__).with_name("verify-spectral.py"))
)

require = helpers["require"]
run = helpers["run"]
parse_axioms = helpers["parse_axioms"]
PACKAGES = helpers["PACKAGES"]

DECL = re.compile(
    r"^\s*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z_0-9']*)\b",
    re.M,
)

NS = re.compile(
    r"^namespace\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$",
    re.M,
)

IMPORT = re.compile(
    r"^import\s+([A-Za-z_][A-Za-z_0-9.]*)",
    re.M,
)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def git_bytes(*args):
    return subprocess.check_output(
        ["git", *args], cwd=ROOT
    )


def load_json(path):
    return path.read_text(encoding="utf-8-sig")


def main():
    require(
        len(sys.argv) == 2,
        "Usage: verify-v27.py OUTPUT_DIRECTORY",
    )

    out = Path(sys.argv[1]).resolve()
    out.mkdir(parents=True, exist_ok=False)

    env = os.environ.copy()

    require(
        bool(env.get("LEAN_PATH")),
        "Run through lake env",
    )

    version = run(
        ["lean", "--version"],
        out / "lean-version.txt",
        env,
    )

    require(
        "version 4.19.0" in version,
        "Wrong Lean version",
    )

    config = json.loads(load_json(
        ROOT / "Collatz Research v2.5/audit/audit-config.json"
    ))

    v26 = json.loads(load_json(
        ROOT / "Collatz Research v2.6/audit/source-inventory.json"
    ))

    projects = dict(config["projects"])

    projects["Collatz Research v2.6"] = {
        entry["file"]: entry["declarations"]
        for entry in v26
    }

    require(
        sum(len(files) for files in projects.values()) == 62,
        "Incorrect original module count",
    )

    require(
        sum(sum(files.values()) for files in projects.values()) == 560,
        "Incorrect original declaration count",
    )

    sources = {}
    expected_names = set()

    for project, files in projects.items():

        for file, count in files.items():

            path = ROOT / project / file
            raw = path.read_bytes()

            relative = path.relative_to(ROOT).as_posix()

            committed = git_bytes(
                "show", BASELINE + ":" + relative
            )

            if raw != committed:
                require(
                    raw.replace(bytes((13, 10)), bytes((10,)))
                    == committed.replace(bytes((13, 10)), bytes((10,))),
                    f"Non-newline source difference: {relative}",
                )

                print(
                    f"CHECKOUT NEWLINES NORMALIZED: {relative}",
                    flush=True,
                )

            # Compile exact committed bytes, not checkout bytes.
            raw = committed

            module = (
                Path(file).with_suffix("")
                .as_posix().replace("/", ".")
            )

            require(
                module not in sources,
                f"Duplicate module name: {module}",
            )

            txt = raw.decode("utf-8-sig")
            namespaces = NS.findall(txt)
            simple = DECL.findall(txt)

            require(
                len(namespaces) == 1
                and len(simple) == count
                and len(set(simple)) == count,
                f"Unexpected declarations: {relative}",
            )

            names = {
                namespaces[0] + "." + n for n in simple
            }

            require(
                not (names & expected_names),
                f"Duplicate theorem names: {relative}",
            )

            expected_names.update(names)

            sources[module] = {
                "path": relative,
                "raw": raw,
                "names": names,
                "count": count,
                "imports": set(IMPORT.findall(txt)),
                "spectral": False,
            }

    require(
        len(expected_names) == 560,
        "Original declaration inventory mismatch",
    )

    spectral_root = ROOT / "Collatz Research v2.7"

    spectral_names = {
        n.strip()
        for n in (
            spectral_root / "audited-declarations.txt"
        ).read_text(encoding="utf-8-sig").splitlines()
        if n.strip()
    }

    require(
        len(spectral_names) == 496,
        "Spectral name inventory mismatch",
    )

    require(
        not (spectral_names & expected_names),
        "Original/spectral name collision",
    )

    expected_names.update(spectral_names)

    for folder, file, module, expected_hash, count in PACKAGES:

        path = spectral_root / folder / file
        raw = path.read_bytes()

        require(
            digest(raw) == expected_hash,
            f"Spectral source hash mismatch: {file}",
        )

        prefix = (
            "CollatzRunyan.GeometricSpectral."
            if folder == "GeometricSpectral"
            else "CollatzRunyan.LeptonSpectral."
        )

        names = {
            n for n in spectral_names
            if n.startswith(prefix)
        }

        require(
            len(names) == count,
            f"Spectral namespace count mismatch: {folder}",
        )

        sources[module] = {
            "path": path.relative_to(ROOT).as_posix(),
            "raw": raw,
            "names": names,
            "count": count,
            "imports": set(
                IMPORT.findall(raw.decode("utf-8-sig"))
            ),
            "spectral": True,
        }

    require(len(sources) == 64, "Module total mismatch")
    require(len(expected_names) == 1056, "Name total mismatch")

    print(
        "PASS: 64 source identities; 1056 distinct expected names",
        flush=True,
    )

    all_axioms = {}
    records = []
    completed = set()

    with tempfile.TemporaryDirectory(prefix="crf-v27-full-") as tmp:

        scratch = Path(tmp)
        src = scratch / "src"
        build = scratch / "build"

        src.mkdir()
        build.mkdir()

        env["LEAN_PATH"] = (
            str(build) + os.pathsep + env["LEAN_PATH"]
        )

        for module, entry in sources.items():

            source = src.joinpath(
                *module.split(".")
            ).with_suffix(".lean")

            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_bytes(entry["raw"])

        while len(completed) < len(sources):

            ready = sorted(
                module
                for module, entry in sources.items()
                if module not in completed
                and (entry["imports"] & sources.keys()) <= completed
            )

            require(bool(ready), "Local dependency cycle")

            for module in ready:

                entry = sources[module]

                source = src.joinpath(
                    *module.split(".")
                ).with_suffix(".lean")

                output = build.joinpath(
                    *module.split(".")
                ).with_suffix(".olean")

                output.parent.mkdir(
                    parents=True, exist_ok=True
                )

                compile_log = run(
                    [
                        "lean",
                        f"--root={src}",
                        "-o",
                        str(output),
                        str(source),
                    ],
                    out / f"{module}-compile.txt",
                    env,
                )

                require(
                    output.is_file(),
                    f"Missing compiled object: {module}",
                )

                require(
                    source.read_bytes() == entry["raw"],
                    f"Source changed: {module}",
                )

                if entry["spectral"]:
                    report = compile_log
                else:
                    driver = src / "AuditDriver.lean"

                    driver.write_text(
                        f"import {module}\n"
                        + "\n".join(
                            f"#print axioms {name}"
                            for name in sorted(entry["names"])
                        )
                        + "\n",
                        encoding="utf-8",
                    )

                    report = run(
                        ["lean", f"--root={src}", str(driver)],
                        out / f"{module}-axioms.txt",
                        env,
                    )

                axioms = parse_axioms(
                    report, entry["count"]
                )

                require(
                    set(axioms) == entry["names"],
                    f"Audited name mismatch: {module}",
                )

                require(
                    not (set(axioms) & all_axioms.keys()),
                    f"Duplicate audited name: {module}",
                )

                all_axioms.update(axioms)

                records.append({
                    "module": module,
                    "source": entry["path"],
                    "source_sha256": digest(entry["raw"]),
                    "compiled_sha256": digest(output.read_bytes()),
                    "declarations": axioms,
                })

                completed.add(module)

                print(
                    f"VERIFIED {len(completed)}/64: "
                    f"{module} ({entry['count']})",
                    flush=True,
                )

        require(
            set(all_axioms) == expected_names,
            "Complete individual audit inventory mismatch",
        )

        # Preserve the individual results even if the joint import fails.
        (out / "individual-inventory.json").write_text(
            json.dumps({
                "status": "passed",
                "modules": len(records),
                "declarations": len(all_axioms),
                "records": records,
            }, indent=2) + "\n",
            encoding="utf-8",
        )

        driver = src / "CRFUnifiedAudit.lean"

        driver.write_text(
            "\n".join(
                f"import {module}"
                for module in sorted(sources)
            )
            + "\n\n"
            + "\n".join(
                f"#print axioms {name}"
                for name in sorted(expected_names)
            )
            + "\n",
            encoding="utf-8",
        )

        (out / driver.name).write_bytes(driver.read_bytes())

        joint_log = run(
            ["lean", f"--root={src}", str(driver)],
            out / "unified-axiom-audit.txt",
            env,
        )

        joint = parse_axioms(joint_log, 1056)

        require(
            joint == all_axioms,
            "Unified axiom inventory differs from individual audits",
        )

    result = {
        "status": "passed",
        "baseline": BASELINE,
        "lean": version.strip(),
        "modules": len(records),
        "distinct_audited_names": len(joint),
        "records": records,
        "axioms": joint,
    }

    (out / "declaration-inventory.json").write_text(
        json.dumps(result, indent=2) + "\n",
        encoding="utf-8",
    )

    (out / "summary.txt").write_text(
        "PASS: 64 modules; 1056 distinct audited names; "
        "joint import passed; zero unexpected axioms.\n",
        encoding="utf-8",
    )

    print("PASS: 64/64 proof-bearing modules")
    print("PASS: 1056 distinct theorem axiom reports")
    print("PASS: Unified module import")
    print("PASS: Zero unexpected axioms")
    print(f"Audit evidence: {out}")


if __name__ == "__main__":
    main()
