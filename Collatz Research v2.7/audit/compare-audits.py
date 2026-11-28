import json
import sys
from pathlib import Path

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def load(path):
    return json.loads(
        Path(path).read_text(encoding="utf-8-sig")
    )

def validate(inventory):
    require(inventory["status"] == "passed", "Audit status")
    require(inventory["modules"] == 64, "Module count")
    require(inventory["distinct_audited_names"] == 1056, "Name count")
    require(len(inventory["records"]) == 64, "Record count")
    require(len(inventory["axioms"]) == 1056, "Axiom inventory count")
    require("4.19.0" in inventory["lean"], "Lean version")

    allowed = {"propext", "Classical.choice", "Quot.sound"}
    records = {}
    names = {}

    for record in inventory["records"]:
        module = record["module"]

        require(module not in records, "Duplicate module")

        declarations = {
            n: sorted(a)
            for n, a in record["declarations"].items()
        }

        for n, a in declarations.items():
            require(n not in names, "Duplicate theorem: " + n)
            require(set(a) <= allowed, "Unexpected axiom: " + n)
            names[n] = a

        records[module] = {
            "source": record["source"].replace(chr(92), "/"),
            "source_sha256": record["source_sha256"],
            "declarations": declarations
        }

    require(
        names == {
            n: sorted(a)
            for n, a in inventory["axioms"].items()
        },
        "Individual and joint inventories disagree"
    )

    return records

require(len(sys.argv) == 3, "Usage: compare-audits.py OLD NEW")

archived = load(sys.argv[1])
fresh = load(sys.argv[2])

require(
    archived["baseline"] == fresh["baseline"],
    "Baseline mismatch"
)

require(
    validate(archived) == validate(fresh),
    "Fresh audit differs from archived local audit"
)

print("PASS: 64 module source identities reproduced")
print("PASS: 1056 theorem names reproduced")
print("PASS: All individual axiom dependencies reproduced")
print("PASS: Fresh and archived audit inventories agree")
