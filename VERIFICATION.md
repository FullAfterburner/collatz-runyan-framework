# Formal verification

## Successful local unified audit

Date: 2026-11-28

- Proof-bearing modules: 64
- Distinct audited theorem names: 1056
- Unified module import: passed
- Unexpected axiom dependencies: zero
- sorryAx dependencies among audited declarations: zero

## Pinned verification environment

- Lean: 4.19.0
- Lean commit: 6caaee842e94
- Mathlib: v4.19.0
- Mathlib commit: c44e0c8ee63ca166450922a373c7409c5d26b00b

Original repository baseline:

`178a78f09608c1a2158e6a7ce64868ec4207b909`

The verifier reads exact committed source bytes for historical
modules. Working-tree differences are accepted only when they
consist of CRLF/LF newline conversion.

Canonical spectral sources are validated by exact SHA-256
fingerprints. Their bytes must not be normalized.

## Verification procedure

The unified verifier:

1. Validates the expected source inventory.
2. Confirms original source identities against the baseline.
3. Checks canonical spectral source fingerprints.
4. Compiles fresh Lean object files in dependency order.
5. Audits individual declarations.
6. Imports all 64 proof-bearing modules together.
7. Repeats all 1056 axiom reports in the shared environment.
8. Checks that individual and joint audit results agree.

## Local evidence

- [Audit summary](Collatz%20Research%20v2.7/audit/evidence/summary.txt)
- [Declaration inventory](Collatz%20Research%20v2.7/audit/evidence/declaration-inventory.json)
- [Unified axiom audit](Collatz%20Research%20v2.7/audit/evidence/unified-axiom-audit.txt)
- [Evidence SHA-256 manifest](Collatz%20Research%20v2.7/audit/evidence/SHA256SUMS.txt)
- [Unified verifier](Collatz%20Research%20v2.7/audit/verify-v27.py)

## Reproducing the audit

Install Elan and use the pinned Lean/Mathlib configuration
inside `Collatz Research v2.3`.

A full Git history is required because the verifier accesses
historical committed source bytes.

From the repository root on Linux:

```bash
repo="$(pwd)"
cd "Collatz Research v2.3"
lake exe cache get
git -C .lake/packages/mathlib rev-parse HEAD
lake env python3 "$repo/Collatz Research v2.7/audit/verify-v27.py" "$repo/full-audit-v27"
```

Use a new output directory for each verification run.

## Axiom audit interpretation

The allowed axiom dependencies are propext,
Classical.choice and Quot.sound.

The audit checks the designated theorem inventory. It does
not establish mathematical independence, physical validity,
external peer review or the Collatz conjecture.

## Automated verification

The v2.7 GitHub Actions workflow is intended to reproduce
the local unified audit on Linux and compare its complete
declaration inventory with the archived local evidence.

A successful local audit is recorded here. The clean-checkout
automated audit remains pending.
