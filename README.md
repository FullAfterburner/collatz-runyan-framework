# The Collatz-Runyan Framework

**A formally verified research program in arithmetic dynamics,
number theory, modular geometry and spectral analysis.**

## v2.7 consolidation

![Lean](https://img.shields.io/badge/Lean-4.19.0-blue)
![Mathlib](https://img.shields.io/badge/Mathlib-v4.19.0-blue)
![Theorems](https://img.shields.io/badge/Audited_theorems-1056-success)
![Modules](https://img.shields.io/badge/Proof_modules-64-success)
![Local audit](https://img.shields.io/badge/Unified_local_audit-passed-success)
![Collatz](https://img.shields.io/badge/Collatz_conjecture-open-orange)

The Collatz-Runyan Framework investigates the arithmetic structure
of Collatz dynamics through machine-checked mathematical proofs,
exact affine identities, parity rigidity, cycle constraints,
modular decompositions and analytical reformulations.

The v2.7 consolidation combines the original arithmetic framework
with Geometric Spectral Stages 1-6 and Lepton Modular Stages 1-9.

On November 28, 2026, all 64 proof-bearing modules were compiled
and imported into one Lean environment. The unified kernel axiom
audit passed for 1,056 distinct theorem names.

The local audit is complete. Automated reproduction of the
reorganized release remains pending.

## Start here

| Resource | Description |
|---|---|
| [Master Research Paper](Papers/Collatz_Runyan_Framework_v2_7_Master_Research_Paper.pdf) | Comprehensive mathematical synthesis and scientific visualizations |
| [Complete theorem catalog](Documentation/Research-Index/README.md) | All 1,056 audited theorem names |
| [Theorem index CSV](Documentation/Research-Index/THEOREM-INDEX.csv) | Searchable machine-readable inventory |
| [Module index](Documentation/Research-Index/MODULE-INDEX.csv) | Source locations and checksums |
| [Verification documentation](VERIFICATION.md) | Kernel audit methodology and reproduction |
| [Reproducibility package](Reproducibility/Collatz_Runyan_v2_7_Master_Paper_Reproducibility.zip) | Manuscript, Python scripts, figures and inventories |
| [Visualizations](Visualizations/README.md) | Scientific figure resources |
| [Changelog](CHANGELOG.md) | Research development history |
| [Historical archive](Archive/README.md) | Earlier papers, programs and experiments |

## Verified mathematical inventory

| Research collection | Modules | Audited theorems |
|---|---:|---:|
| Foundational Lean library | 4 | 16 |
| v2.3 arithmetic research | 13 | 121 |
| v2.4 arithmetic rigidity | 19 | 168 |
| v2.5 coefficient rigidity | 7 | 113 |
| v2.6 binary and adelic research | 19 | 142 |
| Geometric Spectral Stages 1-6 | 1 | 138 |
| Lepton Modular Stages 1-9 | 1 | 358 |
| **Total** | **64** | **1,056** |

## Principal research directions

### Arithmetic dynamics

- Exact shortcut Collatz orbit identities.
- Finite parity cylinders and affine coefficients.
- Conditional descent and non-descent restrictions.
- Coalescence and odd-predecessor family rigidity.
- The conditional 29/32 coefficient-growth bound.

### Cycle rigidity

- Accelerated odd-to-odd iteration.
- Binary valuation budgets and correction products.
- Affine cycle identities and divisibility constraints.
- Prefix admissibility and cyclic rotation certificates.

### Binary and geometric spectral analysis

- Abstract binary conjugation and involutions.
- Rational spectral decompositions.
- Real and 2-adic norm relationships.
- Missing-basin propagation and residue constraints.
- Positive kernel and theta-defect equivalences.

### Modular and analytical research

- Lepton and neutrino mass-model algebra.
- Conditional spectral and covariance obstructions.
- Parity-word probability models.
- Positive Dirichlet series and Basel-sum equivalences.
- Analytical extensions and outstanding Mellin-transform questions.

Physical interpretations are investigated as mathematical models,
not established physical laws.

## Kernel verification

The unified audit permits only the following standard Lean axioms:

- `propext`
- `Classical.choice`
- `Quot.sound`

| Axiom dependency set | Audited names |
|---|---:|
| Classical.choice, Quot.sound, propext | 780 |
| Quot.sound, propext | 210 |
| propext | 40 |
| None | 26 |
| Unexpected dependencies | 0 |

See the [complete local audit inventory](Collatz%20Research%20v2.7/audit/evidence/declaration-inventory.json)
and [unified axiom report](Collatz%20Research%20v2.7/audit/evidence/unified-axiom-audit.txt).

## Repository organization

The original versioned Lean research directories retain their
published paths. Historical non-Lean material is preserved under
`Archive/Legacy/`.

The canonical new spectral sources are located in
`Collatz Research v2.7/`.

## Scientific scope and limitations

The framework does not claim a proof of the Collatz conjecture
or the Riemann hypothesis.

The verified results include conditional statements, finite
certificates, equivalences and obstruction theorems. A verified
equivalence is not an independent proof of either side.

The audited declaration count measures distinct fully qualified
theorem names, not mathematical independence or originality.

Kernel verification is not a substitute for external peer review.

## Citation

The latest archived release cited during consolidation is v2.6:

https://doi.org/10.5281/zenodo.24573216

The v2.7 citation and DOI will be assigned following publication.

See [CITATION.cff](CITATION.cff) and [LICENSE](LICENSE).
