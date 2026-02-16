# Paper B Outline: HCIT Algebra Formulation and Quotient Model

## Scope
- Formalizes Altenkirch-style HCIT algebra signature for signed-digit reals.
- Shows quotient model `𝕀sd` is an instance.
- Isolates terminality as conditional (explicit postulate surface).

## Formal Anchors
- `src/Reals/SignedDigit/IncDec.agda`
- `src/Reals/SignedDigit/HCIT/Algebra.agda`
- `src/Reals/SignedDigit/HCIT/Structure.agda`
- `src/Reals/SignedDigit/HCIT/Terminality.agda`
- `src/Reals/SignedDigit/PaperB/Entrypoint.agda`
- `RealDefinitions.tex` (Section 4)

## Main Theorem Package
- Signature uses generation + completeness/separation (not `no-conf`).
- `no-conf` excluded as false in quotient semantics.
- `𝕀sd-Alg` as concrete model.
- Terminality map and uniqueness exposed conditionally via postulates.

## Stable Naming Contract
- Frozen by `src/Reals/SignedDigit/PaperB/Entrypoint.agda`.
- Canonical names: `inc⁻¹`, `inc⁰`, `inc⁺¹`, `dec⁺¹`, `dec⁰`, `dec⁻¹`, `carry-compl`, `borrow-compl`, `sep-L`, `sep-R`, `gen`.

## Assumption Source
- Canonical ledger: `docs/signed-digit-assumptions.json`.
