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
- Terminality map and uniqueness exposed conditionally via postulates, with semantics valued in the bounded interval `ℝ[-1,1]`.

## Stable Naming Contract
- Frozen by `src/Reals/SignedDigit/PaperB/Entrypoint.agda`.
- Canonical names: `inc⁻¹`, `inc⁰`, `inc⁺¹`, `dec⁺¹`, `dec⁰`, `dec⁻¹`, `carry-compl`, `borrow-compl`, `sep-L`, `sep-R`, `gen`.

## Quotient Model Status

`𝕀sd-Alg` has **14/18 fields proved**. The 4 remaining postulates are:
- `carry-compl-𝕀`, `borrow-compl-𝕀` (completeness, `Structure.agda:100–101`)
- `sep-L-𝕀`, `sep-R-𝕀` (separation, `Structure.agda:104–105`)

Recent: `inc-resp`, `dec-resp`, `carry-raw`, `borrow-raw` proved in `IncDec.agda` via `inc-sem`/`dec-sem` approximation bounds + `cons-resp` (`ConsResp.agda`).

## Terminality Status

- Bounded codomain interface is shared via `src/Reals/SignedDigit/Interval.agda`.
- `src/Reals/SignedDigit/HCIT/Terminality.agda` keeps these postulates:
  - `sem`, `sem-cons`, `sem-𝕀sd` (`ac-omega`)
  - `ι⁻¹`, `ι-section` (`semantic-arithmetic`)
  - `morph-is-hom`, `morph-unique` (`ac-omega`)
- `ι-retract` is derived (not postulated) from `ι-section` and `ι-inj`.

## Assumption Source
- Canonical ledger: `docs/signed-digit-assumptions.json`.
