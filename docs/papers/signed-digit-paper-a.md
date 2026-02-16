# Paper A Outline: Constructive Boundary for Signed-Digit Reals

## Scope
- Primary result: In `--safe`, raw-stream limit machinery is constructive.
- Boundary result: quotient-level lifting to `𝕀sd` requires `AC_ω`.
- Logical boundary: assuming `H : ℝsd ≃ ℝ` for repository `toℝ` yields section/selection principles; LEM still needs extra reflection.

## Formal Anchors
- `src/Reals/SignedDigit/Safe/Limit/Core.agda`
- `src/Reals/SignedDigit/Safe/Limit.agda`
- `src/Reals/SignedDigit/Meta/AssumeEq.agda`
- `src/Reals/SignedDigit/Meta/ChoiceFromEq.agda`
- `src/Reals/SignedDigit/Meta/LEMBoundary.agda`
- `src/Reals/SignedDigit/PaperA/Entrypoint.agda`

## Main Theorem Package
- Constructive: `limA`, `limA-eq`, `limA-close-to-input`.
- Conditional (`AC_ω`): `limA-𝕀sd`, `limA-𝕀sd-close`.
- Conditional equivalence-boundary modules: `AssumeEq`, `ChoiceFromEq`.
- Reflection boundary: `lem-from-eq-and-reflection`.

## Non-Claims
- No claim of full constructive `ℝsd ≃ ℝ` in current repository state.
- No claim of quotient-lifted limit without explicit assumptions.

## Assumption Source
- Canonical ledger: `docs/signed-digit-assumptions.json`.
