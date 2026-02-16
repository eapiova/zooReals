# Signed-Digit vs HoTT Reals: Proof Status

This note records the current formal status of the signed-digit equivalence work and the precise assumption points in the codebase.

## Dependency Map (Assumptions / Gaps)

- `src/Reals/SignedDigit/Equivalence.agda:1`
  Uses `--allow-unsolved-metas` at module level and re-exports the surjection path.
- `src/Reals/SignedDigit/Equivalence/Surjection.agda:1`
  Uses `--allow-unsolved-metas`.
- `src/Reals/SignedDigit/Equivalence/Surjection.agda:166`
  Postulated unbounded normalization bound (`unbounded-case-bounds`).
- `src/Reals/SignedDigit/Equivalence/Surjection.agda:181`
  Postulated unbounded normalization correctness (`unbounded-case-correct`).
- `src/Reals/SignedDigit/Equivalence/Surjection.agda:279`
  Postulated extraction of coherent stream representatives from truncated preimages (`streams-from-preimages`, coherence, correctness).
- `src/Reals/SignedDigit/Limit.agda:530`
  Postulated core technical lemma `approx-limA-close`.
- `src/Reals/SignedDigit/Limit.agda:684`
  Postulated quotient-level limit lift `limA-𝕀sd` and closeness `limA-𝕀sd-close`.
- `src/Reals/SignedDigit/Equivalence/Direct/Full.agda:65`
  Postulated round-trip laws `toℝ-fromℝ` and `fromℝ-toℝ` for the direct `ℝsd ≃ ℝ`.
- `src/Reals/SignedDigit/Equivalence/Helpers.agda:79`
  `choose-k` currently clamps and returns exponent `0`; scaling correctness is not yet established.

## Safe Branch Status

- `src/Reals/SignedDigit/Safe/Limit.agda:9`
  Documents the quotient-lift obstruction as requiring countable dependent choice (`AC_ω`).
- `src/Reals/SignedDigit/Safe/Limit.agda:37`
  Postulates `limA-𝕀sd` and `limA-𝕀sd-close` in the safe layer.
- `src/Reals/SignedDigit/Safe/Equivalence.agda:6`
  States full safe `ℝsd` exports are intentionally absent pending a genuine quotient-based safe representation.

## Conclusions (Current Base Setup)

- The repository does **not** currently contain a fully constructive proof of `ℝsd ≡ ℝ`.
- The repository does **not** currently contain a proof of `¬ (ℝsd ≡ ℝ)`.
- Assuming an equivalence witness for the interpretation map (`toℝ`) yields representation-selection principles (see `src/Reals/SignedDigit/Meta/ChoiceFromEq.agda`).
- Deriving classical principles such as LEM requires an explicit additional reflection principle (see `src/Reals/SignedDigit/Meta/LEMBoundary.agda`), not the equivalence assumption alone.
- In `Meta` APIs, this is encoded as `(H : ℝsd ≃ ℝ)` plus `equivFun H ≡ toℝ`, so results are explicitly about the repository map `toℝ`.
