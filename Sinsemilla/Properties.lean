import Sinsemilla.Spec

namespace Sinsemilla

/-! # Security properties of Sinsemilla

The security of Sinsemilla rests on the discrete logarithm assumption in the
Pallas group. The key results are:

1. **Injectivity of the coefficient mapping `χ`**: the function that maps a
   chunk sequence to its "column-sum" representation is injective. This ensures
   that distinct messages produce distinct Pedersen hash inputs.

2. **Pedersen equivalence**: when no exceptional case occurs,
   `SinsemillaHashToPoint(D, M)` equals `[2ⁿ]·Q(D) + Σⱼ [χ(m)ⱼ₊₁]·S(j)`,
   a Pedersen vector hash whose collision resistance reduces to DLP.

3. **Exceptional case implies DLP**: if `SinsemillaHashToPoint` returns `⊥`
   for any input, one can efficiently extract a nontrivial discrete log relation
   among the generators `Q(D), S(0), ..., S(1023)`.

See §5.4.1.9 and the Sinsemilla security argument in the Zcash protocol spec.
-/

open Pasta

noncomputable section

/-! ## The coefficient mapping χ

For a sequence of chunks `m = (m₁, ..., mₙ)` with `mᵢ ∈ {0, ..., 1023}`,
define `χ(m)ⱼ₊₁ = Σᵢ 2^(n-i) · δ(mᵢ, j)` for `j = 0, ..., 1023`,
where `δ` is the Kronecker delta.
-/

/-- The Kronecker delta: 1 if `a = b`, 0 otherwise. -/
def kronecker (a b : ℕ) : ℕ := if a = b then 1 else 0

/-- The coefficient mapping `χ`.

`χ(m)ⱼ = Σᵢ 2^(n-1-i) · δ(mᵢ, j)` for a sequence of chunks `m` and index `j`.

Each coefficient records which chunks equal `j`, weighted by descending
powers of 2. -/
def chi (m : List (Fin 1024)) (j : Fin 1024) : ℕ :=
  go m.length m 0
where
  go : ℕ → List (Fin 1024) → ℕ → ℕ
    | _, [], _ => 0
    | n, mᵢ :: rest, i =>
      2 ^ (n - 1 - i) * kronecker mᵢ.val j.val + go n rest (i + 1)

/-- The `χ` mapping is injective: distinct chunk sequences produce distinct
coefficient vectors.

This follows from the fact that `2^n ≤ 2^c ≤ (r-1)/2`, so the weighted
column sums do not overflow modulo `r`, and the matrix of Kronecker deltas
uniquely determines the chunk sequence. -/
theorem chi_injective (m₁ m₂ : List (Fin 1024))
    (hlen : m₁.length = m₂.length)
    (hbound : m₁.length ≤ c)
    (heq : ∀ j : Fin 1024, chi m₁ j = chi m₂ j) :
    m₁ = m₂ := by
  sorry

/-! ## Pedersen equivalence

When `SinsemillaHashToPoint(D, M) ≠ ⊥`, the result equals:

  `[2ⁿ] · Q(D) + Σⱼ₌₀¹⁰²³ [χ(m)ⱼ₊₁] · S(j)`

This is a Pedersen vector hash, whose collision resistance reduces to
the hardness of finding discrete log relations among the generators.

The full formal statement requires scalar multiplication on Pallas points,
which is left to future work.
-/

/-- When no exceptional case occurs, `SinsemillaHashToPoint` produces a
definite point — a prerequisite for the Pedersen equivalence. -/
theorem hashToPoint_some_of_ne_none (D : List UInt8) (M : List Bool)
    (_hlen : M.length ≤ maxMessageLength)
    (hne : hashToPoint D M ≠ none) :
    ∃ P : Pallas.toAffine.Point, hashToPoint D M = some P := by
  cases h : hashToPoint D M with
  | none => exact absurd h hne
  | some P => exact ⟨P, rfl⟩

/-! ## Collision resistance

For a fixed domain separator `D` and fixed input length, finding two distinct
messages `M ≠ M'` such that `SinsemillaHash(D, M) = SinsemillaHash(D, M') ≠ ⊥`
yields a nontrivial discrete log relation among `Q(D), S(0), ..., S(1023)`.
-/

/-! ## Exceptional case security

If `SinsemillaHashToPoint(D, M) = ⊥` for any `(D, M)`, then one can
efficiently extract a nontrivial discrete log relation among the generators.

An exceptional case occurs only when the accumulator `Accᵢ₋₁` equals `±S(mᵢ)`
or when `Accᵢ₋₁ + S(mᵢ) = -Accᵢ₋₁`. -/

end

end Sinsemilla
