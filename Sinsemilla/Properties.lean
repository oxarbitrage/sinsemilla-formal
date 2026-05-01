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
define `χ(m)ⱼ₊₁ = Σᵢ 2^(n-1-i) · δ(mᵢ, j)` for `j = 0, ..., 1023`,
where `δ` is the Kronecker delta.
-/

/-- The Kronecker delta: 1 if `a = b`, 0 otherwise. -/
def kronecker (a b : ℕ) : ℕ := if a = b then 1 else 0

@[simp]
theorem kronecker_self (a : ℕ) : kronecker a a = 1 := if_pos rfl

theorem kronecker_of_ne {a b : ℕ} (h : a ≠ b) : kronecker a b = 0 := if_neg h

theorem kronecker_le_one (a b : ℕ) : kronecker a b ≤ 1 := by
  unfold kronecker; split <;> omega

/-- The coefficient mapping `χ`, defined recursively.

`χ(m)ⱼ = Σᵢ 2^(n-1-i) · δ(mᵢ, j)` for a sequence of chunks `m` and index `j`.

Each coefficient records which chunks equal `j`, weighted by descending
powers of 2. -/
def chi : List (Fin 1024) → Fin 1024 → ℕ
  | [], _ => 0
  | mᵢ :: rest, j =>
    2 ^ rest.length * kronecker mᵢ.val j.val + chi rest j

@[simp]
theorem chi_nil (j : Fin 1024) : chi [] j = 0 := rfl

@[simp]
theorem chi_cons (a : Fin 1024) (as : List (Fin 1024)) (j : Fin 1024) :
    chi (a :: as) j = 2 ^ as.length * kronecker a.val j.val + chi as j := rfl

/-- `χ(m, j) < 2^(|m|)`: the coefficient is bounded by the number of positions. -/
theorem chi_lt_pow (m : List (Fin 1024)) (j : Fin 1024) :
    chi m j < 2 ^ m.length := by
  induction m with
  | nil => simp [chi]
  | cons a as ih =>
    simp only [chi_cons, List.length_cons]
    have hmul : 2 ^ as.length * kronecker a.val j.val ≤ 2 ^ as.length := by
      calc 2 ^ as.length * kronecker a.val j.val
          ≤ 2 ^ as.length * 1 := Nat.mul_le_mul_left _ (kronecker_le_one _ _)
        _ = 2 ^ as.length := Nat.mul_one _
    have hpow : 2 ^ (as.length + 1) = 2 ^ as.length * 2 := pow_succ 2 as.length
    omega

/-- The `χ` mapping is injective: distinct chunk sequences of equal length
produce distinct coefficient vectors.

The bound `m₁.length ≤ c` is included for specification fidelity but is not
needed for the proof over `ℕ` (it would matter over `ℤ/rℤ`). -/
theorem chi_injective (m₁ m₂ : List (Fin 1024))
    (hlen : m₁.length = m₂.length)
    (_hbound : m₁.length ≤ c)
    (heq : ∀ j : Fin 1024, chi m₁ j = chi m₂ j) :
    m₁ = m₂ := by
  induction m₁ generalizing m₂ with
  | nil =>
    cases m₂ with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases m₂ with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      have hbound' : as.length ≤ c := by
        simp [List.length_cons] at _hbound; omega
      have hab : a = b := by
        by_contra hab
        have h := heq a
        simp only [chi_cons, ← hlen'] at h
        rw [kronecker_self, kronecker_of_ne (fun he => hab (Fin.ext he.symm)),
            mul_one, mul_zero, zero_add] at h
        have := chi_lt_pow bs a
        rw [← hlen'] at this
        omega
      subst hab
      congr 1
      exact ih bs hlen' hbound' (fun j => by
        have := heq j
        simp only [chi_cons, ← hlen'] at this
        exact Nat.add_left_cancel this)

/-! ## Pedersen equivalence

When `SinsemillaHashToPoint(D, M) ≠ ⊥`, the result equals:

  `[2ⁿ] · Q(D) + Σⱼ₌₀¹⁰²³ [χ(m)ⱼ₊₁] · S(j)`

This is a Pedersen vector hash, whose collision resistance reduces to
the hardness of finding discrete log relations among the generators.

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

/-- The Sinsemilla accumulator step computes double-and-add when it succeeds:
`step(P, mᵢ) = [2]·P + S(mᵢ)`.

This is the per-step Pedersen equivalence: each accumulator step is a
doubling of the current accumulator plus the chunk generator. -/
theorem step_eq_double_add {P : Pallas.toAffine.Point} {mᵢ : Fin 1024}
    {R : Pallas.toAffine.Point}
    (h : step (some P) mᵢ = some R) :
    R = 2 • P + S mᵢ := by
  unfold step at h
  cases hmid : incompleteAdd (some P) (some (S mᵢ)) with
  | none => rw [hmid] at h; simp at h
  | some M =>
    rw [hmid] at h
    have hM : M = P + S mᵢ := incompleteAdd_some_some_eq hmid
    have hR : R = M + P := incompleteAdd_some_some_eq h
    rw [hR, hM, two_nsmul]; abel

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
