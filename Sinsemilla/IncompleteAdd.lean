import Pasta.Fields
import Pasta.Pallas

namespace Sinsemilla

/-! # Incomplete addition on Pallas

Incomplete addition is a partial operation on Pallas curve points that
returns `none` (⊥) whenever standard addition would hit an exceptional case:

- Either input is `none`
- Either input is the identity point `𝒪`
- Both inputs have the same x-coordinate (covers both doubling and negation)

When none of these cases apply, it reduces to standard elliptic curve addition.

This mirrors the incomplete addition gadget used in Halo 2 circuits, where the
cheaper incomplete formula is used and the circuit constrains inputs to avoid
exceptional cases. Sinsemilla's security argument shows that hitting an exceptional
case implies a discrete log relation among the generators.

See §5.4.7.1 of the Zcash protocol specification.
-/

open Pasta

noncomputable section

/-- Extract the x-coordinate of a non-identity Pallas point, if available.

Returns `none` for the identity point `𝒪`. -/
def xCoord : Pallas.toAffine.Point → Option Pasta.Fp
  | .zero => none
  | .some x _ _ => some x

/-- Incomplete addition on Pallas points.

Returns `none` (⊥) if either input is `none`, either is the identity,
or both have the same x-coordinate. Otherwise returns standard addition. -/
def incompleteAdd :
    Option Pallas.toAffine.Point → Option Pallas.toAffine.Point →
    Option Pallas.toAffine.Point
  | none, _ => none
  | _, none => none
  | some .zero, _ => none
  | _, some .zero => none
  | some (.some x₁ y₁ h₁), some (.some x₂ y₂ h₂) =>
    if x₁ = x₂ then none
    else some ((.some x₁ y₁ h₁) + (.some x₂ y₂ h₂))

scoped notation:65 a " ⊕ᵢ " b => incompleteAdd a b

/-- Incomplete addition with `none` on the left is `none`. -/
@[simp]
theorem incompleteAdd_none_left (P : Option Pallas.toAffine.Point) :
    incompleteAdd none P = none := by
  rfl

/-- Incomplete addition with `none` on the right is `none`. -/
@[simp]
theorem incompleteAdd_none_right (P : Option Pallas.toAffine.Point) :
    incompleteAdd P none = none := by
  cases P with
  | none => rfl
  | some p => cases p with
    | zero => rfl
    | some x y h => rfl

/-- When incomplete addition of two definite points succeeds,
it equals standard elliptic curve addition. -/
theorem incompleteAdd_some_some_eq {P Q R : Pallas.toAffine.Point}
    (h : incompleteAdd (some P) (some Q) = some R) :
    R = P + Q := by
  cases P with
  | zero => simp [incompleteAdd] at h
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => simp [incompleteAdd] at h
    | some x₂ y₂ h₂ =>
      simp only [incompleteAdd] at h
      split at h
      · contradiction
      · simp at h; exact h.symm

end

end Sinsemilla
