import Pasta.Fields
import Pasta.Pallas

namespace Sinsemilla

/-! # GroupHash: hash-to-curve for Pallas

`GroupHash` maps a domain separator and a message (both byte strings) to a
non-identity point on the Pallas curve. It is used to derive the generators
`Q(D)` and `S(j)` for Sinsemilla.

Internally it uses the "simplified SWU" hash-to-curve algorithm (RFC 9380 §6.6.3)
with BLAKE2b-512 and a 3-isogeny from IsoPallas to Pallas. We treat it as an
**opaque function** and axiomatize only the property that matters for Sinsemilla's
security: it produces non-identity points that are indifferentiable from random
oracle outputs.

A full formalization of the hash-to-curve internals (simplified SWU map, isogeny,
BLAKE2b) would be a separate project.
-/

open Pasta

noncomputable section

/-- An opaque hash-to-curve function mapping a domain separator `D` and message `M`
(both as byte lists) to a point on the Pallas curve.

This models `GroupHash_P` from §5.4.1.9 of the Zcash protocol specification. -/
opaque groupHash (D : List UInt8) (M : List UInt8) : Pallas.toAffine.Point := by
  exact WeierstrassCurve.Affine.Point.zero

/-- `groupHash` always produces a non-identity point.

This is guaranteed by the hash-to-curve construction (simplified SWU maps
to the curve, never to the identity). It is the key property needed for
Sinsemilla's security argument. -/
axiom groupHash_ne_zero (D : List UInt8) (M : List UInt8) :
    groupHash D M ≠ WeierstrassCurve.Affine.Point.zero

/-! ## Sinsemilla generators

The Sinsemilla hash uses two families of generators derived from `groupHash`:

- `Q(D)`: the initial accumulator, derived from the domain separator `D`
- `S(j)`: 1024 base points indexed by 10-bit chunk values `j ∈ {0, ..., 1023}`
-/

/-- The initial accumulator point for domain separator `D`.

`Q(D) = GroupHash("z.cash:SinsemillaQ", D)` -/
def Q (D : List UInt8) : Pallas.toAffine.Point :=
  groupHash ("z.cash:SinsemillaQ".toUTF8.toList) D

/-- The base point for chunk value `j ∈ {0, ..., 1023}`.

`S(j) = GroupHash("z.cash:SinsemillaS", I2LEOSP₃₂(j))`

where `I2LEOSP₃₂` encodes `j` as a 4-byte little-endian integer. -/
def S (j : Fin 1024) : Pallas.toAffine.Point :=
  groupHash ("z.cash:SinsemillaS".toUTF8.toList) (i2leosp32 j.val)
where
  i2leosp32 (n : ℕ) : List UInt8 :=
    [⟨n % 256, by omega⟩, ⟨(n / 256) % 256, by omega⟩,
     ⟨(n / 65536) % 256, by omega⟩, ⟨(n / 16777216) % 256, by omega⟩]

/-- `Q(D)` is never the identity. -/
theorem Q_ne_zero (D : List UInt8) : Q D ≠ WeierstrassCurve.Affine.Point.zero :=
  groupHash_ne_zero _ _

/-- `S(j)` is never the identity. -/
theorem S_ne_zero (j : Fin 1024) : S j ≠ WeierstrassCurve.Affine.Point.zero :=
  groupHash_ne_zero _ _

end

end Sinsemilla
