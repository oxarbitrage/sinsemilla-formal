import Sinsemilla.GroupHash
import Sinsemilla.IncompleteAdd

namespace Sinsemilla

/-! # Sinsemilla hash function specification

Sinsemilla is an elliptic-curve-based hash function designed for efficient
instantiation inside Halo 2 arithmetic circuits. It operates over the Pallas
curve and is used in Zcash's Orchard protocol for:

- Merkle tree hashing (`MerkleCRH`)
- Note commitments (`NoteCommit`)
- Key commitments (`CommitIvk`)

## Algorithm

Given a domain separator `D` (bytes) and message `M` (bits, length ≤ k·c = 2530):

1. Split `M` into `n = ⌈|M|/k⌉` chunks of `k = 10` bits each (padding the last)
2. Initialize accumulator `Acc₀ = Q(D)`
3. For each chunk `mᵢ`: `Accᵢ = (Accᵢ₋₁ ⊕ S(mᵢ)) ⊕ Accᵢ₋₁`
4. Return `Accₙ` (or extract its x-coordinate for `SinsemillaHash`)

When no exceptional case occurs (⊥ is never produced), the accumulator step
is equivalent to `Accᵢ = [2]·Accᵢ₋₁ + S(mᵢ)`, making Sinsemilla a Pedersen
vector hash with collision resistance reducible to the discrete log problem.

See §5.4.1.9 of the Zcash protocol specification.
-/

open Pasta

noncomputable section

/-- Chunk size in bits. Each chunk encodes a value in `{0, ..., 2^k - 1}`. -/
def k : ℕ := 10

/-- Maximum number of chunks. Ensures `2^n ≤ (r-1)/2` for injectivity. -/
def c : ℕ := 253

/-- Maximum message length in bits. -/
def maxMessageLength : ℕ := k * c

/-- Little-endian bit string to integer: `lebs2ip [b₀, b₁, ...] = b₀·2⁰ + b₁·2¹ + ...` -/
private def lebs2ip : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * lebs2ip rest

/-- Split a bit list into k-bit chunks, each interpreted as a little-endian integer. -/
private def chunkBits (fuel : ℕ) (bits : List Bool) : List (Fin 1024) :=
  match fuel, bits with
  | 0, _ => []
  | _, [] => []
  | fuel + 1, bits =>
    ⟨lebs2ip (bits.take k) % 1024, Nat.mod_lt _ (by omega)⟩ :: chunkBits fuel (bits.drop k)

/-- Pad a bit list to a multiple of `k` bits by appending zeros,
then split into `k`-bit chunks interpreted as little-endian integers. -/
def pad (M : List Bool) : List (Fin 1024) :=
  if M = [] then []
  else
    let rem := M.length % k
    let padded := if rem = 0 then M else M ++ List.replicate (k - rem) false
    chunkBits padded.length padded

/-- The Sinsemilla accumulator step.

`step(Acc, mᵢ) = (Acc ⊕ S(mᵢ)) ⊕ Acc`

When the result is not `⊥`, this equals `[2]·Acc + S(mᵢ)`. -/
def step (acc : Option Pallas.toAffine.Point) (mᵢ : Fin 1024) :
    Option Pallas.toAffine.Point :=
  incompleteAdd (incompleteAdd acc (some (S mᵢ))) acc

/-- `SinsemillaHashToPoint(D, M)`: the core hash function.

Returns a point on Pallas (or `none` if an exceptional case occurs).
Messages longer than `k·c = 2530` bits are rejected. -/
def hashToPoint (D : List UInt8) (M : List Bool) :
    Option Pallas.toAffine.Point :=
  if M.length > maxMessageLength then none
  else
    let chunks := pad M
    chunks.foldl step (some (Q D))

/-- `SinsemillaHash(D, M)`: extract the x-coordinate of the hash point.

Returns an element of `𝔽_p` (or `none` if the hash point is `⊥` or `𝒪`). -/
def hash (D : List UInt8) (M : List Bool) : Option Pasta.Fp :=
  hashToPoint D M >>= xCoord

/-- `SinsemillaCommit_r(D, M)`: a binding and hiding commitment scheme.

Computes `SinsemillaHashToPoint(D ‖ "-M", M) + [r] · R` where
`R = GroupHash(D ‖ "-r", "")` is a randomness base point. -/
def commit (r : Pasta.Fq) (D : List UInt8) (M : List Bool) :
    Option Pallas.toAffine.Point :=
  sorry

/-- `SinsemillaShortCommit_r(D, M)`: commitment with x-coordinate extraction. -/
def shortCommit (r : Pasta.Fq) (D : List UInt8) (M : List Bool) :
    Option Pasta.Fp :=
  commit r D M >>= xCoord

end

end Sinsemilla
