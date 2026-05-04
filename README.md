# sinsemilla-formal

**Status:** Fully proven — zero `sorry` statements.

A Lean 4 formalization of the Sinsemilla hash function from Zcash's Orchard protocol, with a
machine-verified security reduction to the discrete logarithm problem on the Pallas curve.

## Overview

Sinsemilla is an elliptic-curve-based hash function designed for efficient instantiation inside
Halo 2 arithmetic circuits. Unlike generic hash functions, Sinsemilla is defined directly over
curve arithmetic: it accumulates 10-bit message chunks into a running elliptic curve point using
only additions — no multiplications — making it amenable to lookup-table-based circuit gadgets.

In Zcash's Orchard protocol, Sinsemilla is the primitive underlying three distinct applications:
Merkle tree hashing (`MerkleCRH`), note commitments (`NoteCommit`), and key commitments
(`CommitIvk`). Each application uses a domain-separated instance so the same circuit gadget can
be reused across contexts. The commitment variants (`SinsemillaCommit`,
`SinsemillaShortCommit`) augment the hash with a randomness term `[r]·R` to achieve hiding.

Circuit-friendliness is the design's primary constraint. Because Halo 2 proofs are most
efficient when the prover can use precomputed lookup tables, the Sinsemilla step function is
arranged so that each chunk contributes a generator `S(mᵢ)` drawn from a fixed table of 1024
points. The accumulation rule `Accᵢ = (Accᵢ₋₁ + S(mᵢ)) + Accᵢ₋₁` avoids scalar multiplications
entirely; instead the doubling is implicit in the double-and-add interpretation. This
formalization proves that this iterative rule is mathematically equivalent to a standard Pedersen
vector commitment, establishing a clean reduction from collision resistance to the discrete
logarithm problem.

## Mathematical Background

### Sinsemilla Construction

Let 𝔾 be the Pallas group with group law written additively. Fix chunk size `k = 10` and maximum
chunk count `c = 253` (so messages are at most `k·c = 2530` bits).

**Generators** (derived via `GroupHash` / simplified SWU hash-to-curve):

- `Q(D) = GroupHash("z.cash:SinsemillaQ", D)` — domain-dependent initial accumulator
- `S(j) = GroupHash("z.cash:SinsemillaS", I2LEOSP₃₂(j))` for j ∈ {0, …, 1023} — chunk base points

Both families are proven non-identity: `Q_ne_zero` and `S_ne_zero` follow from the single axiom
`groupHash_ne_zero`.

**Message encoding.** A bit string `M` of length ≤ 2530 is right-zero-padded to a multiple of
`k` bits, then split into `n = ⌈|M|/k⌉` chunks, each interpreted as a little-endian integer
`mᵢ ∈ {0, …, 1023}`.

**Accumulation.** Starting from `Acc₀ = Q(D)`, each chunk advances the state via:

```
Accᵢ = (Accᵢ₋₁ ⊕ᵢ S(mᵢ)) ⊕ᵢ Accᵢ₋₁
```

where `⊕ᵢ` is *incomplete addition* — standard affine addition when both inputs are distinct
non-identity points with different x-coordinates, and ⊥ (abort) otherwise.

**Pedersen equivalence.** When no exceptional case occurs (every `⊕ᵢ` succeeds):

```
hashToPoint(D, M) = [2ⁿ]·Q(D) + Σᵢ₌₀ⁿ⁻¹ 2^(n-1-i)·S(mᵢ)
                  = [2ⁿ]·Q(D) + Σⱼ₌₀¹⁰²³ χ(m)ⱼ·S(j)
```

The equivalence `[2]·Accᵢ₋₁ + S(mᵢ)` for each step follows from the algebraic identity
`(P + Q) + P = [2]P + Q` applied to the two incomplete additions. This is proven per-step in
`step_eq_double_add` and unrolled over the full chunk list in `foldl_step_pedersen`.

### Security Argument

**The χ function.** For a chunk sequence `m = (m₀, …, mₙ₋₁)` and index `j ∈ {0, …, 1023}`,
define:

```
χ(m)ⱼ = Σᵢ₌₀ⁿ⁻¹ 2^(n-1-i) · δ(mᵢ, j)
```

where δ is the Kronecker delta. This maps the chunk sequence to a vector of non-negative integer
coefficients, recording — with position-dependent weights — how many times each generator index
appears. The key bound `χ(m)ⱼ < 2ⁿ` (proven as `chi_lt_pow`) ensures that the weighted counts
remain distinct across positions.

**χ injectivity** (`chi_injective`). For equal-length chunk sequences `m₁`, `m₂`:

```
(∀ j, χ(m₁)ⱼ = χ(m₂)ⱼ)  →  m₁ = m₂
```

The proof proceeds by induction on the list length. At each step, the leading coefficient
`χ(m)_{m₀} = 2^(n-1) + χ(tail m)_{m₀}` is strictly larger than any χ value reachable by the
tail alone (by `chi_lt_pow`), so the head element is forced to be equal, and the induction
hypothesis closes the rest.

**Collision resistance.** Suppose `hashToPoint(D, M₁) = hashToPoint(D, M₂) = some R` with
`(pad M₁).length = (pad M₂).length`. By `hashToPoint_pedersen` applied to both sides:

```
[2ⁿ]·Q(D) + Σⱼ χ(pad M₁)ⱼ·S(j) = [2ⁿ]·Q(D) + Σⱼ χ(pad M₂)ⱼ·S(j)
```

Cancelling `[2ⁿ]·Q(D)` (proven in `collision_implies_sumChunks_eq`):

```
Σⱼ (χ(pad M₁)ⱼ − χ(pad M₂)ⱼ)·S(j) = 𝒪
```

If `pad M₁ ≠ pad M₂`, this is a non-trivial integer linear combination of distinct group
generators that equals the identity — a discrete logarithm relation on Pallas. Under DLP
hardness, this is computationally infeasible, so `pad M₁ = pad M₂` (and by `chi_injective`,
the chunk sequences are identical). The length constraint is essential: Sinsemilla is *not*
designed to be collision-resistant across messages of different padded lengths.

## Formalization

### `Sinsemilla/GroupHash.lean`

Declares `groupHash : List UInt8 → List UInt8 → Pallas.Point` as an `opaque` constant (its
body is an unreachable default), accompanied by the single axiom:

```
axiom groupHash_ne_zero (D M : List UInt8) : groupHash D M ≠ 𝒪
```

This axiomatizes the property that the simplified SWU hash-to-curve map never lands on the
identity. The full construction (SWU map, 3-isogeny from IsoPallas, BLAKE2b-512) is not
formalized here; that would constitute a separate project. The generators `Q(D)` and `S(j)` are
defined as applications of `groupHash`, and `Q_ne_zero` / `S_ne_zero` are derived as theorems
from `groupHash_ne_zero` — they are not additional axioms.

### `Sinsemilla/IncompleteAdd.lean`

Defines `incompleteAdd : Option Pallas.Point → Option Pallas.Point → Option Pallas.Point`,
which returns `none` if either input is `none`, either is the identity, or both share the same
x-coordinate (covering both the doubling and negation exceptional cases). Otherwise it reduces
to standard affine addition. The notation `⊕ᵢ` is introduced for readability.

The key theorem `incompleteAdd_some_some_eq` establishes that when incomplete addition of two
definite non-exceptional points succeeds, the result equals their standard sum. This theorem
bridges the circuit-level partial operation to the mathematical group law and is the foundation
for `step_eq_double_add`.

### `Sinsemilla/Spec.lean`

Contains the full executable specification:

| Definition | Description |
|---|---|
| `k = 10`, `c = 253` | Chunk size and maximum chunk count |
| `lebs2ip` | Little-endian bit string to natural number |
| `chunkBits` / `pad` | Pad and split message into `Fin 1024` chunks |
| `step acc mᵢ` | `(acc ⊕ᵢ S mᵢ) ⊕ᵢ acc` — one accumulator step |
| `hashToPoint D M` | `foldl step (some (Q D)) (pad M)`, or `none` if `|M| > 2530` |
| `hash D M` | x-coordinate of `hashToPoint D M` |
| `commit r D M` | `hashToPoint(D‖"-M", M) + [r]·GroupHash(D‖"-r", "")` |
| `shortCommit r D M` | x-coordinate of `commit r D M` |

### `Sinsemilla/Properties.lean`

Contains the security-relevant theorems, structured in three layers:

1. **χ layer** — `kronecker`, `chi`, `chi_lt_pow`, `chi_injective`
2. **Pedersen layer** — `sumChunks`, `step_eq_double_add`, `foldl_step_pedersen`, `hashToPoint_pedersen`
3. **Collision layer** — `collision_implies_sumChunks_eq`

## Key Results

### Theorem: Pedersen Equivalence (`hashToPoint_pedersen`)

```
∀ (D : List UInt8) (M : List Bool) (R : Pallas.Point),
  hashToPoint D M = some R →
  R = [2ⁿ]·Q(D) + Σᵢ₌₀ⁿ⁻¹ 2^(n-1-i)·S((pad M)ᵢ)
```

where `n = (pad M).length`. This is the headline result: Sinsemilla computes a Pedersen vector
commitment over the `S(j)` generator table, with the initial accumulator `Q(D)` contributing a
fixed scalar multiple.

### Theorem: χ Injectivity (`chi_injective`)

```
∀ (m₁ m₂ : List (Fin 1024)),
  m₁.length = m₂.length →
  m₁.length ≤ c →
  (∀ j : Fin 1024, χ(m₁, j) = χ(m₂, j)) →
  m₁ = m₂
```

Distinct equal-length chunk sequences map to distinct coefficient vectors over ℕ. The length
bound `≤ c` appears for specification fidelity (it would be necessary over ℤ/rℤ where the
coefficients could wrap) but is not used in the ℕ proof.

### Theorem: Collision → DLP (`collision_implies_sumChunks_eq`)

```
∀ (D : List UInt8) (M₁ M₂ : List Bool) (R : Pallas.Point),
  hashToPoint D M₁ = some R →
  hashToPoint D M₂ = some R →
  (pad M₁).length = (pad M₂).length →
  sumChunks (pad M₁) = sumChunks (pad M₂)
```

A hash collision on equal-length messages forces the weighted generator sums to be equal. If
`pad M₁ ≠ pad M₂`, this yields the relation `Σⱼ (χ(pad M₁)ⱼ − χ(pad M₂)ⱼ)·S(j) = 𝒪`
— a non-trivial discrete logarithm relation on Pallas.

## Axioms

| Axiom | File | Justification |
|---|---|---|
| `groupHash_ne_zero` | `GroupHash.lean` | Requires full formalization of the simplified SWU map, 3-isogeny, and BLAKE2b-512 over Pallas — a separate project |

`Q_ne_zero` and `S_ne_zero` are derived theorems, not axioms. Beyond `groupHash_ne_zero`, the
proof relies only on Lean 4's kernel and Mathlib's algebraic hierarchy (no additional `sorry`,
`native_decide`, or `unsafe`).

## Scope

This formalization covers the **protocol-level** Sinsemilla specification
([§5.4.1.9](https://zips.z.cash/protocol/protocol.pdf#concretesinsemillahash)). The Halo 2
circuit gadget implementing Sinsemilla uses additional optimizations — running-sum chunk
decomposition, the `Y = 2y` coordinate trick, lookup tables, and selector logic — that are not
part of this formalization.

## Dependencies

- **Lean 4** (v4.30.0-rc2)
- **Mathlib4** — elliptic curve group law, `smul`, `abel`, field tactics
- **[pasta-formal](https://github.com/oxarbitrage/pasta-formal)** — Pallas curve definition, Fp/Fq fields, and primality proofs

## Building

Requires [elan](https://github.com/leanprover/elan). The correct Lean toolchain is pinned in
`lean-toolchain` and installed automatically.

```shell
lake update   # fetch Mathlib + pasta-formal (~3 GB of cached oleans)
lake build    # compiles in ~10 seconds after cache download
```

## References

- [Zcash Protocol Specification §5.4.1.9](https://zips.z.cash/protocol/protocol.pdf#concretesinsemillahash) — Sinsemilla Hash to Point and SinsemillaCommit
- [Halo 2 book — Sinsemilla gadget](https://zcash.github.io/halo2/design/gadgets/sinsemilla.html) — circuit-level design with running-sum optimization
- [ZIP 224 — Orchard Shielded Protocol](https://zips.z.cash/zip-0224) — Orchard deployment context for Sinsemilla
- [pasta-formal](https://github.com/oxarbitrage/pasta-formal) — Lean 4 formalization of the Pallas/Vesta curves
- [zcash/orchard](https://github.com/zcash/orchard) — reference Rust implementation
