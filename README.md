# sinsemilla-formal

Lean 4 formalization of the [Sinsemilla](https://zcash.github.io/orchard/design/commitments/sinsemilla.html) hash function used in Zcash's [Orchard](https://zcash.github.io/orchard/) protocol.

**Status: fully proven — zero `sorry`.**

## What's formalized

All definitions and theorems live under the `Sinsemilla` namespace. Built on top of [pasta-formal](https://github.com/oxarbitrage/pasta-formal).

| Component | File | Description |
|-----------|------|-------------|
| GroupHash (opaque) | `Sinsemilla/GroupHash.lean` | Hash-to-curve via simplified SWU, axiomatized as producing non-identity points |
| Q(D), S(j) generators | `Sinsemilla/GroupHash.lean` | Domain accumulator and 1024 chunk base points, with non-identity proofs |
| Incomplete addition | `Sinsemilla/IncompleteAdd.lean` | Partial EC addition returning `none` on exceptional cases, with simp lemmas |
| SinsemillaHashToPoint | `Sinsemilla/Spec.lean` | Core hash: pad, chunk, accumulate via `(Acc + S(m)) + Acc` |
| SinsemillaHash | `Sinsemilla/Spec.lean` | x-coordinate extraction of hash point |
| SinsemillaCommit | `Sinsemilla/Spec.lean` | Binding commitment: `HashToPoint(D‖"-M", M) + [r]·GroupHash(D‖"-r", "")` |
| SinsemillaShortCommit | `Sinsemilla/Spec.lean` | x-coordinate extraction of commitment |
| Kronecker delta | `Sinsemilla/Properties.lean` | Helper with `kronecker_self`, `kronecker_of_ne`, `kronecker_le_one` |
| Coefficient mapping chi | `Sinsemilla/Properties.lean` | `chi(m, j) = sum of 2^(n-1-i) * delta(m_i, j)` |
| chi bound | `Sinsemilla/Properties.lean` | `chi(m, j) < 2^|m|` — proven by induction |
| **chi injectivity** | `Sinsemilla/Properties.lean` | Distinct equal-length chunk sequences produce distinct coefficient vectors |
| sumChunks | `Sinsemilla/Properties.lean` | Weighted sum of chunk generators `Σᵢ 2^(n-1-i)·S(mᵢ)` |
| hashToPoint definedness | `Sinsemilla/Properties.lean` | Non-none hash implies existence of a point |
| step double-and-add | `Sinsemilla/Properties.lean` | `step(P, mᵢ) = [2]·P + S(mᵢ)` when step succeeds |
| foldl unrolling | `Sinsemilla/Properties.lean` | `foldl step P chunks = [2^n]·P + sumChunks(chunks)` when it succeeds |
| **Pedersen equivalence** | `Sinsemilla/Properties.lean` | `hashToPoint(D, M) = [2^n]·Q(D) + sumChunks(pad M)` — full Pedersen vector hash equivalence |
| **Collision → equal sums** | `Sinsemilla/Properties.lean` | Hash collision implies equal Pedersen generator sums; with distinct pads this yields a DLP relation |

## Security argument

Sinsemilla's collision resistance reduces to the discrete logarithm problem on Pallas:

1. **chi injectivity** (proven): the coefficient mapping from chunk sequences to column-sum vectors is injective, so distinct messages produce distinct Pedersen hash inputs.
2. **Pedersen equivalence** (proven): when no exceptional case occurs, `hashToPoint(D, M) = [2^n]·Q(D) + sumChunks(pad M)`, a Pedersen vector hash whose collision resistance reduces to DLP.
3. **Exceptional case security** (documented): if the hash ever returns `none`, one can efficiently extract a discrete log relation among the generators.

See section 5.4.1.9 of the [Zcash protocol specification](https://zips.z.cash/protocol/protocol.pdf).

## Building

Requires [elan](https://github.com/leanprover/elan). The correct Lean toolchain is installed automatically.

```sh
lake update    # fetch Mathlib + pasta-formal (~3 GB of cached oleans)
lake build     # builds in ~10 seconds after cache download
```

## Dependencies

- **Lean 4** (v4.30.0-rc2)
- **Mathlib4** — elliptic curve library, group law, tactics
- **[pasta-formal](https://github.com/oxarbitrage/pasta-formal)** — Pallas/Vesta curve definitions and primality proofs

## References

- [Sinsemilla design](https://zcash.github.io/orchard/design/commitments/sinsemilla.html) — hash function design rationale
- [Zcash protocol specification, section 5.4.1.9](https://zips.z.cash/protocol/protocol.pdf) — formal specification
- [zcash/orchard](https://github.com/zcash/orchard) — Rust implementation
- [pasta-formal](https://github.com/oxarbitrage/pasta-formal) — Pallas/Vesta Lean 4 formalization
