# sinsemilla-formal

**Status:** Fully proven — zero `sorry` statements.

Lean 4 formalization of the Sinsemilla hash function from Zcash's Orchard protocol, with a machine-verified security reduction to the discrete logarithm problem on the Pallas curve.

## What's formalized

Sinsemilla splits a bit message M into 10-bit chunks and accumulates elliptic curve points: Acc_{i+1} = [2]·Accᵢ + S(mᵢ), starting from Q(D) = GroupHash(D).

**Key results:**

- **`hashToPoint_pedersen`** — the hash equals [2ⁿ]·Q(D) + Σᵢ 2^(n−1−i)·S(mᵢ): a Pedersen vector commitment.
- **`chi_injective`** — distinct equal-length chunk sequences produce distinct coefficient vectors.
- **`collision_implies_sumChunks_eq`** — a collision on equal-length messages yields a DLP relation on Pallas.

## Axioms

| Axiom | Justification |
|-------|--------------|
| `groupHash_ne_zero` | Requires full SWU map + BLAKE2b formalization |

## Build

```shell
lake build
```

## Dependencies

Lean 4 (`v4.30.0-rc2`), [Mathlib4](https://github.com/leanprover-community/mathlib4), [pasta-formal](https://github.com/oxarbitrage/pasta-formal).

## References

- [Zcash Protocol Spec §5.4.1.9](https://zips.z.cash/protocol/protocol.pdf)
- [Halo 2 — Sinsemilla gadget](https://zcash.github.io/halo2/design/gadgets/sinsemilla.html)

---

## Part of a series

Six repositories formally verifying the Zcash Orchard cryptographic stack:

| Layer | Repository |
|-------|-----------|
| Curves | [pasta-formal](https://github.com/oxarbitrage/pasta-formal) |
| Hash | [poseidon-formal](https://github.com/oxarbitrage/poseidon-formal) |
| Hash-to-curve | [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal) |
| Signatures | [redpallas-formal](https://github.com/oxarbitrage/redpallas-formal) |
| Protocol | [orchard-formal](https://github.com/oxarbitrage/orchard-formal) |
| Proof system | [halo2-formal](https://github.com/oxarbitrage/halo2-formal) |
