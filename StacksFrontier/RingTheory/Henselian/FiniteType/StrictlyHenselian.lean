module

public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian.EtaleSectionIdempotent
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian.FiniteIdempotent
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian.HenselianPairRootLift
public import StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian.ProductDecomposition

/-!
# Finite type algebras over a strictly henselian local ring

Let `(R, m, κ)` be a strictly henselian local ring and let `S` be a finite type
`R`-algebra.  Then there exist a natural number `n`, finite local `R`-algebras
`A₁, …, Aₙ`, and an `R`-algebra `B`, together with an isomorphism of `R`-algebras

  `S ≅ A₁ × ⋯ × Aₙ × B`,

such that:

1. each `Aᵢ` is a local ring and is finite over `R` (finite as an `R`-module), and the
   structure map `R → Aᵢ` is a local ring homomorphism;
2. for each `i`, the induced residue field extension `κ → κ(m_{Aᵢ})` is finite purely
   inseparable;
3. `R → B` is not quasi-finite at any prime of `B` lying over `m`: for every prime
   `q ⊆ B` lying over `m`, `R → B` is not quasi-finite at `q`.

## Conventions

All rings are commutative with unit.  An `R`-algebra is a commutative ring with a ring
homomorphism from `R`.

A local ring `(R, m, κ)` is *henselian* if Hensel's lemma holds; in Mathlib,
`HenselianLocalRing R`.  It is *strictly henselian* if, in addition, its residue field
`κ = R/m` is separably algebraically closed, i.e. `IsSepClosed (IsLocalRing.ResidueField R)`.
(An algebraically closed residue field is a special case via `IsSepClosed.of_isAlgClosed`.)

An `R`-algebra `S` is of *finite type* (`Algebra.FiniteType R S`) if it is finitely
generated as an `R`-algebra.  An `R`-algebra `A` is *finite* (`Module.Finite R A`) if it is
finitely generated as an `R`-module.

For an `R`-algebra `S` and a prime `q ⊆ S`, `R → S` is *quasi-finite at* `q`
(`Algebra.QuasiFiniteAt R q`) when the localization `S_q` is a quasi-finite `R`-algebra.
Condition (3) is the negation `¬ Algebra.QuasiFiniteAt R q` ranging over all primes `q` of
`B` with `q ∩ R = m` (i.e. `q.LiesOver m`).

Since `R → Aᵢ` is finite with `Aᵢ` local, it is a local homomorphism, so it induces a field
homomorphism on residue fields `κ = κ(m) → κ(m_{Aᵢ})` via `IsLocalRing.ResidueField.map`.
This gives `κ(m_{Aᵢ})` the structure of a `κ`-algebra (here installed by `letI` from
`(ResidueField.map (algebraMap R (A i))).toAlgebra`).  Statement (2) asserts that this
extension is finite (`Module.Finite κ κ(m_{Aᵢ})`) and purely inseparable
(`IsPurelyInseparable κ κ(m_{Aᵢ})`).  Finiteness is automatic from finiteness of `Aᵢ` over
`R`; the substantive content is pure inseparability, which follows from `κ` being separably
closed.

## Implementation notes

The finite product `A₁ × ⋯ × Aₙ` is formalized as a dependent product `∀ i : Fin n, A i`
over a family `A : Fin n → Type` of `R`-algebras, and the full decomposition as an
`R`-algebra isomorphism `S ≃ₐ[R] (∀ i, A i) × B`.  The cases `n = 0` (empty product) and
`B = 0` are both permitted, matching the Stacks statement.

The only content `06DD` adds over `04GE` (the henselian-only version) is the purely
inseparable conclusion (2).

## References

* [Stacks Project, Tag 06DD](https://stacks.math.columbia.edu/tag/06DD)
* [Stacks Project, Tag 04GE](https://stacks.math.columbia.edu/tag/04GE)

## Contents

The results are split into the following files:

* `StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian.EtaleSectionIdempotent`
* `StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian.FiniteIdempotent`
* `StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian.HenselianPairRootLift`
* `StacksFrontier.RingTheory.Henselian.FiniteType.StrictlyHenselian.ProductDecomposition`
-/
