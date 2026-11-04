module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.ProfiniteSpectrum
public import StacksCore.Tactic.StacksAttribute

/-!
# Closed points above a closed-point ideal after an algebraic residue extension

Let `A` be a ring whose closed points in `Spec A` are cut out by an ideal `I`, and let
`A → B` be a ring map inducing algebraic extensions of residue fields. Every prime of `B`
containing the extended ideal `IB` is then a closed point of `Spec B`.

## Main results

* `AlgebraicGeometry.ProEtale.closedPoints_of_mem_zeroLocus_map`: the zero locus of `IB` is
  contained in the closed points of `Spec B`.

## Implementation notes

The hypothesis is an equality of the zero locus of `I` with the set of closed points of
`Spec A`; radicality of `I` is not needed, since only its zero locus enters. W-locality of
`Spec A` is likewise not needed for this statement, so it is not assumed.

## References

* [Stacks Project, Tag 097A](https://stacks.math.columbia.edu/tag/097A)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

open TopologicalSpace

/-- **Stacks 097A, part (1).** Let `I` be an ideal of `A` whose zero locus is the set of closed
points of `Spec A`, and let `f : A →+* B` induce algebraic extensions of residue fields. Then
every prime of `B` containing the extended ideal `I B` is a closed point of `Spec B`. -/
@[stacks 097A "part (1)"]
theorem closedPoints_of_mem_zeroLocus_map
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A)
    (hzero : PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))
    (halg : ∀ q : Ideal B, ∀ [q.IsPrime],
      letI := (Ideal.ResidueField.map (q.comap f) q f rfl).toAlgebra
      Algebra.IsAlgebraic (q.comap f).ResidueField q.ResidueField) :
    PrimeSpectrum.zeroLocus (Ideal.map f I : Set B) ⊆ closedPoints (PrimeSpectrum B) := by
  intro q hq
  have : q.asIdeal.IsPrime := q.isPrime
  have hpclosed : IsClosed ({PrimeSpectrum.comap f q} : Set (PrimeSpectrum A)) :=
    mem_closedPoints_iff.mp (hzero.subset (Ideal.map_le_iff_le_comap.mp hq))
  have : (q.asIdeal.comap f).IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hpclosed
  have hqm : q.asIdeal.IsMaximal := by
    let := (Ideal.ResidueField.map (q.asIdeal.comap f) q.asIdeal f rfl).toAlgebra
    have : Algebra.IsAlgebraic (q.asIdeal.comap f).ResidueField q.asIdeal.ResidueField :=
      halg q.asIdeal
    exact isMaximal_of_isAlgebraic_residueField f (m := q.asIdeal.comap f) (q := q.asIdeal) rfl
      (by simp [RingHom.algebraMap_toAlgebra])
  exact mem_closedPoints_iff.mpr ((PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mpr hqm)

end AlgebraicGeometry.ProEtale

end
