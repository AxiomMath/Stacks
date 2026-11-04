module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteSubfamily

/-!
# One interval for all members of a covering of a quasi-compact object

If `E` locally has finite Tor dimension
(`Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension`), then every object `U`
of the site has a covering on each member `V` of which the restriction of `E` has Tor amplitude in
some interval `[a_V, b_V]`. When `U` is quasi-compact in the sense of
`CategoryTheory.GrothendieckTopology.IsQuasiCompactObject`, finitely many members of the covering
already generate a covering sieve, and a single interval `[a, b]` contains the Tor amplitude of the
restriction of `E` to each of them.

## Main results

* `exists_finite_covering_hasTorAmplitude_of_locallyHasFiniteTorDimension`: a finite covering
  family of a quasi-compact object together with one interval containing the Tor amplitude of the
  restriction of `E` to each of its members.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, w} (X.over U))]

attribute [local instance] sliceDerived

variable
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max u v, v, w} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- If `E` locally has finite Tor dimension and `U` is a quasi-compact object of the site, then
`U` has a finite covering family on each member of which the restriction of `E` has Tor amplitude
in one and the same interval `[a, b]`. -/
theorem exists_finite_covering_hasTorAmplitude_of_locallyHasFiniteTorDimension
    (T : ∀ U : X.C, DerivedTensorProduct.{max u v, v, w, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, v, w, d} X)
    (hE : LocallyHasFiniteTorDimension T E)
    (U : X.C) (hU : X.J.IsQuasiCompactObject U) :
    ∃ (ι : Type (max u v)) (_ : Finite ι) (V : ι → X.C) (f : ∀ i, V i ⟶ U) (a b : ℤ),
      Sieve.ofArrows V f ∈ X.J U ∧
      ∀ i, HasTorAmplitude (T (V i))
        ((RingedSite.derivedRestriction.{u, v, w, d} X (V i)).obj E) a b := by
  classical
  obtain ⟨S, hScov, hSamp⟩ := hE U
  obtain ⟨ι, hιfin, V, f, hfS, hcov⟩ :=
    GrothendieckTopology.exists_finite_ofArrows_mem_of_isQuasiCompactObject hU S hScov
  have : Finite ι := hιfin
  choose a b hab using fun i : ι => hSamp (f i) (hfS i)
  obtain ⟨a₀, ha₀⟩ := (Set.finite_range a).bddBelow
  obtain ⟨b₀, hb₀⟩ := (Set.finite_range b).bddAbove
  exact ⟨ι, hιfin, V, f, a₀, b₀, hcov, fun i =>
    (hab i).mono (ha₀ (Set.mem_range_self i)) (hb₀ (Set.mem_range_self i))⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end
