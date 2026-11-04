module

public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.RestrictionOfEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.UniformInterval
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude in a fixed interval descends along a covering family

Let `(C, O)` be a ringed site, `T` a derived tensor product on `D(O)` and `T'` a family of
derived tensor products on the slices. If `V : ι → C` is a family of objects covering the final
object of the site and the restriction of an object `E` of `D(O)` to the localization at each
`V i` has Tor amplitude in one and the same interval `[a, b]`, then `E` itself has Tor amplitude
in `[a, b]`. Consequently, when the site has a quasi-compact terminal object, an object of
locally finite Tor dimension has finite Tor dimension.

## Main results

* `Stacks.SheafOfModules.isZero_of_coversTop`: a sheaf of modules whose restrictions to the
  members of a covering family all vanish is zero.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_coversTop`: Tor amplitude in a
  fixed interval on the members of a covering family gives it on the object covered.
* `DerivedTensorProduct.hasFiniteTorDimension_of_locallyHasFiniteTorDimension`: locally finite
  Tor dimension is finite Tor dimension over a quasi-compact terminal object.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 03TT](https://stacks.math.columbia.edu/tag/03TT)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe t u v w c d

namespace Stacks.SheafOfModules

/-- **Vanishing of a sheaf of modules is local on the site.** If `V : ι → C` is a family of
objects covering the final object of the site and the restriction of `M` to the slice over each
`V i` is zero, then `M` is zero. -/
theorem isZero_of_coversTop {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} {ι : Type t} {V : ι → C} (hV : J.CoversTop V)
    (M : _root_.SheafOfModules.{w} R) (h : ∀ i, IsZero (M.over (V i))) : IsZero M := by
  have hiso : IsIso (0 : M ⟶ M) := by
    refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_over hV _ fun i => ?_
    have hz : (0 : M ⟶ M).over (V i) = 0 := Functor.map_zero _ _ _
    rw [hz, (h i).eq_of_src 0 (𝟙 _)]
    infer_instance
  rw [IsZero.iff_id_eq_zero]
  have h0 : 𝟙 M = (0 : M ⟶ M) ≫ inv (0 : M ⟶ M) := (IsIso.hom_inv_id _).symm
  rw [zero_comp] at h0
  exact h0

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{c, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)]
  [∀ U : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max c u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{max c u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor
  OfEssentiallySmall.sliceTensorAdditive OfEssentiallySmall.sliceTensorObjAdditive
  OfEssentiallySmall.sliceHasMapBifunctor

variable [HasDerivedCategory.{d} (RingedSite.Modules.{c, u, u} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max c u, u, u} (X.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived
  OfEssentiallySmall.sliceHasDerivedCategory

/-- **Tor amplitude in a fixed interval descends along a covering family.** Let `V : ι → C` be a
family of objects covering the final object of the site. If the restriction of `E` to the
localized ringed site at each `V i` has Tor amplitude in `[a, b]`, measured against the derived
tensor product `T' (V i)` on that slice, then `E` has Tor amplitude in `[a, b]` for `T`. -/
@[stacks 08FZ "the descent of tor amplitude in a fixed interval from a covering family to the \
object covered"]
theorem hasTorAmplitude_of_coversTop
    (T : DerivedTensorProduct.{c, u, u, d} X)
    (T' : ∀ U : X.C, DerivedTensorProduct.{max c u, u, u, d} (X.over U))
    {ι : Type t} {V : ι → X.C} (hV : X.J.CoversTop V)
    (E : RingedSite.DerivedModules.{c, u, u, d} X) (a b : ℤ)
    (hamp : ∀ i, HasTorAmplitude (T' (V i))
      ((RingedSite.derivedRestriction.{c, u, u, d} X (V i)).obj E) a b) :
    HasTorAmplitude T E a b := by
  intro G n hn
  refine Stacks.SheafOfModules.isZero_of_coversTop hV _ fun i => ?_
  have hz := OfEssentiallySmall.isZero_homology_derivedRestriction_tensorModule
    X (V i) T (T' (V i)) E a b (hamp i) G n hn
  exact hz.of_iso ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O) (V i)) n).app _).symm

/-- **On a quasi-compact site, locally finite Tor dimension is finite Tor dimension.** If the
site has a terminal object which is quasi-compact in the sense of Stacks 090H and `E` locally has
finite Tor dimension, then `E` has finite Tor dimension. -/
@[stacks 08FZ "on a quasi-compact site, locally finite tor dimension is finite tor dimension"]
theorem hasFiniteTorDimension_of_locallyHasFiniteTorDimension
    (T : DerivedTensorProduct.{c, u, u, d} X)
    (T' : ∀ U : X.C, DerivedTensorProduct.{max c u, u, u, d} (X.over U))
    (E : RingedSite.DerivedModules.{c, u, u, d} X)
    (hE : LocallyHasFiniteTorDimension T' E)
    (U : X.C) (hU : IsTerminal U) (hqc : X.J.IsQuasiCompactObject U) :
    HasFiniteTorDimension T E := by
  obtain ⟨ι, -, V, f, a, b, hcov, hamp⟩ :=
    exists_finite_covering_hasTorAmplitude_of_locallyHasFiniteTorDimension T' E hE U hqc
  exact ⟨a, b, hasTorAmplitude_of_coversTop X T T'
    ((X.J.coversTop_iff_of_isTerminal U hU V).2
      ((Sieve.ofArrows_eq_ofObjects hU V f) ▸ hcov)) E a b hamp⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end
