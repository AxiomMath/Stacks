module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackDescent
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackFormalEffectiveness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigPhEtaleSchemeSlices

/-!
# Two inputs of Stacks 0DLH from Stacks 0DLC

The proof of Stacks 0DLH (`Complexes_{X/B}` is a stack in groupoids) in
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackDescent.lean` carries, among its hypotheses,
two consequences of Stacks 0DLC:

* `AlgebraicGeometry.Space.ComplexesSituation.NoNegativeFibreExtDescends`: condition (2) of
  Stacks 0DLD descends along an fppf covering. The source gets it from Stacks 0DLC, part (1):
  the points where the negative self-extensions of the fibres vanish form an open `W`, and an
  fppf covering is surjective, so if `W` contains every point of every member of the covering it
  contains every point.
* `AlgebraicGeometry.Space.ComplexesSituation.HasNoNegativeSelfExt`: an object `(T, E)` of
  `Complexes_{X/B}` has no negative self-extensions. This is part (b) of Stacks 0DLD at `V = T`,
  which is Stacks 0DLC, part (2), in the case `W = Y`, applied to `X_T ⟶ T` with `K = E`.

This file proves both from the forms of Stacks 0DLC stated in
`StacksFrontier/AlgebraicGeometry/Quot/NegativeExtLocus.lean`. Nothing here is registered: Stacks
0DLC is not yet proved here, through Stacks 0DKY (not yet proved here).

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.noNegativeFibreExtDescends_of_negativeExtLocusOpen`:
  condition (2) of Stacks 0DLD descends along fppf coverings, given Stacks 0DLC (1) with an
  open of the scheme `T`; `ComplexesSituation.noNegativeFibreExtDescends_of_existsNegativeExtLocus`
  is the same from the form of Stacks 0DLC (1) with an open subspace.
* `AlgebraicGeometry.Space.ComplexesSituation.hasNoNegativeSelfExt_of_negativeExtVanishesOfFibres`:
  objects of `Complexes_{X/B}` have no negative self-extensions, given Stacks 0DLC (2) at `W = Y`.

## References

* [Stacks Project, Tag 0DLH](https://stacks.math.columbia.edu/tag/0DLH)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.ComplexesSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

variable (D : ComplexesSituation B S hS)

/-! ### Condition (2) of Stacks 0DLD descends along fppf coverings -/

/-- **Condition (2) of Stacks 0DLD descends along fppf coverings, given Stacks 0DLC (1).** Let
`{a_i : T_i ⟶ T}` be an fppf covering and `E` a `T`-perfect complex on `X_T` whose pullbacks to
the `X_{T_i}` satisfy condition (2). By Stacks 0DLC (1) the points of `T` over which the negative
self-extensions of the fibres of `E` vanish form an open `W`. A point `t` of `T` is the image of a
point `t'` of some `T_i`, the covering being jointly surjective; the fibre of `E` over
`Spec κ(t') ⟶ T_i ⟶ T` is the fibre of its pullback to `X_{T_i}` over `Spec κ(t')`, so `t ∈ W`.
Hence `W` is all of `T`, which is condition (2) for `E`. -/
theorem noNegativeFibreExtDescends_of_negativeExtLocusOpen (h : D.NegativeExtLocusOpen) :
    D.NoNegativeFibreExtDescends := by
  intro T I Ti a hcov E hE hEi
  obtain ⟨W, hW⟩ := h T E E hE.1 hE
  have hall : ∀ z, z ∈ W := by
    intro z
    obtain ⟨c, q, hq, -, -, w, hw⟩ := BigFppfOver.exists_mem_of_mem_topology B S hS hcov z
    obtain ⟨i, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hq
    let t := (BigFppfOver.toScheme B S hS).map g w
    have hy := (hW _ (D.isFieldObject_fieldPointTestScheme (Ti i) t)
      (D.fieldPointTestSchemeHom (Ti i) t ≫ a i)).mpr (by
        intro j hj
        exact subsingleton_hom_shift_of_iso
          ((D.compComparison (D.fieldPointTestSchemeHom (Ti i) t) (a i)).app E).symm j
          (hEi i _ (D.isFieldObject_fieldPointTestScheme (Ti i) t)
            (D.fieldPointTestSchemeHom (Ti i) t) j hj))
    obtain ⟨s, hs⟩ := D.mem_range_fieldPointTestSchemeHom (Ti i) t
    have hmem := hy ⟨s, rfl⟩
    rw [CostructuredArrow.comp_left, Functor.map_comp, Scheme.Hom.comp_apply, hs] at hmem
    rwa [← hw, Functor.map_comp, Scheme.Hom.comp_apply]
  exact fun T₀ hT₀ y => (hW T₀ hT₀ y).mp fun x _ => hall x

/-- **Condition (2) of Stacks 0DLD descends along fppf coverings, given Stacks 0DLC (1)** in its
form with an open subspace, `AlgebraicGeometry.Space.ExistsNegativeExtLocus` (not yet proved here,
through Stacks 0DKY, not yet proved here). -/
theorem noNegativeFibreExtDescends_of_existsNegativeExtLocus (h : ExistsNegativeExtLocus B S hS) :
    D.NoNegativeFibreExtDescends :=
  D.noNegativeFibreExtDescends_of_negativeExtLocusOpen
    (D.negativeExtLocusOpen_of_existsNegativeExtLocus h)

/-! ### Objects of `Complexes_{X/B}` have no negative self-extensions -/

/-- **Part (b) of Stacks 0DLD at `V = T`, given Stacks 0DLC (2) at `W = Y`.** Every object
`(T, E)` of `Complexes_{X/B}` has no negative self-extensions: `Ext^n(E, E) = 0` for `n < 0`.

Stacks 0DLC (2) in the case `W = Y` (`AlgebraicGeometry.Space.NegativeExtVanishesOfFibres`;
not yet proved here, through Stacks 0DKY, not yet proved here) is applied to
the projection `X_T ⟶ T`, which is proper, flat and of finite presentation by base change, with
`K = E`: `E` is `T`-perfect, hence pseudo-coherent, and condition (2) of Stacks 0DLD for `E` is
the vanishing of the negative extensions of its fibres over the points of `T` with values in a
field, a point `Spec k ⟶ T` being a morphism of test schemes over `Y` and the fibre of
`X_T ⟶ T` over it being `X_{Spec k}`. At `V = T` the projection `X_T ×_T T ⟶ X_T` is an
isomorphism, along which the derived pullback is an equivalence commuting with the shift. -/
theorem hasNoNegativeSelfExt_of_negativeExtVanishesOfFibres
    (h : NegativeExtVanishesOfFibres B S hS) : D.HasNoNegativeSelfExt := by
  intro A n hn
  let F := (schemeSpaceFunctor B S hS).obj A.T.left
  let f : D.space A.T ⟶ F := D.projection A.T
  have hfib : ∀ T₀ : SchemesOver F, Stack.IsFieldObject B S hS T₀.left →
      HasNoNegativeExtAt f A.E A.E T₀ := by
    intro T₀ hT₀ i hi
    let y₀ : T₀.left ⟶ A.T.left := (schemeSpaceFunctorFullyFaithful B hS).preimage T₀.hom
    have hy₀ : (schemeSpaceFunctor B S hS).map y₀ = T₀.hom :=
      (schemeSpaceFunctorFullyFaithful B hS).map_preimage _
    let T₁ : SchemesOver D.Y := CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map y₀ ≫ A.T.hom)
    let y : T₁ ⟶ A.T := CostructuredArrow.homMk y₀ rfl
    have hpb : IsPullback (D.relativeMap y) (D.projection T₁) f T₀.hom := by
      have h' := isPullback_baseChangeMap D.f y
      rwa [show (schemeSpaceFunctor B S hS).map y.left = T₀.hom from hy₀] at h'
    have hfp := AlgebraicSpaces.isPullback_fiberProduct B S hS f T₀.hom
    exact (subsingleton_pull_iff_of_iso (hpb.isoIsPullback _ _ hfp)
      (hpb.isoIsPullback_hom_fst _ _ hfp) A.E A.E i).mpr (A.noNegativeFibreExt T₁ hT₀ y i hi)
  have hV := h f
    ((isProper_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f A.T.hom) D.proper)
    (D.projection_isFlat A.T)
    ((isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f A.T.hom) D.finitePresentation)
    A.E A.E A.relativelyPerfect.1 A.relativelyPerfect hfib (Over.mk (𝟙 F)) n hn
  have hid : IsPullback (𝟙 (D.space A.T)) f f (𝟙 F) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have hfp := AlgebraicSpaces.isPullback_fiberProduct B S hS f (𝟙 F)
  exact subsingleton_hom_shift_of_iso
    (((smallEtaleDerivedPullbackData B S hS).idIso (D.space A.T)).app A.E) n
    ((subsingleton_pull_iff_of_iso (hid.isoIsPullback _ _ hfp)
      (hid.isoIsPullback_hom_fst _ _ hfp) A.E A.E n).mp hV)

end AlgebraicGeometry.Space.ComplexesSituation

end
