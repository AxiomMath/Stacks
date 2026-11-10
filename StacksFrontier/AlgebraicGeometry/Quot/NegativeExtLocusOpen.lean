module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeDualExtLocus
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusHomFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated

/-!
# Stacks 0DLC, part (1): the locus of vanishing negative fibre extensions is open

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces over a
scheme `S`, `K` a pseudo-coherent and `E` a `Y`-perfect object of `D(𝒪_X)`.  Part (1) of
Stacks 0DLC says that there is an open `W ⊆ Y` characterized by: a point `y : Spec(k) ⟶ Y` with
values in a field lies in `|W|` if and only if `Ext^i_{𝒪_{X_y}}(K_y, E_y) = 0` for all `i < 0`.
This file proves it, granted Stacks 0DKY (`AlgebraicGeometry.Space.RelativeDerivedHomDualExists`,
not yet proved here), as `AlgebraicGeometry.Space.existsNegativeExtLocus_of_dualExists`.

## The argument

As in the source.  Over an affine scheme `U ⟶ Y` (more generally a scheme whose space is
quasi-compact and quasi-separated) Stacks 0DKY gives a pseudo-coherent `L` on `U` which
"universally computes" `Rf_* R𝓗om(K, E)`, so that at every point `y` of `U` with values in a
field `Ext^i(K_y, E_y) = Ext^i(L_y, 𝒪_y)`
(`AlgebraicGeometry.Space.hasNoNegativeExtAt_iff_of_dual`).  By Stacks 0BDI on the small étale
site (`AlgebraicGeometry.Space.exists_openSubspace_hasNoNegativeDualExt_iff`) the locus where the
right side vanishes for `i < 0` is open, and does not change under a field extension
(`AlgebraicGeometry.Space.hasNoNegativeDualExt_iff_of_hom`).  For a general `Y`, the locus is
open on every affine étale chart and descends to `Y`
(`AlgebraicGeometry.Space.exists_openSubspace_forall_isFieldObject_iff`).

The source uses Stacks 0AA7 to see that the vanishing at `y` is a property of the point of `|Y|`
underlying `y`, that is, that it does not change under a field extension `k'/k`.  This is not a
hypothesis here: applying Stacks 0DKY to the base change of `f` to `Spec(k)` itself, the
vanishing at `y` and at `y' : Spec(k') ⟶ Spec(k) ⟶ Y` are those of `Ext^i(L_y, k)` and
`Ext^i(L_y ⊗_k k', k')`, and these agree by the computation on the chart `Spec(k)` of Stacks
0BDI (`AlgebraicGeometry.Space.hasNoNegativeExtAt_iff_of_hom_of_dualExists`).  So Stacks 0DKY is
the only pending input.

## Main results

* `AlgebraicGeometry.Space.exists_isNegativeExtLocus_of_dualExists_of_quasiCompact`: part (1)
  over a quasi-compact and quasi-separated base.
* `AlgebraicGeometry.Space.hasNoNegativeExtAt_iff_of_hom_of_dualExists`: the vanishing of the
  negative fibre extensions does not change under a field extension.
* `AlgebraicGeometry.Space.existsNegativeExtLocus_of_dualExists`: **Stacks 0DLC, part (1)**,
  granted Stacks 0DKY.

Nothing is registered: Stacks 0DKY is a hypothesis.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 0AA7](https://stacks.math.columbia.edu/tag/0AA7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

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

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Locus

variable {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 0DKY on a quasi-compact and quasi-separated scheme over `Y`, read at its points.**
Let `c : U ⟶ Y` be a morphism from a scheme whose space is quasi-compact and quasi-separated.
Granted Stacks 0DKY, there is a pseudo-coherent `L` on `U` such that at every test scheme `T`
over `U` the negative extensions of the fibres of `K` and `E` over `T ⟶ U ⟶ Y` vanish exactly
when `Ext^i(L_T, 𝒪_T) = 0` for `i < 0`. -/
theorem exists_dual_forall_hasNoNegativeExtAt_iff (h0DKY : RelativeDerivedHomDualExists B S hS)
    (f : X ⟶ Y) (hp : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) {U : AlgebraicSpaces B S hS}
    (hqc : IsQuasiCompactSpace B S hS U.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal U.1) (c : U ⟶ Y)
    (hc : yoneda.relativelyRepresentable c.hom) :
    ∃ L : derivedModules B S hS U, (smallEtaleRingedSite B S hS U.1 U.2).IsPseudoCoherent L ∧
      ∀ T : SchemesOver U, HasNoNegativeExtAt f K E
          ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) c).obj T) ↔
        HasNoNegativeDualExt L T.hom := by
  let V : Over Y := Over.mk c
  let fV := overInclusion f V
  let pV := overProjection f V
  have hsqV : IsPullback pV fV f V.hom := AlgebraicSpaces.isPullback_fiberProduct B S hS f V.hom
  have hpV : IsProper B S hS fV.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback hsqV hp
  have hflatV : IsFlat B S hS fV.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hsqV hflat
  have hfpV : IsFinitePresentation B S hS fV.hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hsqV hfp
  have hrep : yoneda.relativelyRepresentable pV.hom :=
    (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS hsqV).flip hc
  have hKV : (smallEtaleRingedSite B S hS (overBaseChange f V).1
      (overBaseChange f V).2).IsPseudoCoherent
      (((smallEtaleDerivedPullbackData B S hS).pull pV).obj K) :=
    isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable B S hS pV hrep K hK
  have hEV :=
    isPerfectRelativeToCanonical_pull_of_isPullback hsqV hrep hflatV hfpV.1 hflat hfp.1 E hE
  obtain ⟨L, hL, -, hbc⟩ := h0DKY B.contains_terminal fV hqc hqs hpV hflatV hfpV _ _ hEV hKV
  refine ⟨L, hL, fun T => (hasNoNegativeExtAt_overInclusion_iff f V K E T).symm.trans ?_⟩
  exact hasNoNegativeExtAt_iff_of_dual fV _ _ L T
    (hbc _ _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS fV T.hom)).some

/-- **Stacks 0DLC, part (1), over a quasi-compact and quasi-separated base**, granted Stacks
0DKY: the `L` of Stacks 0DKY turns the negative fibre extensions into `Ext^i(L_y, 𝒪_y)`, whose
vanishing locus is open by Stacks 0BDI on the small étale site. -/
theorem exists_isNegativeExtLocus_of_dualExists_of_quasiCompact
    (h0DKY : RelativeDerivedHomDualExists B S hS)
    (f : X ⟶ Y) (hp : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E)
    (hqc : IsQuasiCompactSpace B S hS Y.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y.1) :
    ∃ W : OpenSubspaces B S hS Y.1, IsNegativeExtLocus f K E W := by
  obtain ⟨L, hL, -, hbc⟩ := h0DKY B.contains_terminal f hqc hqs hp hflat hfp K E hE hK
  obtain ⟨W, hW⟩ := exists_openSubspace_hasNoNegativeDualExt_iff Y L hL
  exact ⟨W, fun T₀ hT₀ => (hW T₀ hT₀).trans (hasNoNegativeExtAt_iff_of_dual f K E L T₀
    (hbc _ _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS f T₀.hom)).some).symm⟩

/-- An object of the site whose scheme is the spectrum of a field represents a quasi-compact and
quasi-separated algebraic space, representably over any algebraic space it maps to. -/
theorem isQuasiCompactSpace_isAbsolutelyQuasiSeparated_of_isFieldObject {T : BigFppfOver B S hS}
    (hT : Stack.IsFieldObject B S hS T) :
    IsQuasiCompactSpace B S hS (yoneda.obj T) ∧
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal (yoneda.obj T) := by
  obtain ⟨k, hk, ⟨e⟩⟩ := hT
  let := hk
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := IsAffine.of_isIso e.hom
  exact ⟨isQuasiCompactSpace_yoneda_of_isAffine B S hS T inferInstance,
    isAbsolutelyQuasiSeparated_yoneda_obj B S hS B.contains_terminal T inferInstance⟩

/-- **The vanishing of the negative fibre extensions does not change under a field extension**,
granted Stacks 0DKY.  For a morphism `T₁ ⟶ T₀` of test schemes over `Y` with values in fields,
`Ext^i(K_{T₀}, E_{T₀}) = 0` for all `i < 0` exactly when `Ext^i(K_{T₁}, E_{T₁}) = 0` for all
`i < 0`.

This is the consequence of Stacks 0AA7 that the source draws.  Here it comes from Stacks 0DKY
applied to the base change of `f` to `T₀`, which turns both sides into the negative extensions
of the pullbacks of a pseudo-coherent `L` on `T₀` into the structure sheaf, and from their
invariance under field extensions (`AlgebraicGeometry.Space.hasNoNegativeDualExt_iff_of_hom`). -/
theorem hasNoNegativeExtAt_iff_of_hom_of_dualExists (h0DKY : RelativeDerivedHomDualExists B S hS)
    (f : X ⟶ Y) (hp : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) {T₁ T₀ : SchemesOver Y}
    (g : T₁ ⟶ T₀) (hT₁ : Stack.IsFieldObject B S hS T₁.left)
    (hT₀ : Stack.IsFieldObject B S hS T₀.left) :
    HasNoNegativeExtAt f K E T₀ ↔ HasNoNegativeExtAt f K E T₁ := by
  obtain ⟨hqc, hqs⟩ := isQuasiCompactSpace_isAbsolutelyQuasiSeparated_of_isFieldObject hT₀
  obtain ⟨L, hL, hLK⟩ := exists_dual_forall_hasNoNegativeExtAt_iff h0DKY f hp hflat hfp K E hK
    hE (U := (schemeSpaceFunctor B S hS).obj T₀.left) hqc hqs T₀.hom
    (Y.2.diagonal_representable.of_diag T₀.hom.hom)
  let T₀' : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀.left) := CostructuredArrow.mk (𝟙 _)
  let T₁' : SchemesOver ((schemeSpaceFunctor B S hS).obj T₀.left) :=
    CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map g.left)
  let g' : T₁' ⟶ T₀' := CostructuredArrow.homMk g.left (Category.comp_id _)
  have e₀ : (CostructuredArrow.map (S := schemeSpaceFunctor B S hS) T₀.hom).obj T₀' = T₀ := by
    simp only [T₀', CostructuredArrow.map_mk, Category.id_comp]
    rfl
  have e₁ : (CostructuredArrow.map (S := schemeSpaceFunctor B S hS) T₀.hom).obj T₁' = T₁ := by
    simp only [T₁', CostructuredArrow.map_mk, CostructuredArrow.w g]
    rfl
  have h₀ := hLK T₀'
  have h₁ := hLK T₁'
  rw [e₀] at h₀
  rw [e₁] at h₁
  rw [h₀, h₁]
  exact hasNoNegativeDualExt_iff_of_hom L hL g' hT₁ hT₀

/-- **Stacks 0DLC, part (1)**, for a given `f`, `K`, `E`, granted Stacks 0DKY: there is an open
subspace `W` of `Y` such that a point `y : Spec(k) ⟶ Y` with values in a field lies in `|W|`
exactly when `Ext^i_{𝒪_{X_y}}(K_y, E_y) = 0` for all `i < 0`.

On every affine étale chart `Spec(A) ⟶ Y` the corresponding locus is open
(`AlgebraicGeometry.Space.exists_isNegativeExtLocus_of_dualExists_of_quasiCompact` for the base
change of `f` to `Spec(A)`, read through
`AlgebraicGeometry.Space.hasNoNegativeExtAt_overInclusion_iff` of
`StacksFrontier/AlgebraicGeometry/Quot/NegativeExtLocusHomFibres.lean`),
the condition does not change
under field extensions (`AlgebraicGeometry.Space.hasNoNegativeExtAt_iff_of_hom_of_dualExists`),
and the locus descends to `Y`
(`AlgebraicGeometry.Space.exists_openSubspace_forall_isFieldObject_iff`). -/
theorem exists_isNegativeExtLocus_of_dualExists (h0DKY : RelativeDerivedHomDualExists B S hS)
    (f : X ⟶ Y) (hp : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    ∃ W : OpenSubspaces B S hS Y.1, IsNegativeExtLocus f K E W := by
  have hP : ∀ {T₁ T₀ : SchemesOver Y}, (T₁ ⟶ T₀) → Stack.IsFieldObject B S hS T₁.left →
      Stack.IsFieldObject B S hS T₀.left →
      (HasNoNegativeExtAt f K E T₀ ↔ HasNoNegativeExtAt f K E T₁) := fun g hT₁ hT₀ =>
    hasNoNegativeExtAt_iff_of_hom_of_dualExists h0DKY f hp hflat hfp K E hK hE g hT₁ hT₀
  refine exists_openSubspace_forall_isFieldObject_iff (HasNoNegativeExtAt f K E) hP ?_
  intro A _ hA gA φ hφ
  let U : AlgebraicSpaces B S hS := schemeSpace (specFppfOver B S hS hA gA)
  have hU : IsAffine ((BigFppfOver.toScheme B S hS).obj (specFppfOver B S hS hA gA)) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  have hqc : IsQuasiCompactSpace B S hS U.1 :=
    isQuasiCompactSpace_yoneda_of_isAffine B S hS (specFppfOver B S hS hA gA) hU
  have hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal U.1 :=
    isAbsolutelyQuasiSeparated_yoneda_obj B S hS B.contains_terminal
      (specFppfOver B S hS hA gA) inferInstance
  have hrep : yoneda.relativelyRepresentable φ.hom := Y.2.diagonal_representable.of_diag φ.hom
  obtain ⟨L, hL, hLK⟩ := exists_dual_forall_hasNoNegativeExtAt_iff h0DKY f hp hflat hfp K E hK
    hE (U := U) hqc hqs φ hrep
  obtain ⟨W, hW⟩ := exists_openSubspace_hasNoNegativeDualExt_iff U L hL
  exact ⟨Set.range (pointsMap B S hS W.1.toFunctor W.1.ι), isOpen_range_pointsMap_openSubspace W,
    fun T hT =>
      (testPoint_mem_iff_schemesOverPoints_subset W T).symm.trans ((hW T hT).trans (hLK T).symm)⟩

variable (B S hS) in
/-- **Stacks 0DLC, part (1)**, granted Stacks 0DKY (`h0DKY`: Stacks 0DKY, not yet proved here): for
every proper, flat, finitely presented morphism `f : X ⟶ Y` of algebraic spaces,
every pseudo-coherent `K` and every `Y`-perfect `E` in `D(𝒪_X)`, there is an open `W ⊆ Y` with
`y ∈ |W| ⟺ Ext^i_{𝒪_{X_y}}(K_y, E_y) = 0` for `i < 0`, for every point `y : Spec(k) ⟶ Y` with
values in a field. -/
theorem existsNegativeExtLocus_of_dualExists (h0DKY : RelativeDerivedHomDualExists B S hS) :
    ExistsNegativeExtLocus B S hS :=
  fun f hp hflat hfp K E hK hE =>
    exists_isNegativeExtLocus_of_dualExists h0DKY f hp hflat hfp K E hK hE

end Locus

end AlgebraicGeometry.Space

end
