module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomSheafDescentProof

/-!
# Step (S) of Stacks 0DLC, part (3), through the dual of Stacks 0DKY

Step (S) of the proof of Stacks 0DLC, part (3), says that `T ↦ Hom(K_T, E_T)` is an fppf sheaf
over `Y`.  The source applies Stacks 0DL9 to Čech hypercoverings; that citation rests on Stacks
0D9R and 0D9S, whose flatness hypothesis on every transition fails for the degeneracies of a Čech
nerve.  This file gives a route which does
not use Stacks 0DL9.

Over an affine test scheme `V` of `Y` the functor is, by Stacks 0DKY in its compatible form, the
functor `T ↦ Hom(L_T, 𝒪_T)` of a pseudo-coherent `L` with `H^i(L) = 0` for `i > 0` (the fibre
criterion of `AlgebraicGeometry.Space.fieldFibreDualVanishingIsLE`), which step (L)
(`AlgebraicGeometry.Space.relHomStructureRepresentableOfIsLE`) shows to be an algebraic space
affine and of finite presentation over `V`; in particular it is an fppf sheaf over `V`.  What is
left is that the fppf sheaf property of `T ↦ Hom(K_T, E_T)` is local on the test schemes for the
Zariski topology, the named proposition
`AlgebraicGeometry.Space.RelativeDerivedHomZariskiDescent` (internal, in progress).

Nothing here is registered.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDerivedHomZariskiDescent`: Zariski descent of
  `T ↦ Hom(K_T, E_T)` (internal, in progress).

## Main results

* `AlgebraicGeometry.Space.isFppfSheafOver_of_isAffineFinitePresentationAlgebraicSpaceOver`: an
  algebraic space affine and of finite presentation over `Y` is an fppf sheaf over `Y`.
* `AlgebraicGeometry.Space.relativeDerivedHomIsSheafOfDescent_of_dual`: step (S) from Stacks 0DKY
  and Zariski descent, at the hypotheses of Stacks 0DLC.
* `AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_zariski`: Stacks 0DLC,
  part (3), at `W = Y`, from part (2), Stacks 0DKY and Zariski descent, with no Stacks 0DL9.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 0DL9](https://stacks.math.columbia.edu/tag/0DL9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

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

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An algebraic space affine and of finite presentation over `Y` is an fppf sheaf over `Y`**:
its total presheaf is the universe lift of the algebraic space, which is an fppf sheaf. -/
theorem isFppfSheafOver_of_isAffineFinitePresentationAlgebraicSpaceOver
    {Y : AlgebraicSpaces B S hS} {R : (SchemesOver Y)ᵒᵖ ⥤ Type (u + 1)}
    (h : IsAffineFinitePresentationAlgebraicSpaceOver Y R) : IsFppfSheafOver R := by
  obtain ⟨H, p, -, -, ⟨e⟩⟩ := h
  have hH : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (H.1 ⋙ uliftFunctor.{u + 1, u}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ uliftFunctor.{u + 1, u} H.2.isSheaf
  exact (Presheaf.isSheaf_of_iso_iff (totalPresheafIso e.symm ≪≫
    totalPresheafULiftIso (spacePointsOver p) ≪≫
    Functor.isoWhiskerRight (totalPresheafSpacePointsOverIso p) uliftFunctor.{u + 1, u})).2 hH

variable (B S hS) in
/-- **Zariski descent of `T ↦ Hom(K_T, E_T)`** (internal, in progress; the remaining input of
step (S) of Stacks 0DLC, part (3), on the route through the dual of Stacks 0DKY).  Let
`f : X ⟶ Y` be a morphism of algebraic spaces and `K`, `E` pseudo-coherent objects of `D(𝒪_X)`
with `Ext^i(K_V, E_V) = 0` for `i < 0` and every algebraic space `V` over `Y` (in particular
every `V` étale over a test scheme, which is the local vanishing the gluing uses).  If the
restriction of `T ↦ Hom(K_T, E_T)` to the test schemes over every affine test scheme of `Y` is an
fppf sheaf, then `T ↦ Hom(K_T, E_T)` is an fppf sheaf over `Y`.

Its content is the Zariski sheaf property of `T ↦ Hom(K_T, E_T)` for the covering of a test
scheme `T` by its affine opens `T_k`: morphisms `K_{T_k} ⟶ E_{T_k}` agreeing on the overlaps glue
uniquely to `K_T ⟶ E_T`.  With `M = Rf_{T,*} R𝓗om(K_T, E_T)` on the small étale site of `T`, the
vanishing hypothesis gives `M ∈ D^{≥ 0}`, so `Hom(K_W, E_W) = Γ(W, H^0(M))` for every open `W` of
`T`, a sheaf in `W`. -/
def RelativeDerivedHomZariskiDescent : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (K E : derivedModules B S hS X),
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
    (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent E →
    (∀ (V : Over Y) (i : ℤ), i < 0 →
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦i⟧)) →
    (∀ V : SchemesOver Y, IsAffine ((BigFppfOver.toScheme B S hS).obj V.left) →
      IsFppfSheafOver ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).op ⋙
        relativeDerivedHom f K E)) →
    IsFppfSheafOver (relativeDerivedHom f K E)

section Dual

variable {X Y : AlgebraicSpaces B S hS}

/-- **Over an affine test scheme, `T ↦ Hom(K_T, E_T)` is an algebraic space affine and of finite
presentation**, from Stacks 0DKY in its compatible form and step (L): for `f` proper, flat and of
finite presentation, `K` pseudo-coherent, `E` perfect relative to `Y` and the negative extensions
vanishing on the fibres over the points with values in a field.  This is the local step of
`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_steps`. -/
theorem relativeDerivedHom_isAffineFinitePresentation_over_affine
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS)
    (f : X ⟶ Y) (hp : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E)
    (hfib : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt f K E T₀)
    (V : SchemesOver Y) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.left)) :
    IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj V.left)
      ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).op ⋙
        relativeDerivedHom f K E) := by
  let V' : Over Y := (schemesOverToOver Y).obj V
  let fV := overInclusion f V'
  let pV := overProjection f V'
  have hsq : IsPullback pV fV f V'.hom := AlgebraicSpaces.isPullback_fiberProduct B S hS f V'.hom
  have hpV : IsProper B S hS fV.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback hsq hp
  have hflatV : IsFlat B S hS fV.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hsq hflat
  have hfpV : IsFinitePresentation B S hS fV.hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hsq hfp
  have hrep : yoneda.relativelyRepresentable pV.hom :=
    (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS hsq).flip
      (relativelyRepresentable_of_isAlgebraicSpace B S hS Y.2 V.hom.hom)
  have hKV : (smallEtaleRingedSite B S hS (overBaseChange f V').1
      (overBaseChange f V').2).IsPseudoCoherent
      (((smallEtaleDerivedPullbackData B S hS).pull pV).obj K) :=
    isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable B S hS pV hrep K hK
  have hEV :=
    isPerfectRelativeToCanonical_pull_of_isPullback hsq hrep hflatV hfpV.1 hflat hfp.1 E hE
  obtain ⟨L, hLpc, hbc, ⟨e⟩⟩ := h0DKY B.contains_terminal fV
    (isQuasiCompactSpace_yoneda_of_isAffine B S hS V.left hV)
    (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS B.contains_terminal
      (isAffineSpace_yoneda B S hS V.left hV))
    hpV hflatV hfpV _ _ hEV hKV
  have hL0 : L.IsLE 0 := fieldFibreDualVanishingIsLE B S hS (testSpace V) L hLpc fun T₀ hT₀ =>
    (hasNoNegativeExtAt_iff_of_dual fV _ _ L T₀
      (hbc _ _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS fV T₀.hom)).some).1
      ((hasNoNegativeExtAt_overInclusion_iff f V' K E T₀).2 (hfib _ hT₀))
  exact (relHomStructureRepresentableOfIsLE V.left hV L hLpc hL0).of_iso
    (e.symm ≪≫ relativeDerivedHomBaseChangeIso f V' K E)

/-- **Step (S) of Stacks 0DLC, part (3), through the dual of Stacks 0DKY.**  For `f : X ⟶ Y`
proper, flat and of finite presentation, `K` pseudo-coherent, `E` perfect relative to `Y`, the
negative extensions of `K_V`, `E_V` vanishing for every `V` over `Y` (and so on the fibres),
`T ↦ Hom(K_T, E_T)` is an fppf sheaf over `Y`, granted Stacks 0DKY in its compatible form
(`h0DKY`, ours) and Zariski descent (`hZar`, internal, in progress).  No Stacks 0DL9 is used:
over affine test schemes the functor is an algebraic space
(`AlgebraicGeometry.Space.relativeDerivedHom_isAffineFinitePresentation_over_affine`). -/
theorem relativeDerivedHomIsSheafOfDescent_of_dual
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS)
    (hZar : RelativeDerivedHomZariskiDescent B S hS)
    (f : X ⟶ Y) (hp : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E)
    (hfib : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt f K E T₀)
    (hneg : ∀ (V : Over Y) (i : ℤ), i < 0 →
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦i⟧)) :
    IsFppfSheafOver (relativeDerivedHom f K E) :=
  hZar f K E hK hE.1 hneg fun V hV =>
    isFppfSheafOver_of_isAffineFinitePresentationAlgebraicSpaceOver
      (relativeDerivedHom_isAffineFinitePresentation_over_affine h0DKY f hp hflat hfp K E hK hE
        hfib V hV)

/-- **Stacks 0DLC, part (3), in the case `W = Y`, without Stacks 0DL9**: from part (2) in the
case `W = Y` (`h2`), Stacks 0DKY in its compatible form (`h0DKY`) and Zariski descent of
`T ↦ Hom(K_T, E_T)` (`hZar`, internal, in progress).  The sheaf property is
`AlgebraicGeometry.Space.relativeDerivedHomIsSheafOfDescent_of_dual`, the local representability
`AlgebraicGeometry.Space.relativeDerivedHom_isAffineFinitePresentation_over_affine`, and the
gluing `AlgebraicGeometry.Space.affineFinitePresentationOfAffineTestSchemes`.  Compare
`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_external`, which carries
Stacks 0DL9 instead of `hZar`. -/
theorem relativeDerivedHomRepresentableOfFibres_of_zariski
    (h2 : NegativeExtVanishesOfFibres B S hS)
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS)
    (hZar : RelativeDerivedHomZariskiDescent B S hS) :
    RelativeDerivedHomRepresentableOfFibres B S hS := by
  intro X Y f hp hflat hfp K E hK hE hfib
  exact affineFinitePresentationOfAffineTestSchemes Y _
    (relativeDerivedHomIsSheafOfDescent_of_dual h0DKY hZar f hp hflat hfp K E hK hE hfib
      (h2 f hp hflat hfp K E hK hE hfib))
    fun V hV => relativeDerivedHom_isAffineFinitePresentation_over_affine h0DKY f hp hflat hfp
      K E hK hE hfib V hV

end Dual

end AlgebraicGeometry.Space

end
