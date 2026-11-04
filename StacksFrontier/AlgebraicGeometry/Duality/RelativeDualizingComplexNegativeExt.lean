module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineSections
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartOpens
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexNegativeExt
public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.DerivedSheafHomSliceModel
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologyFlatExtension
public import StacksFrontier.RingTheory.Dualizing.RelativeHomothetyGeneral
public import StacksFrontier.RingTheory.Dualizing.RelativeHomothetySelfExt

/-!
# A relative dualizing complex has no negative self-Ext

Let `f : X ⟶ S` be flat and locally of finite presentation and let `(K, ξ)` be a relative
dualizing complex for `f` (Stacks 0E2T). Then `Ext^n(K|_W, K|_W) = 0` for every open `W ⊆ X`
and every `n < 0`.

Over an affine open `U` lying over an affine open `V` of `S`, `K|_U` is the complex associated to
`RΓ(U, K)`, a relative dualizing complex for `Γ(S, V) → Γ(X, U)` (Stacks 0E2U), whose derived
homothety is invertible (Stacks 0E2G); so `Ext^n(K|_U, K|_U) = Ext^n(RΓ(U, K), RΓ(U, K)) = 0`
for `n ≠ 0`. Such opens form a basis of `X`, and negative degrees pass from a basis to every open
by Stacks 0D66, part (2). This is the input "`Ext^i(K|_U, K|_U) = 0` for `i < 0`" of the proofs of
Stacks 0E2W and 0E2X, which the source draws from Stacks 0E2V.

## Main results

* `IsRelativeDualizingComplex.subsingleton_shiftedHom_overFunctor_of_mem_chartOpens`: the vanishing
  away from degree zero over an affine open lying over an affine open.
* `IsRelativeDualizingComplex.subsingleton_shiftedHom_preimageRestrict`: negative self-Ext of the
  restriction to any open, read on the slice site.
* `IsRelativeDualizingComplex.subsingleton_shiftedHom_derivedPullback`: the same with restriction
  read as the derived pullback along the open immersion `W ⟶ X`.

## References

* [Stacks Project, Lemma 48.28.3 (Tag 0E2V)](https://stacks.math.columbia.edu/tag/0E2V)
* [Stacks Project, Lemma 48.28.2 (Tag 0E2U)](https://stacks.math.columbia.edu/tag/0E2U)
* [Stacks Project, Lemma 47.27.7 (Tag 0E2G)](https://stacks.math.columbia.edu/tag/0E2G)
* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

variable {X S : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f]
  {D : DiagonalOpen f} {K : DerivedCategory X.Modules}
  {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}

/-- Vanishing of `Ext^n(K, K)` is carried along an exact functor `F` with exact retractions
`F ⋙ G ≅ 𝟭` and `G ⋙ H ≅ 𝟭`. -/
private theorem subsingleton_shiftedHom_map_of_comp_iso_id {C₁ C₂ : Type*} [Category C₁]
    [Category C₂] [Abelian C₁] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : C₂ ⥤ C₁) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : C₁ ⥤ C₂) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e₁ : F ⋙ G ≅ 𝟭 C₁) (e₂ : G ⋙ H ≅ 𝟭 C₂) {K : DerivedCategory C₁} {n : ℤ}
    (h : Subsingleton (ShiftedHom K K n)) :
    Subsingleton (ShiftedHom (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj K) n) := by
  have := Stacks.DerivedGlueing.faithful_mapDerivedCategory_of_comp G H e₂
  refine Stacks.DerivedGlueing.subsingleton_shiftedHom_of_faithful G.mapDerivedCategory _ _ n ?_
  let e := (Stacks.DerivedGlueing.mapDerivedCategoryCompIso F G ≪≫
    Stacks.DerivedGlueing.mapDerivedCategoryCongr e₁ ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso).app K
  exact Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso e e n h

/-- **No self-Ext away from degree zero over a chart.** Let `(K, ξ)` be a relative dualizing
complex for `f` and let `U` be an affine open of `X` lying over an affine open of `S`. Then
`Ext^n(K|_U, K|_U) = 0` for `n ≠ 0`, restriction being read on the slice site over `U`.

`K|_U` is the complex associated to `RΓ(U, K)`, which is a relative dualizing complex for the
chart ring map (Stacks 0E2U), hence has invertible derived homothety (Stacks 0E2G), hence no
self-Ext away from degree zero; the derived functor of `~` is fully faithful and commutes with
shifts, and so do the comparisons between the slice-site and open-subscheme models. -/
theorem subsingleton_shiftedHom_overFunctor_of_mem_chartOpens
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    {U : X.Opens} (hU : U ∈ chartOpens f) {n : ℤ} (hn : n ≠ 0) :
    Subsingleton (ShiftedHom
      ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapDerivedCategory.obj K)
      ((SheafOfModules.overFunctor.{u} X.ringCatSheaf U).mapDerivedCategory.obj K) n) := by
  obtain ⟨hUa, V, hV, hUV⟩ := hU
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hUa hUV rfl
  let : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
    algebraFinitePresentation_appLE f hV hUa hUV rfl
  have := Dualizing.isIso_relativeHomothety_of_isRelativeDualizingComplex _
    (hK.isRelativeDualizingComplex_derivedSections hUa hV hUV)
  have h₀ : Subsingleton (ShiftedHom ((derivedSectionsUnbounded X U).obj K)
      ((derivedSectionsUnbounded X U).obj K) n) :=
    Dualizing.subsingleton_shift_of_isIso_relativeHomothety Γ(X, U) _ n hn
  obtain ⟨M, ⟨e₁⟩, ⟨e₂⟩⟩ := affineDerivedSectionsPresentation K
    (isQuasicoherentDerived_of_isPseudoCoherent X K hK.isPerfectRelativeTo.1) U hUa
  have hM : Subsingleton (ShiftedHom M M n) :=
    Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso e₂ e₂ n h₀
  -- through the fully faithful derived functor of `~`
  have h₁ : Subsingleton (ShiftedHom ((tilde.functor Γ(X, U)).mapDerivedCategory.obj M)
      ((tilde.functor Γ(X, U)).mapDerivedCategory.obj M) n) :=
    let := (StandardModel.mapDerivedCategoryFullyFaithful Γ(X, U)).full
    Stacks.Duality.subsingleton_shiftedHom_map_of_full _ hM
  -- through restriction along the isomorphism `U ≅ Spec Γ(X, U)`
  let k := hUa.isoSpec.hom
  have h₂ := subsingleton_shiftedHom_map_of_comp_iso_id (Scheme.Modules.restrictFunctor k)
    (Scheme.Modules.restrictFunctor (inv k)) (Scheme.Modules.restrictFunctor (inv (inv k)))
    (Scheme.Modules.restrictFunctorCompInvIso k)
    (Scheme.Modules.restrictFunctorCompInvIso (inv k)) h₁
  have h₃ : Subsingleton (ShiftedHom
      ((tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor k).mapDerivedCategory.obj M)
      ((tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor k).mapDerivedCategory.obj M) n) :=
    let e := (Stacks.DerivedGlueing.mapDerivedCategoryCompIso (tilde.functor Γ(X, U))
      (Scheme.Modules.restrictFunctor k)).symm.app M
    Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso e e n h₂
  -- the presentation of `K|_U`, read in the slice-site model
  let r : tilde.functor Γ(X, U) ⋙ Scheme.Modules.pushforward hUa.isoSpec.inv ≅
      tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hUa.isoSpec.hom :=
    Functor.isoWhiskerLeft _
      (Stacks.AlgebraicGeometry.OpenBaseChange.restrictFunctorIsoPushforwardInv
        hUa.isoSpec).symm
  let i := (Stacks.SheafOfModules.derivedOverFunctorEquiv U).app K ≪≫ e₁ ≪≫
    (RingTheory.TorIndependence.mapDerivedCategoryCompIso _ _ _ r).app M
  let E := Scheme.Modules.overEquiv U
  have := Stacks.DerivedGlueing.faithful_mapDerivedCategory_of_comp E.functor E.inverse
    E.unitIso.symm
  exact Stacks.DerivedGlueing.subsingleton_shiftedHom_of_faithful E.functor.mapDerivedCategory
    _ _ n (Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso i i n h₃)

/-- **Negative self-Ext of a relative dualizing complex vanishes on every open.** For a relative
dualizing complex `(K, ξ)` for `f`, an open `W ⊆ X` and `n < 0`, `Ext^n(K|_W, K|_W) = 0`,
restriction being read on the slice site. The affine opens of `X` lying over affine opens of `S`
form a basis on which this holds
(`subsingleton_shiftedHom_overFunctor_of_mem_chartOpens`), and negative Ext extends from a basis
to every open by Stacks 0D66, part (2). -/
theorem subsingleton_shiftedHom_preimageRestrict
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (W : X.Opens) {n : ℤ} (hn : n < 0) :
    Subsingleton (ShiftedHom
      ((Stacks.Cohomology.UnboundedHigherDirectImage.preimageRestrict (𝟙 X.toRingedSpace) W).obj K)
      ((Stacks.Cohomology.UnboundedHigherDirectImage.preimageRestrict (𝟙 X.toRingedSpace) W).obj K)
      n) :=
  Stacks.Cohomology.UnboundedHigherDirectImage.subsingleton_shiftedHom_preimageRestrict_of_isBasis
    (isBasis_chartOpens f) (𝟙 X.toRingedSpace) K K
    (fun _ hV _ hi => hK.subsingleton_shiftedHom_overFunctor_of_mem_chartOpens hV hi.ne) W n hn

/-- **Negative self-Ext of a relative dualizing complex restricted to an open vanishes**,
restriction being the derived pullback along the open immersion `W ⟶ X`: for `n < 0` every
morphism `K|_W ⟶ (K|_W)[n]` is zero. This is `subsingleton_shiftedHom_preimageRestrict` carried
from the slice site over `W` to the open subspace `W`. -/
theorem subsingleton_shiftedHom_derivedPullback
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (W : X.Opens) {n : ℤ} (hn : n < 0) :
    Subsingleton (ShiftedHom
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        W.ι.toLRSHom.toShHom).obj K)
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        W.ι.toLRSHom.toShHom).obj K) n) := by
  let O := structureSheafRing X.toRingedSpace
  let Sl := Stacks.DerivedGlueing.sliceToSubspace O W
  let T := Stacks.DerivedGlueing.subspaceToSlice O W
  let B := (SheafOfModules.overFunctor.{u} O W).mapDerivedCategory.obj K
  have h₀ : Subsingleton (ShiftedHom B B n) := hK.subsingleton_shiftedHom_preimageRestrict W hn
  have h₁ : Subsingleton (ShiftedHom (Sl.mapDerivedCategory.obj B)
      (Sl.mapDerivedCategory.obj B) n) :=
    subsingleton_shiftedHom_map_of_comp_iso_id Sl T Sl (W.sheafOfModulesEquivOver O).unitIso.symm
      (W.sheafOfModulesEquivOver O).counitIso h₀
  let eA : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      W.ι.toLRSHom.toShHom).obj K ≅ Sl.mapDerivedCategory.obj B :=
    (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso
        X.toRingedSpace W).app K ≪≫
      (Stacks.DerivedGlueing.mapDerivedCategoryCompIso
        (SheafOfModules.overFunctor.{u} O W) Sl).symm.app K
  exact Stacks.DerivedGlueing.subsingleton_shiftedHom_of_iso eA eA _ h₁

end AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

end
