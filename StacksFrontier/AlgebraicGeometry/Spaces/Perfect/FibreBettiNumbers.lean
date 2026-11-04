module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldModules
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleNoetherianModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageSiteOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedFibreBettiRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatDerivedPushforwardFibreSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FibreBettiNumbers
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.Perfect.BettiConstructibility
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.RingTheory.Dualizing.LocalizationTransport
import StacksCore.Tactic.StacksAttribute

/-!
# The Betti numbers of the fibres of a flat proper family of algebraic spaces

Let `Y` be a scheme, `f : X ⟶ Y` a proper, flat morphism of finite presentation from an
algebraic space, and `𝓕` an `𝒪_X`-module of finite presentation, flat over `Y`. For `i ∈ ℤ` the
`i`-th Betti-number function is `β_i(y) = dim_{κ(y)} H^i(X_y, 𝓕_y)`. Stacks 0E0R: its formation
commutes with arbitrary base change, it is upper semicontinuous, and its level sets are locally
constructible.

## Main definitions

* `AlgebraicGeometry.Space.fibreBetti`: the function `β_i` on the points of `Y`.

## Main results

* `AlgebraicGeometry.Space.fibreBetti_baseChange`: Stacks 0E0R (1).
* `AlgebraicGeometry.Space.upperSemicontinuous_fibreBetti`: Stacks 0E0R (2).
* `AlgebraicGeometry.Space.isLocallyConstructible_fibreBetti_preimage`: Stacks 0E0R (3).

The three results hold without the flatness of `f`.

## Implementation notes

The scheme `Y` is an object `U` of the big fppf site, `X ⟶ Y` a morphism of algebraic spaces to
the representable `yoneda.obj U`. The fibre `X_y` is the fibre product of `X` with
`Spec κ(y) ⟶ Y`, and `H^i(X_y, 𝓕_y)` is read as the degree-`i` cohomology of
`RΓ(Spec κ(y), Rf_{y,*}𝓕_y)`, a module over `Γ(Spec κ(y), 𝒪) = κ(y)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Set.Notation

universe u

namespace AlgebraicGeometry.Space

open ProperFlatStein

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The scheme underlying the site object `residueFieldSiteObj B S hS U y` is affine: it is
`Spec κ(y)`, the spectrum of the residue field of the scheme underlying `U` at the point `y`. -/
instance isAffine_residueFieldSiteObj (U : BigFppfOver B S hS)
    (y : (BigFppfOver.toScheme B S hS).obj U) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (residueFieldSiteObj B S hS U y)) :=
  inferInstanceAs (IsAffine (Spec _))

variable {U : BigFppfOver B S hS} {X : AlgebraicSpaces B S hS}
  (f : X ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)

/-- **The `i`-th Betti-number function of the family `(f, 𝓕)`.** Its value at a point `y` of
the scheme `Y` is `dim_{κ(y)} H^i(X_y, 𝓕_y)`, with `X_y = X ×_Y Spec κ(y)`, `𝓕_y` the pullback
of `𝓕`, and `H^i(X_y, 𝓕_y) = H^i(RΓ(Spec κ(y), Rf_{y,*}𝓕_y))` a module over
`Γ(Spec κ(y), 𝒪) = κ(y)`. -/
def fibreBetti (F : Modules.{u, u} B S hS X.1 X.2) (i : ℤ) :
    (BigFppfOver.toScheme B S hS).obj U → ℕ :=
  fun y => Module.finrank Γ((BigFppfOver.toScheme B S hS).obj (residueFieldSiteObj B S hS U y), ⊤)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u}
        Γ((BigFppfOver.toScheme B S hS).obj (residueFieldSiteObj B S hS U y), ⊤)) i).obj
      (baseChangeDerivedSections f (residueFieldSiteHom B S hS U y) F))

/-- Base change of a proper, finitely presented morphism with a finitely presented module flat
over the base keeps all of these properties. -/
private theorem baseChange_isProper_and_isFinitePresentation (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F)
    {U' : BigFppfOver B S hS} (g : U' ⟶ U) :
    IsProper B S hS (pullback.snd f (representedSpaceMap B S hS g)).hom ∧
      IsFinitePresentation B S hS (pullback.snd f (representedSpaceMap B S hS g)).hom ∧
      ((modulePullback B S hS (pullback.fst f (representedSpaceMap B S hS g))).obj
        F).IsFinitePresentation ∧
      IsFlatOver B S hS _ (pullback.snd f (representedSpaceMap B S hS g)).hom
        ((modulePullback B S hS (pullback.fst f (representedSpaceMap B S hS g))).obj F) := by
  have hpb := IsPullback.of_hasPullback f (representedSpaceMap B S hS g)
  have := isQuasicoherentOnSite_of_isFinitePresentation F hFfp
  have hF'fp :=
    isFinitePresentation_modulePullback (pullback.fst f (representedSpaceMap B S hS g)) F hFfp
  have := isQuasicoherentOnSite_of_isFinitePresentation _ hF'fp
  exact ⟨(isProper_isStableUnderBaseChange B S hS).of_isPullback hpb hf,
    (isFinitePresentation_isStableUnderBaseChange (B := B) (S := S) (hS := hS)).of_isPullback
      hpb hfp,
    hF'fp, isFlatOver_modulePullback B S hS hpb F hF⟩

/-- **Stacks 0E0R, part (1): the formation of `β_i` commutes with arbitrary base change.** For
`f : X ⟶ Y` proper and of finite presentation, `𝓕` of finite presentation and flat over `Y`,
and any morphism `g : Y' ⟶ Y` of schemes of the site, the `i`-th Betti-number function of the
base change `(X ×_Y Y' ⟶ Y', 𝓕_{Y'})` is `β_i ∘ g`. -/
@[stacks 0E0R "(1)"]
theorem fibreBetti_baseChange (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F)
    {U' : BigFppfOver B S hS} (g : U' ⟶ U) (i : ℤ) :
    fibreBetti (pullback.snd f (representedSpaceMap B S hS g))
        ((modulePullback B S hS (pullback.fst f (representedSpaceMap B S hS g))).obj F) i =
      fibreBetti f F i ∘ ((BigFppfOver.toScheme B S hS).map g).base := by
  funext y'
  let gS := representedSpaceMap B S hS g
  let f' := pullback.snd f gS
  let F' := (modulePullback B S hS (pullback.fst f gS)).obj F
  let y := ((BigFppfOver.toScheme B S hS).map g).base y'
  let t' := residueFieldSiteHom B S hS U' y'
  let t := residueFieldSiteHom B S hS U y
  let h := residueFieldSiteMap g y'
  obtain ⟨hf', hfp', hF'fp, hF'⟩ :=
    baseChange_isProper_and_isFinitePresentation f hf hfp F hFfp hF g
  have := isQuasicoherentOnSite_of_isFinitePresentation F hFfp
  have := isQuasicoherentOnSite_of_isFinitePresentation F' hF'fp
  let K := (derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F)
  have hKq : QcohDerived B S hS _ K := derivedCategoryB_of_isPerfect B S hS _ K
    (isPerfect_derivedModulePushforward_single_and_isIso_baseChange f hf hfp F hFfp hF).1
  obtain ⟨e1⟩ := nonempty_derivedPullback_iso_baseChange f' hf' hfp' F' hF'fp hF' t'
  obtain ⟨e2⟩ := nonempty_derivedPullback_iso_baseChange f hf hfp F hFfp hF g
  obtain ⟨e3⟩ := nonempty_derivedPullback_iso_baseChange f hf hfp F hFfp hF t
  obtain ⟨e5⟩ := nonempty_totalDerivedExtensionScalars_derivedSections_iso h
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t)).obj K)
    (derivedQuasicoherent_smallEtaleDerivedModulePullback _ _ _ _ K hKq)
  have hm : representedSpaceMap B S hS t' ≫ gS =
      representedSpaceMap B S hS h ≫ representedSpaceMap B S hS t := by
    rw [representedSpaceMap_comp, representedSpaceMap_comp, residueFieldSiteHom_comp]
  have e4 : Nonempty ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t')).obj
      ((smallEtaleDerivedModulePullback B S hS gS).obj K) ≅
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS h)).obj
        ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t)).obj K)) := by
    refine ⟨(smallEtaleDerivedModulePullbackCompIso B S hS _ gS).app K ≪≫ ?_ ≪≫
      ((smallEtaleDerivedModulePullbackCompIso B S hS _ _).app K).symm⟩
    rw [hm]
  obtain ⟨e4⟩ := e4
  let RΓ' := representedAffineDerivedSections B S hS (residueFieldSiteObj B S hS U' y')
  let chain : baseChangeDerivedSections f' t' F' ≅
      (representedAffineDerivedExtension B S hS h).functor.obj
        (baseChangeDerivedSections f t F) :=
    RΓ'.mapIso (e1.symm ≪≫
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS t')).mapIso e2.symm ≪≫
      e4) ≪≫ e5.symm ≪≫
    (representedAffineDerivedExtension B S hS h).functor.mapIso
      ((representedAffineDerivedSections B S hS (residueFieldSiteObj B S hS U y)).mapIso e3)
  exact (((DerivedCategory.homologyFunctor _ i).mapIso chain).toLinearEquiv.finrank_eq).trans
    (finrank_homology_totalDerivedExtensionScalars_of_isField (isField_residueFieldSiteObj U y)
      (isField_residueFieldSiteObj U' y') _ _ i)

section Affine

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- **The Betti numbers over an affine base.** For `Y` affine with `A = Γ(Y, 𝒪)`,
`β_i(y) = dim_{κ(𝔭)} Hⁱ(K ⊗^L_A κ(𝔭))`, where `K = RΓ(Y, Rf_*𝓕)` and `𝔭` is the prime of `A`
corresponding to `y`. -/
theorem fibreBetti_eq_comp_isoSpec (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F) (i : ℤ) :
    fibreBetti f F i =
      StacksDraft.Perfect.fibreBetti.{u, u} ((representedAffineDerivedSections B S hS U).obj
        ((derivedModulePushforward B S hS f).obj ((DerivedCategory.singleFunctor _ 0).obj F))) i ∘
        ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom.base := by
  funext y
  let Y := (BigFppfOver.toScheme B S hS).obj U
  let q := Y.isoSpec.hom.base y
  let k : residueFieldSiteObj B S hS U y ⟶ residueFieldSiteObject B hS
      (specGlobalSectionsPoint B S hS U q.asIdeal)
      (contains_spec_residueField_specGlobalSectionsPoint B S hS U q.asIdeal) :=
    Over.homMk ⟨Spec.map (Y.isoSpec.hom.residueFieldMap y)⟩ (by
      ext1
      change Spec.map (Y.isoSpec.hom.residueFieldMap y) ≫
          ((Spec Γ(Y, ⊤)).fromSpecResidueField q ≫ Y.isoSpec.inv ≫ B.inclusion.map U.hom) =
        Y.fromSpecResidueField y ≫ U.hom.hom
      rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, Iso.hom_inv_id_assoc]
      rfl)
  have hk : k ≫ residueFieldSiteMapOfIsAffine B S hS U q.asIdeal =
      residueFieldSiteHom B S hS U y := by
    ext1
    ext1
    change Spec.map (Y.isoSpec.hom.residueFieldMap y) ≫
        ((Spec Γ(Y, ⊤)).fromSpecResidueField q ≫ Y.isoSpec.inv) = Y.fromSpecResidueField y
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact (finrank_homology_baseChangeDerivedSections_eq f hf hfp F hFfp hF _ _ k hk
    (isField_residueFieldSiteObj U y)
    ((residueFieldSiteObjectRingEquivOfIsAffine B S hS U q.asIdeal).toMulEquiv.isField
      (Field.toIsField _)) i).trans
    (finrank_homology_baseChangeDerivedSections_residueFieldSiteMapOfIsAffine f hf hfp F hFfp hF
      q.asIdeal i)

end Affine

/-- **Locally, `β_i` is the derived-fibre Betti function of a pseudo-coherent complex of
modules.** Every point of `Y` lies in the image of an open embedding `φ : Spec R → Y` with
`β_i ∘ φ = (𝔭 ↦ dim_{κ(𝔭)} Hⁱ(M ⊗^L_R κ(𝔭)))` for some pseudo-coherent `M ∈ D(R)`. -/
theorem exists_isOpenEmbedding_fibreBetti_comp_eq (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F) (i : ℤ)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ (R : CommRingCat.{u}) (M : DerivedCategory (ModuleCat.{u} R))
      (φ : PrimeSpectrum R → (BigFppfOver.toScheme B S hS).obj U),
      Topology.IsOpenEmbedding φ ∧ x ∈ Set.range φ ∧
        StacksDraft.PseudoCoherence.IsPseudoCoherent M ∧
        fibreBetti f F i ∘ φ = StacksDraft.Perfect.fibreBetti.{u, u} M i := by
  let Y := (BigFppfOver.toScheme B S hS).obj U
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let T := siteOpenObject B S hS U W
  let g : T ⟶ U := Over.homMk (B.inclusion.preimage
    (X := B.obj ((Scheme.size_coe_opens_le _ W).trans_lt U.left.property))
    (Y := U.left) (Scheme.Opens.ι W)) (by rfl)
  have hg : (BigFppfOver.toScheme B S hS).map g = (Scheme.Opens.ι W) :=
    B.inclusion.map_preimage
      (X := B.obj ((Scheme.size_coe_opens_le _ W).trans_lt U.left.property)) (Y := U.left)
      (Scheme.Opens.ι W)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hW
  let gS := representedSpaceMap B S hS g
  let f' := pullback.snd f gS
  let F' := (modulePullback B S hS (pullback.fst f gS)).obj F
  obtain ⟨hf', hfp', hF'fp, hF'⟩ :=
    baseChange_isProper_and_isFinitePresentation f hf hfp F hFfp hF g
  have := isQuasicoherentOnSite_of_isFinitePresentation F hFfp
  have := isQuasicoherentOnSite_of_isFinitePresentation F' hF'fp
  let M := (representedAffineDerivedSections B S hS T).obj
    ((derivedModulePushforward B S hS f').obj ((DerivedCategory.singleFunctor _ 0).obj F'))
  let h := Scheme.homeoOfIso ((BigFppfOver.toScheme B S hS).obj T).isoSpec
  refine ⟨Γ((BigFppfOver.toScheme B S hS).obj T, ⊤), M,
    ((BigFppfOver.toScheme B S hS).map g).base ∘ h.symm, ?_, ?_,
    StacksDraft.Perfect.isPseudoCoherent_of_isPerfect.{u, u} _
      (isPerfect_representedAffineDerivedSections_obj B S hS T _
        (isPerfect_derivedModulePushforward_single_and_isIso_baseChange f' hf' hfp' F' hF'fp
          hF').1), ?_⟩
  · rw [hg]
    exact (Scheme.Opens.ι W).isOpenEmbedding.comp h.symm.isOpenEmbedding
  · let w : (BigFppfOver.toScheme B S hS).obj T := ⟨x, hxW⟩
    refine ⟨h w, ?_⟩
    change ((BigFppfOver.toScheme B S hS).map g).base (h.symm (h w)) = x
    rw [h.symm_apply_apply, hg]
    rfl
  · funext z
    change (fibreBetti f F i ∘ ((BigFppfOver.toScheme B S hS).map g).base) (h.symm z) = _
    rw [← fibreBetti_baseChange f hf hfp F hFfp hF g i,
      fibreBetti_eq_comp_isoSpec f' hf' hfp' F' hF'fp hF' i]
    exact congrArg (StacksDraft.Perfect.fibreBetti.{u, u} M i) (h.apply_symm_apply z)

/-- **Stacks 0E0R, part (2): the Betti numbers of the fibres are upper semicontinuous.** For
`f : X ⟶ Y` proper and of finite presentation and `𝓕` of finite presentation and flat over `Y`,
the function `y ↦ dim_{κ(y)} Hⁱ(X_y, 𝓕_y)` is upper semicontinuous on `Y`. -/
@[stacks 0E0R "(2)"]
theorem upperSemicontinuous_fibreBetti (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F) (i : ℤ) :
    UpperSemicontinuous (fibreBetti f F i) := by
  intro x n hn
  obtain ⟨R, M, φ, hφ, ⟨z, rfl⟩, hM, heq⟩ :=
    exists_isOpenEmbedding_fibreBetti_comp_eq f hf hfp F hFfp hF i x
  have hz := StacksDraft.Perfect.upperSemicontinuous_fibreBetti_of_isPseudoCoherent.{u, u} M hM
    i z n (by rw [← heq]; exact hn)
  rw [← heq] at hz
  rw [← hφ.map_nhds_eq z, Filter.eventually_map]
  exact hz

/-- **Stacks 0E0R, part (3): the level sets of the Betti numbers of the fibres are locally
constructible.** For `f : X ⟶ Y` proper and of finite presentation and `𝓕` of finite
presentation and flat over `Y`, each set `{y | dim_{κ(y)} Hⁱ(X_y, 𝓕_y) = n}` is locally
constructible in `Y`. -/
@[stacks 0E0R "(3)"]
theorem isLocallyConstructible_fibreBetti_preimage (hf : IsProper B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hFfp : F.IsFinitePresentation) (hF : IsFlatOver B S hS X.2 f.hom F) (i : ℤ) (n : ℕ) :
    Topology.IsLocallyConstructible (fibreBetti f F i ⁻¹' {n}) := by
  intro x
  obtain ⟨R, M, φ, hφ, hx, hM, heq⟩ :=
    exists_isOpenEmbedding_fibreBetti_comp_eq f hf hfp F hFfp hF i x
  refine ⟨Set.range φ, hφ.isOpen_range.mem_nhds hx, hφ.isOpen_range, ?_⟩
  let e := hφ.isEmbedding.toHomeomorph
  convert (StacksDraft.Perfect.isConstructible_fibreBetti_preimage M hM i n
    ).preimage_of_isOpenEmbedding e.symm.isOpenEmbedding using 1
  ext u
  rw [← heq]
  simp only [Set.mem_preimage, Function.comp_apply]
  rw [show φ (e.symm u) = (u : (BigFppfOver.toScheme B S hS).obj U) from
    congrArg Subtype.val (e.apply_symm_apply u)]

end AlgebraicGeometry.Space
