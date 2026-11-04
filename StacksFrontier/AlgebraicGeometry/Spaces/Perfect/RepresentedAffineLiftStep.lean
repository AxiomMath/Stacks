module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedPerfectConverse
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.AffineSupportedLiftHom
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresOpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport

/-!
# Lifting along an open of an affine represented algebraic space

Let `V₀` be an object of the big fppf site over `S` with affine underlying scheme, let
`O ⊆ V₀` be a quasi-compact open with inclusion `ι : O ⟶ V₀`, and let `Z ⊆ V₀` be closed with
quasi-compact complement.  On the small étale sites of the represented algebraic spaces
`h_{V₀}` and `h_O`: for a perfect `P` on `h_O` supported over `Z`, an object `G` of
`D_QCoh(𝒪_{h_{V₀}})` and a morphism `α : P ⟶ G|_O`, there are a perfect `Q` on `h_{V₀}`
supported over `Z`, an isomorphism `c : P ⊕ P[1] ≅ Q|_O` and a morphism `b : Q ⟶ G` with
`b|_O ∘ c = α ∘ pr₁`.

## Main results

* `CategoryTheory.exists_biprod_shift_iso_comp_map_eq`: a lift of `F ⊕ F[1]` carries across a
  comparison functor commuting with the shift.
* `AlgebraicGeometry.Space.exists_representedDerivedAssociatedModule_map_eq`: `ε^*` is full on
  `D_QCoh`.
* `AlgebraicGeometry.Space.exists_represented_supported_lift_biprod_shift_hom`: the lift of
  `α : P ⟶ G|_O` described above.

## References

* [Stacks Project, Tag 08HN](https://stacks.math.columbia.edu/tag/08HN)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-- Let `ε : D₀ ⥤ D` and `ε' : D₀' ⥤ D'` be functors, `ε'` additive and commuting with the shift,
intertwining `R₀ : D₀ ⥤ D₀'` and `R : D ⥤ D'` through `σ : R₀ ⋙ ε' ≅ ε ⋙ R`.  Let
`ε'F₀ ≅ P`, `εG₀ ≅ G`, let `α : P ⟶ R G` be the image of `α₀ : F₀ ⟶ R₀ G₀`, and let
`c₀ : F₀ ⊕ F₀[1] ≅ R₀ Q₀`, `b₀ : Q₀ ⟶ G₀` satisfy `c₀ ≫ R₀ b₀ = pr₁ ≫ α₀`.  Then there is
`c : P ⊕ P[1] ≅ R (ε Q₀)` with `c ≫ R (ε b₀ ≫ (εG₀ ≅ G)) = pr₁ ≫ α`. -/
theorem exists_biprod_shift_iso_comp_map_eq {D₀ D₀' D D' : Type*} [Category D₀] [Category D₀']
    [Category D] [Category D'] [Preadditive D₀'] [Preadditive D'] [hD₀' : HasBinaryBiproducts D₀']
    [hD' : HasBinaryBiproducts D'] [HasShift D₀' ℤ] [HasShift D' ℤ]
    (ε : D₀ ⥤ D) (ε' : D₀' ⥤ D') [ε'.Additive] [hε' : ε'.CommShift ℤ] (R₀ : D₀ ⥤ D₀') (R : D ⥤ D')
    (σ : R₀ ⋙ ε' ≅ ε ⋙ R) {P : D'} {G : D} {F₀ : D₀'} {G₀ Q₀ : D₀}
    (eP : ε'.obj F₀ ≅ P) (eG : ε.obj G₀ ≅ G) (α : P ⟶ R.obj G) (α₀ : F₀ ⟶ R₀.obj G₀)
    (hα : ε'.map α₀ = eP.hom ≫ α ≫ R.map eG.inv ≫ σ.inv.app G₀)
    (c₀ : F₀ ⊞ F₀⟦(1 : ℤ)⟧ ≅ R₀.obj Q₀) (b₀ : Q₀ ⟶ G₀)
    (hc₀ : c₀.hom ≫ R₀.map b₀ = biprod.fst ≫ α₀) :
    ∃ c : P ⊞ P⟦(1 : ℤ)⟧ ≅ R.obj (ε.obj Q₀),
      c.hom ≫ R.map (ε.map b₀ ≫ eG.hom) = biprod.fst ≫ α := by
  have : PreservesBinaryBiproducts ε' := preservesBinaryBiproducts_of_preservesBiproducts ε'
  refine ⟨biprod.mapIso eP.symm ((shiftFunctor D' (1 : ℤ)).mapIso eP.symm) ≪≫
    biprod.mapIso (Iso.refl _) ((ε'.commShiftIso (1 : ℤ)).app F₀).symm ≪≫
    (ε'.mapBiprod _ _).symm ≪≫ ε'.mapIso c₀ ≪≫ σ.app Q₀, ?_⟩
  have hσ : σ.hom.app Q₀ ≫ R.map (ε.map b₀) = ε'.map (R₀.map b₀) ≫ σ.hom.app G₀ :=
    (σ.hom.naturality b₀).symm
  have hc : ε'.map c₀.hom ≫ ε'.map (R₀.map b₀) = ε'.map biprod.fst ≫ ε'.map α₀ := by
    rw [← Functor.map_comp, hc₀, Functor.map_comp]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc, Functor.map_comp]
  rw [reassoc_of% hσ, reassoc_of% hc, hα]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id, Functor.map_id,
    ← Functor.map_comp, Category.comp_id]
  have h₁ : biprod.desc (ε'.map biprod.inl) (ε'.map biprod.inr) ≫
      ε'.map (biprod.fst : F₀ ⊞ F₀⟦(1 : ℤ)⟧ ⟶ F₀) = biprod.fst := by
    ext <;> simp [← Functor.map_comp]
  rw [Iso.symm_hom, Functor.mapBiprod_inv, reassoc_of% h₁]
  simp

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/-- The derived category of sheaves of modules on a scheme has binary biproducts. -/
theorem hasBinaryBiproducts_derivedCategory_modules (X : Scheme.{u}) :
    HasBinaryBiproducts (DerivedCategory X.Modules) :=
  inferInstance

attribute [local instance] SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance 10000] SmallEtale.hasSheafify_smallEtale
  SmallEtale.wEqualsLocallyBijective_smallEtale smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

/-- `ε^*` on a represented algebraic space is additive. -/
instance additive_representedDerivedAssociatedModule (T : BigFppfOver B S hS) :
    (representedDerivedAssociatedModule B S hS T).Additive :=
  inferInstanceAs ((representedAssociatedModule B S hS T
    (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategory).Additive

/-- `ε^*` on a represented algebraic space commutes with the shift. -/
noncomputable instance commShift_representedDerivedAssociatedModule (T : BigFppfOver B S hS) :
    (representedDerivedAssociatedModule B S hS T).CommShift ℤ :=
  inferInstanceAs (((representedAssociatedModule B S hS T
    (isAlgebraicSpace_yoneda B S hS T)).mapDerivedCategory).CommShift ℤ)

section Full

variable (T : BigFppfOver B S hS)

/-- `ε^*` is full on `D_QCoh`: a morphism `ε^*ω ⟶ ε^*ω'` between the images of
objects with quasi-coherent cohomology is `ε^*` of a morphism `ω ⟶ ω'`. -/
theorem exists_representedDerivedAssociatedModule_map_eq
    (ω ω' : DerivedCategory ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (hω : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω).IsQuasicoherent)
    (hω' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj ω').IsQuasicoherent)
    (f : (representedDerivedAssociatedModule B S hS T).obj ω ⟶
      (representedDerivedAssociatedModule B S hS T).obj ω') :
    ∃ g : ω ⟶ ω', (representedDerivedAssociatedModule B S hS T).map g = f := by
  have := _root_.AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence.{u + 1}
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  let A := _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  let E := A ⋙ (representedSmallEtaleModuleEquivalence B S hS T).functor
  have : E.Additive :=
    additive_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  have : PreservesFiniteLimits E :=
    preservesFiniteLimits_representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)
  have : PreservesFiniteColimits E :=
    preservesFiniteColimits_representedAssociatedModule B S hS T
      (isAlgebraicSpace_yoneda B S hS T)
  let c := Stacks.DerivedGlueing.mapDerivedCategoryCompIso A
    (representedSmallEtaleModuleEquivalence B S hS T).functor
  let ε₂ := E.mapDerivedCategory
  let f' : ε₂.obj ω ⟶ ε₂.obj ω' := f
  let f₁ := c.hom.app ω ≫ f' ≫ c.inv.app ω'
  let f₂ := (representedDerivedModuleEquivalence B S hS T).fullyFaithfulFunctor.preimage f₁
  let ω₀ : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)).FullSubcategory :=
    ⟨ω, hω⟩
  let ω₀' : (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf)).FullSubcategory :=
    ⟨ω', hω'⟩
  let F := _root_.AlgebraicGeometry.SmallEtale.derivedAssociatedModule.{u + 1}
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property
  let ιP := DerivedCategoryB.derivedCategoryB (_root_.AlgebraicGeometry.SmallEtale.qcohOnSite
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T) T.left.property)
  let f₂' : (F.obj ω₀).obj ⟶ (F.obj ω₀').obj := f₂
  let f₃ : F.obj ω₀ ⟶ F.obj ω₀' := (ObjectProperty.fullyFaithfulι ιP).preimage f₂'
  let g := (Functor.FullyFaithful.ofFullyFaithful F).preimage f₃
  refine ⟨g.hom, ?_⟩
  have h₃ : F.map g = f₃ := (Functor.FullyFaithful.ofFullyFaithful F).map_preimage f₃
  have h₃' : ιP.ι.map f₃ = f₂' :=
    (ObjectProperty.fullyFaithfulι ιP).map_preimage (X := F.obj ω₀) (Y := F.obj ω₀') f₂'
  have h₂ : A.mapDerivedCategory.map g.hom = f₂ := (congrArg ιP.ι.map h₃).trans h₃'
  have h₁ : (representedDerivedModuleEquivalence B S hS T).functor.map f₂ = f₁ :=
    (representedDerivedModuleEquivalence B S hS T).fullyFaithfulFunctor.map_preimage f₁
  suffices H : ε₂.map g.hom = f' from H
  have hnat := c.hom.naturality g.hom
  rw [← Iso.cancel_iso_hom_left (c.app ω)]
  refine (hnat.symm.trans ?_)
  show (representedDerivedModuleEquivalence B S hS T).functor.map
    (A.mapDerivedCategory.map g.hom) ≫ c.hom.app ω' = c.hom.app ω ≫ f'
  rw [h₂, h₁]
  show (c.hom.app ω ≫ f' ≫ c.inv.app ω') ≫ c.hom.app ω' = c.hom.app ω ≫ f'
  calc (c.hom.app ω ≫ f' ≫ c.inv.app ω') ≫ c.hom.app ω'
      = c.hom.app ω ≫ f' ≫ c.inv.app ω' ≫ c.hom.app ω' := by simp only [Category.assoc]
    _ = c.hom.app ω ≫ f' := by rw [Iso.inv_hom_id_app, Category.comp_id]

end Full

section Support

attribute [local instance] pointTopology

variable (T : BigFppfOver B S hS)

/-- Support descends along `ε^*`: if `ε^*K` is supported over `Z`, for `K` with
quasi-coherent cohomology, then `K` is supported on `Z`. -/
theorem cohomologySupportedOn_of_representedDerivedAssociatedModule
    (K : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent)
    (Z : Set ((BigFppfOver.toScheme B S hS).obj T))
    (h : CohomologySupportedOn B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
      ((pointsEquivScheme B S hS T) ⁻¹' Z) ((representedDerivedAssociatedModule B S hS T).obj K)) :
    AlgebraicGeometry.CohomologySupportedOn
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf Z K := by
  intro i x hx
  by_contra hne
  have hp := (mem_supportOfSheaf_homology_representedDerivedAssociatedModule_iff B S hS T K i (hK i)
    ((schemePointsHomeomorph B S hS T).symm x)).2 (by rwa [Homeomorph.apply_symm_apply])
  exact hx (by simpa [schemePointsHomeomorph] using h i hp)

/-- Support ascends along `ε^*`: if `K`, with quasi-coherent cohomology, is
supported on `Z`, then `ε^*K` is supported over `Z`. -/
theorem cohomologySupportedOn_representedDerivedAssociatedModule
    (K : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj T).Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent)
    (Z : Set ((BigFppfOver.toScheme B S hS).obj T))
    (h : AlgebraicGeometry.CohomologySupportedOn
      ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf Z K) :
    CohomologySupportedOn B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)
      ((pointsEquivScheme B S hS T) ⁻¹' Z)
      ((representedDerivedAssociatedModule B S hS T).obj K) := by
  intro i p hp
  rw [mem_supportOfSheaf_homology_representedDerivedAssociatedModule_iff B S hS T K i (hK i)] at hp
  exact not_not.1 fun hpZ => hp (h i _ hpZ)

end Support

section Step

variable (V₀ : BigFppfOver B S hS) (O : ((BigFppfOver.toScheme B S hS).obj V₀).Opens)

/-- The inclusion of an open of the scheme underlying `V₀`, read on the represented algebraic
spaces, is étale. -/
theorem isEtale_representedSpaceMap_openIncl :
    IsEtale B S hS (representedSpaceMap B S hS (openIncl B S hS V₀ O)).hom :=
  (isEtale_iff_presheaf_of_yoneda B S hS _).2
    ((presheaf_yoneda_map_etale_iff B S hS (openIncl B S hS V₀ O)).2
      (inferInstanceAs (Etale O.ι)))

/-- The points of a represented algebraic space map to the points of the scheme compatibly with
morphisms of the site. -/
theorem pointsEquivScheme_pointsMap_yoneda_map {U W : BigFppfOver B S hS} (h : U ⟶ W)
    (p : points B S hS (yoneda.obj U)) :
    pointsEquivScheme B S hS W (pointsMap B S hS (yoneda.obj U) (yoneda.map h) p) =
      (BigFppfOver.toScheme B S hS).map h (pointsEquivScheme B S hS U p) := by
  rw [← (pointsEquivScheme B S hS U).symm_apply_apply p,
    ChartBranch.pointsEquivScheme_symm_pointsMap, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- Let `V₀` have affine underlying scheme, `O ⊆ V₀` a quasi-compact open with inclusion `ι`,
and `Z ⊆ V₀` closed with quasi-compact complement. For a perfect `P` on `h_O` supported over
`Z`, an object `G` of `D_QCoh(𝒪_{h_{V₀}})` and `α : P ⟶ ι^*G`, there are a perfect `Q` on
`h_{V₀}` supported over `Z`, an isomorphism `c : P ⊕ P[1] ≅ ι^*Q` and `b : Q ⟶ G` with
`c ≫ ι^*b = pr₁ ≫ α`. -/
theorem exists_represented_supported_lift_biprod_shift_hom
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V₀)]
    (hO : IsCompact (O : Set ((BigFppfOver.toScheme B S hS).obj V₀)))
    (Z : Set ((BigFppfOver.toScheme B S hS).obj V₀)) (hZ : IsClosed Z) (hZc : IsCompact Zᶜ)
    (P : DerivedCategory (Modules.{u, u} B S hS (yoneda.obj (openObj B S hS V₀ O))
      (isAlgebraicSpace_yoneda B S hS _)))
    (hP : (smallEtaleRingedSite B S hS (yoneda.obj (openObj B S hS V₀ O))
      (isAlgebraicSpace_yoneda B S hS _)).IsPerfect P)
    (hPZ : CohomologySupportedOn B S hS (yoneda.obj (openObj B S hS V₀ O))
      (isAlgebraicSpace_yoneda B S hS _)
      (pointsMap B S hS (yoneda.obj (openObj B S hS V₀ O)) (yoneda.map (openIncl B S hS V₀ O)) ⁻¹'
        ((pointsEquivScheme B S hS V₀) ⁻¹' Z)) P)
    (G : DerivedCategory
      (Modules.{u, u} B S hS (yoneda.obj V₀) (isAlgebraicSpace_yoneda B S hS V₀)))
    (hG : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj V₀)
          (isAlgebraicSpace_yoneda B S hS V₀)).O))) G)
    (α : P ⟶ (representedDerivedPullback B S hS (openIncl B S hS V₀ O)
      (isEtale_representedSpaceMap_openIncl B S hS V₀ O)).obj G) :
    ∃ Q : DerivedCategory
        (Modules.{u, u} B S hS (yoneda.obj V₀) (isAlgebraicSpace_yoneda B S hS V₀)),
      (smallEtaleRingedSite B S hS (yoneda.obj V₀)
        (isAlgebraicSpace_yoneda B S hS V₀)).IsPerfect Q ∧
      CohomologySupportedOn B S hS (yoneda.obj V₀) (isAlgebraicSpace_yoneda B S hS V₀)
        ((pointsEquivScheme B S hS V₀) ⁻¹' Z) Q ∧
      ∃ (c : P ⊞ P⟦(1 : ℤ)⟧ ≅ (representedDerivedPullback B S hS (openIncl B S hS V₀ O)
          (isEtale_representedSpaceMap_openIncl B S hS V₀ O)).obj Q) (b : Q ⟶ G),
        c.hom ≫ (representedDerivedPullback B S hS (openIncl B S hS V₀ O)
          (isEtale_representedSpaceMap_openIncl B S hS V₀ O)).map b = biprod.fst ≫ α := by
  let ι := openIncl B S hS V₀ O
  let hι := isEtale_representedSpaceMap_openIncl B S hS V₀ O
  have : Flat ((BigFppfOver.toScheme B S hS).map ι) := inferInstanceAs (Flat O.ι)
  obtain ⟨G₀, hG₀, ⟨eG⟩⟩ := exists_representedDerivedAssociatedModule_iso B S hS V₀ G hG
  have hPq := derivedCategoryB_of_isPseudoCoherent_unconditional B S hS
    (yoneda.obj (openObj B S hS V₀ O)) (isAlgebraicSpace_yoneda B S hS _) P
    (RingedSite.isPseudoCoherent_of_isPerfect_general _ hP)
  obtain ⟨F₀, hF₀, ⟨eP⟩⟩ :=
    exists_representedDerivedAssociatedModule_iso B S hS (openObj B S hS V₀ O) P hPq
  have hF₀perf := isPerfect_of_isPerfect_representedDerivedAssociatedModule B S hS
    (openObj B S hS V₀ O) F₀ hF₀ (by
      obtain ⟨Ec, hEc, ⟨i⟩⟩ := hP
      exact ⟨Ec, hEc, ⟨i ≪≫ eP.symm⟩⟩)
  have hF₀Z : AlgebraicGeometry.CohomologySupportedOn O.toScheme.ringCatSheaf
      (((BigFppfOver.toScheme B S hS).map (openIncl B S hS V₀ O)) ⁻¹' Z) F₀ := by
    refine cohomologySupportedOn_of_representedDerivedAssociatedModule B S hS
      (openObj B S hS V₀ O) F₀ hF₀ _ fun i p hp => ?_
    have := hPZ i ((supportOfSheaf_eq_of_iso B S hS
      ⟨yoneda.obj (openObj B S hS V₀ O), isAlgebraicSpace_yoneda B S hS _⟩
      ((DerivedCategory.homologyFunctor _ i).mapIso eP)).le hp)
    show (BigFppfOver.toScheme B S hS).map (openIncl B S hS V₀ O)
      (pointsEquivScheme B S hS _ p) ∈ Z
    rwa [← pointsEquivScheme_pointsMap_yoneda_map]
  let ε := representedDerivedAssociatedModule B S hS V₀
  let ε' := representedDerivedAssociatedModule B S hS (openObj B S hS V₀ O)
  let R₀ := Stacks.Duality.OpenImmersion.derivedRestrict O.ι
  let Rι := representedDerivedPullback B S hS ι hι
  let σ : R₀ ⋙ ε' ≅ ε ⋙ Rι :=
    Functor.isoWhiskerRight (Scheme.Modules.derivedRestrictIsoDerivedPullback O.ι) ε' ≪≫
      (representedDerivedAssociatedModulePullbackIso B S hS ι hι).symm
  have hRG₀ := Stacks.DerivedQCoh.OpenLift.isQuasicoherent_homology_derivedRestrict O G₀ hG₀
  obtain ⟨α₀, hα₀⟩ := exists_representedDerivedAssociatedModule_map_eq B S hS
    (openObj B S hS V₀ O) F₀ (R₀.obj G₀)
    hF₀ hRG₀ (eP.hom ≫ α ≫ Rι.map eG.inv ≫ σ.inv.app G₀)
  obtain ⟨Q₀, hQ₀, hQ₀Z, c₀, b₀, hc₀⟩ :=
    Stacks.DerivedQCoh.OpenLift.exists_supported_lift_biprod_shift_hom_of_isAffine _ Z hZ hZc O hO
      F₀ hF₀perf hF₀Z G₀ hG₀ α₀
  obtain ⟨c, hc⟩ := CategoryTheory.exists_biprod_shift_iso_comp_map_eq
    (hD₀' := hasBinaryBiproducts_derivedCategory_modules
      ((BigFppfOver.toScheme B S hS).obj (openObj B S hS V₀ O)))
    (hε' := commShift_representedDerivedAssociatedModule B S hS (openObj B S hS V₀ O)) ε
    (representedDerivedAssociatedModule B S hS (openObj B S hS V₀ O)) R₀ Rι σ eP eG α α₀
    hα₀ c₀ b₀ hc₀
  exact ⟨ε.obj Q₀, isPerfect_representedDerivedAssociatedModule B S hS V₀ Q₀ hQ₀,
    cohomologySupportedOn_representedDerivedAssociatedModule B S hS V₀ Q₀
      (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ Q₀ hQ₀) Z hQ₀Z,
    c, ε.map b₀ ≫ eG.hom, hc⟩

end Step

end AlgebraicGeometry.Space
