module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCechVanishingTensorPresheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfAffineCartesianModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleHigherDirectImage

/-!
# Cohomology on affine objects of the homology of a complex of pulled back quasi-coherent modules

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `X` one of its objects and
`𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃` a complex of quasi-coherent `𝒪_X`-modules on the spaces-étale site of `X`. The
homology `𝓗` of the pulled back complex `a_X^*𝓕₁ ⟶ a_X^*𝓕₂ ⟶ a_X^*𝓕₃` on `(Spaces/X)_fppf` has
vanishing higher cohomology on every affine object.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isZero_H'_of_isCartesian`: vanishing of higher
  cohomology on affine objects for a sheaf of modules cartesian along flat maps of affines.
* `AlgebraicGeometry.BigFppfSpaceSite.isZero_H'_homology`: the vanishing for the homology of a
  complex of locally presented sheaves of modules.
* `AlgebraicGeometry.BigFppfSpaceSite.isZero_H'_homology_pullback`: the vanishing for the
  homology of a complex of pulled back quasi-coherent modules.

## References

* [Stacks Project, Tag 0DGQ](https://stacks.math.columbia.edu/tag/0DGQ)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u' v' u

namespace Stacks.PresheafOfModules

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {J : GrothendieckTopology C}
  {K : GrothendieckTopology D} (G : C ⥤ D) [G.IsContinuous J K] (R : Sheaf K RingCat.{u'})

/-- The underlying abelian presheaf of the restriction of a sheaf of modules along a continuous
functor is the restriction of its underlying abelian presheaf. -/
theorem pushforward_id_val_presheaf (M : SheafOfModules.{u'} R) :
    ((SheafOfModules.pushforward.{u'}
      (𝟙 ((G.sheafPushforwardContinuous RingCat.{u'} J K).obj R))).obj M).val.presheaf =
      G.op ⋙ M.val.presheaf := rfl

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {X : T.Spaces}

open AffineSchemesOver

namespace AffineFppfPresentation

variable {U : Over X} {E : PreZeroHypercover.{u + 1} U} (P : AffineFppfPresentation E)

include P in
/-- The members of a finite affine fppf family have flat ring maps. -/
theorem flat_ringFunctor_map_family_f (j : E.I₀) :
    ((ringFunctor T U).map (P.family.f j).op).hom.Flat := by
  have h := P.fppf
  rw [Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at h
  exact flat_ringFunctor_map_of_flat _ (h.2 j).1

/-- The positive Čech cohomology of a sheaf of modules cartesian along flat maps of affines on a
finite affine fppf family vanishes. -/
theorem isZero_cechCohomology_succ_of_isCartesian
    (H : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (hH : ∀ {Y : AffineSchemesOver T U} (g : Y ⟶ P.base),
      ((ringFunctor T U).map g.op).hom.Flat →
        IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
          (R := ringFunctor T U) (affineRestriction (U := U) H).val g.op))
    [Finite E.I₀] [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
    (p : ℕ) :
    IsZero (Stacks.CechSite.cechCohomology E ((SheafOfModules.toSheaf _).obj H).obj (p + 1)) := by
  let := hasFiniteLimits P.W P.eW P.isAffine_W
  have := preservesPullbacks_toOver P.W P.eW
  have : Finite P.family.I₀ := inferInstanceAs (Finite E.I₀)
  have : ∀ (n : ℕ) (i : Fin (n + 1) → (P.family.map (toOver T U)).I₀),
      HasProduct (fun a ↦ Over.mk ((P.family.map (toOver T U)).f (i a))) :=
    Stacks.Sites.hasProduct_fibreProducts _ (fun _ _ _ => inferInstance)
  have hiso : ∀ (n : ℕ) (i : Fin (n + 1) → P.family.I₀),
      IsIso (Stacks.CechSite.cechProductMapOfFunctor (toOver T U) P.family n i) := fun n i =>
    have := Stacks.Sites.preservesLimit_fibreProducts_overPost (toOver T U) P.family
      (fun _ _ _ => inferInstance) (fun _ _ _ => inferInstance) n i
    Stacks.CechSite.isIso_cechProductMapOfFunctor _ _ n i
  let hT₀ := isTerminalOfIso P.W P.isAffine_W P.eW
  let M := (affineRestriction (U := U) H).val
  let κ := Stacks.TerminalBaseChange.baseChangeComparison.{u + 1} (ringPresheaf (T := T) (V := U))
    hT₀ M
  have hκ : ∀ (n : ℕ) (i : Fin (n + 1) → P.family.I₀),
      IsIso (((PresheafOfModules.toPresheaf _).map κ).app
        (op (∏ᶜ (fun a ↦ Over.mk (P.family.f (i a)))).left)) := by
    intro n i
    have hY := Stacks.FlatObjectsSubsite.isFlatOver_of_isLimit_fan (ringFunctor T U) hT₀
      (fun h hg ↦ flat_ringFunctor_of_isPullback P.W P.eW h hg) (n + 1)
      (fun a ↦ Over.mk (P.family.f (i a)))
      (fun a ↦ Stacks.FlatObjectsSubsite.isFlatOver_of_flat _
        (P.flat_ringFunctor_map_family_f (i a)) (Stacks.FlatObjectsSubsite.isFlatOver_self _ _))
      _ (limit.isLimit _)
    have h₁ : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
        (R := ringFunctor T U) M (hT₀.from (∏ᶜ (fun a ↦ Over.mk (P.family.f (i a)))).left).op) :=
      hH (hT₀.from (∏ᶜ (fun a ↦ Over.mk (P.family.f (i a)))).left) hY
    have h₂ : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
        (R := Stacks.TerminalBaseChange.commPresheaf (ringPresheaf (T := T) (V := U))) M
        (Stacks.TerminalBaseChange.iota hT₀ (op (∏ᶜ (fun a ↦ Over.mk (P.family.f (i a)))).left))) :=
      h₁
    have : IsIso (κ.app (op (∏ᶜ (fun a ↦ Over.mk (P.family.f (i a)))).left)) := h₂
    exact Functor.map_isIso (forget₂ (ModuleCat _) AddCommGrpCat) _
  have := Stacks.CechSite.isIso_cechComplexFunctor_map P.family
    ((PresheafOfModules.toPresheaf _).map κ) hκ
  have h₀' := isZero_cechCohomology_baseChangePresheaf_succ P.W P.isAffine_W P.eW hT₀
    (M.obj (op P.base)) P.family P.fppf p
  have h₀a : IsZero (Stacks.CechSite.cechCohomology P.family M.presheaf (p + 1)) :=
    h₀'.of_iso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) (p + 1)).mapIso
      (asIso ((Stacks.CechSite.cechComplexFunctor P.family).map
        ((PresheafOfModules.toPresheaf _).map κ)))).symm
  have e₁ : M.presheaf = (toSlice T U).op ⋙ (H.over U).val.presheaf :=
    Stacks.PresheafOfModules.pushforward_id_val_presheaf
      (J := AffineSchemesOver.topology (T := T) (V := U))
      (K := (BigFppfSpaceOver.topology T X).over U) (toSlice T U) _ (H.over U)
  have e₂ : (H.over U).val.presheaf = (Over.forget U).op ⋙ H.val.presheaf :=
    Stacks.PresheafOfModules.pushforward_id_val_presheaf
      (J := (BigFppfSpaceOver.topology T X).over U) (K := BigFppfSpaceOver.topology T X)
      (Over.forget U) _ H
  have e₃ : M.presheaf = (toOver T U).op ⋙ ((SheafOfModules.toSheaf _).obj H).obj := by
    rw [e₁, e₂]
    rfl
  have h₀ : IsZero (Stacks.CechSite.cechCohomology P.family
      ((toOver T U).op ⋙ ((SheafOfModules.toSheaf _).obj H).obj) (p + 1)) := e₃ ▸ h₀a
  have h₁ : IsZero (Stacks.CechSite.cechCohomology (P.family.map (toOver T U))
      ((SheafOfModules.toSheaf _).obj H).obj (p + 1)) :=
    h₀.of_iso (Stacks.CechSite.cechCohomologyIsoOfFunctor _ _ _ hiso (p + 1))
  exact Stacks.CechSite.isZero_cechCohomology_of_isIso P.homOver P.bijective_homOver_s₀ _
    (p + 1) h₁

end AffineFppfPresentation

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- **Higher cohomology on `(Spaces/X)_fppf` of a sheaf of modules cartesian along flat maps of
affine schemes over every affine object vanishes on affine objects.** -/
theorem isZero_H'_of_isCartesian (H : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (hH : ∀ (U : Over X) (V₀ : T.Schemes)
      (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
      (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ U.left)
      {Y : AffineSchemesOver T U} (g : Y ⟶ ofIso V₀ hV₀ e),
      ((ringFunctor T U).map g.op).hom.Flat →
        IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
          (R := ringFunctor T U) (affineRestriction (U := U) H).val g.op))
    (U : Over X) (hU : BigFppfSpaceOver.IsAffineSchemeOver T X U) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj H) p U) := by
  let B : Set (Over X) := {U | BigFppfSpaceOver.IsAffineSchemeOver T X U}
  have hProducts : ∀ {U : Over X}
      (E : {E : PreZeroHypercover.{u + 1} U // E.sieve₀ ∈ BigFppfSpaceOver.topology T X U}),
      E ∈ {E | E ∈ affineFppfCoverings T X U ∧ U ∈ B} → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))) := fun E _ p i =>
    Stacks.Sites.hasProduct_fibreProducts E.1 (fun _ _ _ => inferInstance) p i
  refine Stacks.CechSite.sheafCohomology_isZero_of_cechCohomology_isZero.{u + 1, u + 1, u + 1}
    (BigFppfSpaceOver.topology T X) B (fun U => {E | E ∈ affineFppfCoverings T X U ∧ U ∈ B})
    hProducts ?_ ?_ _ ?_ U hU p hp
  · rintro U E ⟨⟨hfin, ⟨P⟩⟩, hU⟩
    refine ⟨hU, fun i => ⟨P.Y i, P.isAffine_Y i, ⟨P.eY i⟩⟩, fun p i => ?_⟩
    let := hProducts E ⟨⟨hfin, ⟨P⟩⟩, hU⟩
    exact P.isAffineSchemeOver_pi_left p i
  · intro U hU R hR
    obtain ⟨E, hE, hle⟩ := exists_affineFppfCoverings_le U hU R hR
    exact ⟨E, ⟨hE, hU⟩, hle⟩
  · rintro U E ⟨⟨hfin, ⟨P⟩⟩, hU⟩ p hp
    let := hProducts E ⟨⟨hfin, ⟨P⟩⟩, hU⟩
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have : Finite E.1.I₀ := hfin
    exact P.isZero_cechCohomology_succ_of_isCartesian H
      (fun g hg ↦ hH U P.W P.isAffine_W P.eW g hg) q

/-- The base-change comparison of the restriction to the flat affine schemes is that of the
restriction to all affine schemes, along the image morphism. -/
theorem isIso_restrictionBaseChange_affineRestriction_of_flat {U : Over X} (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ U.left)
    (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)) (Y : (FlatOver V₀ hV₀ e)ᵒᵖ)
    (h₁ : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
      (R := Stacks.TerminalBaseChange.commPresheaf (flatRingSheaf V₀ hV₀ e).obj)
      ((SheafOfModules.pushforward.{u + 1} (𝟙 (flatRingSheaf V₀ hV₀ e))).obj
        (affineRestriction (U := U) N)).val
      (Stacks.TerminalBaseChange.iota (flatIsTerminal V₀ hV₀ e) Y))) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
      (R := Stacks.TerminalBaseChange.commPresheaf
        (Stacks.DenseSubsiteModules.ringRestriction (AffineSchemesOver.topology (T := T) (V := U))
          ((BigFppfSpaceOver.topology T X).over U) (toSlice T U) sliceRingSheaf).obj)
      (affineRestriction (U := U) N).val
      ((flatι V₀ hV₀ e).op.map (Stacks.TerminalBaseChange.iota (flatIsTerminal V₀ hV₀ e) Y))) :=
  (Stacks.PresheafOfModules.isIso_restrictionBaseChange_pushforward_iff (flatι V₀ hV₀ e)
    (Stacks.DenseSubsiteModules.ringRestriction (AffineSchemesOver.topology (T := T) (V := U))
      ((BigFppfSpaceOver.topology T X).over U) (toSlice T U) sliceRingSheaf)
    (affineRestriction N) (Stacks.TerminalBaseChange.iota (flatIsTerminal V₀ hV₀ e) Y)).1 h₁

/-- A sheaf of modules whose comparison on the flat affine schemes over `U` is invertible is
cartesian over every morphism into `U` with flat ring map. -/
theorem isIso_restrictionBaseChange_of_isIso_flatComparison {U : Over X} (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ U.left)
    (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (h : IsIso ((flatComparison V₀ hV₀ e).app ((flatRestriction V₀ hV₀ e).obj N)))
    {Y : AffineSchemesOver T U} (g : Y ⟶ ofIso V₀ hV₀ e)
    (hg : ((ringFunctor T U).map g.op).hom.Flat) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
      (R := ringFunctor T U) (affineRestriction (U := U) N).val g.op) := by
  rw [isIso_flatComparison_app_iff] at h
  simp only [flatRestriction, Functor.comp_obj] at h
  obtain ⟨Y', rfl⟩ : ∃ Y' : FlatOver V₀ hV₀ e, Y'.obj = Y :=
    ⟨⟨Y, Stacks.FlatObjectsSubsite.isFlatOver_of_flat g hg
      (Stacks.FlatObjectsSubsite.isFlatOver_self _ _)⟩, rfl⟩
  have h₁ : IsIso ((Stacks.TerminalBaseChange.baseChangeComparison.{u + 1}
      (flatRingSheaf V₀ hV₀ e).obj (flatIsTerminal V₀ hV₀ e)
      ((SheafOfModules.pushforward.{u + 1} (𝟙 (flatRingSheaf V₀ hV₀ e))).obj
        (affineRestriction (U := U) N)).val).app (op Y')) :=
    Functor.map_isIso (PresheafOfModules.evaluation _ (op Y'))
      (Stacks.TerminalBaseChange.baseChangeComparison.{u + 1}
        (flatRingSheaf V₀ hV₀ e).obj (flatIsTerminal V₀ hV₀ e)
        ((SheafOfModules.pushforward.{u + 1} (𝟙 (flatRingSheaf V₀ hV₀ e))).obj
          (affineRestriction (U := U) N)).val)
  rw [Stacks.TerminalBaseChange.baseChangeComparison_app] at h₁
  have h₂ := isIso_restrictionBaseChange_affineRestriction_of_flat V₀ hV₀ e N (op Y') h₁
  have h₃ : IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
      (R := ringFunctor T U) (affineRestriction (U := U) N).val
      ((flatι V₀ hV₀ e).op.map (Stacks.TerminalBaseChange.iota (flatIsTerminal V₀ hV₀ e)
        (op Y')))) := h₂
  exact Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_eq_op (R := ringFunctor T U)
    (affineRestriction (U := U) N).val (A' := op (ofIso V₀ hV₀ e)) (B' := op Y'.obj) rfl rfl _ g.op
    (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        exact Quiver.Hom.unop_inj ((isTerminalOfIso V₀ hV₀ e).hom_ext _ _)) h₃

/-- **The homology of a complex of locally presented sheaves of modules on `(Spaces/X)_fppf` is
cartesian along flat maps of affine schemes.** -/
theorem isIso_restrictionBaseChange_homology
    (Q : ShortComplex (SheafOfModules.{u + 1} (bigFppfRingSheaf T X)))
    (hS : ∀ (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)), N = Q.X₁ ∨ N = Q.X₂ ∨ N = Q.X₃ →
      ∀ Z : BigFppfSpaceOver T X,
        Sieve.generate (fun (Z' : BigFppfSpaceOver T X) (_ : Z' ⟶ Z) ↦
          (N.over Z').HasGlobalPresentation) ∈ BigFppfSpaceOver.topology T X Z)
    (U : Over X) (V₀ : T.Schemes)
    (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
    (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ U.left)
    {Y : AffineSchemesOver T U} (g : Y ⟶ ofIso V₀ hV₀ e)
    (hg : ((ringFunctor T U).map g.op).hom.Flat) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{_, _, u + 1, u + 1}
      (R := ringFunctor T U) (affineRestriction (U := U) Q.homology).val g.op) := by
  have hcart : ∀ (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)),
      N = Q.X₁ ∨ N = Q.X₂ ∨ N = Q.X₃ → ∀ (Y' : FlatOver V₀ hV₀ e) (g' : Y'.obj ⟶ ofIso V₀ hV₀ e),
        IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u + 1, u + 1}
          (R := ringFunctor T U) (affineRestriction N).val g'.op) := by
    intro N hN Y' g'
    obtain rfl : g' = (isTerminalOfIso V₀ hV₀ e).from Y'.obj :=
      (isTerminalOfIso V₀ hV₀ e).hom_ext _ _
    exact isIso_restrictionBaseChange_of_flat V₀ hV₀ e N (hS N hN) _ Y'.property
  exact isIso_restrictionBaseChange_of_isIso_flatComparison V₀ hV₀ e Q.homology
    (isIso_flatComparison_app_homology V₀ hV₀ e Q (hcart _ (Or.inl rfl))
      (hcart _ (Or.inr (Or.inl rfl))) (hcart _ (Or.inr (Or.inr rfl)))) g hg

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- **The homology of a complex of locally presented sheaves of modules on `(Spaces/X)_fppf` has
no higher cohomology on affine objects.** -/
theorem isZero_H'_homology (Q : ShortComplex (SheafOfModules.{u + 1} (bigFppfRingSheaf T X)))
    (hS : ∀ (N : SheafOfModules.{u + 1} (bigFppfRingSheaf T X)), N = Q.X₁ ∨ N = Q.X₂ ∨ N = Q.X₃ →
      ∀ Z : BigFppfSpaceOver T X,
        Sieve.generate (fun (Z' : BigFppfSpaceOver T X) (_ : Z' ⟶ Z) ↦
          (N.over Z').HasGlobalPresentation) ∈ BigFppfSpaceOver.topology T X Z)
    (U : Over X) (hU : BigFppfSpaceOver.IsAffineSchemeOver T X U) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj Q.homology) p U) :=
  isZero_H'_of_isCartesian Q.homology
    (fun U V₀ hV₀ e _ g hg ↦ isIso_restrictionBaseChange_homology Q hS U V₀ hV₀ e g hg) U hU p hp

/-- **The pullback `a_X^*𝓕` of a quasi-coherent module has a global presentation over the members
of a covering of every object of `(Spaces/X)_fppf`.** -/
theorem generate_hasGlobalPresentation_pullback_mem
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [hF : F.IsQuasicoherentOnSite] (Z : BigFppfSpaceOver T X) :
    Sieve.generate (fun (Z' : BigFppfSpaceOver T X) (_ : Z' ⟶ Z) ↦
      (((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F).over
        Z').HasGlobalPresentation) ∈ BigFppfSpaceOver.topology T X Z := by
  have := (spacesEtaleInclusion_isMorphismOfSites T X).isContinuous
  have hcp := CoverPreserving.of_isContinuous
    (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X)
    (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X) (BigFppfSpaceOver.topology T X)
  obtain ⟨I, Vi, fi, hcov, hpres⟩ := hF.locally_hasGlobalPresentation
    (Space.SpacesEtale.final T.schemeSite S T.scheme_mem X)
  have h₁ := GrothendieckTopology.pullback_stable _ ((Over.mkIdTerminal (X := X)).from Z)
    (hcp.cover_preserve hcov)
  refine GrothendieckTopology.superset_covering _ ?_ h₁
  rintro Z' a ⟨W, g, c, hg, -⟩
  obtain ⟨W', k, f', ⟨i⟩, rfl⟩ := hg
  apply Sieve.le_generate
  exact SheafOfModules.HasGlobalPresentation.overMap.{u + 1, u + 1, u + 1} _
    (c ≫ (Space.SpacesEtale.inclusion T.schemeSite S T.scheme_mem X).map k)
    (hasGlobalPresentation_over_pullback F _ (hpres i))

/-- The pullback `a_X^*` of sheaves of modules is additive. -/
instance fppfToSpacesEtale_pullbackTopos_additive :
    (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.Additive :=
  (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    |>.left_adjoint_additive

attribute [local instance] hasExt_bigFppfSpaceOver in
/-- For a complex `𝓕₁ ⟶ 𝓕₂ ⟶ 𝓕₃` of quasi-coherent `𝒪_X`-modules, the homology `𝓗_fppf` of
`a_X^*𝓕₁ ⟶ a_X^*𝓕₂ ⟶ a_X^*𝓕₃` has `H^p((Spaces/X)_fppf / U, 𝓗_fppf) = 0` for `p > 0` and every
affine object `U`. -/
theorem isZero_H'_homology_pullback
    (Q : ShortComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)))
    [Q.X₁.IsQuasicoherentOnSite] [Q.X₂.IsQuasicoherentOnSite] [Q.X₃.IsQuasicoherentOnSite]
    (U : Over X) (hU : BigFppfSpaceOver.IsAffineSchemeOver T X U) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj
      (Q.map (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos).homology)
      p U) := by
  refine isZero_H'_homology _ ?_ U hU p hp
  rintro N (rfl | rfl | rfl) Z <;> exact generate_hasGlobalPresentation_pullback_mem _ Z

end AlgebraicGeometry.BigFppfSpaceSite

end
