module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfPushforwardQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfQuasicoherentHomologyCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfFlatAffineSchemesOver
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteBaseChangePresentation
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverTerminal
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteGlobalPoint

/-!
# The ringed point of global sections of an affine algebraic space

Let `T` be a big fppf site of algebraic spaces over a scheme `S` and `X` an object of `T` which is
the algebraic space of an affine scheme `V₀`, with ring `A = Γ(X, 𝒪_X)`. This file studies the
morphism of ringed sites

`p : (X_{spaces,étale}, 𝒪_X) ⟶ (pt, A)`

of `AlgebraicGeometry.RingedSite.toGlobalPoint`, at the final object of `X_{spaces,étale}`
presented by `V₀`. Its pullback `p^*` is the associated module functor `M ↦ M^a`, which on an
affine scheme `U` étale over `X` is `M ⊗_A 𝒪(U)` (Stacks 03DX). The facts proved are those of
Stacks 03DX (2) and of the exactness of `M ↦ M^a`:

* `p^*` is exact, the ring maps `A ⟶ 𝒪(U)` being flat for affine `U` étale over `X`;
* the unit `M ⟶ Γ(X, p^*M)` is invertible;
* the counit `p^*Γ(X, 𝓕) ⟶ 𝓕` is invertible for every quasi-coherent `𝓕`.

`M ↦ M^a` is `Stacks.DenseSubsiteBaseChange.associatedSheaf` on the dense subsite of the affine
schemes étale over `X`.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.affinePoint`: the final object of `X_{spaces,étale}`
  presented by `V₀`.
* `AlgebraicGeometry.BigFppfSpaceSite.affineAssociated`: `M ↦ M^a`, from modules over the ring of
  sections over `affinePoint` to modules on `X_{spaces,étale}`.
* `AlgebraicGeometry.BigFppfSpaceSite.affinePointHom`: the morphism `p` to the ringed point.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.affineAssociatedAdjunction`: `M ↦ M^a` is left adjoint to
  sections over `affinePoint`, and `affineAssociatedFullyFaithful`: it is fully faithful.
* `AlgebraicGeometry.BigFppfSpaceSite.preservesFiniteLimits_affineAssociated`: it is exact.
* `AlgebraicGeometry.BigFppfSpaceSite.exists_iso_affineAssociated_of_isQuasicoherentOnSite`:
  every quasi-coherent module is some `M^a`.
* `AlgebraicGeometry.BigFppfSpaceSite.isIso_affinePointHom_unit`,
  `AlgebraicGeometry.BigFppfSpaceSite.isIso_affinePointHom_counit_app`: the unit of `p^* ⊣ p_*`
  is invertible, and the counit is invertible at quasi-coherent modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DenseSubsiteBaseChange Stacks.DenseSubsiteModules

universe u

namespace Stacks.TerminalBaseChange

variable {C : Type*} [Category C] {X : C} (hX : IsTerminal X)

/-- Flatness of the ring maps out of the terminal object is unchanged along an equality of
presheaves of rings. -/
theorem flat_rho_iff_of_eq {O O' : Cᵒᵖ ⥤ RingCat.{u}} [CommSections O] [CommSections O']
    (h : O = O') (Y : Cᵒᵖ) : (rho O hX Y).Flat ↔ (rho O' hX Y).Flat := by
  subst h
  rfl

/-- **Base change along flat ring maps is exact**: if every ring map out of the terminal object
is flat, the base change presheaf `M ↦ (U ↦ O(U) ⊗ M)` preserves finite limits. -/
theorem preservesFiniteLimits_baseChangePresheaf_of_flat (O : Cᵒᵖ ⥤ RingCat.{u})
    [CommSections O] (hflat : ∀ Y : Cᵒᵖ, (rho O hX Y).Flat) :
    PreservesFiniteLimits (baseChangePresheaf.{u} O hX) := by
  refine ⟨fun J _ _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦
    ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun Y ↦ ?_)⟩⟩⟩⟩
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hflat Y)
  exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerLeft K
      (baseChangeEvaluationIso.{u} O hX Y)).symm _).symm
    (IsLimit.ofIsoLimit (isLimitOfPreserves (ModuleCat.extendScalars.{u, u, u} (rho O hX Y)) hc)
      (Cone.ext (Iso.refl _) (fun _ ↦ rfl)))

end Stacks.TerminalBaseChange

namespace Stacks.DenseSubsiteBaseChange

variable {C : Type*} [Category C] {C' : Type*} [Category C']
  {J : GrothendieckTopology C} {K : GrothendieckTopology C'}
  {v : C ⥤ C'} [v.IsDenseSubsite J K]
  {R : Sheaf K RingCat.{u}} [Stacks.TerminalBaseChange.CommSections (ringRestriction J K v R).obj]
  {X : C} {hX : IsTerminal X} (h : BaseChangeIsSheaf J K v R hX)

/-- **The base change sheaf on a dense subsite is exact** when the ring maps out of the terminal
object are flat. -/
theorem preservesFiniteLimits_baseChangeSheaf_of_flat
    (hflat : ∀ Y : Cᵒᵖ, (Stacks.TerminalBaseChange.rho (ringRestriction J K v R).obj hX Y).Flat) :
    PreservesFiniteLimits (baseChangeSheaf h) := by
  have := Stacks.TerminalBaseChange.preservesFiniteLimits_baseChangePresheaf_of_flat hX _ hflat
  have : PreservesFiniteLimits (baseChangeSheaf h ⋙ SheafOfModules.forget.{u} _) :=
    inferInstanceAs (PreservesFiniteLimits
      (Stacks.TerminalBaseChange.baseChangePresheaf.{u} (ringRestriction J K v R).obj hX))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (SheafOfModules.forget.{u} _)

/-- **`M ↦ M^a` is exact** when the ring maps out of the terminal object are flat. -/
theorem preservesFiniteLimits_associatedSheaf_of_flat
    [(v.sheafPushforwardContinuous AddCommGrpCat.{u} J K).IsEquivalence]
    (hflat : ∀ Y : Cᵒᵖ, (Stacks.TerminalBaseChange.rho (ringRestriction J K v R).obj hX Y).Flat) :
    PreservesFiniteLimits (associatedSheaf h) := by
  have := preservesFiniteLimits_baseChangeSheaf_of_flat h hflat
  exact comp_preservesFiniteLimits _ _

end Stacks.DenseSubsiteBaseChange

-- Instance search for the dense-subsite equivalences below exceeds the default budget.
set_option synthInstance.maxHeartbeats 400000

namespace AlgebraicGeometry.BigFppfSpaceSite

open EtaleAffineSchemesOver

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (X : T.Spaces)

/-- The ring sheaf of the ringed spaces-étale site of `X`. -/
abbrev spacesEtaleRing :
    Sheaf (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X) RingCat.{u + 1} :=
  Stacks.SheafOfModules.Tensor.ringSheaf
    (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O

/-- **Modules on `X_{spaces,étale}` are modules on its slice at the final object.** -/
def finalSliceModuleEquivalence :
    SheafOfModules.{u + 1} (spacesEtaleRing T X) ≌
      SheafOfModules.{u + 1} (sliceRingSheaf (W := Space.SpacesEtale.final T.schemeSite S
        T.scheme_mem X)) :=
  haveI := GrothendieckTopology.isDenseSubsite_overForget
    (Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X)
    (Space.SpacesEtale.final_isTerminal T.schemeSite S T.scheme_mem X)
  moduleRestrictionEquivalence _ _ (Over.forget (Space.SpacesEtale.final T.schemeSite S
    T.scheme_mem X)) (spacesEtaleRing T X)

variable {X} (V₀ : T.Schemes)
  (hV₀ : IsAffine ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).obj V₀))
  (e : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ X)

/-- The affine scheme `V₀`, as the terminal affine scheme étale over the final object. -/
abbrev affineChartTerminal :
    EtaleAffineSchemesOver (Space.SpacesEtale.final T.schemeSite S T.scheme_mem X) :=
  ofIso V₀ hV₀ e

/-- **The final object of `X_{spaces,étale}` presented by `V₀`**: the algebraic space of `V₀`,
étale over `X` through the identification `e`. -/
abbrev affinePoint : Space.SpacesEtale T.schemeSite S T.scheme_mem X :=
  ((toSmallSlice (Space.SpacesEtale.final T.schemeSite S T.scheme_mem X)).obj
    (affineChartTerminal T V₀ hV₀ e)).left

/-- `affinePoint` is final in `X_{spaces,étale}`. -/
def isTerminal_affinePoint : IsTerminal (affinePoint T V₀ hV₀ e) :=
  (Space.SpacesEtale.final_isTerminal T.schemeSite S T.scheme_mem X).ofIso
    (ObjectProperty.isoMk _ (Over.isoMk (show (affinePoint T V₀ hV₀ e).obj.left ≅
      (Space.SpacesEtale.final T.schemeSite S T.scheme_mem X).obj.left from e)
      (by rfl))).symm

/-- **The associated module `M ↦ M^a`** on `X_{spaces,étale}`, for a module `M` over the ring of
sections over `affinePoint`: on an affine scheme `U` étale over `X` its sections are
`𝒪(U) ⊗ M`. -/
def affineAssociated :
    ModuleCat.{u + 1} ((spacesEtaleRing T X).obj.obj (op (affinePoint T V₀ hV₀ e))) ⥤
      SheafOfModules.{u + 1} (spacesEtaleRing T X) :=
  associatedSheaf (baseChangeIsSheaf (W := Space.SpacesEtale.final T.schemeSite S T.scheme_mem X)
    V₀ hV₀ e) ⋙ (finalSliceModuleEquivalence T X).inverse

/-- **`M ↦ M^a` is left adjoint to sections over `affinePoint`.** -/
def affineAssociatedAdjunction :
    affineAssociated T V₀ hV₀ e ⊣
      SheafOfModules.evaluation (spacesEtaleRing T X) (op (affinePoint T V₀ hV₀ e)) :=
  ((associatedSheafAdj (baseChangeIsSheaf
    (W := Space.SpacesEtale.final T.schemeSite S T.scheme_mem X) V₀ hV₀ e)).comp
    (finalSliceModuleEquivalence T X).symm.toAdjunction).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

/-- **`M ↦ M^a` is fully faithful.** -/
def affineAssociatedFullyFaithful : (affineAssociated T V₀ hV₀ e).FullyFaithful :=
  (associatedSheafFullyFaithful (baseChangeIsSheaf
    (W := Space.SpacesEtale.final T.schemeSite S T.scheme_mem X) V₀ hV₀ e)).comp
    (finalSliceModuleEquivalence T X).fullyFaithfulInverse

/-! ### Exactness of `M ↦ M^a` -/

section Flat

variable {T} {W : Space.SpacesEtale T.schemeSite S T.scheme_mem X}
  (e' : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ W.obj.left)

/-- **An affine scheme étale over `X` is étale over `V₀`**: the morphism of schemes underlying
the unique map to the terminal affine scheme étale over `W` is étale. -/
theorem etale_from_isTerminalOfIso (A : EtaleAffineSchemesOver W) :
    Etale ((BigFppfOver.toScheme T.schemeSite S T.scheme_mem).map
      ((isTerminalOfIso V₀ hV₀ e').from A).hom.hom.left) := by
  let φ := ((isTerminalOfIso V₀ hV₀ e').from A).hom.hom.left
  have het : Space.IsEtale T.schemeSite S T.scheme_mem (yoneda.map φ) :=
    Space.isEtale_of_isEtale_over T.schemeSite S T.scheme_mem
      ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj A.obj.obj.left).property
      ((schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀).property X.property
      (yoneda.map φ) _ _ A.property (ofIso V₀ hV₀ e').property
      (congrArg (fun k ↦ (k ≫ W.obj.hom).hom)
        (CostructuredArrow.w ((isTerminalOfIso V₀ hV₀ e').from A).hom.hom))
  exact (Space.presheaf_yoneda_map_etale_iff T.schemeSite S T.scheme_mem φ).1
    ((Space.isEtale_iff_presheaf_of_yoneda T.schemeSite S T.scheme_mem (yoneda.map φ)).1 het)

/-- **The ring maps of the base change are flat**: for an affine scheme `U` étale over `W`, the
ring of `U` is flat over the ring of `V₀`. -/
theorem flat_rho_isTerminalOfIso (Y : (EtaleAffineSchemesOver W)ᵒᵖ) :
    (Stacks.TerminalBaseChange.rho (ringPresheaf (W := W)) (isTerminalOfIso V₀ hV₀ e') Y).Flat := by
  have : Stacks.TerminalBaseChange.CommSections
      ((IsEtaleAffineSchemeOver W).ι.op ⋙ AffineSchemesOver.ringPresheaf (T := T) (V := W.obj)) :=
    ⟨fun U ↦ Stacks.TerminalBaseChange.CommSections.mul_comm
      (O := AffineSchemesOver.ringPresheaf (T := T) (V := W.obj)) _⟩
  refine (Stacks.TerminalBaseChange.flat_rho_iff_of_eq (isTerminalOfIso V₀ hV₀ e')
    (O' := (IsEtaleAffineSchemeOver W).ι.op ⋙ AffineSchemesOver.ringPresheaf (T := T) (V := W.obj))
    rfl Y).2 ?_
  have := etale_from_isTerminalOfIso V₀ hV₀ e' Y.unop
  exact AffineSchemesOver.flat_ringFunctor_map_of_flat
    ((isTerminalOfIso V₀ hV₀ e').from Y.unop).hom inferInstance

/-- **`M ↦ M^a` on the slice at `W` is exact.** -/
theorem preservesFiniteLimits_associatedSheaf_isTerminalOfIso :
    PreservesFiniteLimits (associatedSheaf (baseChangeIsSheaf (W := W) V₀ hV₀ e')) :=
  preservesFiniteLimits_associatedSheaf_of_flat _ (flat_rho_isTerminalOfIso V₀ hV₀ e')

end Flat

/-- **`M ↦ M^a` is exact.** -/
theorem preservesFiniteLimits_affineAssociated :
    PreservesFiniteLimits (affineAssociated T V₀ hV₀ e) := by
  have h₁ := preservesFiniteLimits_associatedSheaf_isTerminalOfIso V₀ hV₀
    (W := Space.SpacesEtale.final T.schemeSite S T.scheme_mem X) e
  have := (finalSliceModuleEquivalence T X).toAdjunction.rightAdjoint_preservesLimits
  have h₂ : PreservesFiniteLimits (finalSliceModuleEquivalence T X).inverse := inferInstance
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₂

/-! ### Quasi-coherent modules are associated modules -/

section Quasicoherent

variable {T} {W : Space.SpacesEtale T.schemeSite S T.scheme_mem X}
  (e' : (schemeSpaceFunctor T.schemeSite S T.scheme_mem).obj V₀ ≅ W.obj.left)

/-- **Over an affine object `W` of the spaces-étale site, the direct image `a_{X,*}H` of a locally
presented module is `M^a`** for its module `M` of sections over `W`. -/
theorem nonempty_iso_associatedSheaf_pushforward_over
    (H : SheafOfModules.{u + 1} (bigFppfRingSheaf T X))
    (hH : ∀ Z : BigFppfSpaceOver T X,
      Sieve.generate (fun (Z' : BigFppfSpaceOver T X) (_ : Z' ⟶ Z) ↦
        (H.over Z').HasGlobalPresentation) ∈ BigFppfSpaceOver.topology T X Z) :
    ∃ M, Nonempty ((((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pushforwardTopos.obj
        H).over W) ≅ (associatedSheaf (baseChangeIsSheaf V₀ hV₀ e')).obj M) := by
  let hs := baseChangeIsSheaf V₀ hV₀ e'
  let N := pushforwardRestriction (W := W) H
  have hc : IsIso (Stacks.TerminalBaseChange.baseChangeComparison.{u + 1} (ringPresheaf (W := W))
      (isTerminalOfIso V₀ hV₀ e') N.val) :=
    Stacks.TerminalBaseChange.isIso_baseChangeComparison_of_forall _ _ _ (fun U ↦ by
      have h := isIso_restrictionBaseChange_pushforwardRestriction V₀ hV₀ e' H hH
        ((isTerminalOfIso V₀ hV₀ e').from U.unop)
      convert h using 2 <;> rfl)
  let M := N.val.obj (op (ofIso V₀ hV₀ e'))
  let i₁ : (Stacks.DenseSubsiteBaseChange.baseChangeSheaf hs).obj M ≅ N :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (@asIso _ _ _ _ (Stacks.TerminalBaseChange.baseChangeComparison.{u + 1}
        (ringPresheaf (W := W)) (isTerminalOfIso V₀ hV₀ e') N.val) hc)
  let E := Stacks.DenseSubsiteModules.moduleRestrictionEquivalence
    (EtaleAffineSchemesOver.topology W)
    ((Space.SpacesEtale.topology T.schemeSite S T.scheme_mem X).over W) (toSmallSlice W)
    sliceRingSheaf
  exact ⟨M, ⟨E.unitIso.app _ ≪≫ E.inverse.mapIso i₁.symm⟩⟩

/-- `M^a` on the slice at `W` has a global presentation. -/
theorem hasGlobalPresentation_associatedSheaf_isTerminalOfIso (M) :
    ((associatedSheaf (baseChangeIsSheaf V₀ hV₀ e')).obj M).HasGlobalPresentation := by
  obtain ⟨p⟩ := nonempty_presentation_associatedSheaf (baseChangeIsSheaf V₀ hV₀ e')
    (isTerminal_toSmallSlice_ofIso V₀ hV₀ e') M
  exact SheafOfModules.HasGlobalPresentation.of_presentation' p

end Quasicoherent

/-- **Every quasi-coherent module on the spaces-étale site of the affine `X` is some `M^a`**
(Stacks 03DX (2)). -/
theorem exists_iso_affineAssociated_of_isQuasicoherentOnSite
    (N : SheafOfModules.{u + 1} (spacesEtaleRing T X)) (hN : N.IsQuasicoherentOnSite) :
    ∃ M, Nonempty (N ≅ (affineAssociated T V₀ hV₀ e).obj M) := by
  let a := (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom
  have := isIso_unit_app_of_isQuasicoherentOnSite N
  obtain ⟨M, ⟨i⟩⟩ := nonempty_iso_associatedSheaf_pushforward_over V₀ hV₀
    (W := Space.SpacesEtale.final T.schemeSite S T.scheme_mem X) e (a.pullbackTopos.obj N)
    (generate_hasGlobalPresentation_pullback_mem N)
  let E := finalSliceModuleEquivalence T X
  exact ⟨M, ⟨asIso (a.pullbackPushforwardAdjunctionTopos.unit.app N) ≪≫
    E.unitIso.app _ ≪≫ E.inverse.mapIso (Iso.refl _ ≪≫ i)⟩⟩

/-- **`M^a` is quasi-coherent.** -/
theorem isQuasicoherentOnSite_affineAssociated_obj
    (M : ModuleCat.{u + 1} ((spacesEtaleRing T X).obj.obj (op (affinePoint T V₀ hV₀ e)))) :
    ((affineAssociated T V₀ hV₀ e).obj M).IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    refine ⟨ULift.{u + 1} PUnit.{1}, fun _ ↦ U, fun _ ↦ 𝟙 U, ?_, fun _ ↦ ?_⟩
    · refine GrothendieckTopology.superset_covering _ (fun Z g _ ↦ ?_)
        (GrothendieckTopology.top_mem _ U)
      rw [Sieve.mem_ofArrows_iff]
      exact ⟨ULift.up PUnit.unit, g, by simp⟩
    · exact Stacks.SheafOfModules.GlobalPresentationTransport.hasGlobalPresentation_overMap _
        ((Space.SpacesEtale.final_isTerminal T.schemeSite S T.scheme_mem X).from U) <|
        SheafOfModules.HasGlobalPresentation.of_iso
        ((finalSliceModuleEquivalence T X).counitIso.app _).symm
        (hasGlobalPresentation_associatedSheaf_isTerminalOfIso V₀ hV₀
          (W := Space.SpacesEtale.final T.schemeSite S T.scheme_mem X) e M)

/-! ### The morphism to the ringed point of global sections -/

/-- **The morphism `p : (X_{spaces,étale}, 𝒪_X) ⟶ (pt, Γ(X, 𝒪_X))`** to the ringed point of
global sections, at the final object `affinePoint`. -/
abbrev affinePointHom :
    RingedToposSiteHom
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X))
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (RingedSite.globalPoint
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X) (affinePoint T V₀ hV₀ e))) :=
  (RingedSite.toGlobalPoint (isTerminal_affinePoint T V₀ hV₀ e)).toRingedToposSiteHom

/-- **The pullback along `p` is `M ↦ M^a`** after evaluation at the point. -/
def affinePointHomPullbackIso :
    (affinePointHom T V₀ hV₀ e).pullbackTopos ≅
      RingedSite.globalPointEvaluation _ _ ⋙ affineAssociated T V₀ hV₀ e :=
  RingedSite.toGlobalPointPullbackIso (isTerminal_affinePoint T V₀ hV₀ e)
    (affineAssociatedAdjunction T V₀ hV₀ e) (affineAssociatedFullyFaithful T V₀ hV₀ e)

/-- **The pullback along `p` is exact.** -/
instance preservesFiniteLimits_affinePointHom_pullbackTopos :
    PreservesFiniteLimits (affinePointHom T V₀ hV₀ e).pullbackTopos := by
  have h₁ := preservesFiniteLimits_affineAssociated T V₀ hV₀ e
  have h₂ : PreservesFiniteLimits (RingedSite.globalPointEvaluation
      (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X) (affinePoint T V₀ hV₀ e)) := by
    rw [← RingedSite.globalPointEvaluationEquivalence_functor (isTerminal_affinePoint T V₀ hV₀ e)
      (affineAssociatedAdjunction T V₀ hV₀ e) (affineAssociatedFullyFaithful T V₀ hV₀ e)]
    infer_instance
  have h₃ := @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₂ h₁
  exact preservesFiniteLimits_of_natIso (affinePointHomPullbackIso T V₀ hV₀ e).symm

/-- The pullback along `p` is right exact, being a left adjoint. -/
instance preservesFiniteColimits_affinePointHom_pullbackTopos :
    PreservesFiniteColimits (affinePointHom T V₀ hV₀ e).pullbackTopos :=
  have :=
    (affinePointHom T V₀ hV₀ e).pullbackPushforwardAdjunctionTopos.leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- **The unit `M ⟶ p_*p^*M` is invertible.** -/
theorem isIso_affinePointHom_unit :
    IsIso (affinePointHom T V₀ hV₀ e).pullbackPushforwardAdjunctionTopos.unit :=
  RingedSite.isIso_toGlobalPoint_unit (isTerminal_affinePoint T V₀ hV₀ e)
    (affineAssociatedAdjunction T V₀ hV₀ e) (affineAssociatedFullyFaithful T V₀ hV₀ e)

/-- **The counit `p^*p_*𝓕 ⟶ 𝓕` is invertible at every quasi-coherent `𝓕`.** -/
theorem isIso_affinePointHom_counit_app (N : SheafOfModules.{u + 1} (spacesEtaleRing T X))
    (hN : N.IsQuasicoherentOnSite) :
    IsIso ((affinePointHom T V₀ hV₀ e).pullbackPushforwardAdjunctionTopos.counit.app N) := by
  obtain ⟨M, ⟨i⟩⟩ := exists_iso_affineAssociated_of_isQuasicoherentOnSite T V₀ hV₀ e N hN
  exact RingedSite.isIso_toGlobalPoint_counit_app_of_iso (isTerminal_affinePoint T V₀ hV₀ e)
    (affineAssociatedAdjunction T V₀ hV₀ e) (affineAssociatedFullyFaithful T V₀ hV₀ e) N M i

/-- **The pullback `p^*M` is quasi-coherent.** -/
theorem isQuasicoherentOnSite_affinePointHom_pullbackTopos_obj
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.globalPoint (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X)
        (affinePoint T V₀ hV₀ e)).O)) :
    ((affinePointHom T V₀ hV₀ e).pullbackTopos.obj M).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso ((affinePointHomPullbackIso T V₀ hV₀ e).app M).symm
    (isQuasicoherentOnSite_affineAssociated_obj T V₀ hV₀ e _)

end AlgebraicGeometry.BigFppfSpaceSite

end
