/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiCohomology

/-!
# Cohomology of the associated module on a represented space, over any base and any ring

`AlgebraicGeometry.Space.representedCohomologyAssociatedModuleIso` identifies, for an object `U`
of the big fppf site over `Spec A` with underlying scheme `T` and a quasi-coherent `𝒪_T`-module
`𝓕`, the étale cohomology `Hⁿ(yoneda.obj U, 𝓕ᵃ)` with the Zariski cohomology `Hⁿ(T, 𝓕)` as
`A`-modules, the scalars coming from the base `Spec A` of the site.  The comparison itself does
not involve the base: this file states it over an arbitrary base scheme `S`, for any ring `A`
with ring maps `ψ : A ⟶ Γ(yoneda.obj U, 𝒪)` and `ρ : A ⟶ Γ(T, 𝒪_T)` which agree on the open `⊤`
(the hypothesis `hψρ`).  This is what is needed to compute the cohomology of a module on the
algebraic space of `ℙⁿ_k`, `k` a field, on the big fppf site over `Spec ℤ` (Stacks 0DPB).

The proofs are those of `AlgebraicGeometry.Space.representedCohomologyAssociatedModuleIso` with
the base and the scalars made arbitrary.

## Main definitions

* `AlgebraicGeometry.Space.representedGlobalSectionsIsoAlong`: the global sections on the small
  étale site of `yoneda.obj U` are the Zariski global sections on `T`, `A`-linearly.
* `AlgebraicGeometry.Space.representedCohomologyAssociatedModuleIsoAlong`: **`Hⁿ(yoneda.obj U, 𝓕ᵃ)
  ≅ Hⁿ(T, 𝓕)` as `A`-modules**, in every degree.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The modules on the small étale site of a represented algebraic space form an abelian
category, over any base; stated with the universes pinned. -/
abbrev abelianRepresentedStructureRingSheafAlong :
    Abelian (SheafOfModules.{u} (representedStructureRingSheaf B S hS U)) :=
  SheafOfModules.instAbelian _

attribute [local instance] abelianRepresentedStructureRingSheafAlong

attribute [local instance] enoughInjectives_representedModules

/-- The image of the identity chart of `yoneda.obj U` in the small étale site of the scheme
underlying `U` is terminal. -/
def isTerminal_representedSmallEtaleEquivalence_functor_obj_idChartAlong :
    IsTerminal ((representedSmallEtaleEquivalence B S hS U).functor.obj
      (idChart B S hS U)) :=
  (isTerminal_idChart B S hS U).isTerminalObj _

/-- The open `⊤` of the scheme underlying `U`, as an object of its small étale site, maps to the
image of the identity chart: both are terminal. -/
def representedTopToIdChartAlong :
    _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⊤ ⟶
      (representedSmallEtaleEquivalence B S hS U).functor.obj
        (idChart B S hS U) :=
  (isTerminal_representedSmallEtaleEquivalence_functor_obj_idChartAlong B S hS U).from _

/-- The morphism of the small étale site of `T` from the open `⊤` to the image of the identity
chart is, on underlying schemes, the inclusion of `⊤`. -/
theorem representedTopToIdChartAlong_hom_left :
    (representedTopToIdChartAlong B S hS U).hom.left =
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⊤).obj.hom :=
  (Category.comp_id _).symm.trans (Over.w (representedTopToIdChartAlong B S hS U).hom)

variable (A : Type u) [CommRing A]
  (ψ : A →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)).O)))
  (ρ : A →+* ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf.obj.obj (op ⊤))

/-- The map back from the image of the identity chart to the open `⊤`: `⊤` is terminal in the
small étale site of `T`. -/
def representedIdChartToTopAlong :
    (representedSmallEtaleEquivalence B S hS U).functor.obj
        (idChart B S hS U) ⟶
      _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⊤ :=
  (_root_.AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property).from _

/-- Restricting along `f` and then `g` is the identity at a terminal object. -/
private theorem map_op_map_op_of_isTerminal {C : Type*} [Category C]
    (P : Cᵒᵖ ⥤ AddCommGrpCat) {X Y : C} (hX : IsTerminal X) (f : Y ⟶ X) (g : X ⟶ Y)
    (x : P.obj (op X)) : P.map g.op (P.map f.op x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hX.hom_ext (g ≫ f) (𝟙 _),
    op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

variable {B S hS U} in
/-- Restriction from the image of the identity chart to the open `⊤` and back is the identity. -/
theorem map_representedIdChartToTopAlong_map_representedTopToIdChartAlong
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U))
    (x : M.val.presheaf.obj (op ((representedSmallEtaleEquivalence B S hS U).functor.obj
      (idChart B S hS U)))) :
    M.val.presheaf.map (representedIdChartToTopAlong B S hS U).op
      (M.val.presheaf.map (representedTopToIdChartAlong B S hS U).op x) = x := by
  exact map_op_map_op_of_isTerminal _
    (isTerminal_representedSmallEtaleEquivalence_functor_obj_idChartAlong B S hS U) _ _ x

variable {B S hS U} in
/-- Restriction from the open `⊤` to the image of the identity chart and back is the identity. -/
theorem map_representedTopToIdChartAlong_map_representedIdChartToTopAlong
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U))
    (x : M.val.presheaf.obj (op (_root_.AlgebraicGeometry.SmallEtale.opensObj
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
      U.left.property ⊤))) :
    M.val.presheaf.map (representedTopToIdChartAlong B S hS U).op
      (M.val.presheaf.map (representedIdChartToTopAlong B S hS U).op x) = x := by
  exact map_op_map_op_of_isTerminal _
    (_root_.AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) _ _ x

/-- The `A`-linear map from the global sections of a module on the small étale site of
`yoneda.obj U` to the Zariski global sections of its restriction to `T`: evaluate at the
identity chart, then restrict to the open `⊤`. -/
def representedGlobalSectionsLinearMapAlong
    (hψρ : ∀ a : A, (representedSchemeStructureSheaf B S hS U).obj.map
      (representedTopToIdChartAlong B S hS U).op
      ((Stacks.Cohomology.SiteModules.globalSectionEval (representedStructureRingSheaf B S hS U)
        (op (idChart B S hS U))) (ψ a)) =
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op ⊤) (ρ a))
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    (ModuleCat.restrictScalars (ψ)).obj
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        (representedStructureRingSheaf B S hS U)).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj M)) →ₗ[A]
    (ModuleCat.uliftFunctor.{u + 1} A).obj
      ((zariskiSectionsOver ((BigFppfOver.toScheme B S hS).obj U)
        (ρ)).obj
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj M)) where
  toFun s := ULift.up (M.val.presheaf.map (representedTopToIdChartAlong B S hS U).op
    (s.eval (op (idChart B S hS U))))
  map_add' s t := ULift.ext _ _
    (map_add (M.val.presheaf.map (representedTopToIdChartAlong B S hS U).op).hom
      (s.eval (op (idChart B S hS U))) (t.eval (op (idChart B S hS U))))
  map_smul' a _ := ULift.ext _ _
    ((PresheafOfModules.map_smul _ _ _ _).trans
      (congrArg (· • _) (hψρ a)))

/-- The comparison of global sections is bijective: evaluation at the terminal identity chart is
bijective on compatible families, and restriction between the two terminal objects of the small
étale site of `T` is invertible. -/
theorem bijective_representedGlobalSectionsLinearMapAlong
    (hψρ : ∀ a : A, (representedSchemeStructureSheaf B S hS U).obj.map
      (representedTopToIdChartAlong B S hS U).op
      ((Stacks.Cohomology.SiteModules.globalSectionEval (representedStructureRingSheaf B S hS U)
        (op (idChart B S hS U))) (ψ a)) =
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op ⊤) (ρ a))
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    Function.Bijective (representedGlobalSectionsLinearMapAlong B S hS U A ψ ρ hψρ M) := by
  have hev := Stacks.Cohomology.SiteModules.bijective_globalSectionsEval
    (representedStructureRingSheaf B S hS U) (isTerminal_idChart B S hS U)
    ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj M)
  refine ⟨fun s t h => hev.1 (ULift.ext _ _ ?_), fun y => ?_⟩
  · have h' : M.val.presheaf.map (representedIdChartToTopAlong B S hS U).op
          (M.val.presheaf.map (representedTopToIdChartAlong B S hS U).op
            (s.eval (op (idChart B S hS U)))) =
        M.val.presheaf.map (representedIdChartToTopAlong B S hS U).op
          (M.val.presheaf.map (representedTopToIdChartAlong B S hS U).op
            (t.eval (op (idChart B S hS U)))) :=
      congrArg (fun z => M.val.presheaf.map (representedIdChartToTopAlong B S hS U).op
        (ULift.down z)) h
    exact (map_representedIdChartToTopAlong_map_representedTopToIdChartAlong M _).symm.trans
      (h'.trans (map_representedIdChartToTopAlong_map_representedTopToIdChartAlong M _))
  · obtain ⟨s, hs⟩ := hev.2 (ULift.up
      (M.val.presheaf.map (representedIdChartToTopAlong B S hS U).op (ULift.down y)))
    refine ⟨s, ULift.ext _ _ ?_⟩
    have hs' : s.eval (op (idChart B S hS U)) =
        M.val.presheaf.map (representedIdChartToTopAlong B S hS U).op (ULift.down y) :=
      congrArg ULift.down hs
    exact (congrArg (M.val.presheaf.map (representedTopToIdChartAlong B S hS U).op) hs').trans
      (map_representedTopToIdChartAlong_map_representedIdChartToTopAlong M (ULift.down y))

/-- **The global sections on the small étale site of `yoneda.obj U` are the Zariski global
sections on `T`**, naturally in the module on the small étale site of `T` and linearly over `A`. -/
def representedGlobalSectionsIsoAlong
    (hψρ : ∀ a : A, (representedSchemeStructureSheaf B S hS U).obj.map
      (representedTopToIdChartAlong B S hS U).op
      ((Stacks.Cohomology.SiteModules.globalSectionEval (representedStructureRingSheaf B S hS U)
        (op (idChart B S hS U))) (ψ a)) =
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op ⊤) (ρ a)) :
    (representedSmallEtaleModuleEquivalence B S hS U).functor ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (representedStructureRingSheaf B S hS U) ⋙
        ModuleCat.restrictScalars (ψ) ≅
      _root_.AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
        zariskiSectionsOver ((BigFppfOver.toScheme B S hS).obj U)
          (ρ) ⋙
        ModuleCat.uliftFunctor.{u + 1} A :=
  NatIso.ofComponents
    (fun M => (LinearEquiv.ofBijective _
      (bijective_representedGlobalSectionsLinearMapAlong B S hS U A ψ ρ hψρ M)).toModuleIso)
    (fun {_ _} φ => by
      ext s
      exact ULift.ext _ _ (PresheafOfModules.naturality_apply φ.val
        (representedTopToIdChartAlong B S hS U).op (s.eval (op (idChart B S hS U)))).symm)

/-- **The cohomology of the module associated with a quasi-coherent module, on the small étale
site of a represented algebraic space, is the Zariski cohomology of the module.**  Let `U` be an
object of the big fppf site over `Spec A`, with underlying scheme `T`, and let `𝓕` be a
quasi-coherent `𝒪_T`-module.  Then in every degree `n` the cohomology `Hⁿ(yoneda.obj U, 𝓕ᵃ)` of
the associated module on the small étale site of `yoneda.obj U` is, as an `A`-module, the Zariski
cohomology `Hⁿ(T, 𝓕)`, the latter with its universe raised to that of the former. -/
def representedCohomologyAssociatedModuleIsoAlong
    (hψρ : ∀ a : A, (representedSchemeStructureSheaf B S hS U).obj.map
      (representedTopToIdChartAlong B S hS U).op
      ((Stacks.Cohomology.SiteModules.globalSectionEval (representedStructureRingSheaf B S hS U)
        (op (idChart B S hS U))) (ψ a)) =
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op ⊤) (ρ a))
    (F : SheafOfModules.{u} ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf)
    (hF : SheafOfModules.IsQuasicoherent F) (n : ℕ) :
    (ModuleCat.restrictScalars (ψ)).obj
      (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        (representedStructureRingSheaf B S hS U)).rightDerived n).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj F))) ≅
      (ModuleCat.uliftFunctor.{u + 1} A).obj
        ((ModuleCat.restrictScalars.{u} (ρ)).obj
          (((SheafOfModules.evaluation
            ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf (op ⊤)).rightDerived
              n).obj F)) := by
  let _ : Abelian (SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :=
    _root_.AlgebraicGeometry.SmallEtale.abelian_sheafOfModules_structureSheaf
      (associatedBigEtaleSite B) _ U.left.property
  have : EnoughInjectives (SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :=
    _root_.AlgebraicGeometry.SmallEtale.enoughInjectives_sheafOfModules_structureSheaf
      (associatedBigEtaleSite B) _ U.left.property
  have : HasInjectiveResolutions
      (SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :=
    ⟨fun _ => inferInstance⟩
  let E := representedSmallEtaleModuleEquivalence B S hS U
  have : (ModuleCat.restrictScalars.{u + 1} ψ).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have : (ModuleCat.uliftFunctor.{u + 1} A).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  have : ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS U)) ⋙ (ModuleCat.restrictScalars.{u + 1}
          (ψ))).Additive := ⟨by intros; ext; rfl⟩
  have : (ModuleCat.restrictScalars.{u + 1} (ψ)).Additive :=
    ⟨by intros; ext; rfl⟩
  have hΓ : PreservesFiniteLimits
      (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (representedStructureRingSheaf B S hS U)) :=
    preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B S hS
      (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)
  have hR : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} (ψ)) :=
    StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits _
  have : PreservesFiniteLimits
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (representedStructureRingSheaf B S hS U)) ⋙
              (ModuleCat.restrictScalars.{u + 1} ψ)) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hΓ hR
  have : (_root_.AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).Additive := ⟨rfl⟩
  have : E.functor.Additive := ⟨rfl⟩
  have hA' : ∀ p, 0 < p → IsZero ((E.functor.rightDerived p).obj
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj F)) :=
    fun p hp => Functor.isZero_rightDerived_of_exact E.functor _ p hp
  have hGT : ∀ Y : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U),
      Injective Y → Stacks.RightDerivedComp.acyclic
          ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
              (representedStructureRingSheaf B S hS U)) ⋙
                  (ModuleCat.restrictScalars.{u + 1} (ψ)))
                          (E.functor.obj Y) := fun Y _ =>
    have := Injective.injective_of_adjoint E.symm.toAdjunction Y
    Stacks.RightDerivedComp.acyclic_of_injective _ _
  exact ((@Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _ _ _ _ _ _ _ _
      (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (representedStructureRingSheaf B S hS U)) (ModuleCat.restrictScalars.{u + 1}
              (ψ))
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (representedStructureRingSheaf B S hS U)) ⋙
              (ModuleCat.restrictScalars.{u + 1} (ψ))) _
                      ⟨by intros; ext; rfl⟩ _
      (@Functor.preservesHomologyOfExact _ _ _ _ _ _ (ModuleCat.restrictScalars.{u + 1}
          (ψ)) _ hR
        (StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits _))
      (Iso.refl _) n).app _) ≪≫
    (Stacks.RightDerivedComp.objIsoOfAcyclicImage E.functor
        ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
            (representedStructureRingSheaf B S hS U)) ⋙
                (ModuleCat.restrictScalars.{u + 1} (ψ))) hA' hGT n).symm ≪≫
    (rightDerivedIsoOfIso (representedGlobalSectionsIsoAlong B S hS U A ψ ρ hψρ) n).app _ ≪≫
    ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
                (zariskiSectionsOver ((BigFppfOver.toScheme B S hS).obj U)
                    (ρ))) (ModuleCat.uliftFunctor.{u + 1} A)
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property) ⋙
              (zariskiSectionsOver ((BigFppfOver.toScheme B S hS).obj U)
                  (ρ)) ⋙ (ModuleCat.uliftFunctor.{u + 1} A))
                      (Functor.associator _ _ _) n).app _).symm ≪≫
    (ModuleCat.uliftFunctor.{u + 1} A).mapIso
        (_root_.AlgebraicGeometry.SmallEtale.rightDerivedRestrictModuleCompAssociatedModuleIso
      (associatedBigEtaleSite B) _ U.left.property (ρ) F hF n)

end AlgebraicGeometry.Space

end
