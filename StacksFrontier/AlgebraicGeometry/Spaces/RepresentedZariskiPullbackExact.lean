module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePullbackExact
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackKFlat
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparisonPullback

/-!
# `ε^*` is exact for a representable algebraic space

Let `X = yoneda.obj U` be the algebraic space represented by an object `U` of the big fppf site
over `S`, with underlying scheme `X_0`, and let
`ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X_0})` be
`representedZariskiRingedToposHomRepresentedZariskiRingedToposHom`. The pullback of sheaves of
modules `ε^* : Mod(𝒪_{X_0}) ⥤ Mod(𝒪_X)` is exact: it is the pullback along
`ε_0 = id_{small, étale, Zar}` of Stacks 070R, exact by Stacks 08H8, followed by the pullback
along an equivalence of ringed topoi.

All names below are in the namespace `AlgebraicGeometry.Space`.

## Main results

* `representedSmallEtaleRingedToposHom_pullbackModules_exact_representedZariskiPullbackExact`:
  the pullback along the equivalence of small étale sites is exact.
* `representedZariskiModulePullback_exact_representedZariskiPullbackExact`: `ε^*` is exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TopologicalSpace
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The direct image of sheaves of sets along the equivalence of small étale sites is an
equivalence. -/
instance
    isEquivalence_representedSmallEtaleRingedToposHom_pushforward_representedZariskiPullbackExact :
    (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom
      B S hS U).toToposHom.pushforward.IsEquivalence :=
  inferInstanceAs (Equivalence.sheafCongr (representedSchemeSmallEtaleTopology B S hS U)
    (SmallEtale.topology B S hS (yoneda.obj U))
    (representedSmallEtaleEquivalence B S hS U).symm (Type u)).inverse.IsEquivalence

/-- The structure map of the identification of structure sheaves is invertible. -/
instance isIso_representedCommRingStructureMap_representedZariskiPullbackExact :
    IsIso (representedCommRingStructureMapRepresentedZariskiRingedToposHom B S hS U) :=
  ⟨⟨{ hom := 𝟙 _ }, rfl, rfl⟩⟩

/-- The structure map of the equivalence of small étale sites is invertible. -/
instance isIso_representedSmallEtaleRingedToposHom_fSharp_representedZariskiPullbackExact :
    IsIso (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom
      B S hS U).fSharp := by
  change IsIso (representedCommRingStructureMapRepresentedZariskiRingedToposHom B S hS U ≫ _)
  exact IsIso.comp_isIso' inferInstance (Iso.isIso_inv _)

/-- **The pullback of sheaves of modules along the equivalence of small étale sites is exact.**
It is the inverse image of sheaves of modules followed by extension of scalars along the
inverse-image form of the structure map, which is an isomorphism. -/
theorem representedSmallEtaleRingedToposHom_pullbackModules_exact_representedZariskiPullbackExact :
    exactFunctor _ _
      ((representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom
        B S hS U).toModulesHom.pullbackModules) := by
  have h := RingedToposHom.pullbackModules_eq_pullbackModules_toRingedToposModulesHom
    (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom B S hS U)
  rw [h]
  have hiso := RingedToposHom.isIso_fSharpInverseImage
    (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom B S hS U)
  exact Stacks.Sheaves.RingedToposModules.exactFunctor_pullbackModules_of_preservesFiniteLimits
    (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom B S hS U)
    (Stacks.Sheaves.RingedToposModules.preservesFiniteLimits_extendScalars_of_iso _ _ _ _
      ((sheafCompose (SmallEtale.topology B S hS (yoneda.obj U))
          (forget₂ CommRingCat.{u} RingCat.{u})).mapIso
        (asIso (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom
          B S hS U).fSharpInverseImage)) rfl)

/-- `ε^* : Mod(𝒪_{X_0}) ⥤ Mod(𝒪_X)`, the pullback of sheaves of modules along
`AlgebraicGeometry.Space.representedZariskiRingedToposHomRepresentedZariskiRingedToposHom`. -/
abbrev representedZariskiModulePullbackRepresentedZariskiPullbackExact :=
  Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
    (X := smallEtaleRingedTopos B S hS (representedSpace U))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U).toModulesHom

/-- `ε_* : Mod(𝒪_X) ⥤ Mod(𝒪_{X_0})`, the direct image of sheaves of modules along
`AlgebraicGeometry.Space.representedZariskiRingedToposHomRepresentedZariskiRingedToposHom`. -/
abbrev representedZariskiModulePushforwardRepresentedZariskiPullbackExact :=
  RingedToposHom.pushforwardModules (X := smallEtaleRingedTopos B S hS (representedSpace U))
    (Y := (representedSchemeRepresentedZariskiRingedToposHom B S hS U).zariskiRingedTopos)
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom B S hS U)

/-- **`ε^*` is exact.**  It is the pullback along `ε_0 = id_{small, étale, Zar}`, exact by
Stacks 08H8, followed by the pullback along the equivalence of small étale sites. -/
theorem representedZariskiModulePullback_exact_representedZariskiPullbackExact :
    exactFunctor _ _
      (representedZariskiModulePullbackRepresentedZariskiPullbackExact B S hS U) := by
  have h₀ := _root_.AlgebraicGeometry.SmallEtale.exactFunctor_pullbackModules_toZariski
    (associatedBigEtaleSite B) (representedSchemeRepresentedZariskiRingedToposHom B S hS U)
    U.left.property
  have h₁ :=
    representedSmallEtaleRingedToposHom_pullbackModules_exact_representedZariskiPullbackExact
      B S hS U
  have h := RingedToposHom.pullbackModules_eq_pullbackModules_toRingedToposModulesHom
    (_root_.AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom (associatedBigEtaleSite B)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U) U.left.property)
  rw [_root_.AlgebraicGeometry.SmallEtale.toZariskiModulePullback, ← h] at h₀
  rw [exactFunctor_iff] at h₀ h₁ ⊢
  obtain ⟨_, _⟩ := h₀
  obtain ⟨_, _⟩ := h₁
  let e := RingedToposHom.pullbackModulesCompIso
    (representedSmallEtaleRingedToposHomRepresentedZariskiRingedToposHom B S hS U)
    (_root_.AlgebraicGeometry.SmallEtale.toZariskiAbstractRingedToposHom (associatedBigEtaleSite B)
      (representedSchemeRepresentedZariskiRingedToposHom B S hS U) U.left.property)
  exact ⟨preservesFiniteLimits_of_natIso e.symm, preservesFiniteColimits_of_natIso e.symm⟩

/-- The sections over an open `W` of the scheme of the direct image of a sheaf of sets along `ε`
are the sections over the étale chart `W ⟶ X`, on the nose. -/
def representedZariskiSectionsComparisonRepresentedZariskiPullbackExact
    (W : (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Opens) :
    (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
          B S hS U).toToposHom.pushforward ⋙
        Sheaf.sectionsFunctor
          (Opens.grothendieckTopology ↥(representedSchemeRepresentedZariskiRingedToposHom B S hS U))
          (Opposite.op W) ⟶
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS (yoneda.obj U))
        (Opposite.op ((representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom
          B S hS U).obj W)) where
  app _ := 𝟙 _
  naturality _ _ _ := rfl

/-- The direct image along `ε` followed by sections over an open preserves finite products. -/
instance preservesFiniteProducts_representedZariski_pushforward_comp_sections_representedZariskiPullbackExact
    (W : (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Opens) :
    PreservesFiniteProducts
      ((representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
          B S hS U).toToposHom.pushforward ⋙
        Sheaf.sectionsFunctor
          (Opens.grothendieckTopology ↥(representedSchemeRepresentedZariskiRingedToposHom B S hS U))
          (Opposite.op W)) :=
  haveI := (representedZariskiRingedToposHomRepresentedZariskiRingedToposHom
    B S hS U).toToposHom.adj.rightAdjoint_preservesLimits
  haveI h : PreservesFiniteProducts (Sheaf.sectionsFunctor.{u}
      (Opens.grothendieckTopology ↥(representedSchemeRepresentedZariskiRingedToposHom B S hS U))
      (Opposite.op W)) := by
    delta Sheaf.sectionsFunctor
    infer_instance
  @comp_preservesFiniteProducts _ _ _ _ _ _ _ _ inferInstance h

/-- **The sections over an open `W ⊆ X_0` of `ε_* M` are the sections of `M` over the étale chart
`W ⟶ X`**, as abelian groups, naturally in `M`. -/
def representedZariskiPushforwardEvaluationIsoRepresentedZariskiPullbackExact
    (W : (representedSchemeRepresentedZariskiRingedToposHom B S hS U).Opens) :
    representedZariskiModulePushforwardRepresentedZariskiPullbackExact B S hS U ⋙
        SheafOfModules.evaluation _ (Opposite.op W) ⋙ forget₂ _ AddCommGrpCat.{u} ≅
      SheafOfModules.evaluation _
          (Opposite.op ((representedSchemeOpensToSmallEtaleRepresentedZariskiRingedToposHom
            B S hS U).obj W)) ⋙
        forget₂ _ AddCommGrpCat.{u} :=
  NatIso.ofComponents (fun M => AddEquiv.toAddCommGrpIso
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun x y => Sheaf.app_moduleAddObj _ M
        (representedZariskiSectionsComparisonRepresentedZariskiPullbackExact B S hS U W) x y })
    (fun _ => rfl)

end AlgebraicGeometry.Space
