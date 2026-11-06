module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import
    StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import
    StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedSmallEtaleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsTerminalObject
public import StacksFrontier.Homology.CompositeCollapse
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# Cohomology of the module associated with a quasi-coherent module, on a represented space

Let `U` be an object of the big fppf site over `S`, with underlying scheme `T`, and let `𝓕` be a
quasi-coherent `𝒪_T`-module.  Through Descent, Proposition 03DX, `𝓕` is a quasi-coherent module
`𝓕ᵃ` on the small étale site of the algebraic space `yoneda.obj U`
(`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence`).  This file shows that the
cohomology of `𝓕ᵃ` on the small étale site of `yoneda.obj U` is the Zariski cohomology of `𝓕` on
`T`, in every degree and linearly over any ring mapping compatibly to the global functions.

## The route

Everything is done with derived functors of functors to categories of modules, so that every
comparison is an isomorphism of modules and linearity costs nothing.

1. On the small étale site of the scheme `T`, the global sections are the sections over the
   object `T` itself, that is the composite of the restriction `ε_*` to the small Zariski site
   (`AlgebraicGeometry.SmallEtale.restrictModule`) with the sections over `⊤`.  The functor
   `ε_*` carries injective modules to injective ones, its left adjoint `ε^*` being exact
   (Stacks 08H8), and its higher derived functors vanish on a module quasi-coherent on the site
   (`AlgebraicGeometry.SmallEtale.isZero_rightDerived_restrictModule`), so the derived functors of
   the composite are those of the sections over `⊤` at `ε_*𝓜`
   (`Stacks.RightDerivedComp.objIsoOfAcyclicImage`).  At `𝓜 = 𝓕ᵃ` the restriction is `𝓕`, by
   Stacks 03DX.
2. The small étale site of `yoneda.obj U` is equivalent to that of `T`, the module categories
   being identified by `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`, and both
   global-sections functors are evaluation at a terminal object
   (`AlgebraicGeometry.Space.representedGlobalSectionsIso`); the scalars of `A` agree on the two
   terminal objects by `AlgebraicGeometry.Space.map_representedTopToIdChart_baseRingHom`.

## Main results

* `AlgebraicGeometry.SmallEtale.rightDerivedRestrictModuleCompAssociatedModuleIso`: on the small
  étale site of a scheme `T`, the derived functors of `𝓜 ↦ Γ(T, ε_*𝓜)` at `𝓕ᵃ` are the Zariski
  cohomology of `𝓕`.
* `AlgebraicGeometry.Space.representedGlobalSectionsIso`: the global sections on the small étale
  site of `yoneda.obj U` are the Zariski global sections on `T`, naturally and `A`-linearly.
* `AlgebraicGeometry.Space.representedCohomologyAssociatedModuleIso`: **`Hⁿ(yoneda.obj U, 𝓕ᵃ) ≅
  Hⁿ(T, 𝓕)` as `A`-modules**, in every degree.
* `AlgebraicGeometry.Space.finrank_representedCohomology_eq_finrank_cohomologyOverField`: over a
  field `k`, the two have the same dimension, the Zariski side being
  `AlgebraicGeometry.cohomologyOverField`.

## Implementation notes

Several instances are restated with their universes pinned, or passed explicitly, because
instance search does not unify the universe of the module categories of these sites with the one
the generic `SheafOfModules.instAbelian` produces, and does not see the restriction-of-scalars
instances at the ring of global sections of the small étale site.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe u

/-! ### The Zariski global sections over a ring -/

namespace AlgebraicGeometry

variable (T : Scheme.{u}) {R : Type u} [Ring R] (ρ : R →+* T.ringCatSheaf.obj.obj (op ⊤))

/-- The Zariski global sections of an `𝒪_T`-module, read as an `R`-module along `ρ`. -/
abbrev zariskiSectionsOver : SheafOfModules.{u} T.ringCatSheaf ⥤ ModuleCat.{u} R :=
  SheafOfModules.evaluation T.ringCatSheaf (op ⊤) ⋙ ModuleCat.restrictScalars.{u} ρ

/-- The Zariski global sections functor `zariskiSectionsOver T ρ` is additive. -/
instance additive_zariskiSectionsOver : (zariskiSectionsOver T ρ).Additive where
  map_add := rfl

/-- The Zariski global sections functor `zariskiSectionsOver T ρ` preserves finite limits. -/
instance preservesFiniteLimits_zariskiSectionsOver :
    PreservesFiniteLimits (zariskiSectionsOver T ρ) := by
  have h₁ : PreservesFiniteLimits (SheafOfModules.evaluation T.ringCatSheaf (op ⊤)) :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have h₂ : PreservesFiniteLimits (ModuleCat.restrictScalars.{u} ρ) := inferInstance
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ h₁ h₂

end AlgebraicGeometry

/-! ### The small étale site of a scheme -/

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)

/-- The modules on the small étale site of a scheme form an abelian category; stated with the
universes pinned, which instance search does not find unaided. -/
instance abelian_sheafOfModules_structureSheaf :
    Abelian (SheafOfModules.{u} (structureSheaf B T hT)) :=
  SheafOfModules.instAbelian _

/-- The modules on the small étale site of a scheme have enough injectives, the category being
Grothendieck abelian; stated with the universes pinned, which instance search does not find. -/
instance enoughInjectives_sheafOfModules_structureSheaf :
    EnoughInjectives (SheafOfModules.{u} (structureSheaf B T hT)) :=
  @IsGrothendieckAbelian.enoughInjectives _ _ _
    (smallEtaleRingedSite_isGrothendieckAbelian B T hT _)

/-- The restriction `ε_*` from the small étale site of a scheme to its small Zariski site carries
injective modules to injective modules: its left adjoint, the associated-module functor `ε^*`, is
exact (Stacks 08H8), hence preserves monomorphisms. -/
theorem injective_restrictModuleOfSheaf_obj (Z : SheafOfModules.{u} (structureSheaf B T hT))
    [Injective Z] : Injective ((restrictModuleOfSheaf B T hT).obj Z) :=
  Injective.injective_of_adjoint (associatedModuleOfSheafAdjunction B T hT) Z

variable {R : Type u} [Ring R] (ρ : R →+* T.ringCatSheaf.obj.obj (op ⊤))

/-- **The derived functors of the étale global sections, computed on the Zariski site.**  For a
module `𝓜` on the small étale site of `T` which is quasi-coherent on the site, the derived
functors of `ε_*` followed by the Zariski global sections are those of the Zariski global
sections at `ε_*𝓜`. -/
def rightDerivedRestrictModuleCompIso (M : SheafOfModules.{u} (structureSheaf B T hT))
    (hM : M.IsQuasicoherentOnSite) (n : ℕ) :
    ((restrictModuleOfSheaf B T hT ⋙ zariskiSectionsOver T ρ).rightDerived n).obj M ≅
      ((zariskiSectionsOver T ρ).rightDerived n).obj ((restrictModuleOfSheaf B T hT).obj M) :=
  have : PreservesFiniteLimits (restrictModuleOfSheaf B T hT) :=
    have : PreservesLimitsOfSize.{0, 0} (restrictModuleOfSheaf B T hT) :=
      (associatedModuleOfSheafAdjunction B T hT).rightAdjoint_preservesLimits
    inferInstance
  @Stacks.RightDerivedComp.objIsoOfAcyclicImage _ _ _ _ _ _ _ _ _ _ _
    (restrictModuleOfSheaf B T hT) ⟨rfl⟩ _ (zariskiSectionsOver T ρ) ⟨rfl⟩ _ _
    (fun p hp => isZero_rightDerived_restrictModule B T hT M hM p hp)
    (fun Z _ =>
      have := injective_restrictModuleOfSheaf_obj B T hT Z
      Stacks.RightDerivedComp.acyclic_of_injective _ _) n

/-- **The étale cohomology of `𝓕ᵃ` on the small étale site of a scheme is the Zariski cohomology
of `𝓕`**, for a quasi-coherent `𝒪_T`-module `𝓕` and over a ring `R` mapping to `Γ(T, 𝒪_T)`:
the derived functors of the étale global sections `𝓜 ↦ Γ(T, ε_*𝓜)` at `𝓕ᵃ` are the Zariski
cohomology modules of `𝓕`, read over `R`. -/
def rightDerivedRestrictModuleCompAssociatedModuleIso (F : SheafOfModules.{u} T.ringCatSheaf)
    (hF : SheafOfModules.IsQuasicoherent F) (n : ℕ) :
    ((restrictModuleOfSheaf B T hT ⋙ zariskiSectionsOver T ρ).rightDerived n).obj
        ((associatedModuleOfSheaf B T hT).obj F) ≅
      (ModuleCat.restrictScalars.{u} ρ).obj
        (((SheafOfModules.evaluation T.ringCatSheaf (op ⊤)).rightDerived n).obj F) :=
  have : IsIso ((associatedModuleOfSheafAdjunction B T hT).unit.app F) :=
    unitIsoOnQuasicoherent B T hT ⟨F, hF⟩
  have : (ModuleCat.restrictScalars.{u} ρ).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  rightDerivedRestrictModuleCompIso B T hT ρ _
      (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B T hT F hF) n ≪≫
    ((zariskiSectionsOver T ρ).rightDerived n).mapIso
      (asIso ((associatedModuleOfSheafAdjunction B T hT).unit.app F)).symm ≪≫
    ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (SheafOfModules.evaluation T.ringCatSheaf (op ⊤)) (ModuleCat.restrictScalars.{u} ρ)
      (zariskiSectionsOver T ρ) (Iso.refl _) n).app F).symm

end AlgebraicGeometry.SmallEtale

/-! ### The small étale site of a represented algebraic space -/

namespace AlgebraicGeometry.Space

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (U : BigFppfOver B (Spec (.of A)) hA)

/-- The modules on the small étale site of a represented algebraic space form an abelian
category; stated with the universes pinned, which instance search does not find unaided. -/
instance abelian_sheafOfModules_representedStructureRingSheaf :
    Abelian (SheafOfModules.{u} (representedStructureRingSheaf B (Spec (.of A)) hA U)) :=
  SheafOfModules.instAbelian _

/-- The modules on the small étale site of a represented algebraic space have enough
injectives. -/
instance enoughInjectives_sheafOfModules_representedStructureRingSheaf :
    EnoughInjectives (SheafOfModules.{u} (representedStructureRingSheaf B (Spec (.of A)) hA U)) :=
  enoughInjectives_modules B (Spec (.of A)) hA (yoneda.obj U)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of A)) hA U)

/-- The structure morphism `T ⟶ Spec A` of the scheme `T` underlying an object `U` of the big
fppf site over `Spec A`. -/
abbrev representedStructureMorphism :
    (BigFppfOver.toScheme B (Spec (.of A)) hA).obj U ⟶ Spec (.of A) :=
  B.inclusion.map U.hom

/-- The ring map `A ⟶ Γ(T, 𝒪_T)` along which the Zariski cohomology of the scheme underlying `U`
is read as `A`-modules: the one of `AlgebraicGeometry.cohomologyOverField`. -/
abbrev representedZariskiRingHom :
    A →+* ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).ringCatSheaf.obj.obj (op ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫
    (representedStructureMorphism A B hA U).appLE ⊤ ⊤ (by simp)).hom

/-- The image of the identity chart of `yoneda.obj U` in the small étale site of the scheme
underlying `U` is terminal. -/
def isTerminal_representedSmallEtaleEquivalence_functor_obj_idChart :
    IsTerminal ((representedSmallEtaleEquivalence B (Spec (.of A)) hA U).functor.obj
      (idChart B (Spec (.of A)) hA U)) :=
  (isTerminal_idChart B (Spec (.of A)) hA U).isTerminalObj _

/-- The open `⊤` of the scheme underlying `U`, as an object of its small étale site, maps to the
image of the identity chart: both are terminal. -/
def representedTopToIdChart :
    _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property ⊤ ⟶
      (representedSmallEtaleEquivalence B (Spec (.of A)) hA U).functor.obj
        (idChart B (Spec (.of A)) hA U) :=
  (isTerminal_representedSmallEtaleEquivalence_functor_obj_idChart A B hA U).from _

/-- The morphism of the small étale site of `T` from the open `⊤` to the image of the identity
chart is, on underlying schemes, the inclusion of `⊤`. -/
theorem representedTopToIdChart_hom_left :
    (representedTopToIdChart A B hA U).hom.left =
      (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property ⊤).obj.hom :=
  (Category.comp_id _).symm.trans (Over.w (representedTopToIdChart A B hA U).hom)

/-- **The two readings of a scalar of `A` agree on the open `⊤`.**  An element `a ∈ A` acts on
the sections over the identity chart of `yoneda.obj U` through the base ring map of the algebraic
space, and on the sections over `⊤` of a module on the Zariski site of `T` through the structure
morphism `T ⟶ Spec A`; the restriction along the inclusion of `⊤` carries the first to the
second. -/
theorem map_representedTopToIdChart_baseRingHom (a : A) :
    (representedSchemeStructureSheaf B (Spec (.of A)) hA U).obj.map
        (representedTopToIdChart A B hA U).op
        ((Stacks.Cohomology.SiteModules.globalSectionEval
          (representedStructureRingSheaf B (Spec (.of A)) hA U) (op (idChart B (Spec
              (.of A)) hA U)))
          (baseRingHom A B hA (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of A)) hA U) a)) =
      (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property).hom.app (op ⊤)
        (representedZariskiRingHom A B hA U a) := by
  have key : ∀ x, (representedSchemeStructureSheaf B (Spec (.of A)) hA U).obj.map
      (representedTopToIdChart A B hA U).op x =
        (Scheme.Γ.map ((associatedBigEtaleSite B).inclusion.map
          (representedTopToIdChart A B hA U).hom.left).op).hom x := fun _ => rfl
  refine (key _).trans ?_
  rw [representedTopToIdChart_hom_left]
  have hcomp : Scheme.Γ.map (representedStructureMorphism A B hA U).op ≫
      Scheme.Γ.map ((⊤ : ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).Opens).ι).op =
      (representedStructureMorphism A B hA U).appLE ⊤ ⊤ (by simp) ≫
        (Scheme.Opens.topIso (⊤ : ((BigFppfOver.toScheme B (Spec
            (.of A)) hA).obj U).Opens)).inv := by
    simp only [Scheme.Γ_map_op, Scheme.Hom.appLE, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv,
      Scheme.Hom.appTop]
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine congrArg (_ ≫ ·) ?_
    refine Eq.trans ?_ (((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).presheaf.map_comp _ _)
    exact congrArg ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).presheaf.map
      (Subsingleton.elim _ _)
  show ((Scheme.ΓSpecIso (.of A)).inv ≫ Scheme.Γ.map (representedStructureMorphism A B hA U).op ≫
      Scheme.Γ.map ((⊤ : ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).Opens).ι).op).hom a =
    ((Scheme.ΓSpecIso (.of A)).inv ≫
      (representedStructureMorphism A B hA U).appLE ⊤ ⊤ (by simp) ≫
        (Scheme.Opens.topIso (⊤ : ((BigFppfOver.toScheme B (Spec
            (.of A)) hA).obj U).Opens)).inv).hom a
  exact congrArg (fun f => ((Scheme.ΓSpecIso (.of A)).inv ≫ f).hom a) hcomp

/-- The map back from the image of the identity chart to the open `⊤`: `⊤` is terminal in the
small étale site of `T`. -/
def representedIdChartToTop :
    (representedSmallEtaleEquivalence B (Spec (.of A)) hA U).functor.obj
        (idChart B (Spec (.of A)) hA U) ⟶
      _root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property ⊤ :=
  (_root_.AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property).from _

/-- A presheaf of abelian groups: restricting along `g` and then along `f` is the identity when
`f ≫ g = 𝟙`. -/
private theorem map_op_map_op_of_comp_eq_id {C : Type*} [Category* C] (P : Cᵒᵖ ⥤ Ab) {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X) (x : P.obj (op X)) :
    P.map f.op (P.map g.op x) = x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, h, op_id,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

variable {A B hA U} in
/-- Restriction from the image of the identity chart to the open `⊤` and back is the identity. -/
theorem map_representedIdChartToTop_map_representedTopToIdChart
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B (Spec (.of A)) hA U))
    (x : M.val.presheaf.obj (op ((representedSmallEtaleEquivalence B (Spec
        (.of A)) hA U).functor.obj
      (idChart B (Spec (.of A)) hA U)))) :
    M.val.presheaf.map (representedIdChartToTop A B hA U).op
      (M.val.presheaf.map (representedTopToIdChart A B hA U).op x) = x := by
  exact map_op_map_op_of_comp_eq_id _ _ _
    ((isTerminal_representedSmallEtaleEquivalence_functor_obj_idChart A B hA U).hom_ext _ _) x

variable {A B hA U} in
/-- Restriction from the open `⊤` to the image of the identity chart and back is the identity. -/
theorem map_representedTopToIdChart_map_representedIdChartToTop
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B (Spec (.of A)) hA U))
    (x : M.val.presheaf.obj (op (_root_.AlgebraicGeometry.SmallEtale.opensObj
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)
      U.left.property ⊤))) :
    M.val.presheaf.map (representedTopToIdChart A B hA U).op
      (M.val.presheaf.map (representedIdChartToTop A B hA U).op x) = x := by
  exact map_op_map_op_of_comp_eq_id _ _ _
    ((_root_.AlgebraicGeometry.SmallEtale.isTerminalOpensObjTop (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property).hom_ext _ _) x

/-- The `A`-linear map from the global sections of a module on the small étale site of
`yoneda.obj U` to the Zariski global sections of its restriction to `T`: evaluate at the
identity chart, then restrict to the open `⊤`. -/
def representedGlobalSectionsLinearMap
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B (Spec (.of A)) hA U)) :
    (ModuleCat.restrictScalars (baseRingHom A B hA (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of A)) hA U))).obj
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        (representedStructureRingSheaf B (Spec (.of A)) hA U)).obj
        ((representedSmallEtaleModuleEquivalence B (Spec (.of A)) hA U).functor.obj M)) →ₗ[A]
    (ModuleCat.uliftFunctor.{u + 1} A).obj
      ((zariskiSectionsOver ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)
        (representedZariskiRingHom A B hA U)).obj
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property).obj M)) where
  toFun s := ULift.up (M.val.presheaf.map (representedTopToIdChart A B hA U).op
    (s.eval (op (idChart B (Spec (.of A)) hA U))))
  map_add' s t := ULift.ext
    (map_add (M.val.presheaf.map (representedTopToIdChart A B hA U).op).hom
      (s.eval (op (idChart B (Spec (.of A)) hA U))) (t.eval (op (idChart B (Spec (.of A)) hA U))))
  map_smul' a _ := ULift.ext
    ((PresheafOfModules.map_smul _ _ _ _).trans
      (congrArg (· • _) (map_representedTopToIdChart_baseRingHom A B hA U a)))

/-- The comparison of global sections is bijective: evaluation at the terminal identity chart is
bijective on compatible families, and restriction between the two terminal objects of the small
étale site of `T` is invertible. -/
theorem bijective_representedGlobalSectionsLinearMap
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B (Spec (.of A)) hA U)) :
    Function.Bijective (representedGlobalSectionsLinearMap A B hA U M) := by
  have hev := Stacks.Cohomology.SiteModules.bijective_globalSectionsEval
    (representedStructureRingSheaf B (Spec (.of A)) hA U) (isTerminal_idChart B (Spec (.of A)) hA U)
    ((representedSmallEtaleModuleEquivalence B (Spec (.of A)) hA U).functor.obj M)
  refine ⟨fun s t h => hev.1 (ULift.ext ?_), fun y => ?_⟩
  · have h' : M.val.presheaf.map (representedIdChartToTop A B hA U).op
          (M.val.presheaf.map (representedTopToIdChart A B hA U).op
            (s.eval (op (idChart B (Spec (.of A)) hA U)))) =
        M.val.presheaf.map (representedIdChartToTop A B hA U).op
          (M.val.presheaf.map (representedTopToIdChart A B hA U).op
            (t.eval (op (idChart B (Spec (.of A)) hA U)))) :=
      congrArg (fun z => M.val.presheaf.map (representedIdChartToTop A B hA U).op (ULift.down z)) h
    exact (map_representedIdChartToTop_map_representedTopToIdChart M _).symm.trans
      (h'.trans (map_representedIdChartToTop_map_representedTopToIdChart M _))
  · obtain ⟨s, hs⟩ := hev.2 (ULift.up (M.val.presheaf.map (representedIdChartToTop A B hA U).op
      (ULift.down y)))
    refine ⟨s, ULift.ext ?_⟩
    have hs' : s.eval (op (idChart B (Spec (.of A)) hA U)) =
        M.val.presheaf.map (representedIdChartToTop A B hA U).op (ULift.down y) :=
      congrArg ULift.down hs
    exact (congrArg (M.val.presheaf.map (representedTopToIdChart A B hA U).op) hs').trans
      (map_representedTopToIdChart_map_representedIdChartToTop M (ULift.down y))

/-- **The global sections on the small étale site of `yoneda.obj U` are the Zariski global
sections on `T`**, naturally in the module on the small étale site of `T` and linearly over `A`. -/
def representedGlobalSectionsIso :
    (representedSmallEtaleModuleEquivalence B (Spec (.of A)) hA U).functor ⋙
        Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (representedStructureRingSheaf B (Spec (.of A)) hA U) ⋙
        ModuleCat.restrictScalars (baseRingHom A B hA (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of A)) hA U)) ≅
      _root_.AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property ⋙
        zariskiSectionsOver ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)
          (representedZariskiRingHom A B hA U) ⋙
        ModuleCat.uliftFunctor.{u + 1} A :=
  NatIso.ofComponents
    (fun M => (LinearEquiv.ofBijective _
      (bijective_representedGlobalSectionsLinearMap A B hA U M)).toModuleIso)
    (fun {_ _} φ => by
      ext s
      exact ULift.ext (PresheafOfModules.naturality_apply φ.val
        (representedTopToIdChart A B hA U).op (s.eval (op (idChart B (Spec (.of A)) hA U)))).symm)

/-- Isomorphic additive functors have isomorphic right derived functors. -/
def rightDerivedIsoOfIso {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [HasInjectiveResolutions C] [Abelian D] {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- **The cohomology of the module associated with a quasi-coherent module, on the small étale
site of a represented algebraic space, is the Zariski cohomology of the module.**  Let `U` be an
object of the big fppf site over `Spec A`, with underlying scheme `T`, and let `𝓕` be a
quasi-coherent `𝒪_T`-module.  Then in every degree `n` the cohomology `Hⁿ(yoneda.obj U, 𝓕ᵃ)` of
the associated module on the small étale site of `yoneda.obj U` is, as an `A`-module, the Zariski
cohomology `Hⁿ(T, 𝓕)`, the latter with its universe raised to that of the former. -/
def representedCohomologyAssociatedModuleIso
    (F : SheafOfModules.{u} ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).ringCatSheaf)
    (hF : SheafOfModules.IsQuasicoherent F) (n : ℕ) :
    (ModuleCat.restrictScalars (baseRingHom A B hA (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of A)) hA U))).obj
      (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        (representedStructureRingSheaf B (Spec (.of A)) hA U)).rightDerived n).obj
        ((representedSmallEtaleModuleEquivalence B (Spec (.of A)) hA U).functor.obj
          ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property).obj F))) ≅
      (ModuleCat.uliftFunctor.{u + 1} A).obj
        ((ModuleCat.restrictScalars.{u} (representedZariskiRingHom A B hA U)).obj
          (((SheafOfModules.evaluation
            ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U).ringCatSheaf (op ⊤)).rightDerived
              n).obj F)) := by
  let _ : Abelian (SheafOfModules.{u} (representedSchemeStructureSheaf B (Spec (.of A)) hA U)) :=
    _root_.AlgebraicGeometry.SmallEtale.abelian_sheafOfModules_structureSheaf
      (associatedBigEtaleSite B) _ U.left.property
  have : EnoughInjectives (SheafOfModules.{u} (representedSchemeStructureSheaf B (Spec
      (.of A)) hA U)) :=
    _root_.AlgebraicGeometry.SmallEtale.enoughInjectives_sheafOfModules_structureSheaf
      (associatedBigEtaleSite B) _ U.left.property
  have : HasInjectiveResolutions
      (SheafOfModules.{u} (representedSchemeStructureSheaf B (Spec (.of A)) hA U)) :=
    ⟨fun _ => inferInstance⟩
  let E := representedSmallEtaleModuleEquivalence B (Spec (.of A)) hA U
  have : (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec
          (.of A)) hA U))).PreservesHomology := Functor.preservesHomologyOfExact _
  have : (ModuleCat.uliftFunctor.{u + 1} A).PreservesHomology := Functor.preservesHomologyOfExact _
  have : ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (representedStructureRingSheaf B (Spec (.of A)) hA U)) ⋙ (ModuleCat.restrictScalars.{u + 1}
          (baseRingHom A B hA (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec
              (.of A)) hA U)))).Additive := ⟨by intros; ext; rfl⟩
  have : (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of A)) hA U))).Additive :=
          ⟨by intros; ext; rfl⟩
  have hΓ : PreservesFiniteLimits
      (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (representedStructureRingSheaf B (Spec (.of A)) hA U)) :=
    preservesFiniteLimits_globalSectionsFunctor_structureRingSheaf B (Spec (.of A)) hA
      (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of A)) hA U)
  have hR : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA
      (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of A)) hA U))) :=
    StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits _
  have : PreservesFiniteLimits
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (representedStructureRingSheaf B (Spec (.of A)) hA U)) ⋙
              (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA (yoneda.obj U)
                  (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec
                      (.of A)) hA U)))) := @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hΓ hR
  have : (_root_.AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property).Additive := ⟨rfl⟩
  have : E.functor.Additive := ⟨rfl⟩
  have hA' : ∀ p, 0 < p → IsZero ((E.functor.rightDerived p).obj
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property).obj F)) :=
    fun p hp => Functor.isZero_rightDerived_of_exact E.functor _ p hp
  have hGT : ∀ Y : SheafOfModules.{u} (representedSchemeStructureSheaf B (Spec (.of A)) hA U),
      Injective Y → Stacks.RightDerivedComp.acyclic
          ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
              (representedStructureRingSheaf B (Spec (.of A)) hA U)) ⋙
                  (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA (yoneda.obj U)
                      (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of A)) hA U))))
                          (E.functor.obj Y) := fun Y _ =>
    have := Injective.injective_of_adjoint E.symm.toAdjunction Y
    Stacks.RightDerivedComp.acyclic_of_injective _ _
  exact ((@Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _ _ _ _ _ _ _ _
      (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (representedStructureRingSheaf B (Spec (.of A)) hA U)) (ModuleCat.restrictScalars.{u + 1}
              (baseRingHom A B hA (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec
                  (.of A)) hA U)))
      ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
          (representedStructureRingSheaf B (Spec (.of A)) hA U)) ⋙
              (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA (yoneda.obj U)
                  (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of A)) hA U)))) _
                      ⟨by intros; ext; rfl⟩ _
      (@Functor.preservesHomologyOfExact _ _ _ _ _ _ (ModuleCat.restrictScalars.{u + 1}
          (baseRingHom A B hA (yoneda.obj U) (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec
              (.of A)) hA U))) _ hR
        (StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits _))
      (Iso.refl _) n).app _) ≪≫
    (Stacks.RightDerivedComp.objIsoOfAcyclicImage E.functor
        ((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
            (representedStructureRingSheaf B (Spec (.of A)) hA U)) ⋙
                (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA (yoneda.obj U)
                    (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec
                        (.of A)) hA U)))) hA' hGT n).symm ≪≫
    (rightDerivedIsoOfIso (representedGlobalSectionsIso A B hA U) n).app _ ≪≫
    ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property) ⋙
                (zariskiSectionsOver ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)
                    (representedZariskiRingHom A B hA U))) (ModuleCat.uliftFunctor.{u + 1} A)
      ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleOfSheaf (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U) U.left.property) ⋙
              (zariskiSectionsOver ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj U)
                  (representedZariskiRingHom A B hA U)) ⋙ (ModuleCat.uliftFunctor.{u + 1} A))
                      (Functor.associator _ _ _) n).app _).symm ≪≫
    (ModuleCat.uliftFunctor.{u + 1} A).mapIso
        (_root_.AlgebraicGeometry.SmallEtale.rightDerivedRestrictModuleCompAssociatedModuleIso
      (associatedBigEtaleSite B) _ U.left.property (representedZariskiRingHom A B hA U) F hF n)

/-- The structure morphism of the scheme underlying `U` is the image of any morphism from `U` to
the base object: a morphism to the terminal object of the slice is the structure morphism. -/
theorem toScheme_map_eq_representedStructureMorphism (w : U ⟶ Over.mk (𝟙 (B.obj hA))) :
    (BigFppfOver.toScheme B (Spec (.of A)) hA).map w = representedStructureMorphism A B hA U := by
  show B.inclusion.map w.left = B.inclusion.map U.hom
  rw [← Over.w w]
  exact (congrArg B.inclusion.map (Category.comp_id w.left)).symm

/-- **The étale cohomology of `𝓕ᵃ` on `yoneda.obj U` and the Zariski cohomology of `𝓕` on `T` have
the same dimension over a field `k`**, in every degree, for a quasi-coherent `𝒪_T`-module `𝓕` and
`U` an object of the big fppf site over `Spec k`.  This is
`AlgebraicGeometry.Space.representedCohomologyAssociatedModuleIso` read through dimensions, the
Zariski side being `AlgebraicGeometry.cohomologyOverField`. -/
theorem finrank_representedCohomology_eq_finrank_cohomologyOverField (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) (U : BigFppfOver B (Spec (.of k)) hk)
    (F : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).Modules)
    (hF : SheafOfModules.IsQuasicoherent F) (n : ℕ) :
    Module.finrank k ((ModuleCat.restrictScalars (baseRingHom k B hk (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B (Spec (.of k)) hk U))).obj
      (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
        (representedStructureRingSheaf B (Spec (.of k)) hk U)).rightDerived n).obj
        ((representedQuasicoherentSchemeEquivalence B (Spec (.of k)) hk U).functor.obj
            ⟨F, hF⟩).obj)) =
      Module.finrank k (cohomologyOverField k (representedStructureMorphism k B hk U) F n) :=
  ((representedCohomologyAssociatedModuleIso k B hk U F hF n).toLinearEquiv.trans
    ULift.moduleEquiv).finrank_eq

end AlgebraicGeometry.Space
