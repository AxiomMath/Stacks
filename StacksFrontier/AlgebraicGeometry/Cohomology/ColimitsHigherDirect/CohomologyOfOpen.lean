module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.RestrictionPreservesInjectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleAdjunction
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# Cohomology on an open subspace

The cohomology of a sheaf of modules over an open subset agrees canonically with
the cohomology of its restriction to that open subspace.

## Main definitions

* `AlgebraicGeometry.sectionsNatIso`: sections over an open of a sheaf of modules agree with the
  global sections of its restriction to the open subspace.

## Main results

* `AlgebraicGeometry.cohomologyOverNatIsoRestriction` identifies these
  cohomology functors naturally in the sheaf of modules.
* `AlgebraicGeometry.cohomologyOverModuleNatIsoRestriction` identifies them before forgetting
  the module structure, as functors into modules over the sections on the open.

## Implementation notes

In `AlgebraicGeometry.cohomologyOverNatIsoRestriction` both sides are right-derived section
functors with their module values forgotten to abelian groups, so that they have the same target
category. In `AlgebraicGeometry.cohomologyOverModuleNatIsoRestriction` the two target categories
agree on the nose: the sections of `𝒪_X` over `(jFun X U).obj ⊤` are the global sections of `𝒪_U`
by `rfl`, because `phiSh X U` is the identity. The open is spelled `(jFun X U).obj ⊤` rather than
`U` there; `AlgebraicGeometry.jFun_obj_top` identifies the two.

Restriction to the open subspace is a left adjoint that preserves injective objects, so the
derived functor of the composite is the composite of the derived functors.

## References

* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- Sections over an open of a sheaf of modules agree with global sections of its restriction
to that open subspace, naturally in the sheaf. -/
public noncomputable def sectionsNatIso (X : SheafedSpace RingCat.{u})
    (U : Opens X.carrier) :
    (SheafOfModules.evaluation (OXSh X) (op U) ⋙
      forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op U))) AddCommGrpCat.{u}) ≅
    restMod X U ⋙
      (SheafOfModules.evaluation (OUSh X U) (op (⊤ : Opens U)) ⋙
        forget₂ (ModuleCat.{u} ((OUSh X U).obj.obj (op (⊤ : Opens U)))) AddCommGrpCat.{u}) := by
  have hU : (jFun X U).obj (⊤ : Opens U) = U := by
    apply Opens.ext
    change (Subtype.val '' Set.univ : Set X.carrier) = (U : Set X.carrier)
    rw [Set.image_univ, Subtype.range_coe]
  refine NatIso.ofComponents (fun M => ?_) ?_
  · let V : Opens X.carrier := (jFun X U).obj (⊤ : Opens ((Opens.toTopCat X.carrier).obj U))
    have hscU :
        (forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op U))) AddCommGrpCat.{u}).obj
          (M.val.obj (op U)) =
        (forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op U))) AddCommGrpCat.{u}).obj
          ((ModuleCat.restrictScalars (RingHom.id _)).obj (M.val.obj (op U))) := by rfl
    let eU :
        (forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op U))) AddCommGrpCat.{u}).obj
          ((ModuleCat.restrictScalars (RingHom.id _)).obj (M.val.obj (op U))) =
        (forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op V))) AddCommGrpCat.{u}).obj
          ((ModuleCat.restrictScalars (RingHom.id _)).obj (M.val.obj (op V))) :=
      congrArg (fun W : Opens X.carrier =>
        (forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op W))) AddCommGrpCat.{u}).obj
          ((ModuleCat.restrictScalars (RingHom.id _)).obj (M.val.obj (op W)))) hU.symm
    have hsc :
        (forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op V))) AddCommGrpCat.{u}).obj
          (M.val.obj (op V)) =
        (forget₂ (ModuleCat.{u} ((OUSh X U).obj.obj (op (⊤ : Opens U))))
          AddCommGrpCat.{u}).obj
          ((ModuleCat.restrictScalars ((phiSh X U).hom.app (op (⊤ : Opens U))).hom).obj
            (M.val.obj (op V))) := by
      rfl
    exact eqToIso (hscU.trans (eU.trans hsc))
  · intro M N f
    let z : ∀ V : Opens X.carrier,
        (forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op V))) AddCommGrpCat.{u}).obj
            ((ModuleCat.restrictScalars (RingHom.id _)).obj (M.val.obj (op V))) ⟶
          (forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op V))) AddCommGrpCat.{u}).obj
            ((ModuleCat.restrictScalars (RingHom.id _)).obj (N.val.obj (op V))) :=
      fun V => (forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op V))) AddCommGrpCat.{u}).map
        ((ModuleCat.restrictScalars (RingHom.id _)).map (f.val.app (op V)))
    let V : Opens X.carrier := (jFun X U).obj (⊤ : Opens ((Opens.toTopCat X.carrier).obj U))
    convert CategoryTheory.eqToHom_naturality z hU.symm using 1
    all_goals rfl

/-- Sheaves of modules over a sheaf of rings on a space form a category with enough
injectives. -/
@[sga "4½ Etat_0 6.2" "special case"]
noncomputable local instance sheafOfModulesEnoughInjectives
    (Y : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}) :
    EnoughInjectives (SheafOfModules.{u} R) := by
  let _ : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) := inferInstance
  exact IsGrothendieckAbelian.enoughInjectives

/-- Evaluating a sheaf of modules on an open is an additive functor. -/
local instance evaluation_additive
    (Y : TopCat.{u})
    (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})
    (W : Opens Y) :
    (SheafOfModules.evaluation R (op W)).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- Evaluating a sheaf of modules on an open subspace at its whole space is additive. -/
local instance evaluation_additive_open (X : SheafedSpace RingCat.{u})
    (U : Opens X.carrier) :
    (SheafOfModules.evaluation (OUSh X U) (op (⊤ : Opens U))).Additive := by
  dsimp [SheafOfModules.evaluation]
  infer_instance

/-- The cohomology of a sheaf of modules over an open is naturally isomorphic
to the cohomology of its restriction to that open subspace. -/
@[stacks 01E1 "cohomology_of_open"]
public noncomputable def cohomologyOverNatIsoRestriction (X : SheafedSpace RingCat.{u})
    (U : Opens X.carrier) (p : ℕ) :
    ((SheafOfModules.evaluation (OXSh X) (op U) ⋙
        forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op U))) AddCommGrpCat.{u}).rightDerived p) ≅
      restMod X U ⋙
        ((SheafOfModules.evaluation (OUSh X U) (op (⊤ : Opens U)) ⋙
          forget₂ (ModuleCat.{u} ((OUSh X U).obj.obj (op (⊤ : Opens U))))
            AddCommGrpCat.{u}).rightDerived p) :=
  let F := SheafOfModules.evaluation (OXSh X) (op U) ⋙
    forget₂ (ModuleCat.{u} ((OXSh X).obj.obj (op U))) AddCommGrpCat.{u}
  let G := SheafOfModules.evaluation (OUSh X U) (op (⊤ : Opens U)) ⋙
    forget₂ (ModuleCat.{u} ((OUSh X U).obj.obj (op (⊤ : Opens U)))) AddCommGrpCat.{u}
  let L := restMod X U
  letI : L.IsLeftAdjoint :=
    (ExtensionByZeroModules.jStarAdjunction U (OXSh X)).isLeftAdjoint
  letI : PreservesLimitsOfSize L := (jShriekAdjunction X U).rightAdjoint_preservesLimits
  letI : PreservesColimitsOfSize L := inferInstance
  letI : PreservesFiniteLimits L := inferInstance
  letI : PreservesFiniteColimits L := inferInstance
  letI : L.PreservesZeroMorphisms := inferInstance
  letI : PreservesBinaryBiproducts L :=
    preservesBinaryBiproducts_of_preservesBinaryProducts L
  letI : L.Additive := Functor.additive_of_preservesBinaryBiproducts L
  letI : L.PreservesInjectiveObjects := ⟨fun {I} _ =>
    Stacks.Cohomology.HigherDirectImage.restMod_preservesInjective X U I⟩
  let α : F ≅ L ⋙ G := sectionsNatIso X U
  (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso α p) ≪≫
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G p)

/-- The image of the whole of the open subspace `U` is the open `U`. -/
public theorem jFun_obj_top (X : SheafedSpace RingCat.{u}) (U : Opens X.carrier) :
    (jFun X U).obj (⊤ : Opens ((Opens.toTopCat X.carrier).obj U)) = U := by
  apply Opens.ext
  show (Subtype.val '' Set.univ : Set X.carrier) = (U : Set X.carrier)
  rw [Set.image_univ, Subtype.range_coe]

/-- The cohomology of a sheaf of modules over an open is naturally isomorphic, as a module over
the sections of `𝒪_X` on that open, to the cohomology of its restriction to the open subspace. -/
@[stacks 01E1 "cohomology_of_open, as modules over the sections on the open"]
public noncomputable def cohomologyOverModuleNatIsoRestriction (X : SheafedSpace RingCat.{u})
    (U : Opens X.carrier) (p : ℕ) :
    ((SheafOfModules.evaluation (OXSh X)
          (op ((jFun X U).obj (⊤ : Opens ((Opens.toTopCat X.carrier).obj U)))) :
        SheafOfModules.{u} (OXSh X) ⥤ _).rightDerived p) ≅
      restMod X U ⋙ ((SheafOfModules.evaluation (OUSh X U)
          (op (⊤ : Opens ((Opens.toTopCat X.carrier).obj U))) :
        SheafOfModules.{u} (OUSh X U) ⥤ _).rightDerived p) :=
  let G : SheafOfModules.{u} (OUSh X U) ⥤
      ModuleCat.{u} ((OUSh X U).obj.obj (op (⊤ : Opens ((Opens.toTopCat X.carrier).obj U)))) :=
    SheafOfModules.evaluation (OUSh X U)
      (op (⊤ : Opens ((Opens.toTopCat X.carrier).obj U)))
  let L : SheafOfModules.{u} (OXSh X) ⥤ SheafOfModules.{u} (OUSh X U) := restMod X U
  letI : L.IsLeftAdjoint :=
    (ExtensionByZeroModules.jStarAdjunction U (OXSh X)).isLeftAdjoint
  letI : PreservesLimitsOfSize L := (jShriekAdjunction X U).rightAdjoint_preservesLimits
  letI : PreservesColimitsOfSize L := inferInstance
  letI : PreservesFiniteLimits L := inferInstance
  letI : PreservesFiniteColimits L := inferInstance
  letI : L.PreservesZeroMorphisms := inferInstance
  letI : PreservesBinaryBiproducts L :=
    preservesBinaryBiproducts_of_preservesBinaryProducts L
  letI : L.Additive := Functor.additive_of_preservesBinaryBiproducts L
  letI : L.PreservesInjectiveObjects := ⟨fun {I} _ =>
    Stacks.Cohomology.HigherDirectImage.restMod_preservesInjective X U I⟩
  Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G p

end AlgebraicGeometry
