module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedCocycleSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictBridgeCocycle
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictDerivedEquivalence
public import StacksFrontier.CategoryTheory.Functor.CocycleTransport
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Descent data of derived modules on a simplicial algebraic space, on the strict components

Let `X` be a simplicial algebraic space. A pair `(K₀, α)` of an object `K₀` of `D(𝒪_{X_0})` and
an isomorphism `α : L X(δ¹₁)^* K₀ ≅ L X(δ¹₀)^* K₀` on `X_1` satisfying the cocycle condition on
`X_2` (the input of Stacks 0DLA) is carried, through the equivalences
`L realize_n^* : D(𝒪_n) ≌ D(𝒪_{X_n})` of the strict components, to a pair on the degree-zero strict
component satisfying the cocycle condition of Stacks 0GMF.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.spacesEtaleDerivedPasteIso`: the
  identification `L X(ψ)^* ⋙ L X(φ)^* ≅ L X(v)^*` for a factorization `ψ ≫ φ = v`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.SpacesEtaleDerivedCocycle`: the cocycle
  condition on `X_2` for `α : L X(δ¹₁)^* K₀ ≅ L X(δ¹₀)^* K₀`.

## Main results

* `strictComponentDerivedTransitionIso_pasteIsoOfEq` (in
  `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`): the derived squares of the strict
  components carry the compositor at a factorization to `spacesEtaleDerivedPasteIso`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.exists_derivedModuleCocyclePair`: a pair
  `(K₀, α)` with the cocycle condition on `X_2` gives a pair of Stacks 0GMF on the strict
  components realizing to it.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.Cohomology.DerivedPullbackOfToposHom
open scoped Simplicial

universe u

-- no global `HasDerivedCategory` instance on these categories of sheaves of modules
attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : SimplicialObject (AlgebraicSpaces B S hS))

/-- `X(φ) ≫ X(ψ) = X(v)` for a factorization `ψ ≫ φ = v` of simplex maps. -/
theorem map_op_comp_map_op_of_eq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) : X.map φ.op ≫ X.map ψ.op = X.map v.op := by
  subst h
  exact SimplicialObject.map_op_comp_map_op X ψ φ

/-- The identification `L X(ψ)^* ⋙ L X(φ)^* ≅ L X(v)^*` of derived pullbacks for a
factorization `ψ ≫ φ = v` of simplex maps (Stacks 0D6D). -/
def spacesEtaleDerivedPasteIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) :
    derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op m)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op l)))
        (spacesEtaleRingedToposHom (X.map ψ.op)) ⋙
      derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
        (spacesEtaleRingedToposHom (X.map φ.op)) ≅
      derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op l)))
        (spacesEtaleRingedToposHom (X.map v.op)) :=
  spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp (X.map φ.op) (X.map ψ.op) ≪≫
    Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackCongr.{u + 1, u + 1, u + 1,
      u + 1, u + 1, u + 1} (X' := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := spacesEtaleRingedTopos B S hS (X.obj (op l)))
      (congrArg spacesEtaleRingedToposHom (map_op_comp_map_op_of_eq X ψ φ v h))

/-- **The derived squares of the strict components carry the compositor at a factorization to
`spacesEtaleDerivedPasteIso`**: `strictComponentDerivedTransitionIso_comp` read at a chosen
factorization `ψ ≫ φ = v`. -/
theorem strictComponentDerivedTransitionIso_pasteIsoOfEq {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (v : l ⟶ n) (h : ψ ≫ φ = v)
    (K : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) l).Modules) :
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n)).map
        ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X) ψ φ v h K).hom ≫
      ((strictComponentDerivedTransitionIso X v).app K).hom =
    (strictComponentDerivedTransitionIso X φ).hom.app
        (((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) ψ).obj K) ≫
      (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
          (spacesEtaleRingedToposHom (X.map φ.op))).map
        ((strictComponentDerivedTransitionIso X ψ).hom.app K) ≫
      (spacesEtaleDerivedPasteIso X ψ φ v h).hom.app
        ((derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op l)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) l)
          (strictComponentRingedToposHom X l)).obj K) := by
  subst h
  simp only [SimplicialSiteSituation.derivedModulePasteIsoOfEq,
    SimplicialSiteSituation.derivedModulePasteIso, Iso.trans_hom, Iso.app_hom,
    SimplicialSiteSituation.derivedTransitionCompIso_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id, spacesEtaleDerivedPasteIso, NatTrans.comp_app]
  exact strictComponentDerivedTransitionIso_comp X ψ φ K

/-- The cocycle condition of `derivedModuleCocycle_of_spacesEtale`, at the compositors. -/
theorem derivedModuleCocycle_of_spacesEtale_aux
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules)
    (α : (derivedPullback
        (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (1 : Fin 2)).op))).obj K₀ ≅
      (derivedPullback
        (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (0 : Fin 2)).op))).obj K₀)
    (hα : (derivedPullback (spacesEtaleRingedToposHom
        (X.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (1 : Fin 3)))))).map α.hom =
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (1 : Fin 3))
        _ SimplexCategory.delta_one_comp_delta_one).hom.app K₀ ≫
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (2 : Fin 3))
        _ SimplexCategory.delta_one_comp_delta_two).inv.app K₀ ≫
      (derivedPullback (spacesEtaleRingedToposHom
        (X.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (2 : Fin 3)))))).map α.hom ≫
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (2 : Fin 3))
        _ SimplexCategory.delta_zero_comp_delta_two).hom.app K₀ ≫
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (0 : Fin 3))
        _ SimplexCategory.delta_one_comp_delta_zero).inv.app K₀ ≫
      (derivedPullback (spacesEtaleRingedToposHom
        (X.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (0 : Fin 3)))))).map α.hom ≫
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 3))
        _ SimplexCategory.delta_zero_comp_delta_zero).hom.app K₀ ≫
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 3))
        _ SimplexCategory.delta_zero_comp_delta_one).inv.app K₀)
    (K₀' : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) ⦋0⦌).Modules)
    (e : (derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).obj K₀' ≅ K₀)
    (α' : ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
        (SimplexCategory.δ (1 : Fin 2))).obj K₀' ≅ ((strictSituation X).derivedTransitionPullback
        (strictStructureSheaf X) (SimplexCategory.δ (0 : Fin 2))).obj K₀')
    (hα' : (derivedPullback (strictComponentRingedToposHom X ⦋0 + 1⦌)).map α'.hom =
        (strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2))).hom.app K₀' ≫
          (derivedPullback
            (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (1 : Fin 2)).op))).map e.hom ≫
          α.hom ≫
          (derivedPullback
            (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (0 : Fin 2)).op))).map e.inv ≫
          (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2))).inv.app K₀') :
    ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) (m := ⦋0 + 1⦌)
        (SimplexCategory.δ (1 : Fin 3))).map α'.hom =
      ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
        (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (1 : Fin 3)) _
          SimplexCategory.delta_one_comp_delta_one K₀').hom ≫
      ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
        (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) _
          SimplexCategory.delta_one_comp_delta_two K₀').inv ≫
      ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) (m := ⦋0 + 1⦌)
        (SimplexCategory.δ (2 : Fin 3))).map α'.hom ≫
      ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
        (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) _
          SimplexCategory.delta_zero_comp_delta_two K₀').hom ≫
      ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
        (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (0 : Fin 3)) _
          SimplexCategory.delta_one_comp_delta_zero K₀').inv ≫
      ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) (m := ⦋0 + 1⦌)
        (SimplexCategory.δ (0 : Fin 3))).map α'.hom ≫
      ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
        (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 3)) _
          SimplexCategory.delta_zero_comp_delta_zero K₀').hom ≫
      ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
        (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 3)) _
          SimplexCategory.delta_zero_comp_delta_one K₀').inv :=
  eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq (cocycle_of_faithful
    (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2)))
    (strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2)))
    (strictComponentDerivedTransitionIso X (m := ⦋0 + 1⦌)
      (SimplexCategory.δ (0 : Fin 3)))
    (strictComponentDerivedTransitionIso X (m := ⦋0 + 1⦌)
      (SimplexCategory.δ (1 : Fin 3)))
    (strictComponentDerivedTransitionIso X (m := ⦋0 + 1⦌)
      (SimplexCategory.δ (2 : Fin 3)))
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (1 : Fin 3)) _
        SimplexCategory.delta_one_comp_delta_one)
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) _
        SimplexCategory.delta_one_comp_delta_two)
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) _
        SimplexCategory.delta_zero_comp_delta_two)
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (0 : Fin 3)) _
        SimplexCategory.delta_one_comp_delta_zero)
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 3)) _
        SimplexCategory.delta_zero_comp_delta_zero)
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 3)) _
        SimplexCategory.delta_zero_comp_delta_one)
    ((strictComponentDerivedTransitionIso X (n := ⦋1 + 1⦌)
      (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 0)).app K₀')
    ((strictComponentDerivedTransitionIso X (n := ⦋1 + 1⦌)
      (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 1)).app K₀')
    ((strictComponentDerivedTransitionIso X (n := ⦋1 + 1⦌)
      (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 2)).app K₀')
    ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
      (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (1 : Fin 3)) _
        SimplexCategory.delta_one_comp_delta_one K₀')
    ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
      (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) _
        SimplexCategory.delta_one_comp_delta_two K₀')
    ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
      (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) _
        SimplexCategory.delta_zero_comp_delta_two K₀')
    ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
      (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (0 : Fin 3)) _
        SimplexCategory.delta_one_comp_delta_zero K₀')
    ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
      (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 3)) _
        SimplexCategory.delta_zero_comp_delta_zero K₀')
    ((strictSituation X).derivedModulePasteIsoOfEq (strictStructureSheaf X)
      (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 3)) _
        SimplexCategory.delta_zero_comp_delta_one K₀')
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      (strictComponentDerivedTransitionIso_pasteIsoOfEq X _ _ _
      SimplexCategory.delta_one_comp_delta_one K₀')) (by heq_congr))))
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      (strictComponentDerivedTransitionIso_pasteIsoOfEq X _ _ _
      SimplexCategory.delta_one_comp_delta_two K₀')) (by heq_congr))))
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      (strictComponentDerivedTransitionIso_pasteIsoOfEq X _ _ _
      SimplexCategory.delta_zero_comp_delta_two K₀')) (by heq_congr))))
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      (strictComponentDerivedTransitionIso_pasteIsoOfEq X _ _ _
      SimplexCategory.delta_one_comp_delta_zero K₀')) (by heq_congr))))
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      (strictComponentDerivedTransitionIso_pasteIsoOfEq X _ _ _
      SimplexCategory.delta_zero_comp_delta_zero K₀')) (by heq_congr))))
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      (strictComponentDerivedTransitionIso_pasteIsoOfEq X _ _ _
      SimplexCategory.delta_zero_comp_delta_one K₀')) (by heq_congr))))
    e α (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq hα) (by heq_congr)))) α'
    (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq hα') (by heq_congr))))))
    (by heq_congr)))

/-- **The cocycle condition is carried to the strict components.** Let `K₀ ∈ D(𝒪_{X_0})` and
`α : L X(δ¹₁)^* K₀ ≅ L X(δ¹₀)^* K₀` satisfy the cocycle condition on `X_2`, read through the
identifications `spacesEtaleDerivedPasteIso`. If `e : L realize_0^* K₀' ≅ K₀` and
`L realize_1^* α'` is `α` read through `e` and the derived squares of the strict components, then
`α'` satisfies the cocycle condition of Stacks 0GMF. -/
theorem derivedModuleCocycle_of_spacesEtale
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules)
    (α : (derivedPullback
        (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (1 : Fin 2)).op))).obj K₀ ≅
      (derivedPullback
        (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (0 : Fin 2)).op))).obj K₀)
    (hα : (derivedPullback (spacesEtaleRingedToposHom
        (X.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (1 : Fin 3)))))).map α.hom =
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (1 : Fin 3))
        _ SimplexCategory.delta_one_comp_delta_one).hom.app K₀ ≫
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (2 : Fin 3))
        _ SimplexCategory.delta_one_comp_delta_two).inv.app K₀ ≫
      (derivedPullback (spacesEtaleRingedToposHom
        (X.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (2 : Fin 3)))))).map α.hom ≫
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (2 : Fin 3))
        _ SimplexCategory.delta_zero_comp_delta_two).hom.app K₀ ≫
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (0 : Fin 3))
        _ SimplexCategory.delta_one_comp_delta_zero).inv.app K₀ ≫
      (derivedPullback (spacesEtaleRingedToposHom
        (X.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (0 : Fin 3)))))).map α.hom ≫
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 3))
        _ SimplexCategory.delta_zero_comp_delta_zero).hom.app K₀ ≫
      (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 3))
        _ SimplexCategory.delta_zero_comp_delta_one).inv.app K₀)
    (K₀' : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) ⦋0⦌).Modules)
    (e : (derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).obj K₀' ≅ K₀)
    (α' : ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
        (SimplexCategory.δ (1 : Fin 2))).obj K₀' ≅ ((strictSituation X).derivedTransitionPullback
        (strictStructureSheaf X) (SimplexCategory.δ (0 : Fin 2))).obj K₀')
    (hα' : (derivedPullback (strictComponentRingedToposHom X ⦋0 + 1⦌)).map α'.hom =
        (strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2))).hom.app K₀' ≫
          (derivedPullback
            (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (1 : Fin 2)).op))).map e.hom ≫
          α.hom ≫
          (derivedPullback
            (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (0 : Fin 2)).op))).map e.inv ≫
          (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2))).inv.app K₀') :
    ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
        (SimplexCategory.δ (1 : Fin 3))).map α'.hom =
      ((strictSituation X).derivedModuleGlueLeft (strictStructureSheaf X) K₀').inv ≫
        ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
          (SimplexCategory.δ (2 : Fin 3))).map α'.hom ≫
        ((strictSituation X).derivedModuleGlueMiddle (strictStructureSheaf X) K₀').hom ≫
        ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
          (SimplexCategory.δ (0 : Fin 3))).map α'.hom ≫
        ((strictSituation X).derivedModuleGlueRight (strictStructureSheaf X) K₀').hom := by
  have key := derivedModuleCocycle_of_spacesEtale_aux X K₀ α hα K₀' e α' hα'
  simp only [SimplicialSiteSituation.derivedModuleGlueLeft,
    SimplicialSiteSituation.derivedModuleGlueMiddle, SimplicialSiteSituation.derivedModuleGlueRight,
    SimplicialSiteSituation.derivedModuleGlueOfEq_hom,
    SimplicialSiteSituation.derivedModuleGlueOfEq_inv, Category.assoc]
  exact key

/-- A morphism `L realize_1^* K₁ ⟶ L realize_1^* K₂` on `X_1` which is invertible comes from an
isomorphism of the strict component, `L realize_1^*` being fully faithful. -/
theorem exists_strictComponentDerivedPullback_one_map_eq
    (K₀' : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) ⦋0⦌).Modules)
    (f : (derivedPullback (strictComponentRingedToposHom X ⦋0 + 1⦌)).obj
        (((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
          (SimplexCategory.δ (1 : Fin 2))).obj K₀') ⟶
      (derivedPullback (strictComponentRingedToposHom X ⦋0 + 1⦌)).obj
        (((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
          (SimplexCategory.δ (0 : Fin 2))).obj K₀')) [IsIso f] :
    ∃ α' : ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
        (SimplexCategory.δ (1 : Fin 2))).obj K₀' ≅ ((strictSituation X).derivedTransitionPullback
        (strictStructureSheaf X) (SimplexCategory.δ (0 : Fin 2))).obj K₀',
      (derivedPullback (strictComponentRingedToposHom X ⦋0 + 1⦌)).map α'.hom = f := by
  have hF := Functor.FullyFaithful.ofFullyFaithful
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op ⦋0 + 1⦌)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) ⦋0 + 1⦌)
      (strictComponentRingedToposHom X ⦋0 + 1⦌))
  refine ⟨hF.preimageIso (asIso f), ?_⟩
  exact hF.map_preimage f

/-- The isomorphism `α` on `X_1`, read through `e : L realize_0^* K₀' ≅ K₀` and the derived
squares of the strict components, comes from an isomorphism of the degree-one strict
component. -/
theorem exists_strictComponentDerivedPullback_one_map_eq_conj
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules)
    (α : (derivedPullback
        (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (1 : Fin 2)).op))).obj K₀ ≅
      (derivedPullback
        (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (0 : Fin 2)).op))).obj K₀)
    (K₀' : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) ⦋0⦌).Modules)
    (e : (derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).obj K₀' ≅ K₀) :
    ∃ α' : ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X)
        (SimplexCategory.δ (1 : Fin 2))).obj K₀' ≅ ((strictSituation X).derivedTransitionPullback
        (strictStructureSheaf X) (SimplexCategory.δ (0 : Fin 2))).obj K₀',
      (derivedPullback (strictComponentRingedToposHom X ⦋0 + 1⦌)).map α'.hom =
        (strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2))).hom.app K₀' ≫
          (derivedPullback
            (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (1 : Fin 2)).op))).map e.hom ≫
          α.hom ≫
          (derivedPullback
            (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (0 : Fin 2)).op))).map e.inv ≫
          (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2))).inv.app K₀' :=
  exists_strictComponentDerivedPullback_one_map_eq X K₀' _

/-- Every object of `D(𝒪_{X_0})` is `L realize_0^*` of an object of the degree-zero strict
component, `L realize_0^*` being an equivalence. -/
theorem exists_strictComponentDerivedPullback_zero_obj_iso
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules) :
    ∃ K₀' : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) ⦋0⦌).Modules,
      Nonempty ((derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).obj K₀' ≅ K₀) :=
  ⟨(derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).inv.obj K₀,
    ⟨(derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).asEquivalence.counitIso.app K₀⟩⟩

/-- **The cocycle condition on `X_2`** for `α : L X(δ¹₁)^* K₀ ≅ L X(δ¹₀)^* K₀`: the three
derived pullbacks of `α` to `X_2` compose, read through the identifications
`spacesEtaleDerivedPasteIso` of the composite face maps. -/
structure SpacesEtaleDerivedCocycle
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules)
    (α : (derivedPullback
        (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (1 : Fin 2)).op))).obj K₀ ≅
      (derivedPullback
        (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (0 : Fin 2)).op))).obj K₀) :
    Prop where
  /-- `L X(δ²₁)^* α = L X(δ²₀)^* α ∘ L X(δ²₂)^* α` through the identifications. -/
  cocycle : (derivedPullback (spacesEtaleRingedToposHom
      (X.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (1 : Fin 3)))))).map α.hom =
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (1 : Fin 3)) _
      SimplexCategory.delta_one_comp_delta_one).hom.app K₀ ≫
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) _
      SimplexCategory.delta_one_comp_delta_two).inv.app K₀ ≫
    (derivedPullback (spacesEtaleRingedToposHom
      (X.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (2 : Fin 3)))))).map α.hom ≫
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (2 : Fin 3)) _
      SimplexCategory.delta_zero_comp_delta_two).hom.app K₀ ≫
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (0 : Fin 3)) _
      SimplexCategory.delta_one_comp_delta_zero).inv.app K₀ ≫
    (derivedPullback (spacesEtaleRingedToposHom
      (X.map (Quiver.Hom.op (X := ⦋0 + 1⦌) (SimplexCategory.δ (0 : Fin 3)))))).map α.hom ≫
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 3)) _
      SimplexCategory.delta_zero_comp_delta_zero).hom.app K₀ ≫
    (spacesEtaleDerivedPasteIso X (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 3)) _
      SimplexCategory.delta_zero_comp_delta_one).inv.app K₀

/-- **A cocycle pair on `X` gives a pair of Stacks 0GMF on the strict components.** Let
`K₀ ∈ D(𝒪_{X_0})` and `α : L X(δ¹₁)^* K₀ ≅ L X(δ¹₀)^* K₀` satisfy the cocycle condition on `X_2`.
Then there is a pair `(K₀', α')` on the degree-zero strict component with the cocycle condition
of Stacks 0GMF and an isomorphism `e : L realize_0^* K₀' ≅ K₀` carrying `L realize_1^* α'` to
`α`. -/
theorem exists_derivedModuleCocyclePair
    (K₀ : DerivedCategory (spacesEtaleRingedTopos B S hS (X.obj (op ⦋0⦌))).Modules)
    (α : (derivedPullback
        (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (1 : Fin 2)).op))).obj K₀ ≅
      (derivedPullback
        (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (0 : Fin 2)).op))).obj K₀)
    (hα : SpacesEtaleDerivedCocycle X K₀ α) :
    ∃ (Pr : (strictSituation X).DerivedModuleCocyclePair (strictStructureSheaf X))
      (e : (derivedPullback (strictComponentRingedToposHom X ⦋0⦌)).obj Pr.obj ≅ K₀),
      (derivedPullback (strictComponentRingedToposHom X ⦋0 + 1⦌)).map Pr.iso.hom =
        (strictComponentDerivedTransitionIso X (SimplexCategory.δ (1 : Fin 2))).hom.app Pr.obj ≫
          (derivedPullback
            (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (1 : Fin 2)).op))).map e.hom ≫
          α.hom ≫
          (derivedPullback
            (spacesEtaleRingedToposHom (X.map (SimplexCategory.δ (0 : Fin 2)).op))).map e.inv ≫
          (strictComponentDerivedTransitionIso X (SimplexCategory.δ (0 : Fin 2))).inv.app
            Pr.obj := by
  obtain ⟨K₀', ⟨e⟩⟩ := exists_strictComponentDerivedPullback_zero_obj_iso X K₀
  exact (exists_strictComponentDerivedPullback_one_map_eq_conj X K₀ α K₀' e).elim fun α' hα' ↦
    ⟨⟨K₀', α', derivedModuleCocycle_of_spacesEtale X K₀ α hα.cocycle K₀' e α' hα'⟩, e, hα'⟩

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
