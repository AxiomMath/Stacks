module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHullCriterion.Basic

/-!
# The reflexive-hull adjunction for an abstract canonical map

Let `X` be an integral locally Noetherian scheme on which the dual of every coherent module is
coherent and reflexive. Then the inclusion of the coherent reflexive modules into the coherent
modules has a left adjoint whose value on `F` is the double dual `F^∨∨` and whose unit is the
canonical map `F ⟶ F^∨∨`. Here the canonical map is any map satisfying the local evaluation
formula, and reflexivity is invertibility of that map.

## Main definitions

* `ReflexiveHullCriterion.Card.ToReflexiveHull`: a choice of maps `F ⟶ F^∨∨` satisfying the
  local evaluation formula.
* `ReflexiveHullCriterion.Card.Form`: left adjoints of the inclusion of a full subcategory of
  coherent modules whose value on `F` is `F^∨∨` and whose unit is a given map.

## Main results

* `ReflexiveHullCriterion.Card.cardReflexiveHullAdjunction`: the adjunction, from the hypothesis
  that the dual of a coherent module is coherent and reflexive.

## References

* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.AlgebraicGeometry.ReflexiveHull

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveHullCriterion.Card

/-- A choice, for every scheme `X` and `𝒪_X`-module `F`, of a map `F ⟶ F^∨∨` sending a local
section `f` of `F` to evaluation at `f`. -/
abbrev ToReflexiveHull := ∀ (X : Scheme.{u}) (F : X.Modules),
  { j : F ⟶ dualSheaf (dualSheaf F) //
    ∀ (U : X.Opens) (f : Γ(F, U)) (lam : Γ(dualSheaf F, U)),
      (((j.val.app (op U)).hom f).app (op (Over.mk (𝟙 U)))).hom lam =
        (lam.app (op (Over.mk (𝟙 U)))).hom f }

variable (toRH : ToReflexiveHull.{u})

/-- The module `F` is reflexive with respect to `toRH`: the map `F ⟶ F^∨∨` chosen by `toRH` is an
isomorphism. -/
abbrev IsReflexiveOf (X : Scheme.{u}) (F : X.Modules) : Prop := IsIso (toRH X F).1

/-- An integral locally Noetherian scheme. -/
structure Situation where
  /-- The ambient scheme. -/
  X : Scheme.{u}
  /-- Integrality of the ambient scheme. -/
  [integral : IsIntegral X]
  /-- Local Noetherianity of the ambient scheme. -/
  [locallyNoetherian : IsLocallyNoetherian X]

attribute [instance] Situation.integral Situation.locallyNoetherian

/-- Left adjoints of the inclusion of the coherent modules satisfying `P` whose value on `F` is the
double dual `F^∨∨` and whose unit at `F` is `jj F`. -/
def Form (X : Scheme.{u}) (P : ObjectProperty (CoherentModules X))
    (jj : ∀ F : X.Modules, F ⟶ dualSheaf (dualSheaf F)) : Type _ :=
  { p : (Σ L : CoherentModules X ⥤ P.FullSubcategory, L ⊣ P.ι) //
      ∀ F : CoherentModules X,
        ∃ h : (p.1.obj F).obj.obj = dualSheaf (dualSheaf F.obj),
          (p.2.unit.app F).hom ≫ eqToHom h = jj F.obj }

/-- `Form` at reflexivity with respect to `toRH` and the maps chosen by `toRH`, unfolded. -/
theorem form_eq (S : Situation.{u}) :
    Form S.X (fun F => IsReflexiveOf toRH S.X F.obj) (fun F => (toRH S.X F).1) =
      { p : (Σ L : CoherentModules S.X ⥤
          ObjectProperty.FullSubcategory
            (C := ObjectProperty.FullSubcategory
              (C := SheafOfModules.{u} (structureSheaf S.X.sheaf)) (fun M => M.IsCoherent))
            (fun F => IsReflexiveOf toRH S.X F.obj),
          L ⊣ ObjectProperty.ι _) //
        ∀ F : ObjectProperty.FullSubcategory
            (C := SheafOfModules.{u} (structureSheaf S.X.sheaf)) (fun M => M.IsCoherent),
          ∃ h : (p.1.obj F).obj.obj = dualSheaf (dualSheaf F.obj),
            (p.2.unit.app F).hom ≫ eqToHom h = (toRH S.X F.obj).1 } :=
  rfl

/-- If the dual of every coherent module on `S.X` is coherent and reflexive, then the inclusion of
the coherent modules reflexive with respect to `toRH` has a left adjoint whose value on `F` is
`F^∨∨` and whose unit at `F` is the map chosen by `toRH`. -/
noncomputable def cardReflexiveHullAdjunction (S : Situation.{u})
    (H : ∀ F : S.X.Modules, F.IsCoherent →
      (dualSheaf F).IsCoherent ∧ IsReflexive (dualSheaf F)) :
    Form S.X (fun F => IsReflexiveOf toRH S.X F.obj) (fun F => (toRH S.X F).1) := by
  have hpred : (fun F : CoherentModules S.X => IsReflexiveOf toRH S.X F.obj) =
      reflexiveProperty S.X :=
    funext fun F => congrArg IsIso (toReflexiveHull_eq S.X F.obj (toRH S.X F.obj))
  have hmap : (fun F : S.X.Modules => (toRH S.X F).1) =
      (fun F : S.X.Modules => (toReflexiveHull F).1) :=
    funext fun F => toReflexiveHull_eq S.X F (toRH S.X F)
  rw [hpred, hmap]
  exact reflexiveHullAdjunction_of_dualSheaf S.X H

end Stacks.AlgebraicGeometry.ReflexiveHullCriterion.Card
