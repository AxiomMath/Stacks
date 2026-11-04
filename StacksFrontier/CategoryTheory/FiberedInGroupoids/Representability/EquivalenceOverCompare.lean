module

public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaSquare
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# Comparing the three notions of equivalence over a base

The library carries three structures expressing "the categories over `C` are equivalent over `C`":

* `StacksRepresentableCFG.EquivalenceOver p q`
  (`StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion`) bundles the two
  1-morphisms over `C` and states verticality of the unit and counit as the equality of a
  whiskered 2-cell with an `eqToHom`. This is the notion `Stacks 04SV` and `Stacks 02ZW` are
  stated with.
* `CategoryTheory.IsEquivalenceOver q r G`
  (`StacksFrontier.CategoryTheory.FiberedCategory.InertiaSquare`) takes the forward functor `G` as
  a parameter and states verticality componentwise, as `q.map (unitIso.hom.app X) = eqToHom _`.
  It additionally carries the triangle identity, so it is an *adjoint* equivalence.
* `CategoryTheory.Functor.IsEquivalenceOver p r a`
  (`StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization`) takes the forward functor as a
  parameter, states verticality through `CategoryTheory.Functor.IsVerticalNatTrans`, orients the
  unit as `a ⋙ inv ≅ 𝟭` rather than `𝟭 ≅ a ⋙ inv`, and — the one genuine difference in content
  — does **not** record that the forward functor is over `C`, so that hypothesis has to be
  supplied separately.

This file converts the latter two into the first, and the first back into the third.

## Main definitions

* `StacksRepresentableCFG.EquivalenceOver.ofIsEquivalenceOver`: from
  `CategoryTheory.IsEquivalenceOver`.
* `StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver`: from
  `CategoryTheory.Functor.IsEquivalenceOver` together with the missing hypothesis that the
  forward functor is over `C`.
* `StacksRepresentableCFG.EquivalenceOver.toFunctorIsEquivalenceOver`: the converse of the
  previous one, so that the two notions carrying no triangle identity are interchangeable.

## Implementation notes

There is no conversion into `CategoryTheory.IsEquivalenceOver`, because that structure demands
the triangle identity and `StacksRepresentableCFG.EquivalenceOver` does not carry it; producing
one means adjointifying the unit in the sense of `CategoryTheory.Equivalence.mk`, which replaces
the unit by a composite of whiskerings of the given unit and counit and so needs its verticality
re-proved.
-/

@[expose] public section

open CategoryTheory

namespace StacksRepresentableCFG

universe v u v₁ u₁ v₂ u₂

variable {C : Type u} [Category.{v} C] {D₁ : Type u₁} [Category.{v₁} D₁]
  {D₂ : Type u₂} [Category.{v₂} D₂]

/-- An adjoint equivalence over `C` in the sense of `CategoryTheory.IsEquivalenceOver`, read as
an equivalence over `C` in the sense of `StacksRepresentableCFG.EquivalenceOver`. The two
structures agree field by field; only the shape of the verticality condition differs, the
componentwise `q.map (unitIso.hom.app X) = eqToHom _` of the one being the whiskered
`Functor.whiskerRight unitIso.hom q = eqToHom _` of the other evaluated at `X`. The triangle
identity is discarded. -/
def EquivalenceOver.ofIsEquivalenceOver {q : D₁ ⥤ C} {r : D₂ ⥤ C} {G : D₁ ⥤ D₂}
    (E : CategoryTheory.IsEquivalenceOver q r G) : EquivalenceOver q r where
  hom := ⟨G, E.functor_over⟩
  inv := ⟨E.inverse, E.inverse_over⟩
  unitIso := E.unitIso
  counitIso := E.counitIso
  unit_over := by
    ext X
    simpa using E.unit_over X
  counit_over := by
    ext Y
    simpa using E.counit_over Y

/-- The forward functor of `EquivalenceOver.ofIsEquivalenceOver E` is `G`. -/
@[simp] lemma EquivalenceOver.ofIsEquivalenceOver_hom {q : D₁ ⥤ C} {r : D₂ ⥤ C} {G : D₁ ⥤ D₂}
    (E : CategoryTheory.IsEquivalenceOver q r G) :
    (EquivalenceOver.ofIsEquivalenceOver E).hom.functor = G := rfl

/-- The inverse functor of `EquivalenceOver.ofIsEquivalenceOver E` is `E.inverse`. -/
@[simp] lemma EquivalenceOver.ofIsEquivalenceOver_inv {q : D₁ ⥤ C} {r : D₂ ⥤ C} {G : D₁ ⥤ D₂}
    (E : CategoryTheory.IsEquivalenceOver q r G) :
    (EquivalenceOver.ofIsEquivalenceOver E).inv.functor = E.inverse := rfl

/-- An equivalence over `C` in the sense of `CategoryTheory.Functor.IsEquivalenceOver`, together
with the hypothesis `ha : a ⋙ r = p` that structure does not carry, read as an equivalence over
`C` in the sense of `StacksRepresentableCFG.EquivalenceOver`.

The unit is reoriented: `CategoryTheory.Functor.IsEquivalenceOver` states it as
`a ⋙ inv ≅ 𝟭`, so its inverse is the unit here, and verticality of that inverse comes from
`CategoryTheory.IsHomLift.lift_id_inv` with the base object transported along
`a ⋙ inv ⋙ p = p`. -/
def EquivalenceOver.ofFunctorIsEquivalenceOver {p : D₁ ⥤ C} {r : D₂ ⥤ C} {a : D₁ ⥤ D₂}
    (ha : a ⋙ r = p) (E : Functor.IsEquivalenceOver p r a) : EquivalenceOver p r where
  hom := ⟨a, ha⟩
  inv := ⟨E.inv, E.inv_over⟩
  unitIso := E.unitIso.symm
  counitIso := E.counitIso
  unit_over := by
    apply whiskerRight_eq_eqToHom
    intro x
    have h : p.IsHomLift (𝟙 (p.obj ((a ⋙ E.inv).obj x))) (E.unitIso.app x).hom :=
      E.unit_vertical x
    have hx : p.obj ((a ⋙ E.inv).obj x) = p.obj x := by
      change ((a ⋙ E.inv) ⋙ p).obj x = _
      simp only [Functor.assoc, E.inv_over, ha]
    exact (congrArg (fun U => p.IsHomLift (𝟙 U) (E.unitIso.inv.app x)) hx).mp
      (IsHomLift.lift_id_inv p (p.obj ((a ⋙ E.inv).obj x)) (E.unitIso.app x))
  counit_over := whiskerRight_eq_eqToHom _ _ _ E.counit_vertical

/-- The forward functor of `EquivalenceOver.ofFunctorIsEquivalenceOver ha E` is `a`. -/
@[simp] lemma EquivalenceOver.ofFunctorIsEquivalenceOver_hom {p : D₁ ⥤ C} {r : D₂ ⥤ C}
    {a : D₁ ⥤ D₂} (ha : a ⋙ r = p) (E : Functor.IsEquivalenceOver p r a) :
    (EquivalenceOver.ofFunctorIsEquivalenceOver ha E).hom.functor = a := rfl

/-- The inverse functor of `EquivalenceOver.ofFunctorIsEquivalenceOver ha E` is `E.inv`. -/
@[simp] lemma EquivalenceOver.ofFunctorIsEquivalenceOver_inv {p : D₁ ⥤ C} {r : D₂ ⥤ C}
    {a : D₁ ⥤ D₂} (ha : a ⋙ r = p) (E : Functor.IsEquivalenceOver p r a) :
    (EquivalenceOver.ofFunctorIsEquivalenceOver ha E).inv.functor = E.inv := rfl

/-- The converse of `StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver`: an
equivalence over `C` exhibits its own forward 1-morphism as an equivalence over `C` in the
sense of `CategoryTheory.Functor.IsEquivalenceOver`. Together the two show that the only
content `CategoryTheory.Functor.IsEquivalenceOver` omits is the strict commutation of the
forward functor with the structure functors, which is `EquivalenceOver.hom.w`. -/
def EquivalenceOver.toFunctorIsEquivalenceOver {p : D₁ ⥤ C} {q : D₂ ⥤ C}
    (e : EquivalenceOver p q) : Functor.IsEquivalenceOver p q e.hom.functor where
  inv := e.inv.functor
  inv_over := e.inv.w
  unitIso := e.unitIso.symm
  counitIso := e.counitIso
  unit_vertical := by
    intro x
    have h := e.isHomLift_unitIso_inv_app x
    have hx : p.obj ((e.hom.functor ⋙ e.inv.functor).obj x) = p.obj x := by
      change ((e.hom.functor ⋙ e.inv.functor) ⋙ p).obj x = _
      simp only [Functor.assoc, e.inv.w, e.hom.w]
    exact (congrArg (fun U => p.IsHomLift (𝟙 U) (e.unitIso.inv.app x)) hx).mpr h
  counit_vertical := by
    intro x
    have h := e.isHomLift_counitIso_hom_app x
    have hx : q.obj ((e.inv.functor ⋙ e.hom.functor).obj x) = q.obj x := by
      change ((e.inv.functor ⋙ e.hom.functor) ⋙ q).obj x = _
      simp only [Functor.assoc, e.hom.w, e.inv.w]
    exact (congrArg (fun U => q.IsHomLift (𝟙 U) (e.counitIso.hom.app x)) hx).mpr h

end StacksRepresentableCFG

end
