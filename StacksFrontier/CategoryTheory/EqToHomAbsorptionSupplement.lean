module

public import StacksFrontier.CategoryTheory.EqToHomAbsorption
public import Mathlib.CategoryTheory.EqToHom
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.CategoryTheory.EqToHomAbsorption

/-!
# Additions to `EqToHomAbsorption`

Declarations extending the module above, kept in their own module.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

/-- **A family of morphisms is carried by the two transports of an equality of its parameter.**
For a family `f` of morphisms `X a ⟶ Y a` indexed by `α`, an equality `a = a'`, and *any* two
transports of the source and the target objects, `f a'` followed by the target transport is the
source transport followed by `f a`.

This is the one fact about a parameterised morphism that an assembler needs and that `congrArg`
cannot supply.  `congrArg` on the parameter equality builds a motive in which both objects
appear, and when the spelling the goal fixes differs definitionally from the family's own, it is
forming that motive which exhausts the kernel.  Here the two transports are *hypotheses*, so a
consumer supplies each at whichever spelling its goal fixes, and `subst` discharges the lemma at
plain variables with nothing else in the term.

`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso_eqToHom` is this statement at the
transport of the inverse image of an ideal sheaf, where the pattern arises. -/
theorem comp_eqToHom_eq_eqToHom_comp_of_param {α : Type*} {X Y : α → C}
    (f : ∀ a, X a ⟶ Y a) {a a' : α} (h : a = a') (hΦ : X a' = X a) (hΨ : Y a' = Y a) :
    f a' ≫ eqToHom hΨ = eqToHom hΦ ≫ f a := by
  subst h
  exact (comp_eqToHom_of_refl hΨ _).trans (eqToHom_comp_of_refl hΦ _).symm

/-- **Two equal functors carry a morphism to each other, across any two transports of its
source and target.**  This is `CategoryTheory.Functor.congr_hom` with the two `eqToHom`s taken as
*hypotheses* instead of built from `CategoryTheory.Functor.congr_obj` of the equality.

That is the whole point of having it.  `CategoryTheory.Functor.congr_hom`'s transports are
`CategoryTheory.Functor.congr_obj h X`, and a consumer whose own goal spells them some other way
— as `eqToHom` of a reflexive equation of two definitionally equal objects, say — can only reach
them through a definitional equality of two `eqToHom`s whose proofs are different terms.  The
unifier answers that one by reducing the `Eq.rec` inside `eqToHom`, which on a large category is
unbounded: on the inverse image of modules over a big fppf site, matching
`CategoryTheory.Functor.congr_hom`'s conclusion against a restatement with the consumer's own
transports reduces `Eq.rec` 272 608 times and `Quiver.Hom` 332 822 times, and exhausts 200 000
heartbeats.  With the transports supplied, nothing is matched: `subst` makes both reflexive and
`CategoryTheory.eqToHom_refl` fires on each.

Supply the two transports and then absorb them with `CategoryTheory.eqToHom_comp_of_refl` and
`CategoryTheory.comp_eqToHom_of_refl`, in a declaration of their own; the three steps are
affordable apart and not together. -/
theorem Functor.congr_hom_of_eq {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (h : F = G) {X Y : C} (f : X ⟶ Y)
    (p : F.obj X = G.obj X) (q : G.obj Y = F.obj Y) :
    F.map f = eqToHom p ≫ G.map f ≫ eqToHom q := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

end CategoryTheory

