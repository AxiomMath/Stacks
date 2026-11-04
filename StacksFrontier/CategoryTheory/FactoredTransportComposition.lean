module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.Category

/-!
# The composition law for a transport whose values factor, generically

A *transport* here is a family of comparison morphisms `Θ_g` attached to the morphisms `g` of
some category, each comparing two ways of carrying an object across a square of functors.  Such
a transport is often built as a composite: a first transport followed by a correction, as
`AlgebraicGeometry.Space.representedAssociatedModulePullbackIso` is
`AlgebraicGeometry.Space.representedModuleObjPullbackIso` followed by the base-change comparison
of [Stacks Project, Tag 03LC] (1).  When the correction has a composition law of its own, the
composition law for the composite transport follows from the composition law for the first
transport, the two corrections cancelling.

This file proves that implication **in a generic category, with every functor, object and
morphism a variable**, together with the piece of isomorphism algebra it consumes: a cocycle
condition written with forward comparisons, solved for the inverses that a transport built from
them carries.

## Why it is stated here rather than at its instance

The reason is the one the implementation notes of
`StacksFrontier/CategoryTheory/SquareMapComposition.lean` record for the composition law of the
canonical map of a square, and it applies here too.  At a geometric instantiation the
same chain of rewrites is not available: the statements being combined are stated at
definitionally equal but syntactically different spellings of the same objects, so every `rw`
reports that it cannot find a pattern the goal displays, and a term-mode application of a
*generic* lemma — which unifies up to definitional equality — is the only affordable route.
Keeping the lemma generic also keeps its hypotheses in the shape in which the existing statements
already are, so that no argument at an instantiation is a restatement; that is the condition
under which the instantiation fits the default heartbeat budget at all.

## Main results

* `Stacks.CategoryTheory.inv_comp_inv_comp_eq_of_comp_eq`: an equation of three-factor
  composites, solved for the two inverses on the left.
* `Stacks.CategoryTheory.comp_transport_of_factored`: **the composition law for a transport
  whose values factor through a second transport**, from the composition law for the second,
  the naturality of the second in the correcting factor, and a composition law for the
  corrections.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

/-- **An equation of three-factor composites, solved for the two inverses on the left.**  If
`u ≫ v ≫ w = c ≫ z` with `u`, `v` and `z` invertible, then `v⁻¹ ≫ u⁻¹ ≫ c = w ≫ z⁻¹`.

This is the shape in which a cocycle condition written with forward comparisons is consumed by a
transport written with their inverses. -/
public theorem inv_comp_inv_comp_eq_of_comp_eq {C : Type*} [Category* C] {X Y Z W V : C}
    (u : X ≅ Y) (v : Y ≅ Z) {w : Z ⟶ W} {c : X ⟶ V} (z : V ≅ W)
    (h : u.hom ≫ v.hom ≫ w = c ≫ z.hom) :
    v.inv ≫ u.inv ≫ c = w ≫ z.inv := by
  rw [(Iso.eq_comp_inv z).mpr h.symm]
  simp

/-- **A composition law for a transport whose values factor through a second transport.**

Let `L : D ⥤ E` and `Ψ : C ⥤ E` be functors and consider

* a morphism `Θq : X ⟶ Y` of `D` which factors as `a ≫ b`;
* a morphism `Θp : L.obj Y ⟶ Ψ.obj V` which factors as `e ≫ Ψ.map f`;
* a morphism `Θpq : Z ⟶ Ψ.obj W` which factors as `t ≫ Ψ.map d`.

Assume the naturality `L.map b ≫ e = e' ≫ Ψ.map g` of the second transport in the correcting
factor, a composition law `g ≫ f ≫ c = w ≫ d` for the corrections, and a composition law
`L.map a ≫ e' ≫ Ψ.map w = κ ≫ t` for the second transport.  Then the composition law for the
composite transport follows: `L.map Θq ≫ Θp ≫ Ψ.map c = κ ≫ Θpq`.

Every datum is a variable, so that each argument at an instantiation is an existing statement
applied verbatim; see the implementation notes above for why that is not optional. -/
public theorem comp_transport_of_factored {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (L : D ⥤ E) (Ψ : C ⥤ E) {X Y Y' : D} {Z : E} {U U' V W W' : C}
    {a : X ⟶ Y'} {b : Y' ⟶ Y} {Θq : X ⟶ Y}
    {e : L.obj Y ⟶ Ψ.obj U} {f : U ⟶ V} {Θp : L.obj Y ⟶ Ψ.obj V} {c : V ⟶ W}
    {e' : L.obj Y' ⟶ Ψ.obj U'} {g : U' ⟶ U} {w : U' ⟶ W'} {d : W' ⟶ W}
    {κ : L.obj X ⟶ Z} {t : Z ⟶ Ψ.obj W'} {Θpq : Z ⟶ Ψ.obj W}
    (hΘq : Θq = a ≫ b)
    (hΘp : Θp = e ≫ Ψ.map f)
    (hnat : L.map b ≫ e = e' ≫ Ψ.map g)
    (hcoc : g ≫ f ≫ c = w ≫ d)
    (hΘpq : Θpq = t ≫ Ψ.map d)
    (hfirst : L.map a ≫ e' ≫ Ψ.map w = κ ≫ t) :
    L.map Θq ≫ Θp ≫ Ψ.map c = κ ≫ Θpq := by
  subst hΘq hΘp hΘpq
  rw [L.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (L.map b), hnat]
  simp only [Category.assoc]
  rw [← Ψ.map_comp, ← Ψ.map_comp, hcoc, Ψ.map_comp, reassoc_of% hfirst]

end Stacks.CategoryTheory

end
