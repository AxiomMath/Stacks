module

public import Mathlib.CategoryTheory.Functor.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Cancelling and replacing segments of a composite

Long chases in this library are written as equalities between composites of many morphisms, and
each step rewrites one segment. The statements below are the segment rewrites that recur: a
two-fold segment that composes to the identity is cancelled, and a prefix known to equal a single
morphism is replaced by it.

They are stated at a variable category and proved by `Category.assoc` and the unit laws, so they
are available wherever the chase happens to live. The point of having them as declarations rather
than as `rw` steps inside each proof is that the concrete composites in question are large enough
that a rewrite on the goal does not always find its pattern — the same reason the neighbouring
`StacksFrontier.CategoryTheory.EqToHomAbsorption` exists.

This module is a leaf: it imports Mathlib and the tag attribute and nothing else, so it can be
imported from anywhere in the library without pulling in a subject matter.

## Main results

* `CategoryTheory.comp_cancel_id`: a two-fold segment composing to the identity is cancelled off
  the front of a composite.
* `CategoryTheory.comp₃_prefix_eq`: a three-fold prefix known to equal one morphism is replaced
  by it.
* `CategoryTheory.map_comp_cancel`: a functor's image of a pair composing to the identity composes
  to the identity.
* `CategoryTheory.map_comp₄`: a functor's image of a four-fold composite, split into four.
* `CategoryTheory.comp_square_cancel`: **the segment rewrite a square of two comparisons reduces
  to.** Each of the two paths carries a conjugating pair composing to the identity; with the two
  paths' heads identified (`key`) and the segment between the two conjugations identified
  (`core`), the two paths agree.
* `CategoryTheory.comp_conj_cancel_square`: **the segment rewrite a square of two comparisons
  reduces to when only one path carries a conjugation.** One path is a three-fold composite whose
  last factor is cancelled by the first factor of what follows it; the other path's head and the
  segment after it are each identified by a commuting square.
* `CategoryTheory.map_comp₃_cancel_mid`: the same for a path lying inside a functor's image: a
  functor's three-fold composite followed by its image of a right inverse of the third factor,
  with the two middle factors recombined by a hypothesis.
* `CategoryTheory.comp_glue_two_squares`: **two squares glued along one shared morphism.** One
  contracts a path's two leading factors into the morphism both squares are stated at; the other
  identifies what follows with the second path.
* `CategoryTheory.comp_glue_mid_square`: **one path's middle factor replaced, up to a
  conjugation.** The replacement is a square; the conjugation is a pair composing to the identity.
* `CategoryTheory.comp_glue_three_squares`: **three squares glued along two shared morphisms.**
  Two of them identify a prefix and a suffix of one path with the other path's; the third
  replaces the other path's middle factor, up to a conjugation given as a pair composing to the
  identity. This is the shape three instantiations of one comparison compose in.
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- **A two-fold segment composing to the identity is cancelled off the front of a composite.**
`Category.id_comp` cannot match here: the left factor is not syntactically `𝟙`, it is a composite
known to equal it. -/
theorem comp_cancel_id {X Y W : C} {a : X ⟶ Y} {b : Y ⟶ X} (h : a ≫ b = 𝟙 X) (r : X ⟶ W) :
    a ≫ b ≫ r = r := by
  rw [← Category.assoc, h, Category.id_comp]

/-- **A three-fold prefix known to equal a single morphism is replaced by it.** The hypothesis is
stated on the prefix alone so that the tail `r` is untouched, which is what lets a chase rewrite
one segment at a time. -/
theorem comp₃_prefix_eq {X Y Z Y' W : C} (a : X ⟶ Y) (b : Y ⟶ Z) (m : Z ⟶ Y') {n : X ⟶ Y'}
    (h : a ≫ b ≫ m = n) (r : Y' ⟶ W) : a ≫ b ≫ m ≫ r = n ≫ r := by
  rw [← h, Category.assoc, Category.assoc]

/-- **A functor carries a pair composing to the identity to a pair composing to the identity.**
Stated as a term and with the cancellation given on plain morphisms rather than on an `Iso`, so
that the components of a natural isomorphism it is applied to keep their own spelling and the
identity's object is checked at default transparency — which is what lets it fire across two
definitionally equal spellings of one category. -/
theorem map_comp_cancel {D : Type*} [Category D] (G : C ⥤ D) {X Y : C} {a : X ⟶ Y} {b : Y ⟶ X}
    (h : a ≫ b = 𝟙 X) : G.map a ≫ G.map b = 𝟙 (G.obj X) :=
  (G.map_comp _ _).symm.trans ((congrArg G.map h).trans (G.map_id X))

/-- **A functor's image of a four-fold composite, split into four.** `Functor.map_comp` splits one
factor at a time and leaves the result right-associated after each step, so a chase that needs all
four factors separated pays three rewrites; this is the one statement. Stated at a variable
category and applied as a term, so that the four morphisms keep their own spellings and the three
intermediate objects are checked at default transparency. -/
theorem map_comp₄ {D : Type*} [Category D] (G : C ⥤ D) {X Y Z T T' : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    (c : Z ⟶ T) (d : T ⟶ T') :
    G.map (a ≫ b ≫ c ≫ d) = G.map a ≫ G.map b ≫ G.map c ≫ G.map d := by
  rw [G.map_comp, G.map_comp, G.map_comp]

/-- **The segment rewrite a square of two comparisons reduces to.** Both paths of such a square
run from one object to another through a comparison that is read off a chosen resolution, so each
carries a conjugating pair `v`, `w` (respectively `v'`, `w'`) composing to the identity, and the
two paths' tails `t` agree. Given

* `key`, the identification of the two paths' heads, and
* `core`, the identification of the segment between the two conjugations,

the two paths agree. The conjugations are given as plain morphisms with their composition law as a
hypothesis rather than as an `Iso`, so that the components of whatever isomorphism a caller has
keep their own spelling. -/
theorem comp_square_cancel {A₀ A₁ A₂ A₃ A₄ A₅ A₆ B₁ B₂ B₃ B₄ B₅ : C}
    {ph : A₀ ⟶ A₁} {gm : A₁ ⟶ A₂} {u : A₂ ⟶ A₃} {v : A₃ ⟶ A₄} {w : A₄ ⟶ A₃} {he : A₃ ⟶ A₅}
    (t : A₅ ⟶ A₆) {pj : A₀ ⟶ B₁} {k₁ : B₁ ⟶ B₄} {k₂ : B₄ ⟶ B₅} {k₃ : B₅ ⟶ A₂}
    {u' : B₁ ⟶ B₂} {v' : B₂ ⟶ B₃} {w' : B₃ ⟶ B₂}
    {hc : B₂ ⟶ A₅} (hvw : v ≫ w = 𝟙 A₃) (hv'w' : v' ≫ w' = 𝟙 B₂)
    (key : ph ≫ gm = pj ≫ k₁ ≫ k₂ ≫ k₃) (core : k₁ ≫ k₂ ≫ k₃ ≫ u ≫ he = u' ≫ hc) :
    ph ≫ (gm ≫ u ≫ v) ≫ w ≫ he ≫ t = (pj ≫ u' ≫ v') ≫ w' ≫ hc ≫ t := by
  have e3 := congrArg (fun m => m ≫ t) core
  simp only [Category.assoc] at e3 ⊢
  rw [comp_cancel_id hvw, comp_cancel_id hv'w', ← Category.assoc ph gm, key]
  simp only [Category.assoc]
  rw [e3]

/-- **The segment rewrite a square of two comparisons reduces to when only one of the two paths
carries a conjugation.** One path reads a comparison off a chosen resolution and so ends in a
factor `c` whose right inverse `c'` opens the segment that follows it; the other path is a plain
composite. Given

* `hnat`, the identification of the two paths' heads — a commuting square `f ≫ a' = a ≫ g` — and
* `hsq`, the identification of the segment after them — `g ≫ b' = b ≫ d` —

the two paths agree. The conjugation is given as a pair of plain morphisms with its composition
law as a hypothesis rather than as an `Iso`, and the three intermediate objects are variables, so
that the morphisms a caller supplies keep their own spellings and the objects between them are
checked at default transparency. -/
theorem comp_conj_cancel_square {A₀ A₁ A₂ A₃ A₄ A₅ B₁ B₂ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {c' : A₃ ⟶ A₂} {d : A₂ ⟶ A₄} {e : A₄ ⟶ A₅}
    {f : A₀ ⟶ B₁} {a' : B₁ ⟶ B₂} {b' : B₂ ⟶ A₄} {g : A₁ ⟶ B₂}
    (hcc' : c ≫ c' = 𝟙 A₂) (hnat : f ≫ a' = a ≫ g) (hsq : g ≫ b' = b ≫ d) :
    (a ≫ b ≫ c) ≫ c' ≫ d ≫ e = f ≫ a' ≫ b' ≫ e := by
  simp only [Category.assoc]
  rw [comp_cancel_id hcc', ← Category.assoc b d e, ← hsq]
  simp only [Category.assoc]
  rw [← Category.assoc a g, ← hnat]
  simp only [Category.assoc]

/-- **The same segment rewrite for a path lying inside a functor's image.** The path is the image
under `R` of a three-fold composite `a ≫ b ≫ c`, followed by `R`'s image of a right inverse `c'`
of `c` and then by a tail; `hbb` recombines `R.map b` with the factor after the cancellation into
the single morphism `bb` the other path carries. Stated at variable categories and applied as a
term, so that the cancellation's object is checked at default transparency. -/
theorem map_comp₃_cancel_mid {D : Type*} [Category D] (R : C ⥤ D) {X Y Z W : C} {V U : D}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : Z ⟶ W) (c' : W ⟶ Z) (hcc' : c ≫ c' = 𝟙 Z)
    {m : R.obj Z ⟶ V} {bb : R.obj Y ⟶ V} (hbb : R.map b ≫ m = bb) (e : V ⟶ U) :
    R.map (a ≫ b ≫ c) ≫ R.map c' ≫ m ≫ e = R.map a ≫ bb ≫ e := by
  rw [← hbb, R.map_comp, R.map_comp]
  simp only [Category.assoc]
  rw [comp_cancel_id (map_comp_cancel R hcc')]

/-- **Two squares glued along one shared morphism.** Let one path be `c ≫ s ≫ e` and the other
`m ≫ a ≫ t`. Given `hc`, which contracts the first path's two leading factors into a single
morphism `r`, and `hs`, the square identifying `r ≫ e` with the second path, the two paths agree.

Every intermediate object is a variable, so that a caller's morphisms keep their own spellings and
the objects between them are checked at default transparency — the reason the rest of this module
exists, and here also a concrete cost: at the concrete composites of [Stacks, Tag 0EX3] (c) the
same two steps written as a `congrArg` on the goal exhaust 200,000 heartbeats. -/
theorem comp_glue_two_squares {A₀ A₁ A₂ A₃ B₀ B₁ : C}
    {c : A₀ ⟶ A₁} {s : A₁ ⟶ A₂} {r : A₀ ⟶ A₂} {e : A₂ ⟶ A₃}
    {m : A₀ ⟶ B₀} {a : B₀ ⟶ B₁} {t : B₁ ⟶ A₃}
    (hc : c ≫ s = r) (hs : m ≫ a ≫ t = r ≫ e) :
    c ≫ s ≫ e = m ≫ a ≫ t := by
  rw [← Category.assoc c s e, hc, hs]

/-- **One path's middle factor replaced, up to a conjugation.** Given a path `u` already known to
be `m ≫ a ≫ t`, a square `hn` replacing `a` by `A ≫ ρ` after the morphism `i`, and a left inverse
`j` of `i`, the path is `m ≫ j ≫ A ≫ ρ ≫ t`.

Split off from `comp_glue_three_squares` because at the concrete composites of
[Stacks, Tag 0EX3] (c) the three squares cannot be applied inside one declaration — the
instantiations together exhaust 200,000 heartbeats — so each is proved separately and this is the
step that joins the last one on. -/
theorem comp_glue_mid_square {A₀ A₃ B₀ B₁ D₀ D₁ : C} {u : A₀ ⟶ A₃}
    {m : A₀ ⟶ B₀} {a : B₀ ⟶ B₁} {t : B₁ ⟶ A₃}
    {i : D₀ ⟶ B₀} {j : B₀ ⟶ D₀} {A : D₀ ⟶ D₁} {ρ : D₁ ⟶ B₁}
    (hu : u = m ≫ a ≫ t) (hn : A ≫ ρ = i ≫ a) (hji : j ≫ i = 𝟙 B₀) :
    u = m ≫ j ≫ A ≫ ρ ≫ t := by
  have ha : j ≫ A ≫ ρ = a := by
    rw [hn, comp_cancel_id hji]
  rw [hu, ← Category.assoc j A, ← Category.assoc (j ≫ A) ρ t, Category.assoc j A ρ, ha]

/-- **Three squares glued along two shared morphisms.** Let one path be `c ≫ s ≫ e` and the other
`m ≫ j ≫ A ≫ ρ ≫ t`. Given

* `hc`, which contracts the first path's two leading factors into a single morphism `r` — the
  comparison both remaining squares are stated at;
* `hs`, the square identifying `r ≫ e` with `m ≫ a ≫ t`, where `a` is the second path's middle
  factor in the spelling that square carries; and
* `hn` together with `hji`, the square replacing `a` by `A ≫ ρ` up to the conjugating pair
  `(j, i)`, whose composite is the identity,

the two paths agree. The conjugation is a pair of plain morphisms with its composition law as a
hypothesis rather than an `Iso`, and every intermediate object is a variable, so that a caller's
morphisms keep their own spellings and the objects between them are checked at default
transparency — the reason the rest of this module exists. -/
theorem comp_glue_three_squares {A₀ A₁ A₂ A₃ B₀ B₁ D₀ D₁ : C}
    {c : A₀ ⟶ A₁} {s : A₁ ⟶ A₂} {r : A₀ ⟶ A₂} {e : A₂ ⟶ A₃}
    {m : A₀ ⟶ B₀} {a : B₀ ⟶ B₁} {t : B₁ ⟶ A₃}
    {i : D₀ ⟶ B₀} {j : B₀ ⟶ D₀} {A : D₀ ⟶ D₁} {ρ : D₁ ⟶ B₁}
    (hc : c ≫ s = r) (hs : m ≫ a ≫ t = r ≫ e) (hn : A ≫ ρ = i ≫ a)
    (hji : j ≫ i = 𝟙 B₀) :
    c ≫ s ≫ e = m ≫ j ≫ A ≫ ρ ≫ t :=
  comp_glue_mid_square (comp_glue_two_squares hc hs) hn hji

end CategoryTheory

end
