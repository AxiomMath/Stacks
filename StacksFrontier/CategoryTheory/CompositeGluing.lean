module

public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Gluing a composite out of recorded equations

Bookkeeping lemmas for assembling an equation between two composites out of the equations a
consumer already has, in a *generic* category and for a *generic* functor.

Both are stated with every morphism supplied by the hypotheses rather than solved from the
conclusion. That is not a stylistic choice: at the geometric instantiations this development
reaches, the terms involved are not type-correct at `implicit` transparency — the Zariski
structure sheaf of a scheme is a `TopCat.Sheaf`, which is the sheaves on the topology of its
opens only up to an unfolding `rw` will not perform — so a tactic proof of the instance fails
where a single application of a generic lemma succeeds. The same effect is recorded for other
reasons in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatEquivalence` and in
`StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroTensorBifunctorial`.

## Main results

* `Stacks.CategoryTheory.map_square`: the image of a commuting square under one functor.
* `Stacks.CategoryTheory.comp_eq_comp_of_glue`: **an equation between two composites assembled
  from a factorisation of the first, a square relating the two routes, a square relating what
  remains, and a factorisation of the second.**
* `Stacks.CategoryTheory.eq_comp_of_comp_mono`: **the shape a composition law proved by
  cancelling a monomorphism takes** — the two composites with the monomorphism are matched
  through a common middle supplied by four equations.
* `Stacks.CategoryTheory.conjugate_comp`: **a composition law survives conjugation by
  isomorphisms** — if a map of an outer rectangle factors through the maps of the two squares, so
  do their conjugates, the middle pair of conjugating isomorphisms cancelling.
* `Stacks.CategoryTheory.map_comp_split` and
  `Stacks.CategoryTheory.comp_eq_of_split_and_square`: the two one-step reassociations a
  composition law is assembled from, each with the factorisation it uses as a hypothesis.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

/-- **The image of a commuting square under a functor is a commuting square.**  The square is a
hypothesis, so that no edge has to be solved from the conclusion. -/
theorem map_square {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {W X Y Z : C}
    {x : W ⟶ X} {y : X ⟶ Z} {z : W ⟶ Y} {t : Y ⟶ Z} (h : x ≫ y = z ≫ t) :
    F.map x ≫ F.map y = F.map z ≫ F.map t :=
  ((F.map_comp x y).symm.trans (congrArg F.map h)).trans (F.map_comp z t)

/-- **Two composites agree once the four steps relating them are recorded.**

`f ≫ s` is rewritten through a factorisation `s = a ≫ w` of its second factor, carried across a
square `f ≫ a = u ≫ m`, the remainder `m ≫ w` is replaced by `c ≫ d`, and the result is read
back through a factorisation `ξ = u ≫ c`. Every step is a hypothesis; nothing is unified. -/
theorem comp_eq_comp_of_glue {𝒳 : Type*} [Category 𝒳] {P A N Z C K : 𝒳} {f : P ⟶ A} {s : A ⟶ Z}
    {a : A ⟶ N} {w : N ⟶ Z} {u : P ⟶ C} {m : C ⟶ N} {c : C ⟶ K} {d : K ⟶ Z} {ξ : P ⟶ K}
    (hA : a ≫ w = s) (hC : f ≫ a = u ≫ m) (hmw : m ≫ w = c ≫ d) (hξ : ξ = u ≫ c) :
    f ≫ s = ξ ≫ d := by
  rw [← hA, ← Category.assoc, hC, Category.assoc, hmw, hξ, Category.assoc]

/-- **A composition law proved by cancelling a monomorphism.**

To identify `x` with `ξ ≫ y` it is enough, `m` being a monomorphism, to match `x ≫ m` with
`(ξ ≫ y) ≫ m`. The four hypotheses do that: `hL` reads `x ≫ m` as a composite through `s`, `hs`
factors `s`, `hnat` carries the result across to the route through `ξ`, and `hy` reads `y ≫ m`.

Everything is a hypothesis, including the monomorphism's cancellation, so that no step of the
instantiation is a `rw` on a geometric term. -/
theorem eq_comp_of_comp_mono {𝒳 : Type*} [Category 𝒳] {P Q U D E W : 𝒳} (m : Q ⟶ U) [Mono m]
    {x : P ⟶ Q} {ξ : P ⟶ E} {y : E ⟶ Q} {A : P ⟶ D} {s : D ⟶ U} {ξ' : D ⟶ W} {r : W ⟶ U}
    {X : E ⟶ W} (hL : x ≫ m = A ≫ s) (hs : s = ξ' ≫ r) (hnat : A ≫ ξ' ≫ r = ξ ≫ X ≫ r)
    (hy : y ≫ m = X ≫ r) : x = ξ ≫ y := by
  refine (cancel_mono m).mp ?_
  rw [hL, hs, hnat, Category.assoc, hy]

/-- **A composition law survives conjugation by isomorphisms.**

A canonical map of a commutative square is often presented as a map `m` between one pair of
objects conjugated by isomorphisms onto another pair. If the maps of two stacked squares satisfy
a composition law in the first presentation (`hm`), then so do their conjugates: the two
conjugating isomorphisms at the middle object cancel, and the leading comparison is moved across
by its naturality (`hnat`).

Only the functor `F₁` appears, the inner one entering through the morphism `u` — which at the
point of use is its image of the inverse of the third conjugating isomorphism. -/
theorem conjugate_comp {X Y : Type*} [Category X] [Category Y] (F₁ : Y ⥤ X)
    {A3 B3 A2 B2 : Y} {A1 B1 : X} {P Q : X} (u : B3 ⟶ A3) (m23 : A3 ⟶ A2) (e2 : A2 ≅ B2)
    (m12 : F₁.obj A2 ⟶ A1) (e1 : A1 ≅ B1) (w : P ⟶ Q) (ξ : Q ⟶ F₁.obj A3)
    (ξ' : P ⟶ F₁.obj B3) (m13 : Q ⟶ A1) (hnat : w ≫ ξ = ξ' ≫ F₁.map u)
    (hm : m13 = ξ ≫ F₁.map m23 ≫ m12) :
    w ≫ m13 ≫ e1.hom =
      ξ' ≫ F₁.map (u ≫ m23 ≫ e2.hom) ≫ (F₁.map e2.inv ≫ m12 ≫ e1.hom) := by
  have hcancel : F₁.map e2.hom ≫ F₁.map e2.inv = 𝟙 _ := by
    rw [← F₁.map_comp, Iso.hom_inv_id, F₁.map_id]
  rw [hm, F₁.map_comp, F₁.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (F₁.map e2.hom), hcancel, Category.id_comp, ← Category.assoc w, hnat]
  simp only [Category.assoc]

/-- **The image of a factored morphism, with the tail of the composite reassociated.**  The
factorisation is a hypothesis, so that at the instantiation nothing is restated: the hypothesis
is an existing equation applied verbatim and the conclusion's type comes from it. -/
theorem map_comp_split {X Y : Type*} [Category X] [Category Y] (F : Y ⥤ X) {P Q R : Y} {T : X}
    {m : P ⟶ R} {A : P ⟶ Q} {B : Q ⟶ R} (h : m = A ≫ B) (k : F.obj R ⟶ T) :
    F.map m ≫ k = F.map A ≫ F.map B ≫ k := by
  rw [h, F.map_comp, Category.assoc]

/-- **A factorisation of the second factor carried across a commuting square.**  Both the
factorisation and the square are hypotheses. -/
theorem comp_eq_of_split_and_square {X : Type*} [Category X] {P Q R V W : X} {a : P ⟶ Q}
    {m : Q ⟶ V} {A : Q ⟶ R} {B : R ⟶ V} {A' : P ⟶ W} {B' : W ⟶ R} (h : m = A ≫ B)
    (hsq : a ≫ A = A' ≫ B') : a ≫ m = A' ≫ B' ≫ B := by
  rw [h, ← Category.assoc, hsq, Category.assoc]

end Stacks.CategoryTheory

end
