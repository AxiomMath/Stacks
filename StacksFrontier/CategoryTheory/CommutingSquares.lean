module

public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Gluing two commuting squares along a shared edge

Two commuting squares which share an edge glue to a commuting square. The two lemmas here
differ only in how the composite of the two edges away from the shared one is bracketed, which
is what makes each usable without a reassociation at the point of use.

## Main results

* `CategoryTheory.square_comp'`: the gluing with the composite bracketed to the right.
* `CategoryTheory.square_comp`: the gluing with the composite bracketed to the left.
* `CategoryTheory.square_comp₃`: the same for three commuting squares in a row.
* `CategoryTheory.map_map_comp_assoc`: a composite carried through two functors in turn and
  followed by two further morphisms splits off its first factor on the left.
* `CategoryTheory.square_of_factorizations`: a commuting square assembled from a factorization
  of each of its two sides and a square between the first factors.
* `CategoryTheory.square_of_functor_factorizations`: the same for a square whose top edge is the
  image under a functor of a *three*-factor composite and whose bottom edge is a three-factor
  composite, with both factorizations and all three constituent squares supplied as hypotheses.
* `CategoryTheory.square_of_functor_factorizations₂`: its two-group form, for a chain with only
  two places where a vertical may be named.
* `CategoryTheory.map_comp_naturality`, `CategoryTheory.comp_symm_naturality`,
  `CategoryTheory.naturality_transport`, `CategoryTheory.NatTrans.app_eq_of_iso`: naturality
  squares stated with every object and morphism a variable, so that each is applied by one
  unification.
-/

@[expose] public section

namespace CategoryTheory

/-- Two commuting squares sharing an edge glue to a commuting square, with the composite of
the two bottom edges bracketed to the right. -/
lemma square_comp' {C : Type*} [Category C] {P P' Q Q' R R' : C}
    {f : P ⟶ P'} {g : Q ⟶ Q'} {k : R ⟶ R'}
    {u : P ⟶ Q} {u' : P' ⟶ Q'} {v : Q ⟶ R} {v' : Q' ⟶ R'}
    (h₁ : f ≫ u' = u ≫ g) (h₂ : g ≫ v' = v ≫ k) :
    f ≫ u' ≫ v' = u ≫ v ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- Two commuting squares sharing an edge glue to a commuting square, with the composite of
the two bottom edges bracketed to the left. -/
lemma square_comp {C : Type*} [Category C] {P P' Q Q' R R' : C}
    {f : P ⟶ P'} {g : Q ⟶ Q'} {k : R ⟶ R'}
    {u : P ⟶ Q} {u' : P' ⟶ Q'} {v : Q ⟶ R} {v' : Q' ⟶ R'}
    (h₁ : f ≫ u' = u ≫ g) (h₂ : g ≫ v' = v ≫ k) :
    f ≫ u' ≫ v' = (u ≫ v) ≫ k := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Three commuting squares in a row glue to a commuting square, with the composite of the three
bottom edges bracketed to the right and that of the three top edges bracketed to the left of the
last vertical edge. -/
lemma square_comp₃ {C : Type*} [Category C] {P P' Q Q' R R' T T' : C}
    {f : P ⟶ P'} {g : Q ⟶ Q'} {k : R ⟶ R'} {l : T ⟶ T'}
    {u : P ⟶ Q} {u' : P' ⟶ Q'} {v : Q ⟶ R} {v' : Q' ⟶ R'} {w : R ⟶ T} {w' : R' ⟶ T'}
    (h₁ : f ≫ u' = u ≫ g) (h₂ : g ≫ v' = v ≫ k) (h₃ : k ≫ w' = w ≫ l) :
    f ≫ u' ≫ v' ≫ w' = (u ≫ v ≫ w) ≫ l := by
  rw [Category.assoc, Category.assoc, ← Category.assoc f u', h₁, Category.assoc,
    ← Category.assoc g v', h₂, Category.assoc, h₃]

/-- **Peeling the first factor out of a two-step direct image of a composite.**  A composite
`a ≫ b` carried through two functors in turn and followed by two further morphisms splits off its
first factor, carried through the same two functors, on the left.

Every category, functor, object and morphism is a variable, so a consumer at a concrete tower of
module categories applies this by one unification and never reassociates there:
`CategoryTheory.Category.assoc` with metavariable arguments exhausts the heartbeat budget at
`whnf` on the two spellings of the modules on the small étale site of a represented algebraic
space, which carry different `CategoryTheory.Category`-instance paths. -/
lemma map_map_comp_assoc {C D E : Type*} [Category C] [Category D] [Category E]
    (G₁ : C ⥤ D) (G₂ : D ⥤ E) {X Y Z : C} {W : D} {T : E}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : G₁.obj Z ⟶ W) (d : G₂.obj W ⟶ T) :
    G₂.map (G₁.map (a ≫ b) ≫ c) ≫ d =
      G₂.map (G₁.map a) ≫ G₂.map (G₁.map b ≫ c) ≫ d := by
  rw [G₁.map_comp, Category.assoc, G₂.map_comp, Category.assoc]

/-- **A commuting square assembled from a factorization of each of its two sides and a square
between the first factors.**  Suppose the left side `a` factors as `a₁ ≫ a₂`, the right side `e'`
factors as `a₁' ≫ e`, the second factor `a₂` carries the top edge `t` to `d ≫ e`, and the first
factors sit in a square `a₁ ≫ d = d' ≫ a₁'`.  Then `a ≫ t = d' ≫ e'`.

This is the assembler for a naturality square whose two sides are *composites*: each
factorization is supplied as an equation rather than rewritten into the goal, so that no
reassociation happens at the point of use.  That is what makes it usable when the two sides live
at two definitionally equal but syntactically different spellings of one category, where
`rw [Category.assoc]` cannot match while this lemma still applies. -/
lemma square_of_factorizations {C : Type*} [Category C] {A₀ A₁ A₂ B₀ B₁ D₀ : C}
    {a : A₀ ⟶ A₂} {a₁ : A₀ ⟶ A₁} {a₂ : A₁ ⟶ A₂} (h₀ : a = a₁ ≫ a₂)
    {t : A₂ ⟶ B₁} {d : A₁ ⟶ B₀} {e : B₀ ⟶ B₁} (h₁ : a₂ ≫ t = d ≫ e)
    {d' : A₀ ⟶ D₀} {a₁' : D₀ ⟶ B₀} (h₂ : a₁ ≫ d = d' ≫ a₁')
    {e' : D₀ ⟶ B₁} (h₃ : e' = a₁' ≫ e) :
    a ≫ t = d' ≫ e' := by
  rw [h₀, Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc, h₃]

/-- **The assembler for a naturality square whose two sides are three-factor composites, with
the three constituent squares already pasted.**  Let `H` factor as `h ≫ m ≫ f`, let `H'` factor
as `h' ≫ m' ≫ f'`, and let the pasting of the three constituent squares be given as the single
equation `s`.  Then `F.map H` and `H'` form a square with `v₀` and `v₃`.

This is the form to reach for when the chain's factors are large concrete terms.
`CategoryTheory.square_of_functor_factorizations` takes the three squares separately and is
therefore obliged to solve for two adjacent verticals at once while matching the first of them;
here the two middle verticals do not appear at all, because the pasting has already cancelled
them, and `s` is matched against a shape that `hH` and `hH'` have determined completely.  The
caller supplies `s` as `CategoryTheory.square_comp' s₁.symm (square_comp' s₂.symm s₃.symm)`,
where each `square_comp'` shares its middle vertical with its neighbour as the *same term*, so
nothing is solved for there either.

`CategoryTheory.Functor.map_comp` is distributed over the factorization here rather than at the
point of use, which is what keeps the concrete composite from ever being written out. -/
lemma square_of_functor_factorizations_of_paste {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A₀ A₁ A₂ A₃ : C} {H : A₀ ⟶ A₃} {h : A₀ ⟶ A₁} {m : A₁ ⟶ A₂} {f : A₂ ⟶ A₃}
    (hH : H = h ≫ m ≫ f)
    {B₀ B₁ B₂ B₃ : D} {H' : B₀ ⟶ B₃} {h' : B₀ ⟶ B₁} {m' : B₁ ⟶ B₂} {f' : B₂ ⟶ B₃}
    (hH' : H' = h' ≫ m' ≫ f')
    {v₀ : F.obj A₀ ⟶ B₀} {v₃ : F.obj A₃ ⟶ B₃}
    (s : v₀ ≫ h' ≫ m' ≫ f' = F.map h ≫ F.map m ≫ F.map f ≫ v₃) :
    F.map H ≫ v₃ = v₀ ≫ H' := by
  subst hH
  subst hH'
  rw [F.map_comp, F.map_comp, Category.assoc, Category.assoc]
  exact s.symm

/-- **The assembler for a naturality square whose two sides are three-factor composites that must
never be written out.**  Let `H` factor as `h ≫ m ≫ f`, let `H'` factor as `h' ≫ m' ≫ f'`, and
let `v₀`, `v₁`, `v₂`, `v₃` run from the `F`-images of the objects of the first factorization to
the objects of the second, so that each consecutive pair forms a square with the corresponding
factors.  Then `F.map H` and `H'` form a square with `v₀` and `v₃`.

Everything here is a *variable*: both factorizations arrive as equations and each of the three
constituent squares as a hypothesis, so the only composites the proof forms are composites of
variables, and `CategoryTheory.Functor.map_comp` is distributed over the factorization here
rather than at the point of use.  That is what makes this applicable when the three factors of
`H` are stated at two definitionally equal but syntactically *different* spellings of one
category — where neither `rw [Category.assoc]` nor `rw [F.map_comp]` can be made to fire on the
concrete composite, and where writing the composite out at either spelling asks the kernel to
identify the two underneath a category instance.

The equations are oriented `top ≫ right = left ≫ bottom`, which is the orientation of the
squares this is meant to paste; `CategoryTheory.square_comp'`, which does the pasting, has them
the other way round, and the type of an equation of morphisms is the type of whichever side
elaborated first, so the orientation is not cosmetic.

On a chain whose factors are large concrete terms, prefer
`CategoryTheory.square_of_functor_factorizations_of_paste` and paste the three squares with
`CategoryTheory.square_comp'` at the point of use: this form has to solve for `v₀` and `v₁`
*simultaneously* while matching `s₁`, and that is a `whnf` timeout on the chain of
[Stacks Project, Tag 04AM]'s source comparison, where the pre-pasted form goes through. -/
lemma square_of_functor_factorizations {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A₀ A₁ A₂ A₃ : C} {H : A₀ ⟶ A₃} {h : A₀ ⟶ A₁} {m : A₁ ⟶ A₂} {f : A₂ ⟶ A₃}
    (hH : H = h ≫ m ≫ f)
    {B₀ B₁ B₂ B₃ : D} {H' : B₀ ⟶ B₃} {h' : B₀ ⟶ B₁} {m' : B₁ ⟶ B₂} {f' : B₂ ⟶ B₃}
    (hH' : H' = h' ≫ m' ≫ f')
    {v₀ : F.obj A₀ ⟶ B₀} {v₁ : F.obj A₁ ⟶ B₁} {v₂ : F.obj A₂ ⟶ B₂} {v₃ : F.obj A₃ ⟶ B₃}
    (s₁ : F.map h ≫ v₁ = v₀ ≫ h') (s₂ : F.map m ≫ v₂ = v₁ ≫ m')
    (s₃ : F.map f ≫ v₃ = v₂ ≫ f') :
    F.map H ≫ v₃ = v₀ ≫ H' :=
  square_of_functor_factorizations_of_paste F hH hH'
    (square_comp' s₁.symm (square_comp' s₂.symm s₃.symm))

/-- **The two-group form of `CategoryTheory.square_of_functor_factorizations`.**  Let `H` factor
as `h ≫ m` and `H'` as `h' ≫ m'`, and let the two halves sit in squares with `v₀`, `v₁`, `v₂`.
Then `F.map H` and `H'` form a square with `v₀` and `v₂`.

This is the form to reach for when the chain has three factors but only *two* places where a
vertical may be named.  Grouping the last two factors together removes the vertical between them
from the statement, and with it the obligation to solve for an object that the two factors spell
differently — which is what makes the three-group form unusable on a chain whose factors live at
two definitionally equal but syntactically different spellings of one category. -/
lemma square_of_functor_factorizations₂ {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A₀ A₁ A₂ : C} {H : A₀ ⟶ A₂} {h : A₀ ⟶ A₁} {m : A₁ ⟶ A₂} (hH : H = h ≫ m)
    {B₀ B₁ B₂ : D} {H' : B₀ ⟶ B₂} {h' : B₀ ⟶ B₁} {m' : B₁ ⟶ B₂} (hH' : H' = h' ≫ m')
    {v₀ : F.obj A₀ ⟶ B₀} {v₁ : F.obj A₁ ⟶ B₁} {v₂ : F.obj A₂ ⟶ B₂}
    (s₁ : F.map h ≫ v₁ = v₀ ≫ h') (s₂ : F.map m ≫ v₂ = v₁ ≫ m') :
    F.map H ≫ v₂ = v₀ ≫ H' := by
  subst hH
  subst hH'
  rw [F.map_comp, Category.assoc]
  exact (square_comp' s₁.symm s₂.symm).symm

/-- A naturality square for a composite of the form `F.map f ≫ ψ`.  Every category, functor and
object is a variable, so applying it is a single unification. -/
lemma map_comp_naturality {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z W : C} {P P' : D} (m : X ⟶ Y) (g : Y ⟶ Z) (f : X ⟶ W) (t : W ⟶ Z)
    (φ : F.obj Z ⟶ P) (ψ : F.obj W ⟶ P') (τ : P' ⟶ P)
    (h₁ : m ≫ g = f ≫ t) (h₂ : F.map t ≫ φ = ψ ≫ τ) :
    F.map m ≫ (F.map g ≫ φ) = (F.map f ≫ ψ) ≫ τ := by
  rw [← Category.assoc, ← F.map_comp, h₁, F.map_comp, Category.assoc, h₂]
  exact (Category.assoc _ _ _).symm

/-- A commuting square for two isomorphisms gives one for their inverses. -/
private lemma inv_comp_eq_of_comp_hom_eq {C : Type*} [Category C] {A₁ A₂ B₁ B₂ : C}
    (p : A₁ ≅ B₁) (q : A₂ ≅ B₂) {m : A₁ ⟶ A₂} {m' : B₁ ⟶ B₂}
    (h : m ≫ q.hom = p.hom ≫ m') : p.inv ≫ m = m' ≫ q.inv := by
  rw [p.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Two legs into one object, each natural, compose to a natural isomorphism.  Every object and
morphism is a variable, so the square is closed by one unification. -/
lemma comp_symm_naturality {C : Type*} [Category C] {X Y Z X' Y' Z' : C}
    (lf : X ≅ Z) (rf : Y ≅ Z) (lf' : X' ≅ Z') (rf' : Y' ≅ Z')
    (u : X ⟶ X') (v : Y ⟶ Y') (w : Z ⟶ Z')
    (hl : u ≫ lf'.hom = lf.hom ≫ w) (hr : v ≫ rf'.hom = rf.hom ≫ w) :
    u ≫ (lf' ≪≫ rf'.symm).hom = (lf ≪≫ rf.symm).hom ≫ v := by
  have h := inv_comp_eq_of_comp_hom_eq rf rf' hr
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hl, Category.assoc, ← h, ← Category.assoc]

/-- Conjugating an isomorphism of values by isomorphisms of the objects preserves a naturality
square. -/
lemma naturality_transport {C D : Type*} [Category C] [Category D] (F G : C ⥤ D)
    {Z₁ Z₂ Z₁' Z₂' : C} (e₁ : Z₁ ≅ Z₁') (e₂ : Z₂ ≅ Z₂')
    (x : F.obj Z₁' ≅ G.obj Z₁') (y : F.obj Z₂' ≅ G.obj Z₂')
    (u : Z₁ ⟶ Z₂) (v : Z₁' ⟶ Z₂') (hu : u ≫ e₂.hom = e₁.hom ≫ v)
    (hv : F.map v ≫ y.hom = x.hom ≫ G.map v) :
    F.map u ≫ (F.mapIso e₂ ≪≫ y ≪≫ (G.mapIso e₂).symm).hom =
      (F.mapIso e₁ ≪≫ x ≪≫ (G.mapIso e₁).symm).hom ≫ G.map u := by
  have hui := inv_comp_eq_of_comp_hom_eq e₁ e₂ hu
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, hu, F.map_comp_assoc, reassoc_of% hv, ← G.map_comp, ← G.map_comp, hui]

/-- Two natural transformations agree at an object as soon as they agree at an isomorphic one:
the isomorphism of objects is carried across by naturality. -/
lemma NatTrans.app_eq_of_iso {C E : Type*} [Category C] [Category E] {A B : C ⥤ E}
    (α β : A ⟶ B) {Z Z' : C} (e : Z ≅ Z') (h : α.app Z' = β.app Z') :
    α.app Z = β.app Z := by
  apply (cancel_mono (B.mapIso e).hom).1
  change α.app Z ≫ B.map e.hom = β.app Z ≫ B.map e.hom
  rw [← α.naturality, ← β.naturality, h]

/-- A functor carries a commuting square to a commuting square. -/
lemma square_map {C : Type*} [Category C] {D : Type*} [Category D] (H : C ⥤ D)
    {A₁ A₂ B₁ B₂ : C} (p : A₁ ≅ B₁) (q : A₂ ≅ B₂) (m : A₁ ⟶ A₂) (m' : B₁ ⟶ B₂)
    (h : m ≫ q.hom = p.hom ≫ m') :
    H.map m ≫ (H.mapIso q).hom = (H.mapIso p).hom ≫ H.map m' := by
  rw [Functor.mapIso_hom, Functor.mapIso_hom, ← H.map_comp, h, H.map_comp]

/-- A commuting square for the inverses of two isomorphisms is one for the isomorphisms. -/
lemma square_of_inv {C : Type*} [Category C] {A₁ A₂ B₁ B₂ : C} (p : A₁ ≅ B₁) (q : A₂ ≅ B₂)
    (m : A₁ ⟶ A₂) (m' : B₁ ⟶ B₂) (h : p.inv ≫ m = m' ≫ q.inv) :
    m ≫ q.hom = p.hom ≫ m' := by
  rw [p.inv_comp_eq.1 h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory

end
