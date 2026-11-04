module

public import Mathlib.CategoryTheory.Whiskering
public import StacksFrontier.CategoryTheory.CompositeGluing

/-!
# The composition law for the canonical map of a square, generically

A commutative square of spaces gives rise to a canonical map of modules built from three data: a
comparison isomorphism `Φ` of the two composite inverse-image functors round the square, an
object `I` of the ambient's modules, and a map `a` out of its inverse image along the ambient
edge.  The map is `Φ.hom.app I ≫ p.map a`.

For two such squares stacked vertically there is a composition law: the map of the outer
rectangle is the comparison of the two vertical inverse images, followed by the inverse image of
the lower square's map, followed by the upper square's map.  This file proves that law **in a
generic category, with every functor, natural isomorphism, object and morphism a variable**, from
exactly two hypotheses — that the comparisons paste, and that the maps `a` compose.

## Why it is stated here rather than at its instance

The instance is the composition law of [Stacks Project, Tag 04G2] part (3) for
`AlgebraicGeometry.Space.conormalMapOfImmersions`, whose two hypotheses are proved as
`AlgebraicGeometry.Space.squarePullbackCompIso_paste` and
`AlgebraicGeometry.Space.kernelIdealSquareMap_comp`.  Assembled step by step there, in the way
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModuleCompositionLaw.lean` assembles the closed
case, **every arrangement is a kernel deterministic timeout** — the details are recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquarePieceMapCompositionLaw.lean`, and they
include a single application of `Stacks.CategoryTheory.map_comp_split` and the expansion of the
pasting at a *variable* module.  Each such intermediate statement presents the kernel with two
applications of `CategoryTheory.Functor.map`, or of `CategoryTheory.NatTrans.app`, whose implicit
objects are definitionally but not syntactically equal, and reducing those projections sends it
into the construction of the inverse image of modules on a small étale site by sheafification.
No attribute reaches the kernel, and splitting into more declarations does not help, because each
split introduces one more such statement.

Proved once at variables, the instantiation is free: Lean does not recheck a proved statement's
internal definitional equalities, and every hypothesis at the instantiation is an existing lemma
applied verbatim.  That last clause is the whole condition — an argument that is a *restatement*
of an existing lemma costs as much as the step it replaces.

## Main results

* `Stacks.CategoryTheory.squareMapPasteApp`: the pasting identity read at one object.
* `Stacks.CategoryTheory.square_map_comp`: **the composition law.**
* `Stacks.CategoryTheory.conjugate_comp_of`: the law carried across conjugating isomorphisms,
  with the conjugates and the leading comparison's naturality as variables.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory

universe v₁ v₂ v₃ w₁ w₂ w₃ u₁ u₂ u₃ t₁ t₂ t₃

variable {M₁ : Type u₁} {M₂ : Type u₂} {M₃ : Type u₃} {N₁ : Type t₁} {N₂ : Type t₂}
    {N₃ : Type t₃} [Category.{v₁} M₁] [Category.{v₂} M₂] [Category.{v₃} M₃]
    [Category.{w₁} N₁] [Category.{w₂} N₂] [Category.{w₃} N₃]
    (p₁ : N₁ ⥤ M₁) (p₂ : N₂ ⥤ M₂) (p₃ : N₃ ⥤ M₃)
    (q₁ : M₂ ⥤ M₁) (q₂ : M₃ ⥤ M₂) (q : M₃ ⥤ M₁)
    (r₁ : N₂ ⥤ N₁) (r₂ : N₃ ⥤ N₂) (r : N₃ ⥤ N₁)

/-- **The pasting identity of the three square comparisons, read at one object of the lowest
ambient.**  The four components are read off by
`CategoryTheory.Functor.whiskerLeft_app` and `CategoryTheory.Functor.whiskerRight_app`, each of
which holds by `rfl`.

It is a declaration of its own so that a consumer never has to expand the pasted natural
transformation itself; at the geometric instance that expansion is what the kernel cannot do. -/
theorem squareMapPasteApp (Φ₁ : p₂ ⋙ q₁ ≅ r₁ ⋙ p₁) (Φ₂ : p₃ ⋙ q₂ ≅ r₂ ⋙ p₂)
    (Φ : p₃ ⋙ q ≅ r ⋙ p₁) (κ : q₂ ⋙ q₁ ≅ q) (ρ : r₂ ⋙ r₁ ≅ r)
    (hpaste : Φ.hom ≫ Functor.whiskerRight ρ.inv p₁ =
      Functor.whiskerLeft p₃ κ.inv ≫ Functor.whiskerRight Φ₂.hom q₁ ≫
        Functor.whiskerLeft r₂ Φ₁.hom)
    (I₃ : N₃) :
    Φ.hom.app I₃ ≫ p₁.map (ρ.inv.app I₃) =
      κ.inv.app (p₃.obj I₃) ≫ q₁.map (Φ₂.hom.app I₃) ≫ Φ₁.hom.app (r₂.obj I₃) := by
  have h := NatTrans.congr_app hpaste I₃
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] using h

/-- **The composition law for the canonical map of a square, generically.**

`m`, `m₁` and `m₂` are the canonical maps of the outer rectangle, the upper square and the lower
square: each is its square's comparison isomorphism read at an object of the ambient, followed by
the inverse image along the left edge of a map out of that object's inverse image along the
bottom edge.  Given that the three comparisons paste (`hpaste`) and that the three maps of
ambient objects compose (`ha`), the map of the outer rectangle is the comparison `κ` of the two
vertical inverse images, followed by the inverse image along `q₁` of the lower square's map,
followed by the upper square's map.

The three canonical maps enter as variables with their factorisations as hypotheses, so that at
an instantiation nothing has to be restated: each of `hm`, `hm₁`, `hm₂`, `ha` and `hpaste` is an
existing equation applied verbatim. -/
theorem square_map_comp (Φ₁ : p₂ ⋙ q₁ ≅ r₁ ⋙ p₁) (Φ₂ : p₃ ⋙ q₂ ≅ r₂ ⋙ p₂)
    (Φ : p₃ ⋙ q ≅ r ⋙ p₁) (κ : q₂ ⋙ q₁ ≅ q) (ρ : r₂ ⋙ r₁ ≅ r)
    (hpaste : Φ.hom ≫ Functor.whiskerRight ρ.inv p₁ =
      Functor.whiskerLeft p₃ κ.inv ≫ Functor.whiskerRight Φ₂.hom q₁ ≫
        Functor.whiskerLeft r₂ Φ₁.hom)
    {I₁ : N₁} {I₂ : N₂} {I₃ : N₃} (a₁ : r₁.obj I₂ ⟶ I₁) (a₂ : r₂.obj I₃ ⟶ I₂)
    (a : r.obj I₃ ⟶ I₁) (ha : a = ρ.inv.app I₃ ≫ r₁.map a₂ ≫ a₁)
    {m : q.obj (p₃.obj I₃) ⟶ p₁.obj I₁} {m₁ : q₁.obj (p₂.obj I₂) ⟶ p₁.obj I₁}
    {m₂ : q₂.obj (p₃.obj I₃) ⟶ p₂.obj I₂}
    (hm : m = Φ.hom.app I₃ ≫ p₁.map a) (hm₁ : m₁ = Φ₁.hom.app I₂ ≫ p₁.map a₁)
    (hm₂ : m₂ = Φ₂.hom.app I₃ ≫ p₂.map a₂) :
    m = κ.inv.app (p₃.obj I₃) ≫ q₁.map m₂ ≫ m₁ := by
  have hp := squareMapPasteApp p₁ p₂ p₃ q₁ q₂ q r₁ r₂ r Φ₁ Φ₂ Φ κ ρ hpaste I₃
  have hnat : q₁.map (p₂.map a₂) ≫ Φ₁.hom.app I₂ =
      Φ₁.hom.app (r₂.obj I₃) ≫ p₁.map (r₁.map a₂) := Φ₁.hom.naturality a₂
  rw [hm, hm₁, hm₂, ha, p₁.map_comp, p₁.map_comp, q₁.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (Φ.hom.app I₃), hp]
  simp only [Category.assoc]
  rw [← Category.assoc (Φ₁.hom.app (r₂.obj I₃)), ← hnat]
  simp only [Category.assoc]

/-- **A composition law survives conjugation by isomorphisms, with the three conjugates and the
naturality of the leading comparison entering as variables.**  This is
`Stacks.CategoryTheory.conjugate_comp` with the three conjugated maps `c13`, `c23`, `c12` given
by hypotheses rather than written out in the conclusion, and with the naturality of the leading
comparison taken in the form *with a tail left free*.

Both shapes are forced by what a geometric instance has.  There the three conjugates are the
canonical maps and their three conjugation equations are existing lemmas; and the naturality
of the comparison of inverse images along a composite is proved only with a free tail, that being
the form in which no associativity has to be done at the instantiation.  So **no argument of this
lemma is a restatement** — which is the condition under which the instantiation costs nothing,
since Lean does not recheck a proved statement's internal definitional equalities.  Restating the
naturality without its tail is, as recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSquarePieceMapCompositionLaw.lean`, a `whnf`
timeout on its own, even when the restatement's only proof step is an existing generic lemma. -/
theorem conjugate_comp_of {X : Type u₁} {Y : Type u₂} [Category.{v₁} X] [Category.{v₂} Y]
    (F₁ : Y ⥤ X) {A3 B3 A2 B2 : Y} {A1 B1 : X} {P Q : X} (u : B3 ⟶ A3) (m23 : A3 ⟶ A2)
    (e2 : A2 ≅ B2) (m12 : F₁.obj A2 ⟶ A1) (e1 : A1 ≅ B1) (w : P ⟶ Q) (ξ : Q ⟶ F₁.obj A3)
    (ξ' : P ⟶ F₁.obj B3) (m13 : Q ⟶ A1) {c13 : P ⟶ B1} {c23 : B3 ⟶ B2}
    {c12 : F₁.obj B2 ⟶ B1}
    (hnat : ∀ {T : X} (t : F₁.obj A3 ⟶ T), w ≫ ξ ≫ t = ξ' ≫ F₁.map u ≫ t)
    (hm : m13 = ξ ≫ F₁.map m23 ≫ m12) (h13 : c13 = w ≫ m13 ≫ e1.hom)
    (h23 : c23 = u ≫ m23 ≫ e2.hom) (h12 : c12 = F₁.map e2.inv ≫ m12 ≫ e1.hom) :
    c13 = ξ' ≫ F₁.map c23 ≫ c12 := by
  have hcancel : F₁.map e2.hom ≫ F₁.map e2.inv = 𝟙 _ := by
    rw [← F₁.map_comp, Iso.hom_inv_id, F₁.map_id]
  rw [h13, h23, h12, hm, F₁.map_comp, F₁.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (F₁.map e2.hom), hcancel, Category.id_comp,
    ← hnat (F₁.map m23 ≫ m12 ≫ e1.hom)]

end Stacks.CategoryTheory

end
