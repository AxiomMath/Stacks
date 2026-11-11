module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# The explicit 2-fibre product of categories is a 2-fibre product (Stacks 02X9)

Fix functors `F : A ⥤ C` and `G : B ⥤ C`. Mathlib's `CategoryTheory.Limits.CategoricalPullback`
is the category of triples `(a, b, φ)` with `φ : F a ≅ G b`, and this file shows that it is, with
its two projections and its tautological filler, a 2-fibre product of `F` and `G` in the sense of
Stacks 003Q: a final object of the 2-category of 2-commutative squares over the cospan in the
bicategory `Cat`, and in particular a terminal object of its quotient category. Consequently the
functor comparing a 2-cartesian square of categories with the
explicit construction is an equivalence.

## Main definitions

* `CategoryTheory.Cat.categoricalPullbackSq`: the explicit 2-fibre product as a 2-commutative
  square.
* `CategoryTheory.Cat.toCategoricalPullbackFunctor`: the functor comparing a 2-commutative square
  of categories with the explicit 2-fibre product, sending `x` to `(fst x, snd x, φ_x)`.

## Main results

* `CategoryTheory.Cat.isFinalTwoCommSq_categoricalPullbackSq`: **Stacks 02X9**, the explicit
  construction is a 2-fibre product in the sense of Stacks 003Q (a final object of the
  2-category of 2-commutative diagrams).
* `CategoryTheory.Cat.isTwoFibreProduct_categoricalPullbackSq`: its 1-truncated form, terminality
  in the quotient category of 2-commutative squares.
* `CategoryTheory.Cat.isFinalTwoCommSq_of_isTwoFibreProduct`: in `Cat` the 1-truncated notion
  already implies the one of Stacks 003Q.
* `CategoryTheory.Cat.isEquivalence_toCategoricalPullbackFunctor`: the comparison functor out of a
  2-cartesian square of categories is an equivalence.

## Implementation notes

A morphism of 2-commutative squares is a 1-morphism between the apexes together with comparison
2-cells for the two legs, and terminality has to be proved modulo the 2-cell equivalence by which
`CategoryTheory.Bicategory.TwoCommSq` is a strict category. Existence of the comparison is
`CategoryTheory.Cat.toCategoricalPullbackFunctor`, whose composites with the projections are the
legs of the square on the nose, so both of its comparison 2-cells are identities. Uniqueness is
`CategoryTheory.Cat.preHom_rel`: the compatibility square of Stacks 003O determines the structural
isomorphism of the triple at which a comparison lands, which is what makes the isomorphism
assembled from two comparisons' 2-cells respect those structural isomorphisms.

The bicategory `Cat` is strict, so the associators appearing in the compatibility square are
identities. The construction and the comparison are `@[implicit_reducible]`: the comparison 2-cells
are identities of 1-morphisms whose two descriptions agree only after unfolding them, and the
elaborator has to see through that for the compatibility square to be stated at all.

The apex of the explicit square is a category of triples, so its objects live in the join of the
object and morphism universes of `A`, `B` and `C`; the statements are therefore given for
`Cat.{v, max u v}`, whose object universe already absorbs the morphism universe.

## References

* [Stacks Project, Tag 02X9](https://stacks.math.columbia.edu/tag/02X9)
* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 003R](https://stacks.math.columbia.edu/tag/003R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

namespace CategoryTheory.Cat

universe v u

/-- A 2-isomorphism in `Cat` from a natural isomorphism of the underlying functors. -/
def homIsoOfNatIso {X Y : Cat.{v, u}} {L M : X ⟶ Y} (e : L.toFunctor ≅ M.toFunctor) : L ≅ M where
  hom := Cat.Hom₂.ofNatTrans e.hom
  inv := Cat.Hom₂.ofNatTrans e.inv
  hom_inv_id := Cat.Hom₂.ext (by simp)
  inv_hom_id := Cat.Hom₂.ext (by simp)

/-- The component at `x` of the forward 2-cell of `CategoryTheory.Cat.homIsoOfNatIso e` is the
component of `e.hom` at `x`. -/
@[simp]
lemma homIsoOfNatIso_hom_app {X Y : Cat.{v, u}} {L M : X ⟶ Y} (e : L.toFunctor ≅ M.toFunctor)
    (x : X) : (homIsoOfNatIso e).hom.toNatTrans.app x = e.hom.app x := rfl

variable {A B C : Cat.{v, max u v}} (F : A ⟶ C) (G : B ⟶ C)

/-- **Stacks 003R.** The explicit 2-fibre product of two functors, as a 2-commutative square: its
apex is the category of triples `(a, b, φ)` with `φ : F a ≅ G b`, its legs are the two projections
and its filler is the tautological isomorphism. -/
@[implicit_reducible]
def categoricalPullbackSq : TwoCommSq F G where
  pt := Cat.of (CategoricalPullback F.toFunctor G.toFunctor)
  fst := (CategoricalPullback.π₁ F.toFunctor G.toFunctor).toCatHom
  snd := (CategoricalPullback.π₂ F.toFunctor G.toFunctor).toCatHom
  iso := Cat.Hom.isoMk
    (CatCommSq.iso (CategoricalPullback.π₁ F.toFunctor G.toFunctor)
      (CategoricalPullback.π₂ F.toFunctor G.toFunctor) F.toFunctor G.toFunctor)

variable {F G}

/-- The comparison functor of a 2-commutative square of categories into the explicit 2-fibre
product: an object `x` of the apex goes to the triple `(fst x, snd x, φ_x)` built from the filler
of the square. -/
@[implicit_reducible]
def toCategoricalPullbackFunctor (P : TwoCommSq F G) :
    (P.pt : Type (max u v)) ⥤ CategoricalPullback F.toFunctor G.toFunctor where
  obj x :=
    { fst := P.fst.toFunctor.obj x
      snd := P.snd.toFunctor.obj x
      iso := (Cat.Hom.toNatIso P.iso).app x }
  map {_ _} φ :=
    { fst := P.fst.toFunctor.map φ
      snd := P.snd.toFunctor.map φ
      w := (Cat.Hom.toNatIso P.iso).hom.naturality φ }
  map_id _ := by apply CategoricalPullback.hom_ext <;> simp
  map_comp _ _ := by apply CategoricalPullback.hom_ext <;> simp

/-- `CategoryTheory.Cat.toCategoricalPullbackFunctor` as a 1-morphism of `Cat`. -/
@[implicit_reducible]
def toCategoricalPullback (P : TwoCommSq F G) : P.pt ⟶ (categoricalPullbackSq F G).pt :=
  (toCategoricalPullbackFunctor P).toCatHom

/-- The comparison into the explicit 2-fibre product followed by its first projection is the first
leg of the square. -/
@[simp]
lemma toCategoricalPullback_comp_fst (P : TwoCommSq F G) :
    toCategoricalPullback P ≫ (categoricalPullbackSq F G).fst = P.fst := rfl

/-- The comparison into the explicit 2-fibre product followed by its second projection is the
second leg of the square. -/
@[simp]
lemma toCategoricalPullback_comp_snd (P : TwoCommSq F G) :
    toCategoricalPullback P ≫ (categoricalPullbackSq F G).snd = P.snd := rfl

/-- The comparison functor as a morphism of 2-commutative squares: its two comparison 2-cells are
identities, and its compatibility square holds because the structural isomorphism of the triple
`(fst x, snd x, φ_x)` is the component of the filler of the square at `x`. -/
def preHomCategoricalPullback (P : TwoCommSq F G) :
    TwoCommSq.PreHom P (categoricalPullbackSq F G) where
  hom := toCategoricalPullback P
  isoFst := Iso.refl _
  isoSnd := Iso.refl _
  compat := by
    apply Cat.Hom₂.ext
    ext x
    change P.iso.hom.toNatTrans.app x ≫ G.toFunctor.map (𝟙 _) ≫ 𝟙 _ =
      F.toFunctor.map (𝟙 _) ≫ 𝟙 _ ≫ ((Cat.Hom.toNatIso P.iso).app x).hom
    simp

/-- **The compatibility square of Stacks 003O for a comparison into the explicit 2-fibre
product**, read at an object: the filler of the explicit square at the image of `x` is pinned to
the filler of the source square at `x` by the two comparison 2-cells. -/
lemma preHom_compat_app {P : TwoCommSq F G}
    (K : TwoCommSq.PreHom P (categoricalPullbackSq F G)) (x : P.pt) :
    F.toFunctor.map ((Cat.Hom.toNatIso K.isoFst).app x).hom ≫
        ((Cat.Hom.toNatIso (categoricalPullbackSq F G).iso).app
          (K.hom.toFunctor.obj x)).hom =
      ((Cat.Hom.toNatIso P.iso).app x).hom ≫
        G.toFunctor.map ((Cat.Hom.toNatIso K.isoSnd).app x).hom := by
  simpa [Cat.whiskerRight_app, Cat.whiskerLeft_app] using
    (NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans K.compat) x).symm

/-- **Any two morphisms of 2-commutative squares into the explicit 2-fibre product agree.** The
isomorphism identifying them is assembled componentwise from their comparison 2-cells. -/
theorem preHom_rel {P : TwoCommSq F G}
    (L M : TwoCommSq.PreHom P (categoricalPullbackSq F G)) :
    TwoCommSq.PreHom.Rel L M := by
  let e₁ := Cat.Hom.toNatIso (L.isoFst.symm ≪≫ M.isoFst)
  let e₂ := Cat.Hom.toNatIso (L.isoSnd.symm ≪≫ M.isoSnd)
  have he₁ : ∀ x : P.pt, e₁.hom.app x =
      ((Cat.Hom.toNatIso L.isoFst).app x).inv ≫ ((Cat.Hom.toNatIso M.isoFst).app x).hom :=
    fun _ => rfl
  have he₂ : ∀ x : P.pt, e₂.hom.app x =
      ((Cat.Hom.toNatIso L.isoSnd).app x).inv ≫ ((Cat.Hom.toNatIso M.isoSnd).app x).hom :=
    fun _ => rfl
  have hinv : ∀ x : P.pt,
      ((Cat.Hom.toNatIso (categoricalPullbackSq F G).iso).app (L.hom.toFunctor.obj x)).hom ≫
          G.toFunctor.map ((Cat.Hom.toNatIso L.isoSnd).app x).inv =
        F.toFunctor.map ((Cat.Hom.toNatIso L.isoFst).app x).inv ≫
          ((Cat.Hom.toNatIso P.iso).app x).hom := by
    intro x
    rw [← Iso.cancel_iso_hom_left (F.toFunctor.mapIso ((Cat.Hom.toNatIso L.isoFst).app x))]
    simp only [Functor.mapIso_hom]
    rw [← Category.assoc (F.toFunctor.map ((Cat.Hom.toNatIso L.isoFst).app x).hom),
      preHom_compat_app L x]
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
    simp
  have key : ∀ x : P.pt,
      F.toFunctor.map (e₁.hom.app x) ≫
          ((Cat.Hom.toNatIso (categoricalPullbackSq F G).iso).app (M.hom.toFunctor.obj x)).hom =
        ((Cat.Hom.toNatIso (categoricalPullbackSq F G).iso).app (L.hom.toFunctor.obj x)).hom ≫
          G.toFunctor.map (e₂.hom.app x) := by
    intro x
    rw [he₁ x, he₂ x, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [preHom_compat_app M x, reassoc_of% hinv x]
  let θ : L.hom.toFunctor ≅ M.hom.toFunctor :=
    NatIso.ofComponents
      (fun x => CategoricalPullback.mkIso (e₁.app x) (e₂.app x) (key x))
      (fun {_ _} φ => CategoricalPullback.hom_ext (e₁.hom.naturality φ) (e₂.hom.naturality φ))
  refine ⟨homIsoOfNatIso θ, ?_, ?_⟩
  · apply Cat.Hom₂.ext
    ext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, homIsoOfNatIso_hom_app]
    rw [show (categoricalPullbackSq F G).fst.toFunctor.map (θ.hom.app x) = e₁.hom.app x from rfl,
      he₁ x]
    simp
  · apply Cat.Hom₂.ext
    ext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, homIsoOfNatIso_hom_app]
    rw [show (categoricalPullbackSq F G).snd.toFunctor.map (θ.hom.app x) = e₂.hom.app x from rfl,
      he₂ x]
    simp

/-- The explicit 2-fibre product of two functors is a 1-truncated 2-fibre product of them in the
bicategory of categories: it is a terminal object of the quotient category of 2-commutative
squares over the cospan (`CategoryTheory.Bicategory.IsTwoFibreProduct`). The full statement of
Stacks 02X9, with the uniqueness of the 2-isomorphism of Stacks 003P (2), is
`CategoryTheory.Cat.isFinalTwoCommSq_categoricalPullbackSq`. -/
def isTwoFibreProduct_categoricalPullbackSq (F : A ⟶ C) (G : B ⟶ C) :
    IsTwoFibreProduct (categoricalPullbackSq F G) :=
  IsTerminal.ofUniqueHom
    (fun P => Quotient.mk _ (preHomCategoricalPullback P))
    (fun P m => Quotient.inductionOn m fun L =>
      Quotient.sound (preHom_rel L (preHomCategoricalPullback P)))

/-- **The comparison functor out of a 2-cartesian square of categories is an equivalence.** A
quasi-inverse is the 1-morphism that terminality of the square supplies for the explicit 2-fibre
product, and the two 2-cells are the ones identifying each composite with an identity. -/
theorem isEquivalence_toCategoricalPullbackFunctor {P : TwoCommSq F G}
    (hP : IsTwoFibreProduct P) : (toCategoricalPullbackFunctor P).IsEquivalence := by
  let a := preHomCategoricalPullback P
  let b := twoFibreProductPreHom hP (categoricalPullbackSq F G)
  obtain ⟨e₁, -, -⟩ := twoFibreProductPreHom_rel hP (a.comp b) (TwoCommSq.PreHom.id P)
  obtain ⟨e₂, -, -⟩ :=
    preHom_rel (b.comp a) (TwoCommSq.PreHom.id (categoricalPullbackSq F G))
  exact (CategoryTheory.Equivalence.mk (toCategoricalPullbackFunctor P) b.hom.toFunctor
    (Cat.Hom.toNatIso e₁).symm (Cat.Hom.toNatIso e₂)).isEquivalence_functor

/-- **The projections of the explicit 2-fibre product jointly detect 2-cells.** A morphism of the
category of triples is determined by its two components, so a natural transformation into it is
determined by its whiskerings with the two projections. -/
theorem legsDetect_categoricalPullbackSq : (categoricalPullbackSq F G).LegsDetectTwoCells := by
  intro t a b η θ hfst hsnd
  apply Cat.Hom₂.ext
  ext x
  apply CategoricalPullback.hom_ext
  · have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans hfst) x
    simp only [Cat.whiskerRight_app] at h
    exact h
  · have h := NatTrans.congr_app (congrArg Cat.Hom₂.toNatTrans hsnd) x
    simp only [Cat.whiskerRight_app] at h
    exact h

/-- **Stacks 02X9.** The explicit 2-fibre product of two functors is a 2-fibre product of them in
the 2-category of categories in the sense of Stacks 003Q: a final object of the 2-category of
2-commutative diagrams over the cospan, so any two 1-morphisms into it from a 2-commutative
square are isomorphic by a *unique* 2-morphism. -/
@[stacks 02X9 "the explicit construction is a 2-fibre product in the sense of Stacks 003Q, \
with the uniqueness of the 2-isomorphism of Stacks 003P (2)"]
noncomputable def isFinalTwoCommSq_categoricalPullbackSq (F : A ⟶ C) (G : B ⟶ C) :
    IsFinalTwoCommSq (categoricalPullbackSq F G) :=
  isFinalTwoCommSq_of_legsDetect (isTwoFibreProduct_categoricalPullbackSq F G)
    legsDetect_categoricalPullbackSq

/-- **In the 2-category of categories the two notions of 2-fibre product agree.** A terminal
object of the quotient category of 2-commutative squares over a cospan of categories is a final
object of the 2-category of 2-commutative diagrams (Stacks 003Q): the legs of the explicit
2-fibre product detect 2-cells, and detection passes to every 1-truncated 2-fibre product of the
cospan. -/
noncomputable def isFinalTwoCommSq_of_isTwoFibreProduct {P : TwoCommSq F G}
    (hP : IsTwoFibreProduct P) : IsFinalTwoCommSq P :=
  isFinalTwoCommSq_of_isTwoFibreProduct_of_legsDetect hP
    (isTwoFibreProduct_categoricalPullbackSq F G) legsDetect_categoricalPullbackSq

end CategoryTheory.Cat

end
