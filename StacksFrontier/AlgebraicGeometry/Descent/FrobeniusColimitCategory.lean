module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundles
public import StacksFrontier.AlgebraicGeometry.Frobenius

/-!
# The colimit category along an endofunctor, and `colim_F Vect(X)`

Let `C` be a category and let `F : C ⥤ C` be an endofunctor. Stacks Tag 0EXA describes the
colimit of the sequential diagram

`C →F C →F C →F ⋯`

in down-to-earth terms: an object is a pair `(E, n)` with `E` an object of `C` and `n ≥ 0` an
integer, and the Hom-sets are the colimits

`Hom((E, n), (G, m)) = colim_N Hom_C(F^{N - n}E, F^{N - m}G)`

over the absolute levels `N ≥ n, m`. This file builds that category, and specialises it to
pullback along the absolute Frobenius of a scheme in characteristic `p`, where it is the
category `colim_F Vect(X)` whose equivalence with the finite locally free modules over
`colim_F 𝒪_X` is asserted by Stacks Tag 0EXB.

## Main definitions

* `CategoryTheory.endoRaise`: a morphism between iterates of `F`, pushed up by applying `F` to
  it a number of times. Raising is what the transition maps of the colimit of Hom-sets do.
* `CategoryTheory.endoHomCast`: a morphism between iterates of `F`, transported along equalities
  of the two exponents.
* `CategoryTheory.EndoColim`: the objects `(E, n)` of the colimit category.
* `CategoryTheory.EndoColim.HomRep` and `CategoryTheory.EndoColim.Hom`: a presentation of a
  morphism at a level, and the Hom-sets themselves — the presentations modulo raising.
* `CategoryTheory.EndoColim.compHom`: the composite of two presentations, formed by raising both
  to a common absolute level.
* `CategoryTheory.EndoColim.stageFunctor`: the canonical functor `C ⥤ colim_F C` placing an
  object at a given stage.
* `AlgebraicGeometry.frobeniusColimitVectModel`: **the category `colim_F Vect(X)` of Stacks Tag
  0EXA**, in the explicit form the tag describes it.

## Main results

* `CategoryTheory.EndoColim.instCategory`: **`colim_F C` is a category.** Composition is defined
  on presentations by raising both to a common absolute level; that this is well defined is
  `CategoryTheory.EndoColim.Hom.of_compHom_step_left` and
  `CategoryTheory.EndoColim.Hom.of_compHom_step_right`, and the unit and associativity laws are
  `CategoryTheory.EndoColim.Hom.of_id_compHom`,
  `CategoryTheory.EndoColim.Hom.of_compHom_id` and
  `CategoryTheory.EndoColim.Hom.of_compHom_assoc`.
* `CategoryTheory.EndoColim.Hom.exists_of` and
  `CategoryTheory.EndoColim.Hom.of_eq_of_iff`: **the Hom-sets of `colim_F C` are the colimits of
  the Hom-sets of `C` along `F`**, as Stacks Tag 0EXA describes them. Every morphism is presented
  at some level, and two presentations present the same morphism exactly when raising both to a
  common level carries them to the same morphism of `C` — so nothing is identified beyond what
  raising identifies. `CategoryTheory.EndoColim.Hom.of_eq_of` is the direction of the latter
  which the construction of the category uses.

## Implementation notes

All the content of the construction is exponent bookkeeping, and it is organised as follows.
A presentation of a morphism `(E, n) ⟶ (G, m)` at level `k` is a morphism
`F^{m + k}E ⟶ F^{n + k}G`, which is the morphism at the absolute level `N = n + m + k`; the
levels `N` of this form are cofinal among the `N ≥ n, m`, and using them removes every truncated
subtraction from the construction. Raising adds its argument on the right of an exponent, so
`endoRaise f (j + 1) = F.map (endoRaise f j)` holds definitionally; associativity and
commutativity of the exponents do not, and `CategoryTheory.endoHomCast` transports along them.
Each lemma about transports is proved by substituting the exponent equalities, after which the
transport disappears by proof irrelevance, and every identity between morphisms of `colim_F C`
is reduced to `CategoryTheory.endoHomCast_endoRaise_comp_eq` and its variants: two composites of
transported raises agree as soon as the raise amounts do, whatever exponents the two composites
pass through in the middle. `CategoryTheory.endoHomCast_comp_rfl` is the rewrite which pushes a
transport of a composite down onto its factors, and is what brings a goal into that shape.

Composition raises the first presentation by `t + l` and the second by `n + k`, so that both
land at the absolute level `n + m + t + k + l`, and the result is presented at level
`m + k + l`.

**Why the category is built by hand.** Mathlib's `CategoryTheory.Limits.colimit` in `Cat` —
which is what `AlgebraicGeometry.frobeniusColimitVect` is — is computed by passing to nerves and
reflecting, and so says nothing about the objects or the morphisms of the colimit. Worse, a
cocone on a diagram in `Cat` asks for equalities of functors, whereas the stage functors of Tag
0EXB are compatible only up to isomorphism (extension of scalars is a sheafified tensor product
and composes with itself only up to isomorphism), so no functor out of that colimit can be
assembled from them. The category built here is the pseudo-colimit, which is what Tag 0EXA
describes, and a functor out of it needs only the data the stage functors have.

**Where the rest is proved.** The functor out of this category which Tag 0EXB compares is built
in `StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitComparison`, as
`AlgebraicGeometry.frobeniusColimitVectComparison`; what that tag asserts — that the functor is
an equivalence — is `AlgebraicGeometry.frobeniusColimitVectEquivalence`. The equivalence of this
category with `AlgebraicGeometry.frobeniusColimitVect`, the strict colimit in `Cat` — whose
objects are the *quotient* of `⨆_n Obj(Vect(X))` identifying `(ℰ, n)` with `(F^*ℰ, n + 1)`, so
that the two categories are equivalent but not isomorphic — is
`CategoryTheory.EndoColim.catColimitEquivalence` of
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitStrictColimit`, specialised in
`AlgebraicGeometry.frobeniusColimitVectModelEquivalence`.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

/-! ### Morphisms between iterates of an endofunctor -/

/-- A morphism between iterates of `F`, raised by applying `F` to it `j` more times. -/
def endoRaise {E G : C} {m n : ℕ} (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) :
    ∀ j : ℕ, ((F.endoIter (m + j)).obj E ⟶ (F.endoIter (n + j)).obj G)
  | 0 => f
  | j + 1 => F.map (endoRaise f j)

variable {E G H : C} {m n r s m' n' r' m'' n'' : ℕ}

/-- Raising by `0` leaves a morphism unchanged. -/
@[simp]
lemma endoRaise_zero (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) :
    endoRaise f 0 = f := rfl

/-- Raising by `j + 1` is applying `F` to the raise by `j`. -/
@[simp]
lemma endoRaise_succ (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) (j : ℕ) :
    endoRaise f (j + 1) = F.map (endoRaise f j) := rfl

/-- A morphism between iterates of `F`, transported along equalities of the two exponents. -/
def endoHomCast (hm : m = m') (hn : n = n')
    (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) :
    (F.endoIter m').obj E ⟶ (F.endoIter n').obj G :=
  cast (by rw [hm, hn]) f

/-- Transport along reflexivity leaves a morphism unchanged. -/
@[simp]
lemma endoHomCast_rfl (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) :
    endoHomCast rfl rfl f = f := rfl

/-- Two successive transports are the transport along the composite equalities. -/
lemma endoHomCast_endoHomCast (hm : m = m') (hn : n = n') (hm' : m' = m'') (hn' : n' = n'')
    (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) :
    endoHomCast hm' hn' (endoHomCast hm hn f) = endoHomCast (hm.trans hm') (hn.trans hn') f := by
  subst hm; subst hn; subst hm'; subst hn'; rfl

/-- The transport of a composite is the composite of the transports of its factors. -/
lemma endoHomCast_comp (hm : m = m') (hn : n = n') (hr : r = r')
    (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G)
    (g : (F.endoIter n).obj G ⟶ (F.endoIter r).obj H) :
    endoHomCast hm hr (f ≫ g) = endoHomCast hm hn f ≫ endoHomCast hn hr g := by
  subst hm; subst hn; subst hr; rfl

/-- Two transports meeting at a common object merge into one transport of the composite. The
two proofs of the middle equality are not required to be the same term. -/
lemma endoHomCast_comp_endoHomCast (hm : m = m') (hn hn₂ : n = n') (hr : r = r')
    (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G)
    (g : (F.endoIter n).obj G ⟶ (F.endoIter r).obj H) :
    endoHomCast hm hn f ≫ endoHomCast hn₂ hr g = endoHomCast hm hr (f ≫ g) := by
  subst hm; subst hn; subst hr; rfl

/-- The transport of an identity is the identity. -/
lemma endoHomCast_id (hm : m = m') :
    endoHomCast hm hm (𝟙 ((F.endoIter m).obj E)) = 𝟙 ((F.endoIter m').obj E) := by
  subst hm; rfl

/-- **A transport of a composite splits into transports of the two factors**, leaving the
exponent in the middle alone. -/
lemma endoHomCast_comp_rfl (hm : m = m') (hr : r = r')
    (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G)
    (g : (F.endoIter n).obj G ⟶ (F.endoIter r).obj H) :
    endoHomCast hm hr (f ≫ g) = endoHomCast hm rfl f ≫ endoHomCast rfl hr g := by
  subst hm; subst hr; rfl

/-- Applying `F` to a transport is the transport of `F` applied to the morphism, with both
exponents raised by one. -/
lemma map_endoHomCast (hm : m = m') (hn : n = n')
    (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) :
    F.map (endoHomCast hm hn f) =
      endoHomCast (m := m + 1) (n := n + 1) (m' := m' + 1) (n' := n' + 1)
        (by omega) (by omega) (F.map f) := by
  subst hm; subst hn; rfl

/-- Raising a composite is the composite of the raises. -/
lemma endoRaise_comp (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G)
    (g : (F.endoIter n).obj G ⟶ (F.endoIter r).obj H) (j : ℕ) :
    endoRaise (f ≫ g) j = endoRaise f j ≫ endoRaise g j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [endoRaise_succ, ih, F.map_comp]; rfl

/-- Raising an identity gives the identity. -/
lemma endoRaise_id (j : ℕ) :
    endoRaise (𝟙 ((F.endoIter m).obj E)) j = 𝟙 ((F.endoIter (m + j)).obj E) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [endoRaise_succ, ih, F.map_id]; rfl

/-- Raising a transport is the transport of the raise. -/
lemma endoRaise_endoHomCast (hm : m = m') (hn : n = n')
    (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) (j : ℕ) :
    endoRaise (endoHomCast hm hn f) j =
      endoHomCast (by omega) (by omega) (endoRaise f j) := by
  subst hm; subst hn; rfl

/-- Raising by `j` and then by `i` is raising by `j + i`, up to the transport comparing the
exponents. -/
lemma endoRaise_endoRaise (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) (j i : ℕ) :
    endoRaise (endoRaise f j) i =
      endoHomCast (by omega) (by omega) (endoRaise f (j + i)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have h : endoRaise (endoRaise f j) (i + 1) = F.map (endoRaise (endoRaise f j) i) := rfl
      rw [h, ih, map_endoHomCast]
      rfl

/-- Raising by two amounts which happen to be equal gives the same morphism, up to the
transport comparing the two exponents. -/
lemma endoRaise_congr (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) {j j' : ℕ} (h : j = j') :
    endoRaise f j = endoHomCast (by omega) (by omega) (endoRaise f j') := by
  subst h; rfl

/-- **Raises by equal amounts, transported to the same pair of exponents, agree.** -/
lemma endoHomCast_endoRaise_eq (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) {j j' : ℕ}
    (h : j = j') {q s : ℕ} (h₁ : m + j = q) (h₂ : n + j = s) (h₃ : m + j' = q)
    (h₄ : n + j' = s) :
    endoHomCast h₁ h₂ (endoRaise f j) = endoHomCast h₃ h₄ (endoRaise f j') := by
  subst h; rfl

/-- Raising `F.map f` by `j` is applying `F` to the raise of `f` by `j`, up to the transport
comparing the exponents. -/
lemma endoRaise_map (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) (j : ℕ) :
    endoRaise (m := m + 1) (n := n + 1) (F.map f) j =
      endoHomCast (m := m + j + 1) (n := n + j + 1) (by omega) (by omega)
        (F.map (endoRaise f j)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have h : endoRaise (m := m + 1) (n := n + 1) (F.map f) (j + 1) =
          F.map (endoRaise (m := m + 1) (n := n + 1) (F.map f) j) := rfl
      rw [h, ih]
      exact map_endoHomCast _ _ _

/-- **A transported identity absorbs into the transport of what follows it.** -/
lemma endoHomCast_id_comp_eq (g : (F.endoIter n).obj E ⟶ (F.endoIter s).obj H) {i i' : ℕ}
    (hi : i = i') {q t w : ℕ} (hm : m = q) (hn : m = t)
    (a₃ : n + i = t) (a₄ : s + i = w) (b₁ : n + i' = q) (b₄ : s + i' = w) :
    endoHomCast hm hn (𝟙 ((F.endoIter m).obj E)) ≫ endoHomCast a₃ a₄ (endoRaise g i) =
      endoHomCast b₁ b₄ (endoRaise g i') := by
  subst hi; subst hn; subst hm; exact Category.id_comp _

/-- **A transported identity absorbs into the transport of what precedes it.** -/
lemma endoHomCast_comp_id_eq (g : (F.endoIter n).obj E ⟶ (F.endoIter s).obj H) {i i' : ℕ}
    (hi : i = i') {q t w : ℕ} (hm : m = t) (hn : m = w)
    (a₃ : n + i = q) (a₄ : s + i = t) (b₁ : n + i' = q) (b₄ : s + i' = w) :
    endoHomCast a₃ a₄ (endoRaise g i) ≫ endoHomCast hm hn (𝟙 ((F.endoIter m).obj H)) =
      endoHomCast b₁ b₄ (endoRaise g i') := by
  subst hi; subst hm; subst hn; exact Category.comp_id _

/-- **Raising a morphism of `C` is applying the iterate of `F` to it.** -/
lemma endoRaise_eq_endoIter_map (f : E ⟶ G) (j : ℕ) :
    endoRaise (m := 0) (n := 0) f j =
      endoHomCast (by omega) (by omega) ((F.endoIter j).map f) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have h : endoRaise (m := 0) (n := 0) f (j + 1) =
          F.map (endoRaise (m := 0) (n := 0) f j) := rfl
      rw [h, ih]
      exact map_endoHomCast _ _ _

/-- **Raising an iterate of a morphism of `C` is a higher iterate of it.** -/
lemma endoRaise_endoIter_map (f : E ⟶ G) (m j : ℕ) :
    endoRaise ((F.endoIter m).map f) j =
      endoHomCast (by omega) (by omega) ((F.endoIter (m + j)).map f) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have h : endoRaise ((F.endoIter m).map f) (j + 1) =
          F.map (endoRaise ((F.endoIter m).map f) j) := rfl
      rw [h, ih]
      exact map_endoHomCast _ _ _

/-- **Two transported iterates of morphisms of `C` compose to the same morphism when the
iterates agree.** -/
lemma endoHomCast_endoIter_map_comp_eq {K : C} (f : E ⟶ G) (g : G ⟶ K)
    {j₁ j₂ i₁ i₂ : ℕ} (hj : j₁ = j₂) (hi : i₁ = i₂) {q t t' w : ℕ}
    (a₁ : j₁ = q) (a₂ : j₁ = t) (a₃ : i₁ = t) (a₄ : i₁ = w)
    (b₁ : j₂ = q) (b₂ : j₂ = t') (b₃ : i₂ = t') (b₄ : i₂ = w) :
    endoHomCast a₁ a₂ ((F.endoIter j₁).map f) ≫ endoHomCast a₃ a₄ ((F.endoIter i₁).map g) =
      endoHomCast b₁ b₂ ((F.endoIter j₂).map f) ≫ endoHomCast b₃ b₄ ((F.endoIter i₂).map g) := by
  subst hj; subst hi
  obtain rfl : t = t' := by omega
  rfl

/-- **Two transported raises compose to the same morphism when the raise amounts agree.** The
two composites may run through different exponents in the middle. -/
lemma endoHomCast_endoRaise_comp_eq (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G)
    (g : (F.endoIter r).obj G ⟶ (F.endoIter s).obj H) {j j' i i' : ℕ}
    (hj : j = j') (hi : i = i') {q t t' w : ℕ}
    (a₁ : m + j = q) (a₂ : n + j = t) (a₃ : r + i = t) (a₄ : s + i = w)
    (b₁ : m + j' = q) (b₂ : n + j' = t') (b₃ : r + i' = t') (b₄ : s + i' = w) :
    endoHomCast a₁ a₂ (endoRaise f j) ≫ endoHomCast a₃ a₄ (endoRaise g i) =
      endoHomCast b₁ b₂ (endoRaise f j') ≫ endoHomCast b₃ b₄ (endoRaise g i') := by
  subst hj; subst hi
  obtain rfl : t = t' := by omega
  rfl

/-- The three-factor form of `endoHomCast_endoRaise_comp_eq`. -/
lemma endoHomCast_endoRaise_comp₃_eq {K : C} {z z' : ℕ}
    (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G)
    (g : (F.endoIter r).obj G ⟶ (F.endoIter s).obj H)
    (h : (F.endoIter z).obj H ⟶ (F.endoIter z').obj K) {j j' i i' o o' : ℕ}
    (hj : j = j') (hi : i = i') (ho : o = o') {q t₁ t₂ t₁' t₂' w : ℕ}
    (a₁ : m + j = q) (a₂ : n + j = t₁) (a₃ : r + i = t₁) (a₄ : s + i = t₂)
    (a₅ : z + o = t₂) (a₆ : z' + o = w)
    (b₁ : m + j' = q) (b₂ : n + j' = t₁') (b₃ : r + i' = t₁') (b₄ : s + i' = t₂')
    (b₅ : z + o' = t₂') (b₆ : z' + o' = w) :
    endoHomCast a₁ a₂ (endoRaise f j) ≫ endoHomCast a₃ a₄ (endoRaise g i) ≫
        endoHomCast a₅ a₆ (endoRaise h o) =
      endoHomCast b₁ b₂ (endoRaise f j') ≫ endoHomCast b₃ b₄ (endoRaise g i') ≫
        endoHomCast b₅ b₆ (endoRaise h o') := by
  subst hj; subst hi; subst ho
  obtain rfl : t₁ = t₁' := by omega
  obtain rfl : t₂ = t₂' := by omega
  rfl

/-! ### The colimit category along an endofunctor -/

/-- An object of the colimit category `colim_F C`: an object of `C` together with the stage of
the diagram `C →F C →F ⋯` at which it is placed. -/
structure EndoColim (F : C ⥤ C) where
  /-- the underlying object of `C` -/
  obj : C
  /-- the stage of the diagram at which it is placed -/
  stage : ℕ

namespace EndoColim

/-- A presentation at level `k` of a morphism of `colim_F C` from `(E, n)` to `(G, m)`: a
morphism `F^{m + k}E ⟶ F^{n + k}G` of `C`, that is, a morphism `F^{N - n}E ⟶ F^{N - m}G` at the
absolute level `N = n + m + k`. -/
structure HomRep (A B : EndoColim F) where
  /-- the level at which the morphism is presented -/
  level : ℕ
  /-- the morphism of `C` presenting it -/
  hom : (F.endoIter (B.stage + level)).obj A.obj ⟶ (F.endoIter (A.stage + level)).obj B.obj

/-- The relation identifying a presentation with the presentation one level up obtained by
applying `F` to it. The Hom-sets of `colim_F C` are the colimits of the Hom-sets of `C` along
`F`, so this is the only identification there is. -/
def HomRep.Rel {A B : EndoColim F} (x y : HomRep A B) : Prop :=
  y = ⟨x.level + 1, endoHomCast (by omega) (by omega) (endoRaise x.hom 1)⟩

/-- **The Hom-sets of `colim_F C`.** A morphism from `(E, n)` to `(G, m)` is a morphism
`F^{N - n}E ⟶ F^{N - m}G` of `C` at some absolute level `N`, two of them being identified when
one is obtained from the other by applying `F`; that is,
`Hom((E, n), (G, m)) = colim_N Hom_C(F^{N - n}E, F^{N - m}G)`. -/
def Hom (A B : EndoColim F) : Type v := Quot (α := HomRep A B) HomRep.Rel

/-- The morphism of `colim_F C` presented by the morphism `f` of `C` at level `k`. -/
def Hom.of {A B : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) :
    Hom A B :=
  Quot.mk _ ⟨k, f⟩

/-- Every morphism of `colim_F C` is presented at some level. -/
lemma Hom.exists_of {A B : EndoColim F} (u : Hom A B) :
    ∃ (k : ℕ) (f : (F.endoIter (B.stage + k)).obj A.obj ⟶
      (F.endoIter (A.stage + k)).obj B.obj), Hom.of k f = u := by
  induction u using Quot.ind with
  | _ x => exact ⟨x.level, x.hom, rfl⟩

/-- **Raising the level by one does not change the morphism presented.** -/
lemma Hom.of_step {A B : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) :
    Hom.of (k + 1) (endoHomCast (by omega) (by omega) (endoRaise f 1)) = Hom.of k f :=
  (Quot.sound (r := @HomRep.Rel _ _ F A B) (a := ⟨k, f⟩)
    (b := ⟨k + 1, endoHomCast (by omega) (by omega) (endoRaise f 1)⟩) rfl).symm

/-- Presenting at an equal level, through the transport comparing the two, does not change the
morphism presented. -/
lemma Hom.of_levelCast {A B : EndoColim F} {k l : ℕ}
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj)
    (h : k = l) :
    Hom.of l (endoHomCast (by omega) (by omega) f) = Hom.of k f := by
  subst h; rfl

/-- **Raising the level does not change the morphism presented.** -/
lemma Hom.of_raise {A B : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) (j : ℕ) :
    Hom.of (k + j) (endoHomCast (by omega) (by omega) (endoRaise f j)) = Hom.of k f := by
  induction j with
  | zero => rfl
  | succ j ih =>
      refine Eq.trans ?_ (Eq.trans (Hom.of_step (k + j)
        (endoHomCast (by omega) (by omega) (endoRaise f j))) ih)
      refine congrArg (Hom.of (k + (j + 1))) ?_
      rw [endoRaise_endoHomCast, endoRaise_endoRaise, endoHomCast_endoHomCast,
        endoHomCast_endoHomCast]

/-- **Two presentations which agree after raising present the same morphism.** -/
lemma Hom.of_eq_of {A B : EndoColim F} {k l : ℕ}
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj)
    (g : (F.endoIter (B.stage + l)).obj A.obj ⟶ (F.endoIter (A.stage + l)).obj B.obj)
    (j i : ℕ) (h : k + j = l + i)
    (hfg : endoHomCast (m' := B.stage + (l + i)) (n' := A.stage + (l + i))
        (by omega) (by omega) (endoRaise f j) =
      endoHomCast (m' := B.stage + (l + i)) (n' := A.stage + (l + i))
        (by omega) (by omega) (endoRaise g i)) :
    Hom.of k f = Hom.of l g := by
  refine Eq.trans (Hom.of_raise k f j).symm (Eq.trans ?_ (Hom.of_raise l g i))
  refine Eq.trans (Hom.of_levelCast (A := A) (B := B) (k := k + j) (l := l + i)
    (endoHomCast (by omega) (by omega) (endoRaise f j)) h).symm ?_
  refine congrArg (Hom.of (l + i)) ?_
  rw [endoHomCast_endoHomCast]
  exact hfg

/-! ### The Hom-sets are the colimits of the Hom-sets of `C` -/

/-- Two presentations **agree** when raising both to a common level carries them to the same
morphism of `C`. This is the relation whose quotient is the colimit
`colim_N Hom_C(F^{N - n}E, F^{N - m}G)`. -/
def HomRep.Agree {A B : EndoColim F} (x y : HomRep A B) : Prop :=
  ∃ (j i : ℕ) (h : x.level + j = y.level + i),
    endoHomCast (m' := B.stage + (y.level + i)) (n' := A.stage + (y.level + i))
        (by omega) (by omega) (endoRaise x.hom j) =
      endoHomCast (by omega) (by omega) (endoRaise y.hom i)

/-- Agreement of presentations is reflexive. -/
lemma HomRep.Agree.refl {A B : EndoColim F} (x : HomRep A B) : x.Agree x :=
  ⟨0, 0, rfl, rfl⟩

/-- Agreement of presentations is symmetric. -/
lemma HomRep.Agree.symm {A B : EndoColim F} {x y : HomRep A B} (hxy : x.Agree y) : y.Agree x := by
  obtain ⟨j, i, h, e⟩ := hxy
  refine ⟨i, j, h.symm, ?_⟩
  have e' := congrArg (endoHomCast (m' := B.stage + (x.level + j))
    (n' := A.stage + (x.level + j)) (by omega) (by omega)) e
  simp only [endoHomCast_endoHomCast] at e'
  exact e'.symm

/-- Agreement of presentations is transitive. -/
lemma HomRep.Agree.trans {A B : EndoColim F} {x y z : HomRep A B}
    (hxy : x.Agree y) (hyz : y.Agree z) : x.Agree z := by
  obtain ⟨j, i, h₁, e₁⟩ := hxy
  obtain ⟨j', i', h₂, e₂⟩ := hyz
  refine ⟨j + j', i' + i, by omega, ?_⟩
  have g₁ := congrArg (fun t ↦ endoHomCast (m' := B.stage + (z.level + (i' + i)))
    (n' := A.stage + (z.level + (i' + i))) (by omega) (by omega) (endoRaise t j')) e₁
  have g₂ := congrArg (fun t ↦ endoHomCast (m' := B.stage + (z.level + (i' + i)))
    (n' := A.stage + (z.level + (i' + i))) (by omega) (by omega) (endoRaise t i)) e₂
  simp only [endoRaise_endoHomCast, endoRaise_endoRaise, endoHomCast_endoHomCast] at g₁ g₂
  refine g₁.trans (Eq.trans ?_ g₂)
  exact endoHomCast_endoRaise_eq _ (by omega) _ _ _ _

/-- A presentation and the presentation one level up agree. -/
lemma HomRep.Rel.agree {A B : EndoColim F} {x y : HomRep A B} (h : HomRep.Rel x y) :
    x.Agree y := by
  subst h
  refine ⟨1, 0, by simp, ?_⟩
  simp only [endoRaise_zero, endoHomCast_endoHomCast]

/-- The presentations of morphisms `(E, n) ⟶ (G, m)`, up to agreement after raising. -/
def homRepSetoid (A B : EndoColim F) : _root_.Setoid (HomRep A B) where
  r := HomRep.Agree
  iseqv := ⟨HomRep.Agree.refl, HomRep.Agree.symm, HomRep.Agree.trans⟩

/-- **Two presentations present the same morphism of `colim_F C` exactly when they agree after
being raised to a common level.** With `CategoryTheory.EndoColim.Hom.exists_of` this exhibits
the Hom-sets of `colim_F C` as the colimits `colim_N Hom_C(F^{N - n}E, F^{N - m}G)` of Stacks
Tag 0EXA: nothing is identified in them beyond what raising identifies. -/
lemma Hom.of_eq_of_iff {A B : EndoColim F} {k l : ℕ}
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj)
    (g : (F.endoIter (B.stage + l)).obj A.obj ⟶ (F.endoIter (A.stage + l)).obj B.obj) :
    Hom.of k f = Hom.of l g ↔ HomRep.Agree (⟨k, f⟩ : HomRep A B) ⟨l, g⟩ :=
  ⟨fun heq ↦ _root_.Quotient.exact (s := homRepSetoid A B)
    (congrArg (Quot.lift (fun x ↦ _root_.Quotient.mk (homRepSetoid A B) x)
      fun _ _ hab ↦ _root_.Quotient.sound hab.agree) heq),
    fun ⟨j, i, h, e⟩ ↦ Hom.of_eq_of f g j i h e⟩

/-! ### Composition -/

/-- **The composite of two presentations.** A morphism `(E, n) ⟶ (G, m)` presented at level `k`
and a morphism `(G, m) ⟶ (K, t) ` presented at level `l` are raised to the common absolute
level `n + m + t + k + l`, where they compose in `C`. The composite is presented at level
`m + k + l`. -/
def compHom {A B D : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) (l : ℕ)
    (g : (F.endoIter (D.stage + l)).obj B.obj ⟶ (F.endoIter (B.stage + l)).obj D.obj) :
    (F.endoIter (D.stage + (B.stage + k + l))).obj A.obj ⟶
      (F.endoIter (A.stage + (B.stage + k + l))).obj D.obj :=
  endoHomCast (m' := D.stage + (B.stage + k + l)) (n' := A.stage + D.stage + k + l)
      (by omega) (by omega) (endoRaise f (D.stage + l)) ≫
    endoHomCast (m' := A.stage + D.stage + k + l) (n' := A.stage + (B.stage + k + l))
      (by omega) (by omega) (endoRaise g (A.stage + k))

/-- **Raising the level of the second factor does not change the composite.** -/
lemma Hom.of_compHom_step_right {A B D : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) (l : ℕ)
    (g : (F.endoIter (D.stage + l)).obj B.obj ⟶ (F.endoIter (B.stage + l)).obj D.obj) :
    Hom.of (B.stage + k + (l + 1))
        (compHom k f (l + 1) (endoHomCast (by omega) (by omega) (endoRaise g 1))) =
      Hom.of (B.stage + k + l) (compHom k f l g) := by
  refine Hom.of_eq_of _ _ 0 1 (by omega) ?_
  simp only [compHom, endoRaise_zero, endoRaise_comp, endoRaise_endoHomCast,
    endoRaise_endoRaise, endoHomCast_comp_rfl, endoHomCast_endoHomCast]
  apply endoHomCast_endoRaise_comp_eq <;> omega

/-- **Raising the level of the first factor does not change the composite.** -/
lemma Hom.of_compHom_step_left {A B D : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) (l : ℕ)
    (g : (F.endoIter (D.stage + l)).obj B.obj ⟶ (F.endoIter (B.stage + l)).obj D.obj) :
    Hom.of (B.stage + (k + 1) + l)
        (compHom (k + 1) (endoHomCast (by omega) (by omega) (endoRaise f 1)) l g) =
      Hom.of (B.stage + k + l) (compHom k f l g) := by
  refine Hom.of_eq_of _ _ 0 1 (by omega) ?_
  simp only [compHom, endoRaise_zero, endoRaise_comp, endoRaise_endoHomCast,
    endoRaise_endoRaise, endoHomCast_comp_rfl, endoHomCast_endoHomCast]
  apply endoHomCast_endoRaise_comp_eq <;> omega

/-- **Composition in `colim_F C`.** -/
def Hom.comp {A B D : EndoColim F} (u : Hom A B) (v : Hom B D) : Hom A D :=
  Quot.lift₂ (fun x y ↦ Hom.of (B.stage + x.level + y.level) (compHom x.level x.hom y.level y.hom))
    (fun x y₁ y₂ h ↦ by
      subst h
      exact (Hom.of_compHom_step_right x.level x.hom y₁.level y₁.hom).symm)
    (fun x₁ x₂ y h ↦ by
      subst h
      exact (Hom.of_compHom_step_left x₁.level x₁.hom y.level y.hom).symm) u v

/-- The composite of the morphisms presented by `f` at level `k` and by `g` at level `l` is
the morphism presented by `CategoryTheory.EndoColim.compHom k f l g` at level `B.stage + k + l`. -/
@[simp]
lemma Hom.comp_of_of {A B D : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) (l : ℕ)
    (g : (F.endoIter (D.stage + l)).obj B.obj ⟶ (F.endoIter (B.stage + l)).obj D.obj) :
    Hom.comp (Hom.of k f) (Hom.of l g) =
      Hom.of (B.stage + k + l) (compHom k f l g) :=
  rfl

/-- **The identity morphism of `colim_F C`**, presented at level `0` by the identity of `C`. -/
def Hom.id (A : EndoColim F) : Hom A A :=
  Hom.of 0 (𝟙 ((F.endoIter (A.stage + 0)).obj A.obj))

/-- **Composition of presentations is associative.** -/
lemma Hom.of_compHom_assoc {A B D W : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) (l : ℕ)
    (g : (F.endoIter (D.stage + l)).obj B.obj ⟶ (F.endoIter (B.stage + l)).obj D.obj) (o : ℕ)
    (h : (F.endoIter (W.stage + o)).obj D.obj ⟶ (F.endoIter (D.stage + o)).obj W.obj) :
    Hom.of (D.stage + (B.stage + k + l) + o)
        (compHom (B.stage + k + l) (compHom k f l g) o h) =
      Hom.of (B.stage + k + (D.stage + l + o))
        (compHom k f (D.stage + l + o) (compHom l g o h)) := by
  refine Hom.of_eq_of _ _ 0 0 (by omega) ?_
  simp only [compHom, endoRaise_zero, endoRaise_comp, endoRaise_endoHomCast,
    endoRaise_endoRaise, endoHomCast_comp_rfl, endoHomCast_endoHomCast, Category.assoc]
  apply endoHomCast_endoRaise_comp₃_eq <;> omega

/-- **The identity is a left unit for composition of presentations.** -/
lemma Hom.of_id_compHom {A B : EndoColim F} (l : ℕ)
    (g : (F.endoIter (B.stage + l)).obj A.obj ⟶ (F.endoIter (A.stage + l)).obj B.obj) :
    Hom.of (A.stage + 0 + l)
        (compHom 0 (𝟙 ((F.endoIter (A.stage + 0)).obj A.obj)) l g) = Hom.of l g := by
  refine Hom.of_eq_of _ _ 0 A.stage (by omega) ?_
  simp only [compHom, endoRaise_zero, endoRaise_id, endoHomCast_comp_rfl,
    endoHomCast_endoHomCast]
  apply endoHomCast_id_comp_eq
  omega

/-- **The identity is a right unit for composition of presentations.** -/
lemma Hom.of_compHom_id {A B : EndoColim F} (k : ℕ)
    (f : (F.endoIter (B.stage + k)).obj A.obj ⟶ (F.endoIter (A.stage + k)).obj B.obj) :
    Hom.of (B.stage + k + 0)
        (compHom k f 0 (𝟙 ((F.endoIter (B.stage + 0)).obj B.obj))) = Hom.of k f := by
  refine Hom.of_eq_of _ _ 0 B.stage (by omega) ?_
  simp only [compHom, endoRaise_zero, endoRaise_id, endoHomCast_comp_rfl,
    endoHomCast_endoHomCast]
  apply endoHomCast_comp_id_eq
  omega

/-- The identity is a left unit for composition in `colim_F C`. -/
lemma Hom.id_comp' {A B : EndoColim F} (u : Hom A B) : Hom.comp (Hom.id A) u = u := by
  induction u using Quot.ind with
  | _ x => exact Hom.of_id_compHom x.level x.hom

/-- The identity is a right unit for composition in `colim_F C`. -/
lemma Hom.comp_id' {A B : EndoColim F} (u : Hom A B) : Hom.comp u (Hom.id B) = u := by
  induction u using Quot.ind with
  | _ x => exact Hom.of_compHom_id x.level x.hom

/-- Composition in `colim_F C` is associative. -/
lemma Hom.comp_assoc {A B D W : EndoColim F} (u : Hom A B) (v : Hom B D) (w : Hom D W) :
    Hom.comp (Hom.comp u v) w = Hom.comp u (Hom.comp v w) := by
  obtain ⟨x⟩ := u
  obtain ⟨y⟩ := v
  obtain ⟨z⟩ := w
  exact Hom.of_compHom_assoc x.level x.hom y.level y.hom z.level z.hom

/-- **The iterate of a composite of morphisms of `C`, presented at level `0`, is the composite
of the presentations.** -/
lemma Hom.of_endoIter_map_comp (n : ℕ) {E G H : C} (f : E ⟶ G) (g : G ⟶ H) :
    (Hom.of 0 ((F.endoIter (n + 0)).map (f ≫ g)) : Hom (⟨E, n⟩ : EndoColim F) ⟨H, n⟩) =
      Hom.comp (B := (⟨G, n⟩ : EndoColim F))
        (Hom.of 0 ((F.endoIter (n + 0)).map f))
        (Hom.of 0 ((F.endoIter (n + 0)).map g)) := by
  rw [Hom.comp_of_of]
  refine Hom.of_eq_of _ _ n 0 (by simp) ?_
  simp only [compHom, Functor.map_comp, endoRaise_zero, endoRaise_comp, endoRaise_endoIter_map,
    endoHomCast_comp_rfl, endoHomCast_endoHomCast]
  apply endoHomCast_endoIter_map_comp_eq <;> omega

/-- **The colimit category `colim_F C` of Stacks 0EXA.** Its objects are the pairs `(E, n)` with
`E` an object of `C` and `n` a stage of the diagram `C →F C →F ⋯`, and its Hom-sets are the
colimits `colim_N Hom_C(F^{N - n}E, F^{N - m}G)`. -/
instance instCategory : Category.{v} (EndoColim F) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp'
  comp_id := Hom.comp_id'
  assoc := Hom.comp_assoc

/-- **The canonical functor from `C` into the colimit category at a stage.** It places an
object of `C` at the stage `n` and presents a morphism of `C` at level `0` by its `n`-th
iterate. -/
def stageFunctor (F : C ⥤ C) (n : ℕ) : C ⥤ EndoColim F where
  obj E := ⟨E, n⟩
  map f := Hom.of 0 ((F.endoIter (n + 0)).map f)
  map_id E := congrArg (Hom.of 0) ((F.endoIter (n + 0)).map_id E)
  map_comp f g := Hom.of_endoIter_map_comp n f g

end EndoColim

end CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **The category `colim_F Vect(X)` of Stacks Tag 0EXA**, in the explicit form the tag
describes it: an object is a finite locally free `𝒪_X`-module together with a stage `n ≥ 0`, and
`Hom((ℰ, n), (𝒢, m))` is the colimit over `N` of `Hom_X(F^{N - n, *}ℰ, F^{N - m, *}𝒢)`. -/
noncomputable abbrev frobeniusColimitVectModel : Type (u + 1) :=
  EndoColim (frobeniusPullback X p hX)

/-- The canonical functor from `Vect(X)` into `colim_F Vect(X)` at the stage `n`. -/
noncomputable abbrev frobeniusColimitVectModelStage (n : ℕ) :
    X.Vect ⥤ frobeniusColimitVectModel X p hX :=
  EndoColim.stageFunctor (frobeniusPullback X p hX) n

end AlgebraicGeometry

end
