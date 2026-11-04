module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Descent data from transitions over a class of test objects

Let `F` be a pseudofunctor from `LocallyDiscrete Dᵒᵖ` to `Cat` and let `f i : X i ⟶ S` be a family
of morphisms of `D`.  Mathlib's `CategoryTheory.Pseudofunctor.DescentData` asks for transition
morphisms over **every** object of `D` mapping to two members of the family.  In practice the
transitions are often only available over a smaller class of *test objects* — for a site of
schemes over `S`, over the schemes underlying the objects of the site — and the class is large
enough when it contains chosen fibre products of two and of three members.

This file packages that situation.  The test objects are indexed by a type `C` together with a
map `X : C → D` and structure morphisms `q T : X T ⟶ S`; the members of the family are test
objects `V i`.  `Stacks.Descent.TestTransitions` is a family of transitions over the test objects
satisfying the three laws of a descent datum there, and `Stacks.Descent.TestPullbacks` is a choice
of fibre products of two and of three members among the test objects.  Together they give an
object of `CategoryTheory.Pseudofunctor.DescentData'` on those fibre products, hence a descent
datum, whose transitions over a test object are the given ones.

## Main definitions

* `Stacks.Descent.TestTransitions`: transitions over the test objects, with the three laws.
* `Stacks.Descent.TestPullbacks`: fibre products of two and three members among the test
  objects.
* `Stacks.Descent.TestPullbacks.chosenPullback` and `…chosenPullback₃`: those fibre products as
  `CategoryTheory.Limits.ChosenPullback` and `CategoryTheory.Limits.ChosenPullback₃`.
* `Stacks.Descent.TestTransitions.descentData'`: the resulting object of
  `CategoryTheory.Pseudofunctor.DescentData'`.

## Main results

* `Stacks.Descent.TestTransitions.descentData_hom`: the transitions of the resulting descent
  datum over a test object are the given transitions.

## Implementation notes

The transitions are indexed by morphisms of `D` and not by morphisms between the test objects,
so the three laws of `CategoryTheory.Pseudofunctor.DescentData'` are instances of the given laws
with no transport along equalities of morphisms: the identity law is the pullback law along the
diagonal followed by the identity law, and the cocycle law is the pullback law along the three
projections of the threefold fibre product followed by the composition law.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe t w v' v u' u

namespace Stacks.Descent

variable {D : Type u} [Category.{v} D] (F : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat.{v', u'})
  {S : D} {C : Type w} (X : C → D) (q : ∀ T, X T ⟶ S)
  {ι : Type t} (V : ι → C) (obj : ∀ i, F.obj (.mk (op (X (V i)))))

/-- **Transitions over test objects.**  For every test object `T` and every pair of morphisms
from its underlying object to two members of the family over `S`, a morphism between the two
pullbacks, subject to the three laws of a descent datum: compatibility with pullback along a
morphism of underlying objects over `S`, the identity law and the composition law. -/
structure TestTransitions where
  /-- The transition over a test object. -/
  τ (T : C) ⦃i j : ι⦄ (α : X T ⟶ X (V i)) (β : X T ⟶ X (V j))
    (hα : α ≫ q (V i) = q T) (hβ : β ≫ q (V j) = q T) :
    (F.map α.op.toLoc).toFunctor.obj (obj i) ⟶ (F.map β.op.toLoc).toFunctor.obj (obj j)
  /-- The transitions are compatible with pullback. -/
  pullHom_τ (T T' : C) (c : X T' ⟶ X T) (hc : c ≫ q T = q T') ⦃i j : ι⦄
    (α : X T ⟶ X (V i)) (β : X T ⟶ X (V j)) (hα : α ≫ q (V i) = q T)
    (hβ : β ≫ q (V j) = q T) (α' : X T' ⟶ X (V i)) (β' : X T' ⟶ X (V j))
    (h₁ : c ≫ α = α') (h₂ : c ≫ β = β') :
    pullHom (τ T α β hα hβ) c α' β' h₁ h₂ =
      τ T' α' β' (by rw [← h₁, Category.assoc, hα, hc]) (by rw [← h₂, Category.assoc, hβ, hc])
  /-- The identity law. -/
  τ_self (T : C) ⦃i : ι⦄ (α : X T ⟶ X (V i)) (hα : α ≫ q (V i) = q T) :
    τ T α α hα hα = 𝟙 _
  /-- The composition law. -/
  τ_comp (T : C) ⦃i j k : ι⦄ (α : X T ⟶ X (V i)) (β : X T ⟶ X (V j)) (γ : X T ⟶ X (V k))
    (hα : α ≫ q (V i) = q T) (hβ : β ≫ q (V j) = q T) (hγ : γ ≫ q (V k) = q T) :
    τ T α β hα hβ ≫ τ T β γ hβ hγ = τ T α γ hα hγ

/-- **Fibre products of two and of three members of the family among the test objects.** -/
structure TestPullbacks where
  /-- The fibre product of two members. -/
  P (i j : ι) : C
  /-- Its first projection. -/
  p₁ (i j : ι) : X (P i j) ⟶ X (V i)
  /-- Its second projection. -/
  p₂ (i j : ι) : X (P i j) ⟶ X (V j)
  isPullback (i j : ι) : IsPullback (p₁ i j) (p₂ i j) (q (V i)) (q (V j))
  p₁_q (i j : ι) : p₁ i j ≫ q (V i) = q (P i j)
  /-- The fibre product of three members. -/
  P₃ (i j k : ι) : C
  /-- Its projection to the fibre product of the first two members. -/
  r₁₂ (i j k : ι) : X (P₃ i j k) ⟶ X (P i j)
  /-- Its projection to the fibre product of the last two members. -/
  r₂₃ (i j k : ι) : X (P₃ i j k) ⟶ X (P j k)
  isPullback₃ (i j k : ι) : IsPullback (r₁₂ i j k) (r₂₃ i j k) (p₂ i j) (p₁ j k)
  r₁₂_q (i j k : ι) : r₁₂ i j k ≫ q (P i j) = q (P₃ i j k)

namespace TestPullbacks

variable {F X q V} (Q : TestPullbacks X q V)

/-- The second projection of the fibre product of two members lies over `S`. -/
lemma p₂_q (i j : ι) : Q.p₂ i j ≫ q (V j) = q (Q.P i j) := by
  rw [← (Q.isPullback i j).w, Q.p₁_q]

/-- The fibre product of two members, as a chosen pullback. -/
noncomputable def chosenPullback (i j : ι) : ChosenPullback (q (V i)) (q (V j)) where
  pullback := X (Q.P i j)
  p₁ := Q.p₁ i j
  p₂ := Q.p₂ i j
  condition := (Q.isPullback i j).w
  isLimit := (Q.isPullback i j).isLimit
  p := q (Q.P i j)
  hp₁ := Q.p₁_q i j

/-- The two composites from the threefold fibre product to the outer members agree over `S`. -/
lemma lift₁₃_w (i j k : ι) :
    (Q.r₁₂ i j k ≫ Q.p₁ i j) ≫ q (V i) = (Q.r₂₃ i j k ≫ Q.p₂ j k) ≫ q (V k) := by
  rw [Category.assoc, Category.assoc, (Q.isPullback i j).w, ← (Q.isPullback j k).w,
    ← Category.assoc, ← Category.assoc, (Q.isPullback₃ i j k).w]

/-- The fibre product of three members, as a chosen threefold wide pullback. -/
noncomputable def chosenPullback₃ (i j k : ι) :
    ChosenPullback₃ (Q.chosenPullback i j) (Q.chosenPullback j k) (Q.chosenPullback i k) where
  chosenPullback :=
    { pullback := X (Q.P₃ i j k)
      p₁ := Q.r₁₂ i j k
      p₂ := Q.r₂₃ i j k
      condition := (Q.isPullback₃ i j k).w
      isLimit := (Q.isPullback₃ i j k).isLimit }
  p := q (Q.P₃ i j k)
  l :=
    { f := (Q.isPullback i k).lift (Q.r₁₂ i j k ≫ Q.p₁ i j) (Q.r₂₃ i j k ≫ Q.p₂ j k)
        (Q.lift₁₃_w i j k)
      f_p₁ := (Q.isPullback i k).lift_fst _ _ _
      f_p₂ := (Q.isPullback i k).lift_snd _ _ _
      f_p := by
        change _ ≫ q (Q.P i k) = q (Q.P₃ i j k)
        rw [← Q.p₁_q, ← Category.assoc, (Q.isPullback i k).lift_fst, Category.assoc,
          Q.p₁_q, Q.r₁₂_q] }
  hp₁ := rfl
  hp₃ := rfl

end TestPullbacks

namespace TestTransitions

variable {F X q V obj} (Θ : TestTransitions F X q V obj) (Q : TestPullbacks X q V)

/-- The transitions over the chosen fibre products of two members. -/
noncomputable def hom (i j : ι) :
    (F.map (Q.chosenPullback i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (Q.chosenPullback i j).p₂.op.toLoc).toFunctor.obj (obj j) :=
  Θ.τ (Q.P i j) (Q.p₁ i j) (Q.p₂ i j) (Q.p₁_q i j) (Q.p₂_q i j)

/-- **The transitions over the chosen fibre products, read at an arbitrary test object**, are
the given transitions there. -/
lemma pullHom'_hom (T : C) ⦃i j : ι⦄ (α : X T ⟶ X (V i)) (β : X T ⟶ X (V j))
    (hα : α ≫ q (V i) = q T) (hβ : β ≫ q (V j) = q T) :
    DescentData'.pullHom' (sq := Q.chosenPullback) (Θ.hom Q) (q T) α β hα hβ =
      Θ.τ T α β hα hβ := by
  have hw : α ≫ q (V i) = β ≫ q (V j) := hα.trans hβ.symm
  rw [DescentData'.pullHom'_eq_pullHom (sq := Q.chosenPullback) (Θ.hom Q) (q T) α β
    ((Q.isPullback i j).lift α β hw) hα hβ ((Q.isPullback i j).lift_fst _ _ _)
    ((Q.isPullback i j).lift_snd _ _ _)]
  exact Θ.pullHom_τ (Q.P i j) T _ (by
    rw [← Q.p₁_q, ← Category.assoc, (Q.isPullback i j).lift_fst, hα]) _ _ _ _ α β _ _

/-- **The descent datum on the chosen fibre products defined by transitions over test
objects.** -/
noncomputable def descentData' :
    F.DescentData' Q.chosenPullback Q.chosenPullback₃ where
  obj := obj
  hom := Θ.hom Q
  pullHom'_hom_self i := (Θ.pullHom'_hom Q (V i) (𝟙 _) (𝟙 _) (Category.id_comp _)
    (Category.id_comp _)).trans (Θ.τ_self (V i) (𝟙 _) (Category.id_comp _))
  pullHom'_hom_comp i j k := by
    have h₁ := Θ.pullHom'_hom Q (Q.P₃ i j k) (Q.chosenPullback₃ i j k).p₁
      (Q.chosenPullback₃ i j k).p₂ (Q.chosenPullback₃ i j k).w₁ (Q.chosenPullback₃ i j k).w₂
    have h₂ := Θ.pullHom'_hom Q (Q.P₃ i j k) (Q.chosenPullback₃ i j k).p₂
      (Q.chosenPullback₃ i j k).p₃ (Q.chosenPullback₃ i j k).w₂ (Q.chosenPullback₃ i j k).w₃
    have h₃ := Θ.pullHom'_hom Q (Q.P₃ i j k) (Q.chosenPullback₃ i j k).p₁
      (Q.chosenPullback₃ i j k).p₃ (Q.chosenPullback₃ i j k).w₁ (Q.chosenPullback₃ i j k).w₃
    exact (congrArg₂ (· ≫ ·) h₁ h₂).trans ((Θ.τ_comp _ _ _ _ _ _ _).trans h₃.symm)

/-- **The transitions of the descent datum over a test object are the given transitions.** -/
lemma descentData_hom (T : C) ⦃i j : ι⦄ (α : X T ⟶ X (V i)) (β : X T ⟶ X (V j))
    (hα : α ≫ q (V i) = q T) (hβ : β ≫ q (V j) = q T) :
    (Θ.descentData' Q).descentData.hom (q T) α β hα hβ = Θ.τ T α β hα hβ :=
  Θ.pullHom'_hom Q T α β hα hβ

end TestTransitions

end Stacks.Descent

end
