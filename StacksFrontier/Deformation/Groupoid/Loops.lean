module

public import StacksFrontier.Deformation.Groupoid.Basic
public import Mathlib.CategoryTheory.Elements

/-!
# Loops of a groupoid in functors and their conjugation

Let `K` be a groupoid in functors on a category `D` (Stacks 06K3). Evaluating `K` at an object
`T` of `D` gives a groupoid whose objects are the elements of `K.objects.obj T` and whose arrows
are the elements of `K.arrows.obj T` with the prescribed endpoints. A *loop* at an object `x` of
that groupoid is an arrow from `x` to itself, recorded here as an element of the arrow functor
whose source and target are both `x`.

An arrow `f : x ⟶ y` of the evaluated groupoid conjugates loops at `x` into loops at `y` by
`a ↦ f⁻¹ a f`, and this is functorial in `f`. The resulting functor
`K.loopConjugationFunctor T` from the evaluated groupoid to types is the loop functor; its
category of elements is the groupoid whose objects are pairs consisting of an object and a loop
at it, which is the pointwise inertia of `K` at `T`.

## Main definitions

* `Deformation.GroupoidInFunctors.pointwiseLoops`: the loops at an object of an evaluation.
* `Deformation.GroupoidInFunctors.conjugateLoopMap`: conjugation of loops by an arrow.
* `Deformation.GroupoidInFunctors.loopConjugationFunctor`: the loop functor on an evaluation.

## Main results

* `Deformation.GroupoidInFunctors.conjugateLoopMap_val`: the arrow underlying a conjugated loop.
* `Deformation.GroupoidInFunctors.pointwiseLoops_val_cast`: transport of a loop along an
  equality of base points does not change its underlying arrow.

## Implementation notes

Loops are a subtype of the arrow functor rather than a `Quiver.Hom` of the evaluated groupoid,
because the evaluated groupoid's arrows are only identified with such a subtype through the
chosen equivalence `Deformation.GroupoidInFunctors.evaluationArrowEquiv`; phrasing loops on the
arrow functor keeps the functor below independent of that choice on objects. Conjugation is
nevertheless defined by passing through the equivalence, since `a ↦ f⁻¹ a f` is a statement
about composition in the groupoid.
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory
universe u v w

namespace GroupoidInFunctors

variable {D : Type u} [Category.{v} D]

/-- Composition of generalized arrows depends only on the two arrows, not on the proof that they
are composable. -/
theorem compose_congr (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    {a b a' b' : K.arrows.obj T} (w : K.source.app T a = K.target.app T b)
    (w' : K.source.app T a' = K.target.app T b') (ha : a = a') (hb : b = b') :
    K.compose T a b w = K.compose T a' b' w' :=
  congrArg (K.comp.app T) (Subtype.ext (Prod.ext ha hb))

/-- The arrow underlying the morphism of an evaluation represented by a given arrow of the arrow
functor is that arrow again.

This is `Equiv.apply_symm_apply` for
`Deformation.GroupoidInFunctors.evaluationArrowEquiv`, read on underlying arrows. It is stated
rather than used inline because the two sides of `Equiv.apply_symm_apply` are separated here by
the `Subtype.val` of the endpoint conditions, and `simp` will not rewrite under it without
knowing that the two copies of the equivalence are the same one. -/
theorem evaluationArrowEquiv_symm_val (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y : K.Evaluation T}
    (a : { a : K.arrows.obj T // K.source.app T a = x ∧ K.target.app T a = y }) :
    (K.evaluationArrowEquiv T x y ((K.evaluationArrowEquiv T x y).symm a)).1 = a.1 :=
  congrArg Subtype.val (Equiv.apply_symm_apply (K.evaluationArrowEquiv T x y) a)

/-- A loop at an object `x` of an evaluation of a groupoid in functors: an arrow of the groupoid
whose source and target are both `x`.

Marked `@[implicit_reducible]`, as `Deformation.GroupoidInFunctors.Evaluation` and
`Deformation.GroupoidInFunctors.compose` are: a loop is *the* subtype of the arrow functor cut
out by the two endpoint conditions, and unification has to see that in order to feed a loop to
`Deformation.GroupoidInFunctors.evaluationArrowEquiv`, whose codomain is that subtype
written out. -/
@[implicit_reducible]
def pointwiseLoops (K : GroupoidInFunctors.{u, v, w} D) (T : D) (x : K.Evaluation T) :=
  { a : K.arrows.obj T // K.source.app T a = x ∧ K.target.app T a = x }

/-- Transporting a loop along an equality of its base point does not change the underlying
arrow. -/
theorem pointwiseLoops_val_cast (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y : K.Evaluation T} (h : x = y) (a : pointwiseLoops K T x) :
    (cast (congrArg (pointwiseLoops K T) h) a).1 = a.1 := by
  cases h
  rfl

/-- Conjugation of loops by an arrow `f : x ⟶ y` of an evaluation: the loop `a` at `x` is sent
to the loop `f⁻¹ a f` at `y`. -/
noncomputable def conjugateLoopMap (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y : K.Evaluation T} (f : x ⟶ y) : pointwiseLoops K T x → pointwiseLoops K T y := fun a =>
  let β := Groupoid.inv f ≫ (K.evaluationArrowEquiv T x x).symm a ≫ f
  ⟨(K.evaluationArrowEquiv T y y β).1, (K.evaluationArrowEquiv T y y β).2.1,
    (K.evaluationArrowEquiv T y y β).2.2⟩

/-- The arrow underlying the conjugate of a loop. -/
theorem conjugateLoopMap_val (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y : K.Evaluation T} (f : x ⟶ y) (a : pointwiseLoops K T x) :
    (conjugateLoopMap K T f a).1 =
      (K.evaluationArrowEquiv T y y
        (Groupoid.inv f ≫ (K.evaluationArrowEquiv T x x).symm a ≫ f)).1 :=
  rfl

/-- Conjugation by an identity arrow is the identity on loops. -/
theorem conjugateLoopMap_id (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    (x : K.Evaluation T) (a : pointwiseLoops K T x) :
    (conjugateLoopMap K T (𝟙 x) a).1 = a.1 := by
  rw [conjugateLoopMap_val]
  simp

/-- Conjugation by a composite is conjugation by the factors in turn. -/
theorem conjugateLoopMap_comp (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y z : K.Evaluation T} (f : x ⟶ y) (g : y ⟶ z) (a : pointwiseLoops K T x) :
    (conjugateLoopMap K T (f ≫ g) a).1 =
      (conjugateLoopMap K T g (conjugateLoopMap K T f a)).1 := by
  set α := (K.evaluationArrowEquiv T x x).symm a with hα
  have hcat : Groupoid.inv (f ≫ g) ≫ α ≫ (f ≫ g) =
      Groupoid.inv g ≫ (Groupoid.inv f ≫ α ≫ f) ≫ g := by
    simp [Category.assoc, IsIso.inv_comp]
  have hαf : (K.evaluationArrowEquiv T y y).symm (conjugateLoopMap K T f a) =
      Groupoid.inv f ≫ α ≫ f := by
    apply (K.evaluationArrowEquiv T y y).injective
    apply Subtype.ext
    rw [Equiv.apply_symm_apply, conjugateLoopMap_val, hα]
  rw [conjugateLoopMap_val, conjugateLoopMap_val, hαf, ← hα]
  exact congrArg (fun q => (K.evaluationArrowEquiv T z z q).1) hcat

/-- The loop functor of an evaluation of a groupoid in functors: an object is sent to the type
of loops at it, and an arrow to conjugation of loops by that arrow. -/
noncomputable def loopConjugationFunctor (K : GroupoidInFunctors.{u, v, w} D) (T : D) :
    K.Evaluation T ⥤ Type w where
  obj := pointwiseLoops K T
  map {_ _} f := ↾ (conjugateLoopMap K T f)
  map_id x := by
    ext a
    exact Subtype.ext (conjugateLoopMap_id K T x a)
  map_comp f g := by
    ext a
    exact Subtype.ext (conjugateLoopMap_comp K T f g a)

/-- The loop functor sends an object to the type of loops at it. -/
@[simp]
theorem loopConjugationFunctor_obj (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    (x : K.Evaluation T) : (loopConjugationFunctor K T).obj x = pointwiseLoops K T x :=
  rfl

/-- The loop functor sends an arrow to conjugation of loops by that arrow. -/
theorem loopConjugationFunctor_map_val (K : GroupoidInFunctors.{u, v, w} D) (T : D)
    {x y : K.Evaluation T} (f : x ⟶ y) (a : pointwiseLoops K T x) :
    ((loopConjugationFunctor K T).map f a).1 = (conjugateLoopMap K T f a).1 :=
  rfl

end GroupoidInFunctors

end

end Deformation

end
