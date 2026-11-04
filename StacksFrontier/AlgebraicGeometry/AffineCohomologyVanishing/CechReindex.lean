module

public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# The Čech complex is insensitive to lifting the index type

Mathlib's `CategoryTheory.cechComplexFunctor` is attached to a family `U : ι → C` whose index
type `ι` must lie in the universe of the products available in the coefficient category. Two
statements about the same covering family can therefore be indexed by types in different
universes, and must be compared before one can be used to prove the other. This file supplies
that comparison for the universe lift: the Čech complex of `U` and the Čech complex of the
family reindexed by `ULift ι` are isomorphic as cochain complexes, hence have the same
cohomology.

## Main definitions

* `πUlift` and `πUnlift` are the projections of the two complexes, each at the type that the
  *other* complex ascribes to it.
* `uliftDown` and `uliftUp` are the degreewise comparison maps.
* `uliftComplexIso` assembles them into an isomorphism of cochain complexes.

## Main results

* `isZero_homology_of_ulift` transports the vanishing of a Čech cohomology group along the
  reindexing.

## Implementation notes

The index tuples of the two complexes correspond under `ULift.up` and `ULift.down`, and the
intersection selected by a tuple of lifted indices is *literally* the intersection selected by
the underlying tuple, because `ULift.up i.down` and `i` are definitionally equal. The
comparison maps are therefore built directly from the universal property of the degreewise
products, through `Stacks.CategoryTheory.CechComplex.lift` and
`Stacks.CategoryTheory.CechComplex.π`.

That definitional identification is not visible to `rw`, which requires its intermediate terms
to be type-correct at `implicit` transparency while `inter` is semireducible. So each
projection is given a *name* at the type the other complex ascribes to it — `πUlift` and
`πUnlift` — and `πUlift_eq_π` and `πUnlift_eq_π` are the two bridges between the names. Every
identity below is then an equation between terms that are already type-correct as written, and
no transport or `eqToHom` appears.

## References

* [Stacks Project, Tag 01FG](https://stacks.math.columbia.edu/tag/01FG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v v' u u'

namespace Stacks.CategoryTheory.CechComplex

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasFiniteProducts C] [Preadditive A] [HasProducts.{w} A] [HasProducts.{max w t} A]
  {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ A)

/-- The projection of the degree `n` term of the Čech complex of the family reindexed by
`ULift ι` onto the factor indexed by the lift of a tuple `x : Fin (n + 1) → ι`. Its target is
the sections over `inter U x`, because the intersection selected by the lifted tuple *is* the
intersection selected by `x`. -/
noncomputable def πUlift (n : ℕ) (x : Fin (n + 1) → ι) :
    ((cechComplexFunctor fun i : ULift.{t} ι ↦ U i.down).obj P).X n ⟶ P.obj (op (inter U x)) :=
  π (fun i : ULift.{t} ι ↦ U i.down) P n fun a ↦ ULift.up (x a)

/-- The projection of the degree `n` term of the Čech complex of `U` onto the factor indexed by
the tuple underlying a tuple `y : Fin (n + 1) → ULift ι` of lifted indices. Its target is the
sections over the intersection selected by `y` in the reindexed family. -/
noncomputable def πUnlift (n : ℕ) (y : Fin (n + 1) → ULift.{t} ι) :
    ((cechComplexFunctor U).obj P).X n ⟶
      P.obj (op (inter (fun i : ULift.{t} ι ↦ U i.down) y)) :=
  π U P n fun a ↦ (y a).down

omit [HasProducts.{w} A] in
/-- `πUlift` at the tuple underlying `y` is the projection of the reindexed complex at `y`. -/
theorem πUlift_eq_π (n : ℕ) (y : Fin (n + 1) → ULift.{t} ι) :
    πUlift.{t} U P n (fun a ↦ (y a).down) =
      π (fun i : ULift.{t} ι ↦ U i.down) P n y :=
  rfl

omit [HasProducts.{max w t} A] in
/-- `πUnlift` at the lift of `x` is the projection of the complex of `U` at `x`. -/
theorem πUnlift_eq_π (n : ℕ) (x : Fin (n + 1) → ι) :
    πUnlift.{t} U P n (fun a ↦ ULift.up (x a)) = π U P n x :=
  rfl

/-- The degree `n` comparison map from the Čech complex of the family reindexed by `ULift ι`
to the Čech complex of `U`. -/
noncomputable def uliftDown (n : ℕ) :
    ((cechComplexFunctor fun i : ULift.{t} ι ↦ U i.down).obj P).X n ⟶
      ((cechComplexFunctor U).obj P).X n :=
  lift U P (πUlift.{t} U P n)

/-- The degree `n` comparison map from the Čech complex of `U` to the Čech complex of the
family reindexed by `ULift ι`. -/
noncomputable def uliftUp (n : ℕ) :
    ((cechComplexFunctor U).obj P).X n ⟶
      ((cechComplexFunctor fun i : ULift.{t} ι ↦ U i.down).obj P).X n :=
  lift (fun i : ULift.{t} ι ↦ U i.down) P (πUnlift.{t} U P n)

/-- `uliftDown` followed by the projection of the complex of `U` at `x` is `πUlift` at `x`. -/
@[reassoc (attr := simp)]
theorem uliftDown_comp_π (n : ℕ) (x : Fin (n + 1) → ι) :
    uliftDown.{t} U P n ≫ π U P n x = πUlift.{t} U P n x :=
  lift_comp_π U P _ x

/-- `uliftUp` followed by the projection of the reindexed complex at `y` is `πUnlift` at `y`. -/
@[reassoc (attr := simp)]
theorem uliftUp_comp_π (n : ℕ) (y : Fin (n + 1) → ULift.{t} ι) :
    uliftUp.{t} U P n ≫ π (fun i : ULift.{t} ι ↦ U i.down) P n y = πUnlift.{t} U P n y :=
  lift_comp_π _ P _ y

/-- `uliftDown` followed by `πUnlift` at `y` is the projection of the reindexed complex
at `y`. -/
@[reassoc]
theorem uliftDown_comp_πUnlift (n : ℕ) (y : Fin (n + 1) → ULift.{t} ι) :
    uliftDown.{t} U P n ≫ πUnlift.{t} U P n y =
      π (fun i : ULift.{t} ι ↦ U i.down) P n y :=
  (uliftDown_comp_π.{t} U P n fun a ↦ (y a).down).trans (πUlift_eq_π.{t} U P n y)

/-- `uliftUp` followed by `πUlift` at `x` is the projection of the complex of `U` at `x`. -/
@[reassoc]
theorem uliftUp_comp_πUlift (n : ℕ) (x : Fin (n + 1) → ι) :
    uliftUp.{t} U P n ≫ πUlift.{t} U P n x = π U P n x :=
  (uliftUp_comp_π.{t} U P n fun a ↦ ULift.up (x a)).trans (πUnlift_eq_π.{t} U P n x)

/-- `uliftDown` followed by `uliftUp` is the identity, in each degree. -/
theorem uliftDown_comp_uliftUp (n : ℕ) :
    uliftDown.{t} U P n ≫ uliftUp.{t} U P n = 𝟙 _ :=
  hom_ext _ P fun y ↦ by
    rw [Category.assoc, uliftUp_comp_π, uliftDown_comp_πUnlift, Category.id_comp]

/-- `uliftUp` followed by `uliftDown` is the identity, in each degree. -/
theorem uliftUp_comp_uliftDown (n : ℕ) :
    uliftUp.{t} U P n ≫ uliftDown.{t} U P n = 𝟙 _ :=
  hom_ext U P fun x ↦ by
    rw [Category.assoc, uliftDown_comp_π, uliftUp_comp_πUlift, Category.id_comp]

omit [HasProducts.{w} A] in
/-- **The Čech differential against `πUlift`.** The same alternating-sum formula as
`Stacks.CategoryTheory.CechComplex.d_comp_π`, for the reindexed complex read through the
projections `πUlift`. -/
theorem d_comp_πUlift (n : ℕ) (y : Fin (n + 2) → ι) :
    ((cechComplexFunctor fun i : ULift.{t} ι ↦ U i.down).obj P).d n (n + 1) ≫
        πUlift.{t} U P (n + 1) y =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (πUlift.{t} U P n (y ∘ i.succAbove) ≫ P.map (interMap U y i.succAbove).op) :=
  d_comp_π (fun i : ULift.{t} ι ↦ U i.down) P n fun a ↦ ULift.up (y a)

/-- The comparison maps `uliftDown` commute with the Čech differentials. -/
theorem uliftDown_comp_d (n : ℕ) :
    uliftDown.{t} U P n ≫ ((cechComplexFunctor U).obj P).d n (n + 1) =
      ((cechComplexFunctor fun i : ULift.{t} ι ↦ U i.down).obj P).d n (n + 1) ≫
        uliftDown.{t} U P (n + 1) :=
  hom_ext U P fun y ↦ by
    rw [Category.assoc, d_comp_π, Preadditive.comp_sum, Category.assoc, uliftDown_comp_π,
      d_comp_πUlift]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Preadditive.comp_zsmul, ← Category.assoc, uliftDown_comp_π]

/-- The degreewise comparison maps assembled into a morphism of cochain complexes. -/
noncomputable def uliftDownHom :
    (cechComplexFunctor fun i : ULift.{t} ι ↦ U i.down).obj P ⟶
      (cechComplexFunctor U).obj P where
  f := uliftDown.{t} U P
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    exact uliftDown_comp_d.{t} U P i

/-- Each degreewise comparison map `uliftDown` is an isomorphism, with inverse `uliftUp`. -/
theorem isIso_uliftDown (n : ℕ) : IsIso (uliftDown.{t} U P n) :=
  ⟨uliftUp.{t} U P n, uliftDown_comp_uliftUp.{t} U P n, uliftUp_comp_uliftDown.{t} U P n⟩

/-- **The Čech complex does not change when the index type is lifted.** The Čech complex of
the family `U` reindexed by `ULift ι` is isomorphic, as a cochain complex, to the Čech complex
of `U`. -/
noncomputable def uliftComplexIso :
    (cechComplexFunctor fun i : ULift.{t} ι ↦ U i.down).obj P ≅
      (cechComplexFunctor U).obj P :=
  haveI (n : ℕ) : IsIso ((uliftDownHom.{t} U P).f n) := isIso_uliftDown.{t} U P n
  haveI := HomologicalComplex.Hom.isIso_of_components (uliftDownHom.{t} U P)
  asIso (uliftDownHom.{t} U P)

/-- Vanishing of a Čech cohomology group is unaffected by lifting the index type of the
family. -/
theorem isZero_homology_of_ulift [CategoryWithHomology A] (n : ℕ)
    (h : IsZero (((cechComplexFunctor U).obj P).homology n)) :
    IsZero
      (((cechComplexFunctor fun i : ULift.{t} ι ↦ U i.down).obj P).homology n) :=
  h.of_iso (HomologicalComplex.homologyMapIso (uliftComplexIso.{t} U P) n)

end Stacks.CategoryTheory.CechComplex

end
