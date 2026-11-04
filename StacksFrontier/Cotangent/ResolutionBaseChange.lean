module

public import StacksFrontier.Cotangent.PolynomialAlgebraSiteBaseChange
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteSmall
public import StacksFrontier.Cotangent.ResolutionPointCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# Base change of an augmented simplicial algebra

Let
```
A  --→  A'
|       |
B  --→  B'
```
be a commutative square of rings and let `ε : P_• ⟶ B` be an augmented simplicial `A`-algebra.
Extension of scalars turns it into an augmented simplicial `A'`-algebra `A' ⊗_A P_• ⟶ B'`, whose
term in degree `n` is `A' ⊗_A P_n` and whose augmentation sends `a' ⊗ p` to `a' · b(ε_n(p))`.
This file builds that base change and records what survives it: the terms stay polynomial
algebras, on the *same* sets of variables, so the cardinality bound of the footnote to the
source's section is preserved as well; and the augmentation stays degreewise surjective as soon
as `B ⊗_A A' → B'` is surjective.

What does *not* survive formally is the resolution property: `A' ⊗_A P_• ⟶ B'` is a resolution
only under the hypothesis of **Stacks 08QP**, that the square induce a quasi-isomorphism
`B ⊗_A^L A' = B'`. That implication is not proved here — see the implementation note.

## Main definitions

* `CommAlgCat.augmentationOfOver`: a simplicial object of `Over B`, read as an augmented
  simplicial algebra. This is the inverse of `CommAlgCat.resolutionOver`, on the nose.
* `CommAlgCat.simplicialBaseChange` and `CommAlgCat.augmentationBaseChange`: the base change
  `A' ⊗_A P_• ⟶ B'` of an augmented simplicial `A`-algebra.

## Main results

* `CommAlgCat.resolutionOver_augmentationBaseChange`: the base-changed augmentation, read back as
  a simplicial object of `Over B'`, is the termwise base change of the original. This is the
  equality that makes the base-changed augmentation interchangeable with the functor
  `CommAlgCat.baseChangeOver` of Stacks 08QN, and it holds by definitional unfolding.
* `CommAlgCat.isPolynomialAlgebra_simplicialBaseChange` and
  `CommAlgCat.isPolynomialAlgebraBelow_simplicialBaseChange`: the terms of the base change are
  polynomial algebras over `A'`, on the same sets of variables, hence of the same cardinality.
* `CommAlgCat.surjective_augmentationBaseChange`: the base-changed augmentation is degreewise
  surjective as soon as `ε` is surjective in degree zero and `B ⊗_A A' → B'` is surjective.

## Implementation notes

**The augmentation is built from the `Over` picture, not degreewise.** `CommAlgCat.resolutionOver`
turns an augmented simplicial algebra into a simplicial object of `Over B`; `baseChangeOver` of
Stacks 08QN pushes that to a simplicial object of `Over B'`; and
`CommAlgCat.augmentationOfOver` reads the result back as an augmented simplicial algebra. Going
round the loop is the identity (`CommAlgCat.resolutionOver_augmentationOfOver`), so the
base-changed augmentation satisfies `resolutionOver (A' ⊗_A ε) = resolutionOver ε ⋙
baseChangeOver b` by `rfl` and no transport is needed anywhere downstream. Building the
augmentation degreewise instead would force a naturality proof by induction on tensors and leave
that equality only up to isomorphism.

**Degreewise surjectivity reduces to degree zero.** The target of the augmentation is a
*constant* simplicial algebra, so for any map `f : ⦋n⦌ ⟶ ⦋0⦌` of the simplex category the square
for `f` says that `P_0 → P_n → B` is the degree-zero augmentation. Hence surjectivity in degree
zero gives it in every degree, with no reference to the simplicial identities.

### No `@[stacks 08QP]`

Tag 08QP concludes `Lπ_!(g^{-1}ℱ') = Lπ'_!(ℱ')` from the hypothesis that the square induce a
quasi-isomorphism `B ⊗_A^L A' = B'`. Its proof has two halves: the hypothesis implies that
`A' ⊗_A P_• ⟶ B'` is again a resolution, and the criterion of Tag 08QA then identifies the two
derived lower shrieks. The second half is
`CommAlgCat.leftDerivedColimitPolynomialBaseChangeNatIso` in
`StacksFrontier/Cotangent/PolynomialSiteBaseChangeShriek.lean`, which carries the tag with a label
saying exactly that it assumes the first half. The first half is **not** proved, here or
anywhere: it needs that the Moore complex `s(P_•)` of a resolution, being a complex of free
`A`-modules quasi-isomorphic to `B`, is a free resolution computing
`H_n(s(P_•) ⊗_A A') = Tor_n^A(B, A')`, and no such identification is available — see the second
implementation note of `StacksFrontier/Cotangent/PolynomialSiteBaseChangeShriek.lean` for the
declarations it would need.

## References

* [Stacks Project, Tag 08QP](https://stacks.math.columbia.edu/tag/08QP)
* [Stacks Project, Tag 08QN](https://stacks.math.columbia.edu/tag/08QN)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace CommAlgCat

/-! ### Augmented simplicial algebras and simplicial objects over the target -/

section OfOver

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}

/-- A simplicial object of `Over B`, read as an augmented simplicial `A`-algebra: the underlying
simplicial algebra is the composite with `Over.forget B`, and the augmentation in degree `n` is
the structure morphism of the `n`-th term, which is natural by `Over.w`. -/
def augmentationOfOver (X : SimplexCategoryᵒᵖ ⥤ Over B) :
    (X ⋙ Over.forget B) ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B where
  app n := (X.obj n).hom
  naturality _ _ f := by simp [Over.w (X.map f)]

/-- Reading a simplicial object of `Over B` as an augmented simplicial algebra and back is the
identity. -/
@[simp]
lemma resolutionOver_augmentationOfOver (X : SimplexCategoryᵒᵖ ⥤ Over B) :
    resolutionOver (augmentationOfOver X) = X := rfl

/-- The augmentation of `CommAlgCat.augmentationOfOver` in degree `n` is the structure morphism of
the `n`-th term. -/
@[simp]
lemma augmentationOfOver_app (X : SimplexCategoryᵒᵖ ⥤ Over B) (n : SimplexCategoryᵒᵖ) :
    (augmentationOfOver X).app n = (X.obj n).hom := rfl

end OfOver

/-! ### Base change -/

section BaseChange

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'}
  [Algebra A (B' : Type u)] [IsScalarTower A A' (B' : Type u)]
  (b : (B : Type u) →ₐ[A] (B' : Type u))
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)

/-- The base change `A' ⊗_A P_•` of a simplicial `A`-algebra augmented to `B`, as a simplicial
`A'`-algebra: the term in degree `n` is `A' ⊗_A P_n`. -/
abbrev simplicialBaseChange : SimplicialObject (CommAlgCat.{u} A') :=
  (resolutionOver ε ⋙ baseChangeOver b) ⋙ Over.forget B'

/-- The base change `A' ⊗_A P_• ⟶ B'` of an augmented simplicial `A`-algebra: the augmentation in
degree `n` sends `a' ⊗ p` to `a' · b(ε_n(p))`. -/
abbrev augmentationBaseChange :
    simplicialBaseChange b ε ⟶ (SimplicialObject.const (CommAlgCat.{u} A')).obj B' :=
  augmentationOfOver (resolutionOver ε ⋙ baseChangeOver b)

/-- The base-changed augmentation, read back as a simplicial object of `Over B'`, is the termwise
base change of the original. -/
@[simp]
lemma resolutionOver_augmentationBaseChange :
    resolutionOver (augmentationBaseChange b ε) = resolutionOver ε ⋙ baseChangeOver b := rfl

/-- The `n`-th term of `CommAlgCat.resolutionOver`, read in `Over B`, has the augmentation `ε_n`
as its structure morphism. -/
@[simp]
lemma resolutionOver_obj_hom (n : SimplexCategoryᵒᵖ) :
    ((resolutionOver ε).obj n).hom = ε.app n := rfl

/-- The term of the base change in degree `n` is `A' ⊗_A P_n`. -/
lemma simplicialBaseChange_obj (n : SimplexCategoryᵒᵖ) :
    (simplicialBaseChange b ε).obj n = CommAlgCat.of A' (A' ⊗[A] (P.obj n : Type u)) := rfl

/-- The simplicial operators of the base change act on a pure tensor by `a' ⊗ p ↦ a' ⊗ P(f)(p)`. -/
@[simp]
lemma simplicialBaseChange_map_tmul {m m' : SimplexCategoryᵒᵖ} (f : m ⟶ m') (a' : A')
    (p : (P.obj m : Type u)) :
    ((simplicialBaseChange b ε).map f).hom (a' ⊗ₜ[A] p) = a' ⊗ₜ[A] (P.map f).hom p := rfl

/-- The base-changed augmentation on a pure tensor: `a' ⊗ p ↦ a' · b(ε_n(p))`. -/
@[simp]
lemma augmentationBaseChange_app_tmul (n : SimplexCategoryᵒᵖ) (a' : A')
    (p : (P.obj n : Type u)) :
    ((augmentationBaseChange b ε).app n).hom (a' ⊗ₜ[A] p) =
      algebraMap A' (B' : Type u) a' * b ((ε.app n).hom p) :=
  baseChangeAugmentation_tmul b ((resolutionOver ε).obj n) a' p


/-- The terms of the base change are polynomial algebras over `A'`: extension of scalars takes
`A[S]` to `A'[S]`. -/
lemma isPolynomialAlgebra_simplicialBaseChange
    (hP : ∀ n, IsPolynomialAlgebra A (P.obj n)) (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebra A' ((simplicialBaseChange b ε).obj n) :=
  isPolynomialAlgebra_baseChange (A' := A') (P.obj n) (hP n)

/-- Extension of scalars preserves the cardinality bound of the footnote to the source's section:
`A' ⊗_A A[S] = A'[S]`, on the *same* set `S` of variables. -/
lemma isPolynomialAlgebraBelow_baseChange (κ : Cardinal.{u}) (P : CommAlgCat.{u} A)
    (hP : IsPolynomialAlgebraBelow A κ P) :
    IsPolynomialAlgebraBelow A' κ (baseChangeObj (A' := A') P) := by
  obtain ⟨ι, hι, ⟨e⟩⟩ := hP
  refine ⟨ι, hι, ⟨?_⟩⟩
  exact (MvPolynomial.scalarRTensorAlgEquiv (R := A) (N := A') (σ := ι)).symm.trans
    (AlgEquiv.ofBijective (Algebra.TensorProduct.map (AlgHom.id A' A') e.toAlgHom)
      (Algebra.TensorProduct.map_bijective
        (f := (AlgHom.id A' A').restrictScalars A) (g := e.toAlgHom)
        Function.bijective_id e.bijective))

/-- The terms of the base change are polynomial algebras over `A'` on at most `κ` variables as
soon as the terms of `P_•` are polynomial algebras over `A` on at most `κ` variables: the set of
variables is unchanged. -/
lemma isPolynomialAlgebraBelow_simplicialBaseChange (κ : Cardinal.{u})
    (hP : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n)) (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebraBelow A' κ ((simplicialBaseChange b ε).obj n) :=
  isPolynomialAlgebraBelow_baseChange (A' := A') κ (P.obj n) (hP n)

/-- An augmentation to a *constant* simplicial algebra which is surjective in degree zero is
surjective in every degree: the map `⦋n⦌ ⟶ ⦋0⦌` of the simplex category carries `P_0` into `P_n`
compatibly with the augmentations. -/
lemma surjective_app_of_surjective_app_zero
    (hε : Function.Surjective (ε.app (Opposite.op (SimplexCategory.mk 0))).hom)
    (n : SimplexCategoryᵒᵖ) : Function.Surjective (ε.app n).hom := by
  intro x
  obtain ⟨p, hp⟩ := hε x
  let g : Opposite.op (SimplexCategory.mk 0) ⟶ n :=
    Opposite.op (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0)
  refine ⟨(P.map g).hom p, ?_⟩
  have h := congrArg
    (fun k : P.obj (Opposite.op (SimplexCategory.mk 0)) ⟶ B => k.hom p) (ε.naturality g)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
    CommAlgCat.hom_comp] at h
  exact h.trans hp

/-- The base-changed augmentation is surjective in every degree, as soon as `ε` is surjective in
degree zero and the canonical map `B ⊗_A A' → B'` is surjective — which is the case when the
square is a pushout. Every element of `B'` is then `b(ε_0(p)) · a'` for some `p` and `a'`, and
`a' ⊗ p` is a preimage. -/
lemma surjective_augmentationBaseChange
    (hε : Function.Surjective (ε.app (Opposite.op (SimplexCategory.mk 0))).hom)
    (hb : ∀ y : (B' : Type u), ∃ (a' : A') (x : (B : Type u)),
      y = algebraMap A' (B' : Type u) a' * b x)
    (n : SimplexCategoryᵒᵖ) :
    Function.Surjective ((augmentationBaseChange b ε).app n).hom := by
  intro y
  obtain ⟨a', x, rfl⟩ := hb y
  obtain ⟨p, hp⟩ := surjective_app_of_surjective_app_zero ε hε n x
  exact ⟨a' ⊗ₜ[A] p,
    (augmentationBaseChange_app_tmul b ε n a' p).trans (by rw [hp])⟩

end BaseChange

end CommAlgCat

end
