module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap

/-!
# The base change mate read as an adjoint mate

`Stacks.Cohomology.BaseChange.mate` is the underived base change map `F ⋙ G ⟶ G' ⋙ F'` of a
commutative square whose horizontal arrows `G`, `G'` are left adjoints, built from the
comparison `e : P' ⋙ F ≅ F' ⋙ P` of the two composite *right* adjoints.  It is the shape in
which the base change map of **Stacks 0736** is constructed, both on a ringed topos
(`Stacks.Cohomology.ToposBaseChange.moduleBaseChange`) and on a square of algebraic spaces.

This file identifies that map with `CategoryTheory.mateEquiv`, in two ways.  Across the two
*horizontal* adjunctions it is the mate of the comparison `e` itself;  across the two
*vertical* adjunctions — which exist as soon as the direct images `F`, `F'` are themselves
right adjoints, as they are for morphisms of ringed topoi — it is the mate of the comparison
of the two composite *inverse* images, that being the transformation whose conjugate is `e`.
The second reading is what gives access to the mate calculus, and in particular to the
adjoint characterization that the pasting law of **Stacks 0E47** consumes.

## Main results

* `Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_vertical`: **the base change mate is the
  mate, across the two vertical adjunctions, of the comparison of the two composite inverse
  images.**  The hypothesis is that the conjugate of the inverse-image comparison is the
  direct-image comparison, which is what makes the former canonical.
* `Stacks.Cohomology.BaseChange.homEquiv_symm_mate_app`: **the adjoint characterization.**
  Under the adjunction of the right-hand vertical morphism, the base change map at an object
  `K` is the inverse-image comparison followed by the inverse image along the top arrow of
  the counit of the left-hand vertical adjunction.  Since the adjunct is a bijection this
  determines the map, and it is the description the source gives it by.

## Implementation notes

Everything here is stated with all four categories, all four adjunctions and both comparisons
as variables.  That is not generality for its own sake:  the geometric instances are
categories of `𝒪`-modules on the small étale sites of algebraic spaces, and a rewrite inside a
goal mentioning four of their direct and inverse images at once builds a proof term the kernel
cannot check in its budget.  Proving each identity once with the functors as variables and
then instantiating keeps every geometric proof term a single application.

## References

* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Cohomology.BaseChange

section Mate

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {G : B ⥤ D} {P : D ⥤ B} (adjg : G ⊣ P)
  {G' : A ⥤ C} {P' : C ⥤ A} (adjg' : G' ⊣ P')
  (F : A ⥤ B) (F' : C ⥤ D) (e : P' ⋙ F ≅ F' ⋙ P)

/-- **The base change mate is Mathlib's adjoint mate.**  `Stacks.Cohomology.BaseChange.mate`
is spelled out as a composite of whiskerings;  it is the inverse image, under
`CategoryTheory.mateEquiv` for the two adjunctions of the horizontal arrows, of the comparison
of the two composite right adjoints.

Module-local: the public form of this identity is
`Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm` of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/BasePasting.lean`, which states
it for the same `Stacks.Cohomology.BaseChange.mate` defined one layer below this file.  It is
restated here rather than imported because that file sits in `AlgebraicGeometry` and this one
in `Topology`. -/
private theorem mate_eq_mateEquiv_symm :
    mate adjg adjg' F F' e =
      (mateEquiv adjg' adjg).symm (TwoSquare.mk P' F' F P e.hom) := by
  ext M
  simp [mate, mateEquiv]

variable {F F'} {Lf : B ⥤ A} (adjf : Lf ⊣ F) {Lf' : D ⥤ C} (adjf' : Lf' ⊣ F')

/-- **The base change mate is the mate of the comparison of the two composite inverse
images.**  It is defined as the mate, across the two horizontal adjunctions, of the
comparison `e` of the two composite direct images;  when the two vertical functors are
themselves right adjoints it is also the mate, across *their* adjunctions, of any
transformation `α` of the two composite inverse images whose conjugate is `e`.

Iterating the mates operation on a square all of whose four functors are left adjoints gives
the conjugate, which is `CategoryTheory.iterated_mateEquiv_conjugateEquiv`;  the hypothesis
`hα` says exactly that the two-fold mate of `α` is `e`. -/
theorem mate_eq_mateEquiv_vertical (α : TwoSquare G Lf Lf' G')
    (hα : conjugateEquiv (adjf.comp adjg') (adjg.comp adjf') α = e.hom) :
    mate adjg adjg' F F' e = mateEquiv adjf adjf' α := by
  rw [mate_eq_mateEquiv_symm]
  have h : mateEquiv adjg' adjg (mateEquiv adjf adjf' α) = TwoSquare.mk P' F' F P e.hom := by
    rw [← hα]
    exact iterated_mateEquiv_conjugateEquiv adjf adjf' adjg adjg' α
  rw [← h, Equiv.symm_apply_apply]

/-- **The adjoint characterization of the base change mate.**  Under the adjunction of the
right-hand vertical morphism, the base change map at an object `K` is the comparison of the
two composite inverse images followed by the inverse image along the top arrow of the counit
of the left-hand vertical adjunction.

Since the adjunct is a bijection this pins the map down, and it is the description the source
gives the base change map by.  It is also the hypothesis that the horizontal pasting law of
**Stacks 0E47** asks of each of its three squares. -/
theorem homEquiv_symm_mate_app (α : TwoSquare G Lf Lf' G')
    (hα : conjugateEquiv (adjf.comp adjg') (adjg.comp adjf') α = e.hom) (K : A) :
    (adjf'.homEquiv _ _).symm ((mate adjg adjg' F F' e).app K) =
      α.app (F.obj K) ≫ G'.map (adjf.counit.app K) := by
  rw [mate_eq_mateEquiv_vertical adjg adjg' e adjf adjf' α hα, Adjunction.homEquiv_counit]
  exact mateEquiv_counit adjf adjf' α K

end Mate

end Stacks.Cohomology.BaseChange

end
