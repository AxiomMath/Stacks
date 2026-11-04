module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksFrontier.Algebra.DGA.Abelian

/-!
# Left actions on a complex, and endomorphism differential graded algebras

Let `R` be a commutative ring, `A` a differential graded `R`-algebra and `M` a cochain complex of
`R`-modules. A *left differential graded action* of `A` on `M` is an `R`-linear map from each
homogeneous piece `A^n` to the degree-`n` cochains `M → M`, sending `1` to the identity,
multiplication to composition and the differential of `A` to the graded commutator differential
on cochains.

Dually, an *endomorphism differential graded algebra* of `M` is a differential graded `R`-algebra
whose homogeneous pieces are identified with the degree-`n` cochains `M → M`, compatibly with the
unit, the multiplication and the differential. Such an algebra is unique up to the obvious notion
of isomorphism, and is constructed in
`StacksFrontier.Algebra.DifferentialGraded.Endomorphism.Basic`.

## Main definitions

* `DifferentialGradedAlgebra.LeftAction`: a left differential graded action on a fixed complex,
  recorded on homogeneous elements.
* `CochainComplex.EndomorphismDGA`: a differential graded algebra presented as the endomorphism
  algebra of a complex.

## Implementation notes

The endomorphism algebra is specified by its graded pieces and their operations rather than by a
chosen total-space presentation: this is what lets the correspondence between left actions and
algebra homomorphisms be proved once, for an arbitrary presentation, and only then instantiated
at the canonical construction. Composition of cochains carries no Koszul sign, so the
multiplication rule is a plain `Cochain.comp`.

A `DifferentialGradedAlgebra.{u, v} R` for `R : Type u` has its underlying algebra in `Type v`.
In `LeftAction` that universe is free, since it is read off the algebra being acted with. In
`EndomorphismDGA` the algebra is a field rather than a parameter, so its universe is not
determined by the complex; it is fixed to be `Type u`, the universe in which the cochains
`Cochain M M n` of a complex of `ModuleCat.{u} R` live.

## References

* [Stacks Project, Tag 0FQ3](https://stacks.math.columbia.edu/tag/0FQ3)
-/

@[expose] public section

open CategoryTheory CochainComplex CochainComplex.HomComplex

universe u v

variable {R : Type u} [CommRing R]

namespace DifferentialGradedAlgebra

/-- A left differential graded action of `A` on a fixed cochain complex `M` of `R`-modules,
expressed on homogeneous elements: an `R`-linear map `A^n → Cochain M M n` for every `n`, carrying
the unit to the identity cochain, products to composites of cochains and the differential of `A`
to the graded commutator differential `δ`. -/
structure LeftAction (A : DifferentialGradedAlgebra.{u, v} R)
    (M : CochainComplex (ModuleCat.{u} R) ℤ) where
  /-- The action of the degree-`n` part of `A` by degree-`n` cochains. -/
  action (n : ℤ) : A.grading n →ₗ[R] Cochain M M n
  /-- The unit of `A` acts as the identity. -/
  map_one : action 0 ⟨1, SetLike.one_mem_graded A.grading⟩ = Cochain.ofHom (𝟙 M)
  /-- A product of homogeneous elements acts as the composite of their actions. -/
  map_mul (n m : ℤ) (a : A.grading n) (b : A.grading m) :
    action (n + m) ⟨(a : A.A) * (b : A.A), SetLike.mul_mem_graded a.property b.property⟩ =
      (action m b).comp (action n a) (by omega)
  /-- The differential of `A` acts by the graded commutator differential on cochains. -/
  map_d (n : ℤ) (a : A.grading n) :
    action (n + 1) ⟨A.d a, A.d_mem n a a.property⟩ = δ n (n + 1) (action n a)

end DifferentialGradedAlgebra

namespace CochainComplex

/-- An endomorphism differential graded algebra of a cochain complex `M` of `R`-modules: a
differential graded `R`-algebra together with an identification of each homogeneous piece with the
degree-`n` cochains `M → M`, carrying the unit to the identity cochain, products to composites and
the differential to the graded commutator differential `δ`. -/
structure EndomorphismDGA (M : CochainComplex (ModuleCat.{u} R) ℤ) where
  /-- The underlying differential graded algebra. -/
  algebra : DifferentialGradedAlgebra.{u, u} R
  /-- The identification of the degree-`n` part with the degree-`n` cochains `M → M`. -/
  cochainEquiv (n : ℤ) : algebra.grading n ≃ₗ[R] Cochain M M n
  /-- The unit corresponds to the identity cochain. -/
  map_one : cochainEquiv 0 ⟨1, SetLike.one_mem_graded algebra.grading⟩ = Cochain.ofHom (𝟙 M)
  /-- Multiplication corresponds to composition of cochains. -/
  map_mul (n m : ℤ) (a : algebra.grading n) (b : algebra.grading m) :
    cochainEquiv (n + m)
        ⟨(a : algebra.A) * (b : algebra.A), SetLike.mul_mem_graded a.property b.property⟩ =
      (cochainEquiv m b).comp (cochainEquiv n a) (by omega)
  /-- The differential corresponds to the graded commutator differential on cochains. -/
  map_d (n : ℤ) (a : algebra.grading n) :
    cochainEquiv (n + 1) ⟨algebra.d a, algebra.d_mem n a a.property⟩ =
      δ n (n + 1) (cochainEquiv n a)

end CochainComplex
