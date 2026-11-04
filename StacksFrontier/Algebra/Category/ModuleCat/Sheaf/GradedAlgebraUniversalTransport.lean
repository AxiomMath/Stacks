module

public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundle

/-!
# An exterior algebra is recognised by a degreewise invertible comparison homomorphism

Let `R` be a sheaf of rings on a site, `M` a sheaf of `R`-modules, `A` with the degree-one
generator `ι` an exterior algebra of `M`, and `κ` a square-zero degree-one generator of a second
sheaf of graded `R`-algebras `B`. The universal property of `A` produces the unique unital
homomorphism `A ⟶ B` carrying `ι` to `κ`; if that homomorphism is an isomorphism in every degree,
then `B` with `κ` is itself an exterior algebra of `M`.

The converse holds by `SheafOfModules.GradedAlgebra.IsUniversal.pieceIso`, so for a fixed
square-zero generator the two assertions — that `B` is an exterior algebra on it, and that the
comparison from an exterior algebra is invertible in every degree — are the same.

## Main results

* `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.of_desc_isIso`: **the target of a comparison
  homomorphism out of an exterior algebra which is invertible in every degree is itself an
  exterior algebra**, on the generator that comparison extends.

## Implementation notes

The transport of the underlying universal property along a degreewise invertible unital
homomorphism is `SheafOfModules.GradedAlgebra.IsUniversal.ofDegreewiseIso`, which takes the
invertibility as an instance. The hypothesis here is instead the family
`∀ n, IsIso ((hA.desc B κ hκ).app n)`, so that a consumer holding either form can apply the
result.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public section

open CategoryTheory

universe t a v u

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {M : SheafOfModules.{a} R}

namespace IsExteriorAlgebra

variable {A B : GradedAlgebra.{t, a} R} {ι : M ⟶ A.piece 1}

/-- **The target of a comparison homomorphism out of an exterior algebra which is invertible in
every degree is itself an exterior algebra.** Let `A` with `ι` be an exterior algebra of `M` and
let `κ` be a square-zero degree-one generator of `B`. The universal property of `A` produces the
unique unital homomorphism extending `ι` to `κ`; if its component in every degree is an
isomorphism, then `B` with `κ` is an exterior algebra of `M`.

The converse is `SheafOfModules.GradedAlgebra.IsUniversal.pieceIso`, so for a fixed square-zero
generator the universal property of `B` and the degreewise invertibility of the comparison are
the same assertion. -/
theorem of_desc_isIso (hA : IsExteriorAlgebra A ι) (κ : M ⟶ B.piece 1) (hκ : SquareZero κ)
    (h : ∀ n : ℤ, IsIso ((hA.desc B κ hκ).app n)) : IsExteriorAlgebra B κ := by
  have hext : ι ≫ (hA.desc B κ hκ).app 1 = κ := hA.desc_extends B κ hκ
  have := h
  have huniv := hA.isUniversal.ofDegreewiseIso (hA.desc B κ hκ) (by rw [hext]; exact hκ)
  rw [hext] at huniv
  exact huniv

end IsExteriorAlgebra

end SheafOfModules.GradedAlgebra

end
