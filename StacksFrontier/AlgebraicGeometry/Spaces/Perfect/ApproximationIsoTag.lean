module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationIso
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08HM: the whole lemma

Let `X` be an algebraic space over a scheme `S` which is representable by an affine scheme.
Stacks 08HM asserts that approximation (Stacks 08HI) holds for every triple `(T, E, m)` for which
there is an integer `r ≥ 0` with `E` `m`-pseudo-coherent, `Hⁱ(E)` supported on `T` for
`i ≥ m - r + 1` and `X ∖ T` the union of `r` affine opens, and, in particular, that approximation
by perfect complexes (Stacks 08HJ) holds for `X`.  This file states both on one theorem.

## Main results

* `AlgebraicGeometry.Space.approximationHolds_and_approximationByPerfectComplexes_of_isAffineSpace`:
  **Stacks 08HM**, the whole lemma.

## Implementation notes

Each assertion is spelled exactly as the declaration proving it states it:
`AlgebraicGeometry.Space.approximationHolds_of_isAffineSpace` and
`AlgebraicGeometry.Space.approximationByPerfectComplexes_of_isAffineSpace`.

## References

* [Stacks Project, Tag 08HM](https://stacks.math.columbia.edu/tag/08HM)
* [Stacks Project, Tag 08HI](https://stacks.math.columbia.edu/tag/08HI)
* [Stacks Project, Tag 08HJ](https://stacks.math.columbia.edu/tag/08HJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 08HM.**  Let `S` be a scheme and let `X` be an algebraic space over `S` which is
representable by an affine scheme.  Then

1. approximation holds (Stacks 08HI) for every triple `(Z, E, m)` for which there is an integer
   `r ≥ 0` with
   1. `E` `m`-pseudo-coherent,
   2. `Hⁱ(E)` supported on `Z` for `i ≥ m - r + 1`,
   3. `X ∖ Z` the union of `r` affine opens `V₁, …, V_r` of `X`;
2. in particular, approximation by perfect complexes (Stacks 08HJ) holds for `X`. -/
@[stacks 08HM]
theorem approximationHolds_and_approximationByPerfectComplexes_of_isAffineSpace
    (hXa : IsAffineSpace B S hS F) :
    (∀ (Z : Set (points B S hS F))
      (E : QuasicoherentDerivedCategory.{u, u} B S hS F hF) (m : ℤ) (r : ℕ),
      (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E.obj m →
      (∀ i : ℤ, m - (r : ℤ) + 1 ≤ i →
        supportOfSheaf B S hS F
          ((SheafOfModules.toSheaf
              ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
            ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E.obj)) ⊆ Z) →
      ∀ (V : Fin r → {G : Subfunctor F // IsOpenSubspace B S hS G}),
      (∀ k, IsAffineSpace B S hS (V k).1.toFunctor) →
      ⋃ k, Set.range (pointsMap B S hS (V k).1.toFunctor (V k).1.ι) = Zᶜ →
      ApproximationHolds B S hS F hF Z E m) ∧
    ApproximationByPerfectComplexes.{u, u} B S hS F hF :=
  ⟨approximationHolds_of_isAffineSpace B S hS F hF hXa,
    approximationByPerfectComplexes_of_isAffineSpace B S hS F hF hXa⟩

end AlgebraicGeometry.Space

end
