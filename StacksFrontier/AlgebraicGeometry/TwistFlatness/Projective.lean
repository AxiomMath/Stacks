module

public import StacksFrontier.AlgebraicGeometry.ProjTwistFunctor.Projective
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Basic
public import StacksFrontier.AlgebraicGeometry.TwistFlatness.Polynomial

/-!
# The twist on `ℙⁿ_R` is exact

For every commutative ring `R`, every `n` and every `d`, the twisting sheaf `𝒪_{ℙⁿ_R}(d)` is
invertible, so the twist by `d` on `ℙⁿ_R` is an equivalence of categories of sheaves of modules
and carries short exact sequences to short exact sequences.

## Main results

* `Stacks.AlgebraicGeometry.TwistFlatness.isInvertible_projectiveTwistingSheaf`: the twisting
  sheaf `𝒪_{ℙⁿ_R}(d)` is invertible.
* `Stacks.AlgebraicGeometry.TwistFlatness.isEquivalence_projectiveTwistFunctor`,
  `Stacks.AlgebraicGeometry.TwistFlatness.preservesMonomorphisms_projectiveTwistFunctor` and
  `Stacks.AlgebraicGeometry.TwistFlatness.shortExact_map_projectiveTwistFunctor`: the twist on
  `ℙⁿ_R` is an equivalence, preserves monomorphisms, and carries short exact sequences to short
  exact sequences.

## References

* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.AlgebraicGeometry.TwistFlatness

open Stacks.AlgebraicGeometry.ProjTwistFunctor

variable {R : Type u} [CommRing R]

/-- **The twisting sheaf `𝒪_{ℙⁿ_R}(d)` is invertible**, with no hypothesis on `R`, `n` or `d`. -/
theorem isInvertible_projectiveTwistingSheaf (n : ℕ) (d : ℤ) :
    Stacks.SheafOfModules.IsInvertible (projectiveSpaceOverRing n (.of R)).presheaf
      (projectiveSpaceOverRing n (.of R)).ringCatSheaf.2
      (projectiveTwistingSheaf (R := R) n d) := by
  let : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  have hinv : Stacks.SheafOfModules.IsInvertible
      (projectiveSpaceAtUniverse.{u} n).presheaf
      (projectiveSpaceAtUniverse.{u} n).ringCatSheaf.2
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d) :=
    isInvertible_twistingSheaf_of_adjoin_degree_one _
      (adjoin_degree_one_homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) d
  exact @Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf _ _
    (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of R))) _ hinv

/-- **The twist on `ℙⁿ_R` is an equivalence**, with no hypothesis. -/
instance isEquivalence_projectiveTwistFunctor (n : ℕ) (d : ℤ) :
    (projectiveTwistFunctor (R := R) n d).IsEquivalence :=
  @Stacks.AlgebraicGeometry.ProjTwistFunctor.isEquivalence_projectiveTwistFunctor
    _ _ n d (isInvertible_projectiveTwistingSheaf n d)

/-- **The twist on `ℙⁿ_R` preserves monomorphisms**, equivalently `𝒪_{ℙⁿ_R}(d)` is flat. -/
instance preservesMonomorphisms_projectiveTwistFunctor (n : ℕ) (d : ℤ) :
    (projectiveTwistFunctor (R := R) n d).PreservesMonomorphisms :=
  inferInstance

/-- **The twist on `ℙⁿ_R` of a short exact sequence is short exact**, with no hypothesis on `R`,
`n`, `d` or the sequence beyond short exactness. -/
theorem shortExact_map_projectiveTwistFunctor (n : ℕ) (d : ℤ)
    {T : ShortComplex
      (SheafOfModules.{u} (projectiveSpaceOverRing n (.of R)).ringCatSheaf)}
    (hT : T.ShortExact) :
    (T.map (projectiveTwistFunctor n d)).ShortExact :=
  hT.map_of_exact _

end Stacks.AlgebraicGeometry.TwistFlatness

end
