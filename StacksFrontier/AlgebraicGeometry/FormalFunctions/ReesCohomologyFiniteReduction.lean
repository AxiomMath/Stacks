module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesSmulCompatible
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 02O8]

`Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite_of_isCoherent` proves
[Stacks, Tag 02O8] from [Stacks, Tag 0897] part (1) at every graded `⨁ₙ ℐⁿ`-module whose
negative pieces vanish, carried there as the hypothesis `h0897`, and
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule` proves that hypothesis.
This file composes the two.

## Main results

* `Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite`: **[Stacks, Tag 02O8]**. For `A`
  Noetherian, `f : X ⟶ Spec A` proper and `ℱ` coherent, the graded module
  `⨁_{n ≥ 0} Hᵖ(X, Iⁿℱ)` is a finite module over the Rees algebra `B = ⨁_{n ≥ 0} Iⁿ`.

## References

* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Blowup Stacks.AlgebraicGeometry.GradedProperCohomology

universe u

namespace Stacks.Cohomology.FormalFunctions

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))

/-- **[Stacks, Tag 02O8].** For `A` Noetherian, `f : X ⟶ Spec A` proper and `ℱ` coherent, the
graded module `⨁_{n ≥ 0} Hᵖ(X, Iⁿℱ)` is a finite module over the Rees algebra
`B = ⨁_{n ≥ 0} Iⁿ`.

This is `Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite_of_isCoherent`, the reduction
of the tag to [Stacks, Tag 0897] part (1) at a graded `⨁ₙ ℐⁿ`-module, with that hypothesis
supplied by `Stacks.Cohomology.FormalFunctions.isCohomologyReesFiniteOfGradedModule`. -/
@[stacks 02O8, ega "III 3.3.2", ega "III 4.1.7.12" "more general"]
public theorem isCohomologyReesFinite [IsNoetherianRing A]
    (F : X.left.Modules) [F.IsCoherent] (p : ℕ)
    (hX : AlgebraicGeometry.IsProper X.hom) :
    IsCohomologyReesFinite I X F p :=
  isCohomologyReesFinite_of_isCoherent I X F p hX
    (fun N _ hX' hft hqc hneg =>
      isCohomologyReesFiniteOfGradedModule I X N hqc hneg p hX' hft)

end Stacks.Cohomology.FormalFunctions

end
