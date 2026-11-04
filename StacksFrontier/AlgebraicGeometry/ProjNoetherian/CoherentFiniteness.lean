module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomology of a coherent module on `Proj` of a Noetherian graded ring is finite over `𝒜 0`

Let `A` be a commutative ring with an `ℕ`-grading `𝒜` whose underlying ring is Noetherian, and
let `ℱ` be a coherent module on `X = Proj 𝒜`. Then `Hᵖ(X, ℱ)` is a finite `𝒜 0`-module for every
`p`.

This is the second assertion of [Stacks, Tag 0B5Q], and it is a special case of the finiteness
theorem for a proper morphism over a Noetherian base: a Noetherian graded ring is of finite type
over its degree-zero part (`Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing`), which
is exactly the hypothesis under which the structure morphism `Proj 𝒜 ⟶ Spec (𝒜 0)` is proper, and
`𝒜 0` is Noetherian because it is a quotient of `A`.

## Main results

* `Stacks.AlgebraicGeometry.ProjNoetherian.moduleFinite_cohomology`: `Hᵖ(Proj 𝒜, ℱ)` is a finite
  `𝒜 0`-module, for every coherent `ℱ` and every `p`.

## Implementation notes

The `𝒜 0`-module structure on the cohomology is the one the structure morphism induces:
restriction of scalars along
`Stacks.AlgebraicGeometry.GradedProperCohomology.specAlgebraRingHom (𝒜 0) (Proj.toSpecZero 𝒜)`,
which is the ring map `𝒜 0 ≅ Γ(Spec (𝒜 0), ⊤) ⟶ Γ(Proj 𝒜, ⊤)`. That is the spelling in which
[Stacks, Tag 02O6] is stated, as
`Stacks.AlgebraicGeometry.GradedProperCohomology.tag02O6`, so no transport intervenes.

No tag attribute is attached: this is one assertion of [Stacks, Tag 0B5Q], not the whole tag, and
the covering declaration for the tag is elsewhere.

## References

* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u v

namespace Stacks.AlgebraicGeometry.ProjNoetherian

variable {A : Type u} {σ : Type v} [CommRing A] [IsNoetherianRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The degree-zero part of a Noetherian graded ring is Noetherian.** Named here because it is
used twice below and is otherwise an application of a Mathlib instance under a `letI`. -/
theorem isNoetherianRing_gradeZero : IsNoetherianRing (𝒜 0) :=
  GradedRing.GradeZero.isNoetherianRing 𝒜

/-- **The structure morphism of `Proj` of a Noetherian graded ring is proper.** A Noetherian
graded ring is of finite type over its degree-zero part, which is the hypothesis of Mathlib's
properness instance for `AlgebraicGeometry.Proj.toSpecZero`. -/
@[ega "II 2.7.1" "special case"]
theorem isProper_toSpecZero : IsProper (AlgebraicGeometry.Proj.toSpecZero 𝒜) :=
  have : Algebra.FiniteType (𝒜 0) A :=
    Stacks.AlgebraicGeometry.Proj.finiteType_of_isNoetherianRing 𝒜
  inferInstance

/-- **Assertion (2) of [Stacks, Tag 0B5Q].** For a Noetherian graded ring `𝒜` and a coherent
module `ℱ` on `Proj 𝒜`, the cohomology `Hᵖ(Proj 𝒜, ℱ)` is a finite `𝒜 0`-module in every degree.

`Proj 𝒜 ⟶ Spec (𝒜 0)` is proper and `𝒜 0` is Noetherian, so this is [Stacks, Tag 02O6]. -/
theorem moduleFinite_cohomology (F : (AlgebraicGeometry.Proj 𝒜).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (p : ℕ) :
    Module.Finite (𝒜 0)
      ((ModuleCat.restrictScalars
        (Stacks.AlgebraicGeometry.GradedProperCohomology.specAlgebraRingHom (𝒜 0)
          (AlgebraicGeometry.Proj.toSpecZero 𝒜))).obj
        (Stacks.AlgebraicGeometry.GradedProperCohomology.cohomologyOf
          (AlgebraicGeometry.Proj 𝒜) p F)) :=
  Stacks.AlgebraicGeometry.GradedProperCohomology.tag02O6 (𝒜 0)
    (isNoetherianRing_gradeZero 𝒜) (AlgebraicGeometry.Proj 𝒜)
    (AlgebraicGeometry.Proj.toSpecZero 𝒜) (isProper_toSpecZero 𝒜) F hF p

end Stacks.AlgebraicGeometry.ProjNoetherian

end
