module

public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsHypotheses

/-!
# The graded cohomology of a graded module is the cohomology of its total module

[Stacks, Tag 0897] writes `H^p(X, ℱ)` for the *graded* `B`-module `⨁ₙ H^p(X, ℱₙ)` attached to a
graded `ℬ`-module `ℱ`, and its proof identifies that graded module with the cohomology of the
single sheaf `ℱ' ` on the relative spectrum through `π_* ℱ' = ℱ`, where `ℱ` on the right-hand
side means the *total* module `⨁ₙ ℱₙ`. Those two readings of `H^p(X, ℱ)` agree, and the
agreement is this file: on a quasi-compact quasi-separated scheme

`H^p(X, ⨁ₙ ℱₙ) = ⨁ₙ H^p(X, ℱₙ)`.

That is the step of [Stacks, Tag 0897]'s proof which is invisible in the source, the source
writing the same symbol for both sides.

Nothing about cohomology is reproved here. The input is
`TopDegreeBaseChange.preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections`: on a
quasi-compact quasi-separated scheme the degree-`p` cohomology functor preserves arbitrary direct
sums, which is [Stacks, Tag 01FF] transported from abelian sheaves to sheaves of modules. That
statement is given for index types in the universe `u` of the scheme, while the grading index is
`ℤ`, so it is applied at `ULift.{u} ℤ` and carried to `ℤ` along
`CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`.

## Main definitions

* `Stacks.AlgebraicGeometry.GradedProperCohomology.totalModule`: the total module `⨁ₙ ℱₙ` of a
  graded module, as a single `𝒪_X`-module — the coproduct in `X.Modules` of the homogeneous
  pieces.

## Main results

* `preservesColimitsOfShape_discrete_int_cohomology`: cohomology of a quasi-compact
  quasi-separated scheme commutes with `ℤ`-indexed direct sums.
* `cohomologyTotalModuleIso`: `H^p(X, ⨁ₙ ℱₙ) ≅ ⨁ₙ H^p(X, ℱₙ)` as `Γ(X, ⊤)`-modules.
* `gradedCohomologySumEquiv`: the same isomorphism with the right-hand side spelled as
  `gradedCohomologySum`, the `DirectSum` in which [Stacks, Tag 0897] part (1) states its
  conclusion.
* `compactSpace_of_isProper_over_affine` and `quasiSeparatedSpace_of_isProper_over_affine`: a
  scheme proper over an affine scheme is quasi-compact and quasi-separated, so that the two
  topological hypotheses are available in the situation of [Stacks, Tag 0897].
* `moduleFinite_gradedCohomologySum_of_cohomologyTotalModule`: finiteness of
  `⨁ₙ H^p(X, ℱₙ)` over a ring acting through `H^p(X, ⨁ₙ ℱₙ)`.

## Implementation notes

The coproduct is taken in `X.Modules` and compared with `CategoryTheory.Limits.Sigma` in
`ModuleCat Γ(X, ⊤)`, then with `DirectSum` through Mathlib's
`ModuleCat.coprodIsoDirectSum`. No new model of the direct sum is introduced.

The grading of the resulting module is not asserted here: `gradedCohomologySum` is the
underlying `DirectSum`, and the comparison is `Γ(X, ⊤)`-linear. The graded `B`-action of
[Stacks, Tag 0897] part (1) comes from the `ℬ`-action on `ℱ`, which is a separate matter and is
not touched.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}
  {𝓑 : _root_.SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-! ### The total module of a graded module -/

/-- The total module `⨁ₙ ℱₙ` of a graded module, as a single `𝒪_X`-module: the coproduct in
`X.Modules` of the homogeneous pieces. This is the sheaf [Stacks, Tag 0897] denotes by the same
letter `ℱ` as the graded module, and whose direct image from the relative spectrum is `ℱ`. -/
abbrev totalModule (F : _root_.SheafOfModules.GradedModule 𝓑) : X.Modules :=
  ∐ fun n : ℤ => pieceModule F n

/-! ### Cohomology commutes with the direct sum over the degrees -/

section Qcqs

variable [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]

/-- **Cohomology of a quasi-compact quasi-separated scheme commutes with `ℤ`-indexed direct
sums.** `preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections` gives this for
index types in the universe of the scheme; `ℤ` is carried over from `ULift.{u} ℤ`. -/
theorem preservesColimitsOfShape_discrete_int_cohomology (p : ℕ) :
    PreservesColimitsOfShape (Discrete ℤ)
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p) :=
  have : PreservesColimitsOfShape (Discrete (ULift.{u, 0} ℤ))
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p) :=
    preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections X p (ULift.{u, 0} ℤ)
  preservesColimitsOfShape_of_equiv (Discrete.equivalence (Equiv.ulift (α := ℤ))) _

/-- **`H^p(X, ⨁ₙ ℱₙ) ≅ ⨁ₙ H^p(X, ℱₙ)`** on a quasi-compact quasi-separated scheme, as
`Γ(X, ⊤)`-modules. This is the identification [Stacks, Tag 0897] leaves implicit in writing
`H^p(X, ℱ)` both for the cohomology of the total module and for the graded module of the
cohomologies of the pieces. -/
def cohomologyTotalModuleIso (F : _root_.SheafOfModules.GradedModule 𝓑) (p : ℕ) :
    cohomologyOf X p (totalModule F) ≅ ∐ fun n : ℤ => cohomologyOf X p (pieceModule F n) :=
  have := preservesColimitsOfShape_discrete_int_cohomology (X := X) p
  preservesColimitIso ((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p)
      (Discrete.functor fun n : ℤ => pieceModule F n) ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete _ _)

/-- **`H^p(X, ⨁ₙ ℱₙ) ≃ ⨁ₙ H^p(X, ℱₙ)`**, with the right-hand side spelled as
`gradedCohomologySum`: the `DirectSum` in which [Stacks, Tag 0897] part (1) states its
conclusion. -/
def gradedCohomologySumEquiv (F : _root_.SheafOfModules.GradedModule 𝓑) (p : ℕ) :
    ↥(cohomologyOf X p (totalModule F)) ≃ₗ[Γ(X, ⊤)] gradedCohomologySum F p :=
  (cohomologyTotalModuleIso F p ≪≫
    ModuleCat.coprodIsoDirectSum fun n : ℤ => cohomologyOf X p (pieceModule F n)).toLinearEquiv

end Qcqs

/-! ### The two topological hypotheses in the situation of Tag 0897 -/

/-- A scheme proper over an affine scheme is quasi-compact: a proper morphism is quasi-compact
(it is universally closed) and the spectrum of a ring is a compact space. -/
theorem compactSpace_of_isProper_over_affine {A : Type u} [CommRing A]
    (f : X ⟶ Spec (.of A)) [IsProper f] : CompactSpace (X : Type u) :=
  QuasiCompact.compactSpace_of_compactSpace f

/-- A scheme proper over an affine scheme is quasi-separated: a proper morphism is separated,
hence quasi-separated, and the spectrum of a ring is a quasi-separated space. -/
theorem quasiSeparatedSpace_of_isProper_over_affine {A : Type u} [CommRing A]
    (f : X ⟶ Spec (.of A)) [IsProper f] : QuasiSeparatedSpace (X : Type u) :=
  quasiSeparatedSpace_of_quasiSeparated f

/-! ### Finiteness carried from the total module -/

/-- **Finiteness of `⨁ₙ H^p(X, ℱₙ)` from finiteness of `H^p(X, ⨁ₙ ℱₙ)`.** If a ring `R` acts on
the graded cohomology compatibly with the `Γ(X, ⊤)`-linear identification
`gradedCohomologySumEquiv`, through a module structure making that identification `R`-linear,
then finiteness over `R` of the cohomology of the total module is finiteness over `R` of the
graded cohomology.

This is the step by which [Stacks, Tag 0897] part (1) reads off its conclusion once the
cohomology of the total module has been identified with the cohomology of `ℱ'` upstairs. -/
theorem moduleFinite_gradedCohomologySum_of_cohomologyTotalModule
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]
    (F : _root_.SheafOfModules.GradedModule 𝓑) (p : ℕ)
    (R : Type u) [CommRing R] [Module R (gradedCohomologySum F p)]
    [Module R ↥(cohomologyOf X p (totalModule F))]
    (e : ↥(cohomologyOf X p (totalModule F)) ≃ₗ[R] gradedCohomologySum F p)
    [Module.Finite R ↥(cohomologyOf X p (totalModule F))] :
    Module.Finite R (gradedCohomologySum F p) :=
  Module.Finite.equiv e

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
