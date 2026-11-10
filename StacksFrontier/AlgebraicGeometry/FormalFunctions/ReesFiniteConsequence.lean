module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.FormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8

/-!
# [Stacks, Tag 02OB] and [Stacks, Tag 02OC] with their Tag 02O8 hypothesis discharged

`StacksFrontier/AlgebraicGeometry/FormalFunctions/FormalFunctionsFrom02O8.lean` proves
[Stacks, Tag 02OB] and [Stacks, Tag 02OC] from [Stacks, Tag 02O8], carried there as the explicit
hypothesis `h02O8`, because at the time nothing proved that tag.

It is now a theorem. `Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite`
(`ReesCohomologyFiniteReduction.lean`) carries `@[stacks 02O8]` with no hypothesis beyond the
source's, and `Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem`
(`StalkFormalFunctionsFrom02O8.lean`) is already the universally quantified form that `h02O8`
asks for. Substituting it is all this file does.

## Main results

* `Stacks.Cohomology.FormalFunctions`
  `.exists_uniform_bound_cohomology_idealPowerQuotient_unconditional`:
  [Stacks, Tag 02OB], clause (1), the Mittag-Leffler property and clause (3), verbatim as
  `exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8` states them with the argument
  `h02O8` removed.
* `Stacks.Cohomology.FormalFunctions.exists_formalFunctionsEquiv_unconditional`: the theorem on
  formal functions, [Stacks, Tag 02OC], in the same way — the isomorphism of `A`-modules
  `H^p(X, ℱ) ^∧_I ≅ lim_n H^p(X, ℱ / 𝓘 ^ n ℱ)` together with its compatibility with the
  projections.

## Implementation notes

**No `@[stacks]` attribute is attached here**, following
`StacksFrontier/AlgebraicGeometry/AmpleTwistAcyclicity/GradedConsequence.lean`, which discharges the
`VanishingOverAffineBase` hypothesis of part (2) of [Stacks, Tag 0897] in exactly this way. Both
tags already have sites, on the statements in `FormalFunctionsFrom02O8.lean`, and those sites
belong to the development that proved them; moving or duplicating the attribute is not this
file's business. What this file does mean is that the `granted Tag 02O8, carried as the
hypothesis h02O8` clause of those two sites no longer describes the state of the library.

Three further docstrings in the neighbourhood say that Tag 02O8 is *absent* from this branch —
`CohomologyIdealPowerSystem.lean` at the definition of `IsCohomologyReesFinite` and at
`exists_uniform_bound_cohomology`, and `IdealPowerQuotientCohomologyBound.lean` in its module
documentation. They predate `ReesCohomologyFiniteReduction.lean` and are stale; the theorem
named above is the counterexample to all three.

**What is still not [Stacks, Tag 02OC] in full.** The source also asserts that the comparison is
a homeomorphism for the limit topologies, and that assertion is not proved here or anywhere in
the repository — see the docstring of
`Stacks.Cohomology.FormalFunctions.exists_formalFunctionsEquiv_of_02O8`, whose conclusion is
reproduced below, behind an extra, vacuous `∃ _c : ℕ`. Clauses (2), (4) and (5) of
[Stacks, Tag 02OA], and clause (2) of [Stacks, Tag 02OB] for `n > 0`, are likewise untouched.

## References

* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped ModuleCat.Algebra

universe u

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Cohomology.AffineBase Stacks.Algebraization Stacks.IntertwinedFiltration

attribute [local instance] baseSectionsAlgebra

/-- **[Stacks, Tag 02OB] with no hypothesis beyond the source's.** For `A` Noetherian,
`f : X ⟶ Spec A` proper, `I ⊆ A` an ideal and `ℱ` coherent there is one `c` such that the kernel
of `H^p(X, ℱ) → H^p(X, ℱ / 𝓘 ^ n ℱ)` lies in `I ^ (n - c) H^p(X, ℱ)` for `n ≥ c` — clause (1) —
that the system of quotient cohomologies is Mittag-Leffler, and that the image of
`H^p(X, ℱ / 𝓘 ^ k ℱ) → H^p(X, ℱ / 𝓘 ^ n ℱ)` agrees with the image of `H^p(X, ℱ)` in it once
`n + c ≤ k` — clause (3).

This is `Stacks.Cohomology.FormalFunctions`
`.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8` with its hypothesis `h02O8`
supplied by
`Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem`, the quantified form of
[Stacks, Tag 02O8]. -/
public theorem exists_uniform_bound_cohomology_idealPowerQuotient_unconditional
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (hX : AlgebraicGeometry.IsProper f) (I : Ideal A) (F : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (p : ℕ) :
    ∃ c : ℕ,
      (∀ n : ℕ, c ≤ n →
          LinearMap.ker (cohomologyOverBaseMap A f p
              (cokernel.π (C := X.Modules)
                (idealPowerMultiple (baseIdealSheaf A I f) n F).ι)).hom ≤
            I ^ (n - c) • (⊤ : Submodule A (cohomologyOverBase A f p F))) ∧
        IsMittagLefflerCategorical
          (adicQuotientSystem (baseIdealSheaf A I f) F ⋙
            (Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p) ∧
        ∀ n k : ℕ, (hk : n + c ≤ k) →
          LinearMap.range
              (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
                (idealPowerQuotientDrop (baseIdealSheaf A I f)
                  ((Nat.le_add_right n c).trans hk) F)).hom =
            LinearMap.range
              (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).map
                (cokernel.π (C := X.Modules)
                  (idealPowerMultiple (baseIdealSheaf A I f) n F).ι)).hom :=
  exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8 A f hX I F hF p
    Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem

/-- **The theorem on formal functions, [Stacks, Tag 02OC], with no hypothesis beyond the
source's**, as an isomorphism of `A`-modules: for `A` Noetherian, `f : X ⟶ Spec A` proper and `ℱ`
coherent, the `I`-adic completion of `H^p(X, ℱ)` is the limit of the tower
`n ↦ H^p(X, ℱ / 𝓘 ^ n ℱ)`, compatibly with the projections of both sides.

This is `Stacks.Cohomology.FormalFunctions.exists_formalFunctionsEquiv_of_02O8` with its
hypothesis `h02O8` supplied by
`Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem`. The homeomorphism for the limit
topologies that the source also asserts is not part of the conclusion, there or here. -/
public theorem exists_formalFunctionsEquiv_unconditional
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (hX : AlgebraicGeometry.IsProper f) (I : Ideal A) (F : X.Modules)
    (hF : SheafOfModules.IsCoherent F) (p : ℕ) :
    ∃ (_c : ℕ) (e : AdicCompletion I (cohomologyOverBase A f p F) ≃ₗ[A]
        towerLimit (adicCohomologyTower A f I F p) (adicCohomologyTowerMap A f I F p)),
      ∀ (n : ℕ) (x : cohomologyOverBase A f p F),
        towerLimit.proj n (e (AdicCompletion.of I (cohomologyOverBase A f p F) x)) =
          adicCohomologyProj A f I F p n x :=
  ⟨0, exists_formalFunctionsEquiv_of_02O8 A f hX I F hF p
    Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem⟩

end Stacks.Cohomology.FormalFunctions

end
