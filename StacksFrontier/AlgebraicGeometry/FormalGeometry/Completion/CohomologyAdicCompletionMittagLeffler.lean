module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.FormalCompletionCohomologySequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumCompletedSections

/-!
# The `R¹lim` term of Tag 0A0M vanishes on a Mittag-Leffler tower

[Stacks, Tag 0A0M] produces, for `A` Noetherian, `I ⊆ A` an ideal, `f : X ⟶ Spec A` with `X`
Noetherian and `ℱ` coherent with `H^p(X, ℱ)` finite over `A`, short exact sequences

`0 ⟶ R¹lim H^{p-1}(X, ℱ/𝓘ⁿℱ) ⟶ H^p(X, ℱ)^∧ ⟶ lim H^p(X, ℱ/𝓘ⁿℱ) ⟶ 0`

and then asserts that **if `f` is proper the `R¹lim` term is zero**. The source gets that from
the Mittag-Leffler condition of [Stacks, Tag 02OB] for the tower `n ↦ H^{p-1}(X, ℱ/𝓘ⁿℱ)`.

This file supplies the last step of that implication, unconditionally: a Mittag-Leffler tower of
`A`-modules has vanishing `R¹lim` in the cokernel model
`CompletionSequences.firstDerivedLimit` that the sequence of
`Stacks.Algebraization.exists_shortExact_cohomology_limit_adicQuotients` uses, and therefore the
right-hand map of that sequence is an isomorphism

`H^p(X, lim ℱ/𝓘ⁿℱ) ≅ lim H^p(X, ℱ/𝓘ⁿℱ)`,

which is the source's conclusion under the properness clause with the middle term in the form
that tag's registrant proves it.

## Main results

* `Stacks.Algebraization.isZero_firstDerivedLimit_of_isMittagLefflerCategorical` — the `R¹lim`
  of a Mittag-Leffler tower of modules is zero. It is stated for an arbitrary tower, so it serves
  other towers than this file's: `Completion/AffineAdicTowerR1LimVanishing.lean` applies it to
  `n ↦ H^q(U, K ⊗^𝐋_𝒪 𝒪/ℐⁿ)` over an open of a scheme, where it gives the affine-local
  comparison `lim_n H^q(U, K ⊗^𝐋_𝒪 𝒪/ℐⁿ) ≅ H^q(U, K^∧)` of part (2) of [Stacks, Tag 0A0K].
* `Stacks.Algebraization.exists_iso_cohomology_limit_adicQuotients_of_isMittagLeffler` — hence
  the right-hand map of [Stacks, Tag 0A0M]'s sequence is an isomorphism as soon as the
  degree-`(p-1)` tower is Mittag-Leffler.

## Implementation notes

**No `@[stacks 0A0M]` attribute is attached, and none is earned.** The properness clause of
[Stacks, Tag 0A0M] asserts the vanishing for a *proper* `f`, with no hypothesis on the tower;
what is proved here takes the Mittag-Leffler condition of the tower as an explicit hypothesis,
and for a countable tower that condition is *equivalent* to the vanishing it is used to derive.
So this is the vocabulary of the last step, not the step itself; the mathematical content of the
properness clause is [Stacks, Tag 02OB] for the tower `n ↦ H^{p-1}(X, ℱ/𝓘ⁿℱ)`.

Two things stood between `Stacks.Cohomology.FormalFunctions`'s Tag 02OB and the hypothesis `hML`
below. Both are now in the tree, and so is everything above them: the chain has no remaining gap,
and the properness clause itself is proved, unconditionally, in
`Completion/CohomologyAdicCompletionWhole.lean`.

* Tag 02OB was itself conditional there: `exists_uniform_bound_cohomology_idealPowerQuotient`
  carries clauses (2) and (3) of [Stacks, Tag 02OA] as the hypotheses `h02OA_image` and
  `h02OA_kernel`, which `exists_uniform_bound_cohomology` proves — but in another vocabulary, for
  a scheme presented as an object of `Over (Spec A)` and with the `A`-action coming from
  `Stacks.Cohomology.AffineBase.baseSectionsAlgebra` rather than from `baseRingHom`.
  `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_idealPowerQuotient_of_reesFinite`
  translates between the two, so Tag 02OB now holds granted the Rees-finiteness of
  `⨁ₙ H^p(X, 𝓘ⁿℱ)` ([Stacks, Tag 02O8]) alone.
  That Rees-finiteness is itself proved: it is
  `Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite` of
  `FormalFunctions/ReesCohomologyFiniteReduction.lean`, quantified over its data as
  `Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem` of
  `FormalFunctions/StalkFormalFunctionsFrom02O8.lean`. So Tag 02OB is unconditional here. The
  proper mapping theorem [Stacks, Tag 02O5] below it is available too, as
  `AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherent`, and so is its affine
  case [Stacks, Tag 02O6], as `AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology`
  and `Stacks.AlgebraicGeometry.GradedProperCohomology.tag02O6`. A note here that said the chain
  was still blocked above Tag 02O8 by [Stacks, Tag 0897] part (1) was out of date and has been
  removed.
* Tag 02OB's Mittag-Leffler clause is stated for
  `adicQuotientSystem 𝓘 ℱ ⋙ (moduleGlobalSections X).rightDerived p`, a tower of
  `Γ(X, 𝒪_X)`-modules formed with the `ℕ`-indexed right derived functor, whereas `hML` below is
  about `… ⋙ DerivedCategory.homologyFunctor (ModuleCat A) (p - 1)`, a tower of `A`-modules
  formed in the unbounded derived category. `Stacks.Algebraization.rightDerivedRestrictScalarsIso`
  is the comparison of the two derived-functor models, and
  `Stacks.Algebraization.isMittagLefflerCategorical_homologyDerivedGlobalSections` transports the
  Mittag-Leffler condition along it; both are in
  `StacksFrontier/AlgebraicGeometry/FormalGeometry/Completion/CohomologyAdicDerivedComparison.lean`,
  together with `Stacks.Algebraization.exists_iso_cohomology_limit_adicQuotients_of_reesFinite`,
  which is the conclusion below with `hML` discharged from [Stacks, Tag 02O8].

## References

* [Stacks Project, Tag 0A0M](https://stacks.math.columbia.edu/tag/0A0M)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] Stacks.Algebraization.modulesHasDerivedCategory

universe u

namespace Stacks.Algebraization

/-- **The first derived inverse limit of a Mittag-Leffler tower of modules is zero.** In the
cokernel model `CompletionSequences.firstDerivedLimit` — the cokernel of `1 - shift` on the
product of the terms — the Mittag-Leffler condition makes `1 - shift` an epimorphism. -/
public theorem isZero_firstDerivedLimit_of_isMittagLefflerCategorical {A : Type u} [CommRing A]
    (E : ℕᵒᵖ ⥤ ModuleCat.{u} A) (hE : IsMittagLefflerCategorical E) :
    IsZero (CompletionSequences.firstDerivedLimit A E) :=
  (Preadditive.epi_iff_isZero_cokernel (CompletionSequences.moduleDifference A E)).1
    (epi_milnorDifference_of_isMittagLefflerCategorical E hE)

/-- **The right-hand map of [Stacks, Tag 0A0M]'s sequence is an isomorphism on a Mittag-Leffler
tower.** With the hypotheses of
`Stacks.Algebraization.exists_shortExact_cohomology_limit_adicQuotients` and the Mittag-Leffler
condition for the degree-`(p - 1)` tower `n ↦ H^{p-1}(X, ℱ/𝓘ⁿℱ)`, the `R¹lim` term of that
sequence vanishes, so

`H^p(X, lim ℱ/𝓘ⁿℱ) ≅ lim H^p(X, ℱ/𝓘ⁿℱ)`.

This is the conclusion the source draws under its properness clause, with the middle term in the
form `exists_shortExact_cohomology_limit_adicQuotients` proves it. The Mittag-Leffler hypothesis
is not discharged here; for a proper `f` it is discharged in
`Completion/CohomologyAdicCompletionWhole.lean`, whose
`Stacks.Algebraization.exists_iso_cohomology_limit_adicQuotients_of_isProper` is this conclusion
with no hypothesis on the tower. -/
public theorem exists_iso_cohomology_limit_adicQuotients_of_isMittagLeffler
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of A))
    (F : X.Modules) [F.IsCoherent]
    (hfinite : ∀ p : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj F))))
    (p : ℤ)
    (hML : IsMittagLefflerCategorical
      ((adicQuotientSystem (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F ⋙
          DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) (p - 1))) :
    Nonempty
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
          ((derivedGlobalSectionsOver f).obj
            ((DerivedCategory.singleFunctor X.Modules 0).obj
              (limit (adicQuotientSystem
                (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F)))) ≅
        limit ((adicQuotientSystem
              (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A I f) F ⋙
            DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) p)) := by
  obtain ⟨⟨i, q, w, hs⟩, -⟩ :=
    exists_shortExact_cohomology_limit_adicQuotients A I f F hfinite p
  have hzero := isZero_firstDerivedLimit_of_isMittagLefflerCategorical _ hML
  have hf0 : (ShortComplex.mk i q w).f = 0 := hzero.eq_of_src _ _
  have : Mono q := hs.exact.mono_g hf0
  have : Epi q := hs.epi_g
  have : IsIso q := isIso_of_mono_of_epi q
  exact ⟨asIso q⟩

end Stacks.Algebraization

end
