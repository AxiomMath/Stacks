module

public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Dualizing.NormalizedFiniteMap
public import StacksFrontier.RingTheory.Dualizing.RegularLocalNormalizedShift

/-!
# Dualizing complexes over a Noetherian complete local ring

[Stacks, Tag 0BFR] lists four classes of rings carrying a dualizing complex — fields, Noetherian
complete local rings, `ℤ`, and Dedekind domains — together with the operations preserving the
property. This file settles the second class: a Noetherian complete local ring has a dualizing
complex, and in fact a normalized one.

The route is the source's. By the Cohen structure theorem
(`IsLocalRing.exists_isCoefficientRing_and_exists_surjective_mvPowerSeries`, [Stacks, Tag 032A])
such a ring is a quotient of `Λ[[x_1, …, x_n]]` with `Λ` a field or a Cohen ring; either way `Λ`
is regular local, hence so is the power series ring (`MvPowerSeries.isRegularLocalRing`). Over a
regular local ring the regular module shifted into the degree given by the Krull dimension is a
normalized dualizing complex
(`Dualizing.exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift`). A
surjection of Noetherian local rings is a finite local homomorphism, and `RHom` along such a
homomorphism carries a normalized dualizing complex to a normalized dualizing complex
(`Dualizing.isNormalizedDualizingComplex_derivedHom`, [Stacks, Tag 0AX1]).

## Main results

* `Dualizing.exists_isNormalizedDualizingComplex_of_isPrecomplete_maximalIdeal` — a Noetherian
  complete local ring has a normalized dualizing complex.
* `Dualizing.exists_isDualizingComplex_of_isPrecomplete_maximalIdeal` — **[Stacks, Tag 0BFR]**
  for the class of Noetherian complete local rings.

## Implementation notes

Completeness is asked for as precompleteness for the maximal ideal, as in [Stacks, Tag 07PJ]: for
a Noetherian local ring the Hausdorff half is automatic, so a ring carrying
`IsAdicComplete (IsLocalRing.maximalIdeal A) A` satisfies the hypothesis by inference. This is
the convention of `isUniversallyCatenary_of_isPrecomplete_maximalIdeal`, the other consumer of
the Cohen structure theorem here.

The second universe argument of `Dualizing.IsNormalizedDualizingComplex` is `0`, so the modules
are of the same size as the ring. That is the index at which the regular local case is available,
and it is the index at which the finite-map transport consumes and produces it, so the two
compose with no universe bookkeeping.

The field, `ℤ` and Dedekind cases of [Stacks, Tag 0BFR] are
`Dualizing.exists_isDualizingComplex`, `Dualizing.exists_isDualizingComplex_int` and
`Dualizing.exists_isDualizingComplex_of_isDedekindDomain`, in
`StacksFrontier/RingTheory/Dualizing/Ubiquity.lean`; clause (5) of the source, the stability of the
list under passing to an algebra essentially of finite type and to an ideal-adic completion, is
in `StacksFrontier/RingTheory/Dualizing/UbiquityStability.lean`. The statement conjoining all five
clauses is `Dualizing.exists_isDualizingComplex_ubiquity` in
`StacksFrontier/RingTheory/Dualizing/UbiquityFiveClasses.lean`.

## References

* [Stacks Project, Tag 0BFR](https://stacks.math.columbia.edu/tag/0BFR)
* [Stacks Project, Tag 032A](https://stacks.math.columbia.edu/tag/032A)
* [Stacks Project, Tag 0AX1](https://stacks.math.columbia.edu/tag/0AX1)
* [Stacks Project, Tag 07PJ](https://stacks.math.columbia.edu/tag/07PJ)
-/

@[expose] public noncomputable section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **A Noetherian complete local ring has a normalized dualizing complex.** Write the ring as a
quotient of a power series ring over a field or a Cohen ring by the Cohen structure theorem; that
power series ring is regular local, so it has a normalized dualizing complex, and the derived Hom
along the surjection is a normalized dualizing complex downstairs. -/
public theorem exists_isNormalizedDualizingComplex_of_isPrecomplete_maximalIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsPrecomplete (IsLocalRing.maximalIdeal A) A] :
    ∃ ω : DerivedCategory (ModuleCat.{u} A), IsNormalizedDualizingComplex.{u, 0} ω := by
  have : IsAdicComplete (IsLocalRing.maximalIdeal A) A := IsAdicComplete.mk
  obtain ⟨n, Λ, _, _, hΛ, f, hf⟩ :=
    (IsLocalRing.exists_isCoefficientRing_and_exists_surjective_mvPowerSeries A).2
      (Ideal.fg_of_isNoetherianRing _)
  have : IsRegularLocalRing Λ := by
    rcases hΛ with hΛ | hΛ
    · let : Field Λ := hΛ.toField
      infer_instance
    · have : IsCohenRing Λ := hΛ
      infer_instance
  have : IsRegularLocalRing (MvPowerSeries (Fin n) Λ) := MvPowerSeries.isRegularLocalRing Λ n
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  obtain ⟨d, -, hd⟩ :=
    exists_ringKrullDim_eq_and_isNormalizedDualizingComplex_single_self_shift
      (MvPowerSeries (Fin n) Λ)
  exact ⟨_, isNormalizedDualizingComplex_derivedHom.{u, 0} f
    (RingHom.Finite.of_surjective f hf) _ hd⟩

/-- **Stacks Project, Tag 0BFR, the class of Noetherian complete local rings.** Such a ring has
a dualizing complex; the complex produced is in fact normalized, by
`Dualizing.exists_isNormalizedDualizingComplex_of_isPrecomplete_maximalIdeal`.

Completeness is precompleteness for the maximal ideal, as in [Stacks, Tag 07PJ]; see the
implementation notes of this file. -/
@[stacks 0BFR "Noetherian complete local rings"]
public theorem exists_isDualizingComplex_of_isPrecomplete_maximalIdeal
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsPrecomplete (IsLocalRing.maximalIdeal A) A] :
    ∃ K : DerivedCategory (ModuleCat.{u} A), IsDualizingComplex K := by
  obtain ⟨ω, hω⟩ := exists_isNormalizedDualizingComplex_of_isPrecomplete_maximalIdeal A
  exact ⟨ω, hω.1⟩

end Dualizing

end
