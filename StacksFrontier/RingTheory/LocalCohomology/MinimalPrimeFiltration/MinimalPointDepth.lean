module

public import StacksFrontier.RingTheory.Depth.Nakayama
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.DepthEqLocalCohomology
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.MinimalPrimeComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Depth and the support of local cohomology at a point minimal in `T`

Let `A` be a Noetherian ring, let `T ⊆ Spec(A)` be stable under specialization and let `M` be a
finite `A`-module.  The vanishing criterion one wants is
`H^i_T(M) = 0` for every `i < s` if and only if `depth(M_𝔭) ≥ s` for every `𝔭 ∈ T`; only its
ideal-indexed case `T = V(I)` is available, as
`Stacks.LocalCohomology.depth_eq_sInf_nontrivial_localCohomologyWithSupportIn`, which is
[Stacks, Tag 0AVZ].

This file proves the criterion **localized at a point minimal in `T`**, where it follows from
the ideal-indexed case with no new input: for `𝔭 ∈ T` minimal in `T` the preimage of `T` in
`Spec(A_𝔭)` is the closed point, so `H^i_T(M)_𝔭 = H^i_{𝔭A_𝔭}(M_𝔭)` by
`Stacks.LocalCohomology.nonempty_minimalPrime_localCohomology_iso` ([Stacks, Tag 0EF8]), and the
depth of `M_𝔭` is the first degree in which the right-hand side is nonzero.  Reading the
left-hand side as a condition on `𝔭 ∈ Supp(H^i_T(M))` gives

`depth(M_𝔭) = inf { i : 𝔭 ∈ Supp(H^i_T(M)) }`     (`𝔭` minimal in `T`).

## Main results

* `Stacks.LocalCohomology.mem_support_localCohomologyWithSupportIn_iff_nontrivial_of_minimal` —
  for `𝔭` minimal in `T`, membership of `𝔭` in the support of `H^i_T(M)` is nontriviality of
  `H^i_{𝔭A_𝔭}(M_𝔭)`.
* `Stacks.LocalCohomology.depth_eq_sInf_mem_support_localCohomologyWithSupportIn_of_minimal` —
  the displayed equality.
* `Stacks.LocalCohomology.exists_mem_support_localCohomologyWithSupportIn_of_depth_lt` — the
  form a client uses: a minimal point of `T` at which the depth of `M` is below `s` lies in the
  support of `H^i_T(M)` for some `i < s`.

## Implementation notes

No `@[stacks]` attribute is placed here.  Tag 0AVZ is the ideal-indexed equality, which is
`Stacks.LocalCohomology.depth_eq_sInf_nontrivial_localCohomologyWithSupportIn`, and Tag 0EF8 is
the exact sequence of the minimal-prime filtration, whose localization clause is
`Stacks.LocalCohomology.nonempty_minimalPrime_localCohomology_iso`; what is below is their
composite at one prime, not either statement.

The three bridges the proof crosses, none of them mathematical content:
`Stacks.LocalCohomology.nonempty_minimalPrime_localCohomology_iso` lands in the coreflection
model `Stacks.LocalCohomology.localCohomologyModuleFunctor` of Stacks 0A6Q, which
`Stacks.LocalCohomology.localCohomologyWithSupportInIsoLocalCohomologyModule` identifies with
supported sections; it also lands in `ModuleCat.localizedModule`, whose carrier is a `Shrink` of
`LocalizedModule`, which is what `Module.support` and
`Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff` are stated with; and
the depth hypothesis `𝔪 • M_𝔭 ≠ M_𝔭` of the ideal-indexed criterion is Nakayama,
`Module.maximalIdeal_smul_top_ne_top`.

## References

* [Stacks Project, Tag 0AVZ](https://stacks.math.columbia.edu/tag/0AVZ)
* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomology

/-- **At a point minimal in `T`, the support of `H^i_T(M)` is detected by local cohomology over
`A_𝔭`.** For `𝔭 ∈ T` minimal in `T`, the prime `𝔭` lies in the support of `H^i_T(M)` exactly
when `H^i_{𝔭A_𝔭}(M_𝔭)` is nonzero: the localization at `𝔭` of `H^i_T(M)` *is* that module, by
`Stacks.LocalCohomology.nonempty_minimalPrime_localCohomology_iso`. -/
public theorem mem_support_localCohomologyWithSupportIn_iff_nontrivial_of_minimal
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (p : PrimeSpectrum A) (hp : p ∈ T \ PrimeSpectrum.nonminimalPrimes T)
    (M : ModuleCat.{u} A) (i : ℤ) :
    p ∈ Module.support A (localCohomologyWithSupportIn.{u, u} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) i) ↔
      Nontrivial (localCohomologyWithSupportIn.{u, u} (Localization.AtPrime p.asIdeal)
        (PrimeSpectrum.zeroLocus
          ((maximalIdeal (Localization.AtPrime p.asIdeal) : Ideal _) : Set _))
        ((DerivedCategory.singleFunctor
          (ModuleCat.{u} (Localization.AtPrime p.asIdeal)) 0).obj
          (M.localizedModule p.asIdeal.primeCompl)) i) := by
  obtain ⟨e⟩ := nonempty_minimalPrime_localCohomology_iso.{u, u} A T hT p hp M i
  have hm : (maximalIdeal (Localization.AtPrime p.asIdeal)).FG := Ideal.fg_of_isNoetherianRing _
  refine Module.mem_support_iff.trans ?_
  refine (equivShrink _).nontrivial_congr.trans ?_
  refine (e.toLinearEquiv.toEquiv).nontrivial_congr.trans ?_
  exact ((localCohomologyWithSupportInIsoLocalCohomologyModule
    (Localization.AtPrime p.asIdeal) (maximalIdeal (Localization.AtPrime p.asIdeal)) hm
    (M.localizedModule p.asIdeal.primeCompl) i).toLinearEquiv.toEquiv).nontrivial_congr.symm

/-- **The vanishing criterion for `H^i_T` at a point minimal in `T`.** Let `A` be a Noetherian
ring, let `T ⊆ Spec(A)` be stable under specialization, let `M` be a finite `A`-module and let
`𝔭 ∈ T` be minimal in `T` and in the support of `M`.  Then the depth of `M_𝔭` is the least
degree in which `𝔭` lies in the support of `H^i_T(M)`.

For `T = V(I)` and `𝔭` minimal in `V(I)` this is [Stacks, Tag 0AVZ]; the content here is that
the localization at a minimal point of `T` turns a general specialization-stable `T` into the
closed point of `Spec(A_𝔭)`. -/
@[sga "2 III 3.4" "more general"]
public theorem depth_eq_sInf_mem_support_localCohomologyWithSupportIn_of_minimal
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (p : PrimeSpectrum A) (hp : p ∈ T \ PrimeSpectrum.nonminimalPrimes T)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hM : p ∈ Module.support A (M : Type u)) :
    Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl (M : Type u)) =
      sInf {n : ℕ∞ | ∃ i : ℕ, n = (i : ℕ∞) ∧
        p ∈ Module.support A (localCohomologyWithSupportIn.{u, u} A T
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (i : ℤ))} := by
  have hfin : Module.Finite (Localization.AtPrime p.asIdeal)
      (M.localizedModule p.asIdeal.primeCompl) :=
    Module.Finite.equiv (Shrink.linearEquiv _ _).symm
  have hnt : Nontrivial (M.localizedModule p.asIdeal.primeCompl : Type u) :=
    (Shrink.linearEquiv (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (M : Type u))).toEquiv.nontrivial_congr.mpr
      (Module.mem_support_iff.mp hM)
  have hshrink : Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl (M : Type u)) =
      Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (M.localizedModule p.asIdeal.primeCompl : Type u) :=
    (Module.depth_eq_depth_of_linearEquiv _
      (Shrink.linearEquiv (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl (M : Type u)))).symm
  rw [hshrink,
    depth_eq_sInf_nontrivial_localCohomologyWithSupportIn.{u, u}
      (Localization.AtPrime p.asIdeal) (maximalIdeal (Localization.AtPrime p.asIdeal))
      (M.localizedModule p.asIdeal.primeCompl) (Module.maximalIdeal_smul_top_ne_top _)]
  exact congrArg sInf (Set.ext fun _ => exists_congr fun i => and_congr_right fun _ =>
    (mem_support_localCohomologyWithSupportIn_iff_nontrivial_of_minimal A T hT p hp M
      (i : ℤ)).symm)

/-- **A minimal point of `T` of small depth lies in the support of a low-degree `H^i_T`.** Let
`A` be a Noetherian ring, let `T ⊆ Spec(A)` be stable under specialization, let `M` be a finite
`A`-module and let `𝔭 ∈ T` be minimal in `T` with `depth(M_𝔭) < s`.  Then `𝔭` lies in the
support of `H^i_T(M)` for some `i < s`.

This is the form in which the criterion is consumed: an ideal annihilating `H^i_T(M)` for all
`i < s` — the ideal [Stacks, Tag 0EFC] produces — therefore has its zero locus containing every
minimal point of `T` at which the depth of `M` is below `s`.  No hypothesis on the support of
`M` is needed: a prime outside it has `M_𝔭 = 0`, whose depth is `⊤`. -/
public theorem exists_mem_support_localCohomologyWithSupportIn_of_depth_lt
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (p : PrimeSpectrum A) (hp : p ∈ T \ PrimeSpectrum.nonminimalPrimes T)
    (M : ModuleCat.{u} A) [Module.Finite A M] (s : ℕ∞)
    (hdepth : Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl (M : Type u)) < s) :
    ∃ i : ℕ, (i : ℕ∞) < s ∧ p ∈ Module.support A (localCohomologyWithSupportIn.{u, u} A T
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (i : ℤ)) := by
  have hM : p ∈ Module.support A (M : Type u) := by
    rw [Module.mem_support_iff, ← not_subsingleton_iff_nontrivial]
    exact fun h => hdepth.ne_top (Module.depth_eq_top_of_subsingleton _)
  rw [depth_eq_sInf_mem_support_localCohomologyWithSupportIn_of_minimal A T hT p hp M hM,
    sInf_lt_iff] at hdepth
  obtain ⟨_, ⟨i, rfl, hi⟩, h⟩ := hdepth
  exact ⟨i, h, hi⟩

end Stacks.LocalCohomology

end
