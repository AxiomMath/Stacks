module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToAnnihilation
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToAnnihilationRestrictScalars
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.UniformTorAnnihilation

/-!
# The filtration of [Stacks, Tag 0GA1] from the spectral sequence that produces it

`Stacks.LocalCohomology.UniformityII.exists_pow_le_annihilator_tor_quotient_pow` is
[Stacks, Tag 0GA1] granted the hypothesis `hfilt`: a finite filtration of `Tor_i^A(M, Iᑫ)` whose
graded pieces are annihilated by `Iᶜ`. The source does not assume such a filtration, it builds
one, out of the hypercohomology spectral sequence [Stacks, Tag 0G9Q] of `Lp^*M̃(q)` on the blowup
`p : X ⟶ Spec A`: the second page is annihilated by `Iᶜ` by [Stacks, Tag 0GA0], it vanishes
outside a band of columns by [Stacks, Tag 071L], and the abutment is `Tor_i^A(M, Iᑫ)` by
[Stacks, Tag 0G9Z].

This file performs that construction, in the only part of it that is not geometry: the hypothesis
`hSS` here is the *spectral sequence* with its annihilation, its vanishing and its abutment, and
the filtration `hfilt` asks for is produced from it by
`Stacks.SpectralSequence.Annihilation.AbutsTo.exists_filtration_of_mem_annihilator_of_iso`.

## Where `hSS` is discharged

`hSS` is exactly the geometric input of the source's proof, and it is discharged, in
`StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.TorAnnihilationBlowup`, by
`Stacks.Blowup.exists_hypercohomologySpectralSequence_abutsTo_tor_idealPow`; so nothing below is
assumed, and [Stacks, Tag 0GA1] holds with no hypothesis beyond the Situation of
[Stacks, Tag 0G9W]. The identification this needs — that the
abutment of `AlgebraicGeometry.hypercohomologySpectralSequence_abutsTo` is the cohomology of
`T.RΓ`, the derived global-sections functor carried by the canonical truncation datum, which
takes values in `Γ(X, 𝒪_X)`-modules, whereas [Stacks, Tag 0G9Z] identifies the cohomology of
`AlgebraicGeometry.derivedGlobalSectionsOver p`, the `A`-linear one — is
`AlgebraicGeometry.baseHypercohomologyIso`:

```
(AlgebraicGeometry.restrictScalarsOver p).obj
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, ⊤)) n).obj (T.RΓ.obj E)) ≅
  (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
    ((AlgebraicGeometry.derivedGlobalSectionsOver p).obj E)
```

Restriction of scalars along `A ⟶ Γ(X, 𝒪_X)` is exact
(`AlgebraicGeometry.preservesFiniteLimits_restrictScalarsOver` and its colimit companion), so it
lifts to `Functor.mapDerivedCategory` and commutes with cohomology
(`Stacks.Homology.derivedHomologyIso`); `T.RΓ ⋙ _.mapDerivedCategory` is then a right derived
functor of `AlgebraicGeometry.globalSectionsOver p` — which is
`SheafOfModules.evaluation _ (op ⊤) ⋙ AlgebraicGeometry.restrictScalarsOver p` by `rfl` — by the
recognition criterion `Stacks.Injectives.KInjectiveResolution`
`.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective` fed with
`Stacks.Cohomology.FilteredComplex.isIso_unit_app_of_isKInjective`; and a right derived functor
is unique up to a canonical isomorphism, by `CategoryTheory.Functor.rightDerivedUnique`. The same
assembly is carried out for the forgetful functor to abelian groups in
`AlgebraicGeometry.groupDerivedSections` and `AlgebraicGeometry.groupHypercohomologyIso`, and
once for `AlgebraicGeometry.derivedGlobalSectionsOver` itself, inside the proof of
`AlgebraicGeometry.isIso_derivedGlobalSectionsOverUnit_app_of_termwise_acyclic`, which stops at
an `IsIso` rather than naming the isomorphism.

Nor is the *sections* hypothesis of [Stacks, Tag 0G9Z] owed any longer. The form of that tag
which quantifies over `_hsections : (globalSectionsOver (toSpec I)).obj (blowUpTwist I n) ≅
ModuleCat.of A (Iⁿ)` — clause (3) of [Stacks, Tag 0AG6], one isomorphism per `n ≥ q₀` and
independent of the module — has an unconditional companion, `Stacks.Blowup`
`.exists_threshold_nonempty_derivedGlobalSectionsTwistedPullback_iso_derivedTensorIdealPow`,
which produces the isomorphism from `Stacks.Blowup.exists_forall_sectionsIsoIdealPow`. So the
abutment identification of `hSS` is assemblable outright — `baseHypercohomologyIso`, then
[Stacks, Tag 0G9Z], then `AdicCompletionTor.nonempty_derivedTensorSingleHomology_iso_Tor'`.

All four parts of `hSS` are therefore available, and what it waited on was no longer an input
but the *assembly*: the existential it asks for has to be produced at the hypercohomology
spectral sequence of `Lp^*M̃(q)` on the blowup, with `R = Γ(X, 𝒪_X)`, with the band width `N`
the uniform vanishing bound of [Stacks, Tag 071L] for `X` and the exponent `c` that of
[Stacks, Tag 0GA0], and with the indices of the parts below matched to the antidiagonal
`(p, -i - p)` this file reads them on. That assembly is
`Stacks.Blowup.exists_hypercohomologySpectralSequence_abutsTo_tor_idealPow`, and feeding it to
`exists_pow_le_annihilator_tor_quotient_pow_of_abutsTo_restrictScalars` below gives the
hypothesis-free `Stacks.LocalCohomology.UniformityII`
`.exists_pow_le_annihilator_tor_quotient_pow_blowup`.

The four parts:

* the band vanishing is `AlgebraicGeometry.isZero_hypercohomologySpectralSequence_page_two`,
  which is what the proof of `AlgebraicGeometry.hypercohomologySpectralSequence_isBounded` used
  to assemble inline out of `AlgebraicGeometry.hypercohomologySpectralSequence_e₂`,
  `AlgebraicGeometry.isZero_hypercohomology_single` and the `N` of
  `AlgebraicGeometry.exists_isZero_rightDerivedPlus_groupSections`, now with the row index free
  rather than tied to one antidiagonal, which is the form `hSS` asks for at `j := -i - p`;
* the annihilation of the page is
  `Stacks.Cohomology.FilteredComplex.mem_annihilator_hypercohomologySpectralSequence_page_two`
  fed with `Stacks.Blowup.exists_pow_le_center_app_homology_twistedDerivedPullback_eq_zero`.
  [Stacks, Tag 0GA0] concludes on sections, and
  `Stacks.SheafOfModules.terminalSectionToEnd_app_eq_zero` turns that into the vanishing
  `η.app F = 0` of a centre element — a scalar killing every section over every open is the zero
  endomorphism. The twist is crossed by
  `Stacks.Blowup.twistedHomologyIsoTensorHomology`, which is
  `Stacks.DerivedTensor.RingedSite.homologyTensorFlatIso` — tensoring with a flat sheaf of
  modules commutes with cohomology — read at the flat twist
  (`Stacks.Blowup.isFlat_twistingSheaf_reesGrading`) and at the complex model of the derived
  pullback that `Stacks.Blowup.derivedTwistedPullbackIso` already uses; and then the scalar
  kills the tensor product because it kills the first factor, which is
  `AlgebraicGeometry.SheafOfModules.globalSectionToEnd_app_sheafTensorRight_eq_zero`.

Four further things it used to need are available too:

* that `Lp^*M̃ ⊗^𝐋 𝒪_X(q)` is an object of `AlgebraicGeometry.QuasicoherentDerivedCategory X`,
  which is what that abutment is stated for, and which
  `Stacks.Blowup.twistedDerivedPullbackQcoh` supplies with the underlying object of the derived
  category being the one [Stacks, Tag 0G9Z] is stated for, on the nose — no construction was
  needed, only the quasi-coherence of the cohomology sheaves, which is [Stacks, Tag 08DW] part
  (1) for the derived pullback and [Stacks, Tag 08DX] part (1) for the derived tensor;
* half of [Stacks, Tag 0G9Z] read on homology, namely the identification of `H^{-i}` of a
  derived tensor product of modules with `Tor`, which is
  `AdicCompletionTor.nonempty_derivedTensorSingleHomology_iso_Tor'`;
* the annihilation of `H^a(X, H^b(Lp^*M̃)(q))` by `Iᶜ` out of the section-level annihilation
  [Stacks, Tag 0GA0] gives, which is
  `Stacks.Cohomology.FilteredComplex.mem_annihilator_homology_RΓ_single_of_center_app_eq_zero`
  — section-level annihilation over *every* open is annihilation of the sheaf as an endomorphism,
  and that endomorphism induces multiplication by the scalar on the cohomology module;
* restriction of scalars from `Γ(X, 𝒪_X)`, over which the hypercohomology spectral sequence is a
  sequence of modules, to `A`, which
  `Stacks.LocalCohomology.UniformityII`
  `.exists_pow_le_annihilator_tor_quotient_pow_of_abutsTo_restrictScalars` below absorbs: the
  spectral sequence may be left over `Γ(X, 𝒪_X)`, since the filtration the carrier asks for is
  one of `A`-submodules of a module identified with the abutment *after* restriction of scalars.

## Main results

* `Stacks.LocalCohomology.UniformityII.exists_pow_le_annihilator_tor_quotient_pow_of_abutsTo`:
  [Stacks, Tag 0GA1] with the hypothesis moved from the filtration to the annihilated spectral
  sequence the source builds the filtration from.

## References

* [Stacks Project, Tag 0GA1](https://stacks.math.columbia.edu/tag/0GA1)
* [Stacks Project, Tag 0GA0](https://stacks.math.columbia.edu/tag/0GA0)
* [Stacks Project, Tag 0G9Q](https://stacks.math.columbia.edu/tag/0G9Q)
* [Stacks Project, Tag 0G9Z](https://stacks.math.columbia.edu/tag/0G9Z)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.LocalCohomology.UniformityII

variable {A : Type u} [CommRing A]

/-- **[Stacks, Tag 0GA1] from the spectral sequence, rather than from the filtration it
produces.** Let `A` be a Noetherian ring and `I = (g 0, …, g (t-1))` an ideal generated by at most
`t` elements. Suppose that for every `A`-module `M`, every `i ≥ t` and every `q ≥ q₀` there is a
cohomological spectral sequence of `A`-modules which

* abuts to a graded family `H` whose term in degree `-i` is `Tor_i^A(M, Iᑫ)`,
* has, on some page, all its terms along the antidiagonal of degree `-i` annihilated by `Iᶜ`,
* and has those terms zero outside the band of `N` columns `0 ≤ p < N`.

Then there is an integer `m`, depending only on `A`, `I`, `q₀`, `N` and `c`, such that `I^m`
annihilates `Tor_i^A(M, A/Iᑫ)` for every `A`-module `M`, every `i > t` and every `q ≥ 0`.

The hypothesis is the geometric input of the source's proof — the hypercohomology spectral
sequence [Stacks, Tag 0G9Q] of `Lp^*M̃(q)` on the blowup, annihilated by [Stacks, Tag 0GA0],
banded by [Stacks, Tag 071L] and identified by [Stacks, Tag 0G9Z] — and it is not discharged
here. What is discharged is the step from it to the filtration: the graded pieces of the
abutment's filtration are subquotients of the page's terms, so they inherit the annihilation, and
where they vanish the filtration is constant, which places its ends at the two ends of the
band. -/
theorem exists_pow_le_annihilator_tor_quotient_pow_of_abutsTo [IsNoetherianRing A] {I : Ideal A}
    {t : ℕ} (g : Fin t → A) (hg : I = Ideal.span (Set.range g)) (q₀ N c : ℕ)
    (hSS : ∀ (M : ModuleCat.{u} A) (i q : ℕ), t ≤ i → q₀ ≤ q →
      ∃ (r₀ : ℤ) (E : CohomologicalSpectralSequence (ModuleCat.{u} A) r₀)
        (H : ℤ → ModuleCat.{u} A) (s : ℤ) (hs : r₀ ≤ s),
        SpectralSequence.AbutsTo E H ∧
        (∀ p : ℤ, p < 0 ∨ (N : ℤ) ≤ p → IsZero ((E.page s hs).X (p, -(i : ℤ) - p))) ∧
        (∀ p : ℤ, I ^ c ≤ Module.annihilator A ((E.page s hs).X (p, -(i : ℤ) - p))) ∧
        Nonempty (H (-(i : ℤ)) ≅
          ((Tor' (ModuleCat.{u} A) i).obj M).obj (ModuleCat.of A ↥(I ^ q)))) :
    ∃ m : ℕ, ∀ (M : ModuleCat.{u} A) (i q : ℕ), t < i →
      I ^ m ≤ Module.annihilator A
        (((Tor' (ModuleCat.{u} A) i).obj M).obj (ModuleCat.of A (A ⧸ I ^ q))) := by
  refine exists_pow_le_annihilator_tor_quotient_pow g hg q₀ N c ?_
  intro M i q hi hq
  obtain ⟨r₀, E, H, s, hs, habuts, hvanish, hann, ⟨e⟩⟩ := hSS M i q hi hq
  exact Stacks.SpectralSequence.Annihilation.AbutsTo.exists_filtration_of_mem_annihilator_of_iso
    habuts hs (I ^ c) (-(i : ℤ)) N hvanish hann e

/-- **[Stacks, Tag 0GA1] from a spectral sequence of modules over a ring reached from `A`.**
`Stacks.LocalCohomology.UniformityII.exists_pow_le_annihilator_tor_quotient_pow_of_abutsTo` with
the spectral sequence allowed to be a sequence of modules over a ring `R` equipped with a
homomorphism `ρ : A →+* R`: the annihilation of its page is asked for by the ideal generated by
the image of `Iᶜ`, and the identification of its abutment with `Tor_i^A(M, Iᑫ)` is asked for
after restriction of scalars along `ρ`, as an isomorphism of `A`-modules.

This is the form the geometry produces. The hypercohomology spectral sequence [Stacks, Tag 0G9Q]
of `Lp^*M̃(q)` on the blowup `p : X ⟶ Spec A` is a spectral sequence of `Γ(X, 𝒪_X)`-modules, over
the ring of global functions of the blowup and not over `A`, while the identification of its
abutment with `Tor_i^A(M, Iᑫ)` of [Stacks, Tag 0G9Z] is an identification of `A`-modules; so
`ρ` is the map `A ⟶ Γ(X, 𝒪_X)` induced by the structure morphism, and no restriction of scalars
has to be performed on the spectral sequence itself. -/
theorem exists_pow_le_annihilator_tor_quotient_pow_of_abutsTo_restrictScalars
    [IsNoetherianRing A] {I : Ideal A} {t : ℕ} (g : Fin t → A)
    (hg : I = Ideal.span (Set.range g)) {R : Type u} [CommRing R] (ρ : A →+* R) (q₀ N c : ℕ)
    (hSS : ∀ (M : ModuleCat.{u} A) (i q : ℕ), t ≤ i → q₀ ≤ q →
      ∃ (r₀ : ℤ) (E : CohomologicalSpectralSequence (ModuleCat.{u} R) r₀)
        (H : ℤ → ModuleCat.{u} R) (s : ℤ) (hs : r₀ ≤ s),
        SpectralSequence.AbutsTo E H ∧
        (∀ p : ℤ, p < 0 ∨ (N : ℤ) ≤ p → IsZero ((E.page s hs).X (p, -(i : ℤ) - p))) ∧
        (∀ p : ℤ, (I ^ c).map ρ ≤
          Module.annihilator R ((E.page s hs).X (p, -(i : ℤ) - p))) ∧
        Nonempty ((ModuleCat.restrictScalars ρ).obj (H (-(i : ℤ))) ≅
          ((Tor' (ModuleCat.{u} A) i).obj M).obj (ModuleCat.of A ↥(I ^ q)))) :
    ∃ m : ℕ, ∀ (M : ModuleCat.{u} A) (i q : ℕ), t < i →
      I ^ m ≤ Module.annihilator A
        (((Tor' (ModuleCat.{u} A) i).obj M).obj (ModuleCat.of A (A ⧸ I ^ q))) := by
  refine exists_pow_le_annihilator_tor_quotient_pow g hg q₀ N c ?_
  intro M i q hi hq
  obtain ⟨r₀, E, H, s, hs, habuts, hvanish, hann, ⟨e⟩⟩ := hSS M i q hi hq
  open Stacks.SpectralSequence.Annihilation in
  exact AbutsTo.exists_filtration_of_mem_annihilator_of_restrictScalars_iso
    ρ habuts hs (I ^ c) (-(i : ℤ)) N hvanish hann e

end Stacks.LocalCohomology.UniformityII

end
