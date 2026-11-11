module

public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.Properties.NormalDepthTwo
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Dualizing.CanonicalModuleDepth
public import StacksFrontier.RingTheory.Serre.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace is an isomorphism on a two-dimensional normal singularity

Let `A` be a Noetherian normal local domain of dimension two with a dualizing module `ω_A`. The
proof of [Stacks, Tag 0EA2] turns on the sentence

> the composition `𝒪_{Spec(A)} = f_*𝒪_X → f_*ω_X → ω_A` is an isomorphism by Divisors, Lemma
> [Stacks, Tag 0AVM], as it is an isomorphism over the punctured spectrum of `A` and `A` and
> `ω_A` are `A`-modules of depth `2` (by Algebra, Lemma [Stacks, Tag 031S] and Dualizing
> Complexes, Lemma [Stacks, Tag 0AWE]).

That sentence is proved here, with both depth inputs discharged. Over the affine base the
composition is a map of `A`-modules `A ⟶ ω_A`, its being an isomorphism over the punctured
spectrum is its becoming bijective after localization at every prime other than the maximal
ideal, and [Stacks, Tag 0AVM] is used in the ring form it has in this development,
`bijective_of_bijective_localized_or_depth_two_and_notMem_associatedPrimes` ([Stacks, Tag 0AV8]).

## Main results

* `Stacks.PurityRamification.two_le_depth_localizedModule_maximalIdeal`: the depth-two input for
  the source `A`, which is Serre's criterion [Stacks, Tag 031S] at the maximal ideal, transported
  to the localization there, which is the shape [Stacks, Tag 0AV8] consumes.
* `Stacks.PurityRamification.bijective_of_bijective_localized_of_one_le_depth`: the appeal to
  [Stacks, Tag 0AVM], with the condition on the target in the form in which that tag uses it,
  namely a positive depth at the maximal ideal.
* `Stacks.PurityRamification.bijective_of_bijective_localized_canonicalModule`: the same with the
  target the canonical module of a normalized dualizing complex, where the depth condition is
  [Stacks, Tag 0AWE] and is discharged.

## Implementation notes

`ω_A` is the canonical module `H^{-d}(ω_A^•)` of a normalized dualizing complex, which is the
reading of "dualizing module" under which the source's appeal to [Stacks, Tag 0AWE] is the
development's `Dualizing.min_two_le_depth_canonicalModule`. For a target where that bound is not
available the first theorem takes the depth as a hypothesis, which is also the weakest form of it
that [Stacks, Tag 0AV8] needs: only `𝔪 ∉ Ass(ω_A)`, i.e. positive depth, is used, the depth two
of the source entering through `A` alone.

The depth of the source `A` is needed over the localization `A_𝔪` and for the localized module
`A_𝔪`, not over `A` for `A`, because that is the shape of [Stacks, Tag 0AV8]'s hypothesis.
Serre's criterion gives the latter, and
`Stacks.Depth.ModNonzerodivisor.depth_maximalIdeal_le_depth_localizedModule_maximalIdeal` —
localizing at the maximal ideal does not decrease depth — carries it to the former; only that one
inequality is needed, the conclusion being a lower bound.

No `@[stacks ...]` attribute appears below: these are auxiliary lemmas for [Stacks, Tag 0EA2],
not the tag. Besides this step that tag needs the trace map of Duality for Schemes, Section
[Stacks, Tag 0AWG] — which is the counit of the adjunction `Rf_* ⊣ a` of [Stacks, Tag 0A9E],
proved in this development as
`Stacks.Duality.isLeftAdjoint_quasiCoherentDerivedPushforward_of_qcqs` and used in exactly that
way by `Stacks.Duality.sheafyTrace` ([Stacks, Tag 0B6H]) — and the results below.

* Grauert-Riemenschneider vanishing, [Stacks, Tag 0AXD], is not one of them: it is proved, with
  its duality step (the hypothesis `hvanish` of
  `AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_dualizingModule`) discharged as
  `AlgebraicGeometry.VanishingSituation.forall_linearMap_residueField_eq_zero`, and stated
  unconditionally as
  `AlgebraicGeometry.VanishingSituation.isZero_firstCohomology_of_properRightAdjoint_isoShiftTwo`.
  The contradiction its duality step ends in is [Stacks, Tag 0AXC], proved here as
  `…VanishingSituation.hom_residueFieldShift_derivedGlobalSections_eq_zero`, and the affine
  comparison `D(A) = D_QCoh(𝒪_{Spec(A)})` is [Stacks, Tag 06Z0],
  `AlgebraicGeometry.derivedTilde_isEquivalence`.
* The duality passage from `Rf_*ω_X = ω_A` to `Rf_*𝒪_X = 𝒪_{Spec(A)}`, which is the same
  invertibility of `Stacks.Duality.sheafyTrace` and so rests on the same [Stacks, Tag 0A9Q].
* The short exact sequence of [Stacks, Tag 0AXF], which is what carries `H¹(X, 𝒪_X) = 0` on one
  resolution over to every normal modification and so to
  `AlgebraicGeometry.DefinesRationalSingularity`. Its right-hand exactness input,
  `H²(X, 𝒪_X) = 0`, is available as
  `AlgebraicGeometry.SemistableReduction.TwoModifications.isZero_cohomology_one_lt` of
  `…/ResolutionOfSurfaces/RationalSingularities/CohomologyUnconditional.lean`;
  what is left is the surjectivity of the second Leray edge map, which
  `Stacks.Cohomology.LerayLowDegree.abelianLerayLowDegreeData` does not carry, together with the
  comparison of the abelian-sheaf and module-sheaf models of `H²` that
  `…RationalSingularities.StructureSheafCohomology` assembles in degree one.

## References

* [Stacks Project, Tag 0EA2](https://stacks.math.columbia.edu/tag/0EA2)
* [Stacks Project, Tag 0AVM](https://stacks.math.columbia.edu/tag/0AVM)
* [Stacks Project, Tag 0AV8](https://stacks.math.columbia.edu/tag/0AV8)
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
* [Stacks Project, Tag 0AWE](https://stacks.math.columbia.edu/tag/0AWE)
* [Stacks Project, Tag 00LL](https://stacks.math.columbia.edu/tag/00LL)
* [Stacks Project, Tag 0AWG](https://stacks.math.columbia.edu/tag/0AWG)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AXD](https://stacks.math.columbia.edu/tag/0AXD)
* [Stacks Project, Tag 0AXF](https://stacks.math.columbia.edu/tag/0AXF)
* [Stacks Project, Tag 0AXB](https://stacks.math.columbia.edu/tag/0AXB)
* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0GEW](https://stacks.math.columbia.edu/tag/0GEW)
* [Stacks Project, Tag 0GEV](https://stacks.math.columbia.edu/tag/0GEV)
* [Stacks Project, Tag 0A9Q](https://stacks.math.columbia.edu/tag/0A9Q)
-/

@[expose] public noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.PurityRamification

/-! ### The depth of the source -/

/-- **The depth-two input for `A`.** On a Noetherian normal local domain of dimension at least
two the ring has depth at least two by Serre's criterion [Stacks, Tag 031S], and localizing at
the maximal ideal does not decrease the depth, so the localized module `A_𝔪` has depth at least
two over `A_𝔪`. This is the shape in which [Stacks, Tag 0AV8] asks for the condition. -/
@[ega "IV 5.8.6" "(ii), special case"]
theorem two_le_depth_localizedModule_maximalIdeal (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A) :
    (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime (IsLocalRing.maximalIdeal A))
      (IsLocalRing.maximalIdeal (Localization.AtPrime (IsLocalRing.maximalIdeal A)))
      (LocalizedModule (IsLocalRing.maximalIdeal A).primeCompl A) :=
  (Stacks.NormalDepth.two_le_depth_of_isIntegrallyClosed A hdim).trans
    Stacks.Depth.ModNonzerodivisor.depth_maximalIdeal_le_depth_localizedModule_maximalIdeal

/-! ### The appeal to Tag 0AVM -/

/-- **A map out of `A` which is an isomorphism over the punctured spectrum is an isomorphism.**

This is the application of [Stacks, Tag 0AVM] made in the proof of [Stacks, Tag 0EA2], in the
ring form [Stacks, Tag 0AV8] of that tag. At a prime other than the maximal ideal the hypothesis
`hpunct` gives bijectivity after localization; at the maximal ideal the localized source has depth
at least two by `Stacks.PurityRamification.two_le_depth_localizedModule_maximalIdeal`, and the
maximal ideal is not an associated prime of the target because the target has positive depth
there ([Stacks, Tag 00LL]). -/
theorem bijective_of_bijective_localized_of_one_le_depth {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim A)
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N] (ψ : A →ₗ[A] N)
    (hpunct : ∀ (p : Ideal A) (_ : p.IsPrime), p ≠ IsLocalRing.maximalIdeal A →
      Function.Bijective (LocalizedModule.map p.primeCompl ψ))
    (hdepth : (1 : ℕ∞) ≤ Module.depth A (IsLocalRing.maximalIdeal A) N) :
    Function.Bijective ψ := by
  refine bijective_of_bijective_localized_or_depth_two_and_notMem_associatedPrimes ψ
    fun p hp => ?_
  rcases eq_or_ne p (IsLocalRing.maximalIdeal A) with rfl | hne
  · refine Or.inr ⟨two_le_depth_localizedModule_maximalIdeal A hdim, fun hmem => ?_⟩
    rw [← Module.depth_eq_zero_iff_maximalIdeal_mem_associatedPrimes] at hmem
    rw [hmem] at hdepth
    exact (by decide : ¬ (1 : ℕ∞) ≤ 0) hdepth
  · exact Or.inl (hpunct p hp hne)

/-- **The step of [Stacks, Tag 0EA2] at the canonical module.**

Let `A` be a Noetherian normal local domain of dimension two with a normalized dualizing complex
`ω_A^•`, and let `ω_A = H^{-2}(ω_A^•)` be its canonical module. An `A`-linear map `A ⟶ ω_A` which
is an isomorphism over the punctured spectrum is an isomorphism.

In the source the map is the composition `𝒪_{Spec(A)} = f_*𝒪_X → f_*ω_X → ω_A` of the trace with
the map coming from `𝒪_X → 𝒪_X(E) = ω_X`, and it is an isomorphism over the punctured spectrum
because `f` is. The depth two of `ω_A` is [Stacks, Tag 0AWE] and is supplied here by
`Dualizing.min_two_le_depth_canonicalModule`. -/
theorem bijective_of_bijective_localized_canonicalModule {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hdim : ringKrullDim A = ((2 : ℕ) : WithBot ℕ∞))
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.IsNormalizedDualizingComplex.{u, u} K)
    (ψ : A →ₗ[A] (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-((2 : ℕ) : ℤ))).obj K)
    (hpunct : ∀ (p : Ideal A) (_ : p.IsPrime), p ≠ IsLocalRing.maximalIdeal A →
      Function.Bijective (LocalizedModule.map p.primeCompl ψ)) :
    Function.Bijective ψ := by
  have hfin : Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-((2 : ℕ) : ℤ))).obj K) :=
    hK.1.finiteCohomology _
  have hdepth := Dualizing.min_two_le_depth_canonicalModule 2 K hK hdim
  have hdim' : (2 : WithBot ℕ∞) ≤ ringKrullDim A := by rw [hdim]; norm_num
  have hone : (1 : ℕ∞) ≤ min ((2 : ℕ) : ℕ∞) 2 := by norm_num
  exact bijective_of_bijective_localized_of_one_le_depth hdim' ψ hpunct (hone.trans hdepth)

end Stacks.PurityRamification

end
