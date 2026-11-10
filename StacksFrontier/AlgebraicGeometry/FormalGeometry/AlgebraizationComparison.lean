module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationDimensionBounds
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletedLocalCohomologyShrink
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence

/-!
# Comparing local cohomology with completed local cohomology

Let `I` and `J` be ideals of a Noetherian ring `A`, let `M` be a finite `A`-module and let `s`
and `d` be integers. Write `T` for the subset `Stacks.Algebraization.associatedSubset I J` of
Stacks 0EFG and `(-)^∧` for derived `I`-adic completion. Stacks 0EFL asserts, under a
dualizing-complex and `I`-adic completeness hypothesis, a bound `cd(A, I) ≤ d`, a depth and
dimension inequality off `V(I) ∪ T`, and a supplementary inequality with three alternatives,
that there is an ideal `J₀ ⊆ J` with `V(J₀) ∩ V(I) = V(J) ∩ V(I)` such that every further ideal
`J' ⊆ J₀` with the same intersection with `V(I)` has

`RΓ_{J'}(M) ⟶ RΓ_J(M)^∧`

an isomorphism on cohomology in degrees `≤ s`. The arrow is the one the opening paragraph of the
source constructs, which is
`Stacks.Algebraization.localCohomologyToCompletedLocalCohomology`.

This file states those hypotheses and that conclusion, and proves the conclusion.

## Main definitions

* `Stacks.Algebraization.AlgebraizationHypotheses` — hypotheses (1), (3), (4) and (5) of the
  source, relative to a dimension function `δ` and the extreme values `δmax` and `δmin` of `δ`
  on `V(J) ∩ V(I)` that conditions (5)(b) and (5)(c) are stated against.
* `Stacks.Algebraization.IsAlgebraizationIdeal` — the conclusion of the source, as a property of
  a candidate ideal `J₀`.

## Main results

* `Stacks.Algebraization.exists_isAlgebraizationIdeal` — **Stacks 0EFL**: the ideal `J₀` exists.
* `Stacks.Algebraization.isAlgebraizationIdeal_of_zeroLocus_inter_eq_empty` — **Stacks 0EFL** for
  `V(J) ∩ V(I) = ∅`, the case the extreme values of `δ` exclude, with `J₀ = J`.
* `Stacks.Algebraization.isAlgebraizationIdeal_of_lt_zero` — the conclusion for `s < 0`, with
  `J₀ = J`: both sides have no cohomology in the relevant degrees, so the comparison is an
  isomorphism there.

## Implementation notes

Depth takes values in `ℕ∞` and Krull dimension in `WithBot ℕ∞`; both are carried into `EInt` by
`Stacks.Algebraization.enatToEInt` and `Stacks.Algebraization.krullDimToEInt`, as in the
development of Stacks 0EFI, so that the integer bounds of the source keep their full range on
either side. Condition (4) is spelled exactly as the corresponding condition of
`Stacks.Algebraization.StabilizationHypotheses`, the two being the same inequality in the
source.

The dimension function `δ` of condition (5) is data of the source's statement rather than of its
conclusion, so it is a parameter of the hypotheses and does not appear in
`Stacks.Algebraization.IsAlgebraizationIdeal`. Its extreme values on `V(J) ∩ V(I)` are carried as
two further parameters, constrained by `IsGreatest` and `IsLeast`, which is what "the maximum of
`δ` on `V(J) ∩ V(I)`" says.

That pair exists only when `V(J) ∩ V(I)` is nonempty, so
`Stacks.Algebraization.AlgebraizationHypotheses` is unsatisfiable when `V(J) ∩ V(I)` is empty and
`Stacks.Algebraization.exists_isAlgebraizationIdeal` asserts nothing there. The source imposes no
such nonemptiness: its condition (5) is guarded by `V(𝔭) ∩ V(J) ∩ V(I) ≠ ∅` and is therefore
vacuous once `V(J) ∩ V(I)` is empty, so the hypotheses of the source are then satisfied with no
mention of `δ`. That case is proved separately in
`Stacks.Algebraization.isAlgebraizationIdeal_of_zeroLocus_inter_eq_empty`, and the two results
together are the source's assertion; both carry the tag. It is not a vacuous case either: `J = A`
is an instance of it, and the source's conclusion for it is the vanishing of both sides.

The proof is the source's induction on `s`. The case `s < 0` is the vanishing of both sides,
which on the completed side is Stacks 0EEW; the case `s = 0` is Stacks 0EFI together with
Stacks 0EEX; and the inductive step divides by a nonzerodivisor supplied by Stacks 0EFH after
discarding the submodule of `M` supported in `V(I) ∪ T`. Those four inputs enter through
`Stacks.Algebraization.exists_isStabilizingData`,
`Stacks.Algebraization.isIso_homology_zero_completionUnit_localCohomology_of_stable`,
`Stacks.Algebraization.isIso_homology_completionUnit_localCohomology_of_neg` and
`Stacks.Algebraization.exists_notMem_mem_annihilator_homology_derivedCompletion_localCohomology`.

Stacks 0EFI is available in the library only for `0 ≤ d`, which the hypotheses of Stacks 0EFL do
supply: condition (5) is stated against the extreme values of `δ` on `V(J) ∩ V(I)`, so it forces
that set to be nonempty, hence `V(I)` to be nonempty, and then `0 ≤ cd(A, I) ≤ d` by
`Stacks.Algebraization.nonneg_cohomologicalDimension_of_mem_zeroLocus`. That is
`Stacks.Algebraization.nonneg_of_algebraizationHypotheses`, and it is why no nonnegativity
hypothesis on `d` appears below.

The module universe is the ring universe, which is where `Dualizing.completedLocalCohomology`
lives. The universe of the dualizing complex stays independent in the hypothesis structure, but
`Stacks.Algebraization.exists_isAlgebraizationIdeal` takes it in the ring's own module universe:
that is the universe in which Stacks 0EFI and Stacks 0EFH are available in this library.

## References

* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0EFG](https://stacks.math.columbia.edu/tag/0EFG)
* [Stacks Project, Tag 0EFH](https://stacks.math.columbia.edu/tag/0EFH)
* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0EEX](https://stacks.math.columbia.edu/tag/0EEX)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
* [Stacks Project, Tag 02I9](https://stacks.math.columbia.edu/tag/02I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.Algebraization
/-- The hypotheses (1), (3), (4) and (5) of Stacks 0EFL. Condition (2) of the source is empty.

Here `δ` is a dimension function on `Spec(A)` and `δmax`, `δmin` are the maximum and the minimum
of `δ` on `V(J) ∩ V(I)`, the data against which the three alternatives of condition (5) are
stated. `T` is `Stacks.Algebraization.associatedSubset I J`. -/
public structure AlgebraizationHypotheses
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ) : Prop where
  /-- The ring is `I`-adically complete. -/
  adicComplete : IsAdicComplete I A
  /-- The ring has a dualizing complex, witnessed by `omega`. -/
  dualizing : Dualizing.IsDualizingComplex (A := A) (K := omega)
  /-- The cohomological dimension of `I` is at most `d`. -/
  cohomologicalDimension_le :
    Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d
  /-- Condition (4): a prime outside `V(I)` and outside `T` has depth at least `s`, or depth plus
  relative dimension exceeding `d + s` along every specialization in `V(J) ∩ V(I)`. -/
  depthOrDimensionBound : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      p ∉ associatedSubset I J →
      ((enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) ≥ (s : EInt)) ∨
        (∀ q : PrimeSpectrum A,
          q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (J : Set A)) ∩
            PrimeSpectrum.zeroLocus (I : Set A) →
          enatToEInt
              (Module.depth (Localization.AtPrime p.asIdeal)
                (maximalIdeal (Localization.AtPrime p.asIdeal))
                (LocalizedModule p.asIdeal.primeCompl M)) +
              krullDimToEInt
                (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
                  p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
            ((d + s : ℤ) : EInt)))
  /-- `δ` is a dimension function on `Spec(A)`, in the sense of Stacks 02I9. -/
  isDimensionFunction : IsDimensionFunctionProp δ
  /-- `δmax` is the maximum of `δ` on `V(J) ∩ V(I)`. -/
  isGreatest_δmax : IsGreatest (δ '' (PrimeSpectrum.zeroLocus (J : Set A) ∩
    PrimeSpectrum.zeroLocus (I : Set A))) δmax
  /-- `δmin` is the minimum of `δ` on `V(J) ∩ V(I)`. -/
  isLeast_δmin : IsLeast (δ '' (PrimeSpectrum.zeroLocus (J : Set A) ∩
    PrimeSpectrum.zeroLocus (I : Set A))) δmin
  /-- Condition (5): at a prime `𝔭` outside `V(I)` and outside `T` which has a specialization in
  `V(J) ∩ V(I)` and depth less than `s`, one of three alternatives holds — the support of `M_𝔭`
  has dimension less than `s + 2`, or `δ(𝔭) > d + δmax - 1`, or depth plus relative dimension
  exceeds `d + s + δmax - δmin - 2` along every specialization in `V(J) ∩ V(I)`. -/
  supplementaryBound : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      p ∉ associatedSubset I J →
      ((PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
        PrimeSpectrum.zeroLocus (J : Set A)) ∩
        PrimeSpectrum.zeroLocus (I : Set A)).Nonempty →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) < (s : EInt) →
      (krullDimToEInt (Module.supportDim (Localization.AtPrime p.asIdeal)
            (LocalizedModule p.asIdeal.primeCompl M)) < ((s + 2 : ℤ) : EInt) ∨
        (d + δmax - 1 < δ p) ∨
        (∀ q : PrimeSpectrum A,
          q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (J : Set A)) ∩
            PrimeSpectrum.zeroLocus (I : Set A) →
          enatToEInt
              (Module.depth (Localization.AtPrime p.asIdeal)
                (maximalIdeal (Localization.AtPrime p.asIdeal))
                (LocalizedModule p.asIdeal.primeCompl M)) +
              krullDimToEInt
                (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
                  p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
            ((d + s + δmax - δmin - 2 : ℤ) : EInt)))

/-- The conclusion of Stacks 0EFL, as a property of a candidate ideal `J₀`.

The ideal is contained in `J` and has the same zero-locus intersection with `V(I)`, and for every
further ideal `J' ≤ J₀` with that same intersection the canonical map `RΓ_{J'}(M) ⟶ RΓ_J(M)^∧`
of `Stacks.Algebraization.localCohomologyToCompletedLocalCohomology` is an isomorphism on
cohomology in degrees `≤ s`. -/
public structure IsAlgebraizationIdeal
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) (J₀ : Ideal A) : Prop where
  /-- The ideal shrinks `J`. -/
  le : J₀ ≤ J
  /-- Shrinking does not change the intersection of the zero locus with `V(I)`. -/
  zeroLocus_inter :
    PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
  /-- For every admissible further shrinking the comparison with the completion is an
  isomorphism in degrees `≤ s`. -/
  isIso : ∀ J' : Ideal A, J' ≤ J₀ →
      ∀ hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A),
      ∀ i : ℤ, i ≤ s →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        (localCohomologyToCompletedLocalCohomology A I J J' I.fg_of_isNoetherianRing
          J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing (ModuleCat.of A M) hV))


section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **Stacks 0EFL for `s < 0`.** For negative `s` the ideal `J` itself has the property asserted
of `J₀`: local cohomology of a module vanishes in negative degrees, and so does the cohomology of
the derived `I`-adic completion of `RΓ_J(M)`, so the comparison map is an isomorphism in every
degree `≤ s`.

The second vanishing is Stacks 0EEW, which is the reason the source isolates this case. The
hypotheses of Stacks 0EFL are carried but unused: for `s < 0` the conclusion holds for every
finite module. -/
public theorem isAlgebraizationIdeal_of_lt_zero (I J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A)) (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ)
    (_H : AlgebraizationHypotheses (M := M) I J s d omega δ δmax δmin)
    (hs : s < 0) :
    IsAlgebraizationIdeal (M := M) I J s J where
  le := le_rfl
  zeroLocus_inter := rfl
  isIso J' _ _ i hi := by
    refine IsZero.isIso ?_ ?_ _
    · exact Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg A J'
        J'.fg_of_isNoetherianRing (ModuleCat.of A M) i (lt_of_le_of_lt hi hs)
    · exact Dualizing.isZero_homology_completedLocalCohomology_of_neg A I J
        I.fg_of_isNoetherianRing J.fg_of_isNoetherianRing (ModuleCat.of A M)
        (Dualizing.isDerivedLimit_completedLocalCohomology A I J I.fg_of_isNoetherianRing
          J.fg_of_isNoetherianRing (ModuleCat.of A M)) i (lt_of_le_of_lt hi hs)

/-- **The hypotheses of Stacks 0EFL force `0 ≤ d`.** Condition (5) is stated against the extreme
values of `δ` on `V(J) ∩ V(I)`, so it presupposes that this set is nonempty; then `V(I)` is
nonempty and the cohomological dimension of `I` is nonnegative. -/
public theorem nonneg_of_algebraizationHypotheses {I J : Ideal A} {s d : ℤ}
    {omega : DerivedCategory (ModuleCat.{w} A)} {δ : PrimeSpectrum A → ℤ} {δmax δmin : ℤ}
    (H : AlgebraizationHypotheses (M := M) I J s d omega δ δmax δmin) : 0 ≤ d := by
  obtain ⟨q, hq, -⟩ := H.isGreatest_δmax.1
  exact (nonneg_cohomologicalDimension_of_mem_zeroLocus I q hq.2).trans
    H.cohomologicalDimension_le

end

section Hypotheses

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **Conditions (4) and (5) at the associated primes.** Assume every associated prime of `M`
lies outside `V(I)` and outside `T` and has a specialization in `V(J) ∩ V(I)`. Then for every
prime `p'` below an associated prime and every `q' ∈ V(p') ∩ V(J) ∩ V(I)`,

`depth(M_{p'}) + dim((A/p')_{q'}) > d + s`.

This is the paragraph of the source that turns condition (5) into the hypothesis of
Stacks 0EFH: when the depth at `p'` is at least `s` there is nothing to do, and in the remaining
case `p'` sits strictly above an associated prime, where the dimension function drops, and the
three alternatives of condition (5) each give the bound. -/
public theorem depth_add_dimension_bound_of_associatedPrimes
    (I J : Ideal A) (s d : ℤ) (hs : 0 < s)
    {omega : DerivedCategory (ModuleCat.{w} A)} {δ : PrimeSpectrum A → ℤ} {δmax δmin : ℤ}
    (H : AlgebraizationHypotheses (M := M) I J s d omega δ δmax δmin)
    (hass : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧ p ∉ associatedSubset I J)
    (hmeet : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
      ∃ q : PrimeSpectrum A,
        q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
          PrimeSpectrum.zeroLocus (J : Set A)) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (p : PrimeSpectrum A) (hp : p.asIdeal ∈ associatedPrimes A M)
    (p' q' : PrimeSpectrum A) (hp'p : p'.asIdeal ≤ p.asIdeal)
    (hq' : q' ∈ PrimeSpectrum.zeroLocus (p'.asIdeal : Set A) ∩
      (PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))) :
    enatToEInt
        (Module.depth (Localization.AtPrime p'.asIdeal)
          (maximalIdeal (Localization.AtPrime p'.asIdeal))
          (LocalizedModule p'.asIdeal.primeCompl M)) +
      krullDimToEInt
        (ringKrullDim ((Localization.AtPrime q'.asIdeal) ⧸
          p'.asIdeal.map (algebraMap A (Localization.AtPrime q'.asIdeal)))) >
      ((d + s : ℤ) : EInt) := by
  have hp'I : p' ∉ PrimeSpectrum.zeroLocus (I : Set A) :=
    fun h => (hass p hp).1 (h.trans hp'p)
  have hp'T : p' ∉ associatedSubset I J :=
    fun h => (hass p hp).2 fun q hq => h ⟨hp'p.trans hq.1, hq.2⟩
  rw [krullDimToEInt_localizedQuotient_eq H.isDimensionFunction p' q' hq'.1]
  cases hdep : Module.depth (Localization.AtPrime p'.asIdeal)
      (maximalIdeal (Localization.AtPrime p'.asIdeal))
      (LocalizedModule p'.asIdeal.primeCompl M) using ENat.recTopCoe with
  | top =>
    change ((d + s : ℤ) : EInt) < (⊤ : EInt) + ((δ p' - δ q' : ℤ) : EInt)
    have ht : (⊤ : EInt) + ((δ p' - δ q' : ℤ) : EInt) = ⊤ :=
      congrArg (fun z : WithTop ℤ => (z : WithBot (WithTop ℤ)))
        (WithTop.top_add ((δ p' - δ q' : ℤ) : WithTop ℤ))
    rw [ht]
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_top _)
  | coe n =>
    change ((d + s : ℤ) : EInt) < ((n : ℤ) : EInt) + ((δ p' - δ q' : ℤ) : EInt)
    by_cases hn : (n : ℤ) < s
    · have hsmall : enatToEInt
          (Module.depth (Localization.AtPrime p'.asIdeal)
            (maximalIdeal (Localization.AtPrime p'.asIdeal))
            (LocalizedModule p'.asIdeal.primeCompl M)) < (s : EInt) := by
        rw [hdep]
        exact WithBotTop.coe_lt_coe.mpr hn
      have h := (H.depthOrDimensionBound p' hp'I hp'T).resolve_left (not_le_of_gt hsmall)
        q' ⟨⟨hq'.1, hq'.2.1⟩, hq'.2.2⟩
      rwa [hdep, krullDimToEInt_localizedQuotient_eq H.isDimensionFunction p' q' hq'.1] at h
    have hnontrivial : Nontrivial (LocalizedModule p'.asIdeal.primeCompl M) := by
      by_contra! h
      have htop : Module.depth (Localization.AtPrime p'.asIdeal)
          (maximalIdeal (Localization.AtPrime p'.asIdeal))
          (LocalizedModule p'.asIdeal.primeCompl M) = ⊤ := by
        simp [Module.depth, Submodule.eq_bot_of_subsingleton]
      rw [htop] at hdep
      exact ENat.top_ne_natCast n hdep
    obtain ⟨p'', hp'', hp''p'⟩ := exists_associatedPrime_le_of_mem_support p'
      (Module.mem_support_iff.mpr hnontrivial)
    have hdepth0 := depth_localization_eq_zero_of_mem_associatedPrimes p hp
    have hdepth0' := depth_localization_eq_zero_of_mem_associatedPrimes p'' hp''
    have hsmall (a : PrimeSpectrum A) (ha : a.asIdeal ∈ associatedPrimes A M) :
        enatToEInt
          (Module.depth (Localization.AtPrime a.asIdeal)
            (maximalIdeal (Localization.AtPrime a.asIdeal))
            (LocalizedModule a.asIdeal.primeCompl M)) < (s : EInt) := by
      rw [depth_localization_eq_zero_of_mem_associatedPrimes a ha]
      exact WithBotTop.coe_lt_coe.mpr hs
    have hneq : p' ≠ p := by
      intro he
      subst p'
      rw [hdepth0] at hdep
      have hn0 : n = 0 := by exact_mod_cast hdep.symm
      omega
    have hstep : δ p < δ p' := H.isDimensionFunction.1 p' p
      ((PrimeSpectrum.le_iff_specializes _ _).mp hp'p) hneq
    obtain ⟨q, hq⟩ := hmeet p hp
    have hmin : δmin ≤ δ q := H.isLeast_δmin.2 ⟨q, ⟨hq.1.2, hq.2⟩, rfl⟩
    have hmax : δ q' ≤ δmax := H.isGreatest_δmax.2 ⟨q', hq'.2, rfl⟩
    have hassdim : d + s < δ p'' - δ q' := by
      have h := (H.depthOrDimensionBound p'' (hass p'' hp'').1 (hass p'' hp'').2).resolve_left
        (not_le_of_gt (hsmall p'' hp'')) q' ⟨⟨hp''p'.trans hq'.1, hq'.2.1⟩, hq'.2.2⟩
      rw [hdepth0', krullDimToEInt_localizedQuotient_eq H.isDimensionFunction p'' q'
        (hp''p'.trans hq'.1)] at h
      change ((d + s : ℤ) : EInt) < (0 : EInt) + ((δ p'' - δ q' : ℤ) : EInt) at h
      simpa only [zero_add, WithBotTop.coe_lt_coe] using h
    have hsupp : δ p'' - δ p < s + 2 ∨ d + δmax - 1 < δ p ∨
        d + s + δmax - δmin - 2 < δ p - δ q := by
      rcases H.supplementaryBound p (hass p hp).1 (hass p hp).2 ⟨q, hq⟩ (hsmall p hp)
        with h | h | h
      · left
        have hdim := krullDimToEInt_mono
          (ringKrullDim_localizedQuotient_le_supportDim p'' p hp'' (hp''p'.trans hp'p))
        rw [krullDimToEInt_localizedQuotient_eq H.isDimensionFunction p'' p
          (hp''p'.trans hp'p)] at hdim
        exact WithBotTop.coe_lt_coe.mp (hdim.trans_lt h)
      · exact Or.inr (Or.inl h)
      · refine Or.inr (Or.inr ?_)
        have h := h q hq
        rw [hdepth0, krullDimToEInt_localizedQuotient_eq H.isDimensionFunction p q hq.1.1] at h
        change ((d + s + δmax - δmin - 2 : ℤ) : EInt) <
          (0 : EInt) + ((δ p - δ q : ℤ) : EInt) at h
        simpa only [zero_add, WithBotTop.coe_lt_coe] using h
    apply (eint_int_lt_add_iff_int _ _ _).mpr
    have h := depth_add_dimension_gt_of_supplemental hs (le_of_not_gt hn) hstep
      (le_rfl : δ p'' - δ p ≤ δ p'' - δ p) hassdim hmin hmax hsupp
    omega

end Hypotheses

section Transfer

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **The hypotheses only see `M` through its localizations off `V(I) ∪ T`.** If `M` and `N` have
the same localizations at the primes where conditions (4) and (5) say something, the hypotheses
transfer from `M` to `N`. -/
public theorem algebraizationHypotheses_of_localizedEquiv
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
    {I J : Ideal A} {s d : ℤ} {omega : DerivedCategory (ModuleCat.{w} A)}
    {δ : PrimeSpectrum A → ℤ} {δmax δmin : ℤ}
    (H : AlgebraizationHypotheses (M := M) I J s d omega δ δmax δmin)
    (he : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) → p ∉ associatedSubset I J →
      (∃ q : PrimeSpectrum A, q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
        PrimeSpectrum.zeroLocus (J : Set A)) ∩ PrimeSpectrum.zeroLocus (I : Set A)) →
      Nonempty (LocalizedModule p.asIdeal.primeCompl M ≃ₗ[Localization.AtPrime p.asIdeal]
        LocalizedModule p.asIdeal.primeCompl N)) :
    AlgebraizationHypotheses (M := N) I J s d omega δ δmax δmin where
  adicComplete := H.adicComplete
  dualizing := H.dualizing
  cohomologicalDimension_le := H.cohomologicalDimension_le
  isDimensionFunction := H.isDimensionFunction
  isGreatest_δmax := H.isGreatest_δmax
  isLeast_δmin := H.isLeast_δmin
  depthOrDimensionBound p hpI hpT := by
    classical
    by_cases hq : ∃ q : PrimeSpectrum A,
      q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
        PrimeSpectrum.zeroLocus (J : Set A)) ∩ PrimeSpectrum.zeroLocus (I : Set A)
    · let e := (he p hpI hpT hq).some
      have hd := Module.depth_eq_depth_of_linearEquiv
        (maximalIdeal (Localization.AtPrime p.asIdeal)) e
      simpa only [hd] using H.depthOrDimensionBound p hpI hpT
    · exact Or.inr fun q h => False.elim (hq ⟨q, h⟩)
  supplementaryBound p hpI hpT hq hp := by
    let e := (he p hpI hpT hq).some
    have hd := Module.depth_eq_depth_of_linearEquiv
      (maximalIdeal (Localization.AtPrime p.asIdeal)) e
    have hdim := Module.supportDim_eq_of_equiv e
    simpa only [hd, hdim] using H.supplementaryBound p hpI hpT hq (by simpa only [hd] using hp)

/-- **The hypotheses descend along a drop of depth and support dimension by one.** If dividing by
a nonzerodivisor drops both depth and support dimension by exactly one wherever the depth is
below `s - 1`, the hypotheses for `M` at `s` give the hypotheses for the quotient at `s - 1`. -/
public theorem algebraizationHypotheses_of_depth_and_supportDim_succ
    {N : Type u} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (I J : Ideal A) (s d : ℤ) {omega : DerivedCategory (ModuleCat.{w} A)}
    {δ : PrimeSpectrum A → ℤ} {δmax δmin : ℤ}
    (H : AlgebraizationHypotheses (M := M) I J s d omega δ δmax δmin)
    (hdepth : ∀ p : PrimeSpectrum A,
      enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl N)) < ((s - 1 : ℤ) : EInt) →
      enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) =
      enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl N)) + (1 : EInt))
    (hdim : ∀ p : PrimeSpectrum A,
      enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl N)) < ((s - 1 : ℤ) : EInt) →
      krullDimToEInt
        (Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M)) =
      krullDimToEInt
        (Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl N)) + (1 : EInt)) :
    AlgebraizationHypotheses (M := N) I J (s - 1) d omega δ δmax δmin where
  adicComplete := H.adicComplete
  dualizing := H.dualizing
  cohomologicalDimension_le := H.cohomologicalDimension_le
  isDimensionFunction := H.isDimensionFunction
  isGreatest_δmax := H.isGreatest_δmax
  isLeast_δmin := H.isLeast_δmin
  depthOrDimensionBound p hpI hpT := by
    by_cases hp : ((s - 1 : ℤ) : EInt) ≤ enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl N))
    · exact Or.inl hp
    have hp' := lt_of_not_ge hp
    have hMp : enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) < (s : EInt) := by
      rw [hdepth p hp']
      exact (eint_add_int_lt_iff _ 1 s).2 hp'
    refine Or.inr fun q hq => ?_
    have h := (H.depthOrDimensionBound p hpI hpT).resolve_left (not_le_of_gt hMp) q hq
    rw [hdepth p hp', add_right_comm] at h
    have h' := (eint_int_lt_add_iff _ 1 (d + s)).1 h
    simpa only [show d + s - 1 = d + (s - 1) by omega] using h'
  supplementaryBound p hpI hpT hq hp := by
    have hMp : enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) < (s : EInt) := by
      rw [hdepth p hp]
      exact (eint_add_int_lt_iff _ 1 s).2 hp
    rcases H.supplementaryBound p hpI hpT hq hMp with h | h | h
    · left
      rw [hdim p hp] at h
      have h' := (eint_add_int_lt_iff _ 1 (s + 2)).1 h
      simpa only [show s + 2 - 1 = s - 1 + 2 by omega] using h'
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr fun q hq => ?_)
      have h' := h q hq
      rw [hdepth p hp, add_right_comm] at h'
      have h'' := (eint_int_lt_add_iff _ 1 (d + s + δmax - δmin - 2)).1 h'
      simpa only [show d + s + δmax - δmin - 2 - 1 =
        d + (s - 1) + δmax - δmin - 2 by omega] using h''

/-- **Dividing by a nonzerodivisor lowers `s` by one.** -/
public theorem algebraizationHypotheses_quotSMulTop
    {I J : Ideal A} {s d : ℤ} {omega : DerivedCategory (ModuleCat.{w} A)}
    {δ : PrimeSpectrum A → ℤ} {δmax δmin : ℤ}
    (H : AlgebraizationHypotheses (M := M) I J s d omega δ δmax δmin)
    (a : A) (ha : IsSMulRegular M a) :
    AlgebraizationHypotheses (M := QuotSMulTop a M) I J (s - 1) d omega δ δmax δmin :=
  algebraizationHypotheses_of_depth_and_supportDim_succ I J s d H
    (fun p hp => (depth_supportDim_succ_of_regular_quotient p a ha (s - 1) hp).1)
    (fun p hp => (depth_supportDim_succ_of_regular_quotient p a ha (s - 1) hp).2)

/-- **The hypotheses of Stacks 0EFL contain those of Stacks 0EFI.** Condition (3) of the source
supplies condition (3) of Stacks 0EFI through Stacks 0DXF: a prime outside `V(I)` has a
specialization in `V(I)`, hence — being in `T` — one in `V(J) ∩ V(I)`, along which the relative
dimension is at most `d`. -/
public theorem stabilizationHypotheses_of_algebraizationHypotheses
    (I J : Ideal A) (s d : ℤ) {omega : DerivedCategory (ModuleCat.{w} A)}
    {δ : PrimeSpectrum A → ℤ} {δmax δmin : ℤ}
    (H : AlgebraizationHypotheses (M := M) I J s d omega δ δmax δmin) :
    StabilizationHypotheses (M := M) I J s d omega where
  dualizing := H.dualizing
  depthOrDimensionBound := H.depthOrDimensionBound
  dimensionBound p _ hp := by
    have := H.adicComplete
    obtain ⟨q, hpq, hIq, hd⟩ := exists_specialization_dimension_le I p d
      H.cohomologicalDimension_le
    exact ⟨q, ⟨⟨hpq, (hp ⟨hpq, hIq⟩).1⟩, hIq⟩, hd⟩

/-- **Stacks 0EFI applies.** The stabilizing data of Stacks 0EFI exists under the hypotheses of
Stacks 0EFL, the nonnegativity of `d` that Stacks 0EFI needs being supplied by
`Stacks.Algebraization.nonneg_of_algebraizationHypotheses`. -/
public theorem exists_isStabilizingData_of_algebraizationHypotheses
    (I J : Ideal A) (s d : ℤ) {omega : DerivedCategory (ModuleCat.{u} A)}
    {δ : PrimeSpectrum A → ℤ} {δmax δmin : ℤ}
    (H : AlgebraizationHypotheses (M := M) I J s d omega δ δmax δmin) :
    ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p :=
  exists_isStabilizingData I J s d (nonneg_of_algebraizationHypotheses H) omega
    (stabilizationHypotheses_of_algebraizationHypotheses I J s d H)

end Transfer

section Induction

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- **Discarding the part of `M` supported in the bad locus.** There is a submodule `N ⊆ M` whose
local cohomology becomes derived `I`-complete after shrinking `J`, such that the quotient `M/N`
still satisfies the hypotheses and all of whose associated primes lie outside `V(I)`, outside `T`
and have a specialization in `V(J) ∩ V(I)`. -/
public theorem exists_reduced_quotient (I J : Ideal A) (s d : ℤ)
    {omega : DerivedCategory (ModuleCat.{w} A)} {δ : PrimeSpectrum A → ℤ} {δmax δmin : ℤ}
    (H : AlgebraizationHypotheses (M := M) I J s d omega δ δmax δmin) :
    ∃ N : Submodule A M,
      AlgebraizationHypotheses (M := M ⧸ N) I J s d omega δ δmax δmin ∧
      (∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A (M ⧸ N) →
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧
          p ∉ associatedSubset I J ∧
          ∃ q : PrimeSpectrum A, q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (J : Set A)) ∩ PrimeSpectrum.zeroLocus (I : Set A)) ∧
      ∃ J₀ : Ideal A, J₀ ≤ J ∧
        PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ∧
        ∀ J' : Ideal A, J' ≤ J₀ →
          PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
          IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J'
            J'.fg_of_isNoetherianRing).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A N))).obj := by
  classical
  have := H.adicComplete
  let S : Set (PrimeSpectrum A) := {p |
    p ∈ PrimeSpectrum.zeroLocus (I : Set A) ∨ p ∈ associatedSubset I J ∨
      ¬ ∃ q : PrimeSpectrum A, q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
        PrimeSpectrum.zeroLocus (J : Set A)) ∩ PrimeSpectrum.zeroLocus (I : Set A)}
  have hS : ∀ p ∈ S, ∀ q : PrimeSpectrum A, p ≤ q → q ∈ S := by
    intro p hp q hpq
    rcases hp with hp | hp | hp
    · exact Or.inl (show I ≤ q.asIdeal from hp.trans hpq)
    · exact Or.inr (Or.inl fun t ht => hp ⟨hpq.trans ht.1, ht.2⟩)
    · refine Or.inr (Or.inr ?_)
      rintro ⟨t, ht⟩
      exact hp ⟨t, ⟨⟨hpq.trans ht.1.1, ht.1.2⟩, ht.2⟩⟩
  obtain ⟨N, hN, hass⟩ :=
    exists_submodule_support_subset_and_associatedPrimes_quotient (M := M) S hS
  refine ⟨N, ?_, ?_, ?_⟩
  · refine algebraizationHypotheses_of_localizedEquiv H ?_
    intro p hpI hpT hq
    refine ⟨localizedQuotientEquivOfNotMemSupport N p ?_⟩
    intro hp
    rcases hN hp with h | h | h
    · exact hpI h
    · exact hpT h
    · exact h hq
  · intro p hp
    have h := hass p hp
    refine ⟨fun hpI => h (Or.inl hpI), fun hpT => h (Or.inr (Or.inl hpT)), ?_⟩
    by_contra hq
    exact h (Or.inr (Or.inr hq))
  · exact exists_ideal_isDerivedComplete_localCohomology_of_support I J
      (ModuleCat.of A N) fun p hp => hN hp

/-- **Stacks 0EFH in the reflection model of derived completion.** -/
public theorem exists_notMem_mem_annihilator_homology_completionFunctor_localCohomology
    (I J : Ideal A) (p : PrimeSpectrum A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hp : p ∉ PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d)
    (hdepth : ∀ x y : PrimeSpectrum A, x.asIdeal ≤ p.asIdeal →
      y ∈ PrimeSpectrum.zeroLocus (x.asIdeal : Set A) ∩
        (PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) →
      enatToEInt
          (Module.depth (Localization.AtPrime x.asIdeal)
            (maximalIdeal (Localization.AtPrime x.asIdeal))
            (LocalizedModule x.asIdeal.primeCompl M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime y.asIdeal) ⧸
            x.asIdeal.map (algebraMap A (Localization.AtPrime y.asIdeal)))) >
        ((d + s : ℤ) : EInt)) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ i : ℤ, i ≤ s →
      f ∈ Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((adicCompletionFunctor A I I.fg_of_isNoetherianRing).obj
            ((Dualizing.localCohomologyFunctor A J J.fg_of_isNoetherianRing).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                (ModuleCat.of A M))).obj)) := by
  classical
  obtain ⟨r, gen, hgen⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  change Ideal.span (Set.range gen) = I at hgen
  obtain ⟨f, hfp, hf⟩ :=
    exists_notMem_mem_annihilator_homology_derivedCompletion_localCohomology A M I J p s d
      omega homega hp hcd
      (fun x y hx hy hxy => by
        rw [show s + d = d + s by omega]
        exact hdepth x y hx ⟨hxy, hy⟩)
      gen hgen
  obtain ⟨e, -⟩ := exists_iso_derivedCompletionFunctor_completionFunctor I
    I.fg_of_isNoetherianRing gen hgen
    ((Dualizing.localCohomologyFunctor A J J.fg_of_isNoetherianRing).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M))).obj
  exact ⟨f, hfp, fun i hi => mem_annihilator_of_iso
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e).symm) (hf i hi)⟩

/-- **The nonzerodivisor of the inductive step.** Under the hypotheses of Stacks 0EFL at the
associated primes of `M`, there is a nonzerodivisor `f` on `M` annihilating the cohomology of
`RΓ_{V(J)}(M)^∧` in degrees `≤ s` and, after any admissible shrinking, the local cohomology of
`M` in degrees `≤ s`. The first is Stacks 0EFH together with the fact that no associated prime
contains the resulting annihilator; the second is the uniform annihilation of Stacks 0EFI. -/
public theorem exists_regular_annihilator_of_depth_bound
    (I J : Ideal A) (s d : ℤ) (omega : DerivedCategory (ModuleCat.{u} A))
    (HS : StabilizationHypotheses (M := M) I J s d omega)
    (hex : ∃ q : Ideal A × ℕ, IsStabilizingData (M := M) I J s q)
    (hcd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d)
    (hass : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧ p ∉ associatedSubset I J)
    (hdepth : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
      ∀ p' q : PrimeSpectrum A, p'.asIdeal ≤ p.asIdeal →
        q ∈ PrimeSpectrum.zeroLocus (p'.asIdeal : Set A) ∩
          (PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) →
        enatToEInt
            (Module.depth (Localization.AtPrime p'.asIdeal)
              (maximalIdeal (Localization.AtPrime p'.asIdeal))
              (LocalizedModule p'.asIdeal.primeCompl M)) +
          krullDimToEInt
            (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
              p'.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
          ((d + s : ℤ) : EInt)) :
    ∃ f : A, IsSMulRegular M f ∧
      (∀ i : ℤ, i ≤ s → f ∈ Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((adicCompletionFunctor A I I.fg_of_isNoetherianRing).obj
            ((Dualizing.localCohomologyFunctor A J J.fg_of_isNoetherianRing).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                (ModuleCat.of A M))).obj))) ∧
      ∀ J' : Ideal A, J' ≤ stabilizingIdeal I J s d omega HS →
        PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
        ∀ i : ℤ, i ≤ s → f ∈ Module.annihilator A
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
            ((Dualizing.localCohomologyFunctor A J' J'.fg_of_isNoetherianRing).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                (ModuleCat.of A M))).obj) := by
  classical
  let a : Ideal A := ⨅ i : ℤ, ⨅ (_ : i ≤ s), Module.annihilator A
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((adicCompletionFunctor A I I.fg_of_isNoetherianRing).obj
        ((Dualizing.localCohomologyFunctor A J J.fg_of_isNoetherianRing).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A M))).obj))
  have ha : ∀ p ∈ associatedPrimes A M, ¬ a ≤ p := by
    intro p hp
    let P : PrimeSpectrum A := ⟨p, hp.1⟩
    have hP : P ∉ PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) := fun h => (hass P hp).1 h.2
    obtain ⟨g, hgp, hg⟩ :=
      exists_notMem_mem_annihilator_homology_completionFunctor_localCohomology
        (M := M) I J P s d omega HS.dualizing hP hcd (hdepth P hp)
    exact fun hap => hgp (hap (by simpa only [a, Submodule.mem_iInf] using hg))
  obtain ⟨f, hf, hreg⟩ := exists_isSMulRegular_mem_mul_pow a I J
    (stabilizingIdeal I J s d omega HS) (stabilizingPower I J s d omega HS)
    (zeroLocus_stabilizingIdeal_inter I J s d omega HS) hass ha
  have hfa : f ∈ a := Ideal.mul_le_left hf
  have hfb : f ∈ (stabilizingIdeal I J s d omega HS * I) ^
      stabilizingPower I J s d omega HS := Ideal.mul_le_right hf
  exact ⟨f, hreg, fun i hi => (iInf_le_of_le i (iInf_le_of_le hi le_rfl) : a ≤ _) hfa,
    fun J' hJ' hV' i hi =>
      (isStabilizingData_stabilizingData I J s d omega HS hex).pow_mul_le_annihilator
        J' hJ' hV' i hi hfb⟩

omit [IsNoetherianRing A] in
/-- Shrinking to an intersection of two admissible ideals is admissible. -/
public theorem zeroLocus_inf_inter_eq {I J J₁ J₂ : Ideal A}
    (h₁ : PrimeSpectrum.zeroLocus (J₁ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (h₂ : PrimeSpectrum.zeroLocus (J₂ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    PrimeSpectrum.zeroLocus ((J₁ ⊓ J₂ : Ideal A) : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [PrimeSpectrum.zeroLocus_inf, Set.union_inter_distrib_right, h₁, h₂, Set.union_self]

/-- **The degree-zero case after shrinking.** For `J' ≤ J₀` with the stabilizing ideal `J₀`, the
completion unit is invertible on `H⁰` of `RΓ_{V(J')}(M)`: at `J₀` this is the degree-zero
statement, and the comparison from `J₀` to `J'` is inverted both by `H⁰` (Stacks 0EFI) and by
completion. -/
public theorem isIso_homology_zero_completionUnit_of_le_stabilizingIdeal
    (I J : Ideal A) (s d : ℤ) (omega : DerivedCategory (ModuleCat.{u} A))
    (HS : StabilizationHypotheses (M := M) I J s d omega)
    (hex : ∃ q : Ideal A × ℕ, IsStabilizingData (M := M) I J s q)
    (hcomplete : IsAdicComplete I A) (hs : 0 ≤ s)
    (J' : Ideal A) (hJ' : J' ≤ stabilizingIdeal I J s d omega HS)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
        ((Dualizing.localCohomologyFunctor A J' J'.fg_of_isNoetherianRing).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A M))).obj)) := by
  have := hcomplete
  have hdata := isStabilizingData_stabilizingData I J s d omega HS hex
  have hV₀ := zeroLocus_stabilizingIdeal_inter I J s d omega HS
  have hzero : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
        ((Dualizing.localCohomologyFunctor A (stabilizingIdeal I J s d omega HS)
          (stabilizingIdeal I J s d omega HS).fg_of_isNoetherianRing).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A M))).obj)) :=
    isIso_homology_zero_completionUnit_localCohomology_of_stable I
      (stabilizingIdeal I J s d omega HS) I.fg_of_isNoetherianRing
      (stabilizingIdeal I J s d omega HS).fg_of_isNoetherianRing (ModuleCat.of A M)
      fun L hL hVL => hdata.isIso L hL (hVL.trans hV₀) 0 hs
  have hg : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (localCohomologyComparison A (stabilizingIdeal I J s d omega HS) J'
        (stabilizingIdeal I J s d omega HS).fg_of_isNoetherianRing
        J'.fg_of_isNoetherianRing hJ'
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))) :=
    hdata.isIso J' hJ' hV 0 hs
  have hcg : IsIso ((adicCompletionFunctor A I I.fg_of_isNoetherianRing).map
      (localCohomologyComparison A (stabilizingIdeal I J s d omega HS) J'
        (stabilizingIdeal I J s d omega HS).fg_of_isNoetherianRing
        J'.fg_of_isNoetherianRing hJ'
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))) :=
    isIso_completionFunctor_map_localCohomologyComparison I
      (stabilizingIdeal I J s d omega HS) J' I.fg_of_isNoetherianRing
      (stabilizingIdeal I J s d omega HS).fg_of_isNoetherianRing J'.fg_of_isNoetherianRing hJ'
      _ (hV.trans hV₀.symm)
  exact isIso_map_unit_of_naturality (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0)
    (adicCompletionFunctor A I I.fg_of_isNoetherianRing)
    (adicCompletionUnit A I I.fg_of_isNoetherianRing)
    (localCohomologyComparison A (stabilizingIdeal I J s d omega HS) J'
      (stabilizingIdeal I J s d omega HS).fg_of_isNoetherianRing
      J'.fg_of_isNoetherianRing hJ'
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)))

end Induction

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **The induction of Stacks 0EFL.** For every natural number `n` and every `s ≥ n`, the ideal
of the conclusion exists with the comparison an isomorphism in degrees `≤ n`.

The base case is Stacks 0EFI together with Stacks 0EEX in degree zero and Stacks 0EEW in negative
degrees. The inductive step discards the submodule of `M` supported in `V(I) ∪ T`, chooses by
Stacks 0EFH a nonzerodivisor annihilating both sides in degree `n + 1`, and compares the two
long exact sequences of `0 → M → M → M/aM → 0`. -/
private theorem exists_ideal_isIso_homology_completionUnit
    (I J : Ideal A) (d : ℤ) (omega : DerivedCategory (ModuleCat.{u} A))
    {δ : PrimeSpectrum A → ℤ} {δmax δmin : ℤ} (n : ℕ) :
    ∀ {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
      (s : ℤ), (n : ℤ) ≤ s →
      AlgebraizationHypotheses (M := M) I J s d omega δ δmax δmin →
      ∃ J₀ : Ideal A, J₀ ≤ J ∧
        PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ∧
        ∀ J' : Ideal A, J' ≤ J₀ →
          PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
            PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
          ∀ i : ℤ, i ≤ n →
            IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
              ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
                ((Dualizing.localCohomologyFunctor A J'
                  J'.fg_of_isNoetherianRing).obj
                  ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                    (ModuleCat.of A M))).obj)) := by
  induction n with
  | zero =>
    intro M _ _ _ s hs H
    have hAC := H.adicComplete
    let HS := stabilizationHypotheses_of_algebraizationHypotheses I J s d H
    have hex := exists_isStabilizingData_of_algebraizationHypotheses I J s d H
    refine ⟨stabilizingIdeal I J s d omega HS,
      stabilizingIdeal_le I J s d omega HS,
      zeroLocus_stabilizingIdeal_inter I J s d omega HS, ?_⟩
    intro J' hJ' hV i hi
    obtain rfl | hi0 := eq_or_ne i 0
    · exact isIso_homology_zero_completionUnit_of_le_stabilizingIdeal I J s d omega HS hex
        hAC hs J' hJ' hV
    · exact isIso_homology_completionUnit_localCohomology_of_neg I J'
        I.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing (ModuleCat.of A M) i (by omega)
  | succ n ih =>
    intro M _ _ _ s hs H
    have hAC := H.adicComplete
    obtain ⟨N, HQ, hQ, JN, hJN, hVN, hcN⟩ := exists_reduced_quotient I J s d H
    let Q := M ⧸ N
    let HS := stabilizationHypotheses_of_algebraizationHypotheses I J s d HQ
    have hex := exists_isStabilizingData_of_algebraizationHypotheses I J s d HQ
    have hass : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A Q →
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) ∧ p ∉ associatedSubset I J :=
      fun p hp => ⟨(hQ p hp).1, (hQ p hp).2.1⟩
    have hd := depth_add_dimension_bound_of_associatedPrimes I J s d (by omega) HQ
      hass (fun p hp => (hQ p hp).2.2)
    obtain ⟨a, ha, hca, hla⟩ := exists_regular_annihilator_of_depth_bound
      I J s d omega HS hex HQ.cohomologicalDimension_le hass hd
    obtain ⟨J₁, hJ₁, hV₁, hu₁⟩ := ih (M := Q) s (by omega) HQ
    obtain ⟨J₂, hJ₂, hV₂, hu₂⟩ := ih (M := QuotSMulTop a Q) (s - 1) (by omega)
      (algebraizationHypotheses_quotSMulTop HQ a ha)
    let JS := stabilizingIdeal I J s d omega HS
    refine ⟨(JN ⊓ JS) ⊓ (J₁ ⊓ J₂), (inf_le_left.trans inf_le_left).trans hJN,
      zeroLocus_inf_inter_eq
        (zeroLocus_inf_inter_eq hVN (zeroLocus_stabilizingIdeal_inter I J s d omega HS))
        (zeroLocus_inf_inter_eq hV₁ hV₂), ?_⟩
    intro J' hJ' hV i hi
    have hJ'N : J' ≤ JN := hJ'.trans (inf_le_left.trans inf_le_left)
    have hJ'S : J' ≤ JS := hJ'.trans (inf_le_left.trans inf_le_right)
    have hJ'₁ : J' ≤ J₁ := hJ'.trans (inf_le_right.trans inf_le_left)
    have hJ'₂ : J' ≤ J₂ := hJ'.trans (inf_le_right.trans inf_le_right)
    have huQ : ∀ j : ℤ, j ≤ (n + 1 : ℕ) →
        IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
          ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
            ((Dualizing.localCohomologyFunctor A J' J'.fg_of_isNoetherianRing).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                (ModuleCat.of A Q))).obj)) := by
      intro j hj
      by_cases hjn : j ≤ (n : ℤ)
      · exact hu₁ J' hJ'₁ hV j hjn
      · obtain rfl : j = (n + 1 : ℕ) := by omega
        have hJ'J : J' ≤ J := hJ'₁.trans hJ₁
        have hg : IsIso ((adicCompletionFunctor A I I.fg_of_isNoetherianRing).map
            (localCohomologyComparison A J J' J.fg_of_isNoetherianRing
              J'.fg_of_isNoetherianRing hJ'J
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                (ModuleCat.of A Q)))) :=
          isIso_completionFunctor_map_localCohomologyComparison I J J'
            I.fg_of_isNoetherianRing J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing hJ'J
            _ hV
        let e := ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n + 1)).mapIso
          (asIso ((adicCompletionFunctor A I I.fg_of_isNoetherianRing).map
            (localCohomologyComparison A J J' J.fg_of_isNoetherianRing
              J'.fg_of_isNoetherianRing hJ'J
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
                (ModuleCat.of A Q)))))).toLinearEquiv
        have hca' := hca (n + 1) (by omega)
        rw [e.annihilator_eq] at hca'
        exact completionUnit_localCohomology_isIso_of_regular_annihilator I J'
          I.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing (ModuleCat.of A Q) a ha
          n (n + 1) rfl (hla J' hJ'S hV (n + 1) (by omega)) hca'
          (hu₁ J' hJ'₁ hV n le_rfl) (hu₂ J' hJ'₂ hV n le_rfl)
    exact completionUnit_localCohomology_isIso_of_shortExact I J'
      I.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing
      (ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by
        ext x
        exact LinearMap.exact_subtype_mkQ N |>.apply_apply_eq_zero x))
      (ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ N)
        N.injective_subtype N.mkQ_surjective)
      (hcN J' hJ'N hV) i (fun j hj => huQ j (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
        rcases hj with hj | hj <;> omega))

/-- If the unit of derived completion is invertible on `H^i` of `RΓ_{J'}(M)`, so is the comparison
`RΓ_{J'}(M) ⟶ RΓ_J(M)^∧` on `H^i`, since it is that unit followed by an isomorphism. -/
private theorem isIso_homology_localCohomologyToCompletedLocalCohomology_of_isIso_unit
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J J' : Ideal A)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) (i : ℤ)
    (hunit : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
        ((Dualizing.localCohomologyFunctor A J' J'.fg_of_isNoetherianRing).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A M))).obj))) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyToCompletedLocalCohomology A I J J' I.fg_of_isNoetherianRing
        J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing (ModuleCat.of A M) hV)) := by
  rw [show (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      (localCohomologyToCompletedLocalCohomology A I J J' I.fg_of_isNoetherianRing
        J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing (ModuleCat.of A M) hV) = _ ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
        (completedLocalCohomologyShrinkIso A I J J' I.fg_of_isNoetherianRing
          J.fg_of_isNoetherianRing J'.fg_of_isNoetherianRing (ModuleCat.of A M) hV).hom from
    Functor.map_comp _ _ _]
  exact IsIso.comp_isIso' hunit inferInstance

/-- **Stacks 0EFL when `V(J) ∩ V(I)` is empty.** For an `I`-adically complete Noetherian ring and
ideals with `V(J) ∩ V(I) = ∅`, the ideal `J` itself has the property asserted of `J₀`, in every
degree and for every finite module.

This is the case of the source that the extreme values `δmax` and `δmin` of
`Stacks.Algebraization.AlgebraizationHypotheses` exclude, and it is not vacuous: `J = A` is an
instance. The source's conditions hold in it with no constraint beyond (1), because its condition
(5), the only one mentioning `δ`, is guarded by `V(𝔭) ∩ V(J) ∩ V(I) ≠ ∅`.

Completeness is what makes the case true. Since `I` lies in the Jacobson radical of an
`I`-adically complete ring, every prime has a specialization in `V(I)`, so an admissible
shrinking `J'` has `V(J') ∩ V(I) = ∅` only if `V(J')` is empty — that is, only for `J' = A`.
Then `RΓ_{J'}(M)` is supported on the empty set, hence already derived `I`-complete, so the unit
of derived completion is invertible at it; both sides are in fact zero. -/
@[stacks 0EFL "existence of J₀ in the case V(J) ∩ V(I) = ∅, which the δmax and δmin fields of
AlgebraizationHypotheses exclude and the source does not: the source's condition (5), the only
one naming δ, is guarded by V(𝔭) ∩ V(J) ∩ V(I) ≠ ∅ and so is vacuous here. J₀ = J serves, for
every s and on I-adic completeness alone. With exists_isAlgebraizationIdeal, which is the
nonempty case, this covers the tag"]
public theorem isAlgebraizationIdeal_of_zeroLocus_inter_eq_empty
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) (hcomplete : IsAdicComplete I A)
    (hJI : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) = ∅) :
    IsAlgebraizationIdeal (M := M) I J s J where
  le := le_rfl
  zeroLocus_inter := rfl
  isIso J' _ hV i _ := by
    have := hcomplete
    have hJ'empty : PrimeSpectrum.zeroLocus (J' : Set A) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => ?_
      obtain ⟨m, hm, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
      have hIm : I ≤ m := (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hm⟩)
      have hmem : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈
          PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) :=
        ⟨hq.trans hqm, hIm⟩
      rwa [hV, hJI] at hmem
    have hdc := isDerivedComplete_localCohomology_of_disjoint_support I J'
      J'.fg_of_isNoetherianRing (ModuleCat.of A M) (by rw [hJ'empty, Set.inter_empty])
    have := isIso_completionUnit_of_derivedComplete I I.fg_of_isNoetherianRing _ hdc
    exact isIso_homology_localCohomologyToCompletedLocalCohomology_of_isIso_unit I J J' hV i
      inferInstance

/-- **Stacks 0EFL.** Let `I` and `J` be ideals of a Noetherian ring `A`, let `M` be a finite
`A`-module and let `s` and `d` be integers. Under conditions (1), (3), (4) and (5)
of the source there is an ideal `J₀ ⊆ J` with `V(J₀) ∩ V(I) = V(J) ∩ V(I)` such that for every
further ideal `J' ⊆ J₀` with the same intersection with `V(I)` the canonical map

`RΓ_{J'}(M) ⟶ RΓ_J(M)^∧`

is an isomorphism on cohomology in all degrees `≤ s`.

The proof is the source's induction on `s`; the arrow is
`Stacks.Algebraization.localCohomologyToCompletedLocalCohomology`, the composite of the unit of
derived `I`-adic completion with the identification `RΓ_{J'}(M)^∧ ≅ RΓ_J(M)^∧` of the opening
paragraph of the source, and the latter is invertible, so the assertion is exactly that the unit
is invertible on cohomology in degrees `≤ s`. The case `s < 0`, where both sides vanish in the
relevant degrees and `J₀ = J` serves, is
`Stacks.Algebraization.isAlgebraizationIdeal_of_lt_zero`. -/
@[stacks 0EFL "existence of J₀ in the case V(J) ∩ V(I) ≠ ∅, which is what the δmax and δmin
fields of AlgebraizationHypotheses presuppose; the empty case, where the source's condition (5)
is vacuous, is isAlgebraizationIdeal_of_zeroLocus_inter_eq_empty, and the two together are the
tag. The dualizing complex is taken in the ring's own module universe"]
public theorem exists_isAlgebraizationIdeal
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ) (omega : DerivedCategory (ModuleCat.{u} A))
    (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ)
    (H : AlgebraizationHypotheses (M := M) I J s d omega δ δmax δmin) :
    ∃ J₀ : Ideal A, IsAlgebraizationIdeal (M := M) I J s J₀ := by
  by_cases hs : 0 ≤ s
  swap
  · exact ⟨J, isAlgebraizationIdeal_of_lt_zero I J s d omega δ δmax δmin H (by omega)⟩
  obtain ⟨J₀, hJ₀, hV₀, hu⟩ := exists_ideal_isIso_homology_completionUnit I J d omega
    s.toNat (M := M) s (by simpa only [Int.toNat_of_nonneg hs] using le_refl s) H
  refine ⟨J₀, hJ₀, hV₀, fun J' hJ' hV i hi => ?_⟩
  exact isIso_homology_localCohomologyToCompletedLocalCohomology_of_isIso_unit I J J' hV i
    (hu J' hJ' hV i (by simpa only [Int.toNat_of_nonneg hs] using hi))

end Main

end Stacks.Algebraization

end
