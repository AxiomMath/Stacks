module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletedComplementSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsSupplementaryBound

/-!
# Stacks 0EFL applies at `s = 1` under the hypotheses of Stacks 0EIF

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` which is `I`-adically complete and admits a
dualizing complex, and let `M` be a finite `A`-module. The proof of Stacks 0EIF opens by applying
Stacks 0EFL with `s = 1`, `J = 𝔞` and `d = cd(A, I)`: *"Thus the hypotheses of Lemma 52.8.5 are
satisfied for `s = 1` and `d`; here we use condition (3)."* This file carries out that
verification and draws the conclusion: an ideal `J₀ ⊆ 𝔞` with `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` such
that for every further `J' ⊆ J₀` with the same trace on `V(I)` the comparison

`RΓ_{J'}(M) ⟶ RΓ_𝔞(M)^∧`

is an isomorphism on cohomology in degrees `0` and `1`.

Conditions (2) and (3) of Stacks 0EIF enter in their ring-theoretic form, at the associated
primes of `M` rather than at the associated points of the coherent module on
`U = Spec(A) ∖ V(𝔞)`; the comparison of the two is a separate matter, as is the existence of the
extreme values `δmax` and `δmin`, which condition (3)(b) supplies through
`Stacks.Algebraization.exists_isGreatest_isLeast_of_le_add_two`.

## Main results

* `Stacks.Algebraization.algebraizationHypotheses_of_closureLocalDimension` — conditions (1),
  (2) and (3) of Stacks 0EIF give the hypotheses of Stacks 0EFL at `s = 1`.
* `Stacks.Algebraization.exists_isAlgebraizationIdeal_of_closureLocalDimension` — hence the
  ideal `J₀` of Stacks 0EFL exists at `s = 1`.
* `Stacks.Algebraization.exists_ideal_isIso_homology_zero_completionUnit_complement` — joining
  that to the completed localization triangle: for a suitable `J₀ ⊆ 𝔞` with
  `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` and `V = Spec(A) ∖ V(J₀)`, the completion unit
  `Γ(V, M̃) ⟶ H⁰(RΓ(V, M̃)^∧)` is an isomorphism.

## Implementation notes

Condition (3) of Stacks 0EIF appears as a disjunction of the ring-theoretic form of (3)(a) — the
support of `M_𝔭` has dimension at most `0` at the associated primes off `V(I)` — and of the
numerical consequence `δmax ≤ δmin + 2` of (3)(b). The first settles alternative (a) of
condition (5) of Stacks 0EFL and the second settles alternative (c); condition (4) is settled by
condition (2) of Stacks 0EIF in either case.

Condition (5) of Stacks 0EFL is stated against the extreme values of `δ` on `V(𝔞) ∩ V(I)`, which
are therefore hypotheses here rather than conclusions. Under condition (3)(b) they exist; under
condition (3)(a) their existence is the boundedness of a dimension function on the spectrum of a
Noetherian ring with a dualizing complex, which is not isolated in this library (it is inlined in
the proof of Stacks 0A80).

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **The hypotheses of Stacks 0EFL at `s = 1`, from conditions (1), (2) and (3) of
Stacks 0EIF.**

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` which is `I`-adically complete, let `ω` be a
dualizing complex, let `M` be a finite `A`-module and let `d` bound `cd(A, I)`. Let `δ` be a
dimension function with greatest value `δmax` and least value `δmin` on `V(𝔞) ∩ V(I)`. Assume

* condition (2) of Stacks 0EIF: at every associated prime `𝔭` of `M` off `V(I)` whose closure
  meets `V(I)` outside `V(𝔞)`, every `𝔮 ⊇ 𝔭` containing `𝔞` has
  `dim(𝒪_{closure {𝔭}, 𝔮}) > d + 1`;
* condition (3) of Stacks 0EIF, in one of its two forms: either the support of `M_𝔭` has
  dimension at most `0` at every associated prime `𝔭` off `V(I)` — the ring-theoretic content of
  `(S₁)` off `V(I)` — or `δmax ≤ δmin + 2`.

Then `M` satisfies the hypotheses of Stacks 0EFL for `s = 1`. -/
theorem algebraizationHypotheses_of_closureLocalDimension
    (I a : Ideal A) (d : ℤ)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{w} A))
    (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ)
    (hcomplete : IsAdicComplete I A)
    (hdualizing : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d)
    (hδ : IsDimensionFunctionProp δ)
    (hmax : IsGreatest (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A))) δmax)
    (hmin : IsLeast (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A))) δmin)
    (hbound : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
      ¬ I ≤ p.asIdeal →
      (∃ y : PrimeSpectrum A, p.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
      ∀ z : PrimeSpectrum A, p.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
        ((d + 1 : ℤ) : EInt) < krullDimToEInt (closureLocalDimension A p z))
    (hthird :
      (∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M → ¬ I ≤ p.asIdeal →
        Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M) ≤ (0 : WithBot ℕ∞)) ∨
      δmax ≤ δmin + 2) :
    AlgebraizationHypotheses (M := M) I a 1 d omega δ δmax δmin where
  adicComplete := hcomplete
  dualizing := hdualizing
  cohomologicalDimension_le := hd
  depthOrDimensionBound p hpI hpT :=
    depthOrDimensionBound_of_closureLocalDimension I a d (M := M) hbound p hpI hpT
  isDimensionFunction := hδ
  isGreatest_δmax := hmax
  isLeast_δmin := hmin
  supplementaryBound p hpI hpT hne hdep := by
    rcases hthird with hS | hle
    · exact supplementaryBound_of_supportDim I a d δ δmax δmin (M := M) hS p hpI hpT hne hdep
    · exact supplementaryBound_of_le_add_two I a d δ δmax δmin hle (M := M) hbound p hpI hpT
        hne hdep

/-- **Stacks 0EFL applies at `s = 1` under the hypotheses of Stacks 0EIF.** Under conditions (1),
(2) and (3) of Stacks 0EIF — in the ring-theoretic form of
`Stacks.Algebraization.algebraizationHypotheses_of_closureLocalDimension` — there is an ideal
`J₀ ⊆ 𝔞` with `V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` such that for every further ideal `J' ⊆ J₀` with the
same trace on `V(I)` the canonical map `RΓ_{J'}(M) ⟶ RΓ_𝔞(M)^∧` is an isomorphism on cohomology
in every degree `≤ 1`, in particular in degrees `0` and `1`.

This is the first half of the source's proof of Stacks 0EIF. -/
theorem exists_isAlgebraizationIdeal_of_closureLocalDimension
    (I a : Ideal A) (d : ℤ)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{u} A))
    (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ)
    (hcomplete : IsAdicComplete I A)
    (hdualizing : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d)
    (hδ : IsDimensionFunctionProp δ)
    (hmax : IsGreatest (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A))) δmax)
    (hmin : IsLeast (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A))) δmin)
    (hbound : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
      ¬ I ≤ p.asIdeal →
      (∃ y : PrimeSpectrum A, p.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
      ∀ z : PrimeSpectrum A, p.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
        ((d + 1 : ℤ) : EInt) < krullDimToEInt (closureLocalDimension A p z))
    (hthird :
      (∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M → ¬ I ≤ p.asIdeal →
        Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M) ≤ (0 : WithBot ℕ∞)) ∨
      δmax ≤ δmin + 2) :
    ∃ J₀ : Ideal A, IsAlgebraizationIdeal (M := M) I a 1 J₀ :=
  exists_isAlgebraizationIdeal I a 1 d omega δ δmax δmin
    (algebraizationHypotheses_of_closureLocalDimension I a d omega δ δmax δmin hcomplete
      hdualizing hd hδ hmax hmin hbound hthird)

/-- **The two halves of the proof of Stacks 0EIF, joined.** Under conditions (1), (2) and (3) of
Stacks 0EIF in the ring-theoretic form above there is an ideal `J₀ ⊆ 𝔞` with
`V(J₀) ∩ V(I) = V(𝔞) ∩ V(I)` for which the unit of derived `I`-adic completion is invertible on
`H⁰` of the derived sections of `M̃` on `V = Spec(A) ∖ V(J₀)`:

`Γ(V, M̃) ⟶ H⁰(RΓ(V, M̃)^∧)`

is an isomorphism, for every localization triangle datum of `J₀`.

Stacks 0EFL supplies `J₀` and the invertibility of `RΓ_{J₀}(M) ⟶ RΓ_𝔞(M)^∧` on cohomology in
degrees `0` and `1`; `Stacks.Algebraization.isIso_homology_zero_completionUnit_complement` turns
that into the statement above by completing the localization triangle of `J₀` and applying the
five lemma at its third vertex. -/
theorem exists_ideal_isIso_homology_zero_completionUnit_complement
    (I a : Ideal A) (d : ℤ)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{u} A))
    (δ : PrimeSpectrum A → ℤ) (δmax δmin : ℤ)
    (hcomplete : IsAdicComplete I A)
    (hdualizing : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hd : Stacks.LocalCohomology.cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ d)
    (hδ : IsDimensionFunctionProp δ)
    (hmax : IsGreatest (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A))) δmax)
    (hmin : IsLeast (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A))) δmin)
    (hbound : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
      ¬ I ≤ p.asIdeal →
      (∃ y : PrimeSpectrum A, p.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
      ∀ z : PrimeSpectrum A, p.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
        ((d + 1 : ℤ) : EInt) < krullDimToEInt (closureLocalDimension A p z))
    (hthird :
      (∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M → ¬ I ≤ p.asIdeal →
        Module.supportDim (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl M) ≤ (0 : WithBot ℕ∞)) ∨
      δmax ≤ δmin + 2) :
    ∃ J₀ : Ideal A, J₀ ≤ a ∧
      ∃ _hV : PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A),
        ∀ D : Stacks.LocalCohomology.LocalizationTriangleData.{u, u} A J₀
          J₀.fg_of_isNoetherianRing,
          IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((adicCompletionUnit A I I.fg_of_isNoetherianRing).app
              (D.complement.obj (ModuleCat.of A M)))) := by
  obtain ⟨J₀, hle, hV₀, hiso⟩ := exists_isAlgebraizationIdeal_of_closureLocalDimension
    I a d (M := M) omega δ δmax δmin hcomplete hdualizing hd hδ hmax hmin hbound hthird
  refine ⟨J₀, hle, hV₀, fun D => ?_⟩
  exact isIso_homology_zero_completionUnit_complement I a J₀ hcomplete (ModuleCat.of A M) hV₀ D
    (fun i hi => hiso J₀ le_rfl hV₀ i hi)

end Stacks.Algebraization

end
