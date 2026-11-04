module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.KollarCriterionAssembled

/-!
# [Stacks, Tag 0BL9]: finiteness of the first local cohomology module

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `Z = V(I)` and `M` a finite `A`-module.
[Stacks, Tag 0BL9] characterises finiteness of `H¹_Z(M)`: it holds exactly when, for every
associated prime `𝔭` of `M` with `𝔭 ∉ Z` and every `𝔮 ∈ V(𝔭 + I)`, the completion of `(A/𝔭)_𝔮`
has no associated prime of dimension `1`.

`StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FirstLocalCohomologyFiniteness`
proves everything that equivalence needs apart from Kollár's criterion, [Stacks, Tag 0BK3], at
the one open immersion `U = Spec A \ Z ⟶ Spec A` and the one coherent module `M̃|_U`. The tag is
stated here instead of there because the criterion is proved downstream of that module: it is
`Stacks.LocalCohomology.isCoherent_pushforward_iff_forall_two_le_ringKrullDim`, and it rests on
[Stacks, Tag 0BK1], whose module imports `FirstLocalCohomologyFiniteness` for the identification
of the reduced closure of a point of an affine scheme with the spectrum of the quotient.

## Main results

* `Stacks.LocalCohomology.finite_localCohomologyModule_one_iff_forall_ringKrullDim_ne_one`:
  **[Stacks, Tag 0BL9]**.

## References

* [Stacks Project, Tag 0BL9](https://stacks.math.columbia.edu/tag/0BL9)
* [Stacks Project, Tag 0BK3](https://stacks.math.columbia.edu/tag/0BK3)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BK4](https://stacks.math.columbia.edu/tag/0BK4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
open Stacks.AlgebraicGeometry.CodimensionOneObstruction (isAssociatedPoint_restrict_iff)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-- **[Stacks, Tag 0BL9].** Let `A` be a Noetherian ring, `I` an ideal, `Z = V(I)` and `M` a
finite `A`-module. Then `H¹_Z(M)` is a finite `A`-module if and only if for every prime `𝔭`
associated to `M` with `I ⊄ 𝔭`, and every prime `𝔮 ⊇ 𝔭 + I`, the completion of `(A/𝔭)_𝔮` has no
associated prime `𝔯` with `dim((A/𝔭)^∧_𝔮 / 𝔯) = 1`.

Kollár's criterion, [Stacks, Tag 0BK3], enters at the open immersion `U = Spec A \ Z ⟶ Spec A`
and the coherent module `M̃|_U`, as `isCoherent_pushforward_iff_forall_two_le_ringKrullDim`. The
rest of the proof is the composite of
`finite_localCohomologyModule_one_iff_isCoherent_pushforward`, which turns finiteness of
`H¹_Z(M)` into coherence of the direct image, and the translation of the geometric condition:
`isAssociatedPoint_tilde_iff` together with `isAssociatedPoint_restrict_iff` identifies the
associated points of `M̃|_U` with the associated primes of `M` outside `Z`,
`forall_adicCompletion_pointClosure_iff` and `forall_quotientPrime_iff` rewrite the condition at
the reduced closure of such a point as a condition on the completions of `(A/𝔭)_𝔮`, and
`one_le_ringKrullDim_quotient_adicCompletion_localization` trades `2 ≤ dim` for `dim ≠ 1`. -/
@[stacks 0BL9]
theorem finite_localCohomologyModule_one_iff_forall_ringKrullDim_ne_one (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A) [Module.Finite A M] :
    Module.Finite A (localCohomologyModule A I I.fg_of_isNoetherianRing M 1) ↔
      ∀ (p q : PrimeSpectrum A), IsAssociatedPrimeStacks A M p.asIdeal → ¬ I ≤ p.asIdeal →
        ∀ hpq : p.asIdeal ≤ q.asIdeal, I ≤ q.asIdeal →
        let J := q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)
        letI : J.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hpq
        let B := Localization.AtPrime J
        let R := AdicCompletion (J.map (algebraMap (A ⧸ p.asIdeal) B)) B
        ∀ r : Ideal R, IsAssociatedPrimeStacks R R r → ringKrullDim (R ⧸ r) ≠ 1 := by
  classical
  have : (complementTilde A I M).IsCoherent := isCoherent_complementTilde A I M
  refine (finite_localCohomologyModule_one_iff_isCoherent_pushforward A I M).trans
    ((isCoherent_pushforward_iff_forall_two_le_ringKrullDim
      (complementZeroLocus A I).ι (complementTilde A I M)).trans ?_)
  -- The associated points of `M̃|_U` are the associated primes of `M` not containing `I`.
  have hassoc (x : (complementZeroLocus A I : Scheme)) :
      x ∈ Stacks.Divisors.associatedPoints (complementTilde A I M) ↔
        IsAssociatedPrimeStacks A M x.1.asIdeal :=
    (isAssociatedPoint_restrict_iff (complementZeroLocus A I).ι
        ((tilde.functor (CommRingCat.of A)).obj M) x).trans
      (isAssociatedPoint_tilde_iff A M x.1)
  -- A point of `Spec A` lies outside `U` exactly when its prime contains `I`.
  have hboundary (q : Spec (CommRingCat.of A)) :
      q ∉ Set.range (complementZeroLocus A I).ι.base ↔ I ≤ q.asIdeal := by
    rw [Scheme.Opens.range_ι]
    exact not_not
  -- `2 ≤ dim` and `dim ≠ 1` agree because `1 ≤ dim` is automatic.
  have hdim (p : PrimeSpectrum A) (hpI : ¬ I ≤ p.asIdeal) :
      (∀ z : PrimeSpectrum (A ⧸ p.asIdeal),
        I ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal) z).asIdeal →
        let B := Localization.AtPrime z.asIdeal
        let R := AdicCompletion (maximalIdeal B) B
        ∀ r : Ideal R, IsAssociatedPrimeStacks R R r →
          (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ r)) ↔
      (∀ z : PrimeSpectrum (A ⧸ p.asIdeal),
        I ≤ (PrimeSpectrum.comap (Ideal.Quotient.mk p.asIdeal) z).asIdeal →
        let B := Localization.AtPrime z.asIdeal
        let R := AdicCompletion (maximalIdeal B) B
        ∀ r : Ideal R, IsAssociatedPrimeStacks R R r → ringKrullDim (R ⧸ r) ≠ 1) := by
    refine forall_congr' fun z => forall_congr' fun hz => ?_
    dsimp only
    refine forall_congr' fun r => forall_congr' fun hr => ?_
    have h := one_le_ringKrullDim_quotient_adicCompletion_localization A I p hpI z hz r hr
    exact (ENat.WithBot.add_one_le_iff (n := 1)).trans
      ⟨fun hd h1 => lt_irrefl _ (hd.trans_eq h1), fun hd => lt_of_le_of_ne h (Ne.symm hd)⟩
  refine ⟨fun h p q hp hpI hpq hq => ?_, fun h x hx w hw => ?_⟩
  · have hx := h ⟨p, hpI⟩ ((hassoc ⟨p, hpI⟩).mpr hp)
    have hc := (forall_adicCompletion_pointClosure_iff A I p
      (fun d => (2 : WithBot ℕ∞) ≤ d)).mp (fun w hw => hx w ((hboundary _).mpr hw))
    exact (forall_quotientPrime_iff A I p.asIdeal (fun d => d ≠ 1)).mp
      ((hdim p hpI).mp hc) q hpq hq
  · refine (forall_adicCompletion_pointClosure_iff A I x.1
      (fun d => (2 : WithBot ℕ∞) ≤ d)).mpr ?_ w ((hboundary _).mp hw)
    exact (hdim x.1 x.2).mpr
      ((forall_quotientPrime_iff A I x.1.asIdeal (fun d => d ≠ 1)).mpr
        (fun q hpq hq => h x.1 q ((hassoc x).mp hx) x.2 hpq hq))

end Stacks.LocalCohomology

end
