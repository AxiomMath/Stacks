module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.NearVanishing
public import StacksFrontier.RingTheory.Serre.Defs

/-!
# Condition (2) of Stacks 0EIF in the currency of Stacks 0EFL

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and let `M` be a finite `A`-module. Condition (2)
of Stacks 0EIF bounds `dim(𝒪_{closure {x}, z})` from below at the associated points `x` of the
coherent module off `V(I)`; condition (4) of Stacks 0EFL asks, at `s = 1`, that every prime `𝔭`
off `V(I)` and off `T = Stacks.Algebraization.associatedSubset I 𝔞` either have
`depth(M_𝔭) ≥ 1` or satisfy `depth(M_𝔭) + dim((A/𝔭)_𝔮) > d + 1` for every
`𝔮 ∈ V(𝔭) ∩ V(𝔞) ∩ V(I)`.

The source's proof of Stacks 0EIF derives the second from the first in one sentence: *"Then
either `𝔭` is not an associated prime of `M` and hence `depth(M_𝔭) ≥ 1` or we have
`dim((A/𝔭)_𝔮) > d + 1` by (2)."* This file is that sentence. The two halves are the equivalence
"`depth(M_𝔭) = 0` exactly at the associated primes" and the identification of
`Stacks.Algebraization.closureLocalDimension`, the invariant condition (2) is phrased with, with
`dim((A/𝔭)_𝔮)`.

The hypothesis is taken at the ring-theoretic associated primes of `M` rather than at the
associated points of the coherent module on `U = Spec(A) ∖ V(𝔞)`; the comparison of the two is a
separate matter.

## Main results

* `Stacks.Algebraization.closureLocalDimension_eq_ringKrullDim_localizedQuotient` — the
  dimension of the interval of primes between `𝔭` and `𝔮` is `dim((A/𝔭)_𝔮)`.
* `Stacks.Algebraization.krullDimToEInt_closureLocalDimension_eq` — through a dimension
  function that dimension is `δ(𝔭) - δ(𝔮)`.
* `Stacks.Algebraization.exists_mem_zeroLocus_notMem_zeroLocus_of_notMem_associatedSubset` — a
  prime off `T` has a specialization in `V(I)` outside `V(𝔞)`, which is the hypothesis that
  condition (2) of Stacks 0EIF carries.
* `Stacks.Algebraization.depthOrDimensionBound_of_closureLocalDimension` — **condition (4) of
  Stacks 0EFL at `s = 1`**, from condition (2) of Stacks 0EIF.

## Implementation notes

`Stacks.Algebraization.closureLocalDimension_eq_ringKrullDim_localizedQuotient` restates, as a
public declaration, a one-line consequence of the public
`Stacks.Algebraization.primeSpectrumLocalizedQuotientOrderIso` which until now existed only as a
`private` lemma inside the application of Stacks 0EG5.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
* [Stacks Project, Tag 0EFG](https://stacks.math.columbia.edu/tag/0EFG)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A]

/-- The value of `Stacks.Algebraization.enatToEInt` at zero. -/
private theorem enatToEInt_zero : enatToEInt (0 : ℕ∞) = (0 : EInt) := rfl

/-- The value of `Stacks.Algebraization.enatToEInt` at one. -/
private theorem enatToEInt_one : enatToEInt (1 : ℕ∞) = ((1 : ℤ) : EInt) := rfl

/-- The dimension of the local ring of the closure of `𝔭` at a specialization `𝔮` is the Krull
dimension of `(A_𝔮)/(𝔭 A_𝔮)`: the spectrum of that ring is the interval of primes between `𝔭`
and `𝔮`. -/
theorem closureLocalDimension_eq_ringKrullDim_localizedQuotient (p q : PrimeSpectrum A) :
    closureLocalDimension A p q =
      ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal))) :=
  (Order.krullDim_eq_of_orderIso (primeSpectrumLocalizedQuotientOrderIso p q)).symm

/-- **The dimension of the closure through a dimension function.** For a dimension function `δ`
in the sense of Stacks 02I9 and primes `𝔭 ≤ 𝔮`, the dimension of the local ring of the closure
of `𝔭` at `𝔮` is `δ(𝔭) - δ(𝔮)`. -/
theorem krullDimToEInt_closureLocalDimension_eq [IsNoetherianRing A]
    {δ : PrimeSpectrum A → ℤ} (hδ : IsDimensionFunctionProp δ)
    (p q : PrimeSpectrum A) (hpq : p ≤ q) :
    krullDimToEInt (closureLocalDimension A p q) = ((δ p - δ q : ℤ) : EInt) := by
  rw [closureLocalDimension_eq_ringKrullDim_localizedQuotient]
  exact krullDimToEInt_localizedQuotient_eq hδ p q hpq

/-- **A prime outside `T` has a specialization in `V(I)` off `V(𝔞)`.** The subset
`T = Stacks.Algebraization.associatedSubset I 𝔞` of Stacks 0EFG consists of the primes `𝔭` with
`V(𝔭) ∩ V(I) ⊆ V(𝔞) ∩ V(I)`, so a prime outside it admits a prime above it which contains `I`
and does not contain `𝔞`. That is exactly the hypothesis `closure {x} ∩ V(I) ⊄ V(𝔞)` under which
condition (2) of Stacks 0EIF gives its bound. -/
theorem exists_mem_zeroLocus_notMem_zeroLocus_of_notMem_associatedSubset
    (I a : Ideal A) (p : PrimeSpectrum A) (hp : p ∉ associatedSubset I a) :
    ∃ y : PrimeSpectrum A, p.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal := by
  simp only [associatedSubset, Set.mem_ofPred_eq, Set.not_subset] at hp
  obtain ⟨y, hy, hy'⟩ := hp
  refine ⟨y, (PrimeSpectrum.mem_zeroLocus _ _).1 hy.1, (PrimeSpectrum.mem_zeroLocus _ _).1 hy.2,
    fun hay => hy' ⟨(PrimeSpectrum.mem_zeroLocus _ _).2 hay, hy.2⟩⟩

/-- **Condition (4) of Stacks 0EFL at `s = 1`, from condition (2) of Stacks 0EIF.**

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `M` be a finite `A`-module and let `d` be an
integer. Assume that for every associated prime `𝔭` of `M` which does not contain `I` and which
has a specialization containing `I` but not `𝔞`, every `𝔮 ⊇ 𝔭` containing `𝔞` has
`dim(𝒪_{closure {𝔭}, 𝔮}) > d + 1`. Then every prime `𝔭` outside `V(I)` and outside
`T = Stacks.Algebraization.associatedSubset I 𝔞` either has `depth(M_𝔭) ≥ 1` or has
`depth(M_𝔭) + dim((A/𝔭)_𝔮) > d + 1` for every `𝔮 ∈ V(𝔭) ∩ V(𝔞) ∩ V(I)`.

This is the disjunction of the source's sentence: off the associated primes the depth of the
localization is positive, and at an associated prime it is zero, so the inequality to be proved
is exactly the hypothesis. -/
theorem depthOrDimensionBound_of_closureLocalDimension [IsNoetherianRing A]
    (I a : Ideal A) (d : ℤ)
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hbound : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A M →
      ¬ I ≤ p.asIdeal →
      (∃ y : PrimeSpectrum A, p.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
      ∀ z : PrimeSpectrum A, p.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
        ((d + 1 : ℤ) : EInt) < krullDimToEInt (closureLocalDimension A p z))
    (p : PrimeSpectrum A)
    (hpI : p ∉ PrimeSpectrum.zeroLocus (I : Set A))
    (hpT : p ∉ associatedSubset I a) :
    ((enatToEInt
        (Module.depth (Localization.AtPrime p.asIdeal)
          (maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M)) ≥ ((1 : ℤ) : EInt)) ∨
      (∀ q : PrimeSpectrum A,
        q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
          PrimeSpectrum.zeroLocus (a : Set A)) ∩
          PrimeSpectrum.zeroLocus (I : Set A) →
        enatToEInt
            (Module.depth (Localization.AtPrime p.asIdeal)
              (maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl M)) +
            krullDimToEInt
              (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
                p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) >
          ((d + 1 : ℤ) : EInt))) := by
  by_cases hass : p.asIdeal ∈ associatedPrimes A M
  · -- At an associated prime the depth of the localization is zero, and the inequality to be
    -- proved is condition (2) of Stacks 0EIF.
    refine Or.inr fun q hq => ?_
    have hdepth : Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) = 0 :=
      (Module.depth_localized_eq_zero_iff (M := M) p).2 hass
    have hpz : p.asIdeal ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hq.1.1
    have haz : a ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hq.1.2
    have hpInot : ¬ I ≤ p.asIdeal := fun h =>
      hpI ((PrimeSpectrum.mem_zeroLocus _ _).2 h)
    have hkey := hbound p hass hpInot
      (exists_mem_zeroLocus_notMem_zeroLocus_of_notMem_associatedSubset I a p hpT) q hpz haz
    rw [closureLocalDimension_eq_ringKrullDim_localizedQuotient] at hkey
    rw [hdepth, enatToEInt_zero, zero_add]
    exact hkey
  · -- Off the associated primes the depth of the localization is at least one.
    refine Or.inl ?_
    have hne : Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) ≠ 0 := fun h =>
      hass ((Module.depth_localized_eq_zero_iff (M := M) p).1 h)
    have hone : (1 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) := Order.one_le_iff_ne_zero.2 hne
    exact le_of_eq_of_le enatToEInt_one.symm (enatToEInt_mono hone)

end Stacks.Algebraization

end
