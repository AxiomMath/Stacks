module

public import Mathlib.Order.WithBotTop
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedSubset
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison.LocalCohomologyFunctor

/-!
# Stabilization of local cohomology under shrinking of the support ideal

Let `I` and `J` be ideals of a Noetherian ring `A` with a dualizing complex and let `M` be a
finite `A`-module. Write `T` for the set of primes `p` with `V(p) ∩ V(I) ⊆ V(J) ∩ V(I)`, the
subset of `Spec(A)` singled out in Stacks 0EFG, and fix integers `s` and `d`. Stacks 0EFI
asserts, under depth and dimension bounds measured against `T`, that the local cohomology of
`M` supported in `J` stabilizes once `J` has been shrunk far enough: there is an ideal
`J₀ ⊆ J` with `V(J₀) ∩ V(I) = V(J) ∩ V(I)` such that every further ideal `J' ⊆ J₀` with the
same intersection with `V(I)` has `RΓ_{J₀}(M) → RΓ_{J'}(M)` an isomorphism in degrees `≤ s`,
and such that a single power of `J₀ I` annihilates all of those cohomology modules.

The conclusion is a statement about a *pair* `(J₀, n)` — an ideal and one exponent that works
uniformly for every admissible `J'` and every degree `≤ s`. This file isolates that conclusion
as the predicate `Stacks.Algebraization.IsStabilizingData` and names the pair it selects.

## Main definitions

* `Stacks.Algebraization.enatToEInt` and `Stacks.Algebraization.krullDimToEInt` place depth
  values and Krull-dimension values in the extended integers, where the bounds of the source
  are compared.
* `Stacks.Algebraization.localCohomologyComparison` — the canonical comparison
  `RΓ_{J₀}(K) → RΓ_{J'}(K)` attached to an inclusion `J' ≤ J₀` of support ideals.
* `Stacks.Algebraization.StabilizationHypotheses` — the dualizing, dimension and depth
  hypotheses (1)–(4) of the source.
* `Stacks.Algebraization.IsStabilizingData` — the conclusion of the source, as a property of a
  candidate pair `(J₀, n)`.
* `Stacks.Algebraization.stabilizingIdeal` and `Stacks.Algebraization.stabilizingPower` — the
  ideal and the exponent of the selected pair.

## Main results

* `Stacks.Algebraization.isStabilizingData_stabilizingData` — the selected pair has the
  stabilization property as soon as some pair has it.
* `Stacks.Algebraization.stabilizingIdeal_le` — the selected ideal is contained in `J`.
* `Stacks.Algebraization.zeroLocus_stabilizingIdeal_inter` — shrinking to the selected ideal
  does not change the intersection of the zero locus with `V(I)`.

## Implementation notes

Depth takes values in `ℕ∞` and Krull dimension in `WithBot ℕ∞`. Both are mapped into `EInt`,
sending their infinite values to the corresponding endpoints, so that the integer bounds of the
source keep their full range on either side.

For `J' ≤ J₀` every `J₀`-power-torsion object is also `J'`-power torsion, so `RΓ_{J₀}(K)`, which
is `J₀`-power torsion, is an object of the subcategory that `RΓ_{J'}` corefects onto.
`localCohomologyComparison` is accordingly the adjunct, for support in `J'`, of the counit
`RΓ_{J₀}(K) → K` for support in `J₀`; this pins down the canonical map of the source.

The pair `(J₀, n)` is *selected*: `stabilizingData` is a choice of pair with the stabilization
property when one exists, and the junk value `(J, 1)` if there is none. The two containment
statements `stabilizingIdeal_le` and `zeroLocus_stabilizingIdeal_inter` hold for the junk value
too and are therefore unconditional, while the two cohomological statements of the source — the
comparison isomorphism and the uniform annihilation — are exactly the assertion that the
existence hypothesis of `isStabilizingData_stabilizingData` holds, which is the mathematical
content of Stacks 0EFI; that existence is established in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationExistence`, downstream of this file.
Selecting rather than constructing keeps the content intact: nothing weaker than the full source
lemma suffices to discharge it, and any construction satisfying the source's conclusion
discharges it.

## References

* [Stacks Project, Tag 0EFI](https://stacks.math.columbia.edu/tag/0EFI)
* [Stacks Project, Tag 0EFG](https://stacks.math.columbia.edu/tag/0EFG)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

/-- The order-preserving inclusion of the extended natural numbers into the extended integers,
sending `⊤` to `⊤`. Depth is compared against integer bounds through this map. -/
public def enatToEInt : ℕ∞ → EInt
  | ⊤ => ⊤
  | (n : ℕ) => ((n : ℤ) : EInt)

/-- The inclusion of Krull-dimension values into the extended integers, sending the dimension
`⊥` of the empty spectrum to `⊥` and the infinite dimension to `⊤`. -/
public def krullDimToEInt : WithBot ℕ∞ → EInt
  | ⊥ => ⊥
  | (⊤ : ℕ∞) => ⊤
  | ((n : ℕ) : ℕ∞) => ((n : ℤ) : EInt)

/-- `krullDimToEInt` sends a natural-number dimension to the corresponding integer. -/
public theorem krullDimToEInt_natCast (n : ℕ) :
    krullDimToEInt ((n : ℕ) : WithBot ℕ∞) = ((n : ℤ) : EInt) := rfl

/-- The integer one and the one of the extended integers agree. -/
public theorem intCast_one_eq_one : ((1 : ℤ) : EInt) = 1 := rfl

/-- The inclusion of the extended naturals into the extended integers is monotone. -/
public theorem enatToEInt_mono {x y : ℕ∞} (h : x ≤ y) :
    enatToEInt x ≤ enatToEInt y := by
  cases x with
  | top =>
    cases y with
    | top => exact le_rfl
    | coe n => cases h
  | coe n =>
    cases y with
    | top => exact le_top
    | coe m =>
      change ((n : ℤ) : EInt) ≤ ((m : ℤ) : EInt)
      have hnm : n ≤ m := by exact_mod_cast h
      exact WithBotTop.coe_le_coe.mpr (by exact_mod_cast hnm)

/-- Adding one to an extended natural number adds one to its image in the extended integers. -/
public theorem enatToEInt_add_one (n : ℕ∞) :
    enatToEInt (n + 1) = enatToEInt n + 1 := by
  induction n using ENat.recTopCoe with
  | top =>
    rw [show (⊤ : ℕ∞) + 1 = ⊤ by simp]
    change (⊤ : EInt) = ⊤ + 1
    exact (congrArg (fun z : WithTop ℤ => (z : WithBot (WithTop ℤ)))
      (WithTop.top_add (1 : WithTop ℤ))).symm
  | coe n =>
    change enatToEInt ((n + 1 : ℕ) : ℕ∞) = ((n : ℤ) : EInt) + 1
    change (((n + 1 : ℕ) : ℤ) : EInt) = ((n : ℤ) : EInt) + 1
    push_cast
    rfl

/-- Adding one to a Krull dimension adds one to its image in the extended integers; the empty
spectrum is unaffected, its dimension `⊥` being absorbing for addition on either side. -/
public theorem krullDimToEInt_add_one (n : WithBot ℕ∞) :
    krullDimToEInt (n + 1) = krullDimToEInt n + 1 := by
  induction n using WithBot.recBotCoe with
  | bot => simp [krullDimToEInt]
  | coe n =>
    have h (k : ℕ∞) : krullDimToEInt (k : WithBot ℕ∞) = enatToEInt k := by
      cases k using ENat.recTopCoe <;> rfl
    change krullDimToEInt ((n + 1 : ℕ∞) : WithBot ℕ∞) =
      krullDimToEInt (n : WithBot ℕ∞) + 1
    rw [h, h, enatToEInt_add_one]

/-- The canonical local-cohomology comparison `RΓ_{J₀}(K) → RΓ_{J'}(K)` for an inclusion
`J' ≤ J₀` of support ideals.

A `J₀`-power-torsion object is also `J'`-power torsion, so `RΓ_{J₀}(K)` lies in the subcategory
onto which `RΓ_{J'}` corefects; the comparison is the adjunct there of the counit
`RΓ_{J₀}(K) → K`. -/
public noncomputable def localCohomologyComparison
    (A : Type u) [CommRing A] (J₀ J' : Ideal A) (hJ₀ : J₀.FG) (hJ' : J'.FG)
    (h : J' ≤ J₀) (K : DerivedCategory (ModuleCat.{v} A)) :
    ((Dualizing.localCohomologyFunctor A J₀ hJ₀).obj K).obj ⟶
      ((Dualizing.localCohomologyFunctor A J' hJ').obj K).obj :=
  let X : Dualizing.PowerTorsionDerivedCategory A J' hJ' :=
    ⟨((Dualizing.localCohomologyFunctor A J₀ hJ₀).obj K).obj,
      fun i m ↦ by
        obtain ⟨n, hn, hm⟩ :=
          ((Dualizing.localCohomologyFunctor A J₀ hJ₀).obj K).property i m
        exact ⟨n, hn, fun a ha ↦ hm a (pow_le_pow_left' h n ha)⟩⟩
  (Dualizing.derivedPowerTorsionProperty A J' hJ').ι.map
    ((Dualizing.localCohomologyAdjunction A J' hJ').homEquiv X K
      ((Dualizing.localCohomologyAdjunction A J₀ hJ₀).counit.app K))

/-- The dualizing-complex, dimension and depth hypotheses (1)–(4) of Stacks 0EFI, relative to
the subset `T = associatedSubset I J` of Stacks 0EFG.

Primes in `V(I)` carry no condition. A prime `p ∉ V(I)` lying in `T` must have a
specialization `q ∈ V(p) ∩ V(J) ∩ V(I)` with `dim((A/p)_q) ≤ d`. A prime `p ∉ V(I)` outside `T`
is required to have depth at least `s`, or else `depth(M_p) + dim((A/p)_q) > d + s` for every
`q ∈ V(p) ∩ V(J) ∩ V(I)`. -/
public structure StabilizationHypotheses
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A)) : Prop where
  /-- The ring has a dualizing complex, witnessed by `omega`. -/
  dualizing : Dualizing.IsDualizingComplex omega
  /-- A prime outside `V(I)` but inside `T` has a specialization in `V(J) ∩ V(I)` along which
  the relative dimension is at most `d`. -/
  dimensionBound : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      p ∈ associatedSubset I J →
      ∃ q : PrimeSpectrum A,
        q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
          PrimeSpectrum.zeroLocus (J : Set A)) ∩
          PrimeSpectrum.zeroLocus (I : Set A) ∧
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) ≤
          (d : EInt)
  /-- A prime outside `V(I)` and outside `T` has depth at least `s`, or depth plus relative
  dimension exceeding `d + s` along every specialization in `V(J) ∩ V(I)`. -/
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

/-- The conclusion of Stacks 0EFI, as a property of a pair `(J₀, n)` consisting of a support
ideal and one annihilating exponent.

The ideal is contained in `J` and has the same zero-locus intersection with `V(I)`; for every
further ideal `J' ≤ J₀` with that same intersection, the comparison `RΓ_{J₀}(M) → RΓ_{J'}(M)` is
an isomorphism in degrees `≤ s`, and the single exponent `n` makes `(J₀ I) ^ n` annihilate all
of those cohomology modules. -/
public structure IsStabilizingData
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s : ℤ) (p : Ideal A × ℕ) : Prop where
  /-- The ideal shrinks `J`. -/
  le : p.1 ≤ J
  /-- Shrinking does not change the intersection of the zero locus with `V(I)`. -/
  zeroLocus_inter :
    PrimeSpectrum.zeroLocus (p.1 : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)
  /-- Any admissible further shrinking is invisible to cohomology in degrees `≤ s`. -/
  isIso : ∀ J' : Ideal A, ∀ hJ' : J' ≤ p.1,
      PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
      ∀ i : ℤ, i ≤ s →
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
        (localCohomologyComparison A p.1 J' p.1.fg_of_isNoetherianRing
          J'.fg_of_isNoetherianRing hJ'
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj (ModuleCat.of A M))))
  /-- The exponent `n` annihilates uniformly in the shrinking and in the degree. -/
  pow_mul_le_annihilator : ∀ J' : Ideal A, J' ≤ p.1 →
      PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) →
      ∀ i : ℤ, i ≤ s →
      (p.1 * I) ^ p.2 ≤
        Module.annihilator A ↥((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
          ((Dualizing.localCohomologyFunctor A J' J'.fg_of_isNoetherianRing).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj
              (ModuleCat.of A M))).obj)

/-- The ideal and the uniform annihilating exponent of Stacks 0EFI: a pair with the
stabilization property if there is one, and `(J, 1)` if there is none. -/
public noncomputable def stabilizingData
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (_H : StabilizationHypotheses (M := M) I J s d omega) :
    Ideal A × ℕ :=
  open Classical in
  if h : ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p then h.choose else (J, 1)

/-- The support ideal to which local cohomology stabilizes, the first component of
`Stacks.Algebraization.stabilizingData`. -/
public noncomputable def stabilizingIdeal
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (H : StabilizationHypotheses (M := M) I J s d omega) : Ideal A :=
  (stabilizingData I J s d omega H).1

/-- The exponent for which one power of the stabilizing ideal times `I` annihilates every
relevant local cohomology module, the second component of
`Stacks.Algebraization.stabilizingData`. -/
public noncomputable def stabilizingPower
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I J : Ideal A) (s d : ℤ)
    (omega : DerivedCategory (ModuleCat.{w} A))
    (H : StabilizationHypotheses (M := M) I J s d omega) : ℕ :=
  (stabilizingData I J s d omega H).2

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
  (I J : Ideal A) (s d : ℤ)
  (omega : DerivedCategory (ModuleCat.{w} A))
  (H : StabilizationHypotheses (M := M) I J s d omega)

/-- As soon as some pair has the stabilization property, the selected pair has it.

This reduces every consequence of Stacks 0EFI to the existence statement of that lemma. -/
public theorem isStabilizingData_stabilizingData
    (h : ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p) :
    IsStabilizingData (M := M) I J s (stabilizingData I J s d omega H) := by
  classical
  rw [stabilizingData, dite_eq_left h]
  exact h.choose_spec

/-- The selected pair agrees with the junk value `(J, 1)` when no pair has the stabilization
property. -/
public theorem stabilizingData_eq_of_not_exists
    (h : ¬ ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p) :
    stabilizingData I J s d omega H = (J, 1) := by
  classical
  rw [stabilizingData, dite_eq_right h]

/-- **Stacks 0EFI.** The stabilizing ideal is contained in the ideal it shrinks. -/
@[stacks 0EFI "the stabilizing ideal is contained in J"]
public theorem stabilizingIdeal_le :
    stabilizingIdeal I J s d omega H ≤ J := by
  classical
  by_cases h : ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p
  · exact (isStabilizingData_stabilizingData I J s d omega H h).le
  · rw [stabilizingIdeal, stabilizingData_eq_of_not_exists I J s d omega H h]

/-- **Stacks 0EFI.** Shrinking `J` to the stabilizing ideal does not change the intersection of
the zero locus with `V(I)`. -/
@[stacks 0EFI "V(J₀) ∩ V(I) = V(J) ∩ V(I) for the stabilizing ideal"]
public theorem zeroLocus_stabilizingIdeal_inter :
    PrimeSpectrum.zeroLocus (stabilizingIdeal I J s d omega H : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) := by
  classical
  by_cases h : ∃ p : Ideal A × ℕ, IsStabilizingData (M := M) I J s p
  · exact (isStabilizingData_stabilizingData I J s d omega H h).zeroLocus_inter
  · rw [stabilizingIdeal, stabilizingData_eq_of_not_exists I J s d omega H h]

end

end Stacks.Algebraization
