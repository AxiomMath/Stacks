module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support

/-!
# Flatness at associated primes and the total quotient ring

For a map of Noetherian rings `A → B` the following conditions compare preservation of
nonzerodivisors with flatness after inverting them. Writing `Q(A)` for the total quotient ring of
`A`, the conditions are: (1) nonzerodivisors of `A` stay nonzerodivisors in `B`; (2) condition (1)
together with flatness of `B ⊗[A] Q(A)` over `Q(A)`; (3) `A → B_q` is flat at every associated
prime `q` of `B`; and (4) condition (3) together with flatness at every prime of `B` lying over an
associated prime of `A`. One has (2) implies (1), (2) implies (4), (4) implies (3) and (3) implies
(1), and (2) and (4) are equivalent when `A → B` satisfies going up.

This generalizes the different: condition (1) is the standing hypothesis under which the
complementary module and the Dedekind different are defined.

## Main definitions

* `Stacks.Discriminant.MapsNonZeroDivisors` says that the ring map preserves nonzerodivisors.
* `Stacks.Discriminant.FractionBaseChangeFlat` is flatness after base change to the total
  quotient ring of the source.
* `Stacks.Discriminant.FlatAtAssociatedPrimes` is flatness over the source at every associated
  prime of the target.
* `Stacks.Discriminant.FlatAtPrimesOverAssociatedPrimes` combines the preceding local condition
  with flatness at every prime over an associated prime of the source.

## Main results

* `Stacks.Discriminant.mapsNonZeroDivisors_of_fractionBaseChangeFlat`,
  `Stacks.Discriminant.flatAtAssociatedPrimes_of_flatAtPrimesOverAssociatedPrimes`,
  `Stacks.Discriminant.flatAtPrimesOverAssociatedPrimes_of_fractionBaseChangeFlat` and
  `Stacks.Discriminant.mapsNonZeroDivisors_of_flatAtAssociatedPrimes` are the four implications.
* `Stacks.Discriminant.fractionBaseChangeFlat_iff_flatAtPrimesOverAssociatedPrimes` is the
  equivalence under going up.

## Implementation notes

The four conditions are named predicates so that each arrow in the source's diagram can be
stated independently. The total quotient ring `Q(A)` is `FractionRing A` and `B_q` is
`Localization.AtPrime q`. The localization of `B` at the image of the nonzerodivisors of `A` is
the common intermediate ring through which the comparisons factor; flatness is transported along
it by the two-step transitivity of flatness.

## References

* [Stacks Project, Tag 0BWL](https://stacks.math.columbia.edu/tag/0BWL)
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Stacks.Discriminant

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/-- Condition (1): nonzerodivisors of `A` map to nonzerodivisors of `B`. -/
def MapsNonZeroDivisors : Prop :=
  Submonoid.map (algebraMap A B) (nonZeroDivisors A) ≤ nonZeroDivisors B

/-- Condition (2), apart from condition (1): the base change of `B` to the
total quotient ring of `A` is flat over that total quotient ring. -/
def FractionBaseChangeFlat : Prop :=
  MapsNonZeroDivisors A B ∧ Module.Flat (FractionRing A) (FractionRing A ⊗[A] B)

/-- Condition (3): `A → B_q` is flat for every associated prime `q` of `B`. -/
def FlatAtAssociatedPrimes : Prop :=
  ∀ q : PrimeSpectrum B, q.asIdeal ∈ associatedPrimes B B →
    Module.Flat A (Localization.AtPrime q.asIdeal)

/-- Condition (4): condition (3) holds, and `A → B_q` is flat for every
prime `q` of `B` lying over an associated prime of `A`. -/
def FlatAtPrimesOverAssociatedPrimes : Prop :=
  FlatAtAssociatedPrimes A B ∧
    ∀ q : PrimeSpectrum B,
      q.asIdeal.comap (algebraMap A B) ∈ associatedPrimes A A →
        Module.Flat A (Localization.AtPrime q.asIdeal)

/-- If `D` is a localization of `B` at `M` that is flat over `A`, then so is every localization
of `B` at a larger submonoid `N`. -/
private theorem flat_of_submonoid_le {A B D L : Type*} [CommRing A] [CommRing B] [CommRing D]
    [CommRing L] [Algebra A B] [Algebra A D] [Algebra B D] [IsScalarTower A B D] [Algebra A L]
    [Algebra B L] [IsScalarTower A B L] {M N : Submonoid B} (hMN : M ≤ N) [IsLocalization M D]
    [IsLocalization N L] [Module.Flat A D] : Module.Flat A L := by
  let _ : Algebra D L := IsLocalization.localizationAlgebraOfSubmonoidLe D L M N hMN
  let _ : IsScalarTower B D L :=
    IsLocalization.localization_isScalarTower_of_submonoid_le D L M N hMN
  let _ : IsScalarTower A D L :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap A L x = algebraMap D L (algebraMap A D x)
      rw [IsScalarTower.algebraMap_apply A B D x, ← IsScalarTower.algebraMap_apply B D L,
        ← IsScalarTower.algebraMap_apply A B L x])
  have _ : IsLocalization (N.map (algebraMap B D)) L :=
    IsLocalization.isLocalization_of_submonoid_le D L M N hMN
  have : Module.Flat D L := IsLocalization.flat L (N.map (algebraMap B D))
  exact Module.Flat.trans A D L

/-- If `FractionRing A ⊗[A] B` is flat over `FractionRing A` and no nonzerodivisor of `A` maps
into the prime `q` of `B`, then `Localization.AtPrime q` is flat over `A`. -/
theorem flatAtPrime_of_fractionBaseChangeFlat
    (hflat : Module.Flat (FractionRing A) (FractionRing A ⊗[A] B))
    (q : PrimeSpectrum B)
    (hq : ∀ s : A, s ∈ nonZeroDivisors A → algebraMap A B s ∉ q.asIdeal) :
    Module.Flat A (Localization.AtPrime q.asIdeal) := by
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
  let D := Localization M
  let e := Localization.tensorRightAlgEquiv (nonZeroDivisors A) B
  have hD : Module.Flat (FractionRing A) D :=
    (Module.Flat.equiv_iff e.toLinearEquiv).mp hflat
  let _ : IsScalarTower A (FractionRing A) D :=
    isScalarTower_localizationAlgebra (nonZeroDivisors A) B
  have : Module.Flat A D := Module.Flat.trans A (FractionRing A) D
  refine flat_of_submonoid_le (M := M) (D := D) (N := q.asIdeal.primeCompl) ?_
  rintro y ⟨s, hs, rfl⟩
  exact hq s hs

private theorem regular_not_mem_associatedPrimes {R : Type*} [CommRing R]
    {f : R} (hf : f ∈ nonZeroDivisors R) {p : Ideal R}
    (hp : p ∈ associatedPrimes R R) : f ∉ p := by
  rcases AssociatedPrimes.mem_iff.mp hp with ⟨hprime, x, hx⟩
  have hx0 : x ≠ 0 := by
    intro hxzero
    subst x
    exact hprime.ne_top (by rw [hx]; simp)
  intro hfp
  have hrad : f ∈ ((⊥ : Submodule R R).colon {x}).radical := by rwa [← hx]
  obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff).mp hrad
  have hmul : f ^ n * x = 0 := by
    simpa [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] using hn
  exact hx0 ((mem_nonZeroDivisors_iff_left.mp ((nonZeroDivisors R).pow_mem hf n)) x hmul)

/-- Condition (2) implies condition (1). -/
@[stacks 0BWL "(2) implies (1)"]
theorem mapsNonZeroDivisors_of_fractionBaseChangeFlat
    (h : FractionBaseChangeFlat A B) : MapsNonZeroDivisors A B := h.1

/-- Condition (4) implies condition (3). -/
@[stacks 0BWL "(4) implies (3)"]
theorem flatAtAssociatedPrimes_of_flatAtPrimesOverAssociatedPrimes
    (h : FlatAtPrimesOverAssociatedPrimes A B) : FlatAtAssociatedPrimes A B := h.1

/-- Condition (2) implies condition (4). -/
@[stacks 0BWL "(2) implies (4)"]
theorem flatAtPrimesOverAssociatedPrimes_of_fractionBaseChangeFlat
    (h : FractionBaseChangeFlat A B) : FlatAtPrimesOverAssociatedPrimes A B := by
  rcases h with ⟨hnd, hflat⟩
  refine ⟨fun q hq => ?_, fun q hp => ?_⟩
  · exact flatAtPrime_of_fractionBaseChangeFlat A B hflat q fun s hs =>
      regular_not_mem_associatedPrimes (hnd (Submonoid.mem_map.mpr ⟨s, hs, rfl⟩)) hq
  · exact flatAtPrime_of_fractionBaseChangeFlat A B hflat q fun s hs hsq =>
      regular_not_mem_associatedPrimes hs hp (by simpa using hsq)

/-- Condition (3) implies condition (1) for Noetherian rings. -/
@[stacks 0BWL "(3) implies (1)"]
theorem mapsNonZeroDivisors_of_flatAtAssociatedPrimes
    [IsNoetherianRing A] [IsNoetherianRing B]
    (h : FlatAtAssociatedPrimes A B) : MapsNonZeroDivisors A B := by
  intro y hy
  rcases Submonoid.mem_map.mp hy with ⟨f, hf, rfl⟩
  show algebraMap A B f ∈ nonZeroDivisors B
  by_contra hnot
  have hbad : ¬ ∀ b : B, algebraMap A B f * b = 0 → b = 0 := by
    simpa only [mem_nonZeroDivisors_iff_left] using hnot
  push Not at hbad
  obtain ⟨b, hfb, hb0⟩ := hbad
  have hzdiv : algebraMap A B f ∈ {r : B | ∃ x : B, x ≠ 0 ∧ r • x = 0} :=
    ⟨b, hb0, by simpa [smul_eq_mul] using hfb⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors B B] at hzdiv
  rcases Set.mem_iUnion₂.mp hzdiv with ⟨p, hp, hfp⟩
  let q : PrimeSpectrum B := ⟨p, hp.1⟩
  let _ : q.asIdeal.IsPrime := q.isPrime
  have hq : q.asIdeal ∈ associatedPrimes B B := hp
  have hfq : algebraMap A B f ∈ q.asIdeal := hfp
  have hflat : Module.Flat A (Localization.AtPrime q.asIdeal) := h q hq
  have hreg : IsSMulRegular (Localization.AtPrime q.asIdeal) f :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Localization.AtPrime q.asIdeal) hf
  have hq' : IsAssociatedPrime q.asIdeal B := AssociatedPrimes.mem_iff.mp hq
  rw [isAssociatedPrime_iff] at hq'
  obtain ⟨_, ⟨x, hx⟩⟩ := hq'
  have hx0 : algebraMap B (Localization.AtPrime q.asIdeal) x ≠ 0 := by
    intro hxzero
    obtain ⟨s, hsx⟩ := (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) x).mp hxzero
    have hsQ : (s : B) ∈ q.asIdeal := by
      have hmem : (s : B) ∈ (⊥ : Submodule B B).colon {x} := by
        simpa [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul, mul_comm] using hsx
      exact (congrArg (fun I : Ideal B => (s : B) ∈ I) hx).mpr hmem
    exact s.2 hsQ
  have hfx : algebraMap A (Localization.AtPrime q.asIdeal) f •
      algebraMap B (Localization.AtPrime q.asIdeal) x = 0 := by
    have hmem : algebraMap A B f ∈ (⊥ : Submodule B B).colon {x} :=
      (congrArg (fun I : Ideal B => algebraMap A B f ∈ I) hx).mp hfq
    have hmul : algebraMap A B f * x = 0 := by
      simpa [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
        smul_eq_mul, mul_comm] using hmem
    simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply A B
      (Localization.AtPrime q.asIdeal)] using
      congrArg (algebraMap B (Localization.AtPrime q.asIdeal)) hmul
  exact hx0 (hreg (by simpa [Algebra.smul_def] using hfx))

/-- If `A → B` satisfies going up, conditions (2) and (4) are equivalent. -/
@[stacks 0BWL "equivalence under going up"]
theorem fractionBaseChangeFlat_iff_flatAtPrimesOverAssociatedPrimes
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra.HasGoingUp A B] :
    FractionBaseChangeFlat A B ↔ FlatAtPrimesOverAssociatedPrimes A B := by
  constructor
  · exact flatAtPrimesOverAssociatedPrimes_of_fractionBaseChangeFlat A B
  · intro h
    refine ⟨mapsNonZeroDivisors_of_flatAtAssociatedPrimes A B h.1, ?_⟩
    let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
    let D := Localization M
    let e := Localization.tensorRightAlgEquiv (nonZeroDivisors A) B
    have hADflat : Module.Flat A D := by
      apply Module.flat_of_isLocalized_maximal D D
        (fun P => Localization.AtPrime P)
        (fun P => Algebra.linearMap D (Localization.AtPrime P))
      intro P hP
      let _ : P.IsPrime := hP.isPrime
      let qD : PrimeSpectrum D := ⟨P, hP.isPrime⟩
      let qB : PrimeSpectrum B := PrimeSpectrum.comap (algebraMap B D) qD
      have hdisjM : Disjoint (M : Set B) (qB.asIdeal : Set B) :=
        Set.disjoint_left.mpr fun x hxM hxq => qD.isPrime.ne_top
          (qD.asIdeal.eq_top_of_isUnit_mem hxq (IsLocalization.map_units D ⟨x, hxM⟩))
      let p := qB.asIdeal.comap (algebraMap A B)
      have hpdisj : Disjoint (p : Set A) (nonZeroDivisors A : Set A) :=
        Set.disjoint_left.mpr fun s hsp hs =>
          Set.disjoint_left.mp hdisjM (Submonoid.mem_map.mpr ⟨s, hs, rfl⟩) hsp
      have hpUnion : (p : Set A) ⊆ ⋃ r ∈ associatedPrimes A A, (r : Set A) := by
        rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors A]
        exact hpdisj.subset_compl_right
      obtain ⟨p', hp', hpp'⟩ :=
        (Ideal.subset_union_prime_finite (associatedPrimes.finite A A) (⊥ : Ideal A)
          (⊥ : Ideal A) (fun r hr _ _ => (AssociatedPrimes.mem_iff.mp hr).1)
          (I := p)).mp hpUnion
      let _ : qB.asIdeal.IsPrime := qB.isPrime
      have _ : qB.asIdeal.LiesOver p :=
        ⟨(Ideal.under_def A qB.asIdeal).symm⟩
      let _ : p'.IsPrime := (AssociatedPrimes.mem_iff.mp hp').1
      obtain ⟨q', hqBq', hq'prime, hq'lies⟩ :=
        Ideal.exists_ideal_ge_liesOver_of_le (p := p) (q := p') qB.asIdeal hpp'
      have hq'comap : q'.comap (algebraMap A B) = p' := by
        simpa only [Ideal.under_def] using (q'.over_def p').symm
      have hq'assoc : q'.comap (algebraMap A B) ∈ associatedPrimes A A := by
        rwa [hq'comap]
      have hflatq' : Module.Flat A (Localization.AtPrime q') := h.2 ⟨q', hq'prime⟩ hq'assoc
      have hflatqB : Module.Flat A (Localization.AtPrime qB.asIdeal) :=
        flat_of_submonoid_le (A := A) (D := Localization.AtPrime q') (M := q'.primeCompl)
          (N := qB.asIdeal.primeCompl)
          fun _ hx hxq => hx (hqBq' hxq)
      let eP := IsLocalization.localizationLocalizationAtPrimeIsoLocalization M P
      exact (Module.Flat.equiv_iff (eP.toLinearEquiv.restrictScalars A)).mp hflatqB
    let _ : IsScalarTower A (FractionRing A) D :=
      isScalarTower_localizationAlgebra (nonZeroDivisors A) B
    have hflatFrac : Module.Flat (FractionRing A) D :=
      (Module.flat_iff_of_isLocalization (FractionRing A) (nonZeroDivisors A) D).mpr hADflat
    exact (Module.Flat.equiv_iff e.toLinearEquiv).mpr hflatFrac

end Stacks.Discriminant
