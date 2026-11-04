module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.ResidueBaseChange
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.OrbitPolynomial
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.OrbitExtension
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.PoleReduction
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.WeakSolutionCriteria
import all StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.ResidueBaseChange

/-!
# Eliminating degree-prime ramification: Epp's degree-`p` endgame in characteristic `p`

The constant-numerator endgame and the totally ramified Galois weak solutions in equal
characteristic `p`, from finite support, from a perfect-core bound, and in general.

## References

* [Stacks Project, Tag 09F0](https://stacks.math.columbia.edu/tag/09F0)
-/

@[expose] public section

open Polynomial
open nonZeroDivisors
open WithZero

open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] Ideal.Quotient.field

universe uA uB uC uK uL uM uK₁

namespace IsDiscreteValuationRing

/-- A nonzero element of a domain stays nonzero in an extension of its fraction field. -/
private theorem algebraMap_ne_zero_of_fractionRing_tower {A K L : Type*} [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [IsFractionRing A K] {π : A} (hπ : π ≠ 0) : algebraMap A L π ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply A K L]
  exact (_root_.map_ne_zero _).mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hπ)

/-- The `n`-th power of the maximal ideal of a DVR lies in the span of the `n`-th power of any
uniformizer. -/
private theorem maximalIdeal_pow_le_span_pow {B : Type*} [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] {x : B} (hx : Irreducible x) (n : ℕ) :
    (IsLocalRing.maximalIdeal B) ^ n ≤ Ideal.span {x ^ n} := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hx, Ideal.span_singleton_pow]

/-- The residue field of a local ring of characteristic `p` has characteristic `p`. -/
private theorem charP_residueField (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) (hp : p.Prime)
    [CharP R p] : CharP (IsLocalRing.ResidueField R) p :=
  (CharP.charP_iff_prime_eq_zero (R := IsLocalRing.ResidueField R) hp).mpr
    (by rw [← map_natCast (IsLocalRing.residue R), CharP.cast_eq_zero R p, map_zero])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The constant-numerator endgame from coefficient congruences.**

This is the transport-stable core of the constant Laurent argument.  The coefficients of the
polar part are supplied as actual elements `coeffLift i : B`, together with elements
`baseLift i : A` whose images agree with them modulo the `n`-th power of the maximal ideal.
Those congruences, rather than a section of the whole residue field of `B`, are precisely what the
proof uses to replace the Laurent numerator by one defined over the base.

The distinction matters after a normal residue base change.  In a conjugate factor the transported
original coefficient lifts are still available and residue absorption supplies the congruent
base-origin lifts, but there need not be a ring section of the factor's *entire* residue field
extending the original section.  Requiring such a section made the reusable endpoint strictly
stronger than its proof and blocked the all-conjugate Epp assembly. -/
theorem exists_isGalois_totallyRamified_isWeakSolution_of_constant_laurent_of_coefficients_lift
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (hweak : IsWeaklyUnramified A B)
    (π : A) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n)
    (ξ : L) (z : M) (hz : z ^ p - z = algebraMap L M ξ)
    (hgen : Algebra.adjoin L {z} = ⊤)
    (coeffLift : ℕ → B) (b : B)
    (hexp : ξ = (∑ i ∈ Finset.range n,
      algebraMap B L (coeffLift i) *
        (algebraMap B L (algebraMap A B π))⁻¹ ^ (n - i)) + algebraMap B L b)
    (hmin : ∀ (m : ℕ) (η : L) (w : M),
      w ^ p - w = algebraMap L M η → Algebra.adjoin L {w} = ⊤ →
      algebraMap A L π ^ m * η ∈ (algebraMap B L).range → n ≤ m)
    (baseLift : ℕ → A)
    (hlift : ∀ i ∈ Finset.range n,
      coeffLift i - algebraMap A B (baseLift i) ∈ (IsLocalRing.maximalIdeal B) ^ n)
    (root0 : IsLocalRing.ResidueField A)
    (hroot0 : IsLocalRing.residue A (baseLift 0) = root0 ^ (p ^ n)) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : IsGalois K K₁),
      IsTotallyRamifiedWithRespectTo A K K₁ ∧
        ∃ D : IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
            max uM uK, uK, max uM uK} A C K M K₁,
          D.IsWeakSolution := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hπB : Irreducible (algebraMap A B π) :=
    irreducible_algebraMap_of_isWeaklyUnramified hweak hπ
  have ht : algebraMap A L π ≠ 0 :=
    algebraMap_ne_zero_of_fractionRing_tower (K := K) hπ.ne_zero
  have htB : algebraMap B L (algebraMap A B π) ≠ 0 := by
    simpa only [← IsScalarTower.algebraMap_apply] using ht
  have hI := maximalIdeal_pow_le_span_pow hπB n
  have hexp' := pow_mul_laurent_expansion (algebraMap A B π) htB n coeffLift b ξ hexp
  obtain ⟨b', hξ⟩ := eq_constant_numerator_of_coefficients_lift π ht n
    coeffLift b ξ baseLift
      (by simpa only [← IsScalarTower.algebraMap_apply] using hexp')
      fun i hi => hI (hlift i hi)
  set a : A := ∑ i ∈ Finset.range n, baseLift i * π ^ i with ha_def
  have hπA : π ∈ IsLocalRing.maximalIdeal A :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸
      Ideal.mem_span_singleton_self π
  have hres : IsLocalRing.residue A a = root0 ^ (p ^ n) := by
    rw [ha_def, residue_sum_mul_uniformizer_pow hπA n hn baseLift, hroot0]
  have hpn : ¬p ∣ n :=
    not_dvd_poleOrder_of_constant_numerator_of_root p π hπ ht n hn a b' ξ z
      (root0 ^ (p ^ (n - 1)))
      (by rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hn, hres]) hz hgen hξ hmin
  have ha := isUnit_of_minimal_poleOrder π hπ ht n hn a b' ξ z p hz hgen hξ hmin
  obtain ⟨K₁, _, _, _, _, _, _, htot, w, hw, hwgen⟩ :=
    exists_isGalois_totallyRamified_artinSchreier A K p hp π hπ n hn hpn a ha
  refine ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, htot, ?_⟩
  have hBC : ramificationIndex B C = p :=
    ramificationIndex_eq_prime_of_artinSchreier_pole B C L M p hp ξ z hz hgen
      (algebraMap A B π) hπB n hn hpn (algebraMap A B a) b' (ha.map _)
      (by simpa only [← IsScalarTower.algebraMap_apply] using hξ)
  have hAC : ramificationIndex A C = p := by
    rw [ramificationIndex_tower A B C,
      show ramificationIndex A B = 1 from hweak, hBC, one_mul]
  let : IsScalarTower A L M := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L M, ← IsScalarTower.algebraMap_apply A K M]
  apply isWeakSolution_of_constant_artinSchreier_parameter A C K M K₁ p hp
    π hπ n hn hpn a ha (algebraMap B C b') z w _ hw hwgen htot hAC
  simpa only [hξ, map_add, map_mul, map_pow, map_inv₀,
    ← IsScalarTower.algebraMap_apply] using hz

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The constant-numerator endgame for a supplied Laurent presentation.**

If all coefficients of a positive minimal Artin--Schreier Laurent presentation admit compatible
`p ^ n`-th roots in the base residue field, then a totally ramified Artin--Schreier extension of
the base field is a weak solution.  This is the reusable core of the constant branch below: the
presentation and its roots are arguments, so after a finite normal residue base change the same
argument can be applied independently in every conjugate factor. -/
theorem exists_isGalois_totallyRamified_isWeakSolution_of_constant_laurent
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (hweak : IsWeaklyUnramified A B)
    (π : A) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n)
    (ξ : L) (z : M) (hz : z ^ p - z = algebraMap L M ξ)
    (hgen : Algebra.adjoin L {z} = ⊤)
    (σ : IsLocalRing.ResidueField B → B)
    (hσ : ∀ x, IsLocalRing.residue B (σ x) = x)
    (s : IsLocalRing.ResidueField B →+* B ⧸ (IsLocalRing.maximalIdeal B) ^ n)
    (hs : ∀ x, Ideal.Quotient.mk ((IsLocalRing.maximalIdeal B) ^ n) (σ x) = s x)
    (coeff : ℕ → IsLocalRing.ResidueField B) (b : B)
    (hexp : ξ = (∑ i ∈ Finset.range n,
      algebraMap B L (σ (coeff i)) *
        (algebraMap B L (algebraMap A B π))⁻¹ ^ (n - i)) + algebraMap B L b)
    (hmin : ∀ (m : ℕ) (η : L) (w : M),
      w ^ p - w = algebraMap L M η → Algebra.adjoin L {w} = ⊤ →
      algebraMap A L π ^ m * η ∈ (algebraMap B L).range → n ≤ m)
    (root : ℕ → IsLocalRing.ResidueField A)
    (hroot : ∀ i ∈ Finset.range n,
      algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) (root i) ^
        (p ^ n) = coeff i) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : IsGalois K K₁),
      IsTotallyRamifiedWithRespectTo A K K₁ ∧
        ∃ D : IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
            max uM uK, uK, max uM uK} A C K M K₁,
          D.IsWeakSolution := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : CharP A p := (algebraMap A K).charP (IsFractionRing.injective A K) p
  have : CharP B p := (algebraMap B L).charP (IsFractionRing.injective B L) p
  have hlift : ∀ i : ℕ, ∃ l : A, i ∈ Finset.range n →
      σ (coeff i) - algebraMap A B l ∈ (IsLocalRing.maximalIdeal B) ^ n := by
    intro i
    by_cases hi : i ∈ Finset.range n
    · obtain ⟨l, hl⟩ := exists_sub_algebraMap_mem_pow_of_pow_eq p n σ hσ s hs
        (root i ^ (p ^ n)) (root i) rfl
      exact ⟨l, fun _ => by simpa only [map_pow, hroot i hi] using hl⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose lift hlift using hlift
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
  have hres0 : IsLocalRing.residue A (lift 0) = root 0 ^ (p ^ n) := by
    apply (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).injective
    have hmem : σ (coeff 0) - algebraMap A B (lift 0) ∈ IsLocalRing.maximalIdeal B :=
      Ideal.pow_le_self hn.ne' (hlift 0 h0)
    have heq : IsLocalRing.residue B (algebraMap A B (lift 0)) =
        IsLocalRing.residue B (σ (coeff 0)) := by
      rw [eq_comm, ← sub_eq_zero, ← map_sub]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [IsLocalRing.ResidueField.algebraMap_residue, heq, hσ, map_pow, hroot 0 h0]
  exact exists_isGalois_totallyRamified_isWeakSolution_of_constant_laurent_of_coefficients_lift
    A B C K L M p hp hweak π hπ n hn ξ z hz hgen (fun i => σ (coeff i)) b hexp hmin
      lift (fun i hi => hlift i hi) (root 0) hres0

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The original finite-support assembly below has the same large instance graph as the extracted
-- constant-numerator endgame and likewise needs a larger synthesis budget when rebuilt from
-- source.
set_option synthInstance.maxHeartbeats 200000 in
-- (the larger synthesis budget is explained in the comment just above)
/-- **Epp's complete degree-`p` case in equal characteristic, on the residue hypothesis it
actually uses.**

In equal characteristic `p`, a weakly unramified extension `A ⊆ B` followed by a degree-`p` Galois
extension of fraction fields admits a finite Galois base extension which is totally ramified over
`A` and is a weak solution for `A → C` — with **no residue hypothesis at all** in the binders.
Everything the residue fields are asked for is returned as an antecedent, over an explicitly
produced finite set `S : Finset κ_B` and a single explicitly produced depth `N`:

> for each `x ∈ S` that lies in `perfectCore κ_B p`, some `a : κ_A` has
> `(algebraMap κ_A κ_B a) ^ (p ^ N) = x`.

This one statement replaces both hypotheses the earlier formulation carried.  Where that version
demanded `hperf` (Frobenius onto all of `κ_A`) *and* `hcore` (`perfectCore κ_B p` inside the image
of `κ_A`), the antecedent above asks, at finitely many elements only, for a base element whose
`p ^ N`-th power is the coefficient — which is exactly the composite the proof consumed: it never
used `x` being in the image except to then take a deep root of the preimage inside `κ_A`.  Asking
for the root and the preimage in one breath drops the universal perfectness claim entirely.

**Why the classification is intrinsic.**  The proof splits the Laurent coefficients by membership
in the subfield `perfectCore κ_B p` of `StacksFrontier.FieldTheory.PerfectCore` — and *not* by lying
in the image of `κ_A`.  That is what makes the antecedent returnable rather than demanded:
perfect-core membership is a property of `κ_B` alone, so the split, the terminal depth of each
non-core coefficient (the public `exists_pow_eq_and_not_pow_of_notMem_perfectCore`, which needs no
hypothesis), and hence `S` and `N` are all determined before any base field is interrogated.
Under the old image-based split none of this was available until `hcore` had already been assumed.

The antecedent spells perfect-core membership out as `∀ n ≥ 1, ∃ y, y ^ (p ^ n) = x` rather than
writing `x ∈ perfectCore κ_B p`, so that the statement carries no `ExpChar` instance on a residue
field; inside the proof the two are interchanged by `mem_perfectCore_iff`, the `ExpChar κ_B p`
instance being found there from `CharP κ_B p` and `Fact p.Prime`.

`S` is the set of Laurent coefficients of the Artin--Schreier parameter the proof builds; `N` and
`S` are branch-specific.  When every coefficient is in the perfect core, `N = n` is the pole
order, and the coefficient lifts are the `p ^ n`-th powers supplied by the antecedent, from which
an explicit `p`-th root of the constant numerator's residue is extracted for
`not_dvd_poleOrder_of_constant_numerator_of_root` — replacing the `PerfectRing κ_A p` instance
that call used to need.  When some coefficient is outside the perfect core, `N` is the common
depth dominating every terminal depth, at which the core coefficients are read.

Everything is phrased in elementary `∃`/`∀` form rather than via `PerfectRing κ_A p` and
`perfectCore κ_B p ≤ (algebraMap κ_A κ_B).fieldRange` so that the statement mentions no `ExpChar`
instance on a residue field; those instances are derivable from `hp` and `[CharP K p]` but are not
in scope where the theorem is applied.

The point for Tag 09F9 is that a finite weakly unramified base change does not in general
establish anything about the whole perfect core, which may be infinite over `κ_A`, but it can
establish it at finitely many coefficients and one depth — and that finite set with its depth is
the data a synchronized construction across conjugate factors has to agree on.  The reverse
inclusion `image ⊆ perfectCore` is in any case **not** stable when the ring upstairs is replaced
by a finite extension — `κ_A = 𝔽_p ⊂ 𝔽_{p²} = κ_B` refutes it, as recorded in
`StacksFrontier.RingTheory.DiscreteValuationRing.EppConditionAscent`.

`exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_perfectCore_le` recovers the universal
`hperf`/`hcore` form by discharging the antecedent, and
`exists_isGalois_totallyRamified_isWeakSolution_of_charP` is Tag 09F1 as stated.

**The uniformizer is an input.**  `π` is supplied rather than chosen, because the returned `S` and
`N` depend on the base ring `A` *only* through the element `algebraMap A B π`: the Artin–Schreier
presentation comes from `exists_artinSchreier_presentation_minimal_poleOrder B L M p hπB`, the
lifting datum `σ`, `s` from `exists_residueField_lift_mod_pow (B := B)`, and the Laurent expansion
and its separation from `exists_laurent_expansion` and
`exists_artinSchreier_laurent_presentation_without_related_poles` — every one of which sees the
uniformizer only as an element of `B`.  So for a finite weakly unramified `A ⊆ A₁ ⊆ B` the two
invocations with `π` and with `algebraMap A A₁ π` run on literally the same data, since
`algebraMap A₁ B (algebraMap A A₁ π) = algebraMap A B π`, and they therefore return the same `S`
and the same `N`.

That is what a consumer discharging the antecedent from Epp's condition needs, and it is why
choosing `π` internally was the obstruction: under `Stacks.EppTheorem.EppCondition A B p` a `p ^
  N`-th
root of a perfect-core coefficient is separable algebraic over `κ_A` but is *not* in the image of
`κ_A`, so the antecedent is not dischargeable over `A` itself — one must pass to a finite étale
`A₁` that absorbs the finitely many roots
(`Stacks.EppTheorem.EppCondition.exists_finiteEtale_forall_exists_pow_eq_algebraMap`) and re-enter
  the
layer over `A₁` with the same `S` and `N`.  Note that exploiting the agreement still needs `S` and
`N` exposed rather than existentially bound; this theorem supplies the invariance, not yet the
exposure. -/
theorem exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_finiteSupport_of_uniformizer
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C]
    [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    [FiniteDimensional L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p)
    (hweak : IsWeaklyUnramified A B)
    (π : A) (hπ : Irreducible π) :
    ∃ (S : Finset (IsLocalRing.ResidueField B)) (N : ℕ),
      (∀ x ∈ S,
        (∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x) →
          ∃ a : IsLocalRing.ResidueField A,
            algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a ^ (p ^ N)
              = x) →
      ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
        (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : IsGalois K K₁),
        IsTotallyRamifiedWithRespectTo A K K₁ ∧
          ∃ D : IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
              max uM uK, uK, max uM uK} A C K M K₁,
            D.IsWeakSolution := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hπB := irreducible_algebraMap_of_isWeaklyUnramified hweak hπ
  obtain ⟨n, ξ, z, hz, hgen, hn, hmin⟩ :=
    exists_artinSchreier_presentation_minimal_poleOrder B L M p hπB
      (exists_artinSchreier_presentation_of_charP K L M p hp hdegree)
  by_cases hn0 : n = 0
  · refine ⟨∅, 0, fun _ => ?_⟩
    simp only [hn0, pow_zero, one_mul] at hn
    obtain ⟨b, hb⟩ := hn
    exact exists_weakSolution_of_isWeaklyUnramified A C K M
      (isWeaklyUnramified_trans A B C hweak
        (isWeaklyUnramified_of_artinSchreier_integral B C L M p hp hdegree
          ξ z hz hgen ⟨b, hb.symm⟩))
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have : CharP A p := (algebraMap A K).charP (IsFractionRing.injective A K) p
    have : CharP B p := (algebraMap B L).charP (IsFractionRing.injective B L) p
    have := charP_residueField B p hp
    simp only [← IsScalarTower.algebraMap_apply] at hn hmin
    obtain ⟨σ, hσ, s, hs⟩ := exists_residueField_lift_mod_pow (B := B) p n hnpos
    have htB : algebraMap B L (algebraMap A B π) ≠ 0 := by
      simpa only [← IsScalarTower.algebraMap_apply] using
        algebraMap_ne_zero_of_fractionRing_tower (K := K) (L := L) hπ.ne_zero
    obtain ⟨coeff, b, hexp⟩ := exists_laurent_expansion hπB σ hσ n ξ
      (by simpa only [← IsScalarTower.algebraMap_apply] using hn)
    -- The coefficients are classified by membership in `perfectCore κ_B p`, an intrinsic
    -- property of `κ_B`.  Nothing here mentions `κ_A`, which is what lets the finite set and the
    -- depth be *produced* below rather than demanded in the binders.  The `ExpChar κ_B p`
    -- instance `perfectCore` needs is found from the `CharP κ_B p` above together with
    -- `Fact p.Prime`, so no such instance appears in the statement.
    let P : IsLocalRing.ResidueField B → Prop := fun x =>
      x ∈ perfectCore (IsLocalRing.ResidueField B) p
    have hP : P 0 :=
      mem_perfectCore_iff.mpr fun m => ⟨0, zero_pow (pow_pos hp.pos m).ne'⟩
    have hI := maximalIdeal_pow_le_span_pow hπB n
    obtain ⟨ξ, z, coeff, b, hz, hgen, hexp, hseparated⟩ :=
      exists_artinSchreier_laurent_presentation_without_related_poles p (algebraMap A B π) htB n
        ((IsLocalRing.maximalIdeal B)^n) hI σ s hs P hP ξ z coeff b hz hgen hexp
    by_cases hconst : ∀ i ∈ Finset.range n, P (coeff i)
    · -- Every coefficient is in the perfect core.  The depth interrogated is the pole order `n`
      -- itself: it is what the coefficient lifts need, and being positive it leaves a `p`-th root
      -- of the constant numerator's residue over.
      refine ⟨(Finset.range n).image coeff, n, fun hcore => ?_⟩
      -- The antecedent hands back, for each coefficient, an element of `κ_A` whose `p ^ n`-th
      -- power *is* that coefficient -- exactly the datum
      -- `exists_sub_algebraMap_mem_pow_of_pow_eq` consumes, and the reason no perfectness of
      -- `κ_A` is needed: the deep root comes with the preimage instead of being taken afterwards.
      have hroot : ∀ i : ℕ, ∃ r : IsLocalRing.ResidueField A, i ∈ Finset.range n →
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) r ^ (p ^ n)
            = coeff i := by
        intro i
        by_cases hi : i ∈ Finset.range n
        · obtain ⟨r, hr⟩ :=
            hcore (coeff i) (Finset.mem_image_of_mem coeff hi)
              fun m _ => mem_perfectCore_iff.mp (hconst i hi) m
          exact ⟨r, fun _ => hr⟩
        · exact ⟨0, fun h => (hi h).elim⟩
      choose root hroot using hroot
      exact exists_isGalois_totallyRamified_isWeakSolution_of_constant_laurent A B C K L M p hp
        hweak π hπ n hnpos ξ z hz hgen σ hσ s hs coeff b hexp hmin root
        fun i hi => hroot i hi
    · -- Some coefficient lies outside the perfect core.  `J` collects those, and because
      -- perfect-core membership is intrinsic to `κ_B`, both `J` and the terminal depth of each of
      -- its members are available with no residue hypothesis in hand -- which is precisely what
      -- lets the depth `R` below, computed from those depths, be the one returned.
      let J := (Finset.range n).filter fun i => ¬P (coeff i)
      have hJ : J.Nonempty := by
        by_contra hJ
        apply hconst
        intro i hi
        by_contra hci
        exact hJ ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
      have hdepth : ∀ i : ℕ, ∃ (r : ℕ) (μ : IsLocalRing.ResidueField B),
          i ∈ J → μ ^ (p ^ r) = coeff i ∧ ¬∃ ν : IsLocalRing.ResidueField B, ν ^ p = μ := by
        intro i
        by_cases hi : i ∈ J
        · obtain ⟨r, μ, hμ, hν⟩ :=
            exists_pow_eq_and_not_pow_of_notMem_perfectCore p (Finset.mem_filter.mp hi).2
          exact ⟨r, μ, fun _ => ⟨hμ, hν⟩⟩
        · exact ⟨0, 0, fun h => (hi h).elim⟩
      choose depth μ hdepth using hdepth
      have hJn : ∀ j ∈ J, j < n := fun j hj => Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hsep : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → ∀ r : ℕ,
          n - j' ≠ (n - j) * p ^ r := by
        intro j hj j' hj' hne r
        exact hseparated j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
          j' (Finset.mem_filter.mp hj').1 (Finset.mem_filter.mp hj').2 hne r
      obtain ⟨R, j, hj, hlargeDepth, hlargePole, hmaxPole, hdivPole⟩ :=
        exists_unique_max_scaled_pole p n hp J hJ hJn depth hsep
      -- `R` strictly dominates every terminal depth (`hlargeDepth`), and it is the single depth
      -- at which the perfect-core coefficients are read.  It has to be exactly `R`: the scaled
      -- pole of a core coefficient is `(n - i) * p ^ (R - R) = n - i ≤ n`, which `hlargePole`
      -- puts strictly below the maximal pole, and any shallower reading would inflate it.
      refine ⟨(Finset.range n).image coeff, R, fun hcore => ?_⟩
      obtain ⟨K₁, _, _, _, _, _, _, htot, hdegree₁, V, _, α, hcardV, hα, hV, hprod⟩ :=
        exists_isGalois_totallyRamified_orbitExtension A K p hp π hπ (n + 1) R (by omega)
      refine ⟨K₁, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, htot, ?_⟩
      let L₁ := L ⊗[K] K₁
      let A₁ := integralClosure A K₁
      let B₁ := integralClosure B L₁
      obtain ⟨hLF, hA₁, hB₁, hfrac, f, hfinj, hfmax, hfsquare⟩ :=
        exists_integralClosure_baseChange_dvr A B K L K₁ hweak htot
      let : Field L₁ := hLF.toField
      let : IsDiscreteValuationRing A₁ := hA₁
      let : IsDiscreteValuationRing B₁ := hB₁
      let : IsFractionRing B₁ L₁ := hfrac
      let : IsFractionRing A₁ K₁ := integralClosure.isFractionRing_of_finite_extension K K₁
      let : Algebra.IsSeparable L L₁ := isSeparable_tensorProduct_of_isField K L K₁ hLF
      let : IsExtension B B₁ :=
        isExtension_integralClosure_of_isDiscreteValuationRing B L L₁
      let : Module.IsTorsionFree B B₁ := Module.isTorsionFree_iff_algebraMap_injective.mpr
        (FaithfulSMul.algebraMap_injective B B₁)
      let : (IsLocalRing.maximalIdeal B₁).LiesOver (IsLocalRing.maximalIdeal B) :=
        ⟨(IsLocalRing.maximalIdeal_comap (algebraMap B B₁)).symm⟩
      have htotB : IsTotallyRamifiedWithRespectTo B L L₁ :=
        isTotallyRamified_tensorProduct_of_weaklyUnramified A B K L K₁ hweak htot hLF f hfinj hfmax
      have heB : ramificationIndex B B₁ = p ^ R := by
        rw [ramificationIndex_eq_ramificationIdx B B₁,
          ramificationIdx_eq_ramificationIdx'_maximalIdeal,
          ramificationIdx_eq_finrank_of_totallyRamified B L L₁ htotB _
            inferInstance inferInstance, Module.finrank_baseChange, hdegree₁]
      have hresSurj := residueField_map_surjective_of_totallyRamified B L L₁ htotB
      let αA : A₁ := ⟨α, hα⟩
      let αB : B₁ := f αA
      have hprodA : (∏ v : V, (αA - algebraMap A A₁ v)) = algebraMap A A₁ π := by
        apply IsFractionRing.injective A₁ K₁
        simp only [map_prod, map_sub, ← IsScalarTower.algebraMap_apply]
        exact hprod
      have hprodB : (∏ v : V, (αB - algebraMap A B₁ v)) = algebraMap A B₁ π := by
        have hfc (x : A) : f (algebraMap A A₁ x) = algebraMap A B₁ x := f.commutes x
        simpa only [map_prod, map_sub, hfc] using congrArg f hprodA
      have happrox : αB ^ (p ^ R) - algebraMap B B₁ (algebraMap A B π) ∈
          Ideal.span {algebraMap B B₁ (algebraMap A B π) ^ (n + 1)} := by
        simpa only [hcardV, ← IsScalarTower.algebraMap_apply] using
          pow_card_sub_mem_span_pow_of_prod_eq V π (n + 1) hV αB hprodB
      obtain ⟨hαB, u, hroot, hu⟩ := irreducible_of_pow_sub_mem_span_pow
        (algebraMap A B π) hπB αB (p ^ R) n (pow_pos hp.pos R) hnpos heB happrox
      let d : ℕ → ℕ := fun i => if i ∈ J then depth i else R
      have hν : ∀ i : ℕ, ∃ ν : IsLocalRing.ResidueField B,
          (i ∈ Finset.range n → ν ^ (p ^ d i) = coeff i) ∧
          (i ∈ J → ¬∃ y : IsLocalRing.ResidueField B, ν = y ^ p) := by
        intro i
        by_cases hiJ : i ∈ J
        · refine ⟨μ i, ?_, ?_⟩
          · intro _
            simpa only [d, ite_eq_left hiJ] using (hdepth i hiJ).1
          · intro _ ⟨y, hy⟩
            exact (hdepth i hiJ).2 ⟨y, hy.symm⟩
        · by_cases hin : i ∈ Finset.range n
          · have hci : P (coeff i) := by
              by_contra hci
              exact hiJ (Finset.mem_filter.mpr ⟨hin, hci⟩)
            -- This coefficient is in the perfect core, so the antecedent supplies a base element
            -- whose `p ^ R`-th power is it -- the root and the preimage in one step, with no
            -- perfectness of `κ_A` invoked to take the root afterwards.
            obtain ⟨x, hx⟩ :=
              hcore (coeff i) (Finset.mem_image_of_mem coeff hin)
                fun m _ => mem_perfectCore_iff.mp hci m
            refine ⟨algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) x, ?_,
              fun h => (hiJ h).elim⟩
            intro _
            simpa only [d, ite_eq_right hiJ] using hx
          · exact ⟨0, fun h => (hin h).elim, fun h => (hiJ h).elim⟩
      choose ν hν using hν
      have hd : ∀ i ∈ Finset.range n, d i ≤ R := by
        intro i hi
        by_cases hiJ : i ∈ J
        · have := hlargeDepth i hiJ
          simp only [d, ite_eq_left hiJ]
          omega
        · simp only [d, ite_eq_right hiJ, le_refl]
      have hc : ∀ i ∈ Finset.range n,
          σ (coeff i) - σ (ν i) ^ (p ^ d i) ∈ Ideal.span {algebraMap A B π ^ n} := by
        intro i hi
        apply hI
        apply Ideal.Quotient.eq.mp
        rw [hs, map_pow, hs, ← s.map_pow, (hν i).1 hi]
      let : CharP L₁ p := charP_of_injective_algebraMap (algebraMap K L₁).injective p
      obtain ⟨t, η, b₁, hη, hηexp⟩ := exists_baseChanged_laurent_reduction (F := L₁) p
        (algebraMap A B π) htB αB u R n hroot hu (fun i => σ (coeff i))
        (fun i => σ (ν i)) d hd hc b ξ hexp
      let e : ℕ → ℕ := fun i => (n - i) * p ^ (R - d i)
      have hem : 0 < e j := by
        have h := hlargePole j hj
        simpa only [e, d, ite_eq_left hj] using (Nat.zero_le n).trans_lt h
      have hediv : p ∣ e j := by simpa only [e, d, ite_eq_left hj] using hdivPole
      have hemax : ∀ i ∈ Finset.range n, i ≠ j → e i < e j := by
        intro i hi hne
        by_cases hiJ : i ∈ J
        · simpa only [e, d, ite_eq_left hiJ, ite_eq_left hj] using hmaxPole i hiJ hne
        · have h := hlargePole j hj
          simp only [e, d, ite_eq_right hiJ, ite_eq_left hj, Nat.sub_self, pow_zero, mul_one]
          exact (Nat.sub_le n i).trans_lt h
      obtain ⟨a₁, hηpole, hres⟩ := exists_laurent_numerator_residue_of_unique_max αB hαB
        (Finset.range n) (fun i => algebraMap B B₁ (σ (ν i))) e j
        (Finset.mem_filter.mp hj).1 hem hemax b₁ η
        (by simpa only [e, ← IsScalarTower.algebraMap_apply] using hηexp)
      have ha₁ : ¬∃ y : IsLocalRing.ResidueField B₁, IsLocalRing.residue B₁ a₁ = y ^ p := by
        rw [hres, ← IsLocalRing.ResidueField.map_residue, hσ]
        exact not_exists_pow_of_surjective_field_hom _ hresSurj p (ν j) ((hν j).2 hj)
      apply exists_isWeakSolution_of_baseChanged_artinSchreier_residue A B C K L M K₁
        hLF f hfinj hfmax hfsquare p hp ξ z hz hgen η t hη αB hαB (e j) hem hediv a₁ ha₁
      have htα : algebraMap B₁ L₁ αB ≠ 0 := by
        simpa only [map_zero] using (IsFractionRing.injective B₁ L₁).ne hαB.ne_zero
      change algebraMap B₁ L₁ αB ^ (e j) * η = algebraMap B₁ L₁ a₁
      rw [hηpole, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ htα, one_pow, one_mul]

/-- **Epp's complete degree-`p` case in equal characteristic, on the residue hypothesis it
actually uses.**

`exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_finiteSupport_of_uniformizer` with the
uniformizer chosen internally.  See that theorem's docstring for what `S` and `N` are, why the
antecedent is returnable rather than demanded, and why a consumer discharging it from Epp's
condition wants the uniformizer supplied instead. -/
theorem exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_finiteSupport
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C]
    [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    [FiniteDimensional L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p)
    (hweak : IsWeaklyUnramified A B) :
    ∃ (S : Finset (IsLocalRing.ResidueField B)) (N : ℕ),
      (∀ x ∈ S,
        (∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x) →
          ∃ a : IsLocalRing.ResidueField A,
            algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a ^ (p ^ N)
              = x) →
      ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
        (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : IsGalois K K₁),
        IsTotallyRamifiedWithRespectTo A K K₁ ∧
          ∃ D : IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
              max uM uK, uK, max uM uK} A C K M K₁,
            D.IsWeakSolution := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  exact exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_finiteSupport_of_uniformizer
    A B C K L M p hp hdegree hweak π hπ

/-- **Epp's complete degree-`p` case in equal characteristic, with `hcore` demanded of every
element of `κ_B`.**

The universal form of `exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_finiteSupport`,
obtained by discharging that theorem's antecedent from `hcore` alone.

**No perfectness of `κ_A` is needed.**  A hypothesis
`hperf : ∀ a : κ_A, ∃ b, b ^ p = a`, used iterated `N` times to extract a `p ^ N`-th root
of the preimage *inside* `κ_A`, is avoidable, because the order of the two steps can be
reversed: the coefficient `x` lies in `perfectCore κ_B p`, and the perfect core is a perfect field
in its own right, so a `p ^ N`-th root of `x` may be taken **inside the core**
(`exists_mem_perfectCore_pow_eq`) and only then pulled back along `hcore` — which applies to it
precisely because the root is again in the core.  So the deep root is extracted in `κ_B`, where it
is free, instead of in `κ_A`, where it would cost a universal hypothesis.

This matters beyond economy.  Because `hcore` now discharges the antecedent for *every* `S` and
`N`, a consumer who has arranged `perfectCore κ_B p ⊆ image κ_{A₁}` for some finite weakly
unramified `A₁` can re-enter the finite-support layer over `A₁` without having to know which `S`
and `N` that run returns — which is what makes the finite-étale re-entry available while `S` and
`N` are still existentially bound. -/
theorem exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_perfectCore_le
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C]
    [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    [FiniteDimensional L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p)
    (hweak : IsWeaklyUnramified A B)
    (hcore : ∀ x : IsLocalRing.ResidueField B,
      (∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x) →
        ∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : IsGalois K K₁),
      IsTotallyRamifiedWithRespectTo A K K₁ ∧
        ∃ D : IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
            max uM uK, uK, max uM uK} A C K M K₁,
          D.IsWeakSolution := by
  obtain ⟨S, N, hS⟩ :=
    exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_finiteSupport
      A B C K L M p hp hdegree hweak
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : CharP B p := (algebraMap B L).charP (IsFractionRing.injective B L) p
  have := charP_residueField B p hp
  have : ExpChar (IsLocalRing.ResidueField B) p := ExpChar.prime hp
  refine hS fun x _ hx => ?_
  -- Take the `p ^ N`-th root inside the perfect core, where it is free, and pull *it* back.
  obtain ⟨y, hycore, hy⟩ :=
    exists_mem_perfectCore_pow_eq (mem_perfectCore_iff_forall_one_le.mpr hx) N
  obtain ⟨a, ha⟩ := hcore y (mem_perfectCore_iff_forall_one_le.mp hycore)
  exact ⟨a, by rw [ha, hy]⟩

/-- In equal characteristic `p`, a weakly unramified extension `A ⊆ B` followed
by a degree-`p` Galois extension of fraction fields admits a finite Galois base
extension which is totally ramified over `A` and is a weak solution for `A → C`,
provided the image of the residue field of `A` in that of `B` is the intersection
of all sets of `p ^ n`-th powers for `n ≥ 1`.

This is Tag 09F1 as stated.  The two consequences of `hresidue` that the proof consumes are
isolated in `exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_perfectCore_le`, which is
strictly more general: it drops the inclusion `image ⊆ perfectCore` entirely, keeping only
perfectness of `κ_A` and `perfectCore κ_B p ⊆ image`. -/
@[stacks 09F1]
theorem exists_isGalois_totallyRamified_isWeakSolution_of_charP
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra B L] [Algebra C M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [Algebra A L] [Algebra B M] [Algebra A M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower B C M] [IsScalarTower B L M]
    [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsExtension A B] [IsExtension B C]
    [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    [FiniteDimensional L M] [IsGalois L M]
    (hdegree : Module.finrank L M = p)
    (hweak : IsWeaklyUnramified A B)
    (hresidue : ∀ x : IsLocalRing.ResidueField B,
      (∃ a : IsLocalRing.ResidueField A,
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) a = x) ↔
        ∀ n : ℕ, 1 ≤ n → ∃ y : IsLocalRing.ResidueField B, y ^ (p ^ n) = x) :
    ∃ (K₁ : Type uK) (_ : Field K₁) (_ : Algebra K K₁) (_ : Algebra A K₁)
      (_ : IsScalarTower A K K₁) (_ : Module.Finite K K₁) (_ : IsGalois K K₁),
      IsTotallyRamifiedWithRespectTo A K K₁ ∧
        ∃ D : IntegralClosureBaseChange.{uA, uC, uK, uM, uK,
            max uM uK, uK, max uM uK} A C K M K₁,
          D.IsWeakSolution := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : CharP A p := (algebraMap A K).charP (IsFractionRing.injective A K) p
  have : CharP B p := (algebraMap B L).charP (IsFractionRing.injective B L) p
  have := charP_residueField A p hp
  have := charP_residueField B p hp
  exact exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_perfectCore_le
    A B C K L M p hp hdegree hweak
    (fun x hx => (hresidue x).mpr hx)

end IsDiscreteValuationRing
