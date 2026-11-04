module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.FieldExtension
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange

@[expose] public section

/-!
# Depth, dimension and associated primes along a flat local homomorphism

The commutative algebra behind the fibrewise study of a flat local homomorphism
`R → S` of Noetherian local rings: how depth is transported along a surjection, how the
Cohen–Macaulay property turns a dimension into a depth, how the dimension of a fibre over a
one-dimensional base stays at most one, and how an associated prime of an `R`-module `M` which is
not the maximal ideal is seen by an associated prime of `S ⊗_R M` which is not the maximal ideal
either.

## Main results

* `Stacks.Depth.ringKrullDim_quotient_eq_depth_of_cohenMacaulay`: if `B ⧸ I` is isomorphic to a
  Cohen–Macaulay local ring, its Krull dimension is its depth as a `B`-module.
* `Stacks.Depth.ringKrullDim_quotient_map_le_one_of_closedFibre_dimension_zero`: for a local
  homomorphism with zero-dimensional closed fibre, a prime `p` of `R` with
  `dim (R ⧸ p) ≤ 1` has `dim (S ⧸ p S) ≤ 1`.
* `Stacks.Depth.exists_isAssociatedPrimeStacks_over_of_flat`: an associated prime of `M`
  strictly below `𝔪_R` is dominated by an associated prime of `S ⊗_R M` strictly below `𝔪_S`.
* `Stacks.Depth.covBy_maximalIdeal_of_ringKrullDim_quotient_le_one`: in a local ring with
  `dim (S ⧸ I) ≤ 1`, a prime `q ⊇ I` strictly below `𝔪_S` has no prime strictly between it
  and `𝔪_S`.
* `Stacks.Depth.isAssociatedPrimeStacks_iff_mem_associatedPrimes`: over a Noetherian ring the
  source's notion of an associated prime (Stacks 00LA) is Mathlib's `associatedPrimes`.

## Implementation notes

Depth is `Module.depth` (Stacks 00LI), the value in `ℕ∞` which is `⊤` exactly when the ideal
saturates the module. Both branches of that definition have to be transported in
`Stacks.CohenMacaulay.BaseFieldExtension.depth_eq_depth_map`: the surjection `f` makes
`rs ↦ rs.map f` a
length-preserving bijection from the `M`-regular sequences inside `I` onto the `N`-regular
sequences inside `I.map f` — surjectivity is what lifts a sequence on the `B`-side back to the
`A`-side, which is `Stacks.CohenMacaulay.BaseFieldExtension.exists_list_map_eq` — and `I • M = M`
holds exactly when `(I.map f) • N = N`.

The Cohen–Macaulay predicate used here is `IsCohenMacaulayLocalRing`, which is by definition an
equality of `Module.depthSup` with the Krull dimension of the support; so the proof of
`ringKrullDim_quotient_eq_depth_of_cohenMacaulay` first replaces `Module.depth` by
`Module.depthSup` (legitimate because the maximal ideal does not saturate a nonzero ring) and then
rewrites the support dimension of `A` over itself as `ringKrullDim A`.

The dimension bound for a fibre is the inequality `ht P ≤ ht p + ht (P / p S)` of Stacks 00OM
(`Ideal.height_le_height_add_of_liesOver`) applied to the local homomorphism
`R ⧸ p → S ⧸ p S` induced by `algebraMap R S`, whose closed fibre is a further quotient of the
closed fibre of `R → S` by `DoubleQuot.quotQuotEquivQuotOfLE`. Heights of maximal ideals are
turned into Krull dimensions by `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`.

For the associated prime, flatness of `S` gives going down
(`Algebra.HasGoingDown.of_flat`), which produces a prime of `S` strictly below `𝔪_S` lying over
`𝔪_R`; a minimal prime of `p S` below it lies over `p`, is associated to `S ⧸ p S`, and hence by
Stacks 0312 (`associatedPrimes.tensorProduct_of_flat`) is associated to `S ⊗_R M`.

## References

* [Stacks, Tag 0338](https://stacks.math.columbia.edu/tag/0338)
* [Stacks, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
-/

namespace Stacks.Depth

open IsLocalRing RingTheory.Sequence
open scoped TensorProduct

/-- **The dimension of a Cohen–Macaulay quotient is its depth.** If `I` is an ideal of a local
ring `B` with `B ⧸ I` isomorphic to a Noetherian Cohen–Macaulay local ring `A`, then the Krull
dimension of `B ⧸ I` is the depth of `B ⧸ I` as a `B`-module along the maximal ideal of `B`. -/
theorem ringKrullDim_quotient_eq_depth_of_cohenMacaulay {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A]
    (I : Ideal B) (e : B ⧸ I ≃+* A) (hcm : IsCohenMacaulayLocalRing A) :
    ringKrullDim (B ⧸ I) = (Module.depth B (maximalIdeal B) (B ⧸ I) : WithBot ℕ∞) := by
  have : Nontrivial (B ⧸ I) := e.toEquiv.nontrivial
  have : IsLocalRing (B ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have he : Module.depth B (maximalIdeal B) (B ⧸ I) = Module.depth A (maximalIdeal A) A := by
    rw [Stacks.CohenMacaulay.BaseFieldExtension.depth_eq_depth_map (f := Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective (maximalIdeal B) (AddEquiv.refl (B ⧸ I)) (fun b x => rfl),
      map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
    exact Module.depth_self_eq_of_ringEquiv e
  rw [he, ringKrullDim_eq_of_ringEquiv e]
  show ringKrullDim A = _
  have hdepth : Module.depth A (maximalIdeal A) A = Module.depthSup A (maximalIdeal A) A := by
    rw [Module.depth, if_neg]
    · exact (Module.depthSup_eq_iSup _ _).symm
    · simpa using (maximalIdeal.isMaximal A).ne_top
  rw [hdepth]
  show _ = (Module.depthSup A (maximalIdeal A) A : WithBot ℕ∞)
  change (Module.depthSup A (maximalIdeal A) A : WithBot ℕ∞) = Module.supportDim A A at hcm
  simpa only [Module.supportDim_self_eq_ringKrullDim] using hcm.symm

/-- **A one-dimensional base and a zero-dimensional closed fibre give a one-dimensional fibre.**
Let `R → S` be a local homomorphism of Noetherian local rings whose closed fibre
`S ⧸ 𝔪_R S` has dimension `0`, and let `p` be a prime of `R` with `dim (R ⧸ p) ≤ 1`. Then
`dim (S ⧸ p S) ≤ 1`. -/
theorem ringKrullDim_quotient_map_le_one_of_closedFibre_dimension_zero
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] (p : Ideal R) [p.IsPrime]
    (hpdim : ringKrullDim (R ⧸ p) ≤ 1)
    (hfib : ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0) :
    ringKrullDim (S ⧸ p.map (algebraMap R S)) ≤ 1 := by
  let I := p.map (algebraMap R S)
  let J := (maximalIdeal R).map (algebraMap R S)
  have hp : p ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)
  have hIJ : I ≤ J := Ideal.map_mono hp
  have hJ : J ≤ maximalIdeal S := map_maximalIdeal_le (algebraMap R S)
  have : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top (hIJ.trans hJ))
  have : IsLocalRing (R ⧸ p) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalRing (S ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk I) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  let φ : R ⧸ p →+* S ⧸ I := Ideal.quotientMap I (algebraMap R S) Ideal.le_comap_map
  let : Algebra (R ⧸ p) (S ⧸ I) := φ.toAlgebra
  have : IsLocalHom φ := by
    constructor
    intro a ha
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hu : IsUnit (algebraMap R S r) := isUnit_of_map_unit (Ideal.Quotient.mk I) _ ha
    exact (Ideal.Quotient.mk p).isUnit_map (isUnit_of_map_unit (algebraMap R S) _ hu)
  have : IsLocalHom (algebraMap (R ⧸ p) (S ⧸ I)) := ‹IsLocalHom φ›
  have hmap : (maximalIdeal (R ⧸ p)).map (algebraMap (R ⧸ p) (S ⧸ I)) =
      J.map (Ideal.Quotient.mk I) := by
    rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective,
      Ideal.map_map, Ideal.map_map]
    rfl
  have hd : ringKrullDim ((S ⧸ I) ⧸
      (maximalIdeal (R ⧸ p)).map (algebraMap (R ⧸ p) (S ⧸ I))) = 0 := by
    rwa [hmap, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIJ)]
  have hh' : ringKrullDim (S ⧸ I) ≤ ringKrullDim (R ⧸ p) +
      ringKrullDim ((S ⧸ I) ⧸
        (maximalIdeal (R ⧸ p)).map (algebraMap (R ⧸ p) (S ⧸ I))) := by
    rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]
    have hhcast := WithBot.coe_le_coe.mpr
      (Ideal.height_le_height_add_of_liesOver (maximalIdeal (R ⧸ p)) (maximalIdeal (S ⧸ I)))
    rw [WithBot.coe_add] at hhcast
    exact hhcast.trans (add_le_add le_rfl Ideal.height_le_ringKrullDim_of_isPrime)
  simpa only [hd, add_zero] using hh'.trans (by simpa only [hd, add_zero] using hpdim)

/-- **The source's associated primes are Mathlib's.** Over a Noetherian ring a prime is the
annihilator of a single element of `M` (Stacks 00LA) exactly when it belongs to
`associatedPrimes R M`. -/
theorem isAssociatedPrimeStacks_iff_mem_associatedPrimes {R M : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup M] [Module R M] (p : Ideal R) :
    IsAssociatedPrimeStacks R M p ↔ p ∈ associatedPrimes R M := by
  show _ ↔ IsAssociatedPrime p M
  rw [isAssociatedPrime_iff]
  constructor <;> rintro ⟨hp, m, hm⟩ <;> refine ⟨hp, m, ?_⟩
  · ext r
    rw [← hm, Submodule.mem_colon_singleton, Submodule.mem_colon_span_singleton]
  · ext r
    rw [hm, Submodule.mem_colon_span_singleton, Submodule.mem_colon_singleton]

/-- **Associated primes below the maximal ideal survive a flat base change.** Let `R → S` be a
flat local homomorphism of Noetherian local rings and let `p` be a prime associated to an
`R`-module `M` with `p < 𝔪_R`. Then some prime `q` of `S` associated to `S ⊗_R M` lies over `p`
and satisfies `q < 𝔪_S`. -/
theorem exists_isAssociatedPrimeStacks_over_of_flat
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] [AddCommGroup M] [Module R M]
    (p : Ideal R) (hp : IsAssociatedPrimeStacks R M p) (hlt : p < maximalIdeal R) :
    ∃ q : Ideal S, IsAssociatedPrimeStacks S (S ⊗[R] M) q ∧
      q.under R = p ∧ q < maximalIdeal S := by
  have : p.IsPrime := hp.1
  obtain ⟨q₀, hq₀, hprime, hover⟩ :=
    Ideal.exists_ideal_lt_liesOver_of_lt (R := R) (S := S)
      (q := maximalIdeal R) (maximalIdeal S) hlt
  have : q₀.IsPrime := hprime
  have : q₀.LiesOver p := hover
  have hle : p.map (algebraMap R S) ≤ q₀ := Ideal.map_le_iff_le_comap.mpr
    (Ideal.LiesOver.over (p := p) (P := q₀)).le
  obtain ⟨q, hq, hqq₀⟩ := Ideal.exists_minimalPrimes_le hle
  have : q.IsPrime := hq.1.1
  have hqp : q.under R = p := le_antisymm
    ((Ideal.comap_mono hqq₀).trans (Ideal.LiesOver.over (p := p) (P := q₀)).ge)
    (Ideal.map_le_iff_le_comap.mp hq.1.2)
  have hass : q ∈ associatedPrimes S (S ⧸ p.map (algebraMap R S)) :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes S _
      (by simpa only [Ideal.annihilator_quotient] using hq)
  have ha : q.IsPrime ∧ ∃ n : S ⧸ (p.map (algebraMap R S) • (⊤ : Submodule S S)),
      (⊥ : Submodule S _).colon {n} = q := by
    have heq : p.map (algebraMap R S) • (⊤ : Submodule S S) = p.map (algebraMap R S) :=
      Ideal.mul_top _
    rw [heq]
    obtain ⟨hq, n, hn⟩ := isAssociatedPrime_iff.mp hass
    exact ⟨hq, n, hn.symm⟩
  have hpa : p.IsPrime ∧ ∃ m : M, (⊥ : Submodule R M).colon {m} = p := by
    simpa only [eq_comm] using
      isAssociatedPrime_iff.mp ((isAssociatedPrimeStacks_iff_mem_associatedPrimes p).mp hp)
  have h := (associatedPrimes.tensorProduct_of_flat (R := R) (S := S) (M := M)
    (N := S)).1 (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hpa, ha⟩⟩)
  exact ⟨q, (isAssociatedPrimeStacks_iff_mem_associatedPrimes q).mpr
    (isAssociatedPrime_iff.mpr (by simpa only [Set.mem_setOf_eq, eq_comm] using h)),
    hqp, hqq₀.trans_lt hq₀⟩

/-- **A one-dimensional quotient leaves no room between `q` and `𝔪_S`.** If `I ≤ q` with `q`
prime, `q < 𝔪_S` and `dim (S ⧸ I) ≤ 1`, then every prime `r` with `q ≤ r ≤ 𝔪_S` is `q` or
`𝔪_S`: a third prime strictly in between would give a chain of length `2` in `Spec (S ⧸ I)`. -/
theorem covBy_maximalIdeal_of_ringKrullDim_quotient_le_one
    {S : Type*} [CommRing S] [IsLocalRing S]
    (I q : Ideal S) [q.IsPrime] (hIq : I ≤ q) (hq : q < maximalIdeal S)
    (hdim : ringKrullDim (S ⧸ I) ≤ 1) :
    ∀ r : Ideal S, r.IsPrime → q ≤ r → r ≤ maximalIdeal S → r = q ∨ r = maximalIdeal S := by
  intro r hr hqr hrm
  by_contra hc
  have hqr' : q < r := lt_of_le_of_ne hqr (by tauto)
  have hrm' : r < maximalIdeal S := lt_of_le_of_ne hrm (by tauto)
  let Q : PrimeSpectrum (S ⧸ I) :=
    ⟨q.map (Ideal.Quotient.mk I), Ideal.isPrime_map_quotientMk_of_isPrime hIq⟩
  let P : PrimeSpectrum (S ⧸ I) :=
    ⟨r.map (Ideal.Quotient.mk I), Ideal.isPrime_map_quotientMk_of_isPrime (hIq.trans hqr)⟩
  let L : PrimeSpectrum (S ⧸ I) :=
    ⟨(maximalIdeal S).map (Ideal.Quotient.mk I),
      Ideal.isPrime_map_quotientMk_of_isPrime (hIq.trans hq.le)⟩
  have hmap {a b : Ideal S} (ha : I ≤ a) (hb : I ≤ b) (hab : a < b) :
      a.map (Ideal.Quotient.mk I) < b.map (Ideal.Quotient.mk I) := by
    apply lt_of_le_of_ne (Ideal.map_mono hab.le)
    intro he
    apply hab.ne
    have := congrArg (Ideal.comap (Ideal.Quotient.mk I)) he
    simpa only [Ideal.comap_map_quotientMk, sup_eq_right.mpr ha, sup_eq_right.mpr hb] using this
  have hQP : Q < P := hmap hIq (hIq.trans hqr) hqr'
  have hPL : P < L := hmap (hIq.trans hqr) (hIq.trans hq.le) hrm'
  have htwo : (2 : ℕ∞) ≤ Order.height L := by
    have h₁ : (1 : ℕ∞) ≤ Order.height P := le_add_self.trans (Order.height_add_one_le hQP)
    calc
      _ = 1 + 1 := by norm_num
      _ ≤ Order.height P + 1 := add_le_add h₁ le_rfl
      _ ≤ Order.height L := Order.height_add_one_le hPL
  have : (2 : WithBot ℕ∞) ≤ 1 :=
    (WithBot.coe_le_coe.mpr htwo).trans ((Order.height_le_krullDim L).trans hdim)
  norm_num at this

end Stacks.Depth

end
