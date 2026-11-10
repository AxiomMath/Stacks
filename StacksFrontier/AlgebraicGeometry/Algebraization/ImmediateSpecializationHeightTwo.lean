module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.Algebraization.StalkOfIdealOnOpen
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
import StacksFrontier.AlgebraicGeometry.Algebraization.NonCatenaryCounterexample.Points

/-!
# An immediate specialization of a dimension-two point of `U ∩ Y`

Fix an affine algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, giving
`X = Spec(A)`, the closed subscheme `Y = V(I)` and the open complement `U = X ∖ V(𝔞)`.  Assume
moreover that `A` is local and that `𝔞` is its maximal ideal.

A point `y` of `U ∩ Y` whose closure has dimension two then admits an *immediate* specialization
`y'` inside `U ∩ Y` whose closure has dimension one, together with the data that a later
application of the formal-functions criterion needs at `y'`: the prime `q` of the local ring
`𝒪_{U,y'}` corresponding to `y`, the fact that `q` contains the stalk of `I𝒪_U` at `y'`, and the
computation `dim(𝒪_{U,y'}/q) = 1`.

## Main results

* `Stacks.Algebraization.exists_specializes_height_one` — the statement just described.

## Implementation notes

The dimension of the closure of a point of `X` is its height in the specialization order of the
scheme, in which `a ≤ b ↔ b ⤳ a`.  Through `AlgebraicGeometry.specOrderIsoPrimeSpectrum` this is
the coheight of the corresponding prime in the inclusion order of `Spec(A)`, which is the form in
which the whole argument is run.

Write `𝔮 ⊆ A` for the prime under `y`.  The hypothesis is `coheight 𝔮 = 2`, so
`Order.coheight_eq_coe_add_one_iff` produces at one stroke a prime `𝔮' ⊋ 𝔮` of coheight one and
the bound `coheight r ≤ 1` for every prime `r ⊋ 𝔮`.  Together these say that no prime lies
strictly between `𝔮` and `𝔮'`: such a prime would have coheight at least `coheight 𝔮' + 1 = 2`.
That is what makes the specialization immediate, and it is also what computes the last clause,
because `AlgebraicGeometry.Scheme.fromSpecStalk` identifies the primes of `𝒪_{U,y'}` with the
points of `U` specializing to `y'`, order-reversingly for the specialization order and hence
order-preservingly for the inclusion order of primes of `A`.

That `𝔮'` lies in `U` is forced by its coheight: a prime of nonzero coheight is not the maximal
ideal, and `𝔞` is the maximal ideal.  That it lies in `Y` is inherited from `𝔮`, which contains
`I`.  No catenarity hypothesis is needed: both the existence of `𝔮'` and the absence of a prime
between `𝔮` and `𝔮'` come from the coheight bookkeeping alone.

## References

* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EJA](https://stacks.math.columbia.edu/tag/0EJA)
* [Stacks Project, Tag 0EHW](https://stacks.math.columbia.edu/tag/0EHW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Algebraization

/-- The dimension of the closure of a point of `U`, measured as its height in the specialization
order of `X = Spec(A)`, is the coheight of the prime of `A` under it. -/
private alias height_base_eq_coheight := height_U_ι_base_eq_coheight

/-- **At a point of `U ∩ Y` whose closure has dimension two there is an immediate specialization
inside `U ∩ Y` whose closure has dimension one.**

In the affine algebraization situation with `A` local and `𝔞 = 𝔪`, let `y` be a point of `U`
lying on `Y` whose closure has dimension two.  Then there is a point `y'` of `U`, again lying on
`Y`, such that `y ⤳ y'`, the closure of `y'` has dimension one, and the prime `q` of the local
ring `𝒪_{U,y'}` corresponding to `y` contains the stalk of `I𝒪_U` at `y'` and satisfies
`dim(𝒪_{U,y'}/q) = 1`; the last clause says that `y'` is an *immediate* specialization of `y`. -/
public theorem exists_specializes_height_one
    (S : AlgebraizationSituation.{u}) [IsLocalRing S.A] (ha : S.a = IsLocalRing.maximalIdeal S.A)
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (hheight : Order.height (S.U.ι.base y) = 2) :
    ∃ (y' : S.U.toScheme) (z' : S.Y) (q : PrimeSpectrum (S.U.toScheme.presheaf.stalk y')),
      y ⤳ y' ∧
      S.U.ι.base y' = S.Yι.base z' ∧
      Order.height (S.U.ι.base y') = 1 ∧
      S.U.toScheme.fromSpecStalk y' q = y ∧
      IdealSheafData.stalk (idealOnOpen S) y' ≤ q.asIdeal ∧
      ringKrullDim (S.U.toScheme.presheaf.stalk y' ⧸ q.asIdeal) = 1 := by
  classical
  -- The prime of `A` under `y`, of coheight two.
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum S.A, underlyingPrime S y = p := ⟨_, rfl⟩
  have hcop : Order.coheight p = ((1 : ℕ) : ℕ∞) + 1 := by
    rw [← hp, ← height_base_eq_coheight S y, hheight]
    norm_num
  obtain ⟨-, ⟨p', hpp', hcop'⟩, hbound⟩ := Order.coheight_eq_coe_add_one_iff.mp hcop
  have hcop1 : Order.coheight p' = 1 := by simpa using hcop'
  have hbound1 : ∀ r : PrimeSpectrum S.A, p < r → Order.coheight r ≤ 1 := by
    intro r hr
    simpa using hbound r hr
  -- No prime lies strictly between `p` and `p'`.
  have hbetween : ∀ r : PrimeSpectrum S.A, p < r → r ≤ p' → r = p' := by
    intro r hr hrp'
    by_contra hne
    have h1 : Order.coheight p' + 1 ≤ Order.coheight r :=
      Order.coheight_add_one_le (lt_of_le_of_ne hrp' hne)
    rw [hcop1] at h1
    have h2 : ((1 : ℕ∞) + 1) ≤ 1 := h1.trans (hbound1 r hr)
    norm_num at h2
  -- `p'` is not the maximal ideal, so it lies in `U`.
  have hp'a : ¬ S.a ≤ p'.asIdeal := by
    intro hsub
    have hmax : IsLocalRing.maximalIdeal S.A ≤ p'.asIdeal := by rw [← ha]; exact hsub
    have heq : p' = (⊤ : PrimeSpectrum S.A) := by
      refine PrimeSpectrum.ext ?_
      change p'.asIdeal = IsLocalRing.maximalIdeal S.A
      exact le_antisymm (IsLocalRing.le_maximalIdeal p'.2.ne_top) hmax
    rw [heq, Order.coheight_top] at hcop1
    exact zero_ne_one hcop1
  have hmemU : (p' : S.X) ∈ (S.U : Set S.X) := by
    change p' ∉ PrimeSpectrum.zeroLocus (S.a : Set S.A)
    rw [PrimeSpectrum.mem_zeroLocus]
    exact hp'a
  rw [← Scheme.Opens.range_ι S.U] at hmemU
  obtain ⟨y', hy'⟩ := hmemU
  have hy'base : underlyingPrime S y' = p' := hy'
  -- `p'` contains `I`, so it lies on `Y`.
  have hIp : S.I ≤ p.asIdeal := by
    have hx : underlyingPrime S y = S.Yι.base z :=
      congrArg (fun t : S.X => (t : PrimeSpectrum S.A)) hyz
    rw [← hp, hx]
    intro a hal
    change Ideal.Quotient.mk S.I a ∈ (z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hal]
    exact Submodule.zero_mem _
  have hIp' : S.I ≤ p'.asIdeal := hIp.trans hpp'.le
  obtain ⟨z', hz'⟩ : p' ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk S.I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      PrimeSpectrum.mem_zeroLocus, Ideal.mk_ker]
    exact hIp'
  have hz'base : (S.Yι.base z' : PrimeSpectrum S.A) = p' := hz'
  -- `y` specializes to `y'`.
  have hspecX : S.U.ι.base y ⤳ S.U.ι.base y' := by
    have h := (PrimeSpectrum.le_iff_specializes p p').mp hpp'.le
    rwa [← hp, ← hy'base] at h
  have hspec : y ⤳ y' := S.U.ι.isOpenEmbedding.isInducing.specializes_iff.mp hspecX
  obtain ⟨q, hq⟩ := exists_fromSpecStalk_eq_of_specializes hspec
  -- The primes of `𝒪_{U,y'}`, read as primes of `A`.
  set g : PrimeSpectrum (S.U.toScheme.presheaf.stalk y') → PrimeSpectrum S.A :=
    fun r => S.U.ι.base (S.U.toScheme.fromSpecStalk y' r) with hgdef
  have hgle : ∀ r₁ r₂, g r₁ ≤ g r₂ ↔ r₁ ≤ r₂ := fun r₁ r₂ =>
    (PrimeSpectrum.le_iff_specializes (g r₁) (g r₂)).trans
      ((S.U.ι.isOpenEmbedding.isInducing.specializes_iff.trans
        (S.U.toScheme.fromSpecStalk y').isEmbedding.isInducing.specializes_iff).trans
        (PrimeSpectrum.le_iff_specializes r₁ r₂).symm)
  have hginj : Function.Injective g := fun r₁ r₂ h =>
    le_antisymm ((hgle r₁ r₂).mp h.le) ((hgle r₂ r₁).mp h.ge)
  have hg : ∀ (r) (x : S.U.toScheme), S.U.toScheme.fromSpecStalk y' r = x →
      g r = underlyingPrime S x := fun r x h => by rw [← h]; rfl
  have hgq : g q = p := (hg q y hq).trans hp
  have hgtop : g ⊤ = p' :=
    (hg _ y' Scheme.fromSpecStalk_closedPoint).trans hy'base
  -- The coheight of `q` in `𝒪_{U,y'}` is one.
  have hqlt : q < ⊤ := by
    refine lt_of_le_of_ne le_top fun hcon => ?_
    exact absurd (hgq.symm.trans (hcon ▸ hgtop)) (ne_of_lt hpp')
  have hcoq_ge : 1 ≤ Order.coheight q := by
    have h := Order.coheight_add_one_le hqlt
    rwa [Order.coheight_top, zero_add] at h
  have hcoq_le : Order.coheight q ≤ ((1 : ℕ) : ℕ∞) := by
    refine Order.coheight_le_coe_iff.mpr fun r hr => ?_
    have hlt : g q < g r :=
      lt_of_le_of_ne ((hgle q r).mpr hr.le) fun he => absurd (hginj he) (ne_of_lt hr)
    have hrtop : g r ≤ p' := hgtop ▸ (hgle r ⊤).mpr le_top
    have hreq : r = ⊤ := hginj ((hbetween (g r) (hgq ▸ hlt) hrtop).trans hgtop.symm)
    rw [hreq, Order.coheight_top]
    norm_num
  have hcoq : Order.coheight q = 1 := le_antisymm (by simpa using hcoq_le) hcoq_ge
  -- The stalk of `I𝒪_U` at `y'` is contained in `q`.
  have hysupp : y ∈ ((idealOnOpen S).support : Set S.U.toScheme) := by
    have h := (Stacks.Chow.le_iff_fromSpecStalk_mem_support (idealOnOpen S) y
      (IsLocalRing.closedPoint (S.U.toScheme.presheaf.stalk y))).mp
      (stalk_idealOnOpen_le_maximalIdeal S y z hyz)
    rwa [Scheme.fromSpecStalk_closedPoint] at h
  refine ⟨y', z', q, hspec, ?_, ?_, hq, ?_, ?_⟩
  · exact hy'base.trans hz'base.symm
  · rw [height_base_eq_coheight S y', hy'base, hcop1]
  · exact (Stacks.Chow.le_iff_fromSpecStalk_mem_support (idealOnOpen S) y' q).mpr
      (by rw [hq]; exact hysupp)
  · rw [← coheight_eq_ringKrullDim_quotient q, hcoq]
    rfl

end Stacks.Algebraization

end
