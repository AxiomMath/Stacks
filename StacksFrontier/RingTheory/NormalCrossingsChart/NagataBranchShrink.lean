module

public import StacksFrontier.RingTheory.Nagata.FiniteType
public import StacksFrontier.RingTheory.NormalCrossingsChart.NagataNormalShrink
public import StacksFrontier.RingTheory.NormalCrossingsChart.RegularHypersurfaceShrink
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Shrinking to a normal branch on a Nagata base

Let `B` be a Noetherian Nagata ring, `y : B`, and `q` a prime containing `y` at which the local
ring of the hypersurface `B ⧸ (y)` is regular. Then the hypersurface is normal at every point of
a basic open neighbourhood of `q`: there is `t ∉ q` such that for every prime `q' ∋ y` with
`t ∉ q'` the local ring of `B ⧸ (y)` at `q'` is a normal domain. This is the Nagata shrinking step
of Stacks Tag 0CBS, with the regular point of the hypersurface supplying the normal point that
`exists_notMem_forall_isDomain_and_isIntegrallyClosed_of_isNagataRing_away` propagates.

## Main results

* `exists_notMem_forall_isDomain_and_isIntegrallyClosed_quotient_of_isNagataRing`: the shrinking
  step. Normality is spelled `IsDomain` together with `IsIntegrallyClosed`, Mathlib having no
  predicate for a normal ring.

Along the way, in the namespace `Stacks.NagataBranchShrink`:

* `exists_notMem_forall_mul_mem_nilradical_eq_zero`: in a Noetherian ring with a reduced
  localization at `𝔭` a single element outside `𝔭` kills the whole nilradical.
* `isReduced_localization_atPrime_of_forall_mul_eq_zero`: such an element cuts out a basic open
  on which every localization is reduced.

## Implementation notes

The hypersurface is carried as the quotient ring `B ⧸ (y)` rather than as a scheme, its points as
`Stacks.NormalCrossingsChart.quotPoint`; an element of `B` lies outside `q` exactly when its
image lies outside `quotPoint y q hy`, which is how the denominator produced downstairs is lifted
to `B` at the end.

Two shrinkings are composed, and the composite is the single element returned by
`exists_notMem_forall_isDomain_and_isIntegrallyClosed_of_isNagataRing_away`, whose `u` is the
first of them. The first is reducedness, and needs no Nagata hypothesis: regularity at `q` makes
the local ring there a domain, hence reduced, so each of the finitely many generators of the
nilradical of `B ⧸ (y)` is killed by an element outside `quotPoint y q hy`, and the product `s`
of those kills the nilradical outright. A prime avoiding `s` then has a reduced localization,
because a nilpotent `mk' n u` there has `v * n` nilpotent in `B ⧸ (y)` for some `v` outside the
prime, and `s * v * n = 0` exhibits `mk' n u` as zero. The second is normality, which is where
Nagata enters: `B ⧸ (y)` is of finite type over `B`, hence Nagata by Tag 0334, and regularity at
`q` gives a domain which is a unique factorization domain by Tag 0AG0, hence integrally closed.

## References

* [Stacks Project, Tag 0CBS](https://stacks.math.columbia.edu/tag/0CBS)
* [Stacks Project, Tag 0332](https://stacks.math.columbia.edu/tag/0332)
* [Stacks Project, Tag 0334](https://stacks.math.columbia.edu/tag/0334)
* [Stacks Project, Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0)
-/

@[expose] public section

universe u

namespace Stacks.NagataBranchShrink

section Nilradical

variable {R : Type u} [CommRing R]

/-- **One element kills the nilradical near a reduced point.** In a Noetherian ring whose
localization at the prime `𝔭` is reduced there is `s ∉ 𝔭` with `s * n = 0` for every nilpotent
`n`. -/
public theorem exists_notMem_forall_mul_mem_nilradical_eq_zero [IsNoetherianRing R]
    (𝔭 : Ideal R) [𝔭.IsPrime] (hred : IsReduced (Localization.AtPrime 𝔭)) :
    ∃ s ∉ 𝔭, ∀ n ∈ nilradical R, s * n = 0 := by
  classical
  obtain ⟨G, hG⟩ : (nilradical R).FG := IsNoetherian.noetherian _
  have hchoice : ∀ g : R, g ∈ nilradical R → ∃ m : 𝔭.primeCompl, (m : R) * g = 0 := by
    intro g hg
    refine (IsLocalization.map_eq_zero_iff 𝔭.primeCompl (Localization.AtPrime 𝔭) g).mp ?_
    obtain ⟨k, hk⟩ := mem_nilradical.mp hg
    exact IsReduced.eq_zero _ ⟨k, by rw [← map_pow, hk, map_zero]⟩
  choose! m hm using hchoice
  refine ⟨∏ g ∈ G, (m g : R), Submonoid.prod_mem _ fun g _ => (m g).2, ?_⟩
  intro n hn
  rw [← hG] at hn
  induction hn using Submodule.span_induction with
  | mem g hg =>
      rw [← Finset.mul_prod_erase G (fun x => (m x : R)) (Finset.mem_coe.mp hg), mul_right_comm,
        hm g (hG.le (Submodule.subset_span hg)), zero_mul]
  | zero => exact mul_zero _
  | add x z _ _ hx hz => rw [mul_add, hx, hz, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, mul_left_comm, hx, mul_zero]

/-- **Reducedness spreads over a basic open.** If `s` kills every nilpotent of `R` then the
localization of `R` at any prime avoiding `s` is reduced. -/
@[ega "0 1.2.8" "special case"]
public theorem isReduced_localization_atPrime_of_forall_mul_eq_zero {s : R}
    (hs : ∀ n ∈ nilradical R, s * n = 0) (𝔮 : Ideal R) [𝔮.IsPrime] (hs𝔮 : s ∉ 𝔮) :
    IsReduced (Localization.AtPrime 𝔮) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨n, u⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl x
  obtain ⟨k, hk⟩ := hx
  have hk1 : IsLocalization.mk' (Localization.AtPrime 𝔮) n u ^ (k + 1) = 0 := by
    rw [pow_succ, hk, zero_mul]
  have h1 : algebraMap R (Localization.AtPrime 𝔮) (n ^ (k + 1)) = 0 := by
    rw [map_pow, ← IsLocalization.mk'_spec (Localization.AtPrime 𝔮) n u, mul_pow, hk1, zero_mul]
  obtain ⟨v, hv⟩ :=
    (IsLocalization.map_eq_zero_iff 𝔮.primeCompl (Localization.AtPrime 𝔮) (n ^ (k + 1))).mp h1
  have hnil : (v : R) * n ∈ nilradical R := by
    refine mem_nilradical.mpr ⟨k + 1, ?_⟩
    rw [show ((v : R) * n) ^ (k + 1) = (v : R) ^ k * ((v : R) * n ^ (k + 1)) by ring, hv,
      mul_zero]
  refine (IsLocalization.mk'_eq_zero_iff n u).mpr
    ⟨⟨s * (v : R), Submonoid.mul_mem _ (show s ∈ 𝔮.primeCompl from hs𝔮) v.2⟩, ?_⟩
  change s * (v : R) * n = 0
  rw [mul_assoc]
  exact hs _ hnil

end Nilradical

section Quotient

variable {B : Type u} [CommRing B]


/-- An element of `B` lies in a prime `q ∋ y` exactly when its image lies in the corresponding
point of `Spec (B ⧸ (y))`. -/
private theorem mem_quotPoint_iff {y : B} {q : PrimeSpectrum B} (hy : y ∈ q.asIdeal) (t : B) :
    Ideal.Quotient.mk (Ideal.span {y} : Ideal B) t ∈
        (Stacks.NormalCrossingsChart.quotPoint y q hy).asIdeal ↔ t ∈ q.asIdeal := by
  conv_rhs => rw [← Stacks.NormalCrossingsChart.comap_map_quot hy]
  exact Ideal.mem_comap.symm

end Quotient

end Stacks.NagataBranchShrink

open Stacks.NagataBranchShrink Stacks.NormalCrossingsChart in
/-- **The branches of a hypersurface are normal near a regular point, over a Nagata base.** Let
`B` be a Noetherian Nagata ring, `y : B` and `q` a prime containing `y` at which the local ring
of `B ⧸ (y)` is regular. Then there is `t ∉ q` such that for every prime `q' ∋ y` with `t ∉ q'`
the local ring of `B ⧸ (y)` at `q'` is a normal domain.

Normality of a local ring is spelled as `IsDomain` together with `IsIntegrallyClosed`, Mathlib
having no predicate for a normal ring. -/
public theorem exists_notMem_forall_isDomain_and_isIntegrallyClosed_quotient_of_isNagataRing
    {B : Type u} [CommRing B] [IsNoetherianRing B] (hB : IsNagataRing B)
    (y : B) (q : PrimeSpectrum B) (hy : y ∈ q.asIdeal)
    (hreg : IsRegularLocalRing (Localization.AtPrime
      (Stacks.NormalCrossingsChart.quotPoint y q hy).asIdeal)) :
    ∃ t ∉ q.asIdeal, ∀ (q' : PrimeSpectrum B) (hy' : y ∈ q'.asIdeal), t ∉ q'.asIdeal →
      IsDomain (Localization.AtPrime
        (Stacks.NormalCrossingsChart.quotPoint y q' hy').asIdeal) ∧
      IsIntegrallyClosed (Localization.AtPrime
        (Stacks.NormalCrossingsChart.quotPoint y q' hy').asIdeal) := by
  classical
  have htfae : IsNagataRing B ↔
      ∀ (S : Type u) [CommRing S] [Algebra B S] [Algebra.FiniteType B S], IsNagataRing S :=
    isNagataRing_tfae.out 1 2
  have hNag : IsNagataRing (B ⧸ (Ideal.span {y} : Ideal B)) := htfae.mp hB _
  have hdom : IsDomain (Localization.AtPrime (quotPoint y q hy).asIdeal) :=
    IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (Localization.AtPrime (quotPoint y q hy).asIdeal) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  have hic : IsIntegrallyClosed (Localization.AtPrime (quotPoint y q hy).asIdeal) := inferInstance
  obtain ⟨s, hs𝔭, hs⟩ :=
    exists_notMem_forall_mul_mem_nilradical_eq_zero (quotPoint y q hy).asIdeal inferInstance
  obtain ⟨t', ht'𝔭, ht'⟩ :=
    exists_notMem_forall_isDomain_and_isIntegrallyClosed_of_isNagataRing_away hNag s hs𝔭
      (fun 𝔮 _ h => isReduced_localization_atPrime_of_forall_mul_eq_zero hs 𝔮 h) hdom hic
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t'
  exact ⟨t, (mem_quotPoint_iff hy t).not.mp ht'𝔭, fun q' hy' htq' =>
    ht' (quotPoint y q' hy').asIdeal ((mem_quotPoint_iff hy' t).not.mpr htq')⟩

end
