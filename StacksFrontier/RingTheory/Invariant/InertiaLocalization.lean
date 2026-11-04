module

public import Mathlib.RingTheory.Localization.AsSubring
public import StacksFrontier.RingTheory.Invariant.InertiaIndEtale

/-!
# Invariants of a localized integral closure

Let `A` be a normal domain with fraction field `K`, let `L / K` be a possibly infinite Galois
extension with group `G = Gal(L/K)` and let `B` be the integral closure of `A` in `L`. Let `q` be
a prime of `B` and let `H` be a subgroup of `G` stabilizing `q` — the inertia group
`I = q.inertia G` is one, by `Ideal.inertia_le_stabilizer`.

Taking `H`-invariants and localizing at `q` commute: the `H`-invariants of `B_q` are the
localization of `B ^ H` at the prime below `q`. The point is that a denominator can be made
`H`-invariant. For a finite group one multiplies `s` by its conjugates; for the infinite groups
here the orbit of `s` is still finite, because it sits inside the root set of the minimal
polynomial of `s` over `K`, so the product over the orbit is again available.

## Main results

* `IsIntegralClosure.notMem_smul_of_notMem`: an automorphism stabilizing `q` preserves its
  complement, so that it carries denominators to denominators.
* `IsIntegralClosure.exists_invariant_dvd_of_notMem`: a denominator outside `q` divides an
  `H`-invariant denominator outside `q`.
* `IsIntegralClosure.exists_invariant_num_den`: an element of `L` has a denominator outside `q`
  and is `H`-invariant exactly when it is a fraction with numerator and denominator in `B ^ H`,
  the denominator outside `q`.
* `IsIntegralClosure.exists_inertia_invariant_num_den`: the same for the inertia group, in the
  vocabulary of Stacks 0BSU.

## Implementation notes

The orbit of `s` under `H` is finite because `(σ s : L)` is a root of `minpoly K s` for every
`σ`, and a polynomial has finitely many roots in a domain. This replaces the finite product over
the group used when `H` is finite, and is the only place where algebraicity of `L / K` enters.

## References

* [Stacks Project, Tag 0BSU](https://stacks.math.columbia.edu/tag/0BSU)
* [Stacks Project, Tag 0BSW](https://stacks.math.columbia.edu/tag/0BSW)

## Tags

integral closure, inertia group, invariants, localization, Galois action, orbit
-/

@[expose] public section

namespace IsIntegralClosure

open scoped Pointwise

universe u

variable (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsFractionRing A K] [IsGalois K L]

-- The action of `Gal(L/K)` on the integral closure of `A` in `L`, and its commutation with the
-- `A`-algebra structure, are `IsIntegralClosure.galAction` and
-- `IsIntegralClosure.galSMulCommClass` of `StacksFrontier.RingTheory.Invariant.InertiaIndEtale`.
attribute [local instance] galAction galSMulCommClass

/-- The action of `Gal(L/K)` on the integral closure is the restriction of the action on `L`. -/
alias coe_smul := coe_galSmul

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- **An automorphism stabilizing a prime preserves its complement.** If `σ` fixes the prime `q`
of the integral closure, then it carries elements outside `q` to elements outside `q`. -/
theorem notMem_smul_of_notMem {q : Ideal (integralClosure A L)} {σ : Gal(L/K)}
    (hσ : σ • q = q) {x : integralClosure A L} (hx : x ∉ q) : σ • x ∉ q := by
  rwa [← hσ, Ideal.smul_mem_pointwise_smul_iff]

variable {A K L}

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The orbit of an element of the integral closure under a subgroup of `Gal(L/K)` is finite:
every conjugate is a root of the minimal polynomial over `K`. -/
theorem finite_orbit (H : Subgroup Gal(L/K)) (s : integralClosure A L) :
    (Set.range (fun σ : H => (σ : Gal(L/K)) • s)).Finite := by
  refine Set.Finite.of_finite_image (f := fun x : integralClosure A L => (x : L)) ?_
    (Set.injOn_of_injective Subtype.val_injective)
  refine Set.Finite.subset ((minpoly K (s : L)).rootSet_finite L) ?_
  rintro x ⟨-, ⟨σ, rfl⟩, rfl⟩
  refine Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), ?_⟩
  change Polynomial.aeval (((σ : Gal(L/K)) • s : integralClosure A L) : L)
    (minpoly K (s : L)) = 0
  rw [coe_smul, show ((σ : Gal(L/K)) (s : L)) = (σ : Gal(L/K)).toAlgHom (s : L) from rfl,
    Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]

omit [IsDomain A] [IsIntegrallyClosed A] in
variable (A K L) in
/-- **An invariant denominator.** Let `H` be a subgroup of `Gal(L/K)` stabilizing the prime `q`
of the integral closure. Every `s ∉ q` divides an `H`-invariant element outside `q`, namely the
product of the (finite) `H`-orbit of `s`. -/
theorem exists_invariant_dvd_of_notMem (q : Ideal (integralClosure A L)) [hq : q.IsPrime]
    (H : Subgroup Gal(L/K)) (hH : ∀ σ ∈ H, σ • q = q)
    (s : integralClosure A L) (hs : s ∉ q) :
    ∃ t : integralClosure A L, (∀ σ : H, (σ : Gal(L/K)) • t = t) ∧ t ∉ q ∧ s ∣ t := by
  classical
  set T : Finset (integralClosure A L) := (finite_orbit H s).toFinset with hT
  have hmemT : ∀ x, x ∈ T ↔ ∃ σ : H, (σ : Gal(L/K)) • s = x := fun x => by
    rw [hT, Set.Finite.mem_toFinset, Set.mem_range]
  have hsT : s ∈ T := (hmemT s).mpr ⟨1, one_smul _ _⟩
  refine ⟨∏ y ∈ T, y, ?_, ?_, Finset.dvd_prod_of_mem _ hsT⟩
  · intro τ
    have hinj : ∀ x ∈ T, ∀ y ∈ T, (τ : Gal(L/K)) • x = (τ : Gal(L/K)) • y → x = y :=
      fun x _ y _ h => by simpa using congrArg (fun z => (τ : Gal(L/K))⁻¹ • z) h
    have himage : T.image (fun y => (τ : Gal(L/K)) • y) = T := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) (Finset.card_image_of_injOn hinj).ge
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨σ, rfl⟩ := (hmemT y).mp hy
      exact (hmemT _).mpr ⟨τ * σ, by rw [Subgroup.coe_mul, mul_smul]⟩
    calc (τ : Gal(L/K)) • ∏ y ∈ T, y
        = ∏ y ∈ T, (τ : Gal(L/K)) • y :=
          map_prod (MulSemiringAction.toRingHom Gal(L/K) (integralClosure A L) τ) _ _
      _ = ∏ z ∈ T.image (fun y => (τ : Gal(L/K)) • y), z :=
          (Finset.prod_image (f := fun z => z) hinj).symm
      _ = ∏ y ∈ T, y := by rw [himage]
  · intro hmem
    obtain ⟨y, hyT, hyq⟩ := hq.prod_mem_iff_exists_mem T |>.mp hmem
    obtain ⟨σ, rfl⟩ := (hmemT y).mp hyT
    exact notMem_smul_of_notMem A K L (hH σ σ.2) hs hyq

omit [IsDomain A] [IsIntegrallyClosed A] in
variable (A K L) in
/-- **Invariants and localization commute.** Let `H` be a subgroup of `Gal(L/K)` stabilizing the
prime `q` of the integral closure `B` of `A` in `L`. An element of `L` has a denominator outside
`q` and is fixed by `H` exactly when it is a fraction whose numerator and denominator both lie in
`B ^ H`, the denominator outside `q`. In other words the `H`-invariants of `B_q` are the
localization of `B ^ H` at the prime below `q`, which is the ring Stacks 0BSU is about. -/
theorem exists_invariant_num_den (q : Ideal (integralClosure A L)) [q.IsPrime]
    (H : Subgroup Gal(L/K)) (hH : ∀ σ ∈ H, σ • q = q) (x : L) :
    ((∃ b s : integralClosure A L, s ∉ q ∧ x * (s : L) = (b : L)) ∧
        ∀ σ : H, (σ : Gal(L/K)) x = x)
      ↔ ∃ c t : integralClosure A L, (∀ σ : H, (σ : Gal(L/K)) • c = c) ∧
          (∀ σ : H, (σ : Gal(L/K)) • t = t) ∧ t ∉ q ∧ x * (t : L) = (c : L) := by
  constructor
  · rintro ⟨⟨b, s, hs, hbs⟩, hfix⟩
    obtain ⟨t, htinv, htq, u, hu⟩ := exists_invariant_dvd_of_notMem A K L q H hH s hs
    have hval : ((b * u : integralClosure A L) : L) = x * (t : L) := by
      rw [hu]
      push_cast
      rw [← hbs]
      ring
    refine ⟨b * u, t, fun σ => Subtype.val_injective ?_, htinv, htq, hval.symm⟩
    rw [coe_smul, hval, map_mul, hfix σ, ← coe_smul, htinv σ]
  · rintro ⟨c, t, hcinv, htinv, htq, hxt⟩
    have ht0 : (t : L) ≠ 0 := fun h =>
      htq (by simpa using (Subtype.val_injective h : t = 0) ▸ q.zero_mem)
    refine ⟨⟨c, t, htq, hxt⟩, fun σ => ?_⟩
    have h := congrArg (⇑(σ : Gal(L/K))) hxt
    simp only [map_mul, ← coe_smul, htinv σ, hcinv σ] at h
    exact mul_right_cancel₀ ht0 (h.trans hxt.symm)

omit [IsDomain A] [IsIntegrallyClosed A] in
variable (A K L) in
/-- **The inertia invariants of the localization are the localization of the inertia
invariants.** This is `IsIntegralClosure.exists_invariant_num_den` for the inertia group
`I = q.inertia Gal(L/K)`, stated in the vocabulary of Stacks 0BSU: with `C = B ^ I` and
`p = q ∩ C`, an element of `L` lies in `B_q` and is `I`-invariant exactly when it is a fraction
with numerator in `C` and denominator in `C ∖ p`. The latter condition describes `C_p`, the ring
of `IsIntegralClosure.isFilteredColimitOfEtale_localization_fixedPoints_inertia`, so that result
applies to the inertia invariants of `B_q`. -/
theorem exists_inertia_invariant_num_den (q : Ideal (integralClosure A L)) [q.IsPrime] (x : L) :
    ((∃ b s : integralClosure A L, s ∉ q ∧ x * (s : L) = (b : L)) ∧
        ∀ σ ∈ q.inertia Gal(L/K), σ x = x)
      ↔ ∃ c t : FixedPoints.subalgebra A (integralClosure A L) (q.inertia Gal(L/K)),
          t ∉ q.comap (FixedPoints.subalgebra A (integralClosure A L)
              (q.inertia Gal(L/K))).val ∧
            x * ((t : integralClosure A L) : L) = ((c : integralClosure A L) : L) := by
  have hH : ∀ σ ∈ q.inertia Gal(L/K), σ • q = q := fun σ hσ =>
    MulAction.mem_stabilizer_iff.mp (q.inertia_le_stabilizer hσ)
  rw [show (∀ σ ∈ q.inertia Gal(L/K), σ x = x)
      ↔ ∀ σ : q.inertia Gal(L/K), (σ : Gal(L/K)) x = x from
    ⟨fun h σ => h σ σ.2, fun h σ hσ => h ⟨σ, hσ⟩⟩,
    exists_invariant_num_den A K L q (q.inertia Gal(L/K)) hH x]
  exact ⟨fun ⟨c, t, hcinv, htinv, htq, hxt⟩ => ⟨⟨c, hcinv⟩, ⟨t, htinv⟩, htq, hxt⟩,
    fun ⟨c, t, htq, hxt⟩ => ⟨c, t, c.2, t.2, htq, hxt⟩⟩

end IsIntegralClosure
