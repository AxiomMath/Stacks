module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineCosimplicialSystem

/-!
# A crystalline situation whose nilpotence orders are unbounded

Let `p` be a prime and let `(A, I, γ)` be a divided power ring with `A` an algebra over `ℤ_(p)`
and `p` nilpotent in `A/I`.  Taking `C = A/I` for the target of the structural map makes
`(p, (A, I, γ), C)` an affine crystalline situation, and the finite divided power levels
`(A/p^eA, I/p^eA, γ̄)` of `StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelBase.lean` are
divided power thickenings of `C` over it — indeed objects of the little category `Cris(C/A)`,
because passing to a level does not change the quotient by the divided power ideal.  In the level
`A/p^eA` the image of `p` is killed by `p ^ e` and, when `p` is a nonzero nonunit of a domain `A`,
by nothing smaller: `p ^ (e - 1)` survives.

Specialising to `A = ℤ_(p)` with `I = (p)`, so that `C = 𝐅_p`, the levels therefore form a family
of divided power thickenings on which the nilpotence order of `p` is unbounded, and
`Crystalline.DividedPowerThickening.not_hasProduct_of_forall_exists_pow_natCast_ne_zero` applies
to it: the family has no product in `CRIS(𝐅_p/ℤ_(p))`.

## Main definitions

* `Crystalline.closedFibreSituation` — the affine crystalline situation `(p, (A, I, γ), A/I)`.
* `Crystalline.levelThickeningOfClosedFibre` — the finite divided power level `A/p^eA` as a
  divided power thickening of `A/I`.
* `Crystalline.integersAtPrimeBase` — the divided power ring `(ℤ_(p), (p), γ)` of [Stacks,
  Tag 07GN].
* `Crystalline.integersAtPrimeSituation` — the affine crystalline situation
  `(p, (ℤ_(p), (p), γ), 𝐅_p)`.
* `Crystalline.unboundedLevelFamily` — the family `n ↦ ℤ_(p)/p^{N + n + 1}ℤ_(p)` of divided power
  thickenings of `𝐅_p`.

## Main results

* `Crystalline.isCrystalline_levelThickeningOfClosedFibre` — a finite level of `(A, I, γ)` is an
  object of the little crystalline category `Cris(A/I / A)`.
* `Crystalline.pow_natCast_ne_zero_levelThickeningOfClosedFibre` — in the level `A/p^eA` no power
  of `p` below the `e`-th vanishes, for `A` a domain in which `p` is a nonzero nonunit.
* `Crystalline.nontrivial_unboundedLevelFamily` — the members of the family are nonzero rings, so
  that the nonvanishing statements about them are not about a zero ring.
* `Crystalline.not_hasProduct_unboundedLevelFamily` — **the family of finite levels of `ℤ_(p)` has
  no product in `CRIS(𝐅_p/ℤ_(p))`**, the hypothesis of
  `Crystalline.DividedPowerThickening.not_hasProduct_of_forall_exists_pow_natCast_ne_zero` being
  met by it.

## Implementation notes

The base is `ℤ_(p)` rather than `ℤ_[p]` because `DividedPowers.IntegersAtPrime` carries the
`ℤ_(p)`-algebra structure the level machinery asks for by `Algebra.id`, and because the divided
powers on `(p) ⊆ ℤ_(p)` are supplied by `DividedPowers.exists_dividedPowers_span_natCast`.  No
property of those divided powers beyond their existence enters: the levels are produced by
`Crystalline.exists_forall_isPAdicLevel`, the vanishing `p ^ e = 0` by
`Crystalline.pow_natCast_eq_zero_levelRing`, and the nonvanishing of smaller powers by the
arithmetic of `ℤ_(p)` alone.

## References

* [Stacks Project, Tag 07HN](https://stacks.math.columbia.edu/tag/07HN)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
* [Stacks Project, Tag 07GN](https://stacks.math.columbia.edu/tag/07GN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Crystalline

/-! ### No power of `p` below the level vanishes -/

/-- **Below the exponent `k`, no power of `p` lies in `(p)^k`**, for `p` a nonzero nonunit of a
ring without zero divisors: dividing the containment `p ^ N ∈ (p ^ k)` by `p ^ N` would make
`p ^ (k - N)`, and hence `p`, a unit. -/
theorem pow_natCast_notMem_pAdicIdeal_pow {A : Type u} [CommRing A] [NoZeroDivisors A] {p : ℕ}
    (h0 : (p : A) ≠ 0) (hu : ¬ IsUnit (p : A)) {N k : ℕ} (hNk : N < k) :
    (p : A) ^ N ∉ DividedPowers.pAdicIdeal (A := A) p ^ k := by
  rw [DividedPowers.pAdicIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  rintro ⟨c, hc⟩
  obtain ⟨m, hm⟩ : ∃ m, k = N + (m + 1) := ⟨k - N - 1, by omega⟩
  rw [hm, pow_add, pow_succ'] at hc
  have hone : (1 : A) = (p : A) * ((p : A) ^ m * c) :=
    mul_left_cancel₀ (pow_ne_zero N h0) <|
      calc (p : A) ^ N * 1 = (p : A) ^ N := mul_one _
        _ = (p : A) ^ N * ((p : A) * (p : A) ^ m) * c := hc
        _ = (p : A) ^ N * ((p : A) * ((p : A) ^ m * c)) := by ring
  exact hu (IsUnit.of_mul_eq_one _ hone.symm)

/-! ### The closed fibre as the target of the structural map -/

section ClosedFibre

variable (p : ℕ) [Fact p.Prime] (A : DividedPowerRing.{u})
  [Algebra (DividedPowers.IntegersAtPrime p) A]

/-- **Stacks Project, Tag 07MD.**  The affine crystalline situation `(p, (A, I, γ), A/I)` carried
by a divided power ring over `ℤ_(p)` in which `p` is nilpotent modulo the divided power ideal:
the structural map `A → C` is the quotient map onto the closed fibre, which kills `I` and sends
`p` to a nilpotent element. -/
noncomputable abbrev closedFibreSituation
    (hp : IsNilpotent (Ideal.Quotient.mk A.ideal (p : A))) :
    AffineCrystallineSituation.{u, u} where
  p := p
  A := A
  C := ↥A ⧸ A.ideal
  ideal_map_eq_bot := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.map_quotient_self A.ideal
  prime_nilpotent := by
    rw [← map_natCast (Ideal.Quotient.mk A.ideal) p]
    exact hp

variable (hp : IsNilpotent (Ideal.Quotient.mk A.ideal (p : A)))

/-- The prime of `closedFibreSituation p A hp` is `p`. -/
@[simp]
theorem closedFibreSituation_p : (closedFibreSituation p A hp).p = p := rfl

/-- The base divided power ring of `closedFibreSituation p A hp` is `A`. -/
@[simp]
theorem closedFibreSituation_A : (closedFibreSituation p A hp).A = A := rfl

/-- **Stacks Project, Tag 07MV.**  A finite divided power level `A/p^eA` of the base, as a divided
power thickening of the closed fibre `C = A/I`: the structural map `C → (A/p^eA)/(I/p^eA)` is
`Crystalline.levelQuotientMap`, and `p` is killed by `p ^ e` there. -/
noncomputable def levelThickeningOfClosedFibre {k : ℕ}
    (hk : IsPAdicLevel A.ideal A.dividedPowers p k) :
    DividedPowerThickening.{u, u, u} (closedFibreSituation p A hp) where
  ring := dpQuotientLevelRing p A k hk
  fromBase := levelProj p A k hk
  prime_nilpotent := isNilpotent_prime_levelRing p A k hk
  toQuotient := levelQuotientMap p A k hk
  commutes := by
    refine RingHom.ext fun x => ?_
    change Ideal.Quotient.mk (dpQuotientLevelRing p A k hk).ideal
        (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := ↥A) p ^ k) x) =
      levelQuotientMap p A k hk (Ideal.Quotient.mk A.ideal x)
    rw [levelQuotientMap_mk]

/-- **A finite divided power level of the base is an object of the little crystalline category
`Cris(A/I / A)`**: passing to a level does not change the quotient by the divided power ideal. -/
theorem isCrystalline_levelThickeningOfClosedFibre {k : ℕ}
    (hk : IsPAdicLevel A.ideal A.dividedPowers p k) :
    DividedPowerThickening.IsCrystalline (levelThickeningOfClosedFibre p A hp hk) :=
  levelQuotientMap_bijective p A k hk

/-- **In the level `A/p^eA` no power of `p` below the `e`-th vanishes**, when `p` is a nonzero
nonunit of a ring `A` without zero divisors. -/
theorem pow_natCast_ne_zero_levelThickeningOfClosedFibre [NoZeroDivisors (↥A)]
    (h0 : (p : ↥A) ≠ 0) (hu : ¬ IsUnit (p : ↥A)) {k N : ℕ}
    (hk : IsPAdicLevel A.ideal A.dividedPowers p k) (hNk : N < k) :
    ((closedFibreSituation p A hp).p : (levelThickeningOfClosedFibre p A hp hk).ring) ^ N ≠ 0 := by
  change (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := ↥A) p ^ k) (p : ↥A)) ^ N ≠ 0
  rw [← map_pow, Ne, Ideal.Quotient.eq_zero_iff_mem]
  exact pow_natCast_notMem_pAdicIdeal_pow h0 hu hNk

end ClosedFibre

/-! ### The base `ℤ_(p)` -/

section IntegersAtPrime

variable (p : ℕ) [Fact p.Prime]

/-- The ideal `(p) ⊆ ℤ` is prime. -/
private instance isPrime_span_natCast_int :
    (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
  (Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr (Fact.out : p.Prime).ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))

/-- `ℤ_(p)` is a domain, being a localization of `ℤ` at a multiplicative set of nonzerodivisors. -/
private theorem isDomain_integersAtPrime : IsDomain (DividedPowers.IntegersAtPrime p) :=
  IsLocalization.isDomain_localization
    (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span ({(p : ℤ)} : Set ℤ)))

/-- `p` is nonzero in `ℤ_(p)`, the localization map out of `ℤ` being injective. -/
private theorem natCast_ne_zero_integersAtPrime :
    (p : DividedPowers.IntegersAtPrime p) ≠ 0 := by
  have := charZero_of_injective_algebraMap
    (IsLocalization.injective (DividedPowers.IntegersAtPrime p)
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span ({(p : ℤ)} : Set ℤ))))
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- `p` is not a unit of `ℤ_(p)`: it lies in the prime ideal that was inverted around. -/
private theorem not_isUnit_natCast_integersAtPrime :
    ¬ IsUnit (p : DividedPowers.IntegersAtPrime p) := by
  rw [← map_natCast (algebraMap ℤ (DividedPowers.IntegersAtPrime p)) p,
    IsLocalization.AtPrime.isUnit_to_map_iff (DividedPowers.IntegersAtPrime p)
      (Ideal.span ({(p : ℤ)} : Set ℤ)) (p : ℤ)]
  exact fun h => h (Ideal.subset_span (Set.mem_singleton _))

/-- **Stacks Project, Tag 07GN.**  The divided powers `γₙ(p a) = (p^n / n!) a^n` on the ideal
`(p) ⊆ ℤ_(p)`. -/
noncomputable def integersAtPrimeDividedPowers :
    DividedPowers (Ideal.span {(p : DividedPowers.IntegersAtPrime p)}) :=
  (DividedPowers.exists_dividedPowers_span_natCast
    (A := DividedPowers.IntegersAtPrime p) p).choose_spec.choose

/-- The divided power ring `(A, I, γ) = (ℤ_(p), (p), γ)`. -/
noncomputable abbrev integersAtPrimeBase : DividedPowerRing.{0} :=
  .of (DividedPowers.IntegersAtPrime p) (Ideal.span {(p : DividedPowers.IntegersAtPrime p)})
    (integersAtPrimeDividedPowers p)

/-- `p` vanishes, hence is nilpotent, in the closed fibre `ℤ_(p)/(p) = 𝐅_p`. -/
theorem isNilpotent_prime_integersAtPrimeBase :
    IsNilpotent (Ideal.Quotient.mk (integersAtPrimeBase p).ideal
      (p : integersAtPrimeBase p)) :=
  ⟨1, by
    rw [pow_one, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)⟩

/-- **The affine crystalline situation `(p, (ℤ_(p), (p), γ), 𝐅_p)`.** -/
noncomputable def integersAtPrimeSituation : AffineCrystallineSituation.{0, 0} :=
  closedFibreSituation p (integersAtPrimeBase p) (isNilpotent_prime_integersAtPrimeBase p)

/-- An exponent beyond which every exponent is a `p`-adic level for `(ℤ_(p), (p), γ)`,
[Stacks, Tag 07MV]. -/
noncomputable def integersAtPrimeLevelBound : ℕ :=
  (exists_forall_isPAdicLevel (integersAtPrimeBase p).ideal
    (integersAtPrimeBase p).dividedPowers p (isNilpotent_prime_integersAtPrimeBase p)).choose

/-- Every exponent `e ≥ integersAtPrimeLevelBound p` is a `p`-adic level for
`(ℤ_(p), (p), γ)`. -/
theorem isPAdicLevel_integersAtPrimeBase {e : ℕ} (he : integersAtPrimeLevelBound p ≤ e) :
    IsPAdicLevel (integersAtPrimeBase p).ideal (integersAtPrimeBase p).dividedPowers p e :=
  (exists_forall_isPAdicLevel (integersAtPrimeBase p).ideal
    (integersAtPrimeBase p).dividedPowers p (isNilpotent_prime_integersAtPrimeBase p)).choose_spec
      e he

/-! ### The family of levels, and the failure of its product -/

/-- **The family `n ↦ ℤ_(p)/p^{N + n + 1}ℤ_(p)` of divided power thickenings of `𝐅_p`**, with `N`
the level bound of the base.  The nilpotence order of `p` on the `n`-th member is `N + n + 1`, so
the orders are unbounded along the family. -/
noncomputable def unboundedLevelFamily (n : ℕ) :
    DividedPowerThickening.{0, 0, 0} (integersAtPrimeSituation p) :=
  levelThickeningOfClosedFibre p (integersAtPrimeBase p)
    (isNilpotent_prime_integersAtPrimeBase p)
    (isPAdicLevel_integersAtPrimeBase p (Nat.le_add_right _ (n + 1)))

/-- Each member of the family is an object of the little crystalline category
`Cris(𝐅_p/ℤ_(p))`. -/
theorem isCrystalline_unboundedLevelFamily (n : ℕ) :
    DividedPowerThickening.IsCrystalline (unboundedLevelFamily p n) :=
  isCrystalline_levelThickeningOfClosedFibre p (integersAtPrimeBase p) _ _

/-- **In the `n`-th member of the family no power of `p` below the exponent `N + n + 1` of its
level vanishes**, `p` being a nonzero nonunit of the domain `ℤ_(p)`. -/
theorem pow_natCast_ne_zero_unboundedLevelFamily {N n : ℕ}
    (hN : N < integersAtPrimeLevelBound p + (n + 1)) :
    ((integersAtPrimeSituation p).p : (unboundedLevelFamily p n).ring) ^ N ≠ 0 := by
  let := isDomain_integersAtPrime p
  exact pow_natCast_ne_zero_levelThickeningOfClosedFibre p (integersAtPrimeBase p) _
    (natCast_ne_zero_integersAtPrime p) (not_isUnit_natCast_integersAtPrime p) _ hN

/-- The members of the family are not the zero thickening: `1 = p ^ 0` is nonzero in each of
them, so each `ℤ_(p)/p^{N + n + 1}ℤ_(p)` is a nonzero ring. -/
theorem nontrivial_unboundedLevelFamily (n : ℕ) :
    Nontrivial ↥(unboundedLevelFamily p n).ring :=
  ⟨⟨1, 0, by
    simpa using pow_natCast_ne_zero_unboundedLevelFamily p (N := 0) (n := n) (by omega)⟩⟩

/-- **The nilpotence orders of `p` along the family are unbounded**: whatever `N`, the `N`-th
member is `ℤ_(p)/p^{·}ℤ_(p)` with an exponent exceeding `N`, so `p ^ N` does not vanish in it. -/
theorem exists_pow_natCast_ne_zero_unboundedLevelFamily (N : ℕ) :
    ∃ n, ((integersAtPrimeSituation p).p : (unboundedLevelFamily p n).ring) ^ N ≠ 0 :=
  ⟨N, pow_natCast_ne_zero_unboundedLevelFamily p (by omega)⟩

/-- **The family of finite levels of `ℤ_(p)` has no product in `CRIS(𝐅_p/ℤ_(p))`.**  This
inhabits the hypothesis of
`Crystalline.DividedPowerThickening.not_hasProduct_of_forall_exists_pow_natCast_ne_zero`: the
nilpotence orders of `p` along the family are unbounded, and that is a genuine obstruction to
the existence of the product, which is the infinite-products caveat of [Stacks, Tag 07HN]. -/
theorem not_hasProduct_unboundedLevelFamily : ¬ HasProduct (unboundedLevelFamily p) :=
  DividedPowerThickening.not_hasProduct_of_forall_exists_pow_natCast_ne_zero _
    (exists_pow_natCast_ne_zero_unboundedLevelFamily p)

end IntegersAtPrime

end Crystalline

end
