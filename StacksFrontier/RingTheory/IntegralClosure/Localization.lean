module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.Integral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Integrality is detected on the localizations at maximal ideals

Let `φ : R → S` be a homomorphism of commutative rings, and let `p ⊆ R` be a prime
ideal.

* `R_p` denotes the localization of `R` at the multiplicative subset `R \ p`, with its
  canonical localization map `R → R_p`.
* `S_p` denotes the localization of the ring `S` at the multiplicative subset
  `φ(R \ p) ⊆ S` (the image under `φ` of the complement of `p`). Equivalently,
  `S_p ≅ S ⊗_R R_p`. There is a canonical localization map `S → S_p`, and these maps
  assemble into a commutative square

      R  --φ-->  S
      |          |
      v          v
      R_p --φ_p--> S_p

  making `S_p` an `R_p`-algebra via the induced ring map `φ_p : R_p → S_p`.
* Given a ring map `A → B`, an element `b ∈ B` is *integral over `A`* if there is a
  monic polynomial `f ∈ A[X]` with `f(b) = 0` in `B`.

This is Stacks Tag 034K, in the sharper form proved here: for a ring map `φ : R → S` and
`x ∈ S`, writing `x_p ∈ S_p` for the image of `x` under `S → S_p`, the following are
equivalent.

1. `x` is integral over `R`;
2. for every maximal ideal `p ⊆ R`, the element `x_p ∈ S_p` is integral over `R_p`.

Only the maximal ideals are needed in (2). The tag's own formulation, with `p` ranging
over all primes of `R`, is recorded below as `isIntegral_iff_forall_isPrime`.

## Main results

* `isIntegral_iff_isIntegral_localization_atPrime`: the equivalence (1) ↔ (2).
* `isIntegral_iff_forall_isPrime`: the same equivalence with `p` ranging over every prime
  ideal of `R`, which is how Stacks Tag 034K states it.
* `localization_square_commutes`: the square above commutes, which is what makes
  `S_p` an `R_p`-algebra compatibly with `φ`.

## Implementation notes

Direction (1) ⇒ (2) is the easy one: integrality is preserved under localization and
base change. Direction (2) ⇒ (1) carries the content, and rests on integrality being
a local property on `Spec R` together with quasi-compactness — concretely, on
membership in the `R`-submodule `integralClosure R S` being local at the maximal
ideals (`Submodule.mem_of_localization_maximal`).

Note the convention on multiplicative sets: `S_p` is the localization of `S` at the
multiplicatively closed set `φ(R \ p)`, *not* a localization at a prime of `S`. This
is the standard meaning of the stalk `S_p`, consistent with `S_p ≅ S ⊗_R R_p`.
-/

@[expose] public section

/-- `R_p`, the localization of `R` at the prime `p`, i.e. at the multiplicative set
`R \ p = p.primeCompl`. It carries the canonical `R`-algebra structure given by the
localization map. -/
@[ega "0 1.2.3", ega "0 19.8.3"]
abbrev Rloc (R : Type*) [CommRing R] (p : Ideal R) [p.IsPrime] : Type _ :=
  Localization p.primeCompl

/-- `S_p`, the localization of `S` at the multiplicative set `φ(R \ p)`, where
`φ = algebraMap R S`. The submonoid `Algebra.algebraMapSubmonoid S p.primeCompl` is by
definition the image `(p.primeCompl).map (algebraMap R S)`; see
`algebraMapSubmonoid_eq_image`. -/
abbrev Sloc (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    Type _ :=
  Localization (Algebra.algebraMapSubmonoid S p.primeCompl)

/-- The multiplicative set used to build `S_p` is exactly the image `φ(R \ p)` of the
complement of `p` under `φ = algebraMap R S`. -/
theorem algebraMapSubmonoid_eq_image (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    Algebra.algebraMapSubmonoid S p.primeCompl
      = (p.primeCompl).map (algebraMap R S) := rfl

/-- The localization square commutes: `R → R_p → S_p` equals `R → S → S_p`. Both
composites are `algebraMap R S_p`, so `S_p` is an `R_p`-algebra compatibly with `φ`. -/
@[ega "0 1.5.6" "special case"]
theorem localization_square_commutes (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] :
    (algebraMap (Rloc R p) (Sloc R S p)).comp (algebraMap R (Rloc R p))
      = (algebraMap S (Sloc R S p)).comp (algebraMap R S) := by
  rw [← IsScalarTower.algebraMap_eq R (Rloc R p) (Sloc R S p),
      ← IsScalarTower.algebraMap_eq R S (Sloc R S p)]

/-- Clearing denominators: if the image of `y ∈ S` in the localization `S_p` is
integral over `R`, then some multiple `t • y` with `t ∈ R \ p` is integral over `R`.

An integral relation for `y_p` over `R` pulls back to a relation `t · f(y) = 0` in `S`
for some `t ∈ R \ p`, and `Polynomial.scaleRoots` turns that into a *monic* relation
for `t • y` over `R`. This is the key step of the substantive direction of
`isIntegral_iff_isIntegral_localization_atPrime`. -/
private theorem exists_multiple_isIntegral_of_image
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
    (y : S) (hy : IsIntegral R (algebraMap S (Sloc R S p) y)) :
    ∃ t ∈ p.primeCompl, IsIntegral R (t • y) := by
  classical
  obtain ⟨q, hqmonic, hqeval⟩ := hy
  -- Transport the integral relation from `S_p` down to `S`.
  rw [← Polynomial.aeval_def, Polynomial.aeval_algebraMap_apply,
    IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid S p.primeCompl)] at hqeval
  obtain ⟨m, hm⟩ := hqeval
  obtain ⟨t, ht, hteq⟩ := m.property
  refine ⟨t, ht, ?_⟩
  have hm' : algebraMap R S t * (Polynomial.aeval y) q = 0 := by rwa [hteq]
  have hsmul : t • y = algebraMap R S t * y := Algebra.smul_def t y
  rcases Nat.eq_zero_or_pos q.natDegree with hd | hd
  · -- Degenerate case `deg q = 0`: then `q = 1`, so `φ(t) = 0` and `t • y = 0`.
    rw [Polynomial.eq_one_of_monic_natDegree_zero hqmonic hd, map_one, mul_one] at hm'
    rw [hsmul, hm', zero_mul]
    exact isIntegral_zero
  · -- Main case `deg q ≥ 1`: `scaleRoots` produces a monic relation for `t • y`.
    rw [hsmul]
    refine ⟨q.scaleRoots t, by rwa [Polynomial.monic_scaleRoots_iff], ?_⟩
    have hpow : algebraMap R S t ^ q.natDegree
        = algebraMap R S t ^ (q.natDegree - 1) * algebraMap R S t := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    rw [Polynomial.scaleRoots_eval₂_mul (algebraMap R S) y t (p := q), ← Polynomial.aeval_def,
      hpow, mul_assoc, hm', mul_zero]

/-- **Stacks Tag 034K.** Let `φ : R → S` be a ring map and `x ∈ S`. Then `x` is integral
over `R` if and only if, for every maximal ideal `p ⊆ R`, the image `x_p` of `x` in `S_p`
is integral over `R_p` (where `R_p`, `S_p` are the localizations at `p` as above, and `S_p`
is regarded as an `R_p`-algebra via the induced map `φ_p : R_p → S_p`). Only the maximal
ideals are needed; for the all-primes equivalence as the tag states it, which this
implies, see `isIntegral_iff_forall_isPrime`. -/
@[stacks 034K]
theorem isIntegral_iff_isIntegral_localization_atPrime
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (x : S) :
    IsIntegral R x ↔
      ∀ (p : Ideal R) [p.IsMaximal], IsIntegral (Localization.AtPrime p)
        (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) x) := by
  refine ⟨fun hx p _ ↦ hx.algebraMap.tower_top, fun h ↦ ?_⟩
  -- For each maximal ideal `P`, some multiple `t • x` (with `t ∈ R \ P`) is integral.
  have hloc : ∀ (P : Ideal R) [P.IsMaximal], ∃ s ∈ P.primeCompl, IsIntegral R (s • x) := by
    intro P _
    obtain ⟨m, hmint⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization P.primeCompl _ (h P)
    -- Identify `m • x_P` with the image of `m • x ∈ S`.
    have hmx : (m : R) • algebraMap S (Sloc R S P) x
        = algebraMap S (Sloc R S P) ((m : R) • x) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    rw [Submonoid.smul_def, hmx] at hmint
    obtain ⟨t, ht, hint⟩ := exists_multiple_isIntegral_of_image R S P ((m : R) • x) hmint
    exact ⟨t * m, P.primeCompl.mul_mem ht m.property, by rwa [mul_smul]⟩
  -- The integral closure is an `R`-submodule; use local-global membership.
  rw [← mem_integralClosure_iff, ← Subalgebra.mem_toSubmodule]
  refine Submodule.mem_of_localization_maximal (fun P _ ↦ Sloc R S P)
    (fun P _ ↦ (IsScalarTower.toAlgHom R S (Sloc R S P)).toLinearMap) x _ fun P _ ↦ ?_
  obtain ⟨t, ht, hint⟩ := hloc P
  rw [Submodule.mem_localized₀]
  refine ⟨t • x, by rwa [Subalgebra.mem_toSubmodule, mem_integralClosure_iff], ⟨t, ht⟩, ?_⟩
  rw [← Submonoid.mk_smul t ht x, IsLocalizedModule.mk'_cancel]

/-- **Stacks Tag 034K**, as the tag states it. Let `φ : R → S` be a ring map and `x ∈ S`.
Then `x` is integral over `R` if and only if, for *every* prime ideal `p ⊆ R`, the image
`x_p` of `x` in `S_p` is integral over `R_p`.

The substantive direction is `isIntegral_iff_isIntegral_localization_atPrime`, which needs
the hypothesis only at the maximal ideals; integrality at an arbitrary prime follows from
integrality over `R` by base change. -/
@[stacks 034K]
theorem isIntegral_iff_forall_isPrime (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (x : S) :
    IsIntegral R x ↔ ∀ (p : Ideal R) [p.IsPrime], IsIntegral (Localization.AtPrime p)
      (algebraMap S (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) x) :=
  ⟨fun hx _ _ ↦ hx.algebraMap.tower_top,
    fun h ↦ (isIntegral_iff_isIntegral_localization_atPrime R S x).2 fun P _ ↦ h P⟩
