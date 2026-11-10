module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.BasicOpenVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Stalks
public import StacksFrontier.AlgebraicGeometry.Meromorphic.TotalQuotientSheafStalks

/-!
# The sheaf of meromorphic functions on a locally Noetherian scheme

On a locally Noetherian scheme the sheaf `K_X` of meromorphic functions, the sheafification of
the presheaf of total quotient rings, is already the total quotient ring on affine opens: for
`U` affine the ring `K_X(U)` is the localization of `Γ(X, U)` at its nonzerodivisors. The same
description holds at every point for the stalks.

## Main results

* `AlgebraicGeometry.stalk_totalQuotientSheaf_isFractionRing_of_isLocallyNoetherian`: the stalk
  of the sheaf of meromorphic functions is the total quotient ring of the local ring.
* `AlgebraicGeometry.isLocalization_totalQuotientSheaf_obj_of_isLocallyNoetherian`: on an
  affine open the sections of the sheaf of meromorphic functions form the total quotient ring
  of the ring of regular functions.

## Implementation notes

Sheafification does not change stalks, so the stalk statement is the corresponding statement
for the presheaf transported along the comparison isomorphism.

For the affine statement, the structure map `Γ(X, U) → K_X(U)` is injective over any open and
carries nonzerodivisors to units because that already happens in the presheaf of total
quotient rings. What remains is that every section is a fraction, which is the Stacks
argument: the ideal of denominators of a section `t` of `K_X` over `U` lies in no associated
prime of `Γ(X, U)`, because near the point named by such a prime `t` is a fraction, and a power
of a suitable regular function propagates that relation over all of `U` by Stacks 08I7. Prime
avoidance over the finitely many associated primes then produces a nonzerodivisor denominator.

The purely algebraic steps are isolated as statements about ring homomorphisms, so that the
proof over a scheme only applies them.

## References

* [Stacks Project, Tag 02OV](https://stacks.math.columbia.edu/tag/02OV)
* [Stacks Project, Tag 08I7](https://stacks.math.columbia.edu/tag/08I7)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry

section Algebraic

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The denominators of an element `t` of a commutative ring `S` over a ring homomorphism
`f : R →+* S`: those `c` with `f c * t` in the image of `f`. -/
private def denominators (f : R →+* S) (t : S) : Ideal R where
  carrier := {c | ∃ s : R, f c * t = f s}
  add_mem' := by
    rintro a b ⟨sa, ha⟩ ⟨sb, hb⟩
    exact ⟨sa + sb, by rw [map_add, add_mul, ha, hb, map_add]⟩
  zero_mem' := ⟨0, by rw [map_zero, zero_mul]⟩
  smul_mem' := by
    rintro r a ⟨sa, ha⟩
    exact ⟨r * sa, by rw [smul_eq_mul, map_mul, mul_assoc, ha, map_mul]⟩

/-- A power of `w` annihilating `f γ * t - f δ` makes that power of `γ` a denominator. -/
private lemma pow_mul_mem_denominators (f : R →+* S) (t : S) {w γ δ : R} (n : ℕ)
    (h : f w ^ n * (f γ * t - f δ) = 0) : w ^ n * γ ∈ denominators f t :=
  ⟨w ^ n * δ, by rwa [map_mul, map_mul, map_pow, mul_assoc, ← sub_eq_zero, ← mul_sub]⟩

/-- Clearing the denominators of a fraction twice over: if `t` is `a' / b'` and both `b'` and
`a'` are themselves fractions over `f`, then `t` has numerator and denominator in the image. -/
private lemma mul_eq_of_isFraction {T : Type*} [CommRing T] (f : R →+* S) (g : S →+* T) (t : T)
    {a' b' : S} {a₁ c₁ d₁ e₁ : R} (hab : t * g b' = g a') (hc : b' * f d₁ = f c₁)
    (ha : a' * f e₁ = f a₁) : g (f (c₁ * e₁)) * t = g (f (a₁ * d₁)) := by
  have h1 : f (c₁ * e₁) = b' * f d₁ * f e₁ := by rw [map_mul, hc]
  have h2 : f (a₁ * d₁) = a' * f e₁ * f d₁ := by rw [map_mul, ha]
  rw [h1, h2]
  simp only [map_mul]
  rw [← hab]
  ring

/-- The numerator produced by clearing denominators twice over is a nonzerodivisor. -/
private lemma isFraction_denominator_mem_nonZeroDivisors (f : R →+* S) {b' : S} (hb' : b' ∈ S⁰)
    {c₁ d₁ e₁ : R} (hc : b' * f d₁ = f c₁) (hd : IsUnit (f d₁)) (he : IsUnit (f e₁)) :
    f (c₁ * e₁) ∈ S⁰ := by
  rw [map_mul, ← hc]
  exact mul_mem (mul_mem hb' hd.mem_nonZeroDivisors) he.mem_nonZeroDivisors

/-- A unit times a nonzerodivisor is a nonzerodivisor, read through a ring homomorphism. -/
private lemma mul_pow_mem_nonZeroDivisors (f : R →+* S) {w : R} (hw : IsUnit (f w)) (n : ℕ)
    {γ : R} (hγ : f γ ∈ S⁰) : f (w ^ n * γ) ∈ S⁰ := by
  rw [map_mul, map_pow]
  exact mul_mem (pow_mem hw.mem_nonZeroDivisors n) hγ

/-- A relation `g u * g t = g v` says exactly that `g` kills `u * t - v`. -/
private lemma map_mul_sub_eq_zero (g : R →+* S) (u v t : R) (h : g u * g t = g v) :
    g (u * t - v) = 0 := by
  rw [map_sub, map_mul, h, sub_self]

/-- An element of a Noetherian ring whose image in the localization at an associated prime is a
nonzerodivisor does not lie in that prime: the prime annihilates an element which stays nonzero
in that localization. -/
theorem notMem_of_algebraMap_mem_nonZeroDivisors [IsNoetherianRing R] {q : Ideal R}
    [q.IsPrime] (hq : q ∈ associatedPrimes R R) [Algebra R S]
    [IsLocalization q.primeCompl S] {c : R} (hc : algebraMap R S c ∈ S⁰) : c ∉ q := by
  obtain ⟨-, y, hy⟩ := isAssociatedPrime_iff.mp hq
  have hmem : ∀ r : R, r ∈ q ↔ r * y = 0 := by
    intro r
    rw [hy, Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
  intro hcq
  have hy0 : algebraMap R S y = 0 :=
    mem_nonZeroDivisors_iff_right.mp hc _ (by
      rw [mul_comm, ← map_mul, (hmem c).mp hcq, map_zero])
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl S y).mp hy0
  exact s.2 ((hmem (s : R)).mpr hs)

/-- An ideal of a Noetherian ring contained in no associated prime contains a nonzerodivisor. -/
private lemma exists_mem_nonZeroDivisors_of_forall_notLe [IsNoetherianRing R] (I : Ideal R)
    (h : ∀ q ∈ associatedPrimes R R, ¬ I ≤ q) : ∃ z ∈ I, z ∈ R⁰ := by
  by_contra hcon
  push Not at hcon
  have hsub : (I : Set R) ⊆ ⋃ i ∈ associatedPrimes R R, ((id i : Ideal R) : Set R) := by
    simp only [id_eq]
    rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors R]
    exact hcon
  obtain ⟨q, hq, hIq⟩ :=
    (I.subset_union_prime_finite (associatedPrimes.finite R R) (f := id) 0 0
      fun _ h _ _ => h.1).1 hsub
  exact h q hq hIq

end Algebraic

/-- At every point of a locally Noetherian scheme the stalk of the sheaf of meromorphic
functions is the total quotient ring of the local ring. -/
@[stacks 02OV "part (1), for the sheaf", ega "IV 21.6.7" "partial"]
theorem stalk_totalQuotientSheaf_isFractionRing_of_isLocallyNoetherian
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    letI : Algebra (X.presheaf.stalk x) (X.totalQuotientSheaf.presheaf.stalk x) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        X.toTotalQuotientSheaf.hom).hom.toAlgebra
    IsFractionRing (X.presheaf.stalk x) (X.totalQuotientSheaf.presheaf.stalk x) := by
  let _ : Algebra (X.presheaf.stalk x) (X.presheaf.totalQuotientPresheaf.stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      X.presheaf.toTotalQuotientPresheaf).hom.toAlgebra
  have hfrac : IsFractionRing (X.presheaf.stalk x)
      (X.presheaf.totalQuotientPresheaf.stalk x) :=
    stalk_totalQuotientPresheaf_isFractionRing_of_isLocallyNoetherian X x
  rw [stalkFunctor_map_toTotalQuotientSheaf_hom X x]
  let _ : Algebra (X.presheaf.stalk x) (X.totalQuotientSheaf.presheaf.stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map X.presheaf.toTotalQuotientPresheaf ≫
      (stalkTotalQuotientSheafIso X x).hom).hom.toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv _
    { (stalkTotalQuotientSheafIso X x).commRingCatIsoToRingEquiv with
      commutes' := fun _ => rfl }

/-- Over an affine open of a locally Noetherian scheme the denominators of a section of the
sheaf of meromorphic functions lie in no associated prime of the ring of regular functions. -/
private lemma denominators_notLe_of_mem_associatedPrimes (X : Scheme.{u})
    [IsLocallyNoetherian X] {U : X.Opens} (hU : IsAffineOpen U)
    (t : X.totalQuotientSheaf.presheaf.obj (op U)) {q : Ideal Γ(X, U)}
    (hqass : q ∈ associatedPrimes Γ(X, U) Γ(X, U)) :
    ¬ denominators (X.toTotalQuotientSheaf.hom.app (op U)).hom t ≤ q := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  intro hIq
  have : q.IsPrime := hqass.isPrime
  obtain ⟨x, hxU, hqx⟩ :
      ∃ (x : X) (hxU : x ∈ U), (hU.primeIdealOf ⟨x, hxU⟩).asIdeal = q := by
    have hmem : hU.fromSpec (⟨q, ‹q.IsPrime›⟩ : PrimeSpectrum Γ(X, U)) ∈ U := by
      change _ ∈ (U : Set X)
      rw [← hU.range_fromSpec]
      exact Set.mem_range_self _
    exact ⟨_, hmem, congrArg PrimeSpectrum.asIdeal
      (hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨_, hmem⟩))⟩
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have : IsLocalization q.primeCompl (X.presheaf.stalk x) :=
    hqx ▸ hU.isLocalization_stalk ⟨x, hxU⟩
  let : Algebra (X.presheaf.stalk x) (X.totalQuotientSheaf.presheaf.stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      X.toTotalQuotientSheaf.hom).hom.toAlgebra
  have : IsFractionRing (X.presheaf.stalk x) (X.totalQuotientSheaf.presheaf.stalk x) :=
    stalk_totalQuotientSheaf_isFractionRing_of_isLocallyNoetherian X x
  have hgerm : ∀ c : Γ(X, U), X.totalQuotientSheaf.presheaf.germ U x hxU
      ((X.toTotalQuotientSheaf.hom.app (op U)).hom c) =
      algebraMap (X.presheaf.stalk x) (X.totalQuotientSheaf.presheaf.stalk x)
        (algebraMap Γ(X, U) (X.presheaf.stalk x) c) :=
    fun c => (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
      X.toTotalQuotientSheaf.hom c).symm
  obtain ⟨⟨a', b'⟩, hab⟩ := IsLocalization.surj (M := (X.presheaf.stalk x)⁰)
    (X.totalQuotientSheaf.presheaf.germ U x hxU t)
  obtain ⟨⟨c₁, d₁⟩, hc₁⟩ :=
    IsLocalization.surj (M := q.primeCompl) (b' : X.presheaf.stalk x)
  obtain ⟨⟨a₁, e₁⟩, ha₁⟩ := IsLocalization.surj (M := q.primeCompl) a'
  have hγ : algebraMap Γ(X, U) (X.presheaf.stalk x) (c₁ * (e₁ : Γ(X, U))) ∈
      (X.presheaf.stalk x)⁰ :=
    isFraction_denominator_mem_nonZeroDivisors _ b'.2 hc₁
      (IsLocalization.map_units (X.presheaf.stalk x) d₁)
      (IsLocalization.map_units (X.presheaf.stalk x) e₁)
  have hgzero : X.totalQuotientSheaf.presheaf.germ U x hxU
      ((X.toTotalQuotientSheaf.hom.app (op U)).hom (c₁ * (e₁ : Γ(X, U))) * t -
        (X.toTotalQuotientSheaf.hom.app (op U)).hom (a₁ * (d₁ : Γ(X, U)))) = 0 :=
    map_mul_sub_eq_zero (X.totalQuotientSheaf.presheaf.germ U x hxU).hom _ _ t
      ((congrArg (fun y => y * X.totalQuotientSheaf.presheaf.germ U x hxU t)
        (hgerm (c₁ * (e₁ : Γ(X, U))))).trans
        ((mul_eq_of_isFraction (algebraMap Γ(X, U) (X.presheaf.stalk x))
          (algebraMap (X.presheaf.stalk x) (X.totalQuotientSheaf.presheaf.stalk x))
          _ hab hc₁ ha₁).trans (hgerm (a₁ * (d₁ : Γ(X, U)))).symm))
  obtain ⟨W, hxW, iWU, iWU', hres⟩ :=
    TopCat.Presheaf.germ_eq X.totalQuotientSheaf.presheaf x hxU hxU _ 0
      (hgzero.trans (map_zero _).symm)
  have hW0 : X.totalQuotientSheaf.presheaf.map iWU.op
      ((X.toTotalQuotientSheaf.hom.app (op U)).hom (c₁ * (e₁ : Γ(X, U))) * t -
        (X.toTotalQuotientSheaf.hom.app (op U)).hom (a₁ * (d₁ : Γ(X, U)))) = 0 :=
    hres.trans (map_zero _)
  obtain ⟨e, heW, hxe⟩ := hU.exists_basicOpen_le (V := W) ⟨x, hxW⟩ hxU
  have hgD : X.totalQuotientSheaf.presheaf.map (homOfLE (X.basicOpen_le e)).op
      ((X.toTotalQuotientSheaf.hom.app (op U)).hom (c₁ * (e₁ : Γ(X, U))) * t -
        (X.toTotalQuotientSheaf.hom.app (op U)).hom (a₁ * (d₁ : Γ(X, U)))) = 0 := by
    refine Eq.trans ?_ ((congrArg (X.totalQuotientSheaf.presheaf.map (homOfLE heW).op)
      hW0).trans (map_zero _))
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl
  obtain ⟨n, hn⟩ := pow_mul_eq_zero_of_res_basicOpen_eq_zero X hU.isCompact e _ hgD
  refine notMem_of_algebraMap_mem_nonZeroDivisors hqass
    (mul_pow_mem_nonZeroDivisors (algebraMap Γ(X, U) (X.presheaf.stalk x))
      ((X.mem_basicOpen' e ⟨x, hxU⟩).1 hxe) n hγ)
    (hIq (pow_mul_mem_denominators (X.toTotalQuotientSheaf.hom.app (op U)).hom t n hn))

/-- **The sheaf of meromorphic functions on an affine open of a locally Noetherian scheme.**
The sections of `K_X` over an affine open `U` form the total quotient ring of `Γ(X, U)`. -/
@[stacks 02OV "part (2)"]
theorem isLocalization_totalQuotientSheaf_obj_of_isLocallyNoetherian
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U) (X.totalQuotientSheaf.presheaf.obj (op U)) :=
      (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
    IsLocalization Γ(X, U)⁰ (X.totalQuotientSheaf.presheaf.obj (op U)) := by
  let : Algebra Γ(X, U) (X.totalQuotientSheaf.presheaf.obj (op U)) :=
    (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : Algebra Γ(X, U) (X.presheaf.totalQuotientPresheaf.obj (op U)) :=
    (X.presheaf.toTotalQuotientPresheaf.app (op U)).hom.toAlgebra
  have : IsLocalization Γ(X, U)⁰ (X.presheaf.totalQuotientPresheaf.obj (op U)) :=
    isLocalization_totalQuotientPresheaf_obj_of_isAffineOpen X U hU
  refine ⟨fun b => ?_, fun t => ?_, fun {a b} hab => ?_⟩
  · exact (IsLocalization.map_units (X.presheaf.totalQuotientPresheaf.obj (op U)) b).map
      ((toSheafify (Opens.grothendieckTopology X)
        X.presheaf.totalQuotientPresheaf).app (op U)).hom
  · obtain ⟨z, ⟨s, hs⟩, hz⟩ := exists_mem_nonZeroDivisors_of_forall_notLe
      (denominators (X.toTotalQuotientSheaf.hom.app (op U)).hom t : Ideal Γ(X, U))
      fun q hq => denominators_notLe_of_mem_associatedPrimes X hU t hq
    exact ⟨(s, ⟨z, hz⟩), by rwa [mul_comm]⟩
  · exact ⟨1, by rw [toTotalQuotientSheaf_app_injective X U hab]⟩

end AlgebraicGeometry
