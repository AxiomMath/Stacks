module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Polynomial.Basic
public import StacksFrontier.RingTheory.ArtinRees.SameDenominatorTransfer

/-!
# The denominator criterion passes to a localization of the pair

Let `Q` and `Q'` be two `D`-algebras presented by one `D`-algebra `A`, as in
`Stacks.ArtinRees.SameDenominator.ofComp`, and let `G`, `G'` be two elements of `A` congruent
modulo `m` — in Stacks 0CAY the specialisations along `σ` and along `σ'` of one polynomial over
`C`. This file shows that the denominator criterion for `(A, Q, Q')` implies it for the
one-variable polynomial presentation of the pair of localizations `Q[1/G]`, `Q'[1/G']`.

That is the step the basis-indexed assembly of Stacks 0CAY needs and that no Artin-Rees argument
supplies: the affine comparison produces a bound depending on the presentation, so it can be
invoked at only finitely many charts, whereas
`Stacks.Conormal.CommonChartAssociatedGradedEquiv.isBasis` asks for the comparison at charts
arbitrarily small. Shrinking a chart to a basic open localizes the two chart rings at two elements
which are one `C`-rational function specialised along `σ` and along `σ'`, and the criterion
survives that.

The mechanism is this. Membership of the image of `y` in the ideal `m^(n+1)` generates in the
localization is, by `Stacks.ArtinRees.mem_map_pow_iff_exists_pow_mul`, the existence of some `l`
with `G^l y` in `m^(n+1)`; and an element of `m^n` in the presentation of the localization is,
after clearing denominators, `G^(-d)` times an element `v` of `m^n A`. So both sides of the
criterion become statements about elements `G^l v` of `m^n A`, where the criterion for `A`
applies — and the two clearings, one along `σ` and one along `σ'`, differ by an element of
`m^(n+1) A`, which the denominator cannot see.

## Main results

* `Stacks.ArtinRees.mem_map_pow_iff_exists_pow_mul`: membership in the extension of an ideal to a
  localization away from `g` is divisibility by a power of `g` into that ideal.
* `Stacks.ArtinRees.SameDenominator.ofAwayData`: **the criterion passes to a presentation of the
  pair of localizations**, from the data of a simultaneous denominator-clearing for the elements
  of `m^n`.
* `Stacks.ArtinRees.awayPolyHom`: the one-variable polynomial presentation of a localization away
  from an element, `Stacks.ArtinRees.surjective_awayPolyHom`.
* `Stacks.ArtinRees.SameDenominator.ofAway`: **the criterion for `A` implies the criterion for the
  one-variable polynomial presentations of `Q[1/G]` and `Q'[1/G']`.**

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.ArtinRees

variable {D : Type u} [CommRing D]

/-! ### Elementary ideal arithmetic -/

section Elementary

variable {A : Type*} [CommRing A]

/-- Two elements congruent modulo an ideal have congruent powers. -/
theorem sub_pow_mem (I : Ideal A) {a b : A} (h : a - b ∈ I) (l : ℕ) : a ^ l - b ^ l ∈ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_pow, Ideal.Quotient.eq.2 h, sub_self]

/-- Membership in `I ⊔ J` depends on the element only modulo `I`. -/
theorem mem_sup_iff_of_sub_mem {I J : Ideal A} {a b : A} (h : a - b ∈ I) :
    a ∈ I ⊔ J ↔ b ∈ I ⊔ J :=
  ⟨fun ha => by simpa using Ideal.sub_mem _ ha (Ideal.mem_sup_left h),
    fun hb => by simpa using Ideal.add_mem _ hb (Ideal.mem_sup_left h)⟩

end Elementary

/-! ### Membership in an ideal extended to a localization -/

/-- **Membership in the extension of an ideal to a localization away from `g`.** The image of `y`
lies in the ideal `K` generates exactly when some power of `g` carries `y` into `K`. -/
theorem mem_map_pow_iff_exists_pow_mul {Q QL : Type*} [CommRing Q] [CommRing QL] [Algebra Q QL]
    (g : Q) [IsLocalization.Away g QL] (K : Ideal Q) (y : Q) :
    algebraMap Q QL y ∈ K.map (algebraMap Q QL) ↔ ∃ l : ℕ, g ^ l * y ∈ K := by
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers g)]
  refine ⟨?_, fun ⟨l, h⟩ => ⟨g ^ l, ⟨l, rfl⟩, h⟩⟩
  rintro ⟨_, ⟨l, rfl⟩, h⟩
  exact ⟨l, h⟩

/-- The ideal `m^n` generates in a tower `D → Q → QL` is the extension of the ideal it generates
in `Q`. -/
theorem map_pow_algebraMap_tower {Q QL : Type*} [CommRing Q] [CommRing QL] [Algebra D Q]
    [Algebra D QL] [Algebra Q QL] [IsScalarTower D Q QL] (m : Ideal D) (n : ℕ) :
    (m ^ n).map (algebraMap D QL) = ((m ^ n).map (algebraMap D Q)).map (algebraMap Q QL) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-! ### Transporting a localization along a pair of ring isomorphisms -/

/-- **A localization transported along a pair of ring isomorphisms is a localization.** If
`S` is the localization of `R` at `M` and `eR : R ≃+* R'`, `eS : S ≃+* S'` carry the structure map
of `S` to the structure map of `S'`, then `S'` is the localization of `R'` at the image of `M`.

Stated here because the localization that shrinking a chart produces is a localization of the
*base change* `B ⊗_C D`, whereas the ambient the comparison is stated over is the quotient of a
polynomial ring; the two are identified by Stacks 0CAZ, and this moves the localization across
that identification. -/
theorem isLocalization_of_ringEquiv {R R' S S' : Type*} [CommRing R] [CommRing R'] [CommRing S]
    [CommRing S'] [Algebra R S] [Algebra R' S'] (M : Submonoid R) [IsLocalization M S]
    (eR : R ≃+* R') (eS : S ≃+* S')
    (h : ∀ x : R, algebraMap R' S' (eR x) = eS (algebraMap R S x)) :
    IsLocalization (M.map (eR : R →+* R')) S' := by
  refine (isLocalization_iff (M.map (eR : R →+* R')) S').2 ⟨?_, ?_, ?_⟩
  · rintro ⟨-, s, hs, rfl⟩
    exact (h s).symm ▸ (IsLocalization.map_units S ⟨s, hs⟩).map (eS : S →+* S')
  · intro z
    obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj M (eS.symm z)
    refine ⟨⟨eR x, ⟨eR s, ⟨s, s.2, rfl⟩⟩⟩, ?_⟩
    change z * algebraMap R' S' (eR s) = algebraMap R' S' (eR x)
    rw [h, h, ← eS.apply_symm_apply z, ← map_mul, hx]
  · intro x y hxy
    have hx : eS (algebraMap R S (eR.symm x)) = eS (algebraMap R S (eR.symm y)) := by
      rw [← h, ← h, eR.apply_symm_apply, eR.apply_symm_apply, hxy]
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) (S := S) (eS.injective hx)
    refine ⟨⟨eR c, ⟨c, c.2, rfl⟩⟩, ?_⟩
    change eR c * x = eR c * y
    rw [← eR.apply_symm_apply x, ← eR.apply_symm_apply y, ← map_mul, ← map_mul, hc]

/-- **Two evaluations of a polynomial ring agreeing modulo an ideal on the variables agree modulo
that ideal.** This is how the pair of comparison maps that
`Stacks.ArtinRees.SameDenominator.ofComp` asks for is verified: the two maps are the evaluations
at the two specialisations of one `C`-rational family, which agree modulo `m` variable by
variable. -/
theorem aeval_sub_aeval_mem {A E : Type*} [CommRing A] [CommRing E] [Algebra A E] {ι : Type*}
    (I : Ideal E) (v v' : ι → E) (hvv' : ∀ i, v i - v' i ∈ I) (x : MvPolynomial ι A) :
    MvPolynomial.aeval v x - MvPolynomial.aeval v' x ∈ I := by
  induction x using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.aeval_C, sub_self] using zero_mem I
  | add x y hx hy =>
      rw [map_add, map_add, add_sub_add_comm]
      exact Ideal.add_mem _ hx hy
  | mul_X x i hx =>
      rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
        show MvPolynomial.aeval v x * v i - MvPolynomial.aeval v' x * v' i =
          (MvPolynomial.aeval v x - MvPolynomial.aeval v' x) * v i +
            MvPolynomial.aeval v' x * (v i - v' i) by ring]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ _ (hvv' i))

/-! ### The criterion passes to a localization -/

/-- Membership of `z` in `m^(n+1) ⊔ ker Pi`, for `z` cleared of denominators as the image of `v`,
is divisibility of `v` by a power of `G` into `m^(n+1) ⊔ ker π`. -/
private theorem mem_sup_ker_iff_exists_pow_mul {A B Q QL : Type*}
    [CommRing A] [CommRing B] [CommRing Q] [CommRing QL]
    [Algebra D A] [Algebra D B] [Algebra D Q] [Algebra D QL]
    [Algebra Q QL] [IsScalarTower D Q QL]
    (m : Ideal D) {π : A →ₐ[D] Q} (hπ : Function.Surjective π) (G : A)
    [IsLocalization.Away (π G) QL] {Pi : B →ₐ[D] QL} (hPi : Function.Surjective Pi)
    (z : B) (v : A) (d : ℕ) (hz : Pi z * algebraMap Q QL (π G) ^ d = algebraMap Q QL (π v))
    (n : ℕ) :
    z ∈ (m.map (algebraMap D B)) ^ (n + 1) ⊔ RingHom.ker (Pi : B →+* QL) ↔
      ∃ l : ℕ, G ^ l * v ∈ (m.map (algebraMap D A)) ^ (n + 1) ⊔ RingHom.ker (π : A →+* Q) := by
  have hunit : IsUnit (algebraMap Q QL (π G)) :=
    IsLocalization.map_units QL (⟨π G, Submonoid.mem_powers _⟩ : Submonoid.powers (π G))
  rw [mem_sup_ker_iff (Pi : B →+* QL) hPi, map_pow_map_algebraMap m Pi (n + 1),
    ← Ideal.unit_mul_mem_iff_mem _ (hunit.pow d), mul_comm,
    show (Pi : B →+* QL) z * algebraMap Q QL (π G) ^ d = _ from hz,
    map_pow_algebraMap_tower (D := D) (Q := Q) (QL := QL) m (n + 1),
    mem_map_pow_iff_exists_pow_mul (π G)]
  refine exists_congr fun l => ?_
  rw [mem_sup_ker_iff (π : A →+* Q) hπ, map_pow_map_algebraMap m π (n + 1)]
  exact Iff.of_eq (congrArg (· ∈ (m ^ (n + 1)).map (algebraMap D Q))
    (by rw [map_mul, map_pow]; rfl))

/-- **The denominator criterion passes to a presentation of the pair of localizations.** The data
`hsat` is a simultaneous denominator-clearing: every element `z` of `m^n B` admits one exponent
`d` and two numerators `v`, `v'` in `m^n A`, congruent modulo `m^(n+1) A`, with `Π z · G^d` the
image of `v` in `Q[1/G]` and `Ρ z · G'^d` the image of `v'` in `Q'[1/G']`.

The single exponent and the congruence are the whole content. Both sides of the criterion at `z`
reduce, by `Stacks.ArtinRees.mem_map_pow_iff_exists_pow_mul`, to the existence of an `l` with
`G^l v`, respectively `G'^l v'`, in the `n+1`-st denominator of `A`; the criterion for `A`
compares those two statements with `G^l v` on both sides, and `G^l v` is congruent to `G'^l v'`
modulo `m^(n+1) A`, which the denominator cannot see. -/
theorem SameDenominator.ofAwayData {A B Q Q' QL QL' : Type*}
    [CommRing A] [CommRing B] [CommRing Q] [CommRing Q'] [CommRing QL] [CommRing QL']
    [Algebra D A] [Algebra D B] [Algebra D Q] [Algebra D Q'] [Algebra D QL] [Algebra D QL']
    [Algebra Q QL] [IsScalarTower D Q QL] [Algebra Q' QL'] [IsScalarTower D Q' QL']
    (m : Ideal D) {π : A →ₐ[D] Q} (hπ : Function.Surjective π)
    {ρ : A →ₐ[D] Q'} (hρ : Function.Surjective ρ) (G G' : A)
    [IsLocalization.Away (π G) QL] [IsLocalization.Away (ρ G') QL']
    {Pi : B →ₐ[D] QL} (hPi : Function.Surjective Pi)
    {Rho : B →ₐ[D] QL'} (hRho : Function.Surjective Rho)
    (hGG' : G - G' ∈ m.map (algebraMap D A))
    (hden : SameDenominator (m.map (algebraMap D A)) (RingHom.ker (π : A →+* Q))
      (RingHom.ker (ρ : A →+* Q')))
    (hsat : ∀ (n : ℕ) (z : B), z ∈ (m.map (algebraMap D B)) ^ n →
      ∃ (d : ℕ) (v v' : A), v ∈ (m.map (algebraMap D A)) ^ n ∧
        v - v' ∈ (m.map (algebraMap D A)) ^ (n + 1) ∧
        Pi z * algebraMap Q QL (π G) ^ d = algebraMap Q QL (π v) ∧
        Rho z * algebraMap Q' QL' (ρ G') ^ d = algebraMap Q' QL' (ρ v')) :
    SameDenominator (m.map (algebraMap D B)) (RingHom.ker (Pi : B →+* QL))
      (RingHom.ker (Rho : B →+* QL')) := by
  intro n z hz
  obtain ⟨d, v, v', hv, hvv', hPiz, hRhoz⟩ := hsat n z hz
  have eL := mem_sup_ker_iff_exists_pow_mul m hπ G hPi z v d hPiz n
  have eR := mem_sup_ker_iff_exists_pow_mul m hρ G' hRho z v' d hRhoz n
  rw [eL, eR]
  refine exists_congr fun l => ?_
  have hcong : G ^ l * v - G' ^ l * v' ∈ (m.map (algebraMap D A)) ^ (n + 1) := by
    have h1 : (G ^ l - G' ^ l) * v ∈ (m.map (algebraMap D A)) ^ (n + 1) := by
      have hm := Ideal.mul_mem_mul (sub_pow_mem (m.map (algebraMap D A)) hGG' l) hv
      rwa [← pow_succ'] at hm
    rw [show G ^ l * v - G' ^ l * v' = (G ^ l - G' ^ l) * v + G' ^ l * (v - v') by ring]
    exact Ideal.add_mem _ h1 (Ideal.mul_mem_left _ _ hvv')
  exact (hden n (G ^ l * v) (Ideal.mul_mem_left _ _ hv)).trans (mem_sup_iff_of_sub_mem hcong)

/-! ### The one-variable polynomial presentation of a localization -/

section PolyHom

variable {A Q QL : Type*} [CommRing A] [CommRing Q] [CommRing QL]
  [Algebra D A] [Algebra D Q] [Algebra D QL] [Algebra Q QL] [IsScalarTower D Q QL]

/-- **The one-variable polynomial presentation of a localization away from an element.** For a
surjection `π : A ↠ Q` of `D`-algebras and `G : A`, the ring `Q[1/π G]` is the quotient of `A[X]`
sending `X` to the inverse of `π G`. -/
def awayPolyHom (π : A →ₐ[D] Q) (G : A) (QL : Type*) [CommRing QL] [Algebra D QL]
    [Algebra Q QL] [IsScalarTower D Q QL] [IsLocalization.Away (π G) QL] :
    Polynomial A →ₐ[D] QL :=
  { Polynomial.eval₂RingHom ((algebraMap Q QL).comp (π : A →+* Q))
      (IsLocalization.Away.invSelf (π G)) with
    commutes' := fun c => by
      change Polynomial.eval₂ ((algebraMap Q QL).comp (π : A →+* Q))
        (IsLocalization.Away.invSelf (π G)) (Polynomial.C (algebraMap D A c)) = _
      rw [Polynomial.eval₂_C]
      change algebraMap Q QL (π (algebraMap D A c)) = _
      rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }

/-- The presentation sends a constant polynomial `C a` to the image of `π a` in `Q[1/π G]`. -/
@[simp]
theorem awayPolyHom_C (π : A →ₐ[D] Q) (G : A) [IsLocalization.Away (π G) QL] (a : A) :
    awayPolyHom π G QL (Polynomial.C a) = algebraMap Q QL (π a) :=
  Polynomial.eval₂_C _ _

/-- The presentation sends the variable `X` to the inverse of `π G` in `Q[1/π G]`. -/
@[simp]
theorem awayPolyHom_X (π : A →ₐ[D] Q) (G : A) [IsLocalization.Away (π G) QL] :
    awayPolyHom π G QL Polynomial.X = IsLocalization.Away.invSelf (π G) :=
  Polynomial.eval₂_X _ _

/-- The presentation evaluates a polynomial as the sum of its coefficients against the powers of
the inverse of `π G`. -/
theorem awayPolyHom_eq_sum_range (π : A →ₐ[D] Q) (G : A) [IsLocalization.Away (π G) QL]
    (z : Polynomial A) :
    awayPolyHom π G QL z = ∑ i ∈ Finset.range (z.natDegree + 1),
      algebraMap Q QL (π (z.coeff i)) * IsLocalization.Away.invSelf (π G) ^ i :=
  Polynomial.eval₂_eq_sum_range _ _

/-- **The one-variable polynomial presentation of a localization is surjective**, when the
presentation of the ring being localized is: every element of `Q[1/π G]` is a quotient of an
element of `Q` by a power of `π G`. -/
theorem surjective_awayPolyHom {π : A →ₐ[D] Q} (hπ : Function.Surjective π) (G : A)
    [IsLocalization.Away (π G) QL] : Function.Surjective (awayPolyHom π G QL) := by
  intro y
  obtain ⟨xs, hxs⟩ := IsLocalization.surj (Submonoid.powers (π G)) y
  obtain ⟨k, hk⟩ := xs.2.2
  obtain ⟨a, ha⟩ := hπ xs.1
  refine ⟨Polynomial.C a * Polynomial.X ^ k, ?_⟩
  rw [map_mul, map_pow, awayPolyHom_C, awayPolyHom_X, ha, ← hxs, ← hk, map_pow, mul_assoc,
    ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- **Clearing the denominators of a polynomial at once.** Multiplying the value of a polynomial
`z` of degree `d` by the `d`-th power of the inverted element gives the image of the honest
element `∑_k z_k G^(d-k)` of `A`. -/
theorem awayPolyHom_mul_pow_natDegree (π : A →ₐ[D] Q) (G : A) [IsLocalization.Away (π G) QL]
    (z : Polynomial A) :
    awayPolyHom π G QL z * algebraMap Q QL (π G) ^ z.natDegree =
      algebraMap Q QL (π (∑ i ∈ Finset.range (z.natDegree + 1),
        z.coeff i * G ^ (z.natDegree - i))) := by
  classical
  rw [awayPolyHom_eq_sum_range, Finset.sum_mul, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ z.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hpow : algebraMap Q QL (π G) ^ z.natDegree =
      algebraMap Q QL (π G) ^ i * algebraMap Q QL (π G) ^ (z.natDegree - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hid]
  have hkey : IsLocalization.Away.invSelf (S := QL) (π G) ^ i *
      algebraMap Q QL (π G) ^ z.natDegree =
        algebraMap Q QL (π G) ^ (z.natDegree - i) := by
    rw [hpow, ← mul_assoc, ← mul_pow,
      mul_comm (IsLocalization.Away.invSelf (S := QL) (π G)) (algebraMap Q QL (π G)),
      IsLocalization.Away.mul_invSelf, one_pow, one_mul]
  simp only [map_mul, map_pow]
  rw [mul_assoc, hkey]

end PolyHom

/-- **The denominator-clearing data for the one-variable polynomial presentations.**
For `z ∈ m^n A[X]` of degree `d`, the numerators are `∑_k z_k G^(d-k)` and `∑_k z_k G'^(d-k)`:
both lie in `m^n A`, they are congruent modulo `m^(n+1) A` because `G` and `G'` are congruent
modulo `m A`, and `Stacks.ArtinRees.awayPolyHom_mul_pow_natDegree` clears all the denominators at
once with the single exponent `d`. -/
theorem sat_awayPolyHom {A Q Q' QL QL' : Type*}
    [CommRing A] [CommRing Q] [CommRing Q'] [CommRing QL] [CommRing QL']
    [Algebra D A] [Algebra D Q] [Algebra D Q'] [Algebra D QL] [Algebra D QL']
    [Algebra Q QL] [IsScalarTower D Q QL] [Algebra Q' QL'] [IsScalarTower D Q' QL']
    (m : Ideal D) (π : A →ₐ[D] Q) (ρ : A →ₐ[D] Q') (G G' : A)
    [IsLocalization.Away (π G) QL] [IsLocalization.Away (ρ G') QL']
    (hGG' : G - G' ∈ m.map (algebraMap D A)) (n : ℕ) (z : Polynomial A)
    (hz : z ∈ (m.map (algebraMap D (Polynomial A))) ^ n) :
    ∃ (d : ℕ) (v v' : A), v ∈ (m.map (algebraMap D A)) ^ n ∧
      v - v' ∈ (m.map (algebraMap D A)) ^ (n + 1) ∧
      awayPolyHom π G QL z * algebraMap Q QL (π G) ^ d = algebraMap Q QL (π v) ∧
      awayPolyHom ρ G' QL' z * algebraMap Q' QL' (ρ G') ^ d = algebraMap Q' QL' (ρ v') := by
  classical
  have hkey : (m.map (algebraMap D (Polynomial A))) ^ n =
      ((m.map (algebraMap D A)) ^ n).map (Polynomial.C : A →+* Polynomial A) := by
    rw [← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map, ← Polynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]
  have hcoeff : ∀ k, z.coeff k ∈ (m.map (algebraMap D A)) ^ n :=
    Ideal.mem_map_C_iff.1 (hkey ▸ hz)
  refine ⟨z.natDegree, ∑ i ∈ Finset.range (z.natDegree + 1), z.coeff i * G ^ (z.natDegree - i),
    ∑ i ∈ Finset.range (z.natDegree + 1), z.coeff i * G' ^ (z.natDegree - i), ?_, ?_,
    awayPolyHom_mul_pow_natDegree π G z, awayPolyHom_mul_pow_natDegree ρ G' z⟩
  · exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hcoeff i)
  · rw [← Finset.sum_sub_distrib, pow_succ]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [← mul_sub]
    exact Ideal.mul_mem_mul (hcoeff i) (sub_pow_mem _ hGG' _)

/-- **The denominator criterion for `A` implies the criterion for the one-variable polynomial
presentations of the two localizations.** This is the locality of the identity-induced comparison
of Stacks 0CAY in its usable form: restricting a chart to a basic open inverts one `C`-rational
function, specialised along `σ` on one side and along `σ'` on the other, and the comparison
survives. -/
theorem SameDenominator.ofAway {A Q Q' QL QL' : Type*}
    [CommRing A] [CommRing Q] [CommRing Q'] [CommRing QL] [CommRing QL']
    [Algebra D A] [Algebra D Q] [Algebra D Q'] [Algebra D QL] [Algebra D QL']
    [Algebra Q QL] [IsScalarTower D Q QL] [Algebra Q' QL'] [IsScalarTower D Q' QL']
    (m : Ideal D) {π : A →ₐ[D] Q} (hπ : Function.Surjective π)
    {ρ : A →ₐ[D] Q'} (hρ : Function.Surjective ρ) (G G' : A)
    [IsLocalization.Away (π G) QL] [IsLocalization.Away (ρ G') QL']
    (hGG' : G - G' ∈ m.map (algebraMap D A))
    (hden : SameDenominator (m.map (algebraMap D A)) (RingHom.ker (π : A →+* Q))
      (RingHom.ker (ρ : A →+* Q'))) :
    SameDenominator (m.map (algebraMap D (Polynomial A)))
      (RingHom.ker (awayPolyHom π G QL : Polynomial A →+* QL))
      (RingHom.ker (awayPolyHom ρ G' QL' : Polynomial A →+* QL')) :=
  SameDenominator.ofAwayData m hπ hρ G G' (surjective_awayPolyHom hπ G)
    (surjective_awayPolyHom hρ G') hGG' hden
    (sat_awayPolyHom m π ρ G G' hGG')

end Stacks.ArtinRees

end
