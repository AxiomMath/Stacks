module

public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Ramification indices in a tower of discrete valuation rings

For a tower `A → B → C` of extensions of discrete valuation rings the ramification index is
multiplicative,

$$e(C/A) = e(B/A)\, e(C/B),$$

so if `e(B/A) = 1` then `e(C/A) = e(C/B)`.

For a commutative square of prime ideals whose bottom edge has ramification index one, the top
edge has ramification index one if and only if the two vertical ramification indices agree, and
the lower vertical index always divides the upper one. These facts give criteria for a weak
solution of `IsDiscreteValuationRing.IntegralClosureBaseChange` to remain a weak solution after
enlarging the field.

## Main results

* `Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_mul`: the valuation of the image
  of an element scales by the ramification index.
* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_trans`: multiplicativity in a tower.
* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_eq_of_isWeaklyUnramified`: if
  `e(B/A) = 1` then `e(C/A) = e(C/B)`.
* `Stacks.DiscreteValuationRing.Ramification.isWeaklyUnramified_of_isWeaklyUnramified`: if
  `e(C/A) = 1` then `e(B/A) = 1` and `e(C/B) = 1`.
* `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_eq_of_mul_eq_of_le`: if
  `e(C/A) = d₁ d₂`, `e(B/A) ≤ d₁` and `e(C/B) ≤ d₂`, then `e(B/A) = d₁` and `e(C/B) = d₂`.
* `Ideal.ramificationIdx_eq_one_of_finiteEtale_square`: ramification index one is preserved by a
  finite étale square.
* `Ideal.ramificationIdx_eq_one_iff_ramificationIdx_vertical_eq`: given ramification index one on
  the bottom edge of a square, the top edge has ramification index one if and only if the two
  vertical ramification indices agree.
* `Ideal.ramificationIdx_vertical_dvd_of_ramificationIdx_eq_one`: given ramification index one on
  the bottom edge, the lower vertical index divides the upper one.
* `Ideal.ramificationIdx_eq_one_iff_ramificationIdx_vertical_le`: given ramification index one on
  the bottom edge, the top edge has ramification index one if and only if the upper vertical index
  is at most the lower one.

In the namespace `IsDiscreteValuationRing.IntegralClosureBaseChange`:

* `IsWeakSolution.of_finiteEtale_square`: a weak solution remains one after a finite étale square.
* `IsWeakSolution.of_ramificationIdx_vertical_eq`: a weak solution remains one when the vertical
  ramification indices agree.
* `IsWeakSolution.of_ramificationIdx_vertical_le`: a weak solution remains one when the upper
  vertical ramification index is at most the lower one.

## References

* [The Stacks Project, Tag 09E6](https://stacks.math.columbia.edu/tag/09E6)
* [The Stacks Project, Tag 09ES](https://stacks.math.columbia.edu/tag/09ES)
-/

@[expose] public section

namespace Stacks.DiscreteValuationRing.Ramification

open IsDiscreteValuationRing

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [FaithfulSMul A B]

/-- The `B`-valuation of the image of an element of `A` is its `A`-valuation scaled by the
ramification index. -/
@[sga "7 IX 10.3" "partial"]
theorem addVal_algebraMap_eq_mul {a : A} {n : ℕ} (h : addVal A a = (n : ℕ∞)) :
    addVal B (algebraMap A B a) = ((ramificationIdx A B * n : ℕ) : ℕ∞) := by
  obtain ⟨πA, hπAprime⟩ := exists_prime A
  have hπA : Irreducible πA := hπAprime.irreducible
  have ha : a ≠ 0 := by
    rintro rfl
    rw [addVal_zero] at h
    exact (ENat.natCast_ne_top n) h.symm
  obtain ⟨k, u, hk⟩ := eq_unit_mul_pow_irreducible ha hπA
  have hkn : k = n := by exact_mod_cast (addVal_def a u hπA k hk).symm.trans h
  obtain ⟨w, hw⟩ := (u.isUnit).map (algebraMap A B)
  rw [hk, map_mul, map_pow, addVal_mul, addVal_pow, ← hw, addVal_eq_zero_of_unit,
    addVal_algebraMap_eq_ramificationIdx A B πA hπA, hkn]
  push_cast
  simp [nsmul_eq_mul, mul_comm]

variable (C : Type*) [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra B C]
  [Algebra A C] [IsScalarTower A B C] [FaithfulSMul B C] [FaithfulSMul A C]

/-- **Ramification indices are multiplicative in a tower**: `e(C/A) = e(B/A) * e(C/B)`. -/
theorem ramificationIdx_trans :
    ramificationIdx A C = ramificationIdx A B * ramificationIdx B C := by
  obtain ⟨πA, hπAprime⟩ := exists_prime A
  have hπA : Irreducible πA := hπAprime.irreducible
  have hAB : addVal B (algebraMap A B πA) = (ramificationIdx A B : ℕ∞) :=
    addVal_algebraMap_eq_ramificationIdx A B πA hπA
  have hBC : addVal C (algebraMap B C (algebraMap A B πA))
      = ((ramificationIdx B C * ramificationIdx A B : ℕ) : ℕ∞) :=
    addVal_algebraMap_eq_mul B C hAB
  have hAC : addVal C (algebraMap A C πA) = (ramificationIdx A C : ℕ∞) :=
    addVal_algebraMap_eq_ramificationIdx A C πA hπA
  rw [IsScalarTower.algebraMap_apply A B C, hBC] at hAC
  rw [mul_comm]
  exact_mod_cast hAC.symm

/-- If `B` has ramification index one over `A`, then the ramification indices of `C` over `A` and
over `B` agree. -/
theorem ramificationIdx_eq_of_isWeaklyUnramified (h : ramificationIdx A B = 1) :
    ramificationIdx A C = ramificationIdx B C := by
  rw [ramificationIdx_trans A B C, h, one_mul]

/-- If `C` has ramification index one over `A`, then `B` has ramification index one over `A` and
`C` has ramification index one over `B`. -/
theorem isWeaklyUnramified_of_isWeaklyUnramified (h : ramificationIdx A C = 1) :
    ramificationIdx A B = 1 ∧ ramificationIdx B C = 1 := by
  rw [ramificationIdx_trans A B C] at h
  exact ⟨Nat.eq_one_of_mul_eq_one_right h,
    Nat.eq_one_of_mul_eq_one_right (by rwa [Nat.mul_comm] at h)⟩

/-- If the ramification index of `C` over `A` is `d₁ * d₂`, the ramification index of `B` over `A`
is at most `d₁` and that of `C` over `B` is at most `d₂`, then these two bounds are equalities. -/
theorem ramificationIdx_eq_of_mul_eq_of_le (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hAC : ramificationIdx A C = d₁ * d₂)
    (hAB : ramificationIdx A B ≤ d₁) (hBC : ramificationIdx B C ≤ d₂) :
    ramificationIdx A B = d₁ ∧ ramificationIdx B C = d₂ := by
  rw [ramificationIdx_trans A B C] at hAC
  have hBC' : ramificationIdx B C = d₂ := by nlinarith
  subst hBC'
  exact ⟨by nlinarith, rfl⟩

end Stacks.DiscreteValuationRing.Ramification

namespace Ideal

/-- Let `q'` be a prime of `T'` lying over primes `q` of `T` and `p'` of `R'`, both lying over a
prime `p` of `R`, where `R → R'` and `T → T'` are finite étale and `T → T'`, `R' → T'` are flat. If
`q` has ramification index one over `R`, then `q'` has ramification index one over `R'`. -/
theorem ramificationIdx_eq_one_of_finiteEtale_square
    {R T R' T' : Type*}
    [CommRing R] [CommRing T] [CommRing R'] [CommRing T']
    [Algebra R T] [Algebra R R'] [Algebra T T'] [Algebra R' T']
    [Algebra R T'] [IsScalarTower R T T'] [IsScalarTower R R' T']
    [Algebra.Etale R R'] [Module.Finite R R']
    [Algebra.Etale T T'] [Module.Finite T T']
    [Module.Flat T T'] [Module.Flat R' T']
    (p : Ideal R) (q : Ideal T) (p' : Ideal R') (q' : Ideal T')
    [p.IsPrime] [q.IsPrime] [p'.IsPrime] [q'.IsPrime]
    [q.LiesOver p] [p'.LiesOver p] [q'.LiesOver q] [q'.LiesOver p']
    (hweak : q.ramificationIdx R = 1) :
    q'.ramificationIdx R' = 1 := by
  have hqet : q'.ramificationIdx T = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hpet : p'.ramificationIdx R = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hbottom := Ideal.ramificationIdx_tower (R := R) q q'
  have htop := Ideal.ramificationIdx_tower (R := R) p' q'
  rw [hweak, hqet, one_mul] at hbottom
  rw [hpet, one_mul] at htop
  exact htop.symm.trans hbottom

/-- Let `q'` be a prime of `T'` lying over primes `q` of `T` and `p'` of `R'`, both lying over a
prime `p` of `R`, where `T → T'` and `R' → T'` are flat. If `q` has ramification index one over `R`
and `p'` has positive ramification index over `R`, then `q'` has ramification index one over `R'`
if and only if `q'.ramificationIdx T = p'.ramificationIdx R`. -/
theorem ramificationIdx_eq_one_iff_ramificationIdx_vertical_eq
    {R T R' T' : Type*}
    [CommRing R] [CommRing T] [CommRing R'] [CommRing T']
    [Algebra R T] [Algebra R R'] [Algebra T T'] [Algebra R' T']
    [Algebra R T'] [IsScalarTower R T T'] [IsScalarTower R R' T']
    [Module.Flat T T'] [Module.Flat R' T']
    (p : Ideal R) (q : Ideal T) (p' : Ideal R') (q' : Ideal T')
    [p.IsPrime] [q.IsPrime] [p'.IsPrime] [q'.IsPrime]
    [q.LiesOver p] [p'.LiesOver p] [q'.LiesOver q] [q'.LiesOver p']
    (hweak : q.ramificationIdx R = 1) (hpos : 0 < p'.ramificationIdx R) :
    q'.ramificationIdx R' = 1 ↔ q'.ramificationIdx T = p'.ramificationIdx R := by
  have hbottom := Ideal.ramificationIdx_tower (R := R) q q'
  have htop := Ideal.ramificationIdx_tower (R := R) p' q'
  rw [hweak, one_mul] at hbottom
  rw [hbottom] at htop
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [htop, h, mul_one]
  · rw [h] at htop
    exact (Nat.eq_of_mul_eq_mul_left hpos (by rwa [mul_one])).symm

/-- Let `q'` be a prime of `T'` lying over primes `q` of `T` and `p'` of `R'`, both lying over a
prime `p` of `R`, where `T → T'` and `R' → T'` are flat. If `q` has ramification index one over
`R`, then `p'.ramificationIdx R` divides `q'.ramificationIdx T`, with cofactor
`q'.ramificationIdx R'`. -/
theorem ramificationIdx_vertical_dvd_of_ramificationIdx_eq_one
    {R T R' T' : Type*}
    [CommRing R] [CommRing T] [CommRing R'] [CommRing T']
    [Algebra R T] [Algebra R R'] [Algebra T T'] [Algebra R' T']
    [Algebra R T'] [IsScalarTower R T T'] [IsScalarTower R R' T']
    [Module.Flat T T'] [Module.Flat R' T']
    (p : Ideal R) (q : Ideal T) (p' : Ideal R') (q' : Ideal T')
    [p.IsPrime] [q.IsPrime] [p'.IsPrime] [q'.IsPrime]
    [q.LiesOver p] [p'.LiesOver p] [q'.LiesOver q] [q'.LiesOver p']
    (hweak : q.ramificationIdx R = 1) :
    p'.ramificationIdx R ∣ q'.ramificationIdx T := by
  have hbottom := Ideal.ramificationIdx_tower (R := R) q q'
  have htop := Ideal.ramificationIdx_tower (R := R) p' q'
  rw [hweak, one_mul] at hbottom
  exact ⟨q'.ramificationIdx R', hbottom.symm.trans htop⟩

/-- Let `q'` be a prime of `T'` lying over primes `q` of `T` and `p'` of `R'`, both lying over a
prime `p` of `R`, where `T → T'` and `R' → T'` are flat. If `q` has ramification index one over `R`
and `p'.ramificationIdx R` and `q'.ramificationIdx T` are positive, then `q'` has ramification
index one over `R'` if and only if `q'.ramificationIdx T ≤ p'.ramificationIdx R`. -/
theorem ramificationIdx_eq_one_iff_ramificationIdx_vertical_le
    {R T R' T' : Type*}
    [CommRing R] [CommRing T] [CommRing R'] [CommRing T']
    [Algebra R T] [Algebra R R'] [Algebra T T'] [Algebra R' T']
    [Algebra R T'] [IsScalarTower R T T'] [IsScalarTower R R' T']
    [Module.Flat T T'] [Module.Flat R' T']
    (p : Ideal R) (q : Ideal T) (p' : Ideal R') (q' : Ideal T')
    [p.IsPrime] [q.IsPrime] [p'.IsPrime] [q'.IsPrime]
    [q.LiesOver p] [p'.LiesOver p] [q'.LiesOver q] [q'.LiesOver p']
    (hweak : q.ramificationIdx R = 1) (hpos : 0 < p'.ramificationIdx R)
    (hposT : 0 < q'.ramificationIdx T) :
    q'.ramificationIdx R' = 1 ↔ q'.ramificationIdx T ≤ p'.ramificationIdx R := by
  have hbottom := Ideal.ramificationIdx_tower (R := R) q q'
  have htop := Ideal.ramificationIdx_tower (R := R) p' q'
  rw [hweak, one_mul] at hbottom
  rw [hbottom] at htop
  refine ⟨fun h => le_of_eq (by rw [htop, h, mul_one]), fun h => ?_⟩
  rw [htop] at h hposT
  nlinarith

end Ideal

namespace IsDiscreteValuationRing.IntegralClosureBaseChange

attribute [local instance]
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingA₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.commRingB₁
  IsDiscreteValuationRing.IntegralClosureBaseChange.algebraA₁B₁

/-- If `D₁` is a weak solution and `D₁.A₁ → D₂.A₁` and `D₁.B₁ → D₂.B₁` are finite étale maps
compatible with the algebra structures, then `D₂` is a weak solution. -/
theorem IsWeakSolution.of_finiteEtale_square
    {A B K L K₁ K₂ : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [Algebra K K₂] [Algebra A K₂]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower A K K₁] [IsScalarTower A K K₂]
    [Module.Finite K K₁] [Module.Finite K K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [Algebra D₁.A₁ D₂.A₁] [Algebra D₁.B₁ D₂.B₁]
    [Algebra D₁.A₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₁.B₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₂.A₁ D₂.B₁]
    [Algebra.Etale D₁.A₁ D₂.A₁] [Module.Finite D₁.A₁ D₂.A₁]
    [Algebra.Etale D₁.B₁ D₂.B₁] [Module.Finite D₁.B₁ D₂.B₁]
    [Module.Flat D₁.B₁ D₂.B₁] [Module.Flat D₂.A₁ D₂.B₁]
    (hD₁ : D₁.IsWeakSolution) : D₂.IsWeakSolution := by
  intro q' hq'
  let q : Ideal D₁.B₁ := q'.under D₁.B₁
  let p' : Ideal D₂.A₁ := q'.under D₂.A₁
  let p : Ideal D₁.A₁ := q.under D₁.A₁
  let : q'.IsPrime := hq'.isPrime
  let : q.IsPrime := Ideal.IsPrime.comap (algebraMap D₁.B₁ D₂.B₁)
  let : p'.IsPrime := Ideal.IsPrime.comap (algebraMap D₂.A₁ D₂.B₁)
  let : p.IsPrime := Ideal.IsPrime.comap (algebraMap D₁.A₁ D₁.B₁)
  let : q'.LiesOver q := ⟨rfl⟩
  let : q.LiesOver p := ⟨rfl⟩
  let : q'.LiesOver p' := ⟨rfl⟩
  let : p'.LiesOver p := ⟨((Ideal.under_under q').trans (Ideal.under_under q').symm).symm⟩
  have hq : q.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (hI := hq') q'
  exact Ideal.ramificationIdx_eq_one_of_finiteEtale_square p q p' q'
    (hD₁ q hq)

/-- Let `D₁` be a weak solution, with `D₁.B₁ → D₂.B₁` finite and flat and `D₂.A₁ → D₂.B₁` flat,
compatibly with the algebra structures. If every maximal ideal `q'` of `D₂.B₁` has the same
ramification index over `D₁.B₁` as `q'.under D₂.A₁` has over `D₁.A₁`, and the latter is positive,
then `D₂` is a weak solution. -/
theorem IsWeakSolution.of_ramificationIdx_vertical_eq
    {A B K L K₁ K₂ : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [Algebra K K₂] [Algebra A K₂]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower A K K₁] [IsScalarTower A K K₂]
    [Module.Finite K K₁] [Module.Finite K K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [Algebra D₁.A₁ D₂.A₁] [Algebra D₁.B₁ D₂.B₁]
    [Algebra D₁.A₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₁.B₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₂.A₁ D₂.B₁]
    [Module.Finite D₁.B₁ D₂.B₁]
    [Module.Flat D₁.B₁ D₂.B₁] [Module.Flat D₂.A₁ D₂.B₁]
    (hpos : ∀ q' : Ideal D₂.B₁, q'.IsMaximal →
      0 < (q'.under D₂.A₁).ramificationIdx D₁.A₁)
    (hbal : ∀ q' : Ideal D₂.B₁, q'.IsMaximal →
      q'.ramificationIdx D₁.B₁ = (q'.under D₂.A₁).ramificationIdx D₁.A₁)
    (hD₁ : D₁.IsWeakSolution) : D₂.IsWeakSolution := by
  intro q' hq'
  let q : Ideal D₁.B₁ := q'.under D₁.B₁
  let p' : Ideal D₂.A₁ := q'.under D₂.A₁
  let p : Ideal D₁.A₁ := q.under D₁.A₁
  let : q'.IsPrime := hq'.isPrime
  let : q.IsPrime := Ideal.IsPrime.comap (algebraMap D₁.B₁ D₂.B₁)
  let : p'.IsPrime := Ideal.IsPrime.comap (algebraMap D₂.A₁ D₂.B₁)
  let : p.IsPrime := Ideal.IsPrime.comap (algebraMap D₁.A₁ D₁.B₁)
  let : q'.LiesOver q := ⟨rfl⟩
  let : q.LiesOver p := ⟨rfl⟩
  let : q'.LiesOver p' := ⟨rfl⟩
  let : p'.LiesOver p := ⟨((Ideal.under_under q').trans (Ideal.under_under q').symm).symm⟩
  have hq : q.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (hI := hq') q'
  exact (Ideal.ramificationIdx_eq_one_iff_ramificationIdx_vertical_eq p q p' q'
    (hD₁ q hq) (hpos q' hq')).mpr (hbal q' hq')

/-- Let `D₁` be a weak solution, with `D₁.B₁ → D₂.B₁` finite and flat and `D₂.A₁ → D₂.B₁` flat,
compatibly with the algebra structures. If for every maximal ideal `q'` of `D₂.B₁` the ramification
index of `q'` over `D₁.B₁` is positive and at most the ramification index of `q'.under D₂.A₁` over
`D₁.A₁`, which is positive, then `D₂` is a weak solution. -/
theorem IsWeakSolution.of_ramificationIdx_vertical_le
    {A B K L K₁ K₂ : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [Algebra K K₁] [Algebra A K₁] [Algebra K K₂] [Algebra A K₂]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsScalarTower A K K₁] [IsScalarTower A K K₂]
    [Module.Finite K K₁] [Module.Finite K K₂]
    (D₁ : IntegralClosureBaseChange A B K L K₁)
    (D₂ : IntegralClosureBaseChange A B K L K₂)
    [Algebra D₁.A₁ D₂.A₁] [Algebra D₁.B₁ D₂.B₁]
    [Algebra D₁.A₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₁.B₁ D₂.B₁]
    [IsScalarTower D₁.A₁ D₂.A₁ D₂.B₁]
    [Module.Finite D₁.B₁ D₂.B₁]
    [Module.Flat D₁.B₁ D₂.B₁] [Module.Flat D₂.A₁ D₂.B₁]
    (hpos : ∀ q' : Ideal D₂.B₁, q'.IsMaximal →
      0 < (q'.under D₂.A₁).ramificationIdx D₁.A₁)
    (hposT : ∀ q' : Ideal D₂.B₁, q'.IsMaximal → 0 < q'.ramificationIdx D₁.B₁)
    (hle : ∀ q' : Ideal D₂.B₁, q'.IsMaximal →
      q'.ramificationIdx D₁.B₁ ≤ (q'.under D₂.A₁).ramificationIdx D₁.A₁)
    (hD₁ : D₁.IsWeakSolution) : D₂.IsWeakSolution := by
  intro q' hq'
  let q : Ideal D₁.B₁ := q'.under D₁.B₁
  let p' : Ideal D₂.A₁ := q'.under D₂.A₁
  let p : Ideal D₁.A₁ := q.under D₁.A₁
  let : q'.IsPrime := hq'.isPrime
  let : q.IsPrime := Ideal.IsPrime.comap (algebraMap D₁.B₁ D₂.B₁)
  let : p'.IsPrime := Ideal.IsPrime.comap (algebraMap D₂.A₁ D₂.B₁)
  let : p.IsPrime := Ideal.IsPrime.comap (algebraMap D₁.A₁ D₁.B₁)
  let : q'.LiesOver q := ⟨rfl⟩
  let : q.LiesOver p := ⟨rfl⟩
  let : q'.LiesOver p' := ⟨rfl⟩
  let : p'.LiesOver p := ⟨((Ideal.under_under q').trans (Ideal.under_under q').symm).symm⟩
  have hq : q.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (hI := hq') q'
  exact (Ideal.ramificationIdx_eq_one_iff_ramificationIdx_vertical_le p q p' q'
    (hD₁ q hq) (hpos q' hq') (hposT q' hq')).mpr (hle q' hq')

end IsDiscreteValuationRing.IntegralClosureBaseChange
