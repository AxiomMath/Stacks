module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.KrullDimension.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Completion
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Henselization
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.IntegralClosureCompletion
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.LocalBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.NonZeroDivisors
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Normalization
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import StacksFrontier.RingTheory.DimensionFormula
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.KrullDimension.IntegralExtension

/-!
# The normalization of a flat local base change

Let `A` be a reduced one-dimensional Nagata local ring with normalization
`A' = integralClosure A (FractionRing A)`, and let `B` be a flat local `A`-algebra.  Then
`A' ⊗[A] B` is the normalization of `B` in the total ring of fractions of `B` as soon as it is
a normal ring.

## Main results

* `Stacks.Curves.range_eq_integralClosure_of_isNormalRing_tensorProduct`: the range of an
  injective comparison map `A' ⊗[A] B → Q(B)` is the normalization of `B` as soon as `A' ⊗[A] B`
  is a normal ring.

## References

* [Stacks Project, Tag 0C3V](https://stacks.math.columbia.edu/tag/0C3V)
* [Stacks Project, Tag 0C3S](https://stacks.math.columbia.edu/tag/0C3S)
-/

@[expose] public section

namespace Stacks.Curves

open IsLocalRing
open scoped TensorProduct

universe u v w

/-- A normal ring `R`, finite over a ring `B` and with total ring of fractions `K`, is the
integral closure of `B` in `K`. -/
private theorem isIntegral_iff_mem_range_of_isFractionRing
    (B R K : Type*) [CommRing B] [CommRing R] [CommRing K]
    [Algebra B R] [Algebra B K] [Algebra R K] [IsScalarTower B R K]
    [Module.Finite B R] [IsFractionRing R K] (hnormal : IsNormalRing R) (x : K) :
    IsIntegral B x ↔ ∃ y : R, algebraMap R K y = x := by
  have : Algebra.IsIntegral B R := Algebra.IsIntegral.of_finite B R
  have hclosed : IsIntegrallyClosedIn R K :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn (R := R) K).mp hnormal.isIntegrallyClosed
  refine ⟨fun hx => hclosed.isIntegral_iff.mp hx.tower_top, ?_⟩
  rintro ⟨y, rfl⟩
  exact (Algebra.IsIntegral.isIntegral y).map (IsScalarTower.toAlgHom B R K)

/-- Let `A` be a commutative ring with
normalization `A' = integralClosure A (FractionRing A)` finite over `A`, and let `B` be an
`A`-algebra whose total ring of fractions is already the localization of `B` at the powers of
`algebraMap A B f`.  Given an injective comparison map `g : A' ⊗[A] B → Q(B)` restricting to the
canonical map on `B`, if `A' ⊗[A] B` is a normal ring then the range of `g` is exactly the
normalization of `B` in `Q(B)`. -/
public theorem range_eq_integralClosure_of_isNormalRing_tensorProduct
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra A (FractionRing B)]
    [Module.Finite A ↥(integralClosure A (FractionRing A))] {f : A}
    (hLB : IsLocalization (Submonoid.powers (algebraMap A B f)) (FractionRing B))
    (g : (↥(integralClosure A (FractionRing A)) ⊗[A] B) →ₐ[A] FractionRing B)
    (hg : Function.Injective g)
    (hcompat : ∀ b : B,
      g (Algebra.TensorProduct.includeRight b) = algebraMap B (FractionRing B) b)
    (hnormal : IsNormalRing (↥(integralClosure A (FractionRing A)) ⊗[A] B)) :
    ∀ x : FractionRing B, x ∈ g.range ↔ IsIntegral B x := by
  let fB : B := algebraMap A B f
  let : IsLocalization (Submonoid.powers fB) (FractionRing B) := hLB
  let S := integralClosure A (FractionRing A)
  let R := S ⊗[A] B
  let : Algebra B R := Algebra.TensorProduct.rightAlgebra (R := A) (A := S) (B := B)
  let : IsScalarTower A B R := Algebra.TensorProduct.right_isScalarTower (R := A) (A := S) (B := B)
  let : Algebra R (FractionRing B) := g.toAlgebra
  have hgfB : g (algebraMap B R fB) = algebraMap B (FractionRing B) fB := hcompat fB
  have hufB : IsUnit (g (algebraMap B R fB)) :=
    hgfB ▸ IsLocalization.map_units (FractionRing B) ⟨fB, Submonoid.mem_powers fB⟩
  have hRlocf : IsLocalization (Submonoid.powers (algebraMap B R fB)) (FractionRing B) := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, n, rfl⟩
      show IsUnit (g ((algebraMap B R fB) ^ n))
      rw [map_pow]
      exact hufB.pow n
    · intro z
      obtain ⟨⟨b, d⟩, hz⟩ := IsLocalization.surj
        (M := Submonoid.powers fB) (S := FractionRing B) z
      obtain ⟨n, hpow⟩ := (Submonoid.mem_powers_iff d.1 fB).mp d.2
      refine ⟨(algebraMap B R b, ⟨(algebraMap B R fB) ^ n, ⟨n, rfl⟩⟩), ?_⟩
      show z * g ((algebraMap B R fB) ^ n) = g (algebraMap B R b)
      rw [map_pow, hgfB, ← map_pow, hpow]
      exact hz.trans (hcompat b).symm
    · intro x y hxy
      exact ⟨1, by simp [hg hxy]⟩
  have hfR : algebraMap B R fB ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff_left]
    intro x hx
    have hm : g (algebraMap B R fB) * g x = 0 := by
      simpa [map_mul] using congrArg g hx
    exact hg (by simpa using hufB.mul_right_eq_zero.mp hm)
  have htotal : IsFractionRing R (FractionRing B) := by
    show IsLocalization (nonZeroDivisors R) (FractionRing B)
    rw [isLocalization_iff]
    let : IsLocalization (Submonoid.powers (algebraMap B R fB)) (FractionRing B) := hRlocf
    refine ⟨?_, ?_, ?_⟩
    · intro r
      have hregK : g r.1 ∈ nonZeroDivisors (FractionRing B) := by
        rw [mem_nonZeroDivisors_iff_left]
        intro z hz
        obtain ⟨⟨a, d⟩, hrep⟩ := IsLocalization.surj
          (M := Submonoid.powers (algebraMap B R fB)) (S := FractionRing B) z
        change z * g d.1 = g a at hrep
        have hm : g r.1 * g a = 0 := by rw [← hrep, ← mul_assoc, hz, zero_mul]
        have hra : r.1 * a = 0 := hg (by simpa [map_mul] using hm)
        have ha : a = 0 := (mem_nonZeroDivisors_iff.mp r.2).1 a hra
        have hz' : z * g d.1 = 0 := by simpa [ha] using hrep
        exact (IsLocalization.map_units (FractionRing B) d).mul_left_eq_zero.mp hz'
      rwa [IsFractionRing.nonZeroDivisors_eq_isUnit B (FractionRing B)] at hregK
    · intro z
      obtain ⟨⟨a, d⟩, hrep⟩ := IsLocalization.surj
        (M := Submonoid.powers (algebraMap B R fB)) (S := FractionRing B) z
      obtain ⟨n, hpow⟩ := (Submonoid.mem_powers_iff d.1 (algebraMap B R fB)).mp d.2
      exact ⟨(a, ⟨d.1, hpow ▸ pow_mem hfR n⟩), hrep⟩
    · intro x y hxy
      exact ⟨1, by simp [hg hxy]⟩
  let : Module.Finite B R := by
    let : Module.Finite B (B ⊗[A] S) := Module.Finite.base_change (R := A) (A := B) (M := S)
    exact Module.Finite.equiv (Algebra.TensorProduct.commRight A B S).toLinearEquiv
  let gB : R →ₐ[B] FractionRing B :=
    { toRingHom := g.toRingHom
      commutes' := hcompat }
  let : IsScalarTower B R (FractionRing B) :=
    IsScalarTower.of_algebraMap_eq' gB.comp_algebraMap.symm
  exact fun x => (isIntegral_iff_mem_range_of_isFractionRing B R (FractionRing B) hnormal x).symm

end Stacks.Curves

end
