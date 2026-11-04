module

public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback

/-!
# A cardinality bound for the Picard group of a normal integral scheme

On a locally Noetherian normal integral scheme `X` the first Chern class `Pic(X) → Cl(X)` is
injective ([Stacks, Tag 0BE8]), and the Weil divisors are integer-valued functions on the prime
divisors, which are determined by their ideal sheaves. This bounds the Picard group by
`2 ^ 2 ^ size X`.

## Main results

* `AlgebraicGeometry.Scheme.mk_idealSheafData_le`: `#X.IdealSheafData ≤ 2 ^ size X`.
* `Stacks.Picard.lift_mk_ofScheme_le`: `#Pic(X) ≤ 2 ^ 2 ^ size X`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Cardinal

universe u

namespace AlgebraicGeometry.Scheme

/-- **There are at most `2 ^ size Y` quasi-coherent ideal sheaves on a scheme `Y`.** -/
theorem mk_idealSheafData_le (Y : Scheme.{u}) : #Y.IdealSheafData ≤ 2 ^ Y.size := by
  let φ : Y.IdealSheafData → Set (Σ U : Y.affineOpens, Γ(Y, U.1)) :=
    fun I => {p | p.2 ∈ I.ideal p.1}
  have hφ : Function.Injective φ := by
    intro I J h
    ext U x
    exact Iff.of_eq (congrArg (fun S => (⟨U, x⟩ : Σ U : Y.affineOpens, Γ(Y, U.1)) ∈ S) h)
  refine (Cardinal.mk_le_of_injective hφ).trans ?_
  rw [Cardinal.mk_set]
  refine Cardinal.power_le_power_left two_ne_zero ?_
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_mk_mul_iSup _).trans ?_
  calc #Y.affineOpens * (⨆ U : Y.affineOpens, #Γ(Y, U.1)) ≤ Y.size * Y.size :=
        mul_le_mul' Y.mk_affineOpens_le_size (ciSup_le' fun U => Y.mk_sections_le_size U)
    _ = Y.size := Cardinal.mul_eq_self Y.aleph0_le_size

end AlgebraicGeometry.Scheme

namespace Stacks.Picard

/-- **The Picard group of a locally Noetherian normal integral scheme `Y` has at most
`2 ^ 2 ^ size Y` elements.** -/
theorem lift_mk_ofScheme_le (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] :
    #(ofScheme Y) ≤ Cardinal.lift.{u + 1} ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ Y.size) := by
  have h0 : Cardinal.lift.{u} #(ofScheme Y) ≤ Cardinal.lift.{u + 1} #(weilDivisorClassGroup Y) :=
    Cardinal.lift_mk_le'.2
      ⟨⟨(picardToWeilDivisorClassGroup Y ·), picardToWeilDivisorClassGroup_injective Y⟩⟩
  have h1 : #(ofScheme Y) ≤ Cardinal.lift.{u + 1} #(weilDivisorClassGroup Y) := by
    rwa [Cardinal.lift_id'.{u, u + 1}] at h0
  refine h1.trans (Cardinal.lift_le.2 ?_)
  have hprime : #(PrimeDivisor Y) ≤ 2 ^ Y.size := by
    refine (Cardinal.mk_le_of_injective (f := fun Z : PrimeDivisor Y => Z.idealSheaf) ?_).trans
      (Scheme.mk_idealSheafData_le Y)
    rintro ⟨I, h₁, h₂⟩ ⟨J, h₃, h₄⟩ h
    cases h
    rfl
  calc #(weilDivisorClassGroup Y) ≤ #(WeilDivisor Y) := Cardinal.mk_quotient_le
    _ ≤ #(PrimeDivisor Y → ℤ) := Cardinal.mk_subtype_le _
    _ = ℵ₀ ^ #(PrimeDivisor Y) := by
        rw [Cardinal.mk_arrow, Cardinal.mk_int, Cardinal.lift_aleph0, Cardinal.lift_uzero]
    _ ≤ ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ Y.size) ^ ((2 : Cardinal.{u}) ^ Y.size) := by
        refine (Cardinal.power_le_power_right ?_).trans (Cardinal.power_le_power_left
          (Cardinal.power_ne_zero _ two_ne_zero) hprime)
        exact Y.aleph0_le_size.trans ((Cardinal.cantor _).le.trans (Cardinal.cantor _).le)
    _ = (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ Y.size := by
        rw [← Cardinal.power_mul, Cardinal.mul_eq_self]
        exact Y.aleph0_le_size.trans (Cardinal.cantor _).le

end Stacks.Picard
