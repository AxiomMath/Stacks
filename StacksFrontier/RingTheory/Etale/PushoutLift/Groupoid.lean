module

public import StacksFrontier.RingTheory.Etale.PushoutLift.Composition
public import StacksFrontier.RingTheory.Etale.Lifting
public import StacksFrontier.RingTheory.Descent.SquareZeroGroupoid
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat

/-!
# The lifted Čech groupoid is effective

This file is part of the proof of Stacks 0ALT. Let `A` be a ring, `I, J ⊆ A` ideals with `J`
nilpotent, `B₀` an `A`-algebra, and `B₀ → Γ₀` an étale, faithfully flat map of `A`-algebras such
that `B₀ ⧸ I B₀ → Γ₀ ⧸ I Γ₀` is bijective. Let `Γ → Γ₀` be a surjection of `A`-algebras with
kernel `J Γ`, where `Γ` is étale over `Spec A \ V(I)`.

Then the Čech groupoid `Γ₀ ⇉ Γ₀ ⊗[B₀] Γ₀` of `B₀ → Γ₀` lifts to an *effective* groupoid
`Γ ⇉ Δ` of rings, with `Δ` étale over `Γ` (`exists_effective_groupoid`). Geometrically: the
étale chart `Spec Γ₀ → Spec B₀` lifts to a chart of a (necessarily affine) thickening of
`Spec B₀`; its ring of functions is the ring whose existence is asserted by Stacks 0ALT.

The groupoid is built from the étale lift `Δ` of `Γ₀ ⊗[B₀] Γ₀` along `Γ → Γ₀` (Stacks 04D1), the
diagonal idempotent, the second projection and the unit of
`StacksFrontier.RingTheory.Etale.PushoutLift.Section` and the composition of
`StacksFrontier.RingTheory.Etale.PushoutLift.Composition`. Its effectiveness is deduced from the
effectiveness of the Čech groupoid of the faithfully flat map `B₀ → Γ₀` by
`Module.Descent.SquareZero.isEffective_of_pow_eq_bot`, the deformation of effective flat
groupoids along nilpotent invariant ideals.

## References

* [Stacks Project, Tag 0ALT](https://stacks.math.columbia.edu/tag/0ALT)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public section

open TensorProduct Module.Descent.SquareZero

universe u

namespace Stacks.Etale.PushoutLift

variable {A : Type u} [CommRing A] (I J : Ideal A) (hJ : IsNilpotent J)
variable {B₀ : Type u} [CommRing B₀] [Algebra A B₀]
variable {Γ₀ : Type u} [CommRing Γ₀] [Algebra A Γ₀] [Algebra B₀ Γ₀] [IsScalarTower A B₀ Γ₀]
variable {Γ : Type u} [CommRing Γ] [Algebra A Γ] [Algebra Γ Γ₀] [IsScalarTower A Γ Γ₀]

/-- **The Čech groupoid of a faithfully flat map is effective.** -/
theorem isEffective_includeRight [Module.FaithfullyFlat B₀ Γ₀] :
    IsEffective (Algebra.TensorProduct.includeRight (R := B₀) (A := Γ₀) (B := Γ₀)).toRingHom := by
  have h : ∀ b : B₀, Algebra.TensorProduct.includeRight.toRingHom (algebraMap B₀ Γ₀ b) =
      algebraMap Γ₀ (Γ₀ ⊗[B₀] Γ₀) (algebraMap B₀ Γ₀ b) := fun b => by
    change (1 : Γ₀) ⊗ₜ[B₀] algebraMap B₀ Γ₀ b = algebraMap B₀ Γ₀ b ⊗ₜ[B₀] (1 : Γ₀)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  refine ⟨B₀, inferInstance, inferInstance, h, inferInstance, ?_⟩
  have hid : ∀ z, cmp _ B₀ h z = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      rw [cmp_tmul]
      simp [Algebra.TensorProduct.algebraMap_apply]
    | add z w hz hw => rw [map_add, hz, hw]
  exact ⟨fun z w hzw => by rwa [hid, hid] at hzw, fun z => ⟨z, hid z⟩⟩

variable [Algebra.Etale B₀ Γ₀] [Module.FaithfullyFlat B₀ Γ₀]
variable (hΓ₀ : Function.Surjective (algebraMap Γ Γ₀))
  (hΓ₀ker : RingHom.ker (algebraMap Γ Γ₀) = J.map (algebraMap A Γ))
variable (hΓU : ∀ (T : Type u) [CommRing T] [Algebra A T], I.map (algebraMap A T) = ⊤ →
    Algebra.FormallyEtale T (T ⊗[A] Γ))
variable (hsurjI : ∀ y : Γ₀, ∃ b : B₀, y - algebraMap B₀ Γ₀ b ∈ I.map (algebraMap A Γ₀))
  (hinjI : ∀ b : B₀, algebraMap B₀ Γ₀ b ∈ I.map (algebraMap A Γ₀) →
    b ∈ I.map (algebraMap A B₀))

include hJ hΓ₀ hΓ₀ker hΓU hsurjI hinjI in
/-- **The lifted Čech groupoid.** There are an étale `Γ`-algebra `Δ`, a surjection
`ψ : Δ → Γ₀ ⊗[B₀] Γ₀` of `Γ`-algebras with kernel `J Δ`, and an `A`-algebra map `s : Γ → Δ` lifting
the inclusion of the second factor, such that the groupoid `s, t : Γ ⇉ Δ` is effective. -/
theorem exists_effective_groupoid :
    ∃ (Δ : Type u) (_ : CommRing Δ) (_ : Algebra Γ Δ) (_ : Algebra.Etale Γ Δ)
      (ψ : Δ →ₐ[Γ] Γ₀ ⊗[B₀] Γ₀) (s : Γ →+* Δ),
      Function.Surjective ψ ∧
      RingHom.ker (ψ : Δ →+* Γ₀ ⊗[B₀] Γ₀) = (J.map (algebraMap A Γ)).map (algebraMap Γ Δ) ∧
      (∀ x, ψ (s x) = Algebra.TensorProduct.includeRight (algebraMap Γ Γ₀ x)) ∧
      (∀ a, s (algebraMap A Γ a) = algebraMap Γ Δ (algebraMap A Γ a)) ∧
      IsEffective s := by
  classical
  -- the étale lift `Δ` of `Γ₀ ⊗[B₀] Γ₀` along `Γ → Γ₀`
  obtain ⟨Δ, _, _, hΔ, ψ, hψ, hψker'⟩ :=
    etale_lift_along_surjection Γ Γ₀ (Γ₀ ⊗[B₀] Γ₀) hΓ₀
  have := hΔ
  let : Algebra A Δ := ((algebraMap Γ Δ).comp (algebraMap A Γ)).toAlgebra
  have : IsScalarTower A Γ Δ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hψker : RingHom.ker (ψ : Δ →+* Γ₀ ⊗[B₀] Γ₀) = J.map (algebraMap A Δ) := by
    rw [hψker', hΓ₀ker, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  -- the diagonal idempotent and its lift
  obtain ⟨ε₀, hε₀i, hε₀k, hε₀⟩ := exists_diagonal_idempotent (B₀ := B₀) (Γ₀ := Γ₀)
  have hdiag := ideal_le_map_of_surjective_of_injective I hsurjI hinjI
  obtain ⟨ε, hε, hεψ⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
    (ψ : Δ →+* Γ₀ ⊗[B₀] Γ₀)
    (fun x hx => isNilpotent_of_mem (isNilpotent_map_algebraMap hJ Δ) (hψker ▸ hx))
    ε₀ (hψ ε₀) hε₀i
  -- the second projection and the unit
  obtain ⟨s, hs1, hsψ, hsunit⟩ := exists_secondProjection I J ψ hΓ₀ hΓ₀ker hJ hψ hψker hε₀k hε₀
    hε hεψ hΓU hdiag
  have hone := one_sub_idempotent_mem I J ψ hψ hψker hε₀k hεψ hdiag
  -- the twisted copy `D` of `Δ` and the target `T` of the composition
  let : Algebra Γ (Twist Δ) := ((Twist.equiv Δ).toRingHom.comp s.toRingHom).toAlgebra
  have hσ : ∀ x, Twist.equiv Δ (s x) = algebraMap Γ (Twist Δ) x := fun _ => rfl
  let ι₃ : Γ →+* Twist (Δ ⊗[Γ] Twist Δ) :=
    (Twist.equiv _).toRingHom.comp
      ((Algebra.TensorProduct.includeRight (R := Γ) (A := Δ) (B := Twist Δ)).toRingHom.comp
        ((Twist.equiv Δ).toRingHom.comp (algebraMap Γ Δ)))
  let : Algebra Γ (Twist (Δ ⊗[Γ] Twist Δ)) := ι₃.toAlgebra
  let : Algebra A (Twist (Δ ⊗[Γ] Twist Δ)) := (ι₃.comp (algebraMap A Γ)).toAlgebra
  have : IsScalarTower A Γ (Twist (Δ ⊗[Γ] Twist Δ)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hτ : ∀ x, Twist.equiv (Δ ⊗[Γ] Twist Δ) (1 ⊗ₜ Twist.equiv Δ (algebraMap Γ Δ x)) =
      algebraMap Γ (Twist (Δ ⊗[Γ] Twist Δ)) x := fun _ => rfl
  set m := composition J ψ hΓ₀ hΓ₀ker s (Twist.equiv Δ) hσ (Twist.equiv (Δ ⊗[Γ] Twist Δ)) hτ hJ
    hψker hsψ
  have hms := composition_secondProjection I J ψ hΓ₀ hΓ₀ker s (Twist.equiv Δ) hσ
    (Twist.equiv (Δ ⊗[Γ] Twist Δ)) hτ hJ hψker hsψ hε hs1 hone hΓU
  -- the ideal `K = J Γ`
  set K := J.map (algebraMap A Γ)
  have hK : K.map s.toRingHom = extJ Δ K := by
    change (J.map (algebraMap A Γ)).map s.toRingHom = (J.map (algebraMap A Γ)).map (algebraMap Γ Δ)
    rw [Ideal.map_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    congr 1
    ext a
    exact s.commutes a
  obtain ⟨n, hn⟩ := isNilpotent_map_algebraMap hJ Γ
  -- the reduced groupoid is the Čech groupoid of `B₀ → Γ₀`
  let eB : Γ₀ ≃+* Γ ⧸ K :=
    (RingHom.quotientKerEquivOfSurjective hΓ₀).symm.trans (Ideal.quotEquivOfEq hΓ₀ker)
  let ψr : Δ →+* Γ₀ ⊗[B₀] Γ₀ := ψ
  have hψr : Function.Surjective ψr := hψ
  have hkerK : RingHom.ker ψr = extJ Δ K := by
    change RingHom.ker (ψ : Δ →+* Γ₀ ⊗[B₀] Γ₀) = _
    rw [hψker', hΓ₀ker]
  let eC : Γ₀ ⊗[B₀] Γ₀ ≃+* Δ ⧸ extJ Δ K :=
    (RingHom.quotientKerEquivOfSurjective hψr).symm.trans (Ideal.quotEquivOfEq hkerK)
  have heB : ∀ x, eB (algebraMap Γ Γ₀ x) = Ideal.Quotient.mk K x := fun x => by
    simp [eB, Ideal.quotEquivOfEq_mk]
  have heC : ∀ d, eC (ψ d) = Ideal.Quotient.mk (extJ Δ K) d := fun d => by
    simp only [eC, RingEquiv.trans_apply]
    rw [show ψ d = ψr d from rfl, RingHom.quotientKerEquivOfSurjective_symm_apply,
      Ideal.quotEquivOfEq_mk]
  have h₀ : IsEffective (s₀ s.toRingHom K hK) := by
    refine IsEffective.of_ringEquiv _ eB eC (fun b => ?_) (fun b => ?_)
      (isEffective_includeRight (B₀ := B₀) (Γ₀ := Γ₀))
    · obtain ⟨x, rfl⟩ := hΓ₀ b
      rw [show algebraMap Γ₀ (Γ₀ ⊗[B₀] Γ₀) (algebraMap Γ Γ₀ x) = ψ (algebraMap Γ Δ x) by
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply Γ Γ₀ (Γ₀ ⊗[B₀] Γ₀)], heC, heB]
      rfl
    · obtain ⟨x, rfl⟩ := hΓ₀ b
      rw [show Algebra.TensorProduct.includeRight.toRingHom (algebraMap Γ Γ₀ x) = ψ (s x) from
        (hsψ x).symm, heC, heB, s₀_mk]
      rfl
  have heff := isEffective_of_pow_eq_bot s.toRingHom (Twist.equiv Δ) hσ
    (unit J ψ hΓ₀ hΓ₀ker hJ).toRingHom hsunit (fun x => (unit J ψ hΓ₀ hΓ₀ker hJ).commutes x)
    ((Twist.equiv (Δ ⊗[Γ] Twist Δ)).symm.toRingHom.comp m.toRingHom)
    (fun x => by
      change (Twist.equiv (Δ ⊗[Γ] Twist Δ)).symm (m (s x)) = _
      rw [hms]
      rfl)
    (fun x => by
      change (Twist.equiv (Δ ⊗[Γ] Twist Δ)).symm (m (algebraMap Γ Δ x)) = _
      rw [AlgHom.commutes, ← hτ]
      rfl)
    K hK hn h₀
  exact ⟨Δ, inferInstance, inferInstance, hΔ, ψ, s.toRingHom, hψ, hkerK, hsψ,
    fun a => by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      IsScalarTower.algebraMap_apply A Γ Δ], heff⟩

end Stacks.Etale.PushoutLift

end
