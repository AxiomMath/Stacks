module

public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The fibres of the differentials of a locally standard smooth algebra

Let `B` be an `A`-algebra which is locally standard smooth of relative dimension `n`
(`RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)`, the ring-level form of
`AlgebraicGeometry.SmoothOfRelativeDimension n`). Then at every prime `q` of `B` the fibre
`κ(q) ⊗[B] Ω[B⁄A]` has dimension `n`: on a standard open `D(t) ∋ q` the differentials
`Ω[B_t⁄A] = B_t ⊗[B] Ω[B⁄A]` are free of rank `n`. The property is stable under base change
`A ⟶ A'`.

This is used for the divisor, finite étale over the base, of a family of smooth curves along
which the Gysin map of `R² g_!` is taken in the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): with `n = 1` the fibres of the
differentials do not vanish.

## Main results

* `Algebra.finrank_residueField_tensor_kaehlerDifferential_of_locally`.
* `Algebra.nontrivial_residueField_tensor_kaehlerDifferential_of_locally`.
* `RingHom.locally_isStandardSmoothOfRelativeDimension_tensorProduct`.
-/

public section

universe u

open TensorProduct

namespace Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- **The fibres of `Ω[B⁄A]` of a locally standard smooth algebra of relative dimension `n` have
dimension `n`.** -/
theorem finrank_residueField_tensor_kaehlerDifferential_of_locally {n : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap A B))
    (q : Ideal B) [q.IsPrime] :
    Module.finrank q.ResidueField (q.ResidueField ⊗[B] Ω[B⁄A]) = n := by
  obtain ⟨s, hs, hloc⟩ := h
  obtain ⟨t, hts, htq⟩ : ∃ t ∈ s, t ∉ q := by
    by_contra! H
    exact ‹q.IsPrime›.ne_top (top_le_iff.1 (hs ▸ Ideal.span_le.2 H))
  have hst := hloc t hts
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    at hst
  have hu : IsUnit (algebraMap B q.ResidueField t) := by
    rw [isUnit_iff_ne_zero, ne_eq, Ideal.algebraMap_residueField_eq_zero]
    exact htq
  have : Nontrivial (Localization.Away t) := (IsLocalization.Away.lift t hu).domain_nontrivial
  have := hst
  have : IsStandardSmooth A (Localization.Away t) := hst.isStandardSmooth
  have : Module.Free (Localization.Away t) Ω[Localization.Away t⁄A] := inferInstance
  have hrank : Module.finrank (Localization.Away t) Ω[Localization.Away t⁄A] = n := by
    rw [Module.finrank, IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n,
      Cardinal.toNat_natCast]
  -- `κ(q)` is a `B_t`-algebra
  let : Algebra (Localization.Away t) q.ResidueField :=
    (IsLocalization.Away.lift t hu).toAlgebra
  have : IsScalarTower B (Localization.Away t) q.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq t hu x).symm
  let e : q.ResidueField ⊗[B] Ω[B⁄A] ≃ₗ[q.ResidueField]
      q.ResidueField ⊗[Localization.Away t] Ω[Localization.Away t⁄A] :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B (Localization.Away t) q.ResidueField
      q.ResidueField Ω[B⁄A]).symm ≪≫ₗ
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B
        (Localization.Away t)).baseChange _ _ _ _
  rw [e.finrank_eq, Module.finrank_baseChange, hrank]

/-- **The fibres of `Ω[B⁄A]` of a locally standard smooth algebra of positive relative dimension
do not vanish.** -/
theorem nontrivial_residueField_tensor_kaehlerDifferential_of_locally {n : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (n + 1)) (algebraMap A B))
    (q : Ideal B) [q.IsPrime] :
    Nontrivial (q.ResidueField ⊗[B] Ω[B⁄A]) :=
  Module.nontrivial_of_finrank_eq_succ
    (finrank_residueField_tensor_kaehlerDifferential_of_locally h q)

end Algebra

/-- **Locally standard smooth of relative dimension `n` is stable under base change.** -/
theorem RingHom.locally_isStandardSmoothOfRelativeDimension_tensorProduct {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] {n : ℕ} (A' : Type u) [CommRing A'] [Algebra A A']
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap A B)) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap A' (A' ⊗[A] B)) :=
  (RingHom.locally_isStableUnderBaseChange RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    (RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n)).tensorProduct A' h
