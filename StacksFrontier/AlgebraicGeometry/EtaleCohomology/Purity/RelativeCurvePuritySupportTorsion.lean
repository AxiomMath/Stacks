module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePuritySupport

/-!
# The higher direct images of torsion sheaves along the complement of a divisor

Let `i : Z ⟶ U` be a closed immersion, `j : U₀ ⟶ U` a quasi-compact open immersion onto the
complement of `Z`, and `N` an integer invertible on `U`. For a sheaf `F` of `Λ`-modules on
`U₀_étale` killed by `N` (any ring `Λ`) and `q > 0`, the higher direct image `R^q j_* F` restricts
to zero on `U₀`, so the unit `R^q j_* F ⟶ i_* i⁻¹ R^q j_* F` is an isomorphism
(`Stacks.EtaleCohomology.Purity.isIso_unit_rightDerived_directImage_of_nsmul_id_eq_zero`).

This is step `(A)` of the tower form of cohomological purity in codimension one
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) for the levels of an ℓ-adic sheaf, read as
sheaves of `ℤ_ℓ`-modules killed by `ℓⁿ⁺¹`.

## Main results

* `Stacks.EtaleCohomology.Purity.isZero_restriction_rightDerived_directImage_of_nsmul_id_eq_zero`.
* `Stacks.EtaleCohomology.Purity.isIso_unit_rightDerived_directImage_of_nsmul_id_eq_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Purity

variable (Λ : Type) [Ring Λ] {Z U U₀ : Scheme.{u}} {N : ℕ} (hN0 : 0 < N)
  (hN : IsUnit ((N : ℤ) : Γ(U, ⊤))) (j : U₀ ⟶ U) [IsOpenImmersion j] [QuasiCompact j]

include hN0 hN in
/-- **`R^q j_* F` vanishes on `U₀` for `q > 0`**, for a sheaf `F` of `Λ`-modules on `U₀` killed by
an integer `N` invertible on `U`. -/
theorem isZero_restriction_rightDerived_directImage_of_nsmul_id_eq_zero
    (F : EtaleModules.{u, 0} Λ U₀) (hF : N • 𝟙 F = 0) (q : ℕ) (hq : 0 < q) :
    IsZero ((etaleModuleRestriction.{u, 0} Λ j).obj
      (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj F)) := by
  let Fa := (etaleModuleForgetAb.{u, 0} Λ U₀).obj F
  have hFa : N • 𝟙 Fa = 0 := by
    rw [← (etaleModuleForgetAb.{u, 0} Λ U₀).map_id, ← (etaleModuleForgetAb.{u, 0} Λ U₀).map_nsmul,
      hF, Functor.map_zero]
  have htors : ∀ (t : GeometricPoint U₀) (a : (smallEtaleStalkAb t.hom).obj Fa),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(U, ⊤)) ∧ n • a = 0 := fun t a =>
    ⟨N, hN0, hN, nsmul_eq_zero_stalk_of_nsmul_id hFa t a⟩
  exact (isZero_etaleModuleInverseImage_rightDerived_of_ab Λ j j F q
    ((isZero_restriction_rightDerived_of_isOpenImmersion j Fa htors q hq).of_iso
      ((smallEtalePullbackAbIsoEtaleRestriction j).app _))).of_iso
    ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).app _).symm

include hN0 hN in
/-- **`R^q j_* F` is supported on the closed complement `Z` of `U₀`**: for `q > 0` the unit
`R^q j_* F ⟶ i_* i⁻¹ R^q j_* F` of `i⁻¹ ⊣ i_*` is an isomorphism, for `F` a sheaf of `Λ`-modules on
`U₀` killed by an integer `N` invertible on `U`. -/
theorem isIso_unit_rightDerived_directImage_of_nsmul_id_eq_zero (i : Z ⟶ U)
    [IsClosedImmersion i] (hj : Set.range j.base = (Set.range i.base)ᶜ)
    (F : EtaleModules.{u, 0} Λ U₀) (hF : N • 𝟙 F = 0) (q : ℕ) (hq : 0 < q) :
    IsIso ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app
      (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj F)) :=
  isIso_etaleModuleInverseImageAdj_unit_app_of_isZero Λ i j hj _
    (isZero_restriction_rightDerived_directImage_of_nsmul_id_eq_zero Λ hN0 hN j F hF q hq)

end Stacks.EtaleCohomology.Purity

end
