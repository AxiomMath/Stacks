module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveHigherVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification

/-!
# The higher direct images along the complement of a divisor are supported on the divisor

Let `i : Z ⟶ U` be a closed immersion, `j : U₀ ⟶ U` a quasi-compact open immersion onto the
complement of `Z`, and `N` an integer invertible on `U`. For a sheaf `F` of `ℤ/N`-modules on
`U₀_étale` and `q > 0` the higher direct image `R^q j_* F` restricts to zero on `U₀` (smooth base
change along `j` itself,
`Stacks.EtaleCohomology.Purity.isZero_restriction_rightDerived_of_isOpenImmersion`), so it is
supported on `Z`: the unit `R^q j_* F ⟶ i_* i⁻¹ R^q j_* F` is an isomorphism
(`Stacks.EtaleCohomology.Purity.isIso_unit_rightDerived_directImage_of_isOpenImmersion`).

This is step `(A)` of the tower form of cohomological purity in codimension one, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): `R¹ j_*(j⁻¹ H) = i_* i⁻¹ R¹ j_*(j⁻¹ H)`.

## Main results

* `Stacks.EtaleCohomology.Purity.isZero_restriction_rightDerived_directImage_of_isOpenImmersion`.
* `Stacks.EtaleCohomology.Purity.isIso_unit_rightDerived_directImage_of_isOpenImmersion`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Purity

variable {Z U U₀ : Scheme.{u}} {N : ℕ} (hN0 : 0 < N) (hN : IsUnit ((N : ℤ) : Γ(U, ⊤)))
  (j : U₀ ⟶ U) [IsOpenImmersion j] [QuasiCompact j]

include hN0 hN in
/-- **`R^q j_* F` vanishes on `U₀` for `q > 0`**, for a sheaf `F` of `ℤ/N`-modules on `U₀` and
`N` invertible on `U`. -/
theorem isZero_restriction_rightDerived_directImage_of_isOpenImmersion
    (F : EtaleModules.{u, 0} (ZMod N) U₀) (q : ℕ) (hq : 0 < q) :
    IsZero ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj
      (((etaleModuleDirectImage.{u, 0} (ZMod N) j).rightDerived q).obj F)) := by
  let Fa := (etaleModuleForgetAb.{u, 0} (ZMod N) U₀).obj F
  have htors : ∀ (t : GeometricPoint U₀) (a : (smallEtaleStalkAb t.hom).obj Fa),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(U, ⊤)) ∧ n • a = 0 := fun t a =>
    ⟨N, hN0, hN, nsmul_eq_zero_stalk_of_nsmul_id (nsmul_id_etaleModuleForgetUniv_zmod F) t a⟩
  exact (isZero_etaleModuleInverseImage_rightDerived_of_ab (ZMod N) j j F q
    ((isZero_restriction_rightDerived_of_isOpenImmersion j Fa htors q hq).of_iso
      ((smallEtalePullbackAbIsoEtaleRestriction j).app _))).of_iso
    ((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod N) j).app _).symm

include hN0 hN in
/-- **`R^q j_* F` is supported on the closed complement `Z` of `U₀`**: for `q > 0` the unit
`R^q j_* F ⟶ i_* i⁻¹ R^q j_* F` of `i⁻¹ ⊣ i_*` is an isomorphism, for `F` a sheaf of
`ℤ/N`-modules on `U₀` and `N` invertible on `U`. -/
theorem isIso_unit_rightDerived_directImage_of_isOpenImmersion (i : Z ⟶ U) [IsClosedImmersion i]
    (hj : Set.range j.base = (Set.range i.base)ᶜ) (F : EtaleModules.{u, 0} (ZMod N) U₀) (q : ℕ)
    (hq : 0 < q) :
    IsIso ((etaleModuleInverseImageAdj.{u, 0} (ZMod N) i).unit.app
      (((etaleModuleDirectImage.{u, 0} (ZMod N) j).rightDerived q).obj F)) :=
  isIso_etaleModuleInverseImageAdj_unit_app_of_isZero (ZMod N) i j hj _
    (isZero_restriction_rightDerived_directImage_of_isOpenImmersion hN0 hN j F q hq)

end Stacks.EtaleCohomology.Purity

end
