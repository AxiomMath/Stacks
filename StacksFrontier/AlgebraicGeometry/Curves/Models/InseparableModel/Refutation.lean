module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ComponentIdentification
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ComponentGeometry
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ComponentGenus
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ComponentGlobalSections

/-!
# The separability clause of Stacks Tag 0CEE fails

For the regular proper model `Stacks.Models.InseparableModel.situation` of `ℙ¹_K` over
`R = 𝔽₂(t)⟦π⟧`, the special fibre is `C₁ ∪ E` with `C₁ ≅ ℙ¹_k` and `E ≅ ℙ¹_κ`, `κ = k(√t)`,
meeting transversally in one `κ`-point. A section of the model gives a smooth `k`-rational point
`x ∈ C₁ \ E`; `dim_k H¹((X_k)_red, 𝒪) = 0`, so equality holds in Tag 0CEA, but
`H⁰(E, 𝒪_E) = κ` is not separable over `k`.

## Main results

All names below are in the namespace `Stacks.Models`.

* `InseparableModel.finrank_cohomology_reduction_eq_zero`
* `RegularProperModelSituation.topologicalGenus_add_geometricGenus_eq_of_finrank_eq_zero`
* `RegularProperModelSituation.not_forall_isSeparable_of_genus_equality`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Models.RegularProperModelSituation

/-- **Equality in Tag 0CEA when `H¹((X_k)_red, 𝒪) = 0`**: the bound of Tag 0CEA and the
nonnegativity of both invariants. -/
theorem topologicalGenus_add_geometricGenus_eq_of_finrank_eq_zero
    (S : RegularProperModelSituation.{u}) (x : S.specialFiber)
    (hx : IsRationalPoint S.specialFiberToSpec x)
    (hsm : InfinitesimalLifting.SmoothAt S.specialFiberToSpec x)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (h0 : Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) = 0) :
    (S.associatedNumericalType n e).topologicalGenus +
        (geometricGenus S.k S.specialFiberToSpec : ℤ) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) := by
  have hle := S.topologicalGenus_add_geometricGenus_le_finrank_reduction x hx hsm n e
  have htop := (S.associatedNumericalType n e).topologicalGenus_nonneg
  rw [h0, Nat.cast_zero] at hle ⊢
  omega

end Stacks.Models.RegularProperModelSituation

namespace Stacks.Models.InseparableModel

/-- The `k`-point of the special fibre given by the section of the model is rational. -/
private theorem isRationalPoint_specialFiberSection_modelSection :
    IsRationalPoint situation.specialFiberToSpec
      ((RegularProperModelSituation.specialFiberSection (S := situation) modelSection
        modelSection_comp_X_to_R).base (IsLocalRing.closedPoint situation.k)) :=
  isRationalPoint_base_of_comp_eq_id _
    (RegularProperModelSituation.specialFiberSection_toSpec _ _) _

/-- A rational point of the special fibre does not lie on a component of weight `2`. -/
private theorem not_mem_of_weight_eq_two {x : situation.specialFiber}
    (hx : IsRationalPoint situation.specialFiberToSpec x)
    {Z : irreducibleComponents situation.specialFiber}
    (hw : situation.specialFiberComponentWeight Z = 2) : x ∉ Z.1 := fun hZ => by
  have := situation.specialFiberComponentWeight_eq_one_of_isRationalPoint Z x hx hZ
  omega

/-- `dim_k H¹((X_k)_red, 𝒪) = 0` for the model. -/
theorem finrank_cohomology_reduction_eq_zero :
    Module.finrank situation.k (cohomologyOverField situation.k
        (situation.specialFiber.reductionι ≫ situation.specialFiberToSpec)
        (SheafOfModules.unit situation.specialFiber.reduction.ringCatSheaf) 1) = 0 := by
  classical
  obtain ⟨ZC, ZE, hne, hall, hC, hE⟩ := specialFiber_components
  set x := (RegularProperModelSituation.specialFiberSection (S := situation) modelSection
    modelSection_comp_X_to_R).base (IsLocalRing.closedPoint situation.k)
  have hx : IsRationalPoint situation.specialFiberToSpec x :=
    isRationalPoint_specialFiberSection_modelSection
  have hwE : situation.specialFiberComponentWeight ZE = 2 :=
    (globalSections_of_eq_ker_jE hE (situation.specialFiberComponentToSpec ZE)
      (situation.specialFiberComponentToSpec_comp ZE)).2.1
  have hxC : x ∈ ZC.1 := by
    obtain ⟨Z, hZ⟩ := situation.exists_mem_specialFiberComponent x
    rcases hall Z with rfl | rfl
    · exact hZ
    · exact absurd hZ (not_mem_of_weight_eq_two hx hwE)
  have hwC := situation.specialFiberComponentWeight_eq_one_of_isRationalPoint ZC x hx hxC
  have hgC : situation.specialFiberComponentGenus ZC = 0 := by
    let := (situation.isField_and_finite_globalSections_specialFiberComponent ZC).1.toField
    exact genus_eq_zero_of_eq_ker_jC₁ hC _
  have hgE : situation.specialFiberComponentGenus ZE = 0 := by
    let := (situation.isField_and_finite_globalSections_specialFiberComponent ZE).1.toField
    exact genus_eq_zero_of_eq_ker_jE hE _
  have hg : ((situation.componentIntersectionIdeal ZE ZC).subschemeι ≫
      situation.specialFiberComponentToSpec ZE) ≫
        Spec.map (CommRingCat.ofHom (algebraMap situation.R situation.k)) =
      (situation.componentIntersectionIdeal ZE ZC).subschemeι ≫
        (situation.specialFiberComponentIdeal ZE).subschemeι ≫ situation.X_to_R := by
    rw [Category.assoc, situation.specialFiberComponentToSpec_comp]
  have hint : situation.specialFiberIntersectionMatrix ZE ZC ≤ 2 := by
    rw [situation.specialFiberIntersectionMatrix_eq_finrank_globalSections hne.symm,
      ← finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections]
    exact_mod_cast finrank_meet_le hE hC _ hg
  have h1 := situation.specialFiberDivisorEulerChar_one x hx
  have hfun : (fun _ : irreducibleComponents situation.specialFiber => (1 : ℕ)) =
      fun Z => if Z ∈ insert ZE ({ZC} : Finset _) then 1 else 0 := by
    funext Z
    rcases hall Z with rfl | rfl <;> simp
  rw [hfun, situation.specialFiberDivisorEulerChar_indicator_insert {ZC}
      (by simpa using hne.symm), situation.specialFiberDivisorEulerChar_indicator_singleton,
    Finset.sum_singleton, situation.eulerCharacteristic_specialFiberComponent_eq,
    situation.eulerCharacteristic_specialFiberComponent_eq, hwC, hwE, hgC, hgE] at h1
  omega

end Stacks.Models.InseparableModel

namespace Stacks.Models.RegularProperModelSituation

/-- **The separability clause of [Stacks, Tag 0CEE] (2) fails.** It is not true that, in every
situation of [Stacks, Tag 0C61] with a smooth `k`-rational point `x` of `X_k` and equality in
[Stacks, Tag 0CEA], every irreducible component `C` of `X_k` not through `x` has
`κ = H⁰(C, 𝒪_C)` separable over `k`: the model `Stacks.Models.InseparableModel.situation` has a
component `E ≅ ℙ¹_κ` with `κ = k(√t)` purely inseparable over `k = 𝔽₂(t)`. -/
theorem not_forall_isSeparable_of_genus_equality :
    ¬ ∀ (S : RegularProperModelSituation.{0}) (x : S.specialFiber)
      (_hx : IsRationalPoint S.specialFiberToSpec x)
      (_hsm : InfinitesimalLifting.SmoothAt S.specialFiberToSpec x)
      (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
      (_heq : (S.associatedNumericalType n e).topologicalGenus +
          (geometricGenus S.k S.specialFiberToSpec : ℤ) =
        Module.finrank S.k (cohomologyOverField S.k
          (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
          (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1))
      (Z : irreducibleComponents S.specialFiber), x ∉ Z.1 →
        letI : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
          (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
        letI : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
          ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
        Algebra.IsSeparable S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := by
  intro h
  classical
  obtain ⟨ZC, ZE, hne, hall, hC, hE⟩ := InseparableModel.specialFiber_components
  have hx := InseparableModel.isRationalPoint_specialFiberSection_modelSection
  have hsec := InseparableModel.globalSections_of_eq_ker_jE hE
    (InseparableModel.situation.specialFiberComponentToSpec ZE)
    (InseparableModel.situation.specialFiberComponentToSpec_comp ZE)
  have hxE := InseparableModel.not_mem_of_weight_eq_two hx hsec.2.1
  let e : Fin 2 ≃ irreducibleComponents InseparableModel.situation.specialFiber :=
    { toFun := ![ZC, ZE]
      invFun := fun Z => if Z = ZC then 0 else 1
      left_inv := fun i => by fin_cases i <;> simp [hne.symm]
      right_inv := fun Z => by rcases hall Z with rfl | rfl <;> simp [hne.symm] }
  exact hsec.2.2 (h InseparableModel.situation _ hx (smoothAt_specialFiberSection _ _) 2 e
    (topologicalGenus_add_geometricGenus_eq_of_finrank_eq_zero InseparableModel.situation _ hx
      (smoothAt_specialFiberSection _ _) 2 e InseparableModel.finrank_cohomology_reduction_eq_zero)
    ZE hxE)

end Stacks.Models.RegularProperModelSituation
