module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsToPairs

/-!
# The first-order comparison datum of a module with coordinate operators

Let `(D, J, γ)` be a divided power ring over `A`, `d : D → Ω` a divided power derivation and
`d x_c ∈ Ω` a family of differentials.  Given operators `θ_c` on a `D`-module `M` with finitely
many `θ_c(x)` nonzero for each `x`, the map

`ε(x) = 1 ⊗ x - ∑_c d x_c ⊗ θ_c(x) : M → (D ⊕ Ω) ⊗_D M`

is a first-order comparison datum (`Crystalline.FirstOrderComparison`) as soon as the `θ_c` obey
the Leibniz rule `θ_c(a x) = a θ_c(x) + δ_c(a) x` for coefficients `δ_c(a)` with
`d a ⊗ x = - ∑_c d x_c ⊗ δ_c(a) x`.  This is the shape in which the proof of
[Stacks, Lemma 60.17.3, Tag 07JG] produces the connection of a crystal: `θ_c` is the coefficient
of `ξ_c` in the Taylor expansion over `D(1)`, and `D(1) → D ⊕ Ω` sends `ξ_c` to `-d x_c`.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public section

open scoped TensorProduct

universe uA u v w uI

noncomputable section

namespace Crystalline

variable {A : Type uA} [CommRing A] (D : DividedPowerRing.{u}) {g : A →+* D} (Omega : Type v)
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  (d : DividedPowerDerivation A D g Omega) {ι : Type uI} (dx : ι → Omega)
  {M : Type w} [AddCommGroup M] [Module D M] (θ : M →+ (ι →₀ M))

/-- The map `x ↦ 1 ⊗ x - ∑_c d x_c ⊗ θ_c(x)`. -/
def coordinateComparisonFun (x : M) : firstOrderExtension D Omega ⊗[D] M :=
  (1 : firstOrderExtension D Omega) ⊗ₜ x -
    (θ x).sum fun c y ↦ (TrivSqZeroExt.inr (dx c) : firstOrderExtension D Omega) ⊗ₜ y

/-- The map, as a sum over any finite set of indices containing the support. -/
theorem coordinateComparisonFun_eq (x : M) (T : Finset ι)
    (hT : (θ x).support ⊆ T) :
    coordinateComparisonFun D Omega dx θ x = (1 : firstOrderExtension D Omega) ⊗ₜ x -
      ∑ c ∈ T, (TrivSqZeroExt.inr (dx c) : firstOrderExtension D Omega) ⊗ₜ θ x c := by
  classical
  rw [coordinateComparisonFun, Finsupp.sum_of_support_subset _ hT _
    (fun c _ ↦ TensorProduct.tmul_zero _ _)]

/-- The map `x ↦ 1 ⊗ x - ∑_c d x_c ⊗ θ_c(x)` is additive in `x`. -/
theorem coordinateComparisonFun_add (x y : M) :
    coordinateComparisonFun D Omega dx θ (x + y) =
      coordinateComparisonFun D Omega dx θ x + coordinateComparisonFun D Omega dx θ y := by
  rw [coordinateComparisonFun, coordinateComparisonFun, coordinateComparisonFun, map_add,
    Finsupp.sum_add_index' (fun c ↦ TensorProduct.tmul_zero _ _)
      (fun c y₁ y₂ ↦ TensorProduct.tmul_add _ _ _), TensorProduct.tmul_add]
  abel

/-- The reduction `(D ⊕ Ω) ⊗_D M → M` sends `1 ⊗ x - ∑_c d x_c ⊗ θ_c(x)` back to `x`. -/
theorem firstOrderReduction_coordinateComparisonFun (x : M) :
    firstOrderReduction D Omega M (coordinateComparisonFun D Omega dx θ x) = x := by
  rw [coordinateComparisonFun, map_sub, map_finsuppSum, firstOrderReduction_tmul]
  simp only [firstOrderReduction_tmul, TrivSqZeroExt.fst_inr, zero_smul,
    TrivSqZeroExt.fst_one, one_smul]
  rw [Finsupp.sum, Finset.sum_const_zero, sub_zero]

/-- Scalars of `D` move across the tensor product on the `Ω` part: `b ω ⊗ x = ω ⊗ b x`. -/
private theorem inr_smul_tmul_coord {Ω : Type v} [AddCommGroup Ω] [Module D Ω] (b : D) (ω : Ω)
    (x : M) : (TrivSqZeroExt.inr (b • ω) : TrivSqZeroExt D Ω) ⊗ₜ[D] x =
      (TrivSqZeroExt.inr ω : TrivSqZeroExt D Ω) ⊗ₜ (b • x) := by
  rw [← TensorProduct.smul_tmul]
  congr 1
  ext <;> simp

/-- `p₁(a) · (1 ⊗ x) = 1 ⊗ a x + d a ⊗ x`. -/
theorem firstOrderP₁_smul_one_tmul_coord (a : D) (x : M) :
    firstOrderP₁ A D g Omega d a • ((1 : firstOrderExtension D Omega) ⊗ₜ[D] x) =
      (1 : firstOrderExtension D Omega) ⊗ₜ (a • x) +
        (TrivSqZeroExt.inr (d a) : firstOrderExtension D Omega) ⊗ₜ x := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  change (TrivSqZeroExt.inl a + TrivSqZeroExt.inr (d a) : firstOrderExtension D Omega) ⊗ₜ[D] x = _
  rw [TensorProduct.add_tmul, ← TensorProduct.smul_tmul]
  congr 2
  ext <;> simp

/-- `p₁(a) · (d x_c ⊗ y) = d x_c ⊗ a y`. -/
theorem firstOrderP₁_smul_inr_tmul_coord (a : D) (ω : Omega) (y : M) :
    firstOrderP₁ A D g Omega d a • ((TrivSqZeroExt.inr ω : firstOrderExtension D Omega) ⊗ₜ[D] y) =
      (TrivSqZeroExt.inr ω : firstOrderExtension D Omega) ⊗ₜ (a • y) := by
  rw [TensorProduct.smul_tmul', ← inr_smul_tmul_coord]
  congr 1
  ext <;> simp [firstOrderP₁]

/-- **Naturality**: a `D`-linear map carrying the coordinate operators into one another carries
the comparison maps into one another. -/
theorem lTensor_coordinateComparisonFun {M' : Type w} [AddCommGroup M'] [Module D M']
    (θ' : M' →+ (ι →₀ M')) (φ : M →ₗ[D] M')
    (hφ : ∀ x, θ' (φ x) = (θ x).mapRange φ (map_zero φ)) (x : M) :
    LinearMap.lTensor (firstOrderExtension D Omega) φ (coordinateComparisonFun D Omega dx θ x) =
      coordinateComparisonFun D Omega dx θ' (φ x) := by
  rw [coordinateComparisonFun, coordinateComparisonFun, hφ, map_sub, LinearMap.lTensor_tmul,
    map_finsuppSum, Finsupp.sum_mapRange_index (fun _ ↦ TensorProduct.tmul_zero _ _)]
  simp only [LinearMap.lTensor_tmul]

omit [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega] in
/-- Moving a combination of the `d x_c` across the tensor product. -/
theorem inr_neg_sum_smul_tmul (T : Finset ι) (b : ι → D) (x : M) :
    (TrivSqZeroExt.inr (-∑ c ∈ T, b c • dx c) : firstOrderExtension D Omega) ⊗ₜ[D] x =
      -∑ c ∈ T, (TrivSqZeroExt.inr (dx c) : firstOrderExtension D Omega) ⊗ₜ (b c • x) := by
  rw [TrivSqZeroExt.inr_neg, TensorProduct.neg_tmul]
  congr 1
  rw [← TrivSqZeroExt.inrHom_apply (R := D), map_sum, TensorProduct.sum_tmul]
  simp only [TrivSqZeroExt.inrHom_apply, inr_smul_tmul_coord]

/-- **The first-order comparison datum of a module with coordinate operators obeying the Leibniz
rule.** -/
def coordinateComparison
    (hleib : ∀ (a : D) (x : M), ∃ δ : ι →₀ D,
      (∀ c, θ (a • x) c = a • θ x c + δ c • x) ∧
      (TrivSqZeroExt.inr (d a) : firstOrderExtension D Omega) ⊗ₜ[D] x =
        -δ.sum fun c b ↦ (TrivSqZeroExt.inr (dx c) : firstOrderExtension D Omega) ⊗ₜ (b • x)) :
    FirstOrderComparison A D g Omega d M where
  toFun := coordinateComparisonFun D Omega dx θ
  map_add' := coordinateComparisonFun_add D Omega dx θ
  reduction' := firstOrderReduction_coordinateComparisonFun D Omega dx θ
  semilinear' a x := by
    classical
    obtain ⟨δ, hθ, hd⟩ := hleib a x
    let T : Finset ι := (θ x).support ∪ (θ (a • x)).support ∪ δ.support
    have hT₁ : (θ x).support ⊆ T := fun c hc ↦
      Finset.mem_union_left _ (Finset.mem_union_left _ hc)
    have hT₂ : (θ (a • x)).support ⊆ T := fun c hc ↦
      Finset.mem_union_left _ (Finset.mem_union_right _ hc)
    have hT₃ : δ.support ⊆ T := fun c hc ↦ Finset.mem_union_right _ hc
    rw [coordinateComparisonFun_eq D Omega dx θ _ T hT₂,
      coordinateComparisonFun_eq D Omega dx θ _ T hT₁,
      smul_sub, Finset.smul_sum, firstOrderP₁_smul_one_tmul_coord, hd,
      Finsupp.sum_of_support_subset _ hT₃ _ (fun c _ ↦ by rw [zero_smul, TensorProduct.tmul_zero])]
    simp only [firstOrderP₁_smul_inr_tmul_coord, hθ, TensorProduct.tmul_add, Finset.sum_add_distrib]
    abel

/-- The datum `coordinateComparison` evaluates to `coordinateComparisonFun`. -/
@[simp] theorem coordinateComparison_apply
    (hleib : ∀ (a : D) (x : M), ∃ δ : ι →₀ D,
      (∀ c, θ (a • x) c = a • θ x c + δ c • x) ∧
      (TrivSqZeroExt.inr (d a) : firstOrderExtension D Omega) ⊗ₜ[D] x =
        -δ.sum fun c b ↦ (TrivSqZeroExt.inr (dx c) : firstOrderExtension D Omega) ⊗ₜ (b • x))
    (x : M) :
    coordinateComparison D Omega d dx θ hleib x = coordinateComparisonFun D Omega dx θ x :=
  rfl

end Crystalline

end
