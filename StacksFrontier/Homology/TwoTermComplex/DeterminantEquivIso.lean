module

public import StacksFrontier.Homology.TwoTermComplex.LineBaseChange
import all StacksFrontier.Homology.TwoTermComplex.DeterminantLine
import all StacksFrontier.Homology.TwoTermComplex.DeterminantLine.Homotopy

/-!
# The determinant equivalence of an isomorphism of two-term complexes

An isomorphism of two-term complexes of finite projective modules is in particular a
degreewise-surjective quasi-isomorphism, so it has the determinant equivalence of Stacks 0FJJ.
This file computes it: it is the equivalence of determinant lines induced by the two
components, `TwoTermComplex.lineCongr`.

## Main results

* `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_eq_lineCongr`.

## References

* [Stacks Project, Tag 0FJJ](https://stacks.math.columbia.edu/tag/0FJJ)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace TwoTermComplex

variable {R : Type*} [CommRing R]

/-- An element of the exterior algebra of a module with one element is a scalar. -/
theorem exteriorAlgebra_eq_algebraMap_of_subsingleton {M : Type*} [AddCommGroup M] [Module R M]
    [Subsingleton M] (w : ExteriorAlgebra R M) :
    w = algebraMap R _ (ExteriorAlgebra.algebraMapInv w) := by
  induction w using ExteriorAlgebra.induction with
  | algebraMap r => simp
  | ι m => rw [Subsingleton.elim m 0]; simp
  | mul a b ha hb => rw [map_mul, map_mul, ← ha, ← hb]
  | add a b ha hb => rw [map_add, map_add, ← ha, ← hb]

section General

variable {K₁ K₀ L₁ L₀ : Type*}
variable [AddCommGroup K₁] [Module R K₁] [AddCommGroup K₀] [Module R K₀]
variable [AddCommGroup L₁] [Module R L₁] [AddCommGroup L₀] [Module R L₀]

/-- The composite of two morphisms of two-term complexes. -/
def Hom.comp {M₁ M₀ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₀] [Module R M₀]
    {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀} {d'' : M₁ →ₗ[R] M₀} (b : Hom d' d'') (a : Hom d d') :
    Hom d d'' where
  neg := b.neg.comp a.neg
  zero := b.zero.comp a.zero
  comm := by rw [LinearMap.comp_assoc, a.comm, ← LinearMap.comp_assoc, b.comm,
    LinearMap.comp_assoc]

/-- An isomorphism of two-term complexes is a quasi-isomorphism. -/
theorem isQuasiIso_of_equiv {X₁ X₀ Y₁ Y₀ : Type*} [AddCommGroup X₁] [Module R X₁]
    [AddCommGroup X₀] [Module R X₀] [AddCommGroup Y₁] [Module R Y₁] [AddCommGroup Y₀]
    [Module R Y₀] {x : X₁ →ₗ[R] X₀} {y : Y₁ →ₗ[R] Y₀} (e₁ : X₁ ≃ₗ[R] Y₁) (e₀ : X₀ ≃ₗ[R] Y₀)
    (h : y ∘ₗ e₁.toLinearMap = e₀.toLinearMap ∘ₗ x) :
    (⟨e₁.toLinearMap, e₀.toLinearMap, h.symm⟩ : Hom x y).IsQuasiIso := by
  constructor
  · constructor
    · intro u v huv
      exact Subtype.ext (e₁.injective (congrArg Subtype.val huv))
    · intro v
      refine ⟨⟨e₁.symm v, ?_⟩, Subtype.ext (by simp [Hom.hMinus])⟩
      rw [LinearMap.mem_ker]
      apply e₀.injective
      have := LinearMap.congr_fun h (e₁.symm v)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
      rw [← this, map_zero]
      exact v.2
  · constructor
    · intro u v huv
      induction u using Submodule.Quotient.induction_on with | H u => ?_
      induction v using Submodule.Quotient.induction_on with | H v => ?_
      have huv' : (Submodule.Quotient.mk (e₀ u) : Y₀ ⧸ LinearMap.range y) =
          Submodule.Quotient.mk (e₀ v) := huv
      rw [Submodule.Quotient.eq] at huv' ⊢
      obtain ⟨w, hw⟩ := huv'
      refine ⟨e₁.symm w, e₀.injective ?_⟩
      have := LinearMap.congr_fun h (e₁.symm w)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
      rw [← this, hw, map_sub]
    · intro v
      induction v using Submodule.Quotient.induction_on with | H v => ?_
      exact ⟨Submodule.Quotient.mk (e₀.symm v), by simp [Hom.hZero]⟩

/-- A composite of quasi-isomorphisms of two-term complexes is a quasi-isomorphism. -/
theorem Hom.isQuasiIso_comp {M₁ M₀ : Type*} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₀]
    [Module R M₀] {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀} {d'' : M₁ →ₗ[R] M₀} (a : Hom d d')
    (b : Hom d' d'') (hqa : a.IsQuasiIso) (hqb : b.IsQuasiIso) : (b.comp a).IsQuasiIso := by
  have hn : (b.comp a).hMinus = b.hMinus.comp a.hMinus := by ext x; rfl
  have hz : (b.comp a).hZero = b.hZero.comp a.hZero := by ext x; rfl
  rw [Hom.IsQuasiIso, hn, hz]
  exact ⟨hqb.1.comp hqa.1, hqb.2.comp hqa.2⟩

/-- A morphism conjugate to `a` by two isomorphisms is the composite of `a` with them. -/
private theorem eq_comp_comp_of_conj {M₁ M₀ N₁ N₀ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₀]
    [Module R N₀] {c : M₁ →ₗ[R] M₀} {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀} {c' : N₁ →ₗ[R] N₀}
    (a : Hom d d') (α₁ : M₁ ≃ₗ[R] K₁) (α₀ : M₀ ≃ₗ[R] K₀)
    (hα : d ∘ₗ α₁.toLinearMap = α₀.toLinearMap ∘ₗ c)
    (β₁ : L₁ ≃ₗ[R] N₁) (β₀ : L₀ ≃ₗ[R] N₀) (hβ : c' ∘ₗ β₁.toLinearMap = β₀.toLinearMap ∘ₗ d')
    (a' : Hom c c') (h₁ : a'.neg = β₁.toLinearMap ∘ₗ a.neg ∘ₗ α₁.toLinearMap)
    (h₀ : a'.zero = β₀.toLinearMap ∘ₗ a.zero ∘ₗ α₀.toLinearMap) :
    a' = (⟨β₁.toLinearMap, β₀.toLinearMap, hβ.symm⟩ : Hom d' c').comp
      (a.comp ⟨α₁.toLinearMap, α₀.toLinearMap, hα.symm⟩) := by
  cases a'
  simp only at h₁ h₀
  subst h₁ h₀
  rfl

/-- A morphism of two-term complexes conjugate to a quasi-isomorphism by two isomorphisms is a
quasi-isomorphism. -/
theorem isQuasiIso_conj {M₁ M₀ N₁ N₀ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₀]
    [Module R N₀] {c : M₁ →ₗ[R] M₀} {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀} {c' : N₁ →ₗ[R] N₀}
    (a : Hom d d') (hqa : a.IsQuasiIso)
    (α₁ : M₁ ≃ₗ[R] K₁) (α₀ : M₀ ≃ₗ[R] K₀) (hα : d ∘ₗ α₁.toLinearMap = α₀.toLinearMap ∘ₗ c)
    (β₁ : L₁ ≃ₗ[R] N₁) (β₀ : L₀ ≃ₗ[R] N₀) (hβ : c' ∘ₗ β₁.toLinearMap = β₀.toLinearMap ∘ₗ d')
    (a' : Hom c c') (h₁ : a'.neg = β₁.toLinearMap ∘ₗ a.neg ∘ₗ α₁.toLinearMap)
    (h₀ : a'.zero = β₀.toLinearMap ∘ₗ a.zero ∘ₗ α₀.toLinearMap) : a'.IsQuasiIso := by
  obtain rfl := eq_comp_comp_of_conj a α₁ α₀ hα β₁ β₀ hβ a' h₁ h₀
  exact Hom.isQuasiIso_comp _ _
    (Hom.isQuasiIso_comp _ _ (isQuasiIso_of_equiv α₁ α₀ hα) hqa) (isQuasiIso_of_equiv β₁ β₀ hβ)

/-- A morphism of two-term complexes conjugate to a degreewise-surjective one by two
isomorphisms is degreewise surjective. -/
theorem isDegreewiseSurjective_conj {M₁ M₀ N₁ N₀ : Type*} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₀]
    [Module R N₀] {c : M₁ →ₗ[R] M₀} {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀} {c' : N₁ →ₗ[R] N₀}
    (a : Hom d d') (ha : a.IsDegreewiseSurjective)
    (α₁ : M₁ ≃ₗ[R] K₁) (α₀ : M₀ ≃ₗ[R] K₀) (β₁ : L₁ ≃ₗ[R] N₁) (β₀ : L₀ ≃ₗ[R] N₀)
    (a' : Hom c c') (h₁ : a'.neg = β₁.toLinearMap ∘ₗ a.neg ∘ₗ α₁.toLinearMap)
    (h₀ : a'.zero = β₀.toLinearMap ∘ₗ a.zero ∘ₗ α₀.toLinearMap) :
    a'.IsDegreewiseSurjective :=
  ⟨h₁ ▸ β₁.surjective.comp (ha.1.comp α₁.surjective),
    h₀ ▸ β₀.surjective.comp (ha.2.comp α₀.surjective)⟩

/-- The exterior algebra map of a linear equivalence is cancelled by that of its inverse. -/
private theorem map_map_symm_apply {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (e : M ≃ₗ[R] N) (w : ExteriorAlgebra R N) :
    ExteriorAlgebra.map e.toLinearMap (ExteriorAlgebra.map e.symm.toLinearMap w) = w := by
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  simp

end General

variable {K₁ K₀ L₁ L₀ : Type*}
variable [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
variable [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
variable [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
variable [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]

/-- The determinant equivalence of a surjection of finite projective modules which is an
isomorphism, on an element of the determinant line of its (zero) kernel. -/
private theorem kernelDeterminantEquiv_val_of_equiv (e : K₁ ≃ₗ[R] L₁)
    [Module.Finite R (LinearMap.ker e.toLinearMap)]
    [Module.Projective R (LinearMap.ker e.toLinearMap)]
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker e.toLinearMap))
    (y : ProjectiveDeterminant.module (R := R) (M := L₁)) :
    ((kernelDeterminantEquiv e.toLinearMap e.surjective (x ⊗ₜ[R] y) :
      ProjectiveDeterminant.module (R := R) (M := K₁)) : ExteriorAlgebra R K₁) =
      ExteriorAlgebra.algebraMapInv x.1 •
        ExteriorAlgebra.map e.symm.toLinearMap y.1 := by
  have : Subsingleton (LinearMap.ker e.toLinearMap) := by
    rw [LinearEquiv.ker]
    infer_instance
  rw [kernelDeterminantEquiv_val, (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker e.toLinearMap).subtype e.toLinearMap
    (LinearMap.ker e.toLinearMap).injective_subtype e.toLinearMap.exact_subtype_ker_map
    e.surjective).property _ _ (ExteriorAlgebra.map e.symm.toLinearMap y.1)
    (by
      rw [determinantAnnihilatorEquiv_val, map_map_symm_apply]),
    determinantAnnihilatorEquiv_val, exteriorAlgebra_eq_algebraMap_of_subsingleton x.1,
    AlgHom.commutes, ← Algebra.smul_def]
  simp

/-- The inverse of the determinant equivalence of a linear equivalence, on the exterior
algebra. -/
theorem coe_mapEquiv_symm_apply (e : K₁ ≃ₗ[R] L₁)
    (y : ProjectiveDeterminant.module (R := R) (M := L₁)) :
    (((ProjectiveDeterminant.mapEquiv e).symm y :
      ProjectiveDeterminant.module (R := R) (M := K₁)) : ExteriorAlgebra R K₁) =
      ExteriorAlgebra.map e.symm.toLinearMap y.1 := by
  have h : (ProjectiveDeterminant.mapEquiv e).symm y =
      ProjectiveDeterminant.map (fun p => (ProjectiveDeterminant.rankAtStalk_congr e p).symm)
        e.symm.toLinearMap y := by
    apply (ProjectiveDeterminant.mapEquiv e).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    exact (map_map_symm_apply e y.1).symm
  rw [h]
  rfl

/-- **The determinant equivalence of an isomorphism of two-term complexes** is the equivalence
of determinant lines induced by its two components. -/
theorem determinantEquivOfSurjectiveQuasiIso_eq_lineCongr (d : K₁ →ₗ[R] K₀) (d' : L₁ →ₗ[R] L₀)
    (a : Hom d d') (e₁ : K₁ ≃ₗ[R] L₁) (e₀ : K₀ ≃ₗ[R] L₀) (h₁ : a.neg = e₁.toLinearMap)
    (h₀ : a.zero = e₀.toLinearMap) (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) :
    letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
    letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
    letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
    letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
    (determinantEquivOfSurjectiveQuasiIso d d' a ha hqa).equiv = lineCongr d d' e₁ e₀ := by
  obtain ⟨neg, zero, comm⟩ := a
  dsimp only at h₁ h₀
  subst h₁ h₀
  let : Module.Finite R (LinearMap.ker e₁.toLinearMap) := kernel_finite _ ha.1
  let : Module.Projective R (LinearMap.ker e₁.toLinearMap) := kernel_projective _ ha.1
  let : Module.Finite R (LinearMap.ker e₀.toLinearMap) := kernel_finite _ ha.2
  let : Module.Projective R (LinearMap.ker e₀.toLinearMap) := kernel_projective _ ha.2
  symm
  apply (determinantEquivOfSurjectiveQuasiIso d d' ⟨e₁.toLinearMap, e₀.toLinearMap, comm⟩
    ha hqa).unique
  intro φ x y
  apply Subtype.ext
  change ((kernelDeterminantEquiv e₀.toLinearMap e₀.surjective _ :
      ProjectiveDeterminant.module (R := R) (M := K₀)) : ExteriorAlgebra R K₀) =
    ((φ (kernelDeterminantEquiv e₁.toLinearMap e₁.surjective (x ⊗ₜ[R] y)) :
      ProjectiveDeterminant.module (R := R) (M := K₀)) : ExteriorAlgebra R K₀)
  have hkn : kernelDeterminantEquiv e₁.toLinearMap e₁.surjective (x ⊗ₜ[R] y) =
      ExteriorAlgebra.algebraMapInv x.1 • (ProjectiveDeterminant.mapEquiv e₁).symm y := by
    apply Subtype.ext
    rw [kernelDeterminantEquiv_val_of_equiv, Submodule.coe_smul, coe_mapEquiv_symm_apply]
  rw [kernelDeterminantEquiv_val_of_equiv, hkn, map_smul, Submodule.coe_smul]
  congr 1
  · change ExteriorAlgebra.algebraMapInv (ExteriorAlgebra.map _ x.1) = _
    induction x.1 using ExteriorAlgebra.induction with
    | algebraMap r => simp
    | ι m => simp [ExteriorAlgebra.algebraMapInv]
    | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  · change ExteriorAlgebra.map e₀.symm.toLinearMap
      (ExteriorAlgebra.map e₀.toLinearMap (φ ((ProjectiveDeterminant.mapEquiv e₁).symm y)).1) = _
    simpa using map_map_symm_apply e₀.symm _

/-! ### The determinant equivalence as a named equivalence -/

/-- The determinant equivalence `det(K) ≅ det(L)` of a degreewise-surjective quasi-isomorphism
of two-term complexes of finite projective modules (Stacks 0FJJ). -/
def detEquiv {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀} (a : Hom d d')
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) :
    determinantLine d ≃ₗ[R] determinantLine d' :=
  letI : Module.Finite R (LinearMap.ker a.neg) := kernel_finite a.neg ha.1
  letI : Module.Projective R (LinearMap.ker a.neg) := kernel_projective a.neg ha.1
  letI : Module.Finite R (LinearMap.ker a.zero) := kernel_finite a.zero ha.2
  letI : Module.Projective R (LinearMap.ker a.zero) := kernel_projective a.zero ha.2
  (determinantEquivOfSurjectiveQuasiIso d d' a ha hqa).equiv

/-- The determinant equivalence of an isomorphism is induced by its components. -/
theorem detEquiv_eq_lineCongr {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀} (a : Hom d d')
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) (e₁ : K₁ ≃ₗ[R] L₁) (e₀ : K₀ ≃ₗ[R] L₀)
    (h₁ : a.neg = e₁.toLinearMap) (h₀ : a.zero = e₀.toLinearMap) :
    detEquiv a ha hqa = lineCongr d d' e₁ e₀ :=
  determinantEquivOfSurjectiveQuasiIso_eq_lineCongr d d' a e₁ e₀ h₁ h₀ ha hqa

/-- The determinant equivalence of a composite of degreewise-surjective quasi-isomorphisms is the
composite of their determinant equivalences (Stacks 0FJL). -/
theorem detEquiv_comp {M₁ M₀ : Type*} [AddCommGroup M₁] [Module R M₁] [Module.Finite R M₁]
    [Module.Projective R M₁] [AddCommGroup M₀] [Module R M₀] [Module.Finite R M₀]
    [Module.Projective R M₀]
    {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀} {d'' : M₁ →ₗ[R] M₀} (b : Hom d' d'') (a : Hom d d')
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) (hb : b.IsDegreewiseSurjective)
    (hqb : b.IsQuasiIso) (hc : (b.comp a).IsDegreewiseSurjective) (hqc : (b.comp a).IsQuasiIso) :
    detEquiv (b.comp a) hc hqc = (detEquiv a ha hqa).trans (detEquiv b hb hqb) := by
  obtain ⟨_, h⟩ := determinantEquivOfSurjectiveQuasiIso_comp d d' d'' a b ha hqa hb hqb
  exact h.symm

/-- The determinant equivalence of a degreewise-surjective quasi-isomorphism conjugated by two
isomorphisms is the conjugate of its determinant equivalence. -/
theorem detEquiv_conj {M₁ M₀ N₁ N₀ : Type*} [AddCommGroup M₁] [Module R M₁]
    [Module.Finite R M₁] [Module.Projective R M₁] [AddCommGroup M₀] [Module R M₀]
    [Module.Finite R M₀] [Module.Projective R M₀] [AddCommGroup N₁] [Module R N₁]
    [Module.Finite R N₁] [Module.Projective R N₁] [AddCommGroup N₀] [Module R N₀]
    [Module.Finite R N₀] [Module.Projective R N₀]
    {c : M₁ →ₗ[R] M₀} {d : K₁ →ₗ[R] K₀} {d' : L₁ →ₗ[R] L₀} {c' : N₁ →ₗ[R] N₀}
    (a : Hom d d') (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (α₁ : M₁ ≃ₗ[R] K₁) (α₀ : M₀ ≃ₗ[R] K₀) (hα : d ∘ₗ α₁.toLinearMap = α₀.toLinearMap ∘ₗ c)
    (β₁ : L₁ ≃ₗ[R] N₁) (β₀ : L₀ ≃ₗ[R] N₀) (hβ : c' ∘ₗ β₁.toLinearMap = β₀.toLinearMap ∘ₗ d')
    (a' : Hom c c') (h₁ : a'.neg = β₁.toLinearMap ∘ₗ a.neg ∘ₗ α₁.toLinearMap)
    (h₀ : a'.zero = β₀.toLinearMap ∘ₗ a.zero ∘ₗ α₀.toLinearMap)
    (ha' : a'.IsDegreewiseSurjective) (hqa' : a'.IsQuasiIso) :
    detEquiv a' ha' hqa' =
      ((lineCongr c d α₁ α₀).trans (detEquiv a ha hqa)).trans (lineCongr d' c' β₁ β₀) := by
  let α : Hom c d := ⟨α₁.toLinearMap, α₀.toLinearMap, hα.symm⟩
  let β : Hom d' c' := ⟨β₁.toLinearMap, β₀.toLinearMap, hβ.symm⟩
  have hαs : α.IsDegreewiseSurjective := ⟨α₁.surjective, α₀.surjective⟩
  have hβs : β.IsDegreewiseSurjective := ⟨β₁.surjective, β₀.surjective⟩
  have hqα : α.IsQuasiIso := isQuasiIso_of_equiv α₁ α₀ hα
  have hqβ : β.IsQuasiIso := isQuasiIso_of_equiv β₁ β₀ hβ
  obtain rfl := eq_comp_comp_of_conj a α₁ α₀ hα β₁ β₀ hβ a' h₁ h₀
  have hs₁ : (a.comp α).IsDegreewiseSurjective := ⟨ha.1.comp α₁.surjective, ha.2.comp α₀.surjective⟩
  rw [detEquiv_comp β (a.comp α) hs₁ (Hom.isQuasiIso_comp α a hqα hqa) hβs hqβ,
    detEquiv_comp a α hαs hqα ha hqa,
    detEquiv_eq_lineCongr α hαs hqα α₁ α₀ rfl rfl, detEquiv_eq_lineCongr β hβs hqβ β₁ β₀ rfl rfl]

end TwoTermComplex

end
