module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import StacksFrontier.Topology.Algebra.PontryaginDual.Eval
public import StacksCore.Tactic.StacksAttribute

/-!
# Pontryagin duality for discrete abelian groups

Let `A` be a discrete abelian group. Its Pontryagin dual `PontryaginDual A` is a compact Hausdorff
abelian group, the characters of `A` separate its points, and the evaluation map
`A → PontryaginDual (PontryaginDual A)` is an isomorphism of topological groups.

Separation of points comes from the injectivity of `ℚ/ℤ` as a `ℤ`-module (Mathlib's
`CharacterModule`), followed by the injection `ℚ/ℤ → ℝ/ℤ ≅ Circle`. Surjectivity of the
evaluation map is the Stone–Weierstrass argument: the functions `χ ↦ χ a` span a dense
`*`-subalgebra of `C(PontryaginDual A, ℂ)`, and a character of `PontryaginDual A` that is not of
this form is orthogonal to all of them for the Haar measure, hence to itself.

## Main definitions

* `Stacks.Pontryagin.doubleDualEquivOfDiscreteTopology`: for `A` discrete, the evaluation map
  `A ≃ₜ* PontryaginDual (PontryaginDual A)`.

## Main results

* `Stacks.Pontryagin.compactSpace_of_discreteTopology`: the dual of a discrete group is compact.
* `Stacks.Pontryagin.exists_apply_ne_one_of_discreteTopology`: the characters of a discrete
  abelian group separate points.
* `Stacks.Pontryagin.integral_apply_eq_zero`: a nontrivial character has integral zero against
  a left invariant measure.
* `Stacks.Pontryagin.eval_bijective_of_discreteTopology`: the evaluation map of a discrete
  abelian group is bijective.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

namespace Stacks.Pontryagin

open MeasureTheory ComplexConjugate

section Integral

/-- A nontrivial homomorphism `ψ : G →* Circle` has integral zero against any left invariant
measure: translating by an element `k` with `ψ k ≠ 1` multiplies the integral by `ψ k`. -/
theorem integral_apply_eq_zero {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] {ψ : G →* Circle} (hψ : ψ ≠ 1) :
    ∫ x, (ψ x : ℂ) ∂μ = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, ψ k ≠ 1 := by
    by_contra! h
    exact hψ (MonoidHom.ext h)
  have h := integral_mul_left_eq_self (μ := μ) (fun x ↦ (ψ x : ℂ)) k
  simp only [map_mul, Circle.coe_mul] at h
  rw [integral_const_mul] at h
  have hk' : (ψ k : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr fun h' ↦ hk (Circle.ext (by simpa using h'))
  have : ((ψ k : ℂ) - 1) * ∫ x, (ψ x : ℂ) ∂μ = 0 := by linear_combination h
  exact (mul_eq_zero.mp this).resolve_left hk'

end Integral

section Discrete

variable (A : Type*) [CommGroup A] [TopologicalSpace A] [DiscreteTopology A]

/-- The Pontryagin dual of a discrete abelian group is compact (it is a closed subspace of the
product of copies of the circle indexed by `A`); it is Hausdorff by `PontryaginDual.instT2Space`. -/
@[stacks 03VI "the dual of a discrete abelian group is compact"]
theorem compactSpace_of_discreteTopology : CompactSpace (PontryaginDual A) :=
  inferInstance

/-- The inclusion `ℚ/ℤ → ℝ/ℤ` of additive circles. -/
def ratAddCircleToReal : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom fun x hx ↦ by
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    exact AddSubgroup.mem_comap.mpr ⟨n, by simp⟩

/-- The inclusion `ℚ/ℤ → ℝ/ℤ` is injective. -/
theorem ratAddCircleToReal_injective : Function.Injective ratAddCircleToReal := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  induction x using QuotientAddGroup.induction_on with | H q => ?_
  change ((q : ℝ) : AddCircle (1 : ℝ)) = 0 at hx
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).mp hx
  refine (AddCircle.coe_eq_zero_iff 1).mpr ⟨n, ?_⟩
  simp only [zsmul_eq_mul, mul_one] at hn ⊢
  exact_mod_cast hn

variable {A} in
/-- The character of `A` attached to a `ℚ/ℤ`-valued character of `Additive A`. -/
def ofCharacterModule (c : CharacterModule (Additive A)) : PontryaginDual A :=
  { toFun a := AddCircle.toCircle (ratAddCircleToReal (c (Additive.ofMul a)))
    map_one' := by simp
    map_mul' a b := by simp [AddCircle.toCircle_add]
    continuous_toFun := continuous_of_discreteTopology }

variable {A} in
/-- The characters of a discrete abelian group separate its points. -/
theorem exists_apply_ne_one_of_discreteTopology {a : A} (ha : a ≠ 1) :
    ∃ χ : PontryaginDual A, χ a ≠ 1 := by
  obtain ⟨c, hc⟩ :=
    CharacterModule.exists_character_apply_ne_zero_of_ne_zero (a := Additive.ofMul a)
      (by simpa using ha)
  refine ⟨ofCharacterModule c, fun h ↦ hc ?_⟩
  have h' : AddCircle.toCircle (ratAddCircleToReal (c (Additive.ofMul a))) =
      AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
    rw [AddCircle.toCircle_zero]
    exact h
  have := AddCircle.injective_toCircle one_ne_zero h'
  exact ratAddCircleToReal_injective (by rw [this, map_zero])

/-- The evaluation map of a discrete abelian group is injective. -/
theorem eval_injective_of_discreteTopology : Function.Injective (eval A) := by
  refine (eval_injective_iff).mpr fun a b hab ↦ ?_
  obtain ⟨χ, hχ⟩ := exists_apply_ne_one_of_discreteTopology (div_ne_one.mpr hab)
  refine ⟨χ, fun h ↦ hχ ?_⟩
  rw [map_div, h, div_self']

/-- The character `χ ↦ χ a` of the compact group `PontryaginDual A`, as a complex valued
continuous function. -/
def evalContinuousMap (a : A) : C(PontryaginDual A, ℂ) :=
  ⟨fun χ ↦ (χ a : ℂ), continuous_subtype_val.comp (continuous_eval_const a)⟩

/-- The `*`-subalgebra of `C(PontryaginDual A, ℂ)` generated by the functions `χ ↦ χ a`. -/
def evalSubalgebra : StarSubalgebra ℂ C(PontryaginDual A, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range (evalContinuousMap A))
  star_mem' := by
    change Algebra.adjoin ℂ (Set.range (evalContinuousMap A)) ≤
      star (Algebra.adjoin ℂ (Set.range (evalContinuousMap A)))
    refine Algebra.adjoin_le ?_
    rintro - ⟨a, rfl⟩
    refine Algebra.subset_adjoin ⟨a⁻¹, ContinuousMap.ext fun χ ↦ ?_⟩
    change ((χ a⁻¹ : Circle) : ℂ) = conj (χ a : ℂ)
    rw [map_inv, Circle.coe_inv_eq_conj]

omit [DiscreteTopology A] in
/-- The `*`-subalgebra generated by the functions `χ ↦ χ a` is their linear span. -/
theorem evalSubalgebra_toSubmodule :
    Subalgebra.toSubmodule (evalSubalgebra A).toSubalgebra =
      Submodule.span ℂ (Set.range (evalContinuousMap A)) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ ↦ id) ⟨1, ?_⟩ ?_ hx
  · ext χ
    simp [evalContinuousMap]
  · rintro - - - - ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, ContinuousMap.ext fun χ ↦ by simp [evalContinuousMap]⟩

omit [DiscreteTopology A] in
/-- The functions `χ ↦ χ a` separate the points of `PontryaginDual A`. -/
theorem evalSubalgebra_separatesPoints : (evalSubalgebra A).SeparatesPoints := by
  intro χ χ' hχ
  obtain ⟨a, ha⟩ : ∃ a, χ a ≠ χ' a := by
    by_contra! h
    exact hχ (PontryaginDual.ext h)
  refine ⟨_, ⟨evalContinuousMap A a, Algebra.subset_adjoin ⟨a, rfl⟩, rfl⟩, ?_⟩
  exact fun h ↦ ha (Circle.ext h)

/-- The linear span of the functions `χ ↦ χ a` is dense in `C(PontryaginDual A, ℂ)`. -/
theorem span_evalContinuousMap_closure_eq_top :
    (Submodule.span ℂ (Set.range (evalContinuousMap A))).topologicalClosure = ⊤ := by
  rw [← evalSubalgebra_toSubmodule]
  exact congr_arg (Subalgebra.toSubmodule <| StarSubalgebra.toSubalgebra ·)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
      (evalSubalgebra_separatesPoints A))

/-- The evaluation map of a discrete abelian group is surjective. -/
theorem eval_surjective_of_discreteTopology : Function.Surjective (eval A) := by
  intro Φ
  by_contra! hΦ
  let : MeasurableSpace (PontryaginDual A) := borel _
  have : BorelSpace (PontryaginDual A) := ⟨rfl⟩
  let μ : Measure (PontryaginDual A) := Measure.haar
  let Φc : C(PontryaginDual A, ℂ) := ⟨fun χ ↦ (Φ χ : ℂ), continuous_subtype_val.comp Φ.continuous⟩
  let L : C(PontryaginDual A, ℂ) →L[ℂ] ℂ :=
    (innerSL ℂ (ContinuousMap.toLp 2 μ ℂ Φc)).comp (ContinuousMap.toLp 2 μ ℂ)
  have hL (g : C(PontryaginDual A, ℂ)) : L g = ∫ x, g x * conj (Φc x) ∂μ :=
    ContinuousMap.inner_toLp μ Φc g
  have hspan : Submodule.span ℂ (Set.range (evalContinuousMap A)) ≤
      LinearMap.ker (L : C(PontryaginDual A, ℂ) →ₗ[ℂ] ℂ) := by
    refine Submodule.span_le.mpr ?_
    rintro - ⟨a, rfl⟩
    let ψ : PontryaginDual A →* Circle :=
      { toFun χ := χ a * (Φ χ)⁻¹
        map_one' := by simp
        map_mul' χ χ' := by
          change (χ a * χ' a) * (Φ (χ * χ'))⁻¹ = (χ a * (Φ χ)⁻¹) * (χ' a * (Φ χ')⁻¹)
          rw [map_mul, mul_inv]
          ac_rfl }
    have hψ : ψ ≠ 1 := by
      intro h
      refine hΦ a (PontryaginDual.ext fun χ ↦ ?_)
      have := DFunLike.congr_fun h χ
      change χ a * (Φ χ)⁻¹ = 1 at this
      exact mul_inv_eq_one.mp this
    change L (evalContinuousMap A a) = 0
    rw [hL, ← integral_apply_eq_zero μ hψ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun χ ↦ ?_)
    simp only [ψ, evalContinuousMap, Φc, MonoidHom.coe_mk, OneHom.coe_mk, ContinuousMap.coe_mk,
      Circle.coe_mul, Circle.coe_inv_eq_conj]
  have hle : (⊤ : Submodule ℂ C(PontryaginDual A, ℂ)) ≤
      LinearMap.ker (L : C(PontryaginDual A, ℂ) →ₗ[ℂ] ℂ) := by
    rw [← span_evalContinuousMap_closure_eq_top]
    exact Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  have h0 : L Φc = 0 := hle Submodule.mem_top
  rw [hL] at h0
  have h1 : ∫ x, Φc x * conj (Φc x) ∂μ = ∫ _x, (1 : ℂ) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun χ ↦ by
      simp [Φc, Complex.mul_conj, Circle.normSq_coe])
  rw [h1, integral_const, Complex.real_smul, mul_one, Complex.ofReal_eq_zero] at h0
  exact (measureReal_univ_pos (μ := μ)).ne' h0

/-- The evaluation map of a discrete abelian group is bijective. -/
theorem eval_bijective_of_discreteTopology : Function.Bijective (eval A) :=
  ⟨eval_injective_of_discreteTopology A, eval_surjective_of_discreteTopology A⟩

/-- Pontryagin duality for a discrete abelian group `A`: the evaluation map is an isomorphism of
topological groups `A ≃ₜ* PontryaginDual (PontryaginDual A)`. -/
@[stacks 03VI "Pontryagin duality: a discrete abelian group is its double dual"]
def doubleDualEquivOfDiscreteTopology : A ≃ₜ* PontryaginDual (PontryaginDual A) where
  toMulEquiv := MulEquiv.ofBijective (eval A) (eval_bijective_of_discreteTopology A)
  continuous_toFun := (eval A).continuous
  continuous_invFun := continuous_of_discreteTopology

/-- The discrete double dual isomorphism is the evaluation map. -/
@[simp]
theorem doubleDualEquivOfDiscreteTopology_apply (a : A) :
    doubleDualEquivOfDiscreteTopology A a = eval A a :=
  rfl

end Discrete

end Stacks.Pontryagin
