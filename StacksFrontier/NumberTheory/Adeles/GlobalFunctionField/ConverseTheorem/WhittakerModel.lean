module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.WhittakerRecursion

/-!
# The Whittaker function attached to a family of coefficients

The converse direction of Stacks Tag 03VU builds an eigenform out of its prospective Whittaker
coefficients. This file carries out the first step: given

* an adelic character `ψ`,
* a character `ω` of the ideles trivial on the units `Oˣ` of the integral adeles (the prospective
  central character), and
* a function `c` on divisors with `c(D) = 0` unless `ψ` is trivial on `A(D)`,

the formula `W(κ (α, β; 0, δ)) = ψ(α⁻¹ β) ω(δ) c(div (α δ⁻¹))` defines a function `W` on
`GL₂(A)` (the Iwasawa decomposition, `Stacks.Adeles.GlobalFunctionField.exists_iwasawa`, is not
unique, and the two conditions are exactly what makes the formula independent of the choice).
It is left `GL₂(O)`-invariant, satisfies `W(x n(z)) = ψ(z) W(x)` and `W(a x) = ω(a) W(x)` for
scalar ideles `a`, and `W(diag(y, 1)) = c(div y)`: these are the properties of the Whittaker
function of an eigenform established in `ConverseTheorem/WhittakerRecursion.lean`
(`IsUnramifiedCuspForm.whittaker_mapO_mul_upperGL`), so every such `W` arises this way.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.whittakerModel ψ ω c` — the function `W`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.whittakerModel_mapO_mul_upperGL` — the defining formula holds
  for every Iwasawa decomposition.
* `Stacks.Adeles.GlobalFunctionField.whittakerModel_mapO_mul`,
  `Stacks.Adeles.GlobalFunctionField.whittakerModel_mul_upperRightHom`,
  `Stacks.Adeles.GlobalFunctionField.whittakerModel_scalarGL_mul`,
  `Stacks.Adeles.GlobalFunctionField.whittakerModel_diagGL` — the properties of a Whittaker
  function.

## References

* H. Jacquet, R. P. Langlands, *Automorphic forms on GL(2)*, LNM 114, §3 and §11.
* [Stacks Project, Tag 03VU](https://stacks.math.columbia.edu/tag/03VU)
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GlobalFunctionField

section Matrices

variable {K : Type u} [Field K]

/-- Right multiplication by `n(z) = (1, z; 0, 1)`: `(α, β; 0, δ) n(z) = (α, α z + β; 0, δ)`. -/
public theorem upperGL_mul_upperRightHom_eq (α δ : (AdeleRing K)ˣ) (β z : AdeleRing K) :
    upperGL α δ β * GeneralLinearGroup.upperRightHom z =
      upperGL α δ ((α : AdeleRing K) * z + β) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.coe_mul, upperRightHom_eq_upperGL, coe_upperGL, coe_upperGL,
    coe_upperGL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Left multiplication by the scalar matrix `a`: `a (α, β; 0, δ) = (a α, a β; 0, a δ)`. -/
public theorem scalarGL_mul_upperGL (a α δ : (AdeleRing K)ˣ) (β : AdeleRing K) :
    scalarGL a * upperGL α δ β = upperGL (a * α) (a * δ) ((a : AdeleRing K) * β) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.coe_mul, coe_scalarGL, coe_upperGL, coe_upperGL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]

/-- The entries of `g ∈ GL₂(O)` with `g (α, β; 0, δ) = (α', β'; 0, δ')`: `α' α⁻¹` and `δ' δ⁻¹`
are integral and `β' = α' α⁻¹ β + b δ` with `b` integral. -/
public theorem mapO_mul_upperGL_eq {g : GL (Fin 2) (integralAdeles K)} {α δ α' δ' : (AdeleRing K)ˣ}
    {β β' : AdeleRing K} (h : mapO g * upperGL α δ β = upperGL α' δ' β') :
    ((α' * α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈ integralAdeles K ∧
      ((δ' * δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈ integralAdeles K ∧
      ∃ b ∈ integralAdeles K,
        β' = ((α' * α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β + b * δ := by
  have hm :=
    congrArg (fun x : GL (Fin 2) (AdeleRing K) => (x : Matrix (Fin 2) (Fin 2) (AdeleRing K))) h
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_upperGL] at hm
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, coe_mapO_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, mul_zero, add_zero] at e00 e01 e10 e11
  set M := ((g : GL (Fin 2) (integralAdeles K)) : Matrix (Fin 2) (Fin 2) (integralAdeles K))
  have hα : ∀ x : AdeleRing K, x * (α : AdeleRing K) = α' → x = ((α' * α⁻¹ : (AdeleRing K)ˣ) :
      AdeleRing K) := fun x hx => by
    rw [Units.val_mul, ← hx, mul_assoc, Units.mul_inv, mul_one]
  have h10 : ((M 1 0 : integralAdeles K) : AdeleRing K) = 0 := by
    have : ((M 1 0 : integralAdeles K) : AdeleRing K) * α * ((α⁻¹ : (AdeleRing K)ˣ) :
        AdeleRing K) = 0 := by rw [e10, zero_mul]
    rwa [mul_assoc, Units.mul_inv, mul_one] at this
  rw [h10, zero_mul, zero_add] at e11
  have hδ : ((M 1 1 : integralAdeles K) : AdeleRing K) =
      ((δ' * δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) := by
    rw [Units.val_mul, ← e11, mul_assoc, Units.mul_inv, mul_one]
  have hα' := hα _ e00
  refine ⟨hα' ▸ (M 0 0).2, hδ ▸ (M 1 1).2, (M 0 1 : AdeleRing K), (M 0 1).2, ?_⟩
  rw [← e01, hα']

end Matrices

section Model

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
variable {Λ : Type w} [Field Λ]

omit [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] in
/-- An idele which is integral with integral inverse comes from `Oˣ`. -/
public theorem exists_integralUnit_of_mem {z : (AdeleRing K)ˣ}
    (h₁ : (z : AdeleRing K) ∈ integralAdeles K) (h₂ : ((z⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈
      integralAdeles K) :
    ∃ o : (integralAdeles K)ˣ, Units.map (integralAdeles K).subtype.toMonoidHom o = z :=
  ⟨⟨⟨_, h₁⟩, ⟨_, h₂⟩, Subtype.ext z.mul_inv, Subtype.ext z.inv_mul⟩, Units.ext rfl⟩

variable (K) in
/-- The value `ψ(α⁻¹ β) ω(δ) c(div (α δ⁻¹))` of the Whittaker function at `(α, β; 0, δ)`. -/
public def whittakerValue (ψ : AddChar (AdeleRing K) Λ) (ω : (AdeleRing K)ˣ →* Λˣ)
    (c : (Place K →₀ ℤ) → Λ) (α δ : (AdeleRing K)ˣ) (β : AdeleRing K) : Λ :=
  ψ (((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β) * ((ω δ : Λ) * c (idelDiv k K (α * δ⁻¹)))

variable {ψ : AddChar (AdeleRing K) Λ} {ω : (AdeleRing K)ˣ →* Λˣ} {c : (Place K →₀ ℤ) → Λ}

/-- Ideles differing by an integral idele with integral inverse have equal divisors and `ω`. -/
private theorem idelDiv_eq_of_integral
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    {α α' : (AdeleRing K)ˣ} (h₁ : ((α' * α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈ integralAdeles K)
    (h₂ : ((α * α'⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈ integralAdeles K) :
    idelDiv k K α' = idelDiv k K α ∧ ω α' = ω α := by
  obtain ⟨o, ho⟩ := exists_integralUnit_of_mem h₁ (by rwa [_root_.mul_inv_rev, inv_inv])
  have := idelDiv_units_map_integralAdeles k o
  have h := hω o
  rw [ho, idelDiv_mul, idelDiv_inv, add_neg_eq_zero] at this
  rw [ho, ω.map_mul, ω.map_inv, mul_inv_eq_one] at h
  exact ⟨this, h⟩

/-- **Independence of the Iwasawa decomposition.** -/
public theorem whittakerValue_eq_of_mapO_mul
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) {κ κ' : GL (Fin 2) (integralAdeles K)}
    {α δ α' δ' : (AdeleRing K)ˣ} {β β' : AdeleRing K}
    (h : mapO κ * upperGL α δ β = mapO κ' * upperGL α' δ' β') :
    whittakerValue k K ψ ω c α δ β = whittakerValue k K ψ ω c α' δ' β' := by
  have h₁ : mapO (κ'⁻¹ * κ) * upperGL α δ β = upperGL α' δ' β' := by
    rw [map_mul, mul_assoc, h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have h₂ : mapO (κ⁻¹ * κ') * upperGL α' δ' β' = upperGL α δ β := by
    rw [map_mul, mul_assoc, ← h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  obtain ⟨hα, hδ, b, hb, hβ⟩ := mapO_mul_upperGL_eq h₁
  obtain ⟨hα', hδ', -⟩ := mapO_mul_upperGL_eq h₂
  obtain ⟨hdα, -⟩ := idelDiv_eq_of_integral k hω hα hα'
  obtain ⟨hdδ, hωδ⟩ := idelDiv_eq_of_integral k hω hδ hδ'
  have hD : idelDiv k K (α' * δ'⁻¹) = idelDiv k K (α * δ⁻¹) := by
    rw [idelDiv_mul, idelDiv_mul, idelDiv_inv, idelDiv_inv, hdα, hdδ]
  -- the additive character
  have hsplit : ((α'⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β' =
      ((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β +
        ((α'⁻¹ * δ : (AdeleRing K)ˣ) : AdeleRing K) * b := by
    rw [hβ]
    simp only [Units.val_mul]
    have h1 := Units.inv_mul α'
    linear_combination (((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β) * h1
  simp only [whittakerValue]
  rw [hD, hωδ]
  by_cases hc0 : c (idelDiv k K (α * δ⁻¹)) = 0
  · simp [hc0]
  have hmem : ((α'⁻¹ * δ : (AdeleRing K)ˣ) : AdeleRing K) * b ∈
      adeleLattice K (idelDiv k K (α * δ⁻¹)) := by
    have hb0 : b ∈ adeleLattice K 0 := mem_adeleLattice_zero_iff.2 hb
    have := (idele_mul_mem_adeleLattice_iff k (α'⁻¹ * δ) (E := 0)).2 hb0
    convert this using 2
    rw [idelDiv_mul, idelDiv_inv, idelDiv_mul, idelDiv_inv, hdα]
    abel
  rw [hsplit, AddChar.map_add_eq_mul, hc _ hc0 _ hmem, mul_one]

variable (K) in
/-- **The Whittaker function with coefficients `c`**: `W(κ (α, β; 0, δ)) = ψ(α⁻¹ β) ω(δ)
c(div (α δ⁻¹))`, computed on a chosen Iwasawa decomposition. -/
public def whittakerModel (ψ : AddChar (AdeleRing K) Λ) (ω : (AdeleRing K)ˣ →* Λˣ)
    (c : (Place K →₀ ℤ) → Λ) (x : GL (Fin 2) (AdeleRing K)) : Λ :=
  whittakerValue k K ψ ω c (exists_iwasawa x).choose_spec.choose
    (exists_iwasawa x).choose_spec.choose_spec.choose
    (exists_iwasawa x).choose_spec.choose_spec.choose_spec.choose

/-- The defining formula holds for every Iwasawa decomposition. -/
public theorem whittakerModel_mapO_mul_upperGL
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (κ : GL (Fin 2) (integralAdeles K))
    (α δ : (AdeleRing K)ˣ) (β : AdeleRing K) :
    whittakerModel k K ψ ω c (mapO κ * upperGL α δ β) = whittakerValue k K ψ ω c α δ β := by
  have hx :=
    (exists_iwasawa (mapO κ * upperGL α δ β)).choose_spec.choose_spec.choose_spec.choose_spec
  exact (whittakerValue_eq_of_mapO_mul k hω hc hx).symm

/-- `W` is left `GL₂(O)`-invariant. -/
public theorem whittakerModel_mapO_mul
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (κ : GL (Fin 2) (integralAdeles K))
    (x : GL (Fin 2) (AdeleRing K)) :
    whittakerModel k K ψ ω c (mapO κ * x) = whittakerModel k K ψ ω c x := by
  obtain ⟨κ₀, α, δ, β, rfl⟩ := exists_iwasawa x
  change whittakerModel k K ψ ω c (mapO κ * (mapO κ₀ * upperGL α δ β)) =
    whittakerModel k K ψ ω c (mapO κ₀ * upperGL α δ β)
  rw [← mul_assoc, ← map_mul, whittakerModel_mapO_mul_upperGL k hω hc,
    whittakerModel_mapO_mul_upperGL k hω hc]

/-- `W(x n(z)) = ψ(z) W(x)`. -/
public theorem whittakerModel_mul_upperRightHom
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (x : GL (Fin 2) (AdeleRing K))
    (z : AdeleRing K) :
    whittakerModel k K ψ ω c (x * GeneralLinearGroup.upperRightHom z) =
      ψ z * whittakerModel k K ψ ω c x := by
  obtain ⟨κ₀, α, δ, β, rfl⟩ := exists_iwasawa x
  change whittakerModel k K ψ ω c (mapO κ₀ * upperGL α δ β * GeneralLinearGroup.upperRightHom z) =
    ψ z * whittakerModel k K ψ ω c (mapO κ₀ * upperGL α δ β)
  rw [mul_assoc, upperGL_mul_upperRightHom_eq, whittakerModel_mapO_mul_upperGL k hω hc,
    whittakerModel_mapO_mul_upperGL k hω hc]
  have hz : ((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * ((α : AdeleRing K) * z + β) =
      z + ((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β := by
    rw [mul_add, ← mul_assoc, Units.inv_mul, one_mul]
  simp only [whittakerValue]
  rw [hz, AddChar.map_add_eq_mul]
  ring

/-- Scalar ideles act on `W` by `ω`. -/
public theorem whittakerModel_scalarGL_mul
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (a : (AdeleRing K)ˣ)
    (x : GL (Fin 2) (AdeleRing K)) :
    whittakerModel k K ψ ω c (scalarGL a * x) = ω a * whittakerModel k K ψ ω c x := by
  obtain ⟨κ₀, α, δ, β, rfl⟩ := exists_iwasawa x
  change whittakerModel k K ψ ω c (scalarGL a * (mapO κ₀ * upperGL α δ β)) =
    ω a * whittakerModel k K ψ ω c (mapO κ₀ * upperGL α δ β)
  rw [← mul_assoc, scalarGL_mul_comm, mul_assoc, scalarGL_mul_upperGL,
    whittakerModel_mapO_mul_upperGL k hω hc, whittakerModel_mapO_mul_upperGL k hω hc]
  simp only [whittakerValue]
  have h1 : a * α * (a * δ)⁻¹ = α * δ⁻¹ := by
    rw [_root_.mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
  have h2 : (((a * α)⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * ((a : AdeleRing K) * β) =
      ((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β := by
    rw [_root_.mul_inv, Units.val_mul]
    linear_combination (((α⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β) * Units.inv_mul a
  rw [h1, h2, ω.map_mul a δ, Units.val_mul]
  ring

/-- `W(diag(y, 1)) = c(div y)`. -/
public theorem whittakerModel_diagGL
    (hω : ∀ o : (integralAdeles K)ˣ, ω (Units.map (integralAdeles K).subtype.toMonoidHom o) = 1)
    (hc : ∀ D, c D ≠ 0 → ∀ a ∈ adeleLattice K D, ψ a = 1) (y : (AdeleRing K)ˣ) :
    whittakerModel k K ψ ω c (diagGL y) = c (idelDiv k K y) := by
  rw [diagGL_eq_upperGL, ← one_mul (upperGL y 1 0), ← map_one mapO,
    whittakerModel_mapO_mul_upperGL k hω hc]
  simp [whittakerValue]

end Model

end Stacks.Adeles.GlobalFunctionField

end
