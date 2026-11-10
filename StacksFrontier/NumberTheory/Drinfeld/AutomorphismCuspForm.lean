module

public import StacksFrontier.NumberTheory.Drinfeld.AdeleRingEquiv
public import StacksFrontier.NumberTheory.Drinfeld.UnitEigenform
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.WhittakerSum

/-!
# Cusp forms from an automorphism of the function field

Let `K` be a field, `α` an automorphism of `K`, and `F` a function on `GL₂(A)` invariant under
left multiplication by `GL₂(O)` and right multiplication by `GL₂(K)`. The constant term of `F`
at `x`, the sum of `z ↦ F(x (1, z; 0, 1))` over a transversal of `A / (K + U_x)`, depends only on
the diagonal part `(a, δ)` of an Iwasawa decomposition `x = κ (a, β; 0, δ)`, and only through the
classes of `a` and `δ` modulo `O^×` and `K^×` (the divisor classes of `a` and `δ`). Hence if `α`
fixes every such class, i.e. `α(a) ∈ a O^× K^×` for every idele `a`, the constant terms of `F`
and of `F ∘ α` agree, and `F - F ∘ α` satisfies the cusp condition (in the linear form
`Stacks.Adeles.GlobalFunctionField.StarCusp`).

## Main results

* `Stacks.Drinfeld.cuspSum_eq_of_upperGL` — the constant term at `(a, β; 0, δ)` only depends on
  the classes of `a` and `δ`.
* `Stacks.Drinfeld.starCusp_sub_comp_glMap` — `F - F ∘ α` satisfies the cusp condition.
* `Stacks.Drinfeld.cuspFormsCentralChar_ne_bot_of_glMap_notMem` — if moreover `α` moves `X` out of
  `Z(A) GL₂(O) X GL₂(K)`, a twist of `1_S - 1_S ∘ α` is a nonzero element of `C(Ω)`.
-/

@[expose] public noncomputable section

open Matrix
open scoped RestrictedProduct

universe u w

namespace Stacks.Drinfeld

open Stacks.Adeles Stacks.Adeles.GlobalFunctionField

variable {K : Type u} [Field K]

/-- An adelic matrix with entries and inverse entries in a subring comes from `GL₂` of it. -/
private theorem exists_map_subtype_eq (S : Subring (AdeleRing K)) {g : GL (Fin 2) (AdeleRing K)}
    (h : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j ∈ S)
    (h' : ∀ i j, ((g⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j ∈
      S) :
    ∃ κ : GL (Fin 2) S, GeneralLinearGroup.map S.subtype κ = g := by
  let M : Matrix (Fin 2) (Fin 2) S := Matrix.of fun i j => ⟨_, h i j⟩
  let M' : Matrix (Fin 2) (Fin 2) S := Matrix.of fun i j => ⟨_, h' i j⟩
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin 2) S.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hM : (RingHom.mapMatrix (m := Fin 2) S.subtype) M =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) := rfl
  have hM' : (RingHom.mapMatrix (m := Fin 2) S.subtype) M' =
      ((g⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) := rfl
  refine ⟨⟨M, M', inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hM, hM', map_one, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  · rw [map_mul, hM, hM', map_one, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]

/-- An adelic matrix with integral entries and integral inverse entries lies in `GL₂(O)`. -/
public theorem exists_mapO_eq {g : GL (Fin 2) (AdeleRing K)}
    (h : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j ∈ integralAdeles K)
    (h' : ∀ i j, ((g⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j ∈
      integralAdeles K) :
    ∃ κ : GL (Fin 2) (integralAdeles K), mapO κ = g :=
  exists_map_subtype_eq _ h h'

/-- An adelic matrix with principal entries and principal inverse entries lies in `GL₂(K)`. -/
public theorem exists_mapK_eq {g : GL (Fin 2) (AdeleRing K)}
    (h : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j ∈ principalAdeles K)
    (h' : ∀ i j, ((g⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j ∈
      principalAdeles K) :
    ∃ γ : GL (Fin 2) (principalAdeles K), mapK γ = g :=
  exists_map_subtype_eq _ h h'

public theorem conjE_upperGL (a δ : (AdeleRing K)ˣ) (β : AdeleRing K) :
    conjE K (upperGL a δ β) = !![0, (a : AdeleRing K) * ((δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K);
      0, 0] := by
  have hinv : ((upperGL a δ β)⁻¹ : GL (Fin 2) (AdeleRing K)) =
      upperGL a⁻¹ δ⁻¹ (-((a⁻¹ : (AdeleRing K)ˣ) * β * (δ⁻¹ : (AdeleRing K)ˣ))) := by
    rw [inv_eq_iff_mul_eq_one, upperGL_mul, mul_inv_cancel, mul_inv_cancel]
    have h0 : (a : AdeleRing K) * -(((a⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β *
        ((δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)) + β * ((δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) =
          0 := by
      rw [mul_neg, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, neg_add_cancel]
    rw [h0, ← upperRightHom_eq_upperGL, AddChar.map_zero_eq_one]
  rw [conjE, hinv, coe_upperGL, coe_upperGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eOneTwo, Matrix.mul_apply, Fin.sum_univ_two]

public theorem mem_stabSubgroup_upperGL (a δ : (AdeleRing K)ˣ) (β y : AdeleRing K) :
    y ∈ stabSubgroup K (upperGL a δ β) ↔
      y * ((a : AdeleRing K) * ((δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)) ∈ integralAdeles K := by
  change (∀ i j, y * conjE K _ i j ∈ integralAdeles K) ↔ _
  rw [conjE_upperGL]
  refine ⟨fun h => by simpa using h 0 1, fun h i j => ?_⟩
  fin_cases i <;> fin_cases j <;> simp [h, (integralAdeles K).zero_mem]

/-- The matrices with integral entries. -/
public def IsIntMat (N : Matrix (Fin 2) (Fin 2) (AdeleRing K)) : Prop :=
  ∀ i j, N i j ∈ integralAdeles K

public theorem IsIntMat.mul {N N' : Matrix (Fin 2) (Fin 2) (AdeleRing K)} (hN : IsIntMat N)
    (hN' : IsIntMat N') : IsIntMat (N * N') := fun i j => by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem (mul_mem (hN _ _) (hN' _ _)) (mul_mem (hN _ _) (hN' _ _))

public theorem isIntMat_mapO (κ : GL (Fin 2) (integralAdeles K)) :
    IsIntMat (mapO κ : Matrix (Fin 2) (Fin 2) (AdeleRing K)) := fun i j => by
  rw [coe_mapO_apply]
  exact (κ i j).2

public theorem conjE_mapO_mul (κ : GL (Fin 2) (integralAdeles K)) (g : GL (Fin 2) (AdeleRing K)) :
    conjE K (mapO κ * g) = (mapO κ : Matrix (Fin 2) (Fin 2) (AdeleRing K)) * conjE K g *
      (((mapO κ)⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) := by
  rw [conjE, conjE, _root_.mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul]
  simp only [Matrix.mul_assoc]

public theorem stabSubgroup_mapO_mul (κ : GL (Fin 2) (integralAdeles K))
    (g : GL (Fin 2) (AdeleRing K)) : stabSubgroup K (mapO κ * g) = stabSubgroup K g := by
  ext y
  have key : ∀ (κ : GL (Fin 2) (integralAdeles K)) (N : Matrix (Fin 2) (Fin 2) (AdeleRing K)),
      IsIntMat (y • N) → IsIntMat (y • ((mapO κ : Matrix (Fin 2) (Fin 2) (AdeleRing K)) * N *
        (((mapO κ)⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)))) := by
    intro κ N hN
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    refine ((isIntMat_mapO κ).mul hN).mul ?_
    rw [← map_inv]
    exact isIntMat_mapO κ⁻¹
  have hmem : ∀ x : GL (Fin 2) (AdeleRing K), y ∈ stabSubgroup K x ↔ IsIntMat (y • conjE K x) :=
    fun x => Iff.rfl
  rw [hmem, hmem, conjE_mapO_mul]
  refine ⟨fun h => ?_, key κ _⟩
  have := key κ⁻¹ _ h
  set A : GL (Fin 2) (AdeleRing K) := mapO κ
  have hA : mapO κ⁻¹ = A⁻¹ := map_inv _ _
  rw [hA, inv_inv] at this
  have h1 : ((A⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) * A = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one]
  have h2 : (A : Matrix (Fin 2) (Fin 2) (AdeleRing K)) * ((A⁻¹ : GL (Fin 2) (AdeleRing K))) =
      1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one]
  have e : ((A⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) *
      ((A : Matrix (Fin 2) (Fin 2) (AdeleRing K)) * conjE K g *
        ((A⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) _)) *
        (A : Matrix (Fin 2) (Fin 2) (AdeleRing K)) = conjE K g := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1,
      Matrix.mul_one]
  rwa [e] at this

private theorem inv_upperGL_zero_aux (o o' : (AdeleRing K)ˣ) :
    (upperGL o o' 0)⁻¹ = upperGL o⁻¹ o'⁻¹ 0 := by
  rw [inv_eq_iff_mul_eq_one, upperGL_mul, mul_inv_cancel, mul_inv_cancel, mul_zero, zero_mul,
    add_zero, ← upperRightHom_eq_upperGL, AddChar.map_zero_eq_one]

/-- A diagonal adelic matrix whose entries and their inverses lie in a subring comes from it. -/
private theorem exists_map_subtype_upperGL (S : Subring (AdeleRing K)) {o o' : (AdeleRing K)ˣ}
    (ho : (o : AdeleRing K) ∈ S ∧ ((o⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈ S)
    (ho' : (o' : AdeleRing K) ∈ S ∧ ((o'⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈ S) :
    ∃ κ : GL (Fin 2) S, GeneralLinearGroup.map S.subtype κ = upperGL o o' 0 := by
  refine exists_map_subtype_eq S (fun i j => ?_) (fun i j => ?_)
  · fin_cases i <;> fin_cases j
    exacts [ho.1, S.zero_mem, S.zero_mem, ho'.1]
  · rw [inv_upperGL_zero_aux]
    fin_cases i <;> fin_cases j
    exacts [ho.2, S.zero_mem, S.zero_mem, ho'.2]

section CuspSum

variable {M : Type*} [AddCommMonoid M]

/-- The sum of `z ↦ F(x (1, z; 0, 1))` over a finite set `s`, the unnormalized constant term
of `F` at `x` when `s` is a transversal of `A / (K + U_x)`. -/
public def cuspSum (F : GL (Fin 2) (AdeleRing K) → M) (x : GL (Fin 2) (AdeleRing K))
    (s : Finset (AdeleRing K)) : M :=
  ∑ z ∈ s, F (x * GeneralLinearGroup.upperRightHom z)

/-- A transversal of `A / (K + U_x)`. -/
public def IsCuspTransversal (x : GL (Fin 2) (AdeleRing K)) (s : Finset (AdeleRing K)) : Prop :=
  ∀ a, ∃! z ∈ s, a - z ∈ (principalAdeles K).toAddSubgroup ⊔ stabSubgroup K x

variable {F : GL (Fin 2) (AdeleRing K) → M}
  (hO : ∀ κ x, F (mapO κ * x) = F x) (hK : ∀ γ x, F (x * mapK γ) = F x)
include hO hK

omit [AddCommMonoid M] in
public theorem integrand_periodic (x : GL (Fin 2) (AdeleRing K)) (z : AdeleRing K) {y : AdeleRing K}
    (hy : y ∈ (principalAdeles K).toAddSubgroup ⊔ stabSubgroup K x) :
    F (x * GeneralLinearGroup.upperRightHom (z + y)) =
      F (x * GeneralLinearGroup.upperRightHom z) := by
  obtain ⟨p, hp, u, hu, rfl⟩ := AddSubgroup.mem_sup.1 hy
  rw [add_comm p, ← add_assoc, AddChar.map_add_eq_mul, ← mul_assoc,
    show GeneralLinearGroup.upperRightHom p = mapK (GeneralLinearGroup.upperRightHom ⟨p, hp⟩) from
      (mapK_upperRightHom ⟨p, hp⟩).symm, hK]
  exact left_inv_upperRight_add hO x z hu

/-- The constant term does not depend on the transversal. -/
public theorem cuspSum_eq_of_isCuspTransversal (x : GL (Fin 2) (AdeleRing K))
    {s s' : Finset (AdeleRing K)} (hs : IsCuspTransversal x s) (hs' : IsCuspTransversal x s') :
    cuspSum F x s = cuspSum F x s' := by
  have := sum_transversal_eq (N := (principalAdeles K).toAddSubgroup ⊔ stabSubgroup K x)
    (N' := (principalAdeles K).toAddSubgroup ⊔ stabSubgroup K x) le_rfl
    (fun z => F (x * GeneralLinearGroup.upperRightHom z))
    (fun z y hy => integrand_periodic hO hK x z hy) hs hs'
  rw [AddSubgroup.relIndex_self, one_smul] at this
  exact this.symm

omit hK in
public theorem cuspSum_mapO_mul (κ : GL (Fin 2) (integralAdeles K)) (x : GL (Fin 2) (AdeleRing K))
    (s : Finset (AdeleRing K)) : cuspSum F (mapO κ * x) s = cuspSum F x s := by
  simp only [cuspSum, mul_assoc, hO]

omit hO hK in
public theorem isCuspTransversal_mapO_mul_iff (κ : GL (Fin 2) (integralAdeles K))
    (x : GL (Fin 2) (AdeleRing K)) (s : Finset (AdeleRing K)) :
    IsCuspTransversal (mapO κ * x) s ↔ IsCuspTransversal x s := by
  rw [IsCuspTransversal, IsCuspTransversal, stabSubgroup_mapO_mul]

omit hO hK in
/-- The unit `o` and its inverse are integral adeles. -/
public def IsIntUnit (o : (AdeleRing K)ˣ) : Prop :=
  (o : AdeleRing K) ∈ integralAdeles K ∧ ((o⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈ integralAdeles K

omit hO hK in
/-- The unit `c` and its inverse are principal adeles. -/
public def IsPrincUnit (c : (AdeleRing K)ˣ) : Prop :=
  (c : AdeleRing K) ∈ principalAdeles K ∧ ((c⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈ principalAdeles K

omit hO hK in
public theorem mem_sup_stab_upperGL_iff {a δ o o' c c' : (AdeleRing K)ˣ} (β β' : AdeleRing K)
    (ho : IsIntUnit o) (ho' : IsIntUnit o') (hc : IsPrincUnit c) (hc' : IsPrincUnit c')
    (y : AdeleRing K) :
    ((c : AdeleRing K) * ((c'⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)) * y ∈
        (principalAdeles K).toAddSubgroup ⊔ stabSubgroup K (upperGL a δ β) ↔
      y ∈ (principalAdeles K).toAddSubgroup ⊔
        stabSubgroup K (upperGL (a * o * c) (δ * o' * c') β') := by
  set C : AdeleRing K := (c : AdeleRing K) * ((c'⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)
  set Ci : AdeleRing K := (c' : AdeleRing K) * ((c⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)
  have hC : C ∈ principalAdeles K := mul_mem hc.1 hc'.2
  have hCi : Ci ∈ principalAdeles K := mul_mem hc'.1 hc.2
  have hCCi : Ci * C = 1 := by
    simp only [C, Ci]
    linear_combination (↑c' * ((c'⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)) * Units.mul_inv c +
      Units.mul_inv c'
  simp only [AddSubgroup.mem_sup, mem_stabSubgroup_upperGL, Subring.mem_toAddSubgroup]
  simp only [Units.val_mul, _root_.mul_inv_rev]
  constructor
  · rintro ⟨p, hp, u, hu, he⟩
    refine ⟨Ci * p, mul_mem hCi hp, Ci * u, ?_, ?_⟩
    · have : Ci * u * (↑a * ↑o * ↑c * (↑(c'⁻¹ : (AdeleRing K)ˣ) * (↑(o'⁻¹ : (AdeleRing K)ˣ) *
          ↑(δ⁻¹ : (AdeleRing K)ˣ)))) = (u * (↑a * ↑(δ⁻¹ : (AdeleRing K)ˣ))) *
          (↑o * ↑(o'⁻¹ : (AdeleRing K)ˣ)) := by
        simp only [Ci]
        linear_combination (u * ↑a * ↑(δ⁻¹ : (AdeleRing K)ˣ) * ↑o * ↑(o'⁻¹ : (AdeleRing K)ˣ) *
          (↑c' * ↑(c'⁻¹ : (AdeleRing K)ˣ))) * Units.mul_inv c +
          (u * ↑a * ↑(δ⁻¹ : (AdeleRing K)ˣ) * ↑o * ↑(o'⁻¹ : (AdeleRing K)ˣ)) * Units.mul_inv c'
      rw [this]
      exact mul_mem hu (mul_mem ho.1 ho'.2)
    · rw [← mul_add, he, ← mul_assoc, hCCi, one_mul]
  · rintro ⟨p, hp, u, hu, rfl⟩
    refine ⟨C * p, mul_mem hC hp, C * u, ?_, (mul_add _ _ _).symm⟩
    have : C * u * (↑a * ↑(δ⁻¹ : (AdeleRing K)ˣ)) = (u * (↑a * ↑o * ↑c *
        (↑(c'⁻¹ : (AdeleRing K)ˣ) * (↑(o'⁻¹ : (AdeleRing K)ˣ) * ↑(δ⁻¹ : (AdeleRing K)ˣ))))) *
        (↑(o⁻¹ : (AdeleRing K)ˣ) * ↑o') := by
      simp only [C]
      linear_combination (-(u * ↑c * ↑(c'⁻¹ : (AdeleRing K)ˣ) * ↑a * ↑(δ⁻¹ : (AdeleRing K)ˣ)) *
        (↑(o'⁻¹ : (AdeleRing K)ˣ) * ↑o')) * Units.mul_inv o +
        (-(u * ↑c * ↑(c'⁻¹ : (AdeleRing K)ˣ) * ↑a * ↑(δ⁻¹ : (AdeleRing K)ˣ))) * Units.inv_mul o'
    rw [this]
    exact mul_mem hu (mul_mem ho.2 ho'.1)

omit hO hK in
public theorem upperGL_congr {a a' δ δ' : (AdeleRing K)ˣ} {β β' : AdeleRing K} (ha : a = a')
    (hδ : δ = δ') (hβ : β = β') : upperGL a δ β = upperGL a' δ' β' := by
  rw [ha, hδ, hβ]

omit hO hK in
public theorem upperGL_inv_zero (o o' : (AdeleRing K)ˣ) :
    (upperGL o o' 0)⁻¹ = upperGL o⁻¹ o'⁻¹ 0 :=
  inv_upperGL_zero_aux o o'

omit hO hK in
public theorem exists_mapO_upperGL {o o' : (AdeleRing K)ˣ} (ho : IsIntUnit o)
    (ho' : IsIntUnit o') : ∃ κ : GL (Fin 2) (integralAdeles K), mapO κ = upperGL o o' 0 :=
  exists_map_subtype_upperGL _ ho ho'

omit hO hK in
public theorem exists_mapK_upperGL {c c' : (AdeleRing K)ˣ} (hc : IsPrincUnit c)
    (hc' : IsPrincUnit c') : ∃ γ : GL (Fin 2) (principalAdeles K), mapK γ = upperGL c c' 0 :=
  exists_map_subtype_upperGL _ hc hc'

omit hO hK in
/-- `(a o c, β'; 0, δ o' c') n(z) = (o, 0; 0, o') (a, β; 0, δ) n(C z + d₀) (c, 0; 0, c')` with
`C = c / c'` and `d₀ = (β' / (o c') - β) / a`. -/
public theorem upperGL_mul_upperRightHom_eq (a δ o o' c c' : (AdeleRing K)ˣ)
    (β β' z : AdeleRing K) :
    upperGL (a * o * c) (δ * o' * c') β' * GeneralLinearGroup.upperRightHom z =
      upperGL o o' 0 * (upperGL a δ β * GeneralLinearGroup.upperRightHom
        ((c : AdeleRing K) * ((c'⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * z +
          (β' * (((o * c')⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) - β) *
            ((a⁻¹ : (AdeleRing K)ˣ) : AdeleRing K))) * upperGL c c' 0 := by
  rw [upperRightHom_eq_upperGL, upperRightHom_eq_upperGL, upperGL_mul, upperGL_mul, upperGL_mul,
    upperGL_mul]
  refine upperGL_congr (by simp only [mul_one]; ac_rfl) (by simp only [mul_one]; ac_rfl) ?_
  simp only [Units.val_mul, Units.val_one, mul_one, mul_zero, zero_add, add_zero, zero_mul,
    _root_.mul_inv_rev]
  linear_combination -(z * ↑a * ↑o * ↑c) * Units.mul_inv c' -
    (↑o * ↑c' * (β' * (↑(c'⁻¹ : (AdeleRing K)ˣ) * ↑(o⁻¹ : (AdeleRing K)ˣ)) - β)) *
      Units.mul_inv a + (-β') * ((↑c' * ↑(c'⁻¹ : (AdeleRing K)ˣ)) * Units.mul_inv o +
        Units.mul_inv c')

/-- **The constant term only depends on the classes of the diagonal entries.** -/
public theorem cuspSum_upperGL_eq {a δ o o' c c' : (AdeleRing K)ˣ} (β β' : AdeleRing K)
    (ho : IsIntUnit o) (ho' : IsIntUnit o') (hc : IsPrincUnit c) (hc' : IsPrincUnit c')
    {s s' : Finset (AdeleRing K)} (hs : IsCuspTransversal (upperGL a δ β) s)
    (hs' : IsCuspTransversal (upperGL (a * o * c) (δ * o' * c') β') s') :
    cuspSum F (upperGL (a * o * c) (δ * o' * c') β') s' = cuspSum F (upperGL a δ β) s := by
  classical
  obtain ⟨κo, hκo⟩ := exists_mapO_upperGL ho ho'
  obtain ⟨γc, hγc⟩ := exists_mapK_upperGL hc hc'
  have hCu : IsUnit ((c : AdeleRing K) * ((c'⁻¹ : (AdeleRing K)ˣ) : AdeleRing K)) :=
    c.isUnit.mul (c'⁻¹).isUnit
  obtain ⟨Ci, hCi⟩ : ∃ Ci : AdeleRing K,
      (c : AdeleRing K) * ((c'⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * Ci = 1 :=
    ⟨((hCu.unit⁻¹ : (AdeleRing K)ˣ) : AdeleRing K), hCu.mul_val_inv⟩
  generalize hC : (c : AdeleRing K) * ((c'⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) = C at hCu hCi
  generalize hd : (β' * (((o * c')⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) - β) *
    ((a⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) = d₀
  have hid : ∀ z, upperGL (a * o * c) (δ * o' * c') β' * GeneralLinearGroup.upperRightHom z =
      mapO κo * (upperGL a δ β * GeneralLinearGroup.upperRightHom (C * z + d₀)) * mapK γc := by
    intro z
    rw [hκo, hγc, ← hC, ← hd]
    exact upperGL_mul_upperRightHom_eq a δ o o' c c' β β' z
  have hφinj : Function.Injective fun z => C * z + d₀ := fun z z' h => by
    simp only [add_left_inj] at h
    exact hCu.mul_left_cancel h
  have hmem := fun y => (hC ▸ mem_sup_stab_upperGL_iff (a := a) (δ := δ) β β' ho ho' hc hc' y)
  have hφs : IsCuspTransversal (upperGL a δ β) (s'.image fun z => C * z + d₀) := by
    intro y
    obtain ⟨z', ⟨hz', hz'y⟩, huniq⟩ := hs' (Ci * (y - d₀))
    have key : ∀ z'', y - (C * z'' + d₀) = C * (Ci * (y - d₀) - z'') := by
      intro z''
      linear_combination -(y - d₀) * hCi
    refine ⟨C * z' + d₀, ⟨Finset.mem_image_of_mem _ hz', ?_⟩, ?_⟩
    · rwa [key, hmem]
    · rintro w ⟨hw, hwy⟩
      obtain ⟨z'', hz'', rfl⟩ := Finset.mem_image.1 hw
      rw [key, hmem] at hwy
      rw [huniq z'' ⟨hz'', hwy⟩]
  rw [cuspSum_eq_of_isCuspTransversal hO hK _ hs hφs, cuspSum, cuspSum,
    Finset.sum_image fun _ _ _ _ h => hφinj h]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [hid, hK, hO]

end CuspSum

public theorem glMap_upperGL {K' : Type u} [Field K'] (σ : K ≃+* K') (a δ : (AdeleRing K)ˣ)
    (β : AdeleRing K) : glMap σ (upperGL a δ β) =
      upperGL (Units.map (adeleMap σ).toMonoidHom a) (Units.map (adeleMap σ).toMonoidHom δ)
        (adeleMap σ β) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glMap_apply, coe_upperGL, coe_upperGL]
  fin_cases i <;> fin_cases j <;> simp

/-- **`F - F ∘ α` is cuspidal when `α` fixes the divisor classes.** Let `α` be an automorphism of
`K` such that every idele `a` satisfies `α(a) = a o c` with `o` a unit of `O` and `c ∈ K^×`, and
let `F` be left `GL₂(O)`- and right `GL₂(K)`-invariant. Then `F - F ∘ α` satisfies the cusp
condition. -/
public theorem starCusp_sub_comp_glMap (α : K ≃+* K) {Λ : Type w} [CommRing Λ]
    {F : GL (Fin 2) (AdeleRing K) → Λ} (hO : ∀ κ x, F (mapO κ * x) = F x)
    (hK : ∀ γ x, F (x * mapK γ) = F x)
    (hα : ∀ a : (AdeleRing K)ˣ, ∃ o c : (AdeleRing K)ˣ, IsIntUnit o ∧ IsPrincUnit c ∧
      Units.map (adeleMap α).toMonoidHom a = a * o * c) :
    StarCusp K Λ (fun x => F x - F (glMap α x)) := by
  classical
  intro x s hs
  obtain ⟨κ, a, δ, β, rfl⟩ := exists_iwasawa x
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  change ∑ z ∈ s, F (mapO κ * upperGL a δ β * GeneralLinearGroup.upperRightHom z) =
    ∑ z ∈ s, F (glMap α (mapO κ * upperGL a δ β * GeneralLinearGroup.upperRightHom z))
  have hs₀ : IsCuspTransversal (upperGL a δ β) s :=
    (isCuspTransversal_mapO_mul_iff κ _ s).1 hs
  obtain ⟨κ', hκ'⟩ := glMap_mapO α κ
  have hsα : IsCuspTransversal (mapO κ' * glMap α (upperGL a δ β)) (s.image (adeleMap α)) := by
    have := isTransversal_image_adeleMap α (mapO κ * upperGL a δ β) hs
    rwa [map_mul, hκ'] at this
  rw [isCuspTransversal_mapO_mul_iff, glMap_upperGL] at hsα
  obtain ⟨o, c, ho, hc, hoc⟩ := hα a
  obtain ⟨o', c', ho', hc', hoc'⟩ := hα δ
  rw [hoc, hoc'] at hsα
  have h1 : ∑ z ∈ s, F (glMap α (mapO κ * upperGL a δ β * GeneralLinearGroup.upperRightHom z)) =
      cuspSum F (upperGL (a * o * c) (δ * o' * c') (adeleMap α β)) (s.image (adeleMap α)) := by
    rw [cuspSum, sum_image_adeleMap]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_mul, map_mul, hκ', glMap_upperGL, glMap_upperRightHom, hoc, hoc', mul_assoc, hO]
  rw [h1, cuspSum_upperGL_eq hO hK β _ ho ho' hc hc' hs₀ hsα]
  exact cuspSum_mapO_mul hO κ _ s

section DoubleCoset

/-- The double coset `Z(A) GL₂(O) X GL₂(K)` of `X ∈ GL₂(A)`. -/
public def centralDoubleCoset (X : GL (Fin 2) (AdeleRing K)) : Set (GL (Fin 2) (AdeleRing K)) :=
  {g | ∃ (c : (AdeleRing K)ˣ) (κ : GL (Fin 2) (integralAdeles K))
    (γ : GL (Fin 2) (principalAdeles K)), g = scalarGL c * mapO κ * X * mapK γ}

variable {X g : GL (Fin 2) (AdeleRing K)}

public theorem mem_centralDoubleCoset_self (X : GL (Fin 2) (AdeleRing K)) :
    X ∈ centralDoubleCoset X :=
  ⟨1, 1, 1, by simp only [map_one, one_mul, mul_one]⟩

public theorem mapO_mul_mem_centralDoubleCoset (κ : GL (Fin 2) (integralAdeles K))
    (hg : g ∈ centralDoubleCoset X) : mapO κ * g ∈ centralDoubleCoset X := by
  obtain ⟨c, κ', γ, rfl⟩ := hg
  refine ⟨c, κ * κ', γ, ?_⟩
  rw [map_mul]
  simp only [← mul_assoc]
  rw [scalarGL_mul_comm c (mapO κ)]

public theorem mul_mapK_mem_centralDoubleCoset (γ : GL (Fin 2) (principalAdeles K))
    (hg : g ∈ centralDoubleCoset X) : g * mapK γ ∈ centralDoubleCoset X := by
  obtain ⟨c, κ, γ', rfl⟩ := hg
  exact ⟨c, κ, γ' * γ, by simp only [map_mul, mul_assoc]⟩

public theorem scalarGL_mul_mem_centralDoubleCoset (c : (AdeleRing K)ˣ)
    (hg : g ∈ centralDoubleCoset X) : scalarGL c * g ∈ centralDoubleCoset X := by
  obtain ⟨c', κ, γ, rfl⟩ := hg
  exact ⟨c * c', κ, γ, by simp only [map_mul, mul_assoc]⟩

public theorem mapO_mul_mem_centralDoubleCoset_iff (κ : GL (Fin 2) (integralAdeles K)) :
    mapO κ * g ∈ centralDoubleCoset X ↔ g ∈ centralDoubleCoset X := by
  refine ⟨fun h => ?_, mapO_mul_mem_centralDoubleCoset κ⟩
  have := mapO_mul_mem_centralDoubleCoset κ⁻¹ h
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at this

public theorem mul_mapK_mem_centralDoubleCoset_iff (γ : GL (Fin 2) (principalAdeles K)) :
    g * mapK γ ∈ centralDoubleCoset X ↔ g ∈ centralDoubleCoset X := by
  refine ⟨fun h => ?_, mul_mapK_mem_centralDoubleCoset γ⟩
  have := mul_mapK_mem_centralDoubleCoset γ⁻¹ h
  rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at this

public theorem scalarGL_mul_mem_centralDoubleCoset_iff (c : (AdeleRing K)ˣ) :
    scalarGL c * g ∈ centralDoubleCoset X ↔ g ∈ centralDoubleCoset X := by
  refine ⟨fun h => ?_, scalarGL_mul_mem_centralDoubleCoset c⟩
  have := scalarGL_mul_mem_centralDoubleCoset c⁻¹ h
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at this

end DoubleCoset

section ClassNumber

variable (k : Type u) [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K]
  [IsScalarTower k (RatFunc k) K] [FunctionField k K]

public theorem idelDiv_units_map_adeleMap (α : K ≃+* K) (c : (AdeleRing K)ˣ) (w : Place K) :
    idelDiv k K (Units.map (adeleMap α).toMonoidHom c) w = idelDiv k K c (placeComap α w) := by
  rw [idelDiv_apply, idelDiv_apply]
  exact ordC_completionEquiv α (isDiscrete k w) _

public theorem divNorm_idelDiv_units_map_adeleMap (α : K ≃+* K) (c : (AdeleRing K)ˣ) :
    divNorm K (idelDiv k K (Units.map (adeleMap α).toMonoidHom c)) = divNorm K (idelDiv k K c) := by
  have he : idelDiv k K (Units.map (adeleMap α).toMonoidHom c) =
      Finsupp.equivMapDomain (placeEquiv α) (idelDiv k K c) := by
    ext w
    rw [Finsupp.equivMapDomain_apply, idelDiv_units_map_adeleMap]
    rfl
  rw [he, divNorm, divNorm, Finsupp.prod_equivMapDomain]
  refine Finsupp.prod_congr fun v _ => ?_
  change ((placeComap α.symm v).resCard : ℚ) ^ _ = _
  rw [resCard_placeComap]

/-- With class number one, an automorphism `α` fixes every idele class: `α(a) = a o c` with
`o ∈ O^×` and `c ∈ K^×`. -/
public theorem exists_isIntUnit_isPrincUnit (α : K ≃+* K)
    (hcl : ∀ D : Place K →₀ ℤ, divNorm K D = 1 → ∃ κ : K, κ ≠ 0 ∧ principalDivisor k K κ = D)
    (a : (AdeleRing K)ˣ) : ∃ o c : (AdeleRing K)ˣ, IsIntUnit o ∧ IsPrincUnit c ∧
      Units.map (adeleMap α).toMonoidHom a = a * o * c := by
  set a' := Units.map (adeleMap α).toMonoidHom a
  obtain ⟨κ, hκ, hdiv⟩ := hcl (idelDiv k K a' - idelDiv k K a) (by
    rw [divNorm_sub k, divNorm_idelDiv_units_map_adeleMap, div_self (divNorm_pos k _).ne'])
  set c := diagUnit k hκ
  have hc : IsPrincUnit c := by
    refine ⟨⟨κ, fun v => rfl⟩, ⟨κ⁻¹, fun v => ?_⟩⟩
    have : ((c⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) = diag k K κ⁻¹ :=
      Units.inv_eq_of_mul_eq_one_right
        (by rw [coe_diagUnit, ← map_mul, mul_inv_cancel₀ hκ, map_one])
    rw [this]
    rfl
  set o := a⁻¹ * a' * c⁻¹
  have ho0 : idelDiv k K o = 0 := by
    rw [idelDiv_mul, idelDiv_mul, idelDiv_inv, idelDiv_inv, idelDiv_diagUnit, hdiv]
    abel
  obtain ⟨o', ho'⟩ := exists_integralUnit_of_idelDiv_eq_zero k ho0
  have ho : IsIntUnit o := by
    refine ⟨ho' ▸ (o' : integralAdeles K).2, ?_⟩
    have : ((o⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) = ((o'⁻¹ : (integralAdeles K)ˣ) :
        integralAdeles K) :=
      Units.inv_eq_of_mul_eq_one_right (by rw [← ho']; exact congrArg Subtype.val o'.mul_inv)
    rw [this]
    exact (o'⁻¹ : (integralAdeles K)ˣ).1.2
  refine ⟨o, c, ho, hc, ?_⟩
  simp only [o]
  group

/-- **A nonzero element of `C(Λ)` from an automorphism.** Let `α` be an automorphism of `K`
fixing every idele class (`α(a) ∈ a O^× K^×`) and `X ∈ GL₂(A)` with `α(X)` outside the double
coset `Z(A) GL₂(O) X GL₂(K)`. If `p` is invertible in the algebraically closed field `Ω`, then
`C(Ω) ≠ 0`: the twist by `D ↦ c^{deg D}`, `c² = q`, of `1_S - 1_S ∘ α`, `S` the double coset, is
a nonzero element. -/
public theorem cuspFormsCentralChar_ne_bot_of_glMap_notMem (α : K ≃+* K)
    (hα : ∀ a : (AdeleRing K)ˣ, ∃ o c : (AdeleRing K)ˣ, IsIntUnit o ∧ IsPrincUnit c ∧
      Units.map (adeleMap α).toMonoidHom a = a * o * c)
    {X : GL (Fin 2) (AdeleRing K)} (hX : glMap α X ∉ centralDoubleCoset X)
    {Ω : Type w} [Field Ω] [IsAlgClosed Ω] (hp : IsUnit (ringChar k : Ω)) {c : Ωˣ}
    (hc : (c : Ω) ^ 2 = Nat.card k) : cuspFormsCentralChar K Ω ≠ ⊥ := by
  classical
  let F : GL (Fin 2) (AdeleRing K) → Ω := (centralDoubleCoset X).indicator 1
  have hO : ∀ κ x, F (mapO κ * x) = F x := fun κ x => by
    simp only [F, Set.indicator_apply, mapO_mul_mem_centralDoubleCoset_iff, Pi.one_apply]
  have hK : ∀ γ x, F (x * mapK γ) = F x := fun γ x => by
    simp only [F, Set.indicator_apply, mul_mapK_mem_centralDoubleCoset_iff, Pi.one_apply]
  have hZ : ∀ a x, F (scalarGL a * x) = F x := fun a x => by
    simp only [F, Set.indicator_apply, scalarGL_mul_mem_centralDoubleCoset_iff, Pi.one_apply]
  let f : GL (Fin 2) (AdeleRing K) → Ω := fun x => F x - F (glMap α x)
  have h1 : ∀ κ x, f (mapO κ * x) = f x := fun κ x => by
    obtain ⟨κ', hκ'⟩ := glMap_mapO α κ
    simp only [f, map_mul, hκ', hO]
  have h2 : ∀ γ x, f (x * mapK γ) = f x := fun γ x => by
    obtain ⟨γ', hγ'⟩ := glMap_mapK α γ
    simp only [f, map_mul, hγ', hK]
  have h3 : StarCusp K Ω f := starCusp_sub_comp_glMap α hO hK hα
  have h4 : ∀ v, IsCentralEigenvalueAt v f 1 := fun v a ha x => by
    obtain ⟨π, hπ, rfl⟩ := eq_scalarGL_of_isCentralDataAt k ha
    simp only [centralOperator, f, map_mul, glMap_scalarGL, hZ, one_mul]
  have hf := mem_cuspFormsCentralChar (isCuspFormCentralChar_unramifiedTwist k hp hc h1 h2 h3 h4)
  intro hbot
  rw [hbot, Submodule.mem_bot] at hf
  have h0 := congrFun hf X
  simp only [unramifiedTwist_apply, f, F, Set.indicator_of_mem (mem_centralDoubleCoset_self X),
    Set.indicator_of_notMem hX, Pi.one_apply, sub_zero, mul_one, Pi.zero_apply] at h0
  exact (detCharacter k (degreeCharacter k K c) X).ne_zero h0

end ClassNumber

end Stacks.Drinfeld

end
