module

public import Mathlib.Algebra.Module.Lattice
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.HeckeData

/-!
# Lattices in `K_v^n` and the action of `GL_n(K_v)`

Let `v` be a place of a field `K`, with completion `K_v` and ring of integers `O_v`. An
`O_v`-lattice in `K_v^n` is a finitely generated `O_v`-submodule spanning `K_v^n` over `K_v`
(Mathlib's `Submodule.IsLattice`). The group `GL_n(K_v)` acts on the `O_v`-submodules of `K_v^n`
by `g · Λ = g Λ`, preserving lattices. We show that the stabiliser of the standard lattice
`O_v^n` is `GL_n(O_v)`, that is, the matrices `g` with `g` and `g⁻¹` integral, and that at a
discrete place (every place of a function field) `O_v` is a discrete valuation ring and every
lattice is `g O_v^n` for some `g ∈ GL_n(K_v)`.

## Main definitions

* `Stacks.Drinfeld.Lattice.stdLattice` — the standard lattice `O_v^n`.
* `Stacks.Drinfeld.Lattice.translate` — the lattice `g Λ`.

## Main results

* `Stacks.Drinfeld.Lattice.isLattice_stdLattice`, `Stacks.Drinfeld.Lattice.isLattice_translate`.
* `Stacks.Drinfeld.Lattice.translate_stdLattice_eq_iff` — `g O_v^n = O_v^n` exactly when `g` and
  `g⁻¹` have entries in `O_v`.
* `Stacks.Drinfeld.Lattice.isDiscreteValuationRing_integers` — `O_v` is a DVR at a discrete place.
* `Stacks.Drinfeld.Lattice.exists_eq_translate_stdLattice` — at a discrete place every lattice in
  `K_v^n` is `g O_v^n`.
-/

@[expose] public noncomputable section

open Matrix Module

universe u

namespace Stacks.Drinfeld.Lattice

open Stacks.Adeles

variable {K : Type u} [Field K] (v : Place K) (n : ℕ)

/-- The standard lattice `O_v^n ⊆ K_v^n`. -/
public def stdLattice : Submodule v.integers (Fin n → v.completion) :=
  LinearMap.range ((Algebra.linearMap v.integers v.completion).compLeft (Fin n))

variable {v n}

/-- A vector lies in `O_v^n` exactly when all its coordinates lie in `O_v`. -/
public theorem mem_stdLattice {x : Fin n → v.completion} :
    x ∈ stdLattice v n ↔ ∀ i, x i ∈ v.integers := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact (y i).2
  · intro h
    exact ⟨fun i => ⟨x i, h i⟩, rfl⟩

/-- The standard basis vectors lie in `O_v^n`. -/
private theorem single_one_mem_stdLattice (j : Fin n) :
    (Pi.single j 1 : Fin n → v.completion) ∈ stdLattice v n := by
  refine mem_stdLattice.2 fun l => ?_
  rw [Pi.single_apply]
  split_ifs
  · exact v.integers.one_mem
  · exact v.integers.zero_mem

variable (v n) in
/-- `O_v^n` is a lattice in `K_v^n`. -/
public theorem isLattice_stdLattice : (stdLattice v n).IsLattice v.completion where
  fg := by
    rw [stdLattice, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  span_eq_top := by
    refine eq_top_iff.2 ((Pi.basisFun v.completion (Fin n)).span_eq.symm.le.trans
      (Submodule.span_mono ?_))
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact single_one_mem_stdLattice i

/-- The `O_v`-submodule `g Λ` of `K_v^n`, for `g ∈ GL_n(K_v)`. -/
public def translate (g : GL (Fin n) v.completion)
    (Λ : Submodule v.integers (Fin n → v.completion)) :
    Submodule v.integers (Fin n → v.completion) :=
  Λ.map ((Matrix.toLin' (g : Matrix (Fin n) (Fin n) v.completion)).restrictScalars v.integers)

public theorem mulVec_inv_mulVec (g : GL (Fin n) v.completion) (x : Fin n → v.completion) :
    (g⁻¹ : GL (Fin n) v.completion).val *ᵥ (g.val *ᵥ x) = x := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

public theorem mulVec_mulVec_inv (g : GL (Fin n) v.completion) (x : Fin n → v.completion) :
    g.val *ᵥ ((g⁻¹ : GL (Fin n) v.completion).val *ᵥ x) = x := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

public theorem mem_translate {g : GL (Fin n) v.completion}
    {Λ : Submodule v.integers (Fin n → v.completion)} {x : Fin n → v.completion} :
    x ∈ translate g Λ ↔ (g⁻¹ : GL (Fin n) v.completion).val *ᵥ x ∈ Λ := by
  simp only [translate, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [mulVec_inv_mulVec]
  · intro h
    exact ⟨_, h, mulVec_mulVec_inv g x⟩

public theorem mulVec_mem_translate {g : GL (Fin n) v.completion}
    {Λ : Submodule v.integers (Fin n → v.completion)} {y : Fin n → v.completion} (hy : y ∈ Λ) :
    g.val *ᵥ y ∈ translate g Λ := by
  rwa [mem_translate, mulVec_inv_mulVec]

@[simp]
public theorem translate_one (Λ : Submodule v.integers (Fin n → v.completion)) :
    translate 1 Λ = Λ := by
  ext x
  rw [mem_translate, inv_one, Units.val_one, one_mulVec]

public theorem translate_mul (g h : GL (Fin n) v.completion)
    (Λ : Submodule v.integers (Fin n → v.completion)) :
    translate (g * h) Λ = translate g (translate h Λ) := by
  ext x
  rw [mem_translate, mem_translate, mem_translate, _root_.mul_inv_rev, Units.val_mul,
    ← mulVec_mulVec]

public theorem translate_mono (g : GL (Fin n) v.completion)
    {Λ Λ' : Submodule v.integers (Fin n → v.completion)} (h : Λ ≤ Λ') :
    translate g Λ ≤ translate g Λ' :=
  Submodule.map_mono h

public theorem translate_le_translate_iff (g : GL (Fin n) v.completion)
    {Λ Λ' : Submodule v.integers (Fin n → v.completion)} :
    translate g Λ ≤ translate g Λ' ↔ Λ ≤ Λ' := by
  refine ⟨fun h => ?_, translate_mono g⟩
  have := translate_mono g⁻¹ h
  rwa [← translate_mul, ← translate_mul, inv_mul_cancel, translate_one, translate_one] at this

public theorem translate_inv_translate (g : GL (Fin n) v.completion)
    (Λ : Submodule v.integers (Fin n → v.completion)) :
    translate g⁻¹ (translate g Λ) = Λ := by
  rw [← translate_mul, inv_mul_cancel, translate_one]

/-- `g Λ` is a lattice when `Λ` is. -/
public theorem isLattice_translate (g : GL (Fin n) v.completion)
    {Λ : Submodule v.integers (Fin n → v.completion)} (hΛ : Λ.IsLattice v.completion) :
    (translate g Λ).IsLattice v.completion where
  fg := hΛ.fg.map _
  span_eq_top := by
    rw [translate, Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image,
      hΛ.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact fun y => ⟨(g⁻¹ : GL (Fin n) v.completion).val *ᵥ y, by
      rw [Matrix.toLin'_apply, mulVec_mulVec_inv]⟩

/-- `g O_v^n ⊆ O_v^n` exactly when `g` has entries in `O_v`. -/
public theorem translate_stdLattice_le_iff (g : GL (Fin n) v.completion) :
    translate g (stdLattice v n) ≤ stdLattice v n ↔ ∀ i j, g.val i j ∈ v.integers := by
  constructor
  · intro h i j
    have := mem_stdLattice.1 (h (mulVec_mem_translate (g := g) (single_one_mem_stdLattice j))) i
    rwa [mulVec_single_one] at this
  · rintro h _ ⟨y, hy, rfl⟩
    refine mem_stdLattice.2 fun i => ?_
    simp only [LinearMap.coe_restrictScalars, Matrix.toLin'_apply, mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (h i j) (mem_stdLattice.1 hy j)

/-- **The stabiliser of `O_v^n` is `GL_n(O_v)`**: `g O_v^n = O_v^n` exactly when `g` and `g⁻¹`
have entries in `O_v`. -/
public theorem translate_stdLattice_eq_iff (g : GL (Fin n) v.completion) :
    translate g (stdLattice v n) = stdLattice v n ↔
      (∀ i j, g.val i j ∈ v.integers) ∧
        ∀ i j, (g⁻¹ : GL (Fin n) v.completion).val i j ∈ v.integers := by
  rw [← translate_stdLattice_le_iff, ← translate_stdLattice_le_iff]
  constructor
  · intro h
    refine ⟨h.le, ?_⟩
    conv_lhs => rw [← h]
    rw [translate_inv_translate]
  · rintro ⟨h₁, h₂⟩
    refine le_antisymm h₁ ?_
    have := translate_mono g h₂
    rwa [← translate_mul, mul_inv_cancel, translate_one] at this

/-- At a discrete place, the ring of integers `O_v` of the completion is a discrete valuation
ring: every nonzero element is a unit times a power of the uniformizer. -/
public theorem isDiscreteValuationRing_integers (hv : v.IsDiscrete) :
    IsDiscreteValuationRing v.integers := by
  set π : v.integers := ⟨v.coeRingHom v.unif, Place.coeRingHom_unif_mem_integers hv⟩
  have hπ := Place.isUniformizer_unif hv
  have hπv : Valued.v (π : v.completion) = v.unifVal := by
    change Valued.v (v.coeRingHom v.unif) = _
    rw [Place.valued_coeRingHom]
    rfl
  have hπ0 : (π : v.completion) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπv
    exact Place.unifVal_ne_zero hv hπv.symm
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨π, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π
      (fun h => hπ0 (congrArg Subtype.val h)) hπ.symm, fun {x} hx => ?_⟩
  have hx0 : (x : v.completion) ≠ 0 := fun h => hx (Subtype.ext h)
  have hord : 0 ≤ v.ordC x :=
    ((Place.mem_ball_iff_ordC hv (m := 0)).1 (Place.mem_ball_zero_iff.2 x.2)).resolve_left hx0
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hord
  have hpow0 : (π : v.completion) ^ m ≠ 0 := pow_ne_zero _ hπ0
  have hval : Valued.v ((x : v.completion) * ((π : v.completion) ^ m)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, map_pow, hπv, Place.valued_eq_unifVal_zpow_ordC hv hx0, hm,
      zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (Place.unifVal_ne_zero hv))]
  have hu : (x : v.completion) * ((π : v.completion) ^ m)⁻¹ ∈ v.integers :=
    (Valuation.mem_valuationSubring_iff _ _).2 hval.le
  have hunit : IsUnit (⟨_, hu⟩ : v.integers) :=
    (v.integers.valuation_eq_one_iff _).2 ((Place.integers_valuation_eq_one_iff _).2 hval)
  refine ⟨m, hunit.unit, Subtype.ext ?_⟩
  change (π : v.completion) ^ m * ((x : v.completion) * ((π : v.completion) ^ m)⁻¹) = x
  rw [mul_comm, mul_assoc, inv_mul_cancel₀ hpow0, mul_one]

/-- **Every lattice is a translate of the standard lattice**: at a discrete place, every
`O_v`-lattice `Λ ⊆ K_v^n` is `g O_v^n` for some `g ∈ GL_n(K_v)`, the matrix whose columns are an
`O_v`-basis of `Λ`. -/
public theorem exists_eq_translate_stdLattice (hv : v.IsDiscrete)
    {Λ : Submodule v.integers (Fin n → v.completion)} (hΛ : Λ.IsLattice v.completion) :
    ∃ g : GL (Fin n) v.completion, Λ = translate g (stdLattice v n) := by
  have := isDiscreteValuationRing_integers hv
  have := hΛ
  let b : Basis (Fin n) v.integers Λ := Module.finBasisOfFinrankEq _ _
    (by rw [Submodule.IsLattice.finrank_of_pi v.completion Λ, Fintype.card_fin])
  let bK := b.extendOfIsLattice v.completion
  let M : Matrix (Fin n) (Fin n) v.completion := (Pi.basisFun v.completion (Fin n)).toMatrix bK
  let : Invertible M := (Pi.basisFun v.completion (Fin n)).invertibleToMatrix bK
  refine ⟨unitOfInvertible M, ?_⟩
  have key : ∀ c : Fin n → v.integers,
      M *ᵥ (fun j => (c j : v.completion)) = ((∑ j, c j • b j : Λ) : Fin n → v.completion) := by
    intro c
    ext i
    simp [M, bK, mulVec, dotProduct, Basis.toMatrix_apply, Finset.sum_apply,
      mul_comm, Algebra.smul_def]
  ext x
  constructor
  · intro hx
    refine ⟨fun j => (b.repr ⟨x, hx⟩ j : v.completion),
      mem_stdLattice.2 fun j => (b.repr ⟨x, hx⟩ j).2, ?_⟩
    simp only [LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
    change M *ᵥ _ = x
    rw [key, b.sum_repr]
  · rintro ⟨y, hy, rfl⟩
    simp only [LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
    change M *ᵥ y ∈ Λ
    have hy' : y = fun j => ((⟨y j, mem_stdLattice.1 hy j⟩ : v.integers) : v.completion) := rfl
    rw [hy', key]
    exact Subtype.coe_prop _

end Stacks.Drinfeld.Lattice

end
