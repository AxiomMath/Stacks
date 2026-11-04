module

public import Mathlib.FieldTheory.KrullTopology
import StacksCore.FieldTheory.Galois.Basic
import StacksCore.FieldTheory.PrimitiveElement

/-! # Krull topology on Galois groups -/

@[expose] public section

open IntermediateField Filter Topology

/-- **Stacks 0BMJ** (action is continuous).
For `x : L` and `y : L` algebraic over `K`, the set of `σ ∈ Gal(L/K)` sending `x` to `y` is
open in the Krull topology. -/
@[stacks 0BMJ "continuous"]
theorem isOpen_krullTopology_apply_eq (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) {y : L} (hy : IsAlgebraic K y) : IsOpen {σ : Gal(L/K) | σ x = y} := by
  obtain h | h := Set.eq_empty_or_nonempty {σ : Gal(L/K) | σ x = y}
  · simp [h]
  obtain ⟨σ₀, hσ₀xy : _ = _⟩ := h
  rw [← (Homeomorph.divLeft σ₀).symm.isOpen_preimage]
  have : FiniteDimensional K K⟮y⟯ := adjoin.finiteDimensional hy.isIntegral
  convert K⟮y⟯.fixingSubgroup_isOpen using 1
  ext σ
  simp [hσ₀xy, eq_comm, AlgEquiv.eq_symm_apply]

/-- **Stacks 0BMJ** (action is continuous, algebraic extension).
For an algebraic extension `L/K` and any `x y : L`, the set of `σ ∈ Gal(L/K)` sending `x`
to `y` is open in the Krull topology. -/
@[stacks 0BMJ "continuous"]
theorem isOpen_krullTopology_apply_eq' (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (x y : L) : IsOpen {σ : Gal(L/K) | σ x = y} :=
  isOpen_krullTopology_apply_eq K x <| Algebra.IsAlgebraic.isAlgebraic y

/-- A neighborhood of `σ` in the Krull topology contains `σ * τ` for all `τ` fixing some
finite-dimensional intermediate field. -/
private theorem exists_finiteDimensional_of_mem_nhds_krullTopology {K L : Type*} [Field K]
    [Field L] [Algebra K L] {σ : Gal(L/K)} {u : Set Gal(L/K)} (hu : u ∈ 𝓝 σ) :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧ ∀ τ ∈ E.fixingSubgroup, σ * τ ∈ u :=
  (krullTopology_mem_nhds_one_iff K L _).mp
    ((continuous_id.const_mul σ).tendsto' 1 σ (mul_one σ) hu)

/-- For a separable extension `L/K`, the sets `{τ ∈ Gal(L/K) | τ x = σ x}` indexed by
`x : L` form a neighborhood basis of `σ` in the Krull topology. -/
theorem hasBasis_nhds_krullTopology {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] {σ : Gal(L/K)} :
    (𝓝 σ).HasBasis (fun _ ↦ True) fun x : L ↦ {τ | τ x = σ x} := by
  refine ⟨fun u ↦ ⟨fun hu ↦ ?_, ?_⟩⟩
  · obtain ⟨E, _, hE⟩ := exists_finiteDimensional_of_mem_nhds_krullTopology hu
    obtain ⟨x, -, rfl⟩ := E.exists_primitive_element
    refine ⟨x, trivial, fun τ (hτx : _ = _) ↦ ?_⟩
    simpa using hE (σ⁻¹ * τ) <| by simp [hτx]
  · rintro ⟨x, -, hx⟩
    exact mem_of_superset (isOpen_krullTopology_apply_eq K _ (Algebra.IsAlgebraic.isAlgebraic _)
      |>.mem_nhds rfl) hx

/-- **Stacks 0BMJ** (universal property of the Krull topology).
A map `f : X → Gal(L/K)` from a topological space `X` is continuous whenever the induced
action `X × L → L` is continuous, expressed here as: for every `x : L` and `y : L`,
the set `{i ∈ X | f i x = y}` is open. -/
@[stacks 0BMJ "universal property"]
theorem continuous_krullTopology {K L X : Type*} [Field K] [Field L] [Algebra K L]
    [TopologicalSpace X] {f : X → Gal(L/K)} (hf : ∀ x y, IsOpen {i | f i x = y}) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x u hx ↦ by
    obtain ⟨E, _, hE⟩ := exists_finiteDimensional_of_mem_nhds_krullTopology hx
    obtain ⟨s, rfl⟩ := (essFiniteType_iff (K := E)).mp inferInstance
    refine mem_map.mpr <| mem_of_superset
      ((isOpen_biInter_finset (s := s) fun i _ ↦ hf i (f x i)).mem_nhds (x := x) (by simp))
      fun i hi ↦ ?_
    simpa using hE ((f x)⁻¹ * f i) <| by simpa [AlgEquiv.symm_apply_eq] using hi
