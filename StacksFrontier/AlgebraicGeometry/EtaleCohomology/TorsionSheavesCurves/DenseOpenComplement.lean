module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.GenericLocalConstancy
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeProper
public import Mathlib.Topology.KrullDimension

/-!
# The complement of a dense open in a curve

On a Noetherian scheme of dimension at most one, a point outside a dense open subset is closed:
it is not the generic point of a component, since those lie in every dense open, so the closure
of a point below it would give a chain of length two. Hence the complement of a dense open in a
scheme of finite type and dimension at most one over a field is finite over the field.

This is the first sentence of the proof of Stacks Tag 0GJA.

## Main results

* `AlgebraicGeometry.isClosed_singleton_of_not_mem_of_dense`.
* `AlgebraicGeometry.isFinite_comp_of_range_eq_compl_of_dense`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

/-- The closure of a point, as an irreducible closed subset. -/
def irreducibleClosedsOfPoint {α : Type*} [TopologicalSpace α] (x : α) : IrreducibleCloseds α :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- A point `x ≠ y` in the closure of `y` has strictly smaller closure than `y`. -/
theorem irreducibleClosedsOfPoint_lt_of_mem_closure {α : Type*} [TopologicalSpace α] [T0Space α]
    {x y : α} (h : x ∈ closure ({y} : Set α)) (hne : x ≠ y) :
    irreducibleClosedsOfPoint x < irreducibleClosedsOfPoint y := by
  refine lt_of_le_of_ne (fun w hw => closure_minimal (Set.singleton_subset_iff.mpr h)
    isClosed_closure hw) fun he => hne ?_
  have : closure ({x} : Set α) = closure {y} :=
    congrArg (fun F : IrreducibleCloseds α => (F : Set α)) he
  exact (inseparable_iff_closure_eq.mpr this).eq

/-- **A point outside a dense open subset of a Noetherian sober space of dimension at most one is
closed.** -/
theorem isClosed_singleton_of_not_mem_of_dense {α : Type*} [TopologicalSpace α]
    [NoetherianSpace α] [QuasiSober α] [T0Space α] (hdim : topologicalKrullDim α ≤ 1)
    {V : Set α} (hVo : IsOpen V) (hV : Dense V) {z : α} (hz : z ∉ V) : IsClosed ({z} : Set α) := by
  by_contra hcl
  have hne : closure ({z} : Set α) ≠ {z} := fun h => hcl (h ▸ isClosed_closure)
  obtain ⟨z', hz', hzz'⟩ : ∃ z' ∈ closure ({z} : Set α), z' ≠ z := by
    by_contra h
    push Not at h
    exact hne (Set.Subset.antisymm (fun y hy => h y hy) subset_closure)
  -- the component through `z` and its generic point
  obtain ⟨C, hC, hzC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible {z} isIrreducible_singleton
  have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  set η := hC.1.genericPoint
  have hη : closure ({η} : Set α) = C := by
    have h := hC.1.isGenericPoint_genericPoint_closure
    rwa [hCcl.closure_eq] at h
  have hηC : closure ({η} : Set α) ∈ irreducibleComponents α := hη ▸ hC
  -- the generic point lies in `V`
  have hηV : η ∈ V := by
    obtain ⟨W, hWo, hηW, hWsub⟩ :=
      exists_isOpen_mem_subset_closure_of_mem_irreducibleComponents hηC
    obtain ⟨y, hyW, hyV⟩ := hV.inter_open_nonempty W hWo ⟨η, hηW⟩
    exact (specializes_iff_mem_closure.mpr (hWsub hyW)).mem_open hVo hyV
  -- a chain of length two
  have h1 : irreducibleClosedsOfPoint z' < irreducibleClosedsOfPoint z :=
    irreducibleClosedsOfPoint_lt_of_mem_closure hz' hzz'
  have h2 : irreducibleClosedsOfPoint z < irreducibleClosedsOfPoint η :=
    irreducibleClosedsOfPoint_lt_of_mem_closure (hη ▸ hzC rfl) fun h => hz (h ▸ hηV)
  let p : LTSeries (IrreducibleCloseds α) :=
    ⟨2, ![irreducibleClosedsOfPoint z', irreducibleClosedsOfPoint z,
      irreducibleClosedsOfPoint η], fun i => by fin_cases i <;> simp [h1, h2]⟩
  have : (2 : WithBot ℕ∞) ≤ 1 := (Order.LTSeries.length_le_krullDim p).trans hdim
  exact absurd this (by decide)

/-- A sober space all of whose points are closed has dimension at most zero. -/
theorem topologicalKrullDim_nonpos_of_isClosed_singleton {α : Type*} [TopologicalSpace α]
    [QuasiSober α] (h : ∀ x : α, IsClosed ({x} : Set α)) : topologicalKrullDim α ≤ 0 := by
  refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun Z W hZW => ?_
  have hsing : ∀ Y : IrreducibleCloseds α, ∃ x, (Y : Set α) = {x} := fun Y => by
    obtain ⟨x, hx⟩ := QuasiSober.sober Y.isIrreducible Y.isClosed
    exact ⟨x, by rw [← hx.def, (h x).closure_eq]⟩
  obtain ⟨x, hx⟩ := hsing Z
  obtain ⟨y, hy⟩ := hsing W
  have hxy : x = y := by
    have hxZ : x ∈ (Z : Set α) := by rw [hx]; rfl
    have : x ∈ (W : Set α) := hZW hxZ
    rwa [hy] at this
  intro w hw
  change w ∈ (Z : Set α)
  rwa [hx, hxy, ← hy]

/-- **The complement of a dense open in a curve is finite over the base field.** Let `X` be of
finite type over a field `k` with `dim X ≤ 1`, `V ⊆ X` a dense open and `i : Z ⟶ X` a closed
immersion onto the complement of `V`. Then `Z` is finite over `k`. -/
theorem isFinite_comp_of_range_eq_compl_of_dense (k : Type u) [Field k] {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1) (V : X.Opens) (hV : Dense (V : Set X)) (i : Z ⟶ X)
    [IsClosedImmersion i] (hi : Set.range i.base = (V : Set X)ᶜ) : IsFinite (i ≫ f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have hcl : ∀ z : Z, IsClosed ({z} : Set Z) := by
    intro z
    have hz : i.base z ∉ (V : Set X) := by
      have : i.base z ∈ Set.range i.base := ⟨z, rfl⟩
      rwa [hi] at this
    have : ({z} : Set Z) = i.base ⁻¹' {i.base z} := by
      ext w
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => i.isClosedEmbedding.injective h⟩
    rw [this]
    exact (isClosed_singleton_of_not_mem_of_dense hdim V.isOpen hV hz).preimage i.continuous
  rcases isEmpty_or_nonempty Z with hZ | hZ
  · have := Stacks.Morphisms.isFiniteLocallyFreeOfRank_zero_of_isEmpty (i ≫ f)
    exact Stacks.Morphisms.isFinite_of_isFiniteLocallyFreeOfRank (i ≫ f) 0
  · have : Nonempty (IrreducibleCloseds Z) :=
      ⟨irreducibleClosedsOfPoint (Classical.arbitrary Z)⟩
    have h0 : topologicalKrullDim Z = 0 :=
      le_antisymm (topologicalKrullDim_nonpos_of_isClosed_singleton hcl) Order.krullDim_nonneg
    exact isFinite_of_finiteType_of_dimension_zero k (i ≫ f) h0

end AlgebraicGeometry

end
