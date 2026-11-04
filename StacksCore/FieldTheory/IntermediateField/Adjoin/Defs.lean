module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-! # Intermediate fields -/

@[expose] public section

/-- The image of the top intermediate field under a surjective `k`-algebra homomorphism
of fields is the top intermediate field. -/
theorem IntermediateField.map_top_of_surjective
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] {f : K →ₐ[k] L} (hf : Function.Surjective f) :
    IntermediateField.map f ⊤ = ⊤ := by
  rwa [← AlgHom.fieldRange_eq_map, AlgHom.fieldRange_eq_top]

@[simp] theorem IntermediateField.map_AlgEquiv_top
    {F E K : Type*} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] (e : E ≃ₐ[F] K) :
    (⊤ : IntermediateField F E).map (AlgHomClass.toAlgHom e) = ⊤ :=
  IntermediateField.map_top_of_surjective e.surjective

theorem IntermediateField.fieldRange_comp
    {F E K L : Type*} [Field F] [Field E] [Field K] [Field L]
    [Algebra F E] [Algebra F K] [Algebra F L]
    (e : E →ₐ[F] K) (φ : K →ₐ[F] L) :
    (φ.comp e).fieldRange = e.fieldRange.map φ := by
  simp [AlgHom.fieldRange_eq_map, map_map]

theorem IntermediateField.restrictScalars_adjoin'
    {K M N : Type*} [Field K] [Field M] [Field N]
    [Algebra K M] [Algebra K N] [Algebra M N] [IsScalarTower K M N]
    (s : Set N) : (adjoin M s).restrictScalars K = adjoin K (Set.range (algebraMap M N) ∪ s) := by
  let M' : IntermediateField K N := (Algebra.algHom K M N).fieldRange
  let e : M ≃ₐ[K] M' := (botEquiv M N).symm.restrictScalars K
  rw [restrictScalars_adjoin_of_algEquiv e rfl, restrictScalars_adjoin]
  rfl
