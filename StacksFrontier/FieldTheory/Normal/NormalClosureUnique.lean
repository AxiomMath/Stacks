module

public import StacksCore.FieldTheory.Normal.AlgClosed

/-!
# Uniqueness of the normal closure as an extension of `E`

Stacks Lemma 09DT: for a finite extension `E/F` of fields there is a unique smallest finite
extension `K/E` such that `K/F` is normal. Here "smallest" is read as in the source: no proper
subextension `K/M/E` has `M/F` normal, and "unique" means unique up to an isomorphism of
extensions of `E`.

## Main results

* `isNormalClosure_iff_forall_normal_eq_top`: for `K/E/F` with `E/F` algebraic and `K/F`
  normal, Stacks' minimality is equivalent to Mathlib's `IsNormalClosure F E K`.
* `IsNormalClosure.algEquivOfIsScalarTower`: two normal closures of `E/F` which are extensions
  of `E` are isomorphic as `E`-algebras.
* `algEquivOfForallNormalEqTop`: two smallest normal extensions `K/E`, `K'/E` are
  `E`-isomorphic (the uniqueness clause of 09DT).
* `exists_finiteDimensional_normal_forall_normal_eq_top`: the existence clause of 09DT.
-/

@[expose] public section

open IntermediateField

universe u v

section

variable (F E K : Type*) [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]
  [Algebra E K] [IsScalarTower F E K]

/-- If `K/E/F` is a tower with `E/F` algebraic and `K/F` normal, such that no subextension
`K/M/E` other than `K` itself is normal over `F`, then `K` is a normal closure of `E/F`. -/
theorem isNormalClosure_of_forall_normal_eq_top [Algebra.IsAlgebraic F E] [Normal F K]
    (h : ∀ M : IntermediateField E K, Normal F M → M = ⊤) : IsNormalClosure F E K := by
  rw [Algebra.IsAlgebraic.isNormalClosure_iff]
  refine ⟨fun x ↦ ?_, ?_⟩
  · rw [← minpoly.algebraMap_eq (algebraMap E K).injective x]
    exact Normal.splits' _
  · have hM : (normalClosure' F E E K).restrictScalars F = normalClosure F E K := rfl
    have : Normal F (normalClosure' F E E K) := by
      rw [← restrictScalars_normal (F := F), hM]
      infer_instance
    rw [← hM, h _ this, restrictScalars_top]

/-- A normal closure `K` of `E/F` which is an extension of `E` has no proper subextension `K/M/E`
with `M/F` normal. -/
theorem IsNormalClosure.eq_top_of_normal [Algebra.IsAlgebraic F E] [IsNormalClosure F E K]
    (M : IntermediateField E K) [Normal F M] : M = ⊤ := by
  have : Normal F K := IsNormalClosure.normal (K := E)
  have hle : IntermediateField.normalClosure F E K ≤ M.restrictScalars F :=
    normalClosure_le_iff.mpr fun f ↦ by
      rintro _ ⟨x, rfl⟩
      have hmap := (normal_iff_forall_map_le (K := M.restrictScalars F)).mp
        (restrictScalars_normal.mpr ‹_›) (f.liftNormal K)
      have hx : algebraMap E K x ∈ M.restrictScalars F := M.algebraMap_mem x
      have := hmap ⟨_, hx, rfl⟩
      rwa [AlgHom.coe_toRingHom, f.liftNormal_commutes K x, Algebra.algebraMap_self,
        RingHom.id_apply] at this
  rw [IsNormalClosure.normalClosure_eq_top, top_le_iff] at hle
  exact restrictScalars_injective F (hle.trans restrictScalars_top.symm)

/-- A normal closure `K` of a finite extension `E/F` which is an extension of `E` is finite over
`E`. -/
theorem IsNormalClosure.finiteDimensional_of_isScalarTower [FiniteDimensional F E]
    [IsNormalClosure F E K] : FiniteDimensional E K :=
  have := IsNormalClosure.finiteDimensional F E K
  Module.Finite.of_restrictScalars_finite F E K

/-- **Stacks 09DT** (Stacks' minimality is `IsNormalClosure`). For a tower `K/E/F` with `E/F`
algebraic and `K/F` normal, `K` is a normal closure of `E/F` if and only if no subextension
`K/M/E` other than `K` itself is normal over `F`. -/
@[stacks 09DT "smallest: Stacks' minimality is IsNormalClosure"]
theorem isNormalClosure_iff_forall_normal_eq_top [Algebra.IsAlgebraic F E] [Normal F K] :
    IsNormalClosure F E K ↔ ∀ M : IntermediateField E K, Normal F M → M = ⊤ :=
  ⟨fun _ M _ ↦ IsNormalClosure.eq_top_of_normal F E K M,
    isNormalClosure_of_forall_normal_eq_top F E K⟩

end

variable (F E K K' : Type*) [Field F] [Field E] [Field K] [Field K'] [Algebra F E]
  [Algebra F K] [Algebra F K'] [Algebra E K] [Algebra E K'] [IsScalarTower F E K]
  [IsScalarTower F E K']

/-- **Stacks 09DT** (unique, as extensions of `E`). Two normal closures `K`, `K'` of `E/F`
which are extensions of `E` are isomorphic as `E`-algebras. The map is the lift of
`E → K'` along `E → K` given by `AlgHom.liftNormalClosure`; it is bijective because each of
`K`, `K'` embeds into the other over `F` and `K/F` is algebraic. -/
@[stacks 09DT "unique, as an isomorphism of extensions of E"]
noncomputable def IsNormalClosure.algEquivOfIsScalarTower [IsNormalClosure F E K]
    [IsNormalClosure F E K'] : K ≃ₐ[E] K' :=
  have : Normal F K := IsNormalClosure.normal (K := E)
  have : Normal F K' := IsNormalClosure.normal (K := E)
  let g : K →ₐ[F] K' :=
    (IsScalarTower.toAlgHom F E K').liftNormalClosure (IsScalarTower.toAlgHom F E K)
  AlgEquiv.ofBijective
    { g.toRingHom with commutes' := fun x ↦ AlgHom.liftNormalClosure_commutes' _ _ x }
    (Normal.toIsAlgebraic.algHom_bijective₂ g
      (IsNormalClosure.equiv (K := E) (L := K') (L' := K)).toAlgHom).1

/-- **Stacks 09DT** (uniqueness). Let `E/F` be finite. If `K/E` and `K'/E` are extensions with
`K/F` and `K'/F` normal, each having no proper subextension normal over `F`, then `K` and `K'`
are isomorphic as extensions of `E`. -/
@[stacks 09DT "unique: two smallest normal extensions of E are E-isomorphic"]
noncomputable def algEquivOfForallNormalEqTop [FiniteDimensional F E] [Normal F K] [Normal F K']
    (h : ∀ M : IntermediateField E K, Normal F M → M = ⊤)
    (h' : ∀ M : IntermediateField E K', Normal F M → M = ⊤) : K ≃ₐ[E] K' :=
  have := isNormalClosure_of_forall_normal_eq_top F E K h
  have := isNormalClosure_of_forall_normal_eq_top F E K' h'
  IsNormalClosure.algEquivOfIsScalarTower F E K K'

/-- **Stacks 09DT** (existence). For a finite extension `E/F` there is a finite extension `K/E`
with `K/F` normal and no proper subextension `K/M/E` normal over `F`; `NormalClosure F E` is
one. -/
@[stacks 09DT "existence of a smallest finite K/E with K/F normal"]
theorem exists_finiteDimensional_normal_forall_normal_eq_top {F : Type u} {E : Type v} [Field F]
    [Field E] [Algebra F E] [FiniteDimensional F E] :
    ∃ (K : Type v) (_ : Field K) (_ : Algebra F K) (_ : Algebra E K) (_ : IsScalarTower F E K),
      FiniteDimensional E K ∧ Normal F K ∧ ∀ M : IntermediateField E K, Normal F M → M = ⊤ := by
  have : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  refine ⟨NormalClosure F E, inferInstance, inferInstance, inferInstance, inferInstance,
    IsNormalClosure.finiteDimensional_of_isScalarTower F E _, IsNormalClosure.normal (K := E),
    fun M _ ↦ IsNormalClosure.eq_top_of_normal F E _ M⟩
