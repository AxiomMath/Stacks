module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import StacksCore.FieldTheory.AlgebraicClosure
import StacksCore.FieldTheory.IntermediateField.Adjoin.Defs
import StacksCore.FieldTheory.IntermediateField.Basic
public import StacksCore.FieldTheory.Normal.Closure

/-! # Normal field extensions -/

@[expose] public section

open IntermediateField

@[stacks 09HQ]
theorem normal_iff_forall_fieldRange_eq
    (F E L : Type*) [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [Algebra.IsAlgebraic F E] [IsAlgClosed L] :
    Normal F E ↔ ∀ σ₁ σ₂ : E →ₐ[F] L, σ₁.fieldRange = σ₂.fieldRange := by
  let φ : (E →ₐ[F] algebraicClosure F L) ≃ (E →ₐ[F] L) :=
    IntermediateField.algHomEquivAlgHomOfSplits _ _ fun _ ↦ IsAlgClosed.splits _
  let f : E →ₐ[F] algebraicClosure F L := IsAlgClosed.lift
  let f' : E ≃ₐ[F] f.fieldRange := .ofInjectiveField _
  let f'' := f.comp f'.symm.toAlgHom
  have h : f''.fieldRange = f.fieldRange := by
    simp [f'', fieldRange_comp, ← AlgHom.fieldRange_eq_map]
  simp_rw [f'.transfer_normal, IntermediateField.normal_iff_forall_fieldRange_eq,
    φ.surjective.forall, (f'.symm.arrowCongr .refl).surjective.forall, ← h]
  simp only [AlgEquiv.arrowCongr_apply, AlgEquiv.refl_toAlgHom, AlgHom.id_comp,
    AlgEquiv.symm_symm, algHomEquivAlgHomOfSplits_apply, fieldRange_comp,
    AlgEquiv.fieldRange_eq_top, ← AlgHom.fieldRange_eq_map, map_inj, φ]
  grind

@[stacks 09DT "the absolute normal closure", stacks 0BMF "absolute"]
noncomputable abbrev NormalClosure (F E : Type*) [Field F] [Field E] [Algebra F E] : Type _ :=
  normalClosure F (algebraicClosure F E) (AlgebraicClosure (algebraicClosure F E))

theorem isNormalClosure_algebraicClosure_iff
    (F E N : Type*) [Field F] [Field E] [Field N]
    [Algebra F E] [Algebra F N] :
    IsNormalClosure F (algebraicClosure F E) N ↔ IsNormalClosure F E N := by
  simp_rw [isNormalClosure_iff, ← minpoly.algHom_eq _ (algebraicClosure F E).val.injective]
  refine and_congr ⟨fun h x ↦ ?_, fun h x ↦ h x⟩ ?_
  · by_cases hx : IsIntegral F x
    · exact h ⟨x, hx⟩
    · simp [minpoly.eq_zero hx]
  · rw [iSup_split _ (IsIntegral F (A := E)), iSup_subtype,
      biSup_congr fun x (hx : ¬_) ↦ show _ = ⊥ by simp [minpoly.eq_zero hx]]
    simp [mem_algebraicClosure_iff']

instance (F E N : Type*) [Field F] [Field E] [Field N] [Algebra F E] [Algebra F N]
    [IsNormalClosure F E N] : IsNormalClosure F (algebraicClosure F E) N :=
  (isNormalClosure_algebraicClosure_iff ..).mpr ‹_›

@[stacks 09DT]
instance IsNormalClosure.normalClosure (F E : Type*) [Field F] [Field E] [Algebra F E] :
    IsNormalClosure F E (NormalClosure F E) :=
  have := Nonempty.intro (Algebra.algHom F (algebraicClosure F E)
    (AlgebraicClosure (algebraicClosure F E)))
  (isNormalClosure_algebraicClosure_iff ..).mp <| isNormalClosure_normalClosure ..

@[stacks 09DT "unique"]
noncomputable def IsNormalClosure.algEquiv (F E N : Type*) [Field F] [Field E] [Field N]
    [Algebra F E] [Algebra F N] [IsNormalClosure F E N] :
    N ≃ₐ[F] NormalClosure F E := equiv (K := E)

@[stacks 09DT]
noncomputable instance NormalClosure.algebra
    (F E : Type*) [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] :
    Algebra E (NormalClosure F E) :=
  let e : algebraicClosure F E ≃ₐ[F] E :=
    (equivOfEq (by rwa [algebraicClosure.eq_top_iff])).trans topEquiv
  let := e.symm.toRingHom.toAlgebra
  have : IsScalarTower F (algebraicClosure F E) (AlgebraicClosure (algebraicClosure F E)) :=
    .of_algebraMap_eq fun _ ↦ rfl
  Algebra.restrictScalars _ (algebraicClosure F E) _

instance (F E : Type*) [Field F] [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] :
    IsScalarTower F E (NormalClosure F E) := .of_algebraMap_eq fun _ ↦ rfl

/-- Let `L/E/F` with `L/F` normal. Then a normal closure of `E/F` embeds into `L`.

This is **Stacks 09DT** (smallest).
-/
@[stacks 09DT "smallest"]
noncomputable def IsNormalClosure.lift'
    (F E N L : Type*) [Field F] [Field E] [Field N] [Field L]
    [Algebra F E] [Algebra F N] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [IsNormalClosure F E N] [Normal F L] : N →ₐ[F] L :=
  open scoped Classical in
  if _ : Algebra.IsAlgebraic F E then
    (Algebra.algHom F E L).liftNormalClosure (of F E N)
  else
    (Algebra.algHom F (algebraicClosure F E) L).liftNormalClosure (of F (algebraicClosure F E) N)

@[simp] theorem IsNormalClosure.lift'_commutes
    (F E N L : Type*) [Field F] [Field E] [Field N] [Field L]
    [Algebra F E] [Algebra F N] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [IsNormalClosure F E N] [Normal F L] [Algebra.IsAlgebraic F E]
    (x : E) : lift' F E N L (of F E N x) = algebraMap E L x := by
  simp [lift', dite_eq_left ‹_›, Algebra.algHom]
