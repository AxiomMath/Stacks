module

public import StacksCore.FieldTheory.MvRatFunc.Algebra
import StacksCore.RingTheory.Finiteness.Basic
import StacksCore.Tactic.StacksAttribute

/-! # Relative algebraic closure -/

@[expose] public section

add_to_stacks 037I "(1)" algebraicClosure
add_to_stacks 037I "(1), correctness" mem_algebraicClosure_iff

instance (F E : Type*) [Field F] [Field E] [Algebra F E] [IsAlgClosed E] :
    IsAlgClosed (algebraicClosure F E) :=
  (algebraicClosure.isAlgClosure F E).isAlgClosed

/-- **Stacks 037I** (part 2).
A field extension `E/F` is *algebraically closed in `E`* if every element of `E` that is
algebraic over `F` already lies in `F`, i.e. the relative algebraic closure of `F` in `E`
is trivial. -/
@[stacks 037I "2"]
def IsAlgClosedIn (F E : Type*) [Field F] [Field E] [Algebra F E] : Prop := algebraicClosure F E = ⊥

attribute [local instance] MvRatFunc.algebra
open IntermediateField

/-- **Stacks 037J**.
If `K/k` is an essentially finite type field extension, then the relative algebraic
closure of `k` in `K` is finite over `k`. -/
@[stacks 037J]
instance finiteDimensional_algebraicClosure_of_essFiniteType
    (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K] :
    FiniteDimensional k (algebraicClosure k K) := by
  classical
  -- Obtain a transcendence basis `s` of `K/k̅`
  -- (here `k̅` is relative algebraic closure of `k` in `K`):
  obtain ⟨s, hkbs⟩ := exists_isTranscendenceBasis (algebraicClosure k K) K
  -- Then transfer it to `K/k`:
  have hks := (Algebra.IsAlgebraic.isTranscendenceBasis_iff k _).mpr hkbs
  let ks := adjoin k s
  let kbs := adjoin (algebraicClosure k K) s
  let a : Algebra ks kbs :=
    (inclusion (F := kbs.restrictScalars k) (by simp [ks, kbs])).toAlgebra
  let : Module ks kbs := a.toModule
  have : IsScalarTower k ks kbs := .of_algebraMap_eq fun x ↦ rfl
  have : IsScalarTower ks kbs K := .of_algebraMap_eq fun x ↦ rfl
  -- Transfer to `kbs / ks` (i.e. `k-bar(x_s) / k(x_s)`):
  rw [FiniteDimensional, ← MvRatFunc.finite_iff _ _ s]
  suffices FiniteDimensional ks kbs from
    let e₁ : MvRatFunc s k ≃ₐ[k] ks :=
      (hkbs.1.restrictScalars (R := k) (RingHom.injective _)).aevalEquivField.trans <|
        equivOfEq <| by simp [ks]
    let e₂ : MvRatFunc s (algebraicClosure k K) ≃ₐ[k] kbs :=
      (hkbs.1.aevalEquivField.trans <| equivOfEq <| by simp [kbs]).restrictScalars k
    have he₂ (i : s) : e₂ (algebraMap (MvPolynomial s (algebraicClosure k K)) _ (.X i)) =
        ⟨i, subset_adjoin _ _ i.2⟩ := by simp [e₂]
    have h : (Algebra.algHom k ks kbs).comp e₁ =
        e₂.toAlgHom.comp (Algebra.algHom k (MvRatFunc s k) (MvRatFunc s (algebraicClosure k K))) :=
      MvRatFunc.ext_algHom fun i ↦ by
        simp only [Algebra.algHom, AlgHom.coe_comp, IsScalarTower.coe_toAlgHom',
          AlgEquiv.coe_toAlgHom, AlgEquiv.coe_trans, Function.comp_apply, equivOfEq_apply,
          AlgebraicIndependent.aevalEquivField_apply_coe, AlgHom.toRingHom_eq_coe,
          IsFractionRing.lift_algebraMap, RingHom.coe_coe, MvPolynomial.aeval_X,
          MvRatFunc.algebraMap_algebraMap_mvPolynomial, MvPolynomial.algebraMap_def,
          MvPolynomial.map_X, he₂, e₁]
        rfl
    (Module.finite_iff_of_equiv_equiv e₁.toRingEquiv e₂.toRingEquiv <|
      congrArg AlgHom.toRingHom h).mpr this
  -- Transfer to `K / ks`:
  suffices FiniteDimensional ks K from Module.Finite.left ks kbs K
  have : Algebra.EssFiniteType ks K := .of_comp k ks K
  have : Algebra.IsAlgebraic ks K := by convert hks.isAlgebraic_field <;> simp
  -- Then use finitely generated + algebraic to conclude that `K / ks` is finite
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic
