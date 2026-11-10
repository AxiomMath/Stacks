module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.ExteriorPower
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Formula

/-!
# A two-periodic complex defined by invertible blocks

Let `k` be a field, and let `U` and `V` be invertible square matrices of size `a`. On the
direct sum of two copies of `k^a`, form the endomorphisms with upper-right blocks `U` and `V`
and all other blocks zero. Their periodic determinant is `(-1)^a det(U) / det(V)`.

## Main definitions

* `AlgebraicGeometry.upperBlockEndomorphism` is the block endomorphism with one nonzero block.

## Main results

* `AlgebraicGeometry.periodicDeterminant_upperBlockEndomorphism` computes the periodic
  determinant of the two block endomorphisms.

## Implementation notes

The exactness and finite-length witnesses required by the definition of the periodic
determinant are constructed in the result, rather than imposed as extra hypotheses. The formula
is stated in the residue field, using the canonical residue map from `k`; for a field this map
is an isomorphism.

## References

* [Stacks Project, Tag 02PS](https://stacks.math.columbia.edu/tag/02PS)
-/

@[expose] public section

noncomputable section

open Module.FiniteLength

namespace AlgebraicGeometry

universe u

/-- The endomorphism of `k^a ⊕ k^a` with matrix `[0 U; 0 0]`. -/
abbrev upperBlockEndomorphism {k : Type u} [Field k] {a : ℕ}
    (U : Matrix (Fin a) (Fin a) k) :
    ((Fin a → k) × (Fin a → k)) →ₗ[k] ((Fin a → k) × (Fin a → k)) :=
  (LinearMap.inl k (Fin a → k) (Fin a → k)).comp
    (U.mulVecLin.comp (LinearMap.snd k (Fin a → k) (Fin a → k)))

/-- Two invertible upper-right blocks give an exact sequence. -/
private theorem upperBlockEndomorphism_exact
    {k : Type u} [Field k] {a : ℕ}
    (U V : Matrix (Fin a) (Fin a) k) (hU : IsUnit U) (hV : IsUnit V) :
    Function.Exact (upperBlockEndomorphism U) (upperBlockEndomorphism V) := by
  rw [LinearMap.exact_iff]
  ext z
  constructor
  · intro hz
    simp only [LinearMap.mem_ker] at hz
    have hz2 : z.2 = 0 := by
      apply Matrix.mulVec_injective_iff_isUnit.mpr hV
      simpa [upperBlockEndomorphism] using hz
    obtain ⟨w, hw⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hU) z.1
    refine ⟨(0, w), ?_⟩
    apply Prod.ext <;> simp [upperBlockEndomorphism, hw, hz2]
  · rintro ⟨w, rfl⟩
    simp [LinearMap.mem_ker, upperBlockEndomorphism]

/-- A finite-dimensional vector space over a field has finite length. -/
private theorem upperBlockEndomorphism_isFiniteLength
    {k : Type u} [Field k] (a : ℕ) :
    IsFiniteLength k ((Fin a → k) × (Fin a → k)) := by
  apply Module.length_ne_top_iff.mp
  rw [Module.length_eq_finrank]
  simp

/-- The image of an invertible upper-right block endomorphism is the first summand. -/
private noncomputable def upperBlockRangeEquiv
    {k : Type u} [Field k] {a : ℕ}
    (U : Matrix (Fin a) (Fin a) k) (hU : IsUnit U) :
    (Fin a → k) ≃ₗ[k] LinearMap.range (upperBlockEndomorphism U) := by
  let f : (Fin a → k) →ₗ[k] LinearMap.range (upperBlockEndomorphism U) := {
    toFun := fun x => ⟨(x, 0), by
      obtain ⟨y, hy⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hU) x
      refine ⟨(0, y), ?_⟩
      apply Prod.ext <;> simp [upperBlockEndomorphism, hy]⟩
    map_add' x y := by
      apply Subtype.ext
      ext <;> simp
    map_smul' r x := by
      apply Subtype.ext
      ext <;> simp }
  refine LinearEquiv.ofBijective f
    ⟨fun x y h => congrArg Prod.fst (congrArg Subtype.val h), fun z => ⟨z.1.1, ?_⟩⟩
  apply Subtype.ext
  rcases z.2 with ⟨w, hw⟩
  apply Prod.ext
  · rfl
  · simpa [f, upperBlockEndomorphism] using congrArg Prod.snd hw

/-- The image of an invertible upper-right block has length the size of the block. -/
private theorem moduleLength_upperBlockRange
    {k : Type u} [Field k] {a : ℕ}
    (U : Matrix (Fin a) (Fin a) k) (hU : IsUnit U) :
    moduleLength k (LinearMap.range (upperBlockEndomorphism U)) = a := by
  unfold moduleLength
  rw [Module.length_eq_finrank, ← (upperBlockRangeEquiv U hU).finrank_eq]
  simp

/-- For a field, the residue map onto its residue field is a ring isomorphism. -/
private noncomputable def residueRingEquiv
    {k : Type u} [Field k] : k ≃+* IsLocalRing.ResidueField k :=
  RingEquiv.ofBijective (IsLocalRing.residue k)
    ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩

/-- For a field, the structure map from its residue field is the inverse of the residue map. -/
private theorem algebraMap_residueField_eq_symm
    {k : Type u} [Field k] :
    algebraMap (IsLocalRing.ResidueField k) k = (residueRingEquiv (k := k)).symm.toRingHom := by
  ext c
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
  calc
    algebraMap (IsLocalRing.ResidueField k) k (IsLocalRing.residue k r) = r := by
      simpa [IsLocalRing.ResidueField.algebraMap_eq] using (congrArg (fun f : k →+* k => f r)
        (IsScalarTower.algebraMap_eq k (IsLocalRing.ResidueField k) k)).symm
    _ = (residueRingEquiv (k := k)).symm (IsLocalRing.residue k r) :=
      ((residueRingEquiv (k := k)).symm_apply_apply r).symm

/-- Applying the residue map coordinatewise identifies `k^a` with `κ^a` as residue-field vector
spaces. -/
private noncomputable def piResidueLinearEquiv
    {k : Type u} [Field k] (a : ℕ) :
    (Fin a → k) ≃ₗ[IsLocalRing.ResidueField k] (Fin a → IsLocalRing.ResidueField k) := by
  classical
  let K := IsLocalRing.ResidueField k
  let f : (Fin a → k) →ₗ[K] (Fin a → K) := {
    toFun := fun x i => IsLocalRing.residue k (x i)
    map_add' x y := by
      ext i
      simp
    map_smul' c x := by
      ext i
      change IsLocalRing.residue k (algebraMap K k c * x i) = c * IsLocalRing.residue k (x i)
      rw [map_mul, algebraMap_residueField_eq_symm]
      exact congrArg (fun z : K => z * IsLocalRing.residue k (x i))
        ((residueRingEquiv (k := k)).apply_symm_apply c)
  }
  refine LinearEquiv.ofBijective f
    ⟨fun x y h => funext fun i => (residueRingEquiv (k := k)).injective (congrFun h i),
      fun y => ⟨fun i => algebraMap K k (y i), ?_⟩⟩
  funext i
  change IsLocalRing.residue k (algebraMap K k (y i)) = y i
  rw [algebraMap_residueField_eq_symm]
  exact (residueRingEquiv (k := k)).apply_symm_apply (y i)

/-- Transporting an index along an equality of lengths agrees with `Fin.cast`. -/
private theorem cast_fin_equiv {m n : ℕ} (h : m = n) (i : Fin m) :
    cast (congrArg Fin h) i = Fin.cast h i := by
  cases h
  rfl

/-- A basis reindexed along an equality of lengths still spans. -/
private theorem span_basis_cast {k : Type u} [Field k] {M : Type*}
    [AddCommGroup M] [Module k M] {m n : ℕ}
    (b : Module.Basis (Fin n) k M) (h : m = n) :
    Submodule.span k (Set.range (fun i : Fin m => b (Fin.cast h i))) = ⊤ := by
  subst h
  simp

/-- **Stacks Project, Tag 02PS.** The periodic determinant of two invertible upper-right
blocks is the signed ratio of their ordinary matrix determinants. -/
@[stacks 02PS]
theorem periodicDeterminant_upperBlockEndomorphism
    {k : Type u} [Field k] (a : ℕ)
    (U V : Matrix (Fin a) (Fin a) k) (hU : IsUnit U) (hV : IsUnit V) :
    ∃ (hUV : Function.Exact (upperBlockEndomorphism U) (upperBlockEndomorphism V))
      (hVU : Function.Exact (upperBlockEndomorphism V) (upperBlockEndomorphism U))
      (hM : IsFiniteLength k ((Fin a → k) × (Fin a → k))),
      (periodicDeterminant (upperBlockEndomorphism U) (upperBlockEndomorphism V)
        hUV hVU hM : IsLocalRing.ResidueField k) =
        (-1 : IsLocalRing.ResidueField k) ^ a *
          IsLocalRing.residue k U.det / IsLocalRing.residue k V.det := by
  classical
  let φ := upperBlockEndomorphism U
  let ψ := upperBlockEndomorphism V
  have hUV := upperBlockEndomorphism_exact U V hU hV
  have hVU := upperBlockEndomorphism_exact V U hV hU
  have hM := upperBlockEndomorphism_isFiniteLength (k := k) a
  refine ⟨hUV, hVU, hM, ?_⟩
  let K := IsLocalRing.ResidueField k
  let M := (Fin a → k) × (Fin a → k)
  let : Module.Finite K M := Module.Finite.of_restrictScalars_finite k K M
  let cM := determinantExteriorPowerComparison k M
  let rangeU := LinearMap.range φ
  let rangeV := LinearMap.range ψ
  have hlenU := moduleLength_upperBlockRange U hU
  have hlenV := moduleLength_upperBlockRange V hV
  have hlenRangeU : moduleLength k rangeU = a := by
    simpa [rangeU, φ] using hlenU
  have hlenRangeV : moduleLength k rangeV = a := by
    simpa [rangeV, ψ] using hlenV
  let Ulin : (Fin a → k) ≃ₗ[k] (Fin a → k) :=
    LinearEquiv.ofBijective U.mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hU,
        Matrix.mulVec_surjective_iff_isUnit.mpr hU⟩
  let Vlin : (Fin a → k) ≃ₗ[k] (Fin a → k) :=
    LinearEquiv.ofBijective V.mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hV,
        Matrix.mulVec_surjective_iff_isUnit.mpr hV⟩
  let bU : Module.Basis (Fin a) k rangeU :=
    (Pi.basisFun k (Fin a)).map (Ulin.trans (upperBlockRangeEquiv U hU))
  let bV : Module.Basis (Fin a) k rangeV :=
    (Pi.basisFun k (Fin a)).map (Vlin.trans (upperBlockRangeEquiv V hV))
  let x : AdmissibleSequence k rangeU :=
    ⟨fun i => bU (Fin.cast hlenU i), all_admissible k _ _⟩
  let y : AdmissibleSequence k rangeV :=
    ⟨fun i => bV (Fin.cast hlenV i), all_admissible k _ _⟩
  have hspanU : Submodule.span k (Set.range x.1) = ⊤ := span_basis_cast bU hlenU
  have hspanV : Submodule.span k (Set.range y.1) = ⊤ := span_basis_cast bV hlenV
  have hx := span_symbol_eq_top (hM.of_injective rangeU.subtype_injective) x hspanU
  have hy := span_symbol_eq_top (hM.of_injective rangeV.subtype_injective) y hspanV
  let xLift : Fin (moduleLength k rangeU) → ((Fin a → k) × (Fin a → k)) :=
    fun i => (0, (Pi.basisFun k (Fin a)) (Fin.cast hlenU i))
  let yLift : Fin (moduleLength k rangeV) → ((Fin a → k) × (Fin a → k)) :=
    fun i => (0, (Pi.basisFun k (Fin a)) (Fin.cast hlenV i))
  have hxLift : ∀ i, φ (xLift i) = (x.1 i : ((Fin a → k) × (Fin a → k))) := fun _ => rfl
  have hyLift : ∀ i, ψ (yLift i) = (y.1 i : ((Fin a → k) × (Fin a → k))) := fun _ => rfl
  obtain ⟨hleftLength, hrightLength, hleft, hright, hsymbol⟩ :=
    periodicDeterminant_symbol_eq φ ψ hUV hVU hM x y hx hy xLift yLift hxLift hyLift
  let eLeft : AdmissibleSequence k M :=
    ⟨fun i => Fin.append (fun j => (x.1 j : M)) yLift (Fin.cast hleftLength i), hleft⟩
  let eRight : AdmissibleSequence k M :=
    ⟨fun i => Fin.append (fun j => (y.1 j : M)) xLift (Fin.cast hrightLength i), hright⟩
  have hsymbol' : symbol eLeft =
      (((-1 : K) ^ (moduleLength k rangeU * moduleLength k rangeV)) *
        (periodicDeterminant φ ψ hUV hVU hM : K)) • symbol eRight := by
    simpa [eLeft, eRight, rangeU, rangeV] using hsymbol
  let π := piResidueLinearEquiv (k := k) a
  let bA : Module.Basis (Fin a) K (Fin a → k) := (Pi.basisFun K (Fin a)).map π.symm
  have hfin : Module.finrank K M = a + a := by
    rw [Module.finrank_prod, Module.finrank_eq_card_basis bA]
    simp only [Fintype.card_fin]
  let e : (Fin a ⊕ Fin a) ≃ Fin (Module.finrank K M) :=
    finSumFinEquiv.trans (Equiv.cast (congrArg Fin hfin.symm))
  let bM : Module.Basis (Fin a ⊕ Fin a) K M := bA.prod bA
  let b : Module.Basis (Fin (Module.finrank K M)) K M := bM.reindex e
  let idEmb : Fin (Module.finrank K M) ↪o Fin (Module.finrank K M) :=
    OrderEmbedding.id _
  let s : Set.powersetCard (Fin (Module.finrank K M))
      (Module.finrank K M) := Set.powersetCard.ofFinEmbEquiv idEmb
  let evalDual := exteriorPower.ιMultiDual K (Module.finrank K M) b s
  let leftFamily : Fin (Module.finrank K M) → M := fun i =>
    eLeft.1 (Fin.cast cM.length_eq_finrank.symm i)
  let rightFamily : Fin (Module.finrank K M) → M := fun i =>
    eRight.1 (Fin.cast cM.length_eq_finrank.symm i)
  have hsymbolExt'' :
      evalDual (exteriorPower.ιMulti K (Module.finrank K M) leftFamily) =
        (((-1 : K) ^ (moduleLength k rangeU * moduleLength k rangeV)) *
          (periodicDeterminant φ ψ hUV hVU hM : K)) *
          evalDual (exteriorPower.ιMulti K (Module.finrank K M) rightFamily) := by
    simpa only [cM.equiv_symbol, leftFamily, rightFamily, eLeft, eRight,
      map_smul, smul_eq_mul] using congrArg evalDual (congrArg cM.equiv hsymbol')
  have e_inl (i : Fin a) : e (Sum.inl i) = Fin.cast hfin.symm (Fin.castAdd a i) := by
    dsimp [e]
    exact cast_fin_equiv hfin.symm (Fin.castAdd a i)
  have e_inr (i : Fin a) : e (Sum.inr i) = Fin.cast hfin.symm (Fin.natAdd a i) := by
    dsimp [e]
    exact cast_fin_equiv hfin.symm (Fin.natAdd a i)
  have hleftIndex (i : Fin a) :
      Fin.cast hleftLength (Fin.cast cM.length_eq_finrank.symm (e (Sum.inl i))) =
        Fin.castAdd (moduleLength k rangeV) (Fin.cast hlenU.symm i) := by
    apply Fin.ext
    rw [e_inl]
    simp [Fin.val_cast, Fin.val_castAdd]
  have hleftBottomIndex (i : Fin a) :
      Fin.cast hleftLength (Fin.cast cM.length_eq_finrank.symm (e (Sum.inr i))) =
        Fin.natAdd (moduleLength k rangeU) (Fin.cast hlenV.symm i) := by
    apply Fin.ext
    rw [e_inr]
    simp only [Fin.natAdd_eq_addNat, Fin.cast_cast, Fin.val_cast, Fin.val_addNat, Fin.val_natAdd,
      hlenRangeU]
    omega
  have hrightTopIndex (i : Fin a) :
      Fin.cast hrightLength (Fin.cast cM.length_eq_finrank.symm (e (Sum.inl i))) =
        Fin.castAdd (moduleLength k rangeU) (Fin.cast hlenV.symm i) := by
    apply Fin.ext
    rw [e_inl]
    simp [Fin.val_cast, Fin.val_castAdd]
  have hrightBottomIndex (i : Fin a) :
      Fin.cast hrightLength (Fin.cast cM.length_eq_finrank.symm (e (Sum.inr i))) =
        Fin.natAdd (moduleLength k rangeV) (Fin.cast hlenU.symm i) := by
    apply Fin.ext
    rw [e_inr]
    simp only [Fin.natAdd_eq_addNat, Fin.cast_cast, Fin.val_cast, Fin.val_addNat, Fin.val_natAdd,
      hlenRangeV]
    omega
  have hrange (W : Matrix (Fin a) (Fin a) k) (hW : IsUnit W) (i : Fin a) :
      ((upperBlockRangeEquiv W hW) (W.mulVecLin ((Pi.basisFun k (Fin a)) i)) : M) =
        (W.col i, 0) := by
    apply Prod.ext
    · change W.mulVec ((Pi.basisFun k (Fin a)) i) = W.col i
      simp [Pi.basisFun]
    · rfl
  have hleftTop (i : Fin a) : leftFamily (e (Sum.inl i)) = (U.col i, 0) := by
    change Fin.append (fun j => (x.1 j : M)) yLift _ = _
    rw [hleftIndex, Fin.append_left]
    simp only [x, bU, Module.Basis.map_apply, LinearEquiv.trans_apply]
    exact hrange U hU i
  have hleftBottom (i : Fin a) :
      leftFamily (e (Sum.inr i)) = (0, (Pi.basisFun k (Fin a)) i) := by
    change Fin.append (fun j => (x.1 j : M)) yLift _ = _
    rw [hleftBottomIndex, Fin.append_right]
    simp [yLift]
  have hrightTop (i : Fin a) : rightFamily (e (Sum.inl i)) = (V.col i, 0) := by
    change Fin.append (fun j => (y.1 j : M)) xLift _ = _
    rw [hrightTopIndex, Fin.append_left]
    simp only [y, bV, Module.Basis.map_apply, LinearEquiv.trans_apply]
    exact hrange V hV i
  have hrightBottom (i : Fin a) :
      rightFamily (e (Sum.inr i)) = (0, (Pi.basisFun k (Fin a)) i) := by
    change Fin.append (fun j => (y.1 j : M)) xLift _ = _
    rw [hrightBottomIndex, Fin.append_right]
    simp [xLift]
  have hbM_fst (z : M) (i : Fin a) :
      b.coord (e (Sum.inl i)) z = IsLocalRing.residue k (z.1 i) := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_reindex_apply,
      Equiv.symm_apply_apply, Module.Basis.prod_repr_inl]
    rfl
  have hbM_snd (z : M) (i : Fin a) :
      b.coord (e (Sum.inr i)) z = IsLocalRing.residue k (z.2 i) := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_reindex_apply,
      Equiv.symm_apply_apply, Module.Basis.prod_repr_inr]
    rfl
  have hslot : Set.powersetCard.ofFinEmbEquiv.symm s = idEmb := by
    simp [s, idEmb]
  have hcoordId (j) : (Set.powersetCard.ofFinEmbEquiv.symm s) j = j := by
    simp [hslot, idEmb]
  have hEval (W : Matrix (Fin a) (Fin a) k) (F : Fin (Module.finrank K M) → M)
      (hTop : ∀ i, F (e (Sum.inl i)) = (W.col i, 0))
      (hBot : ∀ i, F (e (Sum.inr i)) = (0, (Pi.basisFun k (Fin a)) i)) :
      evalDual (exteriorPower.ιMulti K (Module.finrank K M) F) = IsLocalRing.residue k W.det := by
    let C : Matrix (Fin (Module.finrank K M)) (Fin (Module.finrank K M)) K :=
      Matrix.of fun i j => b.coord ((Set.powersetCard.ofFinEmbEquiv.symm s) j) (F i)
    have hC : C.reindex e.symm e.symm =
        Matrix.fromBlocks ((W.map (IsLocalRing.residue k)).transpose) 0 0 1 := by
      ext (i | i) (j | j) <;>
        simp only [C, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          Matrix.of_apply, hcoordId, hTop, hBot, hbM_fst, hbM_snd] <;>
        simp [Matrix.fromBlocks, Matrix.col_apply, Pi.basisFun, Pi.single_apply,
          Matrix.one_apply, eq_comm]
    have hdet : C.det = IsLocalRing.residue k W.det := by
      rw [← Matrix.det_reindex_self e.symm C, hC, Matrix.det_fromBlocks_zero₂₁,
        Matrix.det_transpose, Matrix.det_one, mul_one]
      simpa using (RingHom.map_det (IsLocalRing.residue k) W).symm
    simpa only [evalDual, exteriorPower.ιMultiDual_apply_ιMulti, C] using hdet
  have hEvalLeft := hEval U leftFamily hleftTop hleftBottom
  have hEvalRight := hEval V rightFamily hrightTop hrightBottom
  have hscalar : IsLocalRing.residue k U.det =
      (-1 : K) ^ (a * a) *
        (periodicDeterminant φ ψ hUV hVU hM : K) * IsLocalRing.residue k V.det := by
    rw [hlenU, hlenV, hEvalLeft, hEvalRight] at hsymbolExt''
    simpa [mul_assoc] using hsymbolExt''
  have hsign : (-1 : K) ^ (a * a) = (-1 : K) ^ a :=
    neg_one_pow_congr (by simp [Nat.even_mul])
  have hVne : IsLocalRing.residue k V.det ≠ 0 :=
    (IsUnit.map (IsLocalRing.residue k)
      ((Matrix.isUnit_iff_isUnit_det V).mp hV)).ne_zero
  rw [hscalar, ← hsign]
  field_simp [hVne]
  simp [← pow_mul]
  rfl

end AlgebraicGeometry
