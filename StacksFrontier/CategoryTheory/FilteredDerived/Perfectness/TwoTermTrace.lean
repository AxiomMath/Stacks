module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Minus
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Traces on complexes reindexed from chain complexes

A chain complex `K` in degrees `≥ 0` of modules over a ring `R` becomes a cochain complex in
degrees `≤ 0` by `n ↦ -n` (`ComplexShape.embeddingUpIntLE 0`). If the terms of `K` are finite
projective and vanish above degree `1`, the reindexed complex is a bounded complex of finite
projective modules, and the alternating trace of the map induced by a chain map `φ` is
`Tr(φ₀) - Tr(φ₁)`.

## Main results

* `CategoryTheory.FilteredDerived.finiteProjectiveComplex_extend`: the reindexed complex is a
  bounded complex of finite projective modules.
* `CategoryTheory.FilteredDerived.alternatingTrace_extendMap`: its alternating trace is
  `Tr(φ₀) - Tr(φ₁)`.
* `CategoryTheory.FilteredDerived.projectiveModuleTrace_mulRightEnd`: the trace of
  right multiplication by `b` on `R` is the class of `b`.

## References

* [Stacks Project, Tag 03TI](https://stacks.math.columbia.edu/tag/03TI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.FilteredDerived

variable {R : Type u} [Ring R]

/-- Right multiplication by `b`, a linear endomorphism of the left module `R`. -/
@[sga "5 IIIB 5.7"]
public def mulRightEnd (b : R) : Module.End R R where
  toFun x := x * b
  map_add' x y := add_mul x y b
  map_smul' a x := mul_assoc a x b

/-- `mulRightEnd b` sends `x` to `x * b`. -/
@[simp]
public theorem mulRightEnd_apply (b x : R) : mulRightEnd b x = x * b :=
  rfl

/-- **The trace of right multiplication by `b` on `R` is the class of `b`.** -/
@[sga "5 IIIB 5.7" "5.7.1, special case"]
public theorem projectiveModuleTrace_mulRightEnd (b : R) :
    Stacks.Trace.projectiveModuleTrace R R (mulRightEnd b) = additiveCommutatorQuotientMk R b := by
  classical
  let p : (Fin 1 → R) →ₗ[R] R := LinearMap.proj 0
  let i : R →ₗ[R] (Fin 1 → R) := LinearMap.pi fun _ => LinearMap.id
  rw [projectiveModuleTrace_eq_of_split R R _ p i (LinearMap.ext fun x => rfl),
    freeModuleTrace_apply, Fin.sum_univ_one]
  simp [p, i, standardBasisVector]

/-- **The trace of a linear endomorphism of `R` is the class of the image of `1`.** -/
public theorem projectiveModuleTrace_self (f : Module.End R R) :
    Stacks.Trace.projectiveModuleTrace R R f = additiveCommutatorQuotientMk R (f 1) := by
  have hf : f = mulRightEnd (f 1) := LinearMap.ext fun x => by
    rw [mulRightEnd_apply, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  rw [hf, projectiveModuleTrace_mulRightEnd, mulRightEnd_apply, one_mul]

variable (K : ChainComplex (ModuleCat.{u} R) ℕ)

/-- The reindexed complex vanishes in degree `i` unless `i = -n` for some `n`. -/
public theorem isZero_extend_X_of_pos {i : ℤ} (hi : 0 < i) :
    IsZero ((K.extend (ComplexShape.embeddingUpIntLE 0)).X i) :=
  K.isZero_extend_X _ i fun n hn => by
    simp [ComplexShape.embeddingUpIntLE] at hn
    lia

/-- The term of the reindexed complex in degree `-n`. -/
public def extendXIsoNeg (n : ℕ) :
    (K.extend (ComplexShape.embeddingUpIntLE 0)).X (-(n : ℤ)) ≅ K.X n :=
  K.extendXIso _ (by simp [ComplexShape.embeddingUpIntLE])

/-- Every integer is `-n` for a natural number `n`, or positive. -/
public theorem exists_eq_neg_or_pos (i : ℤ) : (∃ n : ℕ, i = -(n : ℤ)) ∨ 0 < i := by
  rcases le_or_gt i 0 with h | h
  · exact Or.inl ⟨(-i).toNat, by lia⟩
  · exact Or.inr h

variable {K}

/-- The finiteness and projectivity of a zero module. -/
public theorem finite_projective_of_isZero {P : ModuleCat.{u} R} (hP : IsZero P) :
    Module.Projective R P ∧ Module.Finite R P := by
  have := ModuleCat.subsingleton_of_isZero hP
  refine ⟨Module.Projective.of_split (M := R) 0 0 (LinearMap.ext fun x => Subsingleton.elim _ _),
    Module.Finite.of_finite⟩

/-- The reindexed complex vanishes in every degree other than `0` and `-1`. -/
private theorem isZero_extend_X_of_ne (hzero : ∀ n, 2 ≤ n → IsZero (K.X n)) {i : ℤ}
    (h0 : i ≠ 0) (h1 : i ≠ -1) : IsZero ((K.extend (ComplexShape.embeddingUpIntLE 0)).X i) := by
  rcases exists_eq_neg_or_pos i with ⟨n, rfl⟩ | h
  · exact (hzero n (by lia)).of_iso (extendXIsoNeg K n)
  · exact isZero_extend_X_of_pos K h

/-- **The reindexed complex is a bounded complex of finite projective modules**, for `K` with
finite projective terms vanishing above degree `1`. -/
public theorem finiteProjectiveComplex_extend
    (hfin : ∀ n, Module.Finite R (K.X n)) (hproj : ∀ n, Module.Projective R (K.X n))
    (hzero : ∀ n, 2 ≤ n → IsZero (K.X n)) :
    finiteProjectiveComplex R (K.extend (ComplexShape.embeddingUpIntLE 0)) := by
  refine ⟨⟨⟨-1, ?_⟩, ⟨0, inferInstance⟩⟩, fun i => ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact isZero_extend_X_of_ne hzero (by lia) (by lia)
  · rcases exists_eq_neg_or_pos i with ⟨n, rfl⟩ | h
    · let e := (extendXIsoNeg K n).toLinearEquiv.symm
      exact ⟨Module.Projective.of_equiv e, Module.Finite.equiv e⟩
    · exact finite_projective_of_isZero (isZero_extend_X_of_pos K h)

/-- **The alternating trace on the reindexed complex** of a complex concentrated in degrees `0`
and `1` is `Tr(φ₀) - Tr(φ₁)`. -/
public theorem alternatingTrace_extendMap
    (hfin : ∀ n, Module.Finite R (K.X n)) (hproj : ∀ n, Module.Projective R (K.X n))
    (hzero : ∀ n, 2 ≤ n → IsZero (K.X n)) (φ : K ⟶ K) :
    alternatingTrace R _ (finiteProjectiveComplex_extend hfin hproj hzero)
        (HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntLE 0)) =
      Stacks.Trace.projectiveModuleTrace R (K.X 0) (φ.f 0).hom -
        Stacks.Trace.projectiveModuleTrace R (K.X 1) (φ.f 1).hom := by
  classical
  have hsupp : ∀ i : ℤ, i ∉ ({0, -1} : Finset ℤ) →
      IsZero ((K.extend (ComplexShape.embeddingUpIntLE 0)).X i) := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact isZero_extend_X_of_ne hzero hi.1 hi.2
  have hP := finiteProjectiveComplex_extend hfin hproj hzero
  have := (hP.2 0).1
  have := (hP.2 0).2
  have := (hP.2 (-1)).1
  have := (hP.2 (-1)).2
  rw [alternatingTrace, finsum_eq_sum_of_support_subset (s := {0, -1})]
  · rw [Finset.sum_pair (by decide)]
    have h0 : (ComplexShape.embeddingUpIntLE 0).f 0 = 0 := by
      simp [ComplexShape.embeddingUpIntLE]
    have h1 : (ComplexShape.embeddingUpIntLE 0).f 1 = -1 := by
      simp [ComplexShape.embeddingUpIntLE]
    simp only [show Even (0 : ℤ) from ⟨0, rfl⟩, if_true, show ¬ Even (-1 : ℤ) by decide,
      if_false]
    rw [HomologicalComplex.extendMap_f φ _ h0, HomologicalComplex.extendMap_f φ _ h1,
      sub_eq_add_neg]
    congr 1
    · exact projectiveModuleTrace_conj R (K.extendXIso _ h0).toLinearEquiv.symm (φ.f 0).hom
    · congr 1
      exact projectiveModuleTrace_conj R (K.extendXIso _ h1).toLinearEquiv.symm (φ.f 1).hom
  · intro i hi
    by_contra hmem
    apply hi
    have := ModuleCat.subsingleton_of_isZero (hsupp i (by simpa using hmem))
    simp only
    split_ifs <;> simp [projectiveModuleTrace_eq_zero_of_subsingleton]

end CategoryTheory.FilteredDerived

end
