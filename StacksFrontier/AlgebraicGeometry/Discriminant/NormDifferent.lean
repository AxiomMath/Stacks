module

public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Norm.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.DifferentIdeal
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.FlatCase
public import StacksFrontier.RingTheory.Norm.Projective

/-!
# The norm of the different lies in the discriminant

Let `A → B` be a finite free algebra whose Dedekind different is defined. Choosing an `A`-basis
`b₁, …, bₙ` of `B`, an element `b` of the Dedekind different multiplies every dual basis vector
`bᵢ^∨` into the `B`-line spanned by the trace functional, say `b · bᵢ^∨ = cᵢ · Tr`. Expanding
`cᵢ` in the basis exhibits the matrix of multiplication by `b` as a product `(a_{il})` times the
trace matrix, so the norm of `b` is a multiple of the discriminant. Localizing at a maximal ideal
of `A` makes a finite projective `B` free, which removes the freeness hypothesis.

## Main results

* `Stacks.Discriminant.smul_dual_mem_range_of_mem_dedekindDifferentIdeal`: an element of the
  Dedekind different carries the whole linear dual into the image of the trace pairing.
* `Stacks.Discriminant.exists_leftMulMatrix_eq_mul_traceMatrix`: the matrix of multiplication by
  such an element factors through the trace matrix.
* `Stacks.Discriminant.exists_norm_eq_det_mul_discr`: consequently its norm is a determinant
  times the discriminant of the basis.
* `Stacks.Discriminant.discr_mem_algebraDiscriminantIdeal`: the discriminant of a basis belongs
  to the discriminant ideal.
* `Stacks.Discriminant.norm_mem_algebraDiscriminantIdeal`: the norm of an element of the Dedekind
  different of a finite free algebra belongs to the discriminant ideal.
* `Stacks.Discriminant.finiteProjective_mem_algebraDiscriminantIdeal`: the same for a finite
  projective algebra, with the projective norm in place of `Algebra.norm`.

## Implementation notes

The computation is run twice over: once for an abstract element `b` satisfying the linear-algebra
hypothesis that `b` carries the whole dual into the image of the trace pairing, and once for the
Dedekind different itself, which satisfies that hypothesis by Tag 0BW3. Keeping the two apart
isolates the only input from the theory of the different, and it is the abstract hypothesis, not
membership in the different, that is transported along the localization.

The discriminant ideal is defined as a Fitting ideal rather than by a determinant, so the
identification with `Algebra.discr` in the free case is part of the work:
`discr_mem_algebraDiscriminantIdeal` presents the cokernel of the trace pairing by the matrix of
the pairing in a basis and its dual basis, which is the transpose of `Algebra.traceMatrix`. Only
the inclusion is proved, since only it is used; the reverse inclusion is the principality
recorded in `algebraDiscriminantIdeal_isPrincipal_of_free`.

In the finite projective case the norm is `Algebra.projectiveNorm` and not `Algebra.norm`:
the latter is `LinearMap.det` of multiplication, which takes the junk value `1` on a module with
no finite basis, so the statement with `Algebra.norm` would be false for a projective algebra
that is not free. The two agree whenever `B` is free, by
`Algebra.projectiveNorm_eq_norm_of_free`. The projective case is deduced from the free one
by `Ideal.mem_of_localization_maximal`: over the localization of `A` at a maximal ideal the
algebra becomes free, the discriminant ideal base changes by
`algebraDiscriminantIdeal_map`, and the norm base changes by
`Algebra.projectiveNorm_baseChange`.

## References

* [Stacks Project, Tag 0BW8](https://stacks.math.columbia.edu/tag/0BW8)
* [Stacks Project, Tag 0BW3](https://stacks.math.columbia.edu/tag/0BW3)
-/

@[expose] public noncomputable section

open scoped Matrix TensorProduct

namespace Stacks.Discriminant

universe u v w

attribute [local instance] algebraDualModule

section General

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The trace pairing against `1` is the trace of multiplication. -/
theorem finiteProjectiveTraceForm_one_apply [Module.Finite A B] [Module.Projective A B] (x : B) :
    finiteProjectiveTraceForm A B 1 x = finiteProjectiveTrace A B (Algebra.lmul A B x) := by
  change finiteProjectiveTrace A B ((Algebra.lmul A B).toLinearMap ((1 : B) * x)) = _
  rw [one_mul]
  rfl

/-- Acting on the trace functional by a scalar gives the trace pairing against that scalar. -/
theorem smul_finiteProjectiveTraceForm_one [Module.Finite A B] [Module.Projective A B] (c : B) :
    (c • (finiteProjectiveTraceForm A B 1 : Module.Dual A B)) =
      finiteProjectiveTraceForm A B c := by
  ext y
  rw [algebraDualModule_smul_apply, finiteProjectiveTraceForm_one_apply (c * y)]
  rfl

/-- For a finite projective algebra the generic-fibre trace of an element of `B` is the image of
its trace pairing against `1`. -/
theorem trace_algebraMap_eq_algebraMap_traceForm_one
    (setup : DedekindDifferentSetup A B) [Module.Finite A B] [Module.Projective A B] (x : B) :
    setup.trace (algebraMap B (B ⊗[A] FractionRing A) x) =
      algebraMap A (FractionRing A) (finiteProjectiveTraceForm A B 1 x) := by
  classical
  let K := FractionRing A
  let L := B ⊗[A] K
  let M := K ⊗[A] B
  let : Algebra K L := Algebra.TensorProduct.rightAlgebra
  let : Algebra K M := Algebra.TensorProduct.leftAlgebra
  let e : M ≃ₐ[K] L := Algebra.TensorProduct.commRight A K B
  have : Module.Finite K M := Module.Finite.base_change A K B
  have : Module.Finite K L := Module.Finite.equiv e.toLinearEquiv
  have : Module.Projective K L := Module.Projective.of_equiv e.toLinearEquiv
  let μ : Module.End A B := Algebra.lmul A B x
  let μK : Module.End K M := μ.baseChange K
  let T : Module.End K L := Algebra.lmul K L (algebraMap B L x)
  have hx1 : algebraMap B L x = e (1 ⊗ₜ[A] x) := by
    change algebraMap B (B ⊗[A] K) x = Algebra.TensorProduct.commRight A K B (1 ⊗ₜ[A] x)
    simp
  have hconj : e.toLinearMap.comp (μK.comp e.symm.toLinearMap) = T := by
    refine LinearMap.ext fun z => ?_
    have hμK : μK = Algebra.lmul K M (1 ⊗ₜ[A] x) := Algebra.baseChange_lmul x
    change e (μK (e.symm z)) = algebraMap B L x * z
    rw [hμK]
    change e ((1 ⊗ₜ[A] x) * e.symm z) = algebraMap B L x * z
    rw [map_mul, ← hx1, e.apply_symm_apply]
  calc
    setup.trace (algebraMap B L x) = finiteProjectiveTrace K L T := by
      simpa [DedekindDifferentSetup.trace, T] using
        (finiteProjectiveTrace_eq_contract (R := K) (P := L) T).symm
    _ = finiteProjectiveTrace K L
          (e.toLinearMap.comp (μK.comp e.symm.toLinearMap)) := by rw [hconj]
    _ = finiteProjectiveTrace K M μK :=
      finiteProjectiveTrace_conj K M L e.toLinearEquiv μK
    _ = algebraMap A K (finiteProjectiveTrace A B μ) :=
      finiteProjectiveTrace_baseChange A B K μ
    _ = algebraMap A K (finiteProjectiveTraceForm A B 1 x) := by
      rw [finiteProjectiveTraceForm_one_apply]

/-- For a finite projective algebra the canonical equivalence of the complementary module with
the dualizing module carries `1` to the trace pairing against `1`. -/
theorem complementaryModuleEquivDualizingModule_one_eq_traceForm_one
    (setup : DedekindDifferentSetup A B) [Module.Finite A B] [Module.Projective A B] :
    complementaryModuleEquivDualizingModule setup
        ⟨1, one_mem_complementaryModule_of_flat setup⟩ = finiteProjectiveTraceForm A B 1 := by
  classical
  refine LinearMap.ext fun x => ?_
  apply IsFractionRing.injective A (FractionRing A)
  rw [complementaryModuleEquivDualizingModule_one_apply setup x,
    trace_algebraMap_eq_algebraMap_traceForm_one setup x]

/-- An element of the Dedekind different of a finite projective algebra carries the whole linear
dual into the image of the trace pairing. This is the only input from the theory of the
different. -/
theorem smul_dual_mem_range_of_mem_dedekindDifferentIdeal
    (setup : DedekindDifferentSetup A B) [Module.Finite A B] [Module.Projective A B]
    {b : B} (hb : b ∈ dedekindDifferentIdeal setup) (f : Module.Dual A B) :
    b • f ∈ LinearMap.range (finiteProjectiveTraceForm A B) := by
  classical
  have hspan := (mem_dedekindDifferent_iff_smul_dual_le_trace setup b).mp hb f
  rw [complementaryModuleEquivDualizingModule_one_eq_traceForm_one setup] at hspan
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
  exact ⟨c, (smul_finiteProjectiveTraceForm_one c).symm.trans hc⟩

/-- The matrix of multiplication by `b` is the matrix of coordinates of elements `c i` whose trace
pairings are `b • bas.coord i`, times the trace matrix. -/
private theorem leftMulMatrix_eq_mul_traceMatrix_aux
    [Module.Finite A B] [Module.Free A B] {n : ℕ} (bas : Module.Basis (Fin n) A B) {b : B}
    (c : Fin n → B)
    (hc : ∀ i, finiteProjectiveTraceForm A B (c i) = b • bas.coord i) :
    Algebra.leftMulMatrix bas b =
      (Matrix.of fun i l => bas.repr (c i) l) * Algebra.traceMatrix A bas := by
  classical
  have hform : (finiteProjectiveTraceForm A B : B →ₗ[A] Module.Dual A B) =
      Algebra.traceForm A B := finiteProjectiveTraceForm_eq_traceForm A B
  have key (y : B) (j : Fin n) :
      Algebra.traceForm A B y (bas j) =
        ∑ l, bas.repr y l * Algebra.traceMatrix A bas l j := by
    conv_lhs => rw [← bas.sum_repr y]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, Algebra.traceMatrix_apply]
  ext i j
  have hentry : bas.repr (b * bas j) i = Algebra.traceForm A B (c i) (bas j) := by
    have h := congrArg (fun φ : Module.Dual A B => φ (bas j)) (hc i)
    simp only [hform] at h
    simpa [algebraDualModule_smul_apply, Module.Basis.coord_apply] using h.symm
  rw [Algebra.leftMulMatrix_eq_repr_mul, hentry, key (c i) j]
  simp only [Matrix.mul_apply, Matrix.of_apply]

/-- **The matrix identity behind Stacks Tag 0BW8.** If multiplication by `b` carries the linear
dual of a finite free algebra into the image of the trace pairing, then the matrix of
multiplication by `b` in a basis is a left multiple of the trace matrix of that basis. -/
theorem exists_leftMulMatrix_eq_mul_traceMatrix
    [Module.Finite A B] [Module.Free A B] {n : ℕ} (bas : Module.Basis (Fin n) A B) {b : B}
    (hb : ∀ f : Module.Dual A B, b • f ∈ LinearMap.range (finiteProjectiveTraceForm A B)) :
    ∃ M : Matrix (Fin n) (Fin n) A,
      Algebra.leftMulMatrix bas b = M * Algebra.traceMatrix A bas :=
  ⟨_, leftMulMatrix_eq_mul_traceMatrix_aux bas (fun i => (hb (bas.coord i)).choose)
    fun i => (hb (bas.coord i)).choose_spec⟩

/-- **The determinant identity behind Stacks Tag 0BW8.** If multiplication by `b` carries the
linear dual of a finite free algebra into the image of the trace pairing, then the norm of `b` is
a determinant times the discriminant of any basis. -/
theorem exists_norm_eq_det_mul_discr
    [Module.Finite A B] [Module.Free A B] {n : ℕ} (bas : Module.Basis (Fin n) A B) {b : B}
    (hb : ∀ f : Module.Dual A B, b • f ∈ LinearMap.range (finiteProjectiveTraceForm A B)) :
    ∃ M : Matrix (Fin n) (Fin n) A, Algebra.norm A b = M.det * Algebra.discr A bas := by
  obtain ⟨M, hM⟩ := exists_leftMulMatrix_eq_mul_traceMatrix bas hb
  exact ⟨M, by rw [Algebra.norm_eq_matrix_det bas, hM, Matrix.det_mul, Algebra.discr_def]⟩

/-- The discriminant ideal of a finite free algebra is the ideal of maximal minors of the
transposed trace matrix of any basis. -/
theorem algebraDiscriminantIdeal_eq_minorIdeal_traceMatrix {n : ℕ}
    (bas : Module.Basis (Fin n) A B) :
    algebraDiscriminantIdeal A B = minorIdeal (Algebra.traceMatrix A bas)ᵀ n := by
  classical
  have : Module.Finite A B := Module.Finite.of_basis bas
  have : Module.Free A B := Module.Free.of_basis bas
  have : Module.Free A (Module.Dual A B) := Module.Free.of_basis bas.dualBasis
  have : Module.Finite A (Module.Dual A B) := Module.Finite.of_basis bas.dualBasis
  let T : B →ₗ[A] Module.Dual A B := finiteProjectiveTraceForm A B
  let D : Matrix (Fin n) (Fin n) A := LinearMap.toMatrix bas bas.dualBasis T
  let eN : (Fin n → A) ≃ₗ[A] Module.Dual A B := bas.dualBasis.equivFun.symm
  have hentry (i j : Fin n) : D i j = T (bas j) (bas i) := by
    change (LinearMap.toMatrix bas bas.dualBasis T) i j = _
    rw [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr]
  have hcol (j : Fin n) : eN (fun i => D i j) = T (bas j) := by
    apply bas.dualBasis.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    ext i
    rw [Module.Basis.equivFun_apply, Module.Basis.dualBasis_repr, hentry]
  have hmap : Submodule.map eN.toLinearMap
      (Submodule.span A (Set.range (fun j : Fin n => fun i : Fin n => D i j))) =
        LinearMap.range T := by
    rw [Submodule.map_span, ← Set.range_comp, LinearMap.range_eq_map, ← bas.span_eq,
      Submodule.map_span, ← Set.range_comp]
    exact congrArg (fun f => Submodule.span A (Set.range f)) (funext hcol)
  have hfit : fittingIdeal (R := A) (M := Module.Dual A B ⧸ LinearMap.range T) ((0 : ℕ) : ℤ) =
      minorIdeal D (n - 0) :=
    fittingIdeal_eq_minorIdeal_of_presentation D 0
      (Submodule.Quotient.equiv _ _ eN hmap)
  have hT : T = (Algebra.traceForm A B : B →ₗ[A] Module.Dual A B) :=
    finiteProjectiveTraceForm_eq_traceForm A B
  have hD : D = (Algebra.traceMatrix A bas)ᵀ := by
    ext i j
    rw [hentry, hT, Matrix.transpose_apply, Algebra.traceMatrix_apply]
  unfold algebraDiscriminantIdeal
  rw [dite_eq_left ⟨inferInstance, inferInstance⟩]
  change fittingIdeal (R := A) (M := Module.Dual A B ⧸ LinearMap.range T) 0 = _
  rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) by norm_num, hfit, Nat.sub_zero, hD]

/-- The discriminant of a basis of a finite free algebra belongs to the discriminant ideal. -/
theorem discr_mem_algebraDiscriminantIdeal {n : ℕ} (bas : Module.Basis (Fin n) A B) :
    Algebra.discr A bas ∈ algebraDiscriminantIdeal A B := by
  have hdet : Algebra.discr A bas = ((Algebra.traceMatrix A bas)ᵀ.submatrix id id).det := by
    rw [Algebra.discr_def, Matrix.submatrix_id_id, Matrix.det_transpose]
  rw [algebraDiscriminantIdeal_eq_minorIdeal_traceMatrix bas, hdet]
  exact Ideal.subset_span ⟨id, id, rfl⟩

/-- If multiplication by `b` carries the linear dual of a finite free algebra into the image of
the trace pairing, then the norm of `b` belongs to the discriminant ideal. -/
theorem norm_mem_algebraDiscriminantIdeal_of_smul_dual_mem_range
    [Module.Finite A B] [Module.Free A B] {b : B}
    (hb : ∀ f : Module.Dual A B, b • f ∈ LinearMap.range (finiteProjectiveTraceForm A B)) :
    Algebra.norm A b ∈ algebraDiscriminantIdeal A B := by
  classical
  let bas := (Module.Free.chooseBasis A B).reindex (Fintype.equivFin _)
  obtain ⟨M, hM⟩ := exists_norm_eq_det_mul_discr bas hb
  rw [hM]
  exact Ideal.mul_mem_left _ _ (discr_mem_algebraDiscriminantIdeal bas)

/-- For a finite free algebra `A → B` whose Dedekind different is defined, the norm of an element
of the Dedekind different belongs to the discriminant ideal of `B` over `A`. -/
theorem norm_mem_algebraDiscriminantIdeal
    (setup : DedekindDifferentSetup A B) [Module.Finite A B] [Module.Free A B]
    {b : B} (hb : b ∈ dedekindDifferentIdeal setup) :
    Algebra.norm A b ∈ algebraDiscriminantIdeal A B :=
  norm_mem_algebraDiscriminantIdeal_of_smul_dual_mem_range
    (smul_dual_mem_range_of_mem_dedekindDifferentIdeal setup hb)

/-! ### The norm of a generator of the different -/

/-- The ideal of maximal minors of a square matrix is generated by its determinant: a minor
indexed by a non-injective selection vanishes, and one indexed by an injective selection is the
determinant up to the sign of a permutation. -/
theorem minorIdeal_fin_eq_span_det {R : Type*} [CommRing R] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) R) : minorIdeal M n = Ideal.span ({M.det} : Set R) := by
  classical
  apply le_antisymm
  · rw [minorIdeal, Ideal.span_le]
    rintro x ⟨g, h, rfl⟩
    by_cases hg : Function.Injective g
    · by_cases hh : Function.Injective h
      · let eg : Fin n ≃ Fin n := Equiv.ofBijective g ⟨hg, Finite.injective_iff_surjective.mp hg⟩
        let eh : Fin n ≃ Fin n := Equiv.ofBijective h ⟨hh, Finite.injective_iff_surjective.mp hh⟩
        let σ := eh.trans eg.symm
        have hmat : M.submatrix g h = (M.submatrix eg eg).submatrix id σ := by
          ext i j
          change M (g i) (h j) = M (eg i) (eg (eg.symm (eh j)))
          rw [eg.apply_symm_apply]
          rfl
        rw [hmat, Matrix.det_permute', Matrix.det_submatrix_equiv_self]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      · obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hh
        have hdet : (M.submatrix g h).det = 0 := by
          apply Matrix.det_zero_of_column_eq hij
          intro k
          simp [Matrix.submatrix_apply, heq]
        exact hdet ▸ Ideal.zero_mem _
    · obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hg
      have hdet : (M.submatrix g h).det = 0 := by
        apply Matrix.det_zero_of_row_eq hij
        ext k
        simp [Matrix.submatrix_apply, heq]
      exact hdet ▸ Ideal.zero_mem _
  · rw [Ideal.span_singleton_le_iff_mem, minorIdeal]
    exact Ideal.subset_span ⟨id, id, rfl⟩

/-- **The discriminant ideal of a finite free algebra is generated by the discriminant of any
basis.** The trace pairing is presented, in a basis and its dual basis, by the transpose of the
trace matrix, and the zeroth Fitting ideal of the cokernel of a square presentation is generated
by its determinant. -/
@[ega "IV 18.10.15" "more general", ega "IV 18.2.7" "special case"]
theorem algebraDiscriminantIdeal_eq_span_discr {n : ℕ} (bas : Module.Basis (Fin n) A B) :
    algebraDiscriminantIdeal A B = Ideal.span ({Algebra.discr A bas} : Set A) := by
  rw [algebraDiscriminantIdeal_eq_minorIdeal_traceMatrix bas, minorIdeal_fin_eq_span_det,
    Matrix.det_transpose, Algebra.discr_def]

/-- **The matrix identity behind Stacks Tag 0BWA (2).** The explicit form of
`Stacks.Discriminant.exists_leftMulMatrix_eq_mul_traceMatrix`: given elements `c i` whose trace
pairings are the multiples `b · bᵢ^∨` of the dual basis, the matrix of multiplication by `b` is
the matrix expressing the `c i` in the basis, times the trace matrix. -/
theorem leftMulMatrix_eq_mul_traceMatrix
    [Module.Finite A B] [Module.Free A B] {n : ℕ} (bas : Module.Basis (Fin n) A B) {b : B}
    (c : Fin n → B)
    (hc : ∀ i, finiteProjectiveTraceForm A B (c i) = b • bas.coord i) :
    Algebra.leftMulMatrix bas b =
      (Matrix.of fun i l => bas.repr (c i) l) * Algebra.traceMatrix A bas :=
  leftMulMatrix_eq_mul_traceMatrix_aux bas c hc

/-- **Stacks Project, Tag 0BWA, part (2), the affine computation.** Let `A → B` be a finite free
algebra whose `A`-linear dual is free of rank one over `B` on a generator `λ`, and write the
trace pairing as `Tr_{B/A} = b · λ`.  Then the discriminant ideal of `B` over `A` is generated
by the norm of `b`, the generator of the different.

Writing the dual basis as `bᵢ^∨ = cᵢ · λ` exhibits `c₁, …, cₙ` as an `A`-basis of `B`, because
`λ` identifies `B` with its dual; so the matrix expressing the `cᵢ` in the given basis has unit
determinant.  The matrix of multiplication by `b` is that matrix times the trace matrix, whose
determinant generates the discriminant ideal. -/
theorem algebraDiscriminantIdeal_eq_span_norm_of_dualGenerator
    [Module.Finite A B] [Module.Free A B]
    {n : ℕ} (bas : Module.Basis (Fin n) A B) (lam : Module.Dual A B)
    (hlam : Function.Bijective fun c : B => c • lam)
    {b : B} (hb : finiteProjectiveTraceForm A B 1 = b • lam) :
    algebraDiscriminantIdeal A B = Ideal.span ({Algebra.norm A b} : Set A) := by
  classical
  -- the generator `λ` identifies `B` with its `A`-linear dual, `A`-linearly
  let ψ : B →ₗ[A] Module.Dual A B :=
    { toFun := fun c => c • lam
      map_add' := fun c c' => add_smul c c' lam
      map_smul' := fun a c => by
        refine LinearMap.ext fun x => ?_
        change lam ((a • c) * x) = a • lam (c * x)
        rw [Algebra.smul_def a c, mul_assoc, ← Algebra.smul_def a (c * x), map_smul] }
  let e : B ≃ₗ[A] Module.Dual A B := LinearEquiv.ofBijective ψ hlam
  let cbas : Module.Basis (Fin n) A B := bas.dualBasis.map e.symm
  have hcbas (i : Fin n) : (cbas i) • lam = bas.coord i :=
    (e.apply_symm_apply (bas.dualBasis i)).trans (congrFun bas.coe_dualBasis i)
  have hc (i : Fin n) : finiteProjectiveTraceForm A B (cbas i) = b • bas.coord i := by
    rw [← smul_finiteProjectiveTraceForm_one (cbas i), hb, smul_comm, hcbas i]
  have hmat : (Matrix.of fun i l => bas.repr (cbas i) l) = (bas.toMatrix cbas)ᵀ := rfl
  have hunit : IsUnit
      ((Matrix.of fun i l => bas.repr (cbas i) l : Matrix (Fin n) (Fin n) A)).det := by
    rw [hmat, Matrix.det_transpose]
    exact Matrix.isUnit_det_of_right_inverse (bas.toMatrix_mul_toMatrix_flip cbas)
  have hnorm : Algebra.norm A b =
      ((Matrix.of fun i l => bas.repr (cbas i) l : Matrix (Fin n) (Fin n) A)).det *
        Algebra.discr A bas := by
    rw [Algebra.norm_eq_matrix_det bas, leftMulMatrix_eq_mul_traceMatrix bas cbas hc,
      Matrix.det_mul, Algebra.discr_def]
  rw [algebraDiscriminantIdeal_eq_span_discr bas, hnorm,
    Ideal.span_singleton_mul_left_unit hunit]

end General

section BaseChange

variable (R : Type u) (A : Type v) (S : Type w)
  [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]

/-- Multiplying a base-changed functional by a pure tensor `1 ⊗ b` is the base change of
multiplication by `b`. -/
theorem smul_dualTensorBaseChange_tmul [Module.Finite R A] [Module.Projective R A]
    (b : A) (s : S) (g : Module.Dual R A) :
    ((1 : S) ⊗ₜ[R] b) • dualTensorBaseChange R A S (s ⊗ₜ[R] g) =
      dualTensorBaseChange R A S (s ⊗ₜ[R] (b • g)) := by
  classical
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t y =>
    rw [algebraDualModule_smul_apply, Algebra.TensorProduct.tmul_mul_tmul,
      dualTensorBaseChange_tmul_apply, dualTensorBaseChange_tmul_apply]
    simp [algebraDualModule_smul_apply, Module.Dual.baseChange_apply_tmul]
  | add z z' hz hz' =>
    rw [algebraDualModule_smul_apply] at hz hz' ⊢
    rw [mul_add, map_add, map_add, hz, hz']

/-- The hypothesis that an element carries the whole linear dual into the image of the trace
pairing is stable under base change. -/
theorem smul_dual_mem_range_baseChange [Module.Finite R A] [Module.Projective R A]
    {b : A} (hb : ∀ g : Module.Dual R A, b • g ∈ LinearMap.range (finiteProjectiveTraceForm R A))
    (f : Module.Dual S (S ⊗[R] A)) :
    ((1 : S) ⊗ₜ[R] b) • f ∈
      LinearMap.range (finiteProjectiveTraceForm S (S ⊗[R] A)) := by
  classical
  obtain ⟨z, rfl⟩ := (dualTensorBaseChange_bijective R A S).2 f
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s g =>
    obtain ⟨c, hc⟩ := hb g
    refine ⟨s ⊗ₜ[R] c, ?_⟩
    rw [smul_dualTensorBaseChange_tmul, ← hc]
    simpa [LinearMap.baseChange_tmul] using
      congrArg (fun T : (S ⊗[R] A) →ₗ[S] Module.Dual S (S ⊗[R] A) => T (s ⊗ₜ[R] c))
        (finiteProjectiveTraceForm_scalarTensor_map R A S)
  | add z z' hz hz' =>
    rw [map_add, smul_add]
    exact add_mem hz hz'

end BaseChange

section Projective

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- If multiplication by `b` carries the linear dual of a finite projective algebra into the
image of the trace pairing, then the projective norm of `b` belongs to the discriminant ideal. -/
theorem finiteProjective_mem_algebraDiscriminantIdeal_of_smul_dual_mem_range
    [Module.Finite A B] [Module.Projective A B] {b : B}
    (hb : ∀ f : Module.Dual A B, b • f ∈ LinearMap.range (finiteProjectiveTraceForm A B)) :
    Algebra.projectiveNorm A b ∈ algebraDiscriminantIdeal A B := by
  classical
  refine Ideal.mem_of_localization_maximal fun P hP => ?_
  have : P.IsPrime := hP.isPrime
  let S := Localization.AtPrime P
  have : Module.FinitePresentation S (S ⊗[A] B) :=
    Module.finitePresentation_of_projective S (S ⊗[A] B)
  have : Module.Free S (S ⊗[A] B) := Module.free_of_flat_of_isLocalRing
  rw [algebraDiscriminantIdeal_map A B S,
    ← Algebra.projectiveNorm_baseChange (R := A) (A := S) (B := B) b,
    Algebra.projectiveNorm_eq_norm_of_free]
  exact norm_mem_algebraDiscriminantIdeal_of_smul_dual_mem_range
    (smul_dual_mem_range_baseChange A B S hb)

/-- **Stacks Project, Tag 0BW8, the affine computation.** For a finite projective algebra
`A → B` whose Dedekind different is defined, the norm of an element of the Dedekind different
belongs to the discriminant ideal of `B` over `A`. The norm here is the projective norm
`Algebra.projectiveNorm`, which agrees with `Algebra.norm` when `B` is free over `A`. -/
@[stacks 0BW8 "the affine computation"]
theorem finiteProjective_mem_algebraDiscriminantIdeal
    (setup : DedekindDifferentSetup A B) [Module.Finite A B] [Module.Projective A B]
    {b : B} (hb : b ∈ dedekindDifferentIdeal setup) :
    Algebra.projectiveNorm A b ∈ algebraDiscriminantIdeal A B :=
  finiteProjective_mem_algebraDiscriminantIdeal_of_smul_dual_mem_range
    (smul_dual_mem_range_of_mem_dedekindDifferentIdeal setup hb)

end Projective

end Stacks.Discriminant

end
