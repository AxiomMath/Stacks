module

public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.ChartAlgebra
public import StacksFrontier.RingTheory.Fitting.Rank
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The locus where a chart applies

Let `K ⊆ R' ⊗_R A` be an ideal such that `B = (R' ⊗_R A) / K` is a finite locally free
`R'`-module of rank `d`, and let `w : Fin d → A`. The images of the `1 ⊗ w l` span `B` exactly
when they form a basis of it, and the locus of `Spec R'` over which they span is the
complement of the zero locus of the zeroth Fitting ideal of the cokernel: for an
`R'`-algebra `R''` the images span `(R'' ⊗_R A) / K R''` over `R''` exactly when that Fitting
ideal generates the unit ideal of `R''`. These are the openness and the covering statements for
the charts of the Hilbert scheme of points in the proof of Stacks Tag 0B99 (the source cites
Stacks Tag 00O0 and Nakayama's lemma).

## Main results

* `Stacks.Hilbert.Chart.injective_of_surjective_of_isFiniteLocallyFreeOfRank`: a surjection
  `R^d → M` onto a finite locally free module of rank `d` is injective.
* `Stacks.Hilbert.Chart.subsingleton_tensor_iff`: base change kills a finite module exactly
  when the zeroth Fitting ideal extends to the unit ideal.
* `Stacks.Hilbert.Chart.span_chartVector_map_eq_top_iff`: the locus where the chart applies.
-/

@[expose] public noncomputable section

open TensorProduct

universe u v w

namespace Stacks.Hilbert.Chart

/-- **A surjection `R^d → M` onto a finite locally free module of rank `d` is injective.** The
zeroth-minus-one Fitting ideal `Fit_{d-1}(M)` vanishes and contains every coordinate of every
element of the kernel. -/
theorem injective_of_surjective_of_isFiniteLocallyFreeOfRank {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] {d : ℕ}
    (h : Module.IsFiniteLocallyFreeOfRank R M d) (φ : (Fin d → R) →ₗ[R] M)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  rcases d with _ | k
  · exact fun x y _ => Subsingleton.elim x y
  have hfit : fittingIdeal (R := R) (M := M) ((k : ℤ)) = ⊥ := by
    have := ((finiteLocallyFreeOfRank_fittingIdeal_tfae (R := R) (M := M) (k + 1)).out 1 2).mp h
    simpa using this.1
  let A : Matrix (Fin (k + 1)) (LinearMap.ker φ) R := fun i j => (j : Fin (k + 1) → R) i
  have hker : Submodule.span R (Set.range fun j : LinearMap.ker φ => fun i => A i j) =
      LinearMap.ker φ :=
    le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 fun j => j.2))
      fun x hx => Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
  have hminor := fittingIdeal_eq_minorIdeal_of_presentation (M := M) A k
    ((Submodule.quotEquivOfEq _ _ hker).trans (φ.quotKerEquivOfSurjective hφ))
  rw [hfit, show k + 1 - k = 1 by omega] at hminor
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  funext i
  have hmem : A i ⟨x, hx⟩ ∈ minorIdeal A 1 :=
    Ideal.subset_span ⟨fun _ => i, fun _ => ⟨x, hx⟩, by simp [Matrix.det_unique]⟩
  rw [← hminor] at hmem
  exact (Submodule.mem_bot R).mp hmem

/-- **Base change kills a finite module exactly when its zeroth Fitting ideal extends to the
unit ideal.** -/
@[sga "7 VI 5.1" "more general"]
theorem subsingleton_tensor_iff {R : Type u} [CommRing R] {N : Type v} [AddCommGroup N]
    [Module R N] [Module.Finite R N] (R'' : Type w) [CommRing R''] [Algebra R R''] :
    Subsingleton (R'' ⊗[R] N) ↔
      Ideal.map (algebraMap R R'') (fittingIdeal (R := R) (M := N) 0) = ⊤ := by
  have h3 := (fittingIdeal_basic_properties.{u, v, v, w} (R := R) (M := N)).2.2.1 R'' 0
  have h7 := (fittingIdeal_basic_properties.{w, max v w, max v w, w} (R := R'')
    (M := R'' ⊗[R] N)).2.2.2.2.2.2.1
  rw [← Module.support_eq_empty_iff (R := R''), ← h7, PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  simp only [Nat.cast_zero] at h3
  rw [h3]

/-- The image of `R'' ⊗_R n` in `R'' ⊗_R B`, for `n` spanned by a family `v`, is the
`R''`-span of the `1 ⊗ v i`. -/
theorem range_lTensor_span {R : Type u} [CommRing R] {B : Type v} [AddCommGroup B] [Module R B]
    (R'' : Type w) [CommRing R''] [Algebra R R''] {ι : Type*} (v : ι → B) :
    LinearMap.range (AlgebraTensorModule.lTensor R'' R''
      ((Submodule.span R (Set.range v)).subtype.restrictScalars R)) =
      Submodule.span R'' (Set.range fun i => (1 : R'') ⊗ₜ[R] v i) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul r y =>
      obtain ⟨y, hy⟩ := y
      simp only [AlgebraTensorModule.lTensor_tmul, LinearMap.coe_restrictScalars,
        Submodule.subtype_apply]
      rw [show r ⊗ₜ[R] y = r • ((1 : R'') ⊗ₜ[R] y) by rw [smul_tmul', smul_eq_mul, mul_one]]
      refine Submodule.smul_mem _ _ ?_
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [tmul_add]
        exact add_mem hx hy
      | smul a x _ hx =>
        rw [tmul_smul, ← algebraMap_smul R'' a]
        exact Submodule.smul_mem _ _ hx
    | add x y hx hy =>
      rw [map_add]
      exact add_mem hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(1 : R'') ⊗ₜ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩, rfl⟩

/-- The `R''`-span of the `1 ⊗ v i` is everything exactly when base change kills the quotient
by the span of the `v i`. -/
theorem span_one_tmul_eq_top_iff {R : Type u} [CommRing R] {B : Type v} [AddCommGroup B]
    [Module R B] (R'' : Type w) [CommRing R''] [Algebra R R''] {ι : Type*} (v : ι → B) :
    Submodule.span R'' (Set.range fun i => (1 : R'') ⊗ₜ[R] v i) = ⊤ ↔
      Subsingleton (R'' ⊗[R] (B ⧸ Submodule.span R (Set.range v))) := by
  let e := AlgebraTensorModule.tensorQuotientEquiv (R := R) R'' R R''
    (Submodule.span R (Set.range v))
  rw [e.subsingleton_congr, Submodule.Quotient.subsingleton_iff, range_lTensor_span]

section BaseChange

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {d : ℕ}
  (w : Fin d → A) {R' : Type u} [CommRing R'] [Algebra R R'] {R'' : Type u} [CommRing R'']
  [Algebra R R'']

/-- **Base change of a quotient of `R' ⊗_R A`.** For an `R`-algebra map `φ : R' → R''` and an
ideal `K` of `R' ⊗_R A`, the quotient of `R'' ⊗_R A` by the extension of `K` is the base change
along `φ` of `(R' ⊗_R A) / K`. -/
def quotientBaseChange (φ : R' →ₐ[R] R'') (K : Ideal (R' ⊗[R] A)) :
    letI := φ.toRingHom.toAlgebra
    R'' ⊗[R'] (R' ⊗[R] A ⧸ K) ≃ₐ[R''] R'' ⊗[R] A ⧸ K.map (Algebra.TensorProduct.map φ
      (AlgHom.id R A)) :=
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R R' R'' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R') R'' (R' ⊗[R] A) R'' K).trans
    (Ideal.quotientEquivAlg _ _ (Algebra.TensorProduct.cancelBaseChange R R' R'' R'' A) (by
      have hc : (Algebra.TensorProduct.map φ (AlgHom.id R A)).toRingHom =
          ((Algebra.TensorProduct.cancelBaseChange R R' R'' R'' A : _ ≃ₐ[R''] _) :
            R'' ⊗[R'] (R' ⊗[R] A) →+* R'' ⊗[R] A).comp
            (Algebra.TensorProduct.includeRight :
              R' ⊗[R] A →ₐ[R'] R'' ⊗[R'] (R' ⊗[R] A)).toRingHom := by
        refine RingHom.ext fun x => ?_
        induction x using TensorProduct.inductionOn with
        | tmul r a =>
          simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
            Function.comp_apply, Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.map_tmul,
            AlgHom.coe_id, id_eq]
          rw [Algebra.smul_def, mul_one]
          rfl
        | add x y hx hy =>
          simp only [map_add] at hx hy ⊢
          rw [hx, hy]
      change Ideal.map (Algebra.TensorProduct.map φ (AlgHom.id R A)).toRingHom K = Ideal.map
        ((Algebra.TensorProduct.cancelBaseChange R R' R'' R'' A : _ ≃ₐ[R''] _) :
          R'' ⊗[R'] (R' ⊗[R] A) →+* R'' ⊗[R] A)
        (Ideal.map (Algebra.TensorProduct.includeRight :
          R' ⊗[R] A →ₐ[R'] R'' ⊗[R'] (R' ⊗[R] A)).toRingHom K)
      rw [Ideal.map_map, hc]))

/-- The isomorphism `quotientBaseChange φ K` sends `1 ⊗ x̄` to the class of the image of `x` under
`φ ⊗ id_A`. -/
theorem quotientBaseChange_one_tmul (φ : R' →ₐ[R] R'') (K : Ideal (R' ⊗[R] A)) (x : R' ⊗[R] A) :
    letI := φ.toRingHom.toAlgebra
    quotientBaseChange φ K (1 ⊗ₜ Ideal.Quotient.mk K x) =
      Ideal.Quotient.mk _ (Algebra.TensorProduct.map φ (AlgHom.id R A) x) := by
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R R' R'' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    simp only [quotientBaseChange, AlgEquiv.trans_apply,
      Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg,
      Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
    change Ideal.Quotient.mk _ (Algebra.TensorProduct.cancelBaseChange R R' R'' R'' A
      (1 ⊗ₜ (r ⊗ₜ a))) = _
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy =>
    simp only [map_add, tmul_add] at hx hy ⊢
    rw [hx, hy]

/-- **The locus where the chart applies.** The images of `w` span the base change along
`φ : R' → R''` of `(R' ⊗_R A) / K` exactly when the zeroth Fitting ideal of the cokernel of
`R'^d → (R' ⊗_R A) / K` extends to the unit ideal of `R''`. -/
theorem span_chartVector_map_eq_top_iff (φ : R' →ₐ[R] R'') (K : Ideal (R' ⊗[R] A))
    [Module.Finite R' (R' ⊗[R] A ⧸ K)] :
    Submodule.span R'' (Set.range (chartVector w
      (K.map (Algebra.TensorProduct.map φ (AlgHom.id R A))))) = ⊤ ↔
      Ideal.map φ (fittingIdeal (R := R')
        (M := (R' ⊗[R] A ⧸ K) ⧸ Submodule.span R' (Set.range (chartVector w K))) 0) = ⊤ := by
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R R' R'' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have hE : ∀ l, quotientBaseChange φ K (1 ⊗ₜ chartVector w K l) =
      chartVector w (K.map (Algebra.TensorProduct.map φ (AlgHom.id R A))) l := by
    intro l
    rw [chartVector, quotientBaseChange_one_tmul]
    simp only [Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]
    rfl
  have h1 : Submodule.span R'' (Set.range (chartVector w
      (K.map (Algebra.TensorProduct.map φ (AlgHom.id R A))))) =
      Submodule.map ((quotientBaseChange φ K).toLinearEquiv :
        R'' ⊗[R'] (R' ⊗[R] A ⧸ K) →ₗ[R''] R'' ⊗[R] A ⧸ _)
        (Submodule.span R'' (Set.range fun l => (1 : R'') ⊗ₜ[R'] chartVector w K l)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply, AlgEquiv.toLinearEquiv_toLinearMap,
      AlgEquiv.toLinearMap_apply, hE]
  rw [h1, Submodule.map_eq_top_iff, span_one_tmul_eq_top_iff, subsingleton_tensor_iff]
  rfl

end BaseChange

end Stacks.Hilbert.Chart

end
