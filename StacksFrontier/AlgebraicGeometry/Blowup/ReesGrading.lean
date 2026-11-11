module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.ReesAlgebra
public import StacksCore.Tactic.StacksAttribute

/-!
# The grading of the Rees algebra

The Rees algebra `R[It]` of an ideal `I` of a commutative ring `R` is the subalgebra of `R[X]`
whose `i`-th coefficient lies in `Iⁱ`. Mathlib defines it as `reesAlgebra I` but records no
grading on it, even though the point of the Rees algebra is that it is the graded algebra
`⨁ₙ Iⁿ`. This file supplies that grading.

The degree-`n` part is the set of elements of `reesAlgebra I` supported in degree `n`, that is
the monomials `monomial n r` with `r ∈ Iⁿ`. These pieces are `R`-submodules, they satisfy the
graded-monoid axioms, and the resulting decomposition makes `reesAlgebra I` a graded `R`-algebra.

`Proj` of this grading is the blowup of `Spec R` in `I`.

## Main definitions

* `Stacks.Blowup.reesGrading` is the degree-`n` homogeneous part of `reesAlgebra I`.
* `Stacks.Blowup.reesMonomial` is the `R`-linear inclusion of `Iⁿ` as the degree-`n` part.
* `Stacks.Blowup.reesComponent` is the projection onto the degree-`n` part.
* `Stacks.Blowup.instGradedAlgebraReesGrading` makes `reesAlgebra I` a graded `R`-algebra.

## Main results

* `Stacks.Blowup.reesGradingEquivPow` identifies the degree-`n` part with `Iⁿ`.
* `Stacks.Blowup.reesGradingZeroEquiv` identifies the degree-zero part with `R`.
* `Stacks.Blowup.reesGrading_eq_range` describes the degree-`n` part as the image of `Iⁿ`.
* `Stacks.Blowup.adjoin_reesGrading_one_eq_top` says the Rees algebra is generated in degree
  one.

## Implementation notes

The grading is registered as a global instance. Unlike a polynomial ring, which carries several
useful gradings and whose grading Mathlib therefore keeps local, the Rees algebra has only this
one, so there is no competing instance to shadow.

The decomposition is built from `DirectSum.mk` over the polynomial support.

## References

* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 052Q](https://stacks.math.columbia.edu/tag/052Q), part (1)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open Polynomial DirectSum

universe u

namespace Stacks.Blowup

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The degree-`n` homogeneous part of the Rees algebra: those elements of `reesAlgebra I`
whose only possibly nonzero coefficient is the `n`-th one. Concretely these are the monomials
`monomial n r` with `r ∈ Iⁿ`; see `reesGrading_eq_range`. -/
def reesGrading (n : ℕ) : Submodule R (reesAlgebra I) where
  carrier := {f | ∀ i, i ≠ n → ((f : R[X])).coeff i = 0}
  add_mem' hf hg i hi := by
    simp only [Subalgebra.coe_add, coeff_add, hf i hi, hg i hi, add_zero]
  zero_mem' i _ := by simp
  smul_mem' c f hf i hi := by
    simp only [SetLike.val_smul, coeff_smul, hf i hi, smul_zero]

/-- An element of the Rees algebra has degree `n` iff all its coefficients other than the `n`-th
vanish. -/
theorem mem_reesGrading_iff {n : ℕ} {f : reesAlgebra I} :
    f ∈ reesGrading I n ↔ ∀ i, i ≠ n → ((f : R[X])).coeff i = 0 :=
  Iff.rfl

/-- A homogeneous element of degree `n` is the monomial determined by its `n`-th coefficient. -/
theorem coe_eq_monomial {n : ℕ} {f : reesAlgebra I} (hf : f ∈ reesGrading I n) :
    ((f : R[X])) = monomial n ((f : R[X]).coeff n) := by
  ext i
  rw [coeff_monomial]
  split_ifs with h
  · rw [h]
  · exact hf i fun e => h e.symm

/-- The `R`-linear map sending `r ∈ Iⁿ` to the degree-`n` element `monomial n r` of the Rees
algebra. It is an isomorphism onto the degree-`n` part; see `reesGradingEquivPow`. -/
def reesMonomial (n : ℕ) : (I ^ n : Ideal R) →ₗ[R] reesGrading I n where
  toFun r := ⟨⟨monomial n r, reesAlgebra.monomial_mem.mpr r.2⟩, by
    intro i hi
    simp [coeff_monomial, Ne.symm hi]⟩
  map_add' r s := by ext; simp
  map_smul' c r := by ext i; simp [coeff_monomial, mul_ite]

/-- The image of `r ∈ Iⁿ` under `reesMonomial I n` is the polynomial `monomial n r`. -/
@[simp]
theorem coe_reesMonomial {n : ℕ} (r : (I ^ n : Ideal R)) :
    ((reesMonomial I n r : reesAlgebra I) : R[X]) = monomial n (r : R) :=
  rfl

/-- The map `reesMonomial I n` is injective. -/
theorem reesMonomial_injective (n : ℕ) : Function.Injective (reesMonomial I n) := by
  intro r s h
  have h2 : ((reesMonomial I n r : reesAlgebra I) : R[X]) =
      ((reesMonomial I n s : reesAlgebra I) : R[X]) := by rw [h]
  rw [coe_reesMonomial, coe_reesMonomial] at h2
  exact Subtype.ext (by simpa using congrArg (fun p : R[X] => p.coeff n) h2)

/-- The degree-`n` part of the Rees algebra is exactly the image of `Iⁿ` under `monomial n`. -/
theorem reesGrading_eq_range (n : ℕ) : reesGrading I n = LinearMap.range
    ((reesGrading I n).subtype ∘ₗ reesMonomial I n) := by
  refine le_antisymm (fun f hf => ?_) (fun f hf => ?_)
  · exact ⟨⟨(f : R[X]).coeff n, f.2 n⟩, Subtype.ext (coe_eq_monomial I hf).symm⟩
  · obtain ⟨r, rfl⟩ := hf
    exact (reesMonomial I n r).2

/-- The degree-`n` part of the Rees algebra is `Iⁿ`, via `r ↦ monomial n r`. -/
def reesGradingEquivPow (n : ℕ) : (I ^ n : Ideal R) ≃ₗ[R] reesGrading I n :=
  LinearEquiv.ofBijective (reesMonomial I n) ⟨reesMonomial_injective I n, fun f =>
    ⟨⟨((f : reesAlgebra I) : R[X]).coeff n, (f : reesAlgebra I).2 n⟩,
      Subtype.ext (Subtype.ext (coe_eq_monomial I f.2).symm)⟩⟩

/-- The image of `r ∈ Iⁿ` under `reesGradingEquivPow I n` is the polynomial `monomial n r`. -/
@[simp]
theorem coe_reesGradingEquivPow {n : ℕ} (r : (I ^ n : Ideal R)) :
    ((reesGradingEquivPow I n r : reesAlgebra I) : R[X]) = monomial n (r : R) :=
  rfl

/-- The inverse of `reesGradingEquivPow I n` sends a degree-`n` element to its `n`-th
coefficient. -/
@[simp]
theorem coe_reesGradingEquivPow_symm {n : ℕ} (f : reesGrading I n) :
    (((reesGradingEquivPow I n).symm f : R)) = ((f : reesAlgebra I) : R[X]).coeff n := by
  conv_rhs => rw [← (reesGradingEquivPow I n).apply_symm_apply f]
  rw [coe_reesGradingEquivPow]
  simp

/-- The homogeneous pieces of the Rees algebra form a graded monoid: `1` has degree zero and
the product of elements of degrees `m` and `n` has degree `m + n`. -/
instance instGradedMonoidReesGrading : SetLike.GradedMonoid (reesGrading I) where
  one_mem i hi := by simp [coeff_one, hi]
  mul_mem m n a b ha hb i hi := by
    obtain ⟨ca, hca⟩ : ∃ c, ((a : R[X])) = monomial m c := ⟨_, coe_eq_monomial I ha⟩
    obtain ⟨cb, hcb⟩ : ∃ c, ((b : R[X])) = monomial n c := ⟨_, coe_eq_monomial I hb⟩
    have h : ((a * b : reesAlgebra I) : R[X]) = monomial (m + n) (ca * cb) := by
      rw [Subalgebra.coe_mul, hca, hcb, monomial_mul_monomial]
    rw [h]
    simp [coeff_monomial, Ne.symm hi]

/-- The projection of the Rees algebra onto its degree-`n` part, sending `f` to the monomial
`monomial n (f.coeff n)`. -/
def reesComponent (n : ℕ) : reesAlgebra I →ₗ[R] reesGrading I n where
  toFun f := ⟨⟨monomial n ((f : R[X]).coeff n), reesAlgebra.monomial_mem.mpr (f.2 n)⟩, by
    intro i hi
    simp [coeff_monomial, Ne.symm hi]⟩
  map_add' f g := by ext; simp
  map_smul' c f := by ext i; simp [coeff_monomial, mul_ite]

/-- The degree-`n` component of `f` is the polynomial `monomial n (f.coeff n)`. -/
@[simp]
theorem coe_reesComponent {n : ℕ} (f : reesAlgebra I) :
    ((reesComponent I n f : reesAlgebra I) : R[X]) = monomial n ((f : R[X]).coeff n) :=
  rfl

/-- The degree-`n` component of an element of degree `n` is that element itself. -/
theorem reesComponent_eq_self {n : ℕ} {f : reesAlgebra I} (hf : f ∈ reesGrading I n) :
    reesComponent I n f = ⟨f, hf⟩ :=
  Subtype.ext (Subtype.ext (coe_eq_monomial I hf).symm)

/-- The degree-`n` component of `f` vanishes when the `n`-th coefficient of `f` does. -/
theorem reesComponent_eq_zero {n : ℕ} {f : reesAlgebra I} (hf : (f : R[X]).coeff n = 0) :
    reesComponent I n f = 0 :=
  Subtype.ext (Subtype.ext (by simp [hf]))

/-- A coefficient of a sum of homogeneous elements only sees the piece of matching degree: the
`i`-th coefficient of `∑ₙ xₙ` is the `i`-th coefficient of `xᵢ`. -/
theorem coeff_coeAddMonoidHom (x : ⨁ n, reesGrading I n) (i : ℕ) :
    (((DirectSum.coeAddMonoidHom (reesGrading I) x : reesAlgebra I)) : R[X]).coeff i =
      (((x i : reesGrading I i) : reesAlgebra I) : R[X]).coeff i := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j y =>
    obtain rfl | h := eq_or_ne j i
    · rw [DirectSum.coeAddMonoidHom_of, DirectSum.of_eq_same]
    · rw [DirectSum.coeAddMonoidHom_of, DirectSum.of_eq_of_ne _ _ _ h.symm]
      simpa using y.2 i (Ne.symm h)
  | add x y hx hy =>
    rw [map_add, Subalgebra.coe_add, coeff_add, hx, hy, DFinsupp.add_apply,
      AddMemClass.coe_add, Subalgebra.coe_add, coeff_add]

/-- The homogeneous decomposition of an element of the Rees algebra, as a function. -/
def reesDecomposeFun (f : reesAlgebra I) : ⨁ n, reesGrading I n :=
  DirectSum.mk (fun n => reesGrading I n) ((f : R[X]).support)
    fun i => reesComponent I i.1 f

/-- The degree-`n` entry of `reesDecomposeFun I f` is the degree-`n` component of `f`. -/
@[simp]
theorem reesDecomposeFun_apply (f : reesAlgebra I) (n : ℕ) :
    reesDecomposeFun I f n = reesComponent I n f := by
  by_cases hn : n ∈ (f : R[X]).support
  · exact DirectSum.mk_apply_of_mem hn
  · rw [reesDecomposeFun, DirectSum.mk_apply_of_notMem hn]
    exact (reesComponent_eq_zero I (notMem_support_iff.mp hn)).symm

/-- The decomposition of the Rees algebra into its homogeneous pieces, as an additive map. -/
def reesDecompose : reesAlgebra I →+ ⨁ n, reesGrading I n where
  toFun := reesDecomposeFun I
  map_zero' := DFinsupp.ext fun n => by
    rw [reesDecomposeFun_apply, DFinsupp.zero_apply, map_zero]
  map_add' f g := DFinsupp.ext fun n => by
    rw [reesDecomposeFun_apply, DFinsupp.add_apply, reesDecomposeFun_apply,
      reesDecomposeFun_apply, map_add]

/-- The degree-`n` entry of `reesDecompose I f` is the degree-`n` component of `f`. -/
@[simp]
theorem reesDecompose_apply (f : reesAlgebra I) (n : ℕ) :
    reesDecompose I f n = reesComponent I n f :=
  reesDecomposeFun_apply I f n

/-- The Rees algebra is the direct sum of its homogeneous pieces. -/
instance instDecompositionReesGrading : DirectSum.Decomposition (reesGrading I) :=
  DirectSum.Decomposition.ofAddHom (reesGrading I) (reesDecompose I)
    (AddMonoidHom.ext fun f => Subtype.ext (Polynomial.ext fun i => by
      simp [coeff_coeAddMonoidHom]))
    (AddMonoidHom.ext fun x => DFinsupp.ext fun n => Subtype.ext (Subtype.ext (by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.id_apply,
        reesDecompose_apply, coe_reesComponent, coeff_coeAddMonoidHom]
      exact (coe_eq_monomial I (x n).2).symm)))

/-- **The Rees algebra is a graded algebra.** The ideal powers `Iⁿ`, placed in degree `n`,
decompose `R[It]`. This is the blowup algebra `Bl_I(R) = ⨁_{n ≥ 0} Iⁿ` of Stacks 052Q (1): the
`R`-algebra `reesAlgebra I` with this grading, whose degree-`n` part is `Iⁿ` by
`reesGradingEquivPow`. -/
@[ega "III 4.1.7.7", stacks 052Q "(1) the blowup (Rees) algebra Bl_I(R) = ⨁ₙ Iⁿ as a graded \
  R-algebra: `reesAlgebra I` graded by `reesGrading I`, degree n part ≅ Iⁿ (`reesGradingEquivPow`)"]
instance instGradedAlgebraReesGrading : GradedAlgebra (reesGrading I) where

/-- The degree-zero part of the Rees algebra is `R`. -/
def reesGradingZeroEquiv : R ≃+* reesGrading I 0 :=
  RingEquiv.ofBijective (algebraMap R (reesGrading I 0)) <| by
    constructor
    · intro a b hab
      have h : (C a : R[X]) = C b := by
        simpa [SetLike.GradeZero.coe_algebraMap] using
          congrArg (fun x : reesGrading I 0 => ((x : reesAlgebra I) : R[X])) hab
      simpa using congrArg (fun p : R[X] => p.coeff 0) h
    · intro f
      refine ⟨((f : reesAlgebra I) : R[X]).coeff 0, Subtype.ext (Subtype.ext ?_)⟩
      rw [SetLike.GradeZero.coe_algebraMap]
      simpa [monomial_zero_left] using (coe_eq_monomial I f.2).symm

/-- The degree-one part of the Rees algebra, as a subset of the Rees algebra, is the set of
monomials `monomial 1 r` with `r ∈ I`. -/
theorem coe_image_reesGrading_one :
    (reesAlgebra I).val '' ((reesGrading I 1 : Submodule R (reesAlgebra I)) :
        Set (reesAlgebra I)) =
      (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) := by
  ext p
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨(f : R[X]).coeff 1, ?_, (coe_eq_monomial I hf).symm⟩
    simpa using f.2 1
  · rintro ⟨r, hr, rfl⟩
    refine ⟨reesMonomial I 1 ⟨r, by simpa using hr⟩, (reesMonomial I 1 _).2, rfl⟩

/-- **The Rees algebra is generated in degree one.** Over `R`, the Rees algebra `R[It]` is
generated by its degree-one part, a copy of `I`. -/
theorem adjoin_reesGrading_one_eq_top :
    Algebra.adjoin R ((reesGrading I 1 : Submodule R (reesAlgebra I)) :
      Set (reesAlgebra I)) = ⊤ := by
  refine Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective ?_
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val,
    coe_image_reesGrading_one, adjoin_monomial_eq_reesAlgebra]

/-- **The Rees algebra is generated in degree one over its degree-zero part.** The Rees algebra
is generated, as an algebra over its degree-zero part, by its degree-one part. -/
public theorem adjoin_reesGradingZero_reesGrading_one_eq_top :
    Algebra.adjoin (reesGrading I 0)
        ((reesGrading I 1 : Submodule R (reesAlgebra I)) : Set (reesAlgebra I)) = ⊤ := by
  rw [Algebra.eq_top_iff]
  intro x
  have hx : x ∈ Algebra.adjoin R
      ((reesGrading I 1 : Submodule R (reesAlgebra I)) : Set (reesAlgebra I)) :=
    Algebra.eq_top_iff.mp (adjoin_reesGrading_one_eq_top I) x
  induction hx using Algebra.adjoin_induction with
  | mem z hz => exact Algebra.subset_adjoin hz
  | algebraMap r =>
      exact Subalgebra.algebraMap_mem _
        (⟨_, SetLike.algebraMap_mem_graded (reesGrading I) r⟩ : reesGrading I 0)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

end Stacks.Blowup

end
