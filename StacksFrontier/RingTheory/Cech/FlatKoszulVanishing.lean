module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.RingTheory.Cech.KoszulResolution
public import StacksFrontier.RingTheory.Cech.Tensor

/-!
# The extended alternating Čech complex of a Koszul-regular sequence on a flat module

Let `R` be a commutative ring, let `f₁, …, f_r ∈ R` be a Koszul-regular sequence and let `M` be
a flat `R`-module.  Then the extended alternating Čech complex

`M → ⨁_{i₀} M_{f_{i₀}} → ⨁_{i₀ < i₁} M_{f_{i₀}f_{i₁}} → ⋯ → M_{f₁⋯f_r}`

has cohomology only in degree `r`.

This is the algebra statement to which [Stacks, Tag 0G7P] reduces its geometric conclusion
`ℋ ^i_Z(ℱ) = 0` for `i ≠ c`, and the proof is the one the source gives for it: the vanishing
holds for the coefficient module `R` by [Stacks, Tag 0G6L], and the complex for `M` is obtained
from the complex for `R` by tensoring with `M`, degreewise and compatibly with the differentials,
by [Stacks, Tag 0G6H]; since `M` is flat, tensoring with it preserves exactness.

## Main results

* `Cech.cechComplex_homology_isZero_of_isKoszulRegular_of_flat`: the cohomology of
  `Cech.cechComplex f M` vanishes in every degree other than the length of `f`.
* `Cech.extend_homology_isZero_of_isKoszulRegular_of_flat`: the same for the integer-indexed
  extension of the complex, which is the form in which the derived category reads it.
* `Cech.isZero_homology_succ_iff` and `Cech.isZero_homology_zero_iff`: the vanishing of the
  cohomology of `Cech.cechComplex` in a given degree, read as exactness of the pair of linear
  maps meeting there.

## Implementation notes

**Why the transport is elementwise.** The degreewise identification of [Stacks, Tag 0G6H] is
`Cech.ExtendedCech.termTensorEquiv f M p : Čᵖ(M) ≃ₗ[R] M ⊗_R Čᵖ(R)`, and the two sides live in
different module universes: `M` is a `Type v` and `R` is a `Type u`, so `Cech.cechComplex f M`
is a complex in `ModuleCat.{max u v} R` while `Cech.cechComplex f R` is one in
`ModuleCat.{u} R`.  There is therefore no single endofunctor `M ⊗ -` relating the two complexes,
and the exactness is transported with `Module.Flat.lTensor_exact` and
`Function.Exact.of_ladder_linearEquiv_of_exact`, both of which are universe-polymorphic in the
modules involved, rather than with `CategoryTheory.ShortComplex.mapHomologyIso`.

**The two `IsZero`-to-`Function.Exact` bridges.** `Cech.cechComplex` is built with
`CochainComplex.of`, whose differential is a `dif` on the degrees; `(cechComplex f M).d p (p+1)`
is therefore equal to `Cech.cechD f M p` only propositionally, by `CochainComplex.of_d`, and the
objects `(cechComplex f M).X p` are reducible to `ModuleCat.of R (Cech.cechTerm f M p)` only at
default transparency.  The bridges consequently rewrite with `Cech.hom_cechComplex_d` inside a
hypothesis or goal that is already spelled with `HomologicalComplex.d` — never inside one
spelled with `HomologicalComplex.sc'`, where the rewrite's motive fails to typecheck at the
transparency `rw` re-checks at.

In degree `0` the short complex of the cochain complex has the zero map on its left, so the
statement there is exactness of `0 → Č⁰ → Č¹`, i.e. injectivity of the first differential; the
`Function.Exact` form is kept so that `Module.Flat.lTensor_exact` applies verbatim, using
`LinearMap.lTensor_zero`.

## References

* [Stacks Project, Tag 0G6H](https://stacks.math.columbia.edu/tag/0G6H)
* [Stacks Project, Tag 0G6L](https://stacks.math.columbia.edu/tag/0G6L)
* [Stacks Project, Tag 0G7P](https://stacks.math.columbia.edu/tag/0G7P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace Cech

open ExtendedCech

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
  (M : Type v) [AddCommGroup M] [Module R M]

/-! ### Reading the cohomology of `Cech.cechComplex` as exactness of linear maps -/

/-- The differential of `Cech.cechComplex` from degree `p` to degree `p + 1` is the Čech
differential `Cech.cechD`, read on underlying linear maps. -/
theorem hom_cechComplex_d (p : ℕ) : ((cechComplex f M).d p (p + 1)).hom = cechD f M p :=
  congrArg ModuleCat.Hom.hom
    (show (cechComplex f M).d p (p + 1) = ModuleCat.ofHom (cechD f M p) from by
      simp [cechComplex])

/-- `Cech.hom_cechComplex_d` in degree `0`, with the target degree written as the numeral `1`. -/
theorem hom_cechComplex_d_zero : ((cechComplex f M).d 0 1).hom = cechD f M 0 :=
  hom_cechComplex_d f M 0

/-- Vanishing of the cohomology of `Cech.cechComplex` in degree `j` is exactness of the pair of
linear maps underlying the differentials meeting there. -/
private theorem isZero_homology_iff_exact_hom (i j k : ℕ)
    (hi : (ComplexShape.up ℕ).prev j = i) (hk : (ComplexShape.up ℕ).next j = k) :
    IsZero ((cechComplex f M).homology j) ↔
      Function.Exact ((cechComplex f M).d i j).hom ((cechComplex f M).d j k).hom :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).symm.trans
    ((HomologicalComplex.exactAt_iff' _ i j k (by simpa using hi) (by simpa using hk)).trans
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _))

/-- The extended alternating Čech complex has vanishing cohomology in degree `p + 1` exactly
when the two Čech differentials meeting in that degree are an exact pair of linear maps. -/
theorem isZero_homology_succ_iff (p : ℕ) :
    IsZero ((cechComplex f M).homology (p + 1)) ↔
      Function.Exact (cechD f M p) (cechD f M (p + 1)) := by
  rw [isZero_homology_iff_exact_hom f M p (p + 1) (p + 2) (by simp) (by simp),
    hom_cechComplex_d, hom_cechComplex_d]
  exact Iff.rfl

/-- The extended alternating Čech complex has vanishing cohomology in degree `0` exactly when
its first differential is injective, written as exactness of the pair `0`, `Cech.cechD f M 0`. -/
theorem isZero_homology_zero_iff :
    IsZero ((cechComplex f M).homology 0) ↔
      Function.Exact (0 : cechTerm f M 0 →ₗ[R] cechTerm f M 0) (cechD f M 0) := by
  have hzero : ((cechComplex f M).d 0 0).hom = 0 := by
    rw [HomologicalComplex.shape _ 0 0 (by simp)]
    rfl
  rw [isZero_homology_iff_exact_hom f M 0 0 1 (by simp) (by simp), hzero, hom_cechComplex_d_zero]
  exact Iff.rfl

/-- The Čech differentials for `M` and `R` correspond under the identifications of Stacks 0G6H. -/
private theorem cechD_comp_termTensorEquiv_symm (q : ℕ) :
    cechD f M q ∘ₗ (termTensorEquiv f M q).symm =
      (termTensorEquiv f M (q + 1)).symm ∘ₗ LinearMap.lTensor M (cechD f R q) := by
  refine LinearMap.ext fun y => ?_
  apply (termTensorEquiv f M (q + 1)).injective
  simpa using LinearMap.congr_fun (termTensorEquiv_comm_d f M q) ((termTensorEquiv f M q).symm y)

/-! ### Flat coefficients -/

variable [Module.Flat R M]

/-- **Stacks Project, Tag 0G6H and flatness.**  An exact pair of Čech differentials of the
coefficient module `R` stays exact after passing to a flat module `M`: the degreewise
identification `Čᵖ(M) ≅ M ⊗_R Čᵖ(R)` of Stacks 0G6H carries the pair to `M ⊗_R -` of the pair
over `R`, and tensoring with a flat module preserves exactness. -/
theorem exact_cechD_of_flat (p : ℕ)
    (h : Function.Exact (cechD f R p) (cechD f R (p + 1))) :
    Function.Exact (cechD f M p) (cechD f M (p + 1)) := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := (termTensorEquiv f M p).symm) (e₂ := (termTensorEquiv f M (p + 1)).symm)
    (e₃ := (termTensorEquiv f M (p + 2)).symm) (cechD_comp_termTensorEquiv_symm f M p)
    (cechD_comp_termTensorEquiv_symm f M (p + 1)) (Module.Flat.lTensor_exact M h)

/-- `Cech.exact_cechD_of_flat` in degree `0`: injectivity of the first Čech differential passes
from the coefficient module `R` to a flat module `M`. -/
theorem exact_zero_cechD_of_flat
    (h : Function.Exact (0 : cechTerm f R 0 →ₗ[R] cechTerm f R 0) (cechD f R 0)) :
    Function.Exact (0 : cechTerm f M 0 →ₗ[R] cechTerm f M 0) (cechD f M 0) := by
  have hT := Module.Flat.lTensor_exact M h
  rw [LinearMap.lTensor_zero] at hT
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := (termTensorEquiv f M 0).symm) (e₂ := (termTensorEquiv f M 0).symm)
    (e₃ := (termTensorEquiv f M 1).symm) (by simp) (cechD_comp_termTensorEquiv_symm f M 0) hT

/-- **Stacks 0G6L for a flat coefficient module**, the algebra statement to which the proof of
[Stacks, Tag 0G7P] reduces.  Given a ring `R`, a Koszul-regular sequence `f₁, …, f_r ∈ R` and a
flat `R`-module `M`, the extended alternating Čech complex

`M → ⨁_{i₀} M_{f_{i₀}} → ⋯ → M_{f₁⋯f_r}`

has cohomology only in degree `r`.

Stacks 0G6L is the case `M = R`; the complex for `M` is `M ⊗_R` the complex for `R` by
Stacks 0G6H, and flatness of `M` turns the vanishing for `R` into the vanishing for `M`. -/
theorem cechComplex_homology_isZero_of_isKoszulRegular_of_flat
    (hf : Koszul.IsKoszulRegular f) (p : ℕ) (hp : p ≠ r) :
    IsZero ((cechComplex f M).homology p) := by
  match p with
  | 0 =>
    exact (isZero_homology_zero_iff f M).2 (exact_zero_cechD_of_flat f M
      ((isZero_homology_zero_iff f R).1
        (cechComplex_homology_isZero_of_isKoszulRegular f hf 0 hp)))
  | (q + 1) =>
    exact (isZero_homology_succ_iff f M q).2 (exact_cechD_of_flat f M q
      ((isZero_homology_succ_iff f R q).1
        (cechComplex_homology_isZero_of_isKoszulRegular f hf (q + 1) hp)))

/-- `Cech.cechComplex_homology_isZero_of_isKoszulRegular_of_flat` for the integer-indexed
extension of the complex along `ComplexShape.embeddingUpNat`, which is the shape in which the
complex is passed to the derived category.  In a negative degree the extension vanishes, and in
a degree coming from `ℕ` the cohomology is transported by
`HomologicalComplex.extendHomologyIso`. -/
theorem extend_homology_isZero_of_isKoszulRegular_of_flat
    (hf : Koszul.IsKoszulRegular f) (q : ℤ) (hq : q ≠ (r : ℤ)) :
    IsZero (((cechComplex f M).extend ComplexShape.embeddingUpNat).homology q) := by
  set K := (cechComplex f M).extend ComplexShape.embeddingUpNat with hK
  by_cases hq0 : 0 ≤ q
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by simp [hq0]⟩
    refine IsZero.of_iso ?_ (HomologicalComplex.extendHomologyIso (cechComplex f M)
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) (by simp))
    exact cechComplex_homology_isZero_of_isKoszulRegular_of_flat f M hf n
      (by exact_mod_cast hq)
  · have hzX : IsZero (K.X q) := by
      rw [hK]
      refine HomologicalComplex.isZero_extend_X _ _ _ fun n hn => ?_
      rw [ComplexShape.embeddingUpNat_f] at hn
      omega
    exact IsZero.of_epi (K.homologyπ q) (IsZero.of_mono (K.iCycles q) hzX)

end Cech

end
