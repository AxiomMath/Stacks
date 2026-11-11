module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.MvPolynomial.HypersurfaceDimension
public import StacksFrontier.RingTheory.Smooth.JacobianCriterion

/-!
# The Jacobian criterion for an affine hypersurface

Let `k` be a field and let `f ∈ k[x₁, …, xₙ]`. The quotient `k[x₁, …, xₙ] ⧸ (f)` is presented
over `k` by `n` variables and the single relation `f`, and the Jacobian minors of that
presentation are the partial derivatives `∂f/∂xᵢ`. The Jacobian criterion [Stacks, Tag 00TE]
therefore makes `k[x₁, …, xₙ] ⧸ (f)` smooth over `k` at every prime avoiding one of the partial
derivatives, and smooth over `k` as soon as `f` and its partial derivatives generate the unit
ideal of `k[x₁, …, xₙ]`.

This is the `n`-variable form of `StacksFrontier/RingTheory/Smooth/PlaneHypersurface.lean`, which
treats `n = 2`.

## Main definitions

* `Stacks.AffineHypersurface.presentation`: the presentation of `k[x₁, …, xₙ] ⧸ (f)` by `n`
  variables and one relation.

## Main results

* `Stacks.AffineHypersurface.presentation_jacobian`: the Jacobian minor of that presentation
  attached to `e : Fin 1 ↪ Fin n` is the class of `∂f/∂x_{e 0}`.
* `Stacks.AffineHypersurface.isSmoothAt_of_pderiv_notMem`: `k[x] ⧸ (f)` is smooth over `k` at a
  prime avoiding some `∂f/∂xᵢ`.
* `Stacks.AffineHypersurface.smooth_quotient_of_span_eq_top`: **the Jacobian criterion** — if
  `f, ∂f/∂x₁, …, ∂f/∂xₙ` generate the unit ideal, then `k[x] ⧸ (f)` is smooth over `k`.

## Implementation notes

The fibre dimension hypothesis of the Jacobian criterion
`Algebra.Presentation.isSmoothAt_iff_exists_jacobian_notMem` is discharged by
`Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton_add_one`: the only prime of `k` is `⊥`,
its fibre is `k[x] ⧸ (f)` itself, and a nontrivial fibre forces `f` to be a nonunit. Global
smoothness is read off from the smooth locus (`Algebra.smoothLocus_eq_univ_iff`), the quotient
being finitely presented.

## References

* [Stacks Project, Tag 00TE](https://stacks.math.columbia.edu/tag/00TE)
* [Stacks Project, Tag 00TB](https://stacks.math.columbia.edu/tag/00TB)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace Stacks.AffineHypersurface

variable {k : Type u} [Field k] {n : ℕ}

/-- **The one-relation presentation of the affine hypersurface `k[x₁, …, xₙ] ⧸ (f)`**: `n`
variables and the single relation `f`. -/
def presentation (f : MvPolynomial (Fin n) k) :
    Algebra.Presentation k (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) (Fin n) (Fin 1) :=
  (Algebra.Presentation.naive (v := fun _ : Fin 1 => f)).ofAlgEquiv
    (Ideal.quotientEquivAlgOfEq k (by rw [Set.range_const]))

/-- The only relation of `Stacks.AffineHypersurface.presentation` is `f`. -/
theorem presentation_relation (f : MvPolynomial (Fin n) k) (i : Fin 1) :
    (presentation f).relation i = f := by
  simp [presentation, Algebra.Presentation.ofAlgEquiv_relation]

/-- The structure map of `Stacks.AffineHypersurface.presentation` is the quotient map. -/
theorem presentation_algebraMap (f x : MvPolynomial (Fin n) k) :
    algebraMap (presentation f).Ring (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) x =
      Ideal.Quotient.mk _ x := by
  have hval : ∀ i : Fin n,
      (presentation f).val i = Ideal.Quotient.mk (Ideal.span {f}) (X i) := by
    intro i
    simp [presentation, Algebra.Presentation.ofAlgEquiv,
      Algebra.Generators.ofAlgEquiv_val, Algebra.Generators.naive_val]
  rw [Algebra.Generators.algebraMap_apply]
  have h : (MvPolynomial.aeval (presentation f).val :
        MvPolynomial (Fin n) k →ₐ[k] _) = Ideal.Quotient.mkₐ k (Ideal.span {f}) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hval]
  exact DFunLike.congr_fun h x

/-- **The Jacobian minor of the hypersurface presentation is a partial derivative.** A
one-element subset of the `n` variables is an injection `e : Fin 1 ↪ Fin n`, and the
corresponding `1 × 1` minor is the class of `∂f/∂x_{e 0}`. -/
theorem presentation_jacobian (f : MvPolynomial (Fin n) k) (e : Fin 1 ↪ Fin n) :
    (Algebra.PreSubmersivePresentation.mk (presentation f) e e.injective).jacobian
      = Ideal.Quotient.mk (Ideal.span {f}) (pderiv (e 0) f) := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
    show ((Algebra.PreSubmersivePresentation.mk (presentation f) e
      e.injective).map default) = e 0 from rfl,
    show ((Algebra.PreSubmersivePresentation.mk (presentation f) e
      e.injective).relation default) = f from presentation_relation f default]
  exact presentation_algebraMap f _

/-- **The fibre dimension hypothesis of the Jacobian criterion for a hypersurface.** The base is
a field, so the only prime is `⊥` and the fibre over it is `k[x] ⧸ (f)`; when it is nontrivial,
`f` is a nonunit, and the quotient has dimension `n - 1`. -/
theorem presentation_fiber_dim (f : MvPolynomial (Fin n) k) (hf0 : f ≠ 0)
    (p : Ideal k) [p.IsPrime] :
    Nontrivial (p.Fiber (MvPolynomial (Fin n) k ⧸ Ideal.span {f})) →
      ringKrullDim (p.Fiber (MvPolynomial (Fin n) k ⧸ Ideal.span {f}))
        + (Nat.card (Fin 1) : WithBot ℕ∞) = (Nat.card (Fin n) : WithBot ℕ∞) := by
  intro hnt
  have hp : p = ⊥ := (Ideal.eq_bot_or_top p).resolve_right (Ideal.IsPrime.ne_top ‹_›)
  subst hp
  have ebij : Function.Bijective (algebraMap k ((⊥ : Ideal k).ResidueField)) :=
    ⟨(algebraMap k _).injective, Ideal.algebraMap_residueField_surjective ⊥⟩
  let e : k ≃ₐ[k] (⊥ : Ideal k).ResidueField := AlgEquiv.ofBijective (Algebra.ofId k _) ebij
  let E : (⊥ : Ideal k).Fiber (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) ≃ₐ[k]
      (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) :=
    (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid k _)
  have hnt' : Nontrivial (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) :=
    E.toRingEquiv.injective.nontrivial
  have hfu : ¬ IsUnit f := fun hu =>
    (Ideal.Quotient.nontrivial_iff.mp hnt') (Ideal.span_singleton_eq_top.mpr hu)
  rw [ringKrullDim_eq_of_ringEquiv E.toRingEquiv,
    ← Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton_add_one k (Fin n) f hf0 hfu]
  simp

/-- **An affine hypersurface is smooth at a prime avoiding a partial derivative.** For
`f ∈ k[x₁, …, xₙ]` nonzero, `k[x] ⧸ (f)` is smooth over `k` at a prime `Q` as soon as some
`∂f/∂xᵢ` lies outside the preimage of `Q` in `k[x]`. -/
theorem isSmoothAt_of_pderiv_notMem {f : MvPolynomial (Fin n) k} (hf0 : f ≠ 0)
    (Q : Ideal (MvPolynomial (Fin n) k ⧸ Ideal.span {f})) [Q.IsPrime] (i : Fin n)
    (hi : pderiv i f ∉ Q.comap (Ideal.Quotient.mk (Ideal.span {f}))) :
    Algebra.IsSmoothAt k Q :=
  (Algebra.Presentation.isSmoothAt_iff_exists_jacobian_notMem (presentation f)
    (fun p _ h => presentation_fiber_dim f hf0 p h) Q).2
    ⟨⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩, by rwa [presentation_jacobian]⟩

/-- **The Jacobian criterion for an affine hypersurface.** If `f` and its partial derivatives
`∂f/∂x₁, …, ∂f/∂xₙ` generate the unit ideal of `k[x₁, …, xₙ]`, then `k[x₁, …, xₙ] ⧸ (f)` is
smooth over `k`. -/
theorem smooth_quotient_of_span_eq_top {f : MvPolynomial (Fin n) k}
    (h : Ideal.span (insert f (Set.range fun a => pderiv a f)) = ⊤) :
    Algebra.Smooth k (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) := by
  have hfp : Algebra.FinitePresentation k (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton f)
  have hf0 : f ≠ 0 := by
    rintro rfl
    have hle : Ideal.span (insert (0 : MvPolynomial (Fin n) k)
        (Set.range fun a => pderiv a (0 : MvPolynomial (Fin n) k))) ≤ ⊥ :=
      Ideal.span_le.2 (by rintro _ (rfl | ⟨a, rfl⟩) <;> simp)
    rw [h] at hle
    exact top_ne_bot (eq_bot_iff.2 hle)
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun q => ?_), hfp⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin n,
      pderiv i f ∉ q.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {f})) := by
    by_contra hall
    push Not at hall
    have hle : Ideal.span (insert f (Set.range fun a => pderiv a f)) ≤
        q.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {f})) := by
      refine Ideal.span_le.2 ?_
      rintro x (hx | ⟨a, rfl⟩)
      · rw [hx]
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
      · exact hall a
    rw [h] at hle
    exact (inferInstance : (q.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {f}))).IsPrime).ne_top
      (top_le_iff.mp hle)
  exact isSmoothAt_of_pderiv_notMem hf0 q.asIdeal i hi

end Stacks.AffineHypersurface

end
