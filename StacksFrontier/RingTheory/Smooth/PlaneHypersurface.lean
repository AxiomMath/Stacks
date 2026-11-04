module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksFrontier.RingTheory.MvPolynomial.HypersurfaceDimension
public import StacksFrontier.RingTheory.Smooth.JacobianCriterion

/-!
# Smoothness of an affine plane curve is the nonvanishing of a partial derivative

Let `k` be a field and let `f ∈ k[x₀, x₁]` be nonzero and not a unit.  The quotient
`k[x₀, x₁] ⧸ (f)` is presented over `k` by two variables and the single relation `f`, and the
Jacobian minors of that presentation are the two partial derivatives `∂f/∂x₀`, `∂f/∂x₁`.  The
Jacobian criterion [Stacks, Tag 00TE] therefore says that `k[x₀, x₁] ⧸ (f)` is smooth over `k` at
a prime exactly when one of the two derivatives avoids it.

The dimension hypothesis of the criterion — every nonempty fibre of
`Spec(k[x₀, x₁] ⧸ (f)) → Spec(k)` has dimension `2 - 1` — is discharged here once and for all.
There is only one prime of `k`, and its fibre is `k[x₀, x₁] ⧸ (f)` itself, whose Krull dimension
is one by `Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton`, with no hypothesis that the
quotient be reduced or a domain.

## Main definitions

* `Stacks.Curves.planeHypersurfacePresentation`: the presentation of `k[x₀, x₁] ⧸ (f)` by two
  variables and one relation.

## Main results

* `Stacks.Curves.planeHypersurfacePresentation_jacobian`: the Jacobian of that presentation,
  equipped with the injection sending the relation to the variable `e 0`, is the class of
  `∂f/∂x_{e 0}`.
* `Stacks.Curves.isSmoothAt_iff_exists_pderiv_notMem`: **the criterion** — `k[x₀, x₁] ⧸ (f)` is
  smooth over `k` at a prime `Q` exactly when some `∂f/∂xᵢ` lies outside the preimage of `Q`.

## Implementation notes

The presentation is Mathlib's `Algebra.Presentation.naive` for the family `fun _ : Fin 1 => f`,
transported along `Ideal.quotientEquivAlgOfEq` from the quotient by `Ideal.span (Set.range _)` to
the quotient by `Ideal.span {f}`, which is the ideal every consumer writes.  Transport leaves the
relation and the generators alone, so the Jacobian is computed directly from
`Algebra.PreSubmersivePresentation.jacobiMatrix_apply` and the determinant of a `1 × 1` matrix.

A subset of the variables of cardinality one is an injection `Fin 1 ↪ Fin 2`, so the existential
over subsets in [Stacks, Tag 00TE] becomes the existential over `i : Fin 2` here.

## References

* [Stacks Project, Tag 00TE](https://stacks.math.columbia.edu/tag/00TE)
* [Stacks Project, Tag 00TB](https://stacks.math.columbia.edu/tag/00TB)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

/-- **The one-relation presentation of the affine plane curve `k[x₀, x₁] ⧸ (f)`**: two variables
and the single relation `f`. -/
def planeHypersurfacePresentation (f : MvPolynomial (Fin 2) k) :
    Algebra.Presentation k (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) (Fin 2) (Fin 1) :=
  (Algebra.Presentation.naive (v := fun _ : Fin 1 => f)).ofAlgEquiv
    (Ideal.quotientEquivAlgOfEq k (by rw [Set.range_const]))

/-- The only relation of `Stacks.Curves.planeHypersurfacePresentation` is `f`. -/
theorem planeHypersurfacePresentation_relation (f : MvPolynomial (Fin 2) k) (i : Fin 1) :
    (planeHypersurfacePresentation f).relation i = f := by
  simp [planeHypersurfacePresentation, Algebra.Presentation.ofAlgEquiv_relation]

/-- The structure map of `Stacks.Curves.planeHypersurfacePresentation` is the quotient map. -/
theorem planeHypersurfacePresentation_algebraMap (f x : MvPolynomial (Fin 2) k) :
    algebraMap (planeHypersurfacePresentation f).Ring
        (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) x = Ideal.Quotient.mk _ x := by
  have hval : ∀ i : Fin 2,
      (planeHypersurfacePresentation f).val i = Ideal.Quotient.mk (Ideal.span {f}) (X i) := by
    intro i
    simp [planeHypersurfacePresentation, Algebra.Presentation.ofAlgEquiv,
      Algebra.Generators.ofAlgEquiv_val, Algebra.Generators.naive_val]
  rw [Algebra.Generators.algebraMap_apply]
  have h : (MvPolynomial.aeval (planeHypersurfacePresentation f).val :
        MvPolynomial (Fin 2) k →ₐ[k] _) = Ideal.Quotient.mkₐ k (Ideal.span {f}) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [hval]
  exact DFunLike.congr_fun h x

/-- **The Jacobian minor of the plane hypersurface presentation is a partial derivative.**  A
one-element subset of the two variables is an injection `e : Fin 1 ↪ Fin 2`, and the
corresponding `1 × 1` minor is the class of `∂f/∂x_{e 0}`. -/
theorem planeHypersurfacePresentation_jacobian (f : MvPolynomial (Fin 2) k) (e : Fin 1 ↪ Fin 2) :
    (Algebra.PreSubmersivePresentation.mk (planeHypersurfacePresentation f) e e.injective).jacobian
      = Ideal.Quotient.mk (Ideal.span {f}) (pderiv (e 0) f) := by
  classical
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply,
    show ((Algebra.PreSubmersivePresentation.mk (planeHypersurfacePresentation f) e
      e.injective).map default) = e 0 from rfl,
    show ((Algebra.PreSubmersivePresentation.mk (planeHypersurfacePresentation f) e
      e.injective).relation default) = f from planeHypersurfacePresentation_relation f default]
  exact planeHypersurfacePresentation_algebraMap f _

/-- **The fibre dimension hypothesis of the Jacobian criterion for a plane curve.**  The base is a
field, so the only prime is `⊥` and the fibre over it is `k[x₀, x₁] ⧸ (f)`, of Krull dimension
one. -/
theorem planeHypersurfacePresentation_fiber_dim (f : MvPolynomial (Fin 2) k) (hf0 : f ≠ 0)
    (hfu : ¬ IsUnit f) (p : Ideal k) [p.IsPrime] :
    Nontrivial (p.Fiber (MvPolynomial (Fin 2) k ⧸ Ideal.span {f})) →
      ringKrullDim (p.Fiber (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}))
        + (Nat.card (Fin 1) : WithBot ℕ∞) = (Nat.card (Fin 2) : WithBot ℕ∞) := by
  intro _
  have hp : p = ⊥ := (Ideal.eq_bot_or_top p).resolve_right (Ideal.IsPrime.ne_top ‹_›)
  subst hp
  have ebij : Function.Bijective (algebraMap k ((⊥ : Ideal k).ResidueField)) :=
    ⟨(algebraMap k _).injective, Ideal.algebraMap_residueField_surjective ⊥⟩
  let e : k ≃ₐ[k] (⊥ : Ideal k).ResidueField := AlgEquiv.ofBijective (Algebra.ofId k _) ebij
  let E : (⊥ : Ideal k).Fiber (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) ≃ₐ[k]
      (MvPolynomial (Fin 2) k ⧸ Ideal.span {f}) :=
    (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid k _)
  rw [ringKrullDim_eq_of_ringEquiv E.toRingEquiv,
    Stacks.MvPolynomial.ringKrullDim_quotient_span_singleton k (Fin 2) (n := 1) (by simp) f hf0
      hfu]
  simp
  rfl

/-- **Smoothness of an affine plane curve at a prime is the nonvanishing of a partial
derivative.**  For `f ∈ k[x₀, x₁]` nonzero and not a unit, `k[x₀, x₁] ⧸ (f)` is smooth over `k`
at a prime `Q` exactly when one of `∂f/∂x₀`, `∂f/∂x₁` lies outside the preimage of `Q` in
`k[x₀, x₁]`.  This is [Stacks, Tag 00TE] for the presentation
`Stacks.Curves.planeHypersurfacePresentation`. -/
theorem isSmoothAt_iff_exists_pderiv_notMem {f : MvPolynomial (Fin 2) k} (hf0 : f ≠ 0)
    (hfu : ¬ IsUnit f) (Q : Ideal (MvPolynomial (Fin 2) k ⧸ Ideal.span {f})) [Q.IsPrime] :
    Algebra.IsSmoothAt k Q ↔
      ∃ i : Fin 2, pderiv i f ∉ Q.comap (Ideal.Quotient.mk (Ideal.span {f})) := by
  rw [Algebra.Presentation.isSmoothAt_iff_exists_jacobian_notMem
    (planeHypersurfacePresentation f)
    (fun p _ h => planeHypersurfacePresentation_fiber_dim f hf0 hfu p h) Q]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e 0, by rwa [Ideal.mem_comap, ← planeHypersurfacePresentation_jacobian f e]⟩
  · rintro ⟨i, hi⟩
    exact ⟨⟨fun _ => i, fun a b _ => Subsingleton.elim a b⟩, by
      rwa [planeHypersurfacePresentation_jacobian]⟩


end Stacks.Curves

end
