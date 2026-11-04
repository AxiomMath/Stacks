module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import StacksFrontier.RingTheory.MvPolynomial.LinearSubspaceDimension

/-!
# The determinant cutting out the tuples that span

Let `κ` be a field, let `W` be a `κ`-vector space with a basis indexed by `Fin d`, and let
`φ : κ^ι → W` be a linear map.  A `d`-tuple of vectors of `κ^ι` is a point of `κ^(Fin d × ι)`,
and this file writes down the one polynomial in those `d · #ι` coordinates whose nonvanishing
says that the `d` images under `φ` span `W`: the determinant of the `d × d` matrix whose `j`-th
column is the coordinate vector of `φ(a_j)` in the chosen basis.

Each entry of that matrix is a linear form in the coordinates of the `j`-th vector — the linear
form `Stacks.LinearSubspace.linearForm` of
`StacksFrontier.RingTheory.MvPolynomial.LinearSubspaceDimension`, renamed into the `j`-th block of
variables — so the determinant is a polynomial of degree `d` and its nonvanishing locus is an
open subset of the affine space of tuples.  That `d` vectors of a `d`-dimensional space span
exactly when the determinant is nonzero is `Module.Basis.is_basis_iff_det` together with
`linearIndependent_of_top_le_span_of_card_eq_finrank`, which supplies the linear independence
that `Module.Basis.is_basis_iff_det` also asks for and that spanning forces when the number of
vectors is the dimension.

## Main definitions

* `Stacks.SpanningTuple.spanMatrix`: the `d × d` matrix of linear forms whose `(l, j)` entry is
  the `l`-th coordinate of `φ(a_j)`.
* `Stacks.SpanningTuple.spanDet`: **its determinant**, a polynomial in `κ[Fin d × ι]`.

## Main results

* `Stacks.SpanningTuple.eval_spanDet`: **the determinant evaluated at a tuple `a` is
  `e.det (φ ∘ a)`**, the determinant of the `d` images in the chosen basis.
* `Stacks.SpanningTuple.span_eq_top_iff_eval_spanDet_ne_zero`: **a tuple's images span `W`
  exactly when the determinant does not vanish on it.**
* `Stacks.SpanningTuple.spanDet_ne_zero`: **the determinant is a nonzero polynomial** as soon as
  `φ` is surjective, because a tuple lifting the basis makes the matrix the identity.  This is
  what makes the nonvanishing locus nonempty.
* `Stacks.SpanningTuple.exists_span_eq_top`: the existence of one spanning tuple, which is the
  same statement read backwards.

## Implementation notes

The `j`-th block of variables is reached by `MvPolynomial.rename (Prod.mk j)`, so the entries are
the linear forms of `Stacks.LinearSubspace.linearForm` rather than new sums; the evaluation of a
renamed polynomial is `MvPolynomial.eval_rename_prod_mk`.

A tuple of vectors is a function `Fin d × ι → κ` rather than `Fin d → ι → κ`, so that it is a
point of a single affine space; the two are exchanged by `Function.curry`, which is what appears
in the statements.

The hypothesis is a basis `e : Module.Basis (Fin d) κ W` rather than `Module.finrank κ W = d`:
the two are interchangeable through `Module.finBasisOfFinrankEq`, and a basis is what the
determinant needs anyway.

No `@[stacks]` attribute is attached: this is a step inside the proof of
[Stacks, Tag 0FH5], not the assertion of a tag.

## References

* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u v w

namespace Stacks.SpanningTuple

variable {κ : Type u} [Field κ] {ι : Type v} [Fintype ι] [DecidableEq ι]
  {W : Type w} [AddCommGroup W] [Module κ W] {d : ℕ}

/-- The coordinates of `φ(b)` in a basis are the linear combination, with coefficients `b`, of
the coordinates of the images of the standard basis vectors. -/
theorem repr_apply_eq_sum (e : Module.Basis (Fin d) κ W) (φ : (ι → κ) →ₗ[κ] W) (b : ι → κ)
    (l : Fin d) : e.repr (φ b) l = ∑ i, b i * e.repr (φ (Pi.single i 1)) l := by
  have hb : ∑ i, b i • (Pi.single i 1 : ι → κ) = b := by
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using (Pi.basisFun κ ι).sum_repr b
  conv_lhs => rw [← hb]
  rw [map_sum, map_sum]
  simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.coe_finset_sum,
    Finset.sum_apply]

/-- **The matrix of a `d`-tuple of vectors of `κ^ι` in a basis of `W` indexed by `Fin d`**, with
entries polynomials in the coordinates of the tuple: the `(l, j)` entry is the `l`-th coordinate
of `φ(a_j)`, a linear form in the `j`-th block of variables. -/
def spanMatrix (e : Module.Basis (Fin d) κ W) (φ : (ι → κ) →ₗ[κ] W) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin d × ι) κ) :=
  Matrix.of fun l j =>
    rename (Prod.mk j) (Stacks.LinearSubspace.linearForm fun i => e.repr (φ (Pi.single i 1)) l)

/-- **The determinant whose nonvanishing says that a `d`-tuple of vectors of `κ^ι` has images
spanning `W`**, as a polynomial of degree `d` in the `d · #ι` coordinates of the tuple. -/
def spanDet (e : Module.Basis (Fin d) κ W) (φ : (ι → κ) →ₗ[κ] W) :
    MvPolynomial (Fin d × ι) κ :=
  (spanMatrix e φ).det

/-- An entry of the matrix evaluated at a tuple is the corresponding coordinate of the image of
the corresponding vector. -/
theorem eval_spanMatrix (e : Module.Basis (Fin d) κ W) (φ : (ι → κ) →ₗ[κ] W)
    (a : Fin d × ι → κ) (l j : Fin d) :
    eval a (spanMatrix e φ l j) = e.toMatrix (fun t => φ (Function.curry a t)) l j := by
  rw [spanMatrix, Matrix.of_apply, eval_rename_prod_mk, Stacks.LinearSubspace.linearForm_apply,
    map_sum, Module.Basis.toMatrix_apply, repr_apply_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, eval_C, eval_X, mul_comm]; rfl

/-- **The determinant evaluated at a tuple is the determinant of the `d` images in the chosen
basis.** -/
theorem eval_spanDet (e : Module.Basis (Fin d) κ W) (φ : (ι → κ) →ₗ[κ] W) (a : Fin d × ι → κ) :
    eval a (spanDet e φ) = e.det fun t => φ (Function.curry a t) := by
  rw [spanDet, Module.Basis.det_apply, RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun l j => ?_)
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact eval_spanMatrix e φ a l j

/-- **A `d`-tuple of vectors of `κ^ι` has images spanning `W` exactly when the determinant does
not vanish on it.**

The determinant of `Module.Basis.is_basis_iff_det` tests being a basis, that is spanning
*together with* linear independence; here the number of vectors is the dimension of `W`, so
spanning forces linear independence by
`linearIndependent_of_top_le_span_of_card_eq_finrank`. -/
theorem span_eq_top_iff_eval_spanDet_ne_zero (e : Module.Basis (Fin d) κ W)
    (φ : (ι → κ) →ₗ[κ] W) (a : Fin d × ι → κ) :
    Submodule.span κ (Set.range fun t => φ (Function.curry a t)) = ⊤ ↔
      eval a (spanDet e φ) ≠ 0 := by
  rw [eval_spanDet, ← isUnit_iff_ne_zero]
  refine ⟨fun hspan => (e.is_basis_iff_det).1 ⟨?_, hspan⟩,
    fun hdet => ((e.is_basis_iff_det).2 hdet).2⟩
  refine linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge ?_
  rw [Module.finrank_eq_card_basis e, Fintype.card_fin]

/-- **The determinant is a nonzero polynomial** when `φ` is surjective: a tuple whose images are
the basis vectors makes the matrix the identity. -/
theorem spanDet_ne_zero (e : Module.Basis (Fin d) κ W) {φ : (ι → κ) →ₗ[κ] W}
    (hφ : Function.Surjective φ) : spanDet e φ ≠ 0 := by
  choose c hc using fun t : Fin d => hφ (e t)
  intro h0
  have h := eval_spanDet e φ (Function.uncurry c)
  rw [h0, map_zero, Function.curry_uncurry, funext hc, Module.Basis.det_self] at h
  exact one_ne_zero h.symm

omit [Fintype ι] [DecidableEq ι] in
/-- **A surjective `φ` admits a `d`-tuple whose images span `W`**: the nonvanishing locus of the
determinant is nonempty. -/
theorem exists_span_eq_top (e : Module.Basis (Fin d) κ W) {φ : (ι → κ) →ₗ[κ] W}
    (hφ : Function.Surjective φ) :
    ∃ a : Fin d × ι → κ, Submodule.span κ (Set.range fun t => φ (Function.curry a t)) = ⊤ := by
  choose c hc using fun t : Fin d => hφ (e t)
  refine ⟨Function.uncurry c, ?_⟩
  rw [Function.curry_uncurry, funext hc]
  exact e.span_eq

end Stacks.SpanningTuple

end
