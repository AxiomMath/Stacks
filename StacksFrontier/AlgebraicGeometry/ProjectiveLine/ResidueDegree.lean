module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import StacksFrontier.AlgebraicGeometry.ProjectiveLine.Complement

/-!
# The residue degree of a closed point of the projective line

The closed point `V₊(f)` of `ℙ¹_k` cut out by a homogeneous irreducible form `f` of degree `d`
lies in the standard open `D₊(T₁)` exactly when `T₁` does not divide `f`. Dehomogenization carries
`f` to an irreducible polynomial `F ∈ k[X]` of the same degree `d`, so `(F)` is a maximal ideal of
the chart ring, its residue field is `k[X] ⧸ (F)`, and that has degree `d` over `k`. This integer
`d` is the one appearing in [Stacks, Tag 0CDP].

## Main definitions

* `Stacks.ProjectiveLine.residueFieldAlgEquivQuotient`: the residue field of a maximal ideal of a
  `k`-algebra is the quotient by it.

## Main results

* `Stacks.ProjectiveLine.pointOfForm_mem_basicOpen_X_one_iff`: `V₊(f)` lies in the standard open
  `D₊(T₁)` exactly when `T₁` does not divide `f`.
* `Stacks.ProjectiveLine.isMaximal_span_dehomogenize`: the dehomogenization of `f` generates a
  maximal ideal of `k[X]`.
* `Stacks.ProjectiveLine.finrank_quotient_span_dehomogenize` and
  `Stacks.ProjectiveLine.finrank_residueField_span_dehomogenize`: **the residue degree is
  `deg f`**.

## References

* [Stacks Project, Tag 0CDP](https://stacks.math.columbia.edu/tag/0CDP)
-/

@[expose] public section

open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveLine

universe u

variable {k : Type u} [Field k] {d : ℕ} {f : MvPolynomial (Fin 2) k}

/-- **The closed point `V₊(f)` lies in the standard chart `D₊(T₁)`** exactly when `T₁` does not
divide `f`; the remaining case is `f` associated to `T₁`, the point at infinity. -/
theorem pointOfForm_mem_basicOpen_X_one_iff (hf : f.IsHomogeneous d) (hirr : Irreducible f) :
    pointOfForm hf hirr ∈ Proj.basicOpen (grading k) (MvPolynomial.X 1) ↔
      ¬ MvPolynomial.X (1 : Fin 2) ∣ f :=
  (Proj.mem_basicOpen (grading k) (MvPolynomial.X 1) (pointOfForm hf hirr)).trans
    (not_congr ((mem_pointOfForm_iff hf hirr).trans (dvd_X_one_iff_X_one_dvd hf hirr)))

/-- The dehomogenization of a homogeneous irreducible form not divisible by `T₁` generates a
maximal ideal of the chart ring `k[X]`. -/
theorem isMaximal_span_dehomogenize (hf : f.IsHomogeneous d) (hirr : Irreducible f)
    (h : ¬ MvPolynomial.X (1 : Fin 2) ∣ f) :
    (Ideal.span {dehomogenize k f}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (irreducible_dehomogenize hf hirr h)

/-- **The residue field of a maximal ideal is the quotient by it**, as an algebra over the ground
ring. -/
noncomputable def residueFieldAlgEquivQuotient (K : Type*) [CommRing K] (R : Type*) [CommRing R]
    [Algebra K R] (I : Ideal R) [I.IsMaximal] : (R ⧸ I) ≃ₐ[K] I.ResidueField :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom K (R ⧸ I) I.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField I)

/-- **The residue degree at a closed point of `ℙ¹_k`, read in the standard chart**: the quotient
of the chart ring by the maximal ideal cut out by `f` has degree `deg f` over `k`. -/
theorem finrank_quotient_span_dehomogenize (hf : f.IsHomogeneous d)
    (h : ¬ MvPolynomial.X (1 : Fin 2) ∣ f) :
    Module.finrank k (Polynomial k ⧸ Ideal.span {dehomogenize k f}) = d := by
  rw [finrank_quotient_span_eq_natDegree, natDegree_dehomogenize_eq_of_not_X_one_dvd hf h]

/-- **`[κ(t) : k] = deg f`, read in the standard chart**: the residue field of the maximal ideal
cut out by `f` in the chart ring has degree `deg f` over `k`. This is the integer `d` of
[Stacks, Tag 0CDP]. -/
theorem finrank_residueField_span_dehomogenize (hf : f.IsHomogeneous d) (hirr : Irreducible f)
    (h : ¬ MvPolynomial.X (1 : Fin 2) ∣ f) [(Ideal.span {dehomogenize k f}).IsPrime] :
    Module.finrank k (Ideal.span {dehomogenize k f}).ResidueField = d := by
  have := isMaximal_span_dehomogenize hf hirr h
  have he : Module.finrank k (Polynomial k ⧸ Ideal.span {dehomogenize k f}) =
      Module.finrank k (Ideal.span {dehomogenize k f}).ResidueField :=
    (residueFieldAlgEquivQuotient k (Polynomial k)
      (Ideal.span {dehomogenize k f})).toLinearEquiv.finrank_eq
  rw [← he]
  exact finrank_quotient_span_dehomogenize hf h

end Stacks.ProjectiveLine

end
