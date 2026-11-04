module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.StandardModel
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FunctionFieldEssFiniteType
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyReducedOfTensor

/-!
# The standard model of the residue field of a scheme of finite type

Let `f : X ⟶ Spec R` be locally of finite type, let `x` be a point of `X` above a point `s` of
`Spec R`, and write `K` and `L` for the residue fields at `s` and `x`. If `L ⊗[K] K̄` is a domain,
where `K̄ = AlgebraicClosure K`, then `L` is the function field of a hypersurface over `K` that
stays irreducible over `K̄`.

## Main results

* `AlgebraicGeometry.exists_mvPolynomial_model_residueField`: the hypersurface model of the
  residue field `L` over `K`.

## Implementation notes

The algebra structure on `L` over `K` is a `letI` of the statement, not an instance: a residue
field carries several algebra structures.

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), Step B of the first
  proof
-/

@[expose] public section

open CategoryTheory MvPolynomial

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- Let `f : X ⟶ Spec R` be locally of finite type, let `x` be a point of `X` and `s` a point of
`Spec R` equal to `f x`, and write `K` for the residue field of `Spec R` at `s` and `L` for the
residue field of `X` at `x`. If `L ⊗[K] K̄` is a domain for `K̄` an algebraic closure of `K`, then
`L` is the function field of a hypersurface over `K`: there are `n`, a family `v : Fin n → L`
generating `L` over `K` and a nonzero `Q : MvPolynomial (Fin n) K` generating the kernel of
evaluation at `v`, with `Q` irreducible after coefficientwise extension to `K̄`, and with `L` a
field of fractions of `MvPolynomial (Fin n) K ⧸ (Q)`. -/
theorem exists_mvPolynomial_model_residueField (R : CommRingCat.{u}) {X : Scheme.{u}}
    (f : X ⟶ Spec R) [LocallyOfFiniteType f] {x : X} {s : Spec R} (hs : f x = s) :
    letI := residueFieldAlgebraOfEq f hs
    IsDomain (X.residueField x ⊗[(Spec R).residueField s]
        AlgebraicClosure ((Spec R).residueField s)) →
      ∃ (n : ℕ) (v : Fin n → X.residueField x)
        (Q : MvPolynomial (Fin n) ((Spec R).residueField s)),
        IntermediateField.adjoin ((Spec R).residueField s) (Set.range v) = ⊤ ∧
        RingHom.ker (aeval v : MvPolynomial (Fin n) ((Spec R).residueField s) →ₐ[_]
          (X.residueField x)).toRingHom = Ideal.span {Q} ∧
        Q ≠ 0 ∧
        Irreducible (Q.map (algebraMap ((Spec R).residueField s)
          (AlgebraicClosure ((Spec R).residueField s)))) ∧
        ∀ φ : (MvPolynomial (Fin n) ((Spec R).residueField s) ⧸ Ideal.span {Q}) →ₐ[_]
            (X.residueField x),
          φ.comp (Ideal.Quotient.mkₐ _ (Ideal.span {Q})) =
              (aeval v : MvPolynomial (Fin n) ((Spec R).residueField s) →ₐ[_]
                (X.residueField x)) →
            letI := φ.toRingHom.toAlgebra
            IsFractionRing (MvPolynomial (Fin n) ((Spec R).residueField s) ⧸ Ideal.span {Q})
              (X.residueField x) := by
  let := residueFieldAlgebraOfEq f hs
  intro hdom
  have : Algebra.EssFiniteType ((Spec R).residueField s) (X.residueField x) :=
    essFiniteType_specResidueField_residueField R f hs
  have : Algebra.IsGeometricallyReduced ((Spec R).residueField s) (X.residueField x) :=
    Algebra.isGeometricallyReduced_of_isDomain_tensor_isAlgClosure _ _ _ hdom
  exact Algebra.exists_mvPolynomial_model_of_isDomain_tensor _ _ _ hdom

end AlgebraicGeometry

end
