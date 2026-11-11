module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.CuspForm
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.GaloisSide
public import StacksFrontier.NumberTheory.TraceFormula.GeometricMonodromyFiniteness

/-!
# The automorphic form attached to a representation of `π₁` of a curve

Let `X` be a smooth, projective, geometrically irreducible curve over a finite field with
function field `K` and `ρ : π₁(X) → GL_n(F_ℓ[[t]])` a continuous representation. The input of
Gaitsgory's theorem (Tag 03W0) is an automorphic form with coefficients in an extension `Λ` of
`F_ℓ((t))` attached to `ρ`: unramified cuspidal Hecke eigenforms `f_1, …, f_m` on
`GL_{n_1}(A), …, GL_{n_m}(A)` with `n_1 + ⋯ + n_m = n` such that, at every place `v` and every
geometric Frobenius element `F_v` at `v`, the characteristic polynomial of `ρ(F_v)` is the product
of the Hecke polynomials of the `f_j` at `v`. For `ρ` irreducible this is a single cuspidal
eigenform (`m = 1`), as in de Jong's formulation; the factorization accounts for the
Jordan–Hölder constituents of `ρ`, a cuspidal eigenform with the eigenvalues of a reducible `ρ`
not existing in general. For `GL_2` the matching is the compatibility of the base,
`Stacks.Adeles.GlobalFunctionField.IsFrobeniusCompatible`. Gaitsgory constructs these
eigenforms from a Hecke eigensheaf with `F_ℓ((t))`-coefficients for `ℓ > 2n`, using a theory of
sheaves with such coefficients which is not worked out in the literature.

## Main definitions

* `Stacks.TraceFormula.HasCuspidalHeckeEigenforms` — `ρ` has an attached automorphic form.

## References

* [Stacks Project, Tag 03W0](https://stacks.math.columbia.edu/tag/03W0)
* [Gaitsgory]
* [dJ-conjecture]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Adeles Stacks.Adeles.GlobalFunctionField

open scoped PowerSeries.WithPiTopology

universe u

namespace Stacks.TraceFormula

variable {X : Scheme.{u}} [IsIntegral X] [ConnectedSpace X] {n ℓ : ℕ}

/-- `ρ : π₁(X, base) → GL_n(F_ℓ[[t]])` has an attached automorphic form: there are a field `Λ`
with an embedding `ι : F_ℓ[[t]] → Λ`, sizes `n_j > 0` with `∑ n_j = n`, and unramified cusp forms
`f_j` on `GL_{n_j}(A)` with values in `Λ` which are Hecke eigenforms with eigenvalues
`t_j v i`, such that for every place `v` of the function field and every geometric Frobenius
element `F` at `v`, the characteristic polynomial of `ρ(F)`, mapped by `ι`, is the product of the
Hecke polynomials `∑_i (-1)^i q_v^{i(i-1)/2} t_j v i X^{n_j - i}`. -/
public def HasCuspidalHeckeEigenforms (base : GeometricPoint X)
    (ρ : EtaleFundamentalGroup X base →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ))) : Prop :=
  ∃ (Λ : Type u) (_ : Field Λ) (ι : PowerSeries (ZMod ℓ) →+* Λ) (m : ℕ) (d : Fin m → ℕ)
    (F : ∀ j, GL (Fin (d j)) (AdeleRing X.functionField) → Λ)
    (t : Fin m → Place X.functionField → ℕ → Λ),
    Function.Injective ι ∧ ∑ j, d j = n ∧ (∀ j, 0 < d j) ∧
      (∀ j, IsUnramifiedCuspFormGL (d j) (F j)) ∧ (∀ j, IsHeckeEigenformGL (F j) (t j)) ∧
      ∀ (v : Place X.functionField) (g : EtaleFundamentalGroup X base),
        GlobalFunctionField.IsGeometricFrobeniusAt base v g →
          (ρ g : Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ))).charpoly.map ι =
            ∏ j, heckePolynomial (d j) v.residueCard (t j v)

end Stacks.TraceFormula

end
