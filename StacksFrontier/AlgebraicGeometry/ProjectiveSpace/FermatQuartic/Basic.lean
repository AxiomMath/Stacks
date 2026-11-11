module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology

/-!
# The Fermat quartic surface

Let `k` be a field. The *Fermat quartic* is the hypersurface

`X = V(x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴) ⊆ 𝐏³_k = Proj k[x₀, x₁, x₂, x₃]`.

When `2` is invertible in `k` it is a smooth quartic surface, hence a K3 surface. This file fixes
the data: the quartic polynomial as a homogeneous element of degree four, the ideal sheaf of `X`
as the zero scheme of the corresponding section of `𝒪(4)`, the scheme `X` as the closed subscheme
it cuts out, its closed immersion into `𝐏³_k` and its structure morphism to `Spec k`.

## Main definitions

* `AlgebraicGeometry.FermatQuartic.fermatPolynomial`: `x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴`, homogeneous of
  degree four.
* `AlgebraicGeometry.FermatQuartic.idealSheaf`: the zero scheme of the section of `𝒪(4)` attached
  to it.
* `AlgebraicGeometry.FermatQuartic.fermatQuartic`: the scheme `X`.
* `AlgebraicGeometry.FermatQuartic.toProjectiveSpace`: the closed immersion `X ⟶ 𝐏³_k`.
* `AlgebraicGeometry.FermatQuartic.toSpec`: the structure morphism `X ⟶ Spec k`.

## Main results

* `AlgebraicGeometry.FermatQuartic.ker_toProjectiveSpace`: the ideal sheaf of `X ⊆ 𝐏³_k` is the
  zero scheme of the section of `𝒪(4)` attached to the quartic.
* `AlgebraicGeometry.FermatQuartic.fermatPolynomial_ne_zero`: the quartic is nonzero.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MvPolynomial
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheafModule degreeSection)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.FermatQuartic

variable (k : Type u) [Field k]

/-- The Fermat quartic polynomial `x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴`, as a homogeneous element of degree
four of `k[x₀, x₁, x₂, x₃]`. -/
def fermatPolynomial : polyGrading k 3 4 :=
  ⟨∑ i : Fin 4, X i ^ 4, (mem_homogeneousSubmodule _ _).2
    (IsHomogeneous.sum _ _ _ fun i _ => by simpa using (isHomogeneous_X k i).pow 4)⟩

/-- The underlying polynomial of `fermatPolynomial` is `∑ xᵢ⁴`. -/
theorem coe_fermatPolynomial :
    (fermatPolynomial k : MvPolynomial (Fin 4) k) = ∑ i : Fin 4, X i ^ 4 := rfl

/-- The Fermat quartic polynomial is nonzero: its coefficient at `x₀⁴` is `1`. -/
theorem fermatPolynomial_ne_zero : (fermatPolynomial k : MvPolynomial (Fin 4) k) ≠ 0 := by
  intro h
  have h1 := congrArg (eval (Pi.single 0 1)) h
  simp [coe_fermatPolynomial, Fin.sum_univ_four] at h1

/-- The ideal sheaf of the Fermat quartic in `𝐏³_k`: the zero scheme of the section of `𝒪(4)`
attached to `x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴`. -/
def idealSheaf : (Proj (polyGrading k 3)).IdealSheafData :=
  zeroScheme (Proj (polyGrading k 3)) (twistingSheafModule (polyGrading k 3) ((4 : ℕ) : ℤ))
    (degreeSection (polyGrading k 3) 4 (fermatPolynomial k))

/-- **The Fermat quartic surface** `X = V(x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴) ⊆ 𝐏³_k`, the closed subscheme
cut out by `idealSheaf k`. -/
def fermatQuartic : Scheme.{u} := (idealSheaf k).subscheme

/-- The closed immersion of the Fermat quartic into `𝐏³_k`. -/
def toProjectiveSpace : fermatQuartic k ⟶ Proj (polyGrading k 3) := (idealSheaf k).subschemeι

/-- The inclusion of the Fermat quartic into `𝐏³_k` is a closed immersion. -/
instance isClosedImmersion_toProjectiveSpace : IsClosedImmersion (toProjectiveSpace k) :=
  (fun {X : Scheme.{u}} (I : X.IdealSheafData) => (inferInstance : IsClosedImmersion I.subschemeι))
    (idealSheaf k)

/-- The structure morphism of the Fermat quartic, `X ⟶ 𝐏³_k ⟶ Spec k`. -/
def toSpec : fermatQuartic k ⟶ Spec (.of k) := toProjectiveSpace k ≫ projToSpecCoeff k 3

/-- **The ideal sheaf of the Fermat quartic** is the zero scheme of the section of `𝒪(4)`
attached to `x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴`. -/
theorem ker_toProjectiveSpace :
    (toProjectiveSpace k).ker =
      zeroScheme (Proj (polyGrading k 3)) (twistingSheafModule (polyGrading k 3) ((4 : ℕ) : ℤ))
        (degreeSection (polyGrading k 3) 4 (fermatPolynomial k)) :=
  Scheme.IdealSheafData.ker_subschemeι _

end AlgebraicGeometry.FermatQuartic

end
