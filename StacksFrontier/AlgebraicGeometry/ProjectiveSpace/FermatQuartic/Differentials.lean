module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.FermatQuartic.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HypersurfaceDifferentials

/-!
# The Fermat quartic has no global differential forms

Let `k` be a field and `X = V(x₀⁴ + x₁⁴ + x₂⁴ + x₃⁴) ⊆ 𝐏³_k` the Fermat quartic. If `X` is smooth
over `k` (which holds when `2` is invertible in `k`), then `H⁰(X, Ω_{X/k}) = 0`: every morphism
`𝒪_X ⟶ Ω_{X/k}` is zero. This is the specialization to `n = 3`, `d = 4` of
`Stacks.ProjectiveSpace.Differentials.subsingleton_unit_hom_relativeDifferentials_hypersurface`.

## Main results

* `AlgebraicGeometry.FermatQuartic.subsingleton_unit_hom_relativeDifferentials_of_smooth`:
  `H⁰(X, Ω_{X/k}) = 0` for the Fermat quartic, as soon as it is smooth over `k`.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FermatQuartic

variable (k : Type u) [Field k]

/-- **The Fermat quartic has no global differential forms**: if `X` is smooth over `k`, every
morphism `𝒪_X ⟶ Ω_{X/k}` is zero, that is `H⁰(X, Ω_{X/k}) = 0`. -/
theorem subsingleton_unit_hom_relativeDifferentials_of_smooth
    (h : AlgebraicGeometry.Smooth (toSpec k)) :
    Subsingleton (SheafOfModules.unit _ ⟶ Scheme.Hom.relativeDifferentials (toSpec k)) :=
  Stacks.ProjectiveSpace.Differentials.subsingleton_unit_hom_relativeDifferentials_hypersurface
    k 3 le_rfl 4 (fermatPolynomial k) (fermatPolynomial_ne_zero k) h

end AlgebraicGeometry.FermatQuartic

end
