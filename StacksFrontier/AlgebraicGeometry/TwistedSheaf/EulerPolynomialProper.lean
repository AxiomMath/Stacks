module

public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.StepAssembly

/-!
# Euler characteristics of twists on a proper scheme over a field

For `X` proper over a field `k`, invertible `𝒪_X`-modules `𝓛_1, …, 𝓛_r` and a coherent
`𝒪_X`-module `ℱ`, the Euler characteristics of the twists `ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}`
are the values of a numerical polynomial (Stacks, Tag 0BEM).

## Main results

* `AlgebraicGeometry.exists_eulerPolynomial_twistedSheaf_of_isProper`: there is a polynomial
  `P ∈ ℚ[n_1, …, n_r]`, zero or of total degree at most `dim Supp ℱ`, whose value at every
  integer vector `n` is the Euler characteristic of `ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}`.

## References

* [Stacks Project, Tag 0BEM](https://stacks.math.columbia.edu/tag/0BEM)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Let `k` be a field, let `X` be a scheme proper over `k`, let `𝓛_1, …, 𝓛_r` be invertible
`𝒪_X`-modules and let `ℱ` be a coherent `𝒪_X`-module.  Then the Euler characteristics of the
twists `ℱ ⊗ 𝓛_1^{⊗ n_1} ⊗ ⋯ ⊗ 𝓛_r^{⊗ n_r}` are the values of a polynomial in `ℚ[n_1, …, n_r]`
which is zero or of total degree at most `dim Supp ℱ`. -/
@[stacks 0BEM]
theorem exists_eulerPolynomial_twistedSheaf_of_isProper (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {r : ℕ} (L : Fin r → X.Modules)
    [∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L i)] [IsProper f]
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤
        topologicalKrullDim (_root_.SheafOfModules.supp F)) ∧
      ∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P
        = (@eulerCharacteristic k _ X f _ (twistedSheaf F L n)
            (@twistedSheaf_isCoherent X r F L _ hF n) : ℚ) :=
  exists_eulerPolynomial_twistedSheaf_of_finiteDimensional_cohomology k f L
    (forall_finiteDimensional_cohomologyOverField_of_isProper k f) F hF

end AlgebraicGeometry

end
