module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.RingTheory.Length.AdicFiltration

/-!
# The multiplicity of a coherent sheaf as a sum of residue dimensions

Let `F` be a coherent `𝒪_X`-module on a locally Noetherian scheme and let `ξ` be the generic
point of an irreducible component of its support, with local ring `(R, m) = (𝒪_{X,ξ}, m_ξ)` and
residue field `k = κ(ξ)`. The stalk `F_ξ` has finite length over `R` [Stacks, Tag 02QW], and that
length is the multiplicity of the component in `F` [Stacks, Tag 02QX]. By
`Stacks.Length.length_eq_finsum_finrank_adicGradedPiece` the length is the total dimension of the
graded pieces of the `m`-adic filtration of `F_ξ`, so

`m_{Z,F} = ∑_{p ≥ 0} dim_k (m^p F_ξ / m^{p+1} F_ξ)`.

This is the form in which the count of residue dimensions enters the general, non-Noetherian
route to [Stacks, Tag 02S9]: the graded pieces of the ideal-adic filtration of `F` are, near `ξ`,
free `𝒪_Z`-modules of rank `dim_k (m^p F_ξ / m^{p+1} F_ξ)`, and this identity says that those
ranks add up to the coefficient of `Z` in the cycle of `F`.

## Main results

* `Stacks.Chow.sheafMultiplicity_eq_finsum_finrank_adicGradedPiece`.

## References

* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- **The multiplicity of a coherent sheaf at a generic point of its support is the total
dimension over the residue field of the graded pieces of the `m`-adic filtration of its stalk.**
The stalk has finite length there, so its `m`-adic filtration is finite and the two counts agree
by `Stacks.Length.length_eq_finsum_finrank_adicGradedPiece`. -/
theorem sheafMultiplicity_eq_finsum_finrank_adicGradedPiece [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X)) (ξ : X)
    (hξ : IsGenericPoint ξ (Subtype.val '' Z.1 : Set X)) :
    sheafMultiplicity F ξ =
      ((∑ᶠ p : ℕ, Module.finrank (ResidueField (X.presheaf.stalk ξ))
        (Stacks.Length.adicGradedPiece (maximalIdeal (X.presheaf.stalk ξ))
          (F.presheaf.stalk ξ) p) : ℕ) : ℤ) := by
  rw [sheafMultiplicity, Stacks.Length.finsum_finrank_adicGradedPiece_eq_toNat_length
    (isFiniteLength_stalk_of_isGenericPoint_component_supp F Z ξ hξ)]

end Stacks.Chow

end
