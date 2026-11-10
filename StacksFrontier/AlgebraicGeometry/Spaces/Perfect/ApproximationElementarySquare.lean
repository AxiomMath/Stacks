module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.Approximation.OpenSubscheme
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Approximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardOfSupportedPerfect
import StacksCore.Tactic.StacksAttribute

/-!
# Support along an isomorphism of abelian sheaves

An isomorphism of abelian sheaves on the small étale site of an algebraic space does not
enlarge the support (Stacks 04KB, through
`AlgebraicGeometry.Space.supportOfSheaf_subset_of_mono`).

Stacks 08HL, that approximation descends along an elementary distinguished square, is
`AlgebraicGeometry.Space.approximationHolds_of_isElementaryDistinguishedSquare` in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ApproximationAcrossSquare.lean`.

## References

* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 08HL](https://stacks.math.columbia.edu/tag/08HL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An isomorphism of abelian sheaves on the small étale site of an algebraic space does not
enlarge the support: it is a monomorphism, so Stacks 04KB applies. -/
theorem supportOfSheaf_subset_of_isIso (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{u}} (f : F ⟶ G) (hf : IsIso f) :
    supportOfSheaf B S hS X F ⊆ supportOfSheaf B S hS X G :=
  let := hf
  supportOfSheaf_subset_of_mono B S hS X hX f

end AlgebraicGeometry.Space

end
