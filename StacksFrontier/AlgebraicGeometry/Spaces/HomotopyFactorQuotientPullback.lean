module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePullbackHomotopyFactorQuotient

/-!
# The contraction of pullbacks on homotopy categories, at the image of a complex

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces and a factorisation `f ≫ g = k`,
`AlgebraicGeometry.Space.smallEtalePullbackMapHomotopyFactorIso` identifies `g^* ⋙ f^*` with `k^*`
on the unbounded homotopy categories of complexes of modules.  This file reads its inverse at the
image of a complex: it is the image under `CategoryTheory.HomotopyCategory.quotient` of the
inverse of the degreewise contraction
`AlgebraicGeometry.Space.smallEtaleToposPullbackFactorIso`.

## Main results

* `AlgebraicGeometry.Space.smallEtalePullbackMapHomotopyFactorIso_inv_app_quotient`: the inverse
  of the contraction on homotopy categories is, at the image of a complex, the image of the
  inverse of the degreewise contraction.

## Implementation notes

The proof is the already-general
`StacksDraft.ComparisonSquare.mapHomotopyCategoryCompIso_inv_app_quotient'`, which is `rfl` on
variables, applied after the three factors of the contraction have been contracted into a single
`CategoryTheory.Functor.mapHomotopyCategoryCompIso` by
`AlgebraicGeometry.Space.smallEtalePullbackMapHomotopyFactorIso_eq`.  Both halves are essential
and neither can be skipped:

* Without the contraction the statement is not `rfl`: the contraction carries a
  `CategoryTheory.eqToIso` along the factorisation, and a renaming is not an identity.
* The contraction must be rewritten into the goal rather than supplied to a general lemma that
  takes it as a hypothesis and substitutes it.  The latter spelling elaborates, but the proof
  term it produces is rejected by the kernel with `(kernel) deterministic timeout`; the `rw`
  spelling is checked.

The degreewise contraction is read at the ascribed spelling of
`CategoryTheory.Functor.mapHomologicalComplexCompIso`, whose type is `g^{*•} ⋙ f^{*•} ≅ k^{*•}`,
rather than at the `CategoryTheory.NatIso.mapHomologicalComplex` it is defined to be, whose type
is `(g^* ⋙ f^*)^• ≅ k^{*•}`.  The two are the same term; the conversion identifying the two
spellings is performed once, in Mathlib, where the functors are variables.  At inverse images of
sheaves of modules it unfolds the construction of an inverse image, and elaborating
`(g^* ⋙ f^*)^•` as a type alone costs more than half of the heartbeat budget.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS}

/-- **The contraction `g^* ⋙ f^* ≅ k^*` on homotopy categories, read backwards at the image of a
complex, is the image of the degreewise contraction read backwards.** -/
theorem smallEtalePullbackMapHomotopyFactorIso_inv_app_quotient (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (hk : f ≫ g = k)
    (N : HomologicalComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
      (ComplexShape.up ℤ)) :
    (smallEtalePullbackMapHomotopyFactorIso f g k hk).inv.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (smallEtaleToposPullbackFactorIso f g k hk)
          (ComplexShape.up ℤ)).inv.app N) := by
  rw [smallEtalePullbackMapHomotopyFactorIso_eq]
  exact StacksDraft.ComparisonSquare.mapHomotopyCategoryCompIso_inv_app_quotient' _ _ _

end AlgebraicGeometry.Space

end
