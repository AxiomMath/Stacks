module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections

/-!
# The global-sections comparison of an inverse image, restricted to an étale scheme

The canonical comparison `Γ(S, G) ⟶ Γ(T, f⁻¹G)` of
`Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImage`, followed by restriction to the
base change of an étale `S`-scheme `V`, is restriction to `V` followed by the unit of the
inverse-image adjunction at `V`. The comparison is built from a limit cone in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections`, whose factorization lemma is
private there; it is read here through `import all`.

## Main results

* `Stacks.EtaleCohomology.globalSectionsSmallEtaleInverseImage_app_comp_ΓRes`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MorphismProperty
open AlgebraicGeometry.Scheme

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition
attribute [local instance] AlgebraicGeometry.Etale.instIsMultiplicativeScheme

universe u v

namespace Stacks.EtaleCohomology

/-- The Mathlib instance `Scheme.instHasSheafifyEtaleSmallEtaleTopology` (for `Category.{u}`
coefficients) is tried first and its universe constraint fails hard while a universe level is
still a metavariable; this instance for sheaves of types answers first. -/
private instance (priority := high) hasSheafifySmallEtaleType' (X : Scheme.{u}) :
    HasSheafify X.smallEtaleTopology (Type (max (u + 1) v)) := inferInstance

/-- The canonical comparison on global sections, followed by restriction to the base change of
an étale `S`-scheme `V`, is restriction to `V` followed by the unit of the inverse-image
adjunction at `V`. -/
public theorem globalSectionsSmallEtaleInverseImage_app_comp_ΓRes {T S : Scheme.{u}}
    (f : T ⟶ S) (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))) (V : S.Etale) :
    (globalSectionsSmallEtaleInverseImage.{u, v} f).app G ≫
        ((smallEtaleInverseImage.{u, v} f).obj G).ΓRes
          (Opposite.op ((smallEtaleBaseChange f).obj V)) =
      G.ΓRes (Opposite.op V) ≫ smallEtaleUnitApp.{u, v} f G V :=
  globalSectionsComparisonApp_ΓRes f G V

end Stacks.EtaleCohomology
