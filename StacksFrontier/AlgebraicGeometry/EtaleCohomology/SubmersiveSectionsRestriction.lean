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

/-- The canonical comparison on global sections, followed by restriction to the base change of
an étale `S`-scheme `V`, is restriction to `V` followed by the unit of the inverse-image
adjunction at `V`. -/
public theorem globalSectionsSmallEtaleInverseImage_app_comp_ΓRes {T S : Scheme.{u}}
    (f : T ⟶ S) (G : Sheaf (smallEtaleTopology S) (Type (max (u + 1) v))) (V : S.Etale) :
    (globalSectionsSmallEtaleInverseImage f).app G ≫
        ((smallEtaleInverseImage f).obj G).ΓRes (Opposite.op ((smallEtaleBaseChange f).obj V)) =
      G.ΓRes (Opposite.op V) ≫ smallEtaleUnitApp f G V :=
  globalSectionsComparisonApp_ΓRes f G V

end Stacks.EtaleCohomology
