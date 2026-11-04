module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisActionStalks.GlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Global sections over a field on Mathlib's small étale site are Galois invariants

Tag 04JM identifies the global sections of a sheaf of sets on the small étale site of `Spec K`,
`K` a field, with the elements of its stalk at a geometric point `sbar` fixed by the absolute
Galois group at `sbar`. The library proves it on the small étale site of Stacks 021B cut out by a
big étale site `B` (`AlgebraicGeometry.etaleGlobalSectionsEquivGaloisFixedPoints`). This file
reads it on Mathlib's small étale site `(Spec K).smallEtaleTopology`, through the identification
`AlgebraicGeometry.SmallEtale.sheafEquiv` of the two sheaf categories: for a sheaf `G` on
Mathlib's site,
```
Γ(Spec K, G) ≃ (stalk of G at sbar)^{Gal(K^sep/K)},
```
the stalk being that of the restriction of `G` to the bounded site, on which the Galois action is
defined.

## Main definitions

* `AlgebraicGeometry.sheafΓEquivGaloisFixedPoints` — the displayed bijection.

## Implementation notes

The restriction of `G` to the bounded site evaluates at the final object of that site as `G`
evaluates at the image of that object, which is terminal in Mathlib's site
(`AlgebraicGeometry.isTerminalToEtaleSiteFinal`); global sections are sections over any terminal
object (`CategoryTheory.Sheaf.ΓNatIsoSheafSections`).

## References

* [Stacks Project, Tag 04JM](https://stacks.math.columbia.edu/tag/04JM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K)))

/-- **Tag 04JM on Mathlib's small étale site.** The global sections of a sheaf of sets on
Mathlib's small étale site of the spectrum of a field are the Galois-fixed elements of its stalk
at a geometric point, the stalk being that of its restriction to the bounded small étale site. -/
def sheafΓEquivGaloisFixedPoints (G : Sheaf (Spec (.of K)).smallEtaleTopology (Type (u + 1))) :
    (Sheaf.Γ (Spec (.of K)).smallEtaleTopology (Type (u + 1))).obj G ≃
      etaleStalkGaloisFixedPoints.{u, u + 1} B K hK sbar
        ((SmallEtale.sheafEquiv B (Spec (.of K)) hK (Type (u + 1))).inverse.obj G) :=
  ((Sheaf.ΓNatIsoSheafSections _ _
      (isTerminalToEtaleSiteFinal B (Spec (.of K)) hK)).app G).toEquiv.trans
    (etaleGlobalSectionsEquivGaloisFixedPoints.{u, u + 1} B K hK sbar
      ((SmallEtale.sheafEquiv B (Spec (.of K)) hK (Type (u + 1))).inverse.obj G))

end AlgebraicGeometry

end
