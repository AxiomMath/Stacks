module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleModuleSheafInstances
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The constructible derived category `D_c(X_ét, Λ)`

For a scheme `X` and a coefficient ring `Λ`, `D_c(X_ét, Λ)` is the full subcategory of the
derived category `D(X_ét, Λ)` of sheaves of `Λ`-modules on the small étale site of `X` on the
complexes whose cohomology sheaves are constructible sheaves of `Λ`-modules.

## Main definitions

* `Stacks.EtaleCohomology.ConstructibleEtaleDerivedCategory` is `D_c(X_ét, Λ)`.

## Implementation notes

The subcategory is `Stacks.EtaleCohomology.ConstructibleDerivedCategory` at module sections in
`Type (max u w)`, where `u` is the universe of the schemes. In that range the sheafification of
module presheaves on `X_ét` and on its slices, and the inverse image along every small étale base
change, are theorems (`AlgebraicGeometry.SmallEtale.hasSheafify_moduleCat_of_univLE`,
`AlgebraicGeometry.SmallEtale.hasSheafify_over_moduleCat_of_univLE` and
`AlgebraicGeometry.smallEtaleBaseChange_isRightAdjoint_sheafPushforward_moduleCat`), supplied by
instance search, so the definition depends only on `X` and `Λ`. Constructibility is that of
Stacks 03RW, part (3), stated for an arbitrary ring; the source takes `Λ` Noetherian.

## References

* [Stacks Project, Tag 095W](https://stacks.math.columbia.edu/tag/095W)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w r

namespace Stacks.EtaleCohomology

/-- **Stacks 095W.** `D_c(X_ét, Λ)`: the full subcategory of the unbounded derived category of
sheaves of `Λ`-modules on the small étale site of `X` on the complexes all of whose cohomology
sheaves are constructible sheaves of `Λ`-modules. -/
@[stacks 095W "the full subcategory of D(X_ét, Λ) of complexes whose cohomology sheaves are \
  constructible, for module sections in any universe containing that of the schemes",
  sga "5 IIIB 6.1"]
public abbrev ConstructibleEtaleDerivedCategory (B : BigEtaleSite.{u}) (X : B.Scheme)
    (Λ : Type r) [Ring Λ] :=
  ConstructibleDerivedCategory.{u, max u w, r} B X Λ

end Stacks.EtaleCohomology
