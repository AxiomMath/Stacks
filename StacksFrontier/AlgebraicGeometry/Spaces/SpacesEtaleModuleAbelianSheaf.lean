module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp

/-!
# The abelian sheaf on the spaces-étale site underlying an `𝒪_X`-module

Let `X` be an algebraic space. `𝒪_X`-modules live on the small étale site `X_étale` of Stacks 03ED
(`AlgebraicGeometry.Space.SmallEtale`), whose objects are the étale scheme charts of `X`, while
sheaves attached to a category over `X_{spaces,étale}` (Stacks 03G0) — such as the band of a gerbe
over that site, Stacks 0CJY — live on the spaces-étale site. Restriction along the comparison
functor of Stacks 03G1 is an equivalence of the two categories of abelian sheaves
(`AlgebraicGeometry.Space.comparisonFunctor_sheafEquivalence`), so an `𝒪_X`-module determines an
abelian sheaf on `X_{spaces,étale}` up to unique isomorphism. This file names it:

* `AlgebraicGeometry.Space.spacesEtaleAbelianSheaf`: the abelian sheaf on `X_{spaces,étale}` of an
  `𝒪_X`-module `M`, whose restriction to `X_étale` is the underlying abelian sheaf of `M`
  (`AlgebraicGeometry.Space.spacesEtaleAbelianSheafRestrictionIso`);
* `AlgebraicGeometry.Space.nonempty_iso_spacesEtaleAbelianSheaf_iff`: an abelian sheaf `G` on
  `X_{spaces,étale}` is that sheaf exactly when its restriction to `X_étale` is the underlying
  abelian sheaf of `M`. This is the meaning of "a sheaf of abelian groups on `X_{spaces,étale}` is
  an `𝒪_X`-module" used in Stacks 0CKG (2).

The module universe is `u + 1`, the universe of the objects of the two sites, at which the
restriction functor is an equivalence with no further input.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Restriction of abelian sheaves from `X_{spaces,étale}` to `X_étale`** along the comparison
functor of Stacks 03G1; an equivalence. -/
abbrev spacesEtaleAbelianRestriction :
    Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u + 1} :=
  (comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)

/-- **The abelian sheaf on `X_{spaces,étale}` of an `𝒪_X`-module**: the preimage, under the
restriction equivalence of Stacks 03G1, of the underlying abelian sheaf of `M`. -/
def spacesEtaleAbelianSheaf (M : SheafOfModules.{u + 1} (structureRingSheaf B S hS X)) :
    Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1} :=
  (spacesEtaleAbelianRestriction B S hS X).inv.obj ((SheafOfModules.toSheaf _).obj M)

/-- The restriction of `AlgebraicGeometry.Space.spacesEtaleAbelianSheaf M` to `X_étale` is the
underlying abelian sheaf of `M`. -/
def spacesEtaleAbelianSheafRestrictionIso
    (M : SheafOfModules.{u + 1} (structureRingSheaf B S hS X)) :
    (spacesEtaleAbelianRestriction B S hS X).obj (spacesEtaleAbelianSheaf B S hS X M) ≅
      (SheafOfModules.toSheaf _).obj M :=
  (spacesEtaleAbelianRestriction B S hS X).asEquivalence.counitIso.app _

/-- **An abelian sheaf on `X_{spaces,étale}` is the sheaf of an `𝒪_X`-module `M` exactly when its
restriction to `X_étale` is the underlying abelian sheaf of `M`.** -/
theorem nonempty_iso_spacesEtaleAbelianSheaf_iff
    (G : Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{u + 1})
    (M : SheafOfModules.{u + 1} (structureRingSheaf B S hS X)) :
    Nonempty (G ≅ spacesEtaleAbelianSheaf B S hS X M) ↔
      Nonempty ((spacesEtaleAbelianRestriction B S hS X).obj G ≅
        (SheafOfModules.toSheaf _).obj M) :=
  ⟨fun ⟨e⟩ => ⟨(spacesEtaleAbelianRestriction B S hS X).mapIso e ≪≫
      spacesEtaleAbelianSheafRestrictionIso B S hS X M⟩,
    fun ⟨e⟩ => ⟨(spacesEtaleAbelianRestriction B S hS X).preimageIso
      (e ≪≫ (spacesEtaleAbelianSheafRestrictionIso B S hS X M).symm)⟩⟩

end AlgebraicGeometry.Space
