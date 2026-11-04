module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.CohomologyOfALocalizedSite

/-!
# Cohomology of the small crystalline site localized at an object

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `A = (U, T, δ)` of the small
crystalline site `Cris(X/S)`. Localizing the site at `A` gives the site `Cris(X/S)/A`, whose
objects are the objects of `Cris(X/S)` equipped with a morphism to `A` and whose coverings are the
coverings of `Cris(X/S)` lying over `A`. Its global cohomology is what [Stacks, Tag 07JJ] calls
`H^p((U, T, δ), F)`, the cohomology of `F` over the object.

This file sets up cohomology on the localized site, at the coefficient universe `u + 1`, and
identifies it with the right derived functors of the sections functor over `A`:

`H^p(Cris(X/S)/A, F|_A) ≅ R^p Γ(A, F)`,

naturally in the abelian sheaf `F` on `Cris(X/S)`, for every object and every abelian sheaf.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `restrictToOver`: the restriction `F ↦ F|_A` of an abelian sheaf on `Cris(X/S)` to the
  localized site `Cris(X/S)/A`.
* `overGlobalSections`, `overCohomologyFunctor`, `overCohomology`: global sections and the
  cohomology groups `H^j(Cris(X/S)/A, -)` of abelian sheaves on the localized site.
* `sectionsFunctorOver`: the sections functor `F ↦ F(A)` of abelian sheaves on `Cris(X/S)`.

## Main results

* `instHasSheafifyOver`, `instLocallySmallOver`, `instEnoughInjectivesOver`, `instHasExtOver`:
  abelian sheaves on the localized site, at the coefficient universe `u + 1`, admit
  sheafification, are locally small, have enough injectives and have `Ext`-groups.
* `overRightDerivedGlobalSectionsIso`: cohomology on the localized site is the right derived
  functor of its global sections.
* `overGlobalSectionsIsoSections`: the global sections of the localized site are the sections
  over the terminal object `𝟙 A` of `Cris(X/S)/A`.
* `overCohomologyFunctorIsoRightDerivedSections`: the cohomology of the localized site is the
  right derived functor of sections over the object, `H^j(Cris(X/S)/A, F|_A) ≅ R^j Γ(A, F)`,
  naturally in `F`.
* `overCohomologyIsoRightDerivedSections`: the same isomorphism at a fixed abelian sheaf.

## References

* [Stacks Project, Tag 07JJ](https://stacks.math.columbia.edu/tag/07JJ)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u}) (A : CrystallineThickening S)

/-- Abelian sheaves on the small crystalline site localized at an object admit sheafification,
with the coefficients in the universe of the objects of the site. -/
instance instHasSheafifyOver :
    HasSheafify ((smallTopology S).over A) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- Abelian sheaves on the localized site `Cris(X/S)/A` are locally `(u + 1)`-small. -/
instance instLocallySmallOver :
    LocallySmall.{u + 1} (Sheaf ((smallTopology S).over A) AddCommGrpCat.{u + 1}) :=
  Sheaf.locallySmall_of_small.{u + 1, u + 1, u, u + 1, u + 2} ((smallTopology S).over A)
    AddCommGrpCat.{u + 1}

/-- **Abelian sheaves on the localized site `Cris(X/S)/A` have enough injectives.** -/
instance instEnoughInjectivesOver :
    EnoughInjectives (Sheaf ((smallTopology S).over A) AddCommGrpCat.{u + 1}) :=
  Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u + 1, u + 2} ((smallTopology S).over A)
    AddCommGrpCat.{u + 1}

/-- **`Ext`-groups of abelian sheaves on `Cris(X/S)/A` exist in `Type (u + 1)`.** -/
instance instHasExtOver :
    HasExt.{u + 1} (Sheaf ((smallTopology S).over A) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

/-- **The restriction `F ↦ F|_A`** of an abelian sheaf on the small crystalline site to the
localized site `Cris(X/S)/A`. -/
abbrev restrictToOver :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf ((smallTopology S).over A) AddCommGrpCat.{u + 1} :=
  (smallTopology S).overPullback AddCommGrpCat.{u + 1} A

/-- **The global sections functor `Γ(Cris(X/S)/A, -)`** of abelian sheaves on the localized
site. -/
abbrev overGlobalSections :
    Sheaf ((smallTopology S).over A) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.Γ ((smallTopology S).over A) AddCommGrpCat.{u + 1}

/-- Global sections of abelian sheaves on `Cris(X/S)/A` are additive. -/
instance instAdditiveOverGlobalSections : (overGlobalSections S A).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1, u, u + 1} ((smallTopology S).over A)

/-- **The `j`-th cohomology functor `H^j(Cris(X/S)/A, -)`** of abelian sheaves on the localized
site: the `Ext`-groups in degree `j` out of the constant sheaf on `ℤ`. -/
def overCohomologyFunctor (j : ℕ) :
    Sheaf ((smallTopology S).over A) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.functorH.{u + 1, u + 1, u, u + 1} ((smallTopology S).over A) j

/-- **The cohomology group `H^j(Cris(X/S)/A, F)`** of an abelian sheaf on the localized site. -/
abbrev overCohomology (F : Sheaf ((smallTopology S).over A) AddCommGrpCat.{u + 1}) (j : ℕ) :
    Type (u + 1) :=
  Sheaf.H.{u + 1, u + 1} F j

/-- **Cohomology on `Cris(X/S)/A` is the right derived functor of its global sections**,
`R^j Γ(Cris(X/S)/A, -) ≅ H^j(Cris(X/S)/A, -)`. -/
def overRightDerivedGlobalSectionsIso (j : ℕ) :
    (overGlobalSections S A).rightDerived j ≅ overCohomologyFunctor S A j :=
  Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u, u + 1}
    ((smallTopology S).over A) j

/-- **The sections functor `F ↦ F(A)`** of abelian sheaves on the small crystalline site at an
object. -/
abbrev sectionsFunctorOver :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  (sheafSections (smallTopology S) AddCommGrpCat.{u + 1}).obj (op A)

/-- Sections of abelian sheaves over an object of the small crystalline site are additive. -/
instance instAdditiveSectionsFunctorOver : (sectionsFunctorOver S A).Additive :=
  inferInstanceAs ((sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
    (evaluation (CrystallineThickening S)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op A)).Additive)

/-- Sections of abelian sheaves over an object of a localized small crystalline site are
additive. -/
instance instAdditiveSectionsOverLocalized (V : Over A) :
    ((sheafSections ((smallTopology S).over A) AddCommGrpCat.{u + 1}).obj (op V)).Additive :=
  inferInstanceAs ((sheafToPresheaf ((smallTopology S).over A) AddCommGrpCat.{u + 1} ⋙
    (evaluation (Over A)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).Additive)

/-- **The global sections of the localized site are the sections over its terminal object**
`𝟙 A` of `Cris(X/S)/A`. -/
def overGlobalSectionsIsoSections :
    overGlobalSections S A ≅
      (sheafSections ((smallTopology S).over A) AddCommGrpCat.{u + 1}).obj
        (op (Over.mk (𝟙 A))) :=
  Sheaf.ΓNatIsoSheafSections ((smallTopology S).over A) AddCommGrpCat.{u + 1} Over.mkIdTerminal

/-- **The cohomology of the small crystalline site localized at an object is the right derived
functor of the sections over that object.**  For every degree `j`,

`H^j(Cris(X/S)/A, F|_A) ≅ R^j Γ(A, F)`,

naturally in the abelian sheaf `F` on `Cris(X/S)`. -/
def overCohomologyFunctorIsoRightDerivedSections (j : ℕ) :
    restrictToOver S A ⋙ overCohomologyFunctor S A j ≅ (sectionsFunctorOver S A).rightDerived j :=
  Functor.isoWhiskerLeft (restrictToOver S A) (overRightDerivedGlobalSectionsIso S A j).symm ≪≫
    Functor.isoWhiskerLeft (restrictToOver S A)
      (Functor.rightDerivedIsoOfNatIso (overGlobalSectionsIsoSections S A) j) ≪≫
    Stacks.Cohomology.LocalizedSite.overPullbackRightDerivedSectionsIso.{u, u + 1, u + 1}
      (smallTopology S) A j (Over.mk (𝟙 A))

/-- **The cohomology of a sheaf over an object of the small crystalline site, computed on the
localized site, is its right derived sections over that object**: the isomorphism of
`overCohomologyFunctorIsoRightDerivedSections` at a fixed abelian sheaf. -/
def overCohomologyIsoRightDerivedSections
    (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (j : ℕ) :
    (overCohomologyFunctor S A j).obj ((restrictToOver S A).obj F) ≅
      ((sectionsFunctorOver S A).rightDerived j).obj F :=
  (overCohomologyFunctorIsoRightDerivedSections S A j).app F

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
