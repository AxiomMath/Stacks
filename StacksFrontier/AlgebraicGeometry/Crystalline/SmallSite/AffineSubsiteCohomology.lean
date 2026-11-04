module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineSubsite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology

/-!
# Cohomology on the affine crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`.  The inclusion of the affine crystalline
site `AffineCris(X/S)` into the small crystalline site `Cris(X/S)` is a special cocontinuous
functor, `affineι_isSpecialCocontinuous`, so restriction along it is an equivalence on abelian
sheaves.  This file draws the cohomological consequence: **the cohomology of `Cris(X/S)` is
computed on `AffineCris(X/S)`**,

`H^j(AffineCris(X/S), F|_{AffineCris(X/S)}) ≅ H^j(Cris(X/S), F)`,

naturally in the abelian sheaf `F`, in every degree.

## Main definitions

Everything below lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `restrictToAffine` — the restriction `F ↦ F|_{AffineCris(X/S)}` of an abelian sheaf on the
  small crystalline site to the affine crystalline site.
* `affineGlobalSections`, `affineCohomologyFunctor`, `affineCohomology` — global sections and the
  cohomology groups `H^j(AffineCris(X/S), -)` of abelian sheaves on the affine crystalline site.

## Main results

* `instHasSheafifyAffine`, `instLocallySmallAffine`, `instEnoughInjectivesAffine`,
  `instHasExtAffine` — the four instances that make cohomology on the affine crystalline site
  exist, at the coefficient universe `u + 1`.
* `restrictToAffine_isEquivalence` — **restriction to the affine crystalline site is an
  equivalence** on abelian sheaves.
* `affineRightDerivedGlobalSectionsIso` — `R^j Γ(AffineCris(X/S), -) ≅ H^j(AffineCris(X/S), -)`.
* `affineCohomologyFunctorIso` — **restriction to the affine crystalline site does not change
  cohomology**: `(-)|_{AffineCris(X/S)} ⋙ H^j(AffineCris(X/S), -) ≅ H^j(Cris(X/S), -)`.
* `affineCohomologyIso` — the same isomorphism at a fixed abelian sheaf.

## References

* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 03CG](https://stacks.math.columbia.edu/tag/03CG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- Abelian sheaves on the affine crystalline site admit sheafification, with the coefficients in
the universe of the objects of the site. -/
instance instHasSheafifyAffine :
    HasSheafify (affineTopology S) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- Abelian sheaves on the affine crystalline site are locally `(u + 1)`-small. -/
instance instLocallySmallAffine :
    LocallySmall.{u + 1} (Sheaf (affineTopology S) AddCommGrpCat.{u + 1}) :=
  Sheaf.locallySmall_of_small.{u + 1, u + 1, u, u + 1, u + 2} (affineTopology S)
    AddCommGrpCat.{u + 1}

/-- **Abelian sheaves on the affine crystalline site have enough injectives.** -/
instance instEnoughInjectivesAffine :
    EnoughInjectives (Sheaf (affineTopology S) AddCommGrpCat.{u + 1}) :=
  Sheaf.enoughInjectives_of_small.{u + 1, u + 1, u, u + 1, u + 2} (affineTopology S)
    AddCommGrpCat.{u + 1}

/-- **`Ext`-groups of abelian sheaves on the affine crystalline site exist in `Type (u + 1)`**. -/
instance instHasExtAffine :
    HasExt.{u + 1} (Sheaf (affineTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

/-- **The restriction `F ↦ F|_{AffineCris(X/S)}`** of an abelian sheaf on the small crystalline
site to the affine crystalline site. -/
abbrev restrictToAffine :
    Sheaf (smallTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (affineTopology S) AddCommGrpCat.{u + 1} :=
  (affineι S).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (affineTopology S) (smallTopology S)

/-- The sections of `F|_{AffineCris(X/S)}` over an affine object are the sections of `F` over that
object of `Cris(X/S)`. -/
theorem restrictToAffine_obj_obj (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (A : AffineCrystallineThickening S) :
    ((restrictToAffine S).obj F).obj.obj (op A) = F.obj.obj (op ((affineι S).obj A)) := rfl

/-- **Restriction to the affine crystalline site is an equivalence** on abelian sheaves. -/
instance restrictToAffine_isEquivalence : (restrictToAffine S).IsEquivalence :=
  inferInstance

/-- **The global sections functor `Γ(AffineCris(X/S), -)`** of abelian sheaves on the affine
crystalline site. -/
abbrev affineGlobalSections :
    Sheaf (affineTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.Γ (affineTopology S) AddCommGrpCat.{u + 1}

/-- Global sections of abelian sheaves on the affine crystalline site form an additive functor. -/
instance instAdditiveAffineGlobalSections : (affineGlobalSections S).Additive :=
  Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1, u, u + 1} (affineTopology S)

/-- **The `j`-th cohomology functor `H^j(AffineCris(X/S), -)`** of abelian sheaves on the affine
crystalline site: the `Ext`-groups in degree `j` out of the constant sheaf on `ℤ`. -/
def affineCohomologyFunctor (j : ℕ) :
    Sheaf (affineTopology S) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.functorH.{u + 1, u + 1, u, u + 1} (affineTopology S) j

/-- **The cohomology group `H^j(AffineCris(X/S), F)`** of an abelian sheaf on the affine
crystalline site. -/
abbrev affineCohomology (F : Sheaf (affineTopology S) AddCommGrpCat.{u + 1}) (j : ℕ) :
    Type (u + 1) :=
  Sheaf.H.{u + 1, u + 1} F j

/-- **Cohomology on the affine crystalline site is the right derived functor of its global
sections**, `R^j Γ(AffineCris(X/S), -) ≅ H^j(AffineCris(X/S), -)`. -/
def affineRightDerivedGlobalSectionsIso (j : ℕ) :
    (affineGlobalSections S).rightDerived j ≅ affineCohomologyFunctor S j :=
  Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u, u + 1}
    (affineTopology S) j

/-- **Restriction to the affine crystalline site does not change cohomology.**  For every degree
`j`,

`H^j(AffineCris(X/S), F|_{AffineCris(X/S)}) ≅ H^j(Cris(X/S), F)`

naturally in the abelian sheaf `F` on the small crystalline site. -/
def affineCohomologyFunctorIso (j : ℕ) :
    restrictToAffine S ⋙ affineCohomologyFunctor S j ≅ cohomologyFunctor S j :=
  Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence.{u + 1, u, u + 1}
    (affineTopology S) (smallTopology S) (affineι S) j

/-- **The cohomology of an abelian sheaf on the small crystalline site is the cohomology of its
restriction to the affine crystalline site**, the isomorphism of `affineCohomologyFunctorIso` at a
fixed sheaf. -/
def affineCohomologyIso (F : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) (j : ℕ) :
    (affineCohomologyFunctor S j).obj ((restrictToAffine S).obj F) ≅
      (cohomologyFunctor S j).obj F :=
  (affineCohomologyFunctorIso S j).app F

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
