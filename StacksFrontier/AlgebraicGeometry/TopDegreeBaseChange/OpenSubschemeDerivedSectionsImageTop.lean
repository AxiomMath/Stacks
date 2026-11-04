module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedSectionsModelCrossing
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphismExactFunctor

/-!
# Derived sections over `U.ι ''ᵁ ⊤` against derived sections over `U`

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.sectionsOnImageTopNatIso` identifies the degreewise
sections functors of an open `U` of a scheme `X` read at the two opens `U.ι ''ᵁ ⊤` and `U` — the
first being the open the open subscheme's own global sections live over, the second the open itself
— with the scalars crossed by `AlgebraicGeometry.Scheme.Opens.topIso`. Its derived form existed
only for Mathlib's classical `CategoryTheory.Functor.rightDerived`, as
`…TopDegreeBaseChange.sectionsOnImageTopDerivedIso`. This file gives it on the **unbounded**
derived category, which is the model the tail of conclusion (c) of [Stacks, Tag 0EX3] speaks in.

Both sides are right derived functors of isomorphic degreewise functors along the same localization
`DerivedCategory.Qh`, so the comparison is Mathlib's `CategoryTheory.Functor.rightDerivedNatIso`
once the right-hand side has been exhibited as a right derived functor — which it is, by one
application of the general brick
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit`, restriction of
scalars being exact.

Nothing is assumed of `X`, of `U` or of the module.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.imageTopRestrictScalarsOf` — restriction of scalars
  along `AlgebraicGeometry.Scheme.Opens.topIso` at `U`, with its source and target *declared* at
  the `structureSheafRing` spellings of the two rings. The ascription is not cosmetic, see the
  implementation notes.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.imageTopCompUnit` — the unit exhibiting
  `RΓ(U.ι ''ᵁ ⊤, -)` followed by that restriction of scalars as a right derived functor of the
  degreewise composite.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.sectionsImageTopNatIsoOf` —
  `sectionsOnImageTopNatIso` read at that spelling; the two are equal by `rfl`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedSectionsImageTopIso` — **the crossing**:
  `RΓ(U.ι ''ᵁ ⊤, -) ⋙ res_{topIso} ≅ RΓ(U, -)` on the unbounded derived categories.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isRightDerivedFunctor_imageTopCompUnit`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedSectionsImageTopIso_hom_app_unit` — the
  equation that characterizes the crossing: composed with the unit of the left-hand model it is the
  degreewise isomorphism on the homotopy category followed by the unit of `RΓ(U, -)`.

## Implementation notes

*Why the restriction of scalars is re-declared with ascribed source and target.* The functor
`ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom` presents its two rings as
`X.presheaf.obj (op U)` and `(U : Scheme).presheaf.obj (op ⊤)`, while
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤)` presents its
value category as `ModuleCat ((structureSheafRing X.toRingedSpace).obj.obj (op (U.ι ''ᵁ ⊤)))`. The
two are `rfl`-equal, and each functor's own `CategoryTheory.Functor.Additive` instance is found
standing alone — but `CategoryTheory.Functor.instAdditiveComp` is keyed on the intermediate
category, so the **composite** is reported as a missing `Functor.Additive` instance, at both the
`sectionsOverOpen` and the `AlgebraicGeometry.sectionsOn` spelling of the first factor. Hence
`imageTopRestrictScalarsOf` is a `def` whose *declared* source and target carry the wanted
spellings, with the three exactness instances carried over by `inferInstanceAs` in term mode, where
the conversion runs at default transparency. It is deliberately not an `abbrev`.

*No `@[stacks …]` attribute is placed.* Conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere,
as `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`),
by a route that does not use this file, and nothing here is a tagged statement of the Stacks
project.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (exists_quasiIso_isKInjective)
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison
  (exactPostcomposeUnit isRightDerivedFunctor_exactPostcomposeUnit)
open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen derivedSectionsOverOpen derivedSectionsOverOpenUnit)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable (X : Scheme.{u}) (U : X.Opens)

/-! ### Restriction of scalars along `topIso`, at the `structureSheafRing` spellings -/

/-- **Restriction of scalars along `AlgebraicGeometry.Scheme.Opens.topIso` at `U`**, from modules
over `Γ(U.ι ''ᵁ ⊤, 𝒪_X)` to modules over `Γ(U, 𝒪_X)`, both rings spelled through
`structureSheafRing`.

This is `ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom` and nothing else; the
ascription is forced by instance synthesis for the composite below, see this module's
implementation notes. -/
def imageTopRestrictScalarsOf :
    ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op (U.ι ''ᵁ ⊤))) ⥤
      ModuleCat.{u} ((structureSheafRing X.toRingedSpace).obj.obj (op U)) :=
  ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom

/-- Restriction of scalars along `topIso` is additive. -/
instance imageTopRestrictScalarsOf_additive : (imageTopRestrictScalarsOf X U).Additive :=
  inferInstanceAs ((ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom).Additive)

/-- Restriction of scalars along `topIso` is left exact. -/
instance imageTopRestrictScalarsOf_preservesFiniteLimits :
    PreservesFiniteLimits (imageTopRestrictScalarsOf X U) :=
  inferInstanceAs (PreservesFiniteLimits
    (ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom))

/-- Restriction of scalars along `topIso` is right exact. -/
instance imageTopRestrictScalarsOf_preservesFiniteColimits :
    PreservesFiniteColimits (imageTopRestrictScalarsOf X U) :=
  inferInstanceAs (PreservesFiniteColimits
    (ModuleCat.restrictScalars (Scheme.Opens.topIso U).inv.hom))

/-- **The degreewise crossing at the ascribed spelling.** `sectionsOnImageTopNatIso` and nothing
else: sections over `U.ι ''ᵁ ⊤` read over `Γ(U, 𝒪_X)` are sections over `U`. -/
def sectionsImageTopNatIsoOf :
    sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙ imageTopRestrictScalarsOf X U ≅
      sectionsOverOpen X.toRingedSpace U :=
  sectionsOnImageTopNatIso X U

/-! ### The second model, and the crossing -/

/-- **The unit exhibiting `RΓ(U.ι ''ᵁ ⊤, -)` followed by restriction of scalars as a right derived
functor** of the degreewise composite. One application of
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit`, at the pair
`(Γ(U.ι ''ᵁ ⊤, -), res_{topIso})`, the second factor being exact. -/
def imageTopCompUnit :
    (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
          imageTopRestrictScalarsOf X U).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        (imageTopRestrictScalarsOf X U).mapDerivedCategory :=
  exactPostcomposeUnit (sectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
    (imageTopRestrictScalarsOf X U)
    (derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤))
    (derivedSectionsOverOpenUnit X.toRingedSpace (U.ι ''ᵁ ⊤))

/-- `imageTopCompUnit` does exhibit a right derived functor: the general brick
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.isRightDerivedFunctor_exactPostcomposeUnit`, with the K-injective resolutions on `X` supplied by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective`. -/
instance isRightDerivedFunctor_imageTopCompUnit :
    (derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        (imageTopRestrictScalarsOf X U).mapDerivedCategory).IsRightDerivedFunctor
      (imageTopCompUnit X U)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_exactPostcomposeUnit _ _ _ _ (exists_quasiIso_isKInjective X.toRingedSpace)

/-- **The crossing of the two unbounded derived sections functors.** Unbounded derived sections
over `U.ι ''ᵁ ⊤` on `X`, read over `Γ(U, 𝒪_X)` through
`AlgebraicGeometry.Scheme.Opens.topIso`, are unbounded derived sections over `U`.

Both sides are right derived functors along `DerivedCategory.Qh` of the two degreewise functors
`sectionsImageTopNatIsoOf` identifies, so this is Mathlib's
`CategoryTheory.Functor.rightDerivedNatIso` at that isomorphism read on the homotopy category.
**Nothing is assumed of `X`, of `U` or of the module.** -/
def derivedSectionsImageTopIso :
    derivedSectionsOverOpen X.toRingedSpace (U.ι ''ᵁ ⊤) ⋙
        (imageTopRestrictScalarsOf X U).mapDerivedCategory ≅
      derivedSectionsOverOpen X.toRingedSpace U :=
  Functor.rightDerivedNatIso _ _ (imageTopCompUnit X U)
    (derivedSectionsOverOpenUnit X.toRingedSpace U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ))
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryNatIso (sectionsImageTopNatIsoOf X U) (ComplexShape.up ℤ))
      DerivedCategory.Qh)

/-- **The equation characterizing the crossing, pointwise.** Composing it with the unit of
`RΓ(U.ι ''ᵁ ⊤, -) ⋙ res_{topIso}` is the degreewise crossing read on the homotopy category and
localized, followed by the unit of `RΓ(U, -)`; that equation determines it. -/
theorem derivedSectionsImageTopIso_hom_app_unit
    (L : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (imageTopCompUnit X U).app L ≫
        (derivedSectionsImageTopIso X U).hom.app (DerivedCategory.Qh.obj L) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryNatIso (sectionsImageTopNatIsoOf X U)
            (ComplexShape.up ℤ)).hom.app L) ≫
        (derivedSectionsOverOpenUnit X.toRingedSpace U).app L :=
  Functor.rightDerivedNatTrans_app _ _ (imageTopCompUnit X U)
    (derivedSectionsOverOpenUnit X.toRingedSpace U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (ComplexShape.up ℤ)) _ L

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
