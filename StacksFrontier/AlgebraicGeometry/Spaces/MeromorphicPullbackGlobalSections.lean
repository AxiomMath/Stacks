module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackModuleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSheafifyForgetHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleDirectImageGlobalSections

/-!
# The global pullback map on meromorphic sections

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` for which pullbacks of
meromorphic functions are defined (Stacks 0EN8) and let `M` be a sheaf of `𝒪_Y`-modules on the
small étale site of `Y`.  Stacks 0ENC, part (1) asserts a canonical map

`Γ(Y, 𝒦_Y(M)) ⟶ Γ(X, 𝒦_X(f^*M))`

on global meromorphic sections.  This file constructs it, with the sheaf `𝒦(M)` of meromorphic
sections spelled as Stacks 0EN5 describes it: the sheafification of the presheaf of sectionwise
localizations `U ↦ 𝒮(U)⁻¹M(U)`.

The construction is the chartwise fraction rule `m/b ↦ (f^*m)/(f^♯b)` of
`AlgebraicGeometry.Space.chartPullbackMeromorphicSections`, carried in three steps:

* the descent of Stacks 03G4 turns the `f`-map of the fraction rule into a morphism of
  presheaves on the small étale site of `Y`, from the sectionwise localizations of `M` into the
  direct image of the sheafification of the sectionwise localizations of `f^*M`
  (`AlgebraicGeometry.Space.meromorphicSectionsDescendedHom`);
* the target is a sheaf, so that morphism extends over the sheafification of the source
  (`AlgebraicGeometry.Space.sheafifyForgetHomEquiv`);
* the global sections of a direct image are the global sections of the sheaf
  (`AlgebraicGeometry.Space.equivSectionsSpacesDirectImage`).

## Main definitions

* `AlgebraicGeometry.Space.regularSectionsLocalizationModuleUp` and
  `AlgebraicGeometry.Space.regularSectionsLocalizationModuleSheafSet` are the presheaf of
  sectionwise localizations at the universe of the objects of the small étale site and its
  sheafification, read as a sheaf of sets.
* `AlgebraicGeometry.Space.pullbackSheafifiedRegularSections` is the global pullback map.

## Implementation notes

The source and target are the sections of the sheafification of the sectionwise localizations,
which is the sheaf of meromorphic sections *as Stacks 0EN5 describes it*.  It is **not** the
Lean object `AlgebraicGeometry.Space.MeromorphicSection`, which realizes Stacks 0EN5 through the
other description in that tag, the extension of scalars `M ⊗_{𝒪} 𝒦` along `𝒪 ⟶ 𝒦` followed by
sheafification.  The two agree by Stacks 0EMD — the canonical morphism
`M ⊗_{𝒪} 𝒮⁻¹𝒪 ⟶ M ⊗_{𝒪} 𝒦` is a local isomorphism, so the two sheafifications coincide — and
that identification is not proved here.  So the map of this file is the global map of
Stacks 0ENC, part (1) for the first description only; part (1) for the second is
`AlgebraicGeometry.Space.pullbackMeromorphicSection`
(`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionGlobalPullback.lean`), which runs the
same three steps over the *sheaf* `𝒦` rather than over the presheaf of sectionwise
localizations and therefore needs Stacks 0EMD no more than this one does.  Part (2), which is
stated through `AlgebraicGeometry.Space.IsRegularMeromorphicSection`, is not asserted here; it is
proved, for an invertible module and over that other description, by
`AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection`.

The sheaf on the small étale site of `X` that the `f`-map is descended against is presented as
the restriction of a spaces-étale sheaf by the comparison equivalence of Stacks 03G1, through
`CategoryTheory.Functor.objPreimage` of
`AlgebraicGeometry.Space.comparisonRestriction`; this is the same presentation
`AlgebraicGeometry.Space.fMapEquivPushforwardHom` uses, and
`AlgebraicGeometry.Space.descendedHom_map` is what makes the result independent of it.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 0EMD](https://stacks.math.columbia.edu/tag/0EMD)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf of abelian groups of sectionwise localizations `𝒮_F⁻¹M` of a sheaf of
`𝒪_F`-modules, lifted to the universe of the objects of the small étale site: the universe in
which that site admits sheafification of presheaves of abelian groups, by
`AlgebraicGeometry.Space.objUniverseHasWeakSheafify`.

Forgetting the abelian group structure gives
`AlgebraicGeometry.Space.regularSectionsLocalizationModuleSetUp`, the presheaf of sets the
chartwise fraction rule is an `f`-map of. -/
noncomputable abbrev regularSectionsLocalizationModuleUp
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (regularSectionsLocalizationModule B S hS F hF M).presheaf ⋙
    AddCommGrpCat.uliftFunctor.{u + 1}

/-- **The sheaf of meromorphic sections as Stacks 0EN5 describes it**, read as a sheaf of sets:
the sheafification of the presheaf of sectionwise localizations `U ↦ 𝒮_F(U)⁻¹M(U)`, with the
abelian group structure forgotten.

This is a sheaf of sets because the forgetful functor of `AddCommGrpCat` preserves limits, so it
carries sheaves of abelian groups to sheaves of sets. -/
noncomputable abbrev regularSectionsLocalizationModuleSheafSet
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) :
    Sheaf (SmallEtale.topology B S hS F) (Type (u + 1)) :=
  (sheafCompose (SmallEtale.topology B S hS F)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
    ((presheafToSheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1}).obj
      (regularSectionsLocalizationModuleUp B S hS F hF M))

section GlobalMap

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search through sheafification and the small étale ringed topoi of `X` and `Y` is heavy
/-- **Stacks 0ENC, part (1), for the sheafification of the sectionwise localizations.**  When
pullbacks of meromorphic functions are defined for `f`, there is a canonical map on global
sections

`Γ(Y, 𝒦_Y(M)) ⟶ Γ(X, 𝒦_X(f^*M))`

with the sheaf of meromorphic sections taken as Stacks 0EN5 describes it, the sheafification of
the presheaf of sectionwise localizations `U ↦ 𝒮(U)⁻¹M(U)`.

It is the chartwise fraction rule `m/b ↦ (f^*m)/(f^♯b)` of
`AlgebraicGeometry.Space.chartPullbackMeromorphicSections`, carried along three identifications:
the descent of Stacks 03G4 for a presheaf of sections on the target
(`AlgebraicGeometry.Space.meromorphicSectionsDescendedHom`), the extension of a morphism into a
sheaf over the sheafification of its source
(`AlgebraicGeometry.Space.sheafifyForgetHomEquiv`), and the identification of the global
sections of a direct image with those of the sheaf
(`AlgebraicGeometry.Space.equivSectionsSpacesDirectImage`).

Only the additive structure of the sectionwise localizations is used, so the map is produced on
the underlying sets; it is a map of sets of global sections and is not here asserted to be
additive. -/
@[stacks 0ENC "part (1), for the first of the two descriptions of the sheaf of meromorphic \
sections in Stacks 0EN5: the global map Γ(Y, 𝒦_Y(F)) ⟶ Γ(X, 𝒦_X(f^*F)) with 𝒦(F) taken to be \
the sheafification of the presheaf of sectionwise localizations U ↦ 𝒮(U)⁻¹F(U). The same map \
for AlgebraicGeometry.Space.MeromorphicSection, which realizes Stacks 0EN5 through the other \
description there, the sheafification of the extension of scalars F ⊗_𝒪 𝒦, is \
AlgebraicGeometry.Space.pullbackMeromorphicSection. Stacks 0EMD, which identifies the two \
descriptions, is not proved and neither map uses it. Additivity of the map \
is not asserted, and neither is part (2), which is stated through \
AlgebraicGeometry.Space.IsRegularMeromorphicSection and proved for an invertible module by \
AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection"]
noncomputable def pullbackSheafifiedRegularSections
    (hf : PullbacksMeromorphicSections B S hS f.hom) :
    (regularSectionsLocalizationModuleSheafSet B S hS Y.1 Y.2 M).obj.sections →
      (regularSectionsLocalizationModuleSheafSet B S hS X.1 X.2
        ((modulePullback B S hS f).obj M)).obj.sections :=
  let FX := regularSectionsLocalizationModuleSheafSet B S hS X.1 X.2
    ((modulePullback B S hS f).obj M)
  let H := (comparisonRestriction B S hS X).objPreimage FX
  let i := ((comparisonRestriction B S hS X).objObjPreimageIso FX).symm
  let α : regularSectionsLocalizationModuleSetUp B S hS X.1 X.2
      ((modulePullback B S hS f).obj M) ⟶ FX.obj :=
    Functor.whiskerRight (toSheafify (SmallEtale.topology B S hS X.1)
      (regularSectionsLocalizationModuleUp B S hS X.1 X.2
        ((modulePullback B S hS f).obj M)))
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let Ψ := (sheafifyForgetHomEquiv B S hS Y.1
      (regularSectionsLocalizationModuleUp B S hS Y.1 Y.2 M)
      ((spacesDirectImageRestriction B S hS f).obj H)).symm
    (meromorphicSectionsDescendedHom B S hS f M hf FX H i α)
  fun s ↦
    ((Functor.sectionsFunctor _).map i.inv.hom)
      (equivSectionsSpacesDirectImage B S hS f H
        (((Functor.sectionsFunctor _).map Ψ) s))

end GlobalMap

end AlgebraicGeometry.Space

end
