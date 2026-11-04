module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartCorrespondence

/-!
# The chartwise pullback of meromorphic sections as a map into a direct image

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` for which pullbacks of
meromorphic functions are defined (Stacks 0EN8) and let `M` be a sheaf of `𝒪_Y`-modules on the
small étale site of `Y`.  The fraction rule `m/b ↦ (f^*m)/(f^♯b)` of
`AlgebraicGeometry.Space.fmapMeromorphicSections` is an `f`-map of Stacks 03G3 between the
presheaves of sectionwise localizations.  This file carries it through the descent of
Stacks 03G4: the rule becomes a morphism of *presheaves* on the small étale site of `Y` from
`𝒮_Y⁻¹M` into the direct image of any sheaf on the small étale site of `X` that the sectionwise
localizations map to.

## Main definitions

* `AlgebraicGeometry.Space.regularSectionsLocalizationModuleSetUp` is the presheaf of sets
  underlying `𝒮_F⁻¹M`, lifted to the universe of the objects of the small étale site — the
  universe in which that site admits sheafification of presheaves of modules, and the one
  `AlgebraicGeometry.Space.meromorphicSectionPresheaf` lifts its own extension of scalars to.
* `AlgebraicGeometry.Space.fmapMeromorphicSectionsSetUp` is
  `AlgebraicGeometry.Space.fmapMeromorphicSections` in that universe.
* `AlgebraicGeometry.Space.meromorphicSectionsDescendedHom` is the morphism of presheaves into
  the direct image that the fraction rule descends to.

## Implementation notes

The universe lift is needed because the `f`-map lives at the universe `u` of the structure
rings, where the inverse image of modules of Stacks 03LU lives, while the descent of
Stacks 03G4, `AlgebraicGeometry.Space.descendedHomPresheaf`, is instantiated at `Type (u + 1)`,
the universe of the objects of the two étale sites.  It is
performed on the presheaf of sets rather than on the presheaf of abelian groups because the
descent is a statement about sheaves of sets.

The descent used is `AlgebraicGeometry.Space.descendedHomPresheaf`: the sectionwise
localizations are a presheaf and not a sheaf, so the bijection of Stacks 03G4 itself does not
apply to them, only the construction of the map.  The target is a sheaf, so the morphism
extends over any sheafification of the sectionwise localizations; carrying that out is
`AlgebraicGeometry.Space.pullbackSheafifiedRegularSections`, the global map of Stacks 0ENC,
part (1) for the first of the two descriptions of `𝒦(M)` in Stacks 0EN5.  The same chain run
over the *sheaf* `𝒦` rather than the presheaf of sectionwise localizations gives part (1) for
the other description, `AlgebraicGeometry.Space.pullbackMeromorphicSection`.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf of sets underlying the sectionwise localizations `𝒮_F⁻¹M` of a sheaf of
`𝒪_F`-modules, lifted to the universe of the objects of the small étale site.  The lift is the
one `AlgebraicGeometry.Space.meromorphicSectionPresheaf` applies to its own extension of
scalars. -/
noncomputable abbrev regularSectionsLocalizationModuleSetUp
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) : (SmallEtale B S hS F)ᵒᵖ ⥤ Type (u + 1) :=
  (regularSectionsLocalizationModule B S hS F hF M).presheaf ⋙
    AddCommGrpCat.uliftFunctor.{u + 1} ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}

section Descent

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)

/-- **The local fraction rule as an `f`-map at the universe of the objects of the site.**  The
`f`-map `AlgebraicGeometry.Space.fmapMeromorphicSections` of the sectionwise localizations,
lifted from the universe of the structure rings to the universe of the objects of the two étale
sites, which is where the descent of Stacks 03G4 is instantiated. -/
noncomputable def fmapMeromorphicSectionsSetUp
    (hf : PullbacksMeromorphicSections B S hS f.hom) :
    FMap B S hS X.1 Y.1 f.hom
      (regularSectionsLocalizationModuleSetUp B S hS X.1 X.2
        ((modulePullback B S hS f).obj M))
      (regularSectionsLocalizationModuleSetUp B S hS Y.1 Y.2 M) where
  app d s := ULift.up (chartPullbackMeromorphicSections B S hS f M hf d s.down)
  naturality d d' i j h s :=
    congrArg ULift.up (chartPullbackMeromorphicSections_comp B S hS f M hf d d' i j h s.down)

/-- **The fraction rule descends to a morphism into a direct image.**  Let `F` be a sheaf of
sets on the small étale site of `X` presented as the restriction of a spaces-étale sheaf `H`,
and let the sectionwise localizations of `f^*M` map to `F` — for instance by a sheafification.
Then the fraction rule `m/b ↦ (f^*m)/(f^♯b)` becomes a morphism of presheaves on the small
étale site of `Y` from the sectionwise localizations of `M` into the direct image of `H`.

This is the descent of Stacks 03G4 applied to
`AlgebraicGeometry.Space.fmapMeromorphicSectionsSetUp`, in the form
`AlgebraicGeometry.Space.descendedHomPresheaf` that does not ask the presheaf of sections on `Y`
to be a sheaf — the sectionwise localizations are not one. -/
noncomputable def meromorphicSectionsDescendedHom
    (hf : PullbacksMeromorphicSections B S hS f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
    (i : F ≅ (comparisonRestriction B S hS X).obj H)
    (α : regularSectionsLocalizationModuleSetUp B S hS X.1 X.2
      ((modulePullback B S hS f).obj M) ⟶ F.obj) :
    regularSectionsLocalizationModuleSetUp B S hS Y.1 Y.2 M ⟶
      ((spacesDirectImageRestriction B S hS f).obj H).obj :=
  descendedHomPresheaf B S hS f F _ H i
    (FMap.compSource B S hS f (fmapMeromorphicSectionsSetUp B S hS f M hf) α)

/-- The descended morphism on a section over an étale scheme chart `U` of `X` above the
cartesian base change of a chart `V` of `Y`: it is the fraction rule of the chart diagram that
arrow determines, followed by the presentation of `F`. -/
theorem meromorphicSectionsDescendedHom_restrict
    (hf : PullbacksMeromorphicSections B S hS f.hom)
    (F : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
    (i : F ≅ (comparisonRestriction B S hS X).obj H)
    (α : regularSectionsLocalizationModuleSetUp B S hS X.1 X.2
      ((modulePullback B S hS f).obj M) ⟶ F.obj)
    (U : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (k : (comparisonFunctor B S hS X).obj U ⟶ chartBaseChange B S hS f V)
    (s : (regularSectionsLocalizationModuleSetUp B S hS Y.1 Y.2 M).obj (op V)) :
    H.obj.map k.op
        ((meromorphicSectionsDescendedHom B S hS f M hf F H i α).app (op V) s) =
      i.hom.hom.app (op U) (α.app (op U) (ULift.up
        (chartPullbackMeromorphicSections B S hS f M hf
          (chartDiagramOfBaseChangeArrow B S hS f U V k) s.down))) :=
  descendedSection_restrict B S hS f F _ H i
    (FMap.compSource B S hS f (fmapMeromorphicSectionsSetUp B S hS f M hf) α) U V k s

end Descent

end AlgebraicGeometry.Space

end
