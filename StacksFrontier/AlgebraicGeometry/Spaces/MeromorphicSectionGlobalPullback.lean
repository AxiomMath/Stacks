module

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackModuleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionsChartPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSheafifyForgetHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleDirectImageGlobalSections
import StacksCore.Tactic.StacksAttribute

/-!
# The global pullback map on meromorphic sections

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` for which pullbacks of
meromorphic functions are defined (Stacks 0EN8) and let `M` be a sheaf of `𝒪_Y`-modules on the
small étale site of `Y`.  Stacks 0ENC, part (1) asserts a canonical map

`Γ(Y, 𝒦_Y(M)) ⟶ Γ(X, 𝒦_X(f^*M))`

on global meromorphic sections.  This file constructs it on
`AlgebraicGeometry.Space.MeromorphicSection` itself — the sheaf `𝒦(M)` of meromorphic sections
being `AlgebraicGeometry.Space.meromorphicSectionSheaf`, the sheafification of the extension of
scalars `M ⊗_{𝒪} 𝒦` along `𝒪 ⟶ 𝒦`, which is the description of Stacks 0EN5 that Stacks 0ENB's
regularity and hence part (2) use.

The construction is the chartwise rule `m ⊗ a ↦ (f^*m) ⊗ (f^♯a)` of
`AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf`, carried in three steps, exactly
as `AlgebraicGeometry.Space.pullbackSheafifiedRegularSections` carries the corresponding rule on
the presheaves of sectionwise localizations:

* the descent of Stacks 03G4 turns the `f`-map of the chartwise rule into a morphism of
  presheaves on the small étale site of `Y`, from `M ⊗_{𝒪_Y} 𝒦_Y` into the direct image of the
  sheafification of `(f^*M) ⊗_{𝒪_X} 𝒦_X`
  (`AlgebraicGeometry.Space.meromorphicSectionSheafDescendedHom`);
* the target is a sheaf, so that morphism extends over the sheafification of the source
  (`AlgebraicGeometry.Space.sheafifyForgetHomEquiv`);
* the global sections of a direct image are the global sections of the sheaf
  (`AlgebraicGeometry.Space.equivSectionsSpacesDirectImage`).

## Main definitions

* `AlgebraicGeometry.Space.meromorphicSectionModuleUp` and
  `AlgebraicGeometry.Space.meromorphicSectionModuleSetUp` are the presheaf `M ⊗_{𝒪} 𝒦` at the
  universe of the objects of the small étale site, as a presheaf of abelian groups and of sets.
* `AlgebraicGeometry.Space.fmapMeromorphicSectionsSheafUp` is the `f`-map of
  `AlgebraicGeometry.Space.fmapMeromorphicSectionsSheaf` in that universe.
* `AlgebraicGeometry.Space.pullbackMeromorphicSection` is the global pullback map.

## Implementation notes

The source and target are `AlgebraicGeometry.Space.MeromorphicSection` on the nose: the
sheafification of presheaves of modules of
`AlgebraicGeometry.Space.meromorphicSectionSheaf` has for its underlying presheaf of abelian
groups the `AddCommGrpCat`-sheafification of `M ⊗_{𝒪} 𝒦` lifted to the universe of the objects
of the site, so the module of global sections of the one is the set of global sections of the
other, and no comparison of the two sheafifications is needed.

Only the additive structure of `M ⊗_{𝒪} 𝒦` is used, so the map is produced on the underlying
sets; it is a map of sets of global sections.  That it is additive and `𝒦`-semilinear is
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_add` and
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_smul_chartDiagram`, proved from the
value of the map over a commuting square of étale charts; global additivity against the group
structure on global sections is `AlgebraicGeometry.Space.pullbackMeromorphicSection_add`, bundled
as `AlgebraicGeometry.Space.pullbackMeromorphicSectionAddHom`.

The sheaf on the small étale site of `X` that the `f`-map is descended against is presented as
the restriction of a spaces-étale sheaf by the comparison equivalence of Stacks 03G1, through
`CategoryTheory.Functor.objPreimage` of
`AlgebraicGeometry.Space.comparisonRestriction`, as in
`AlgebraicGeometry.Space.pullbackSheafifiedRegularSections`;
`AlgebraicGeometry.Space.descendedHom_map` is what makes the result independent of that choice.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The presheaf of abelian groups `M ⊗_{𝒪_F} 𝒦_F` of meromorphic sections of a sheaf of
`𝒪_F`-modules, lifted to the universe of the objects of the small étale site: the universe in
which that site admits sheafification of presheaves of abelian groups, and the one
`AlgebraicGeometry.Space.meromorphicSectionPresheaf` lifts its own extension of scalars to. -/
noncomputable abbrev meromorphicSectionModuleUp
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (meromorphicSectionModule B S hS F hF M).presheaf ⋙ AddCommGrpCat.uliftFunctor.{u + 1}

/-- The presheaf of sets underlying `M ⊗_{𝒪_F} 𝒦_F` at the universe of the objects of the small
étale site: the presheaf the chartwise rule is an `f`-map of. -/
noncomputable abbrev meromorphicSectionModuleSetUp
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) : (SmallEtale B S hS F)ᵒᵖ ⥤ Type (u + 1) :=
  meromorphicSectionModuleUp B S hS F hF M ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}

/-- **The sheaf `𝒦_F(M)` of meromorphic sections, read as a sheaf of sets.**  Its global sections
are `AlgebraicGeometry.Space.MeromorphicSection` on the nose: the sheafification of presheaves
of modules used by `AlgebraicGeometry.Space.meromorphicSectionSheaf` has for its underlying
presheaf of abelian groups the sheafification of `M ⊗_{𝒪_F} 𝒦_F`. -/
noncomputable abbrev meromorphicSectionSheafSet
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) :
    Sheaf (SmallEtale.topology B S hS F) (Type (u + 1)) :=
  (sheafCompose (SmallEtale.topology B S hS F)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
    ((presheafToSheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{u + 1}).obj
      (meromorphicSectionModuleUp B S hS F hF M))

/-- The global sections of the sheaf of meromorphic sections read as a sheaf of sets are the
meromorphic sections of Stacks 0EN5. -/
theorem meromorphicSection_eq_sheafSet_sections
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (M : Modules.{u, u} B S hS F hF) :
    MeromorphicSection.{u, u} B S hS F hF M =
      (meromorphicSectionSheafSet B S hS F hF M).obj.sections :=
  rfl

section GlobalMap

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
  (hf : PullbacksMeromorphicSections B S hS f.hom)

/-- **The chartwise rule as an `f`-map at the universe of the objects of the site.**  The `f`-map
`AlgebraicGeometry.Space.fmapMeromorphicSectionsSheaf` of the presheaves `M ⊗_{𝒪} 𝒦`, lifted
from the universe of the structure rings to the universe of the objects of the two étale sites,
which is where the descent of Stacks 03G4 is instantiated. -/
noncomputable def fmapMeromorphicSectionsSheafUp :
    FMap B S hS X.1 Y.1 f.hom
      (meromorphicSectionModuleSetUp B S hS X.1 X.2 ((modulePullback B S hS f).obj M))
      (meromorphicSectionModuleSetUp B S hS Y.1 Y.2 M) where
  app d s := ULift.up (chartPullbackMeromorphicSectionsSheaf B S hS f M hf d s.down)
  naturality d d' i j h s :=
    congrArg ULift.up
      (chartPullbackMeromorphicSectionsSheaf_comp B S hS f M hf d d' i j h s.down)

/-- **The chartwise rule descends to a morphism into a direct image.**  Let `G` be a sheaf of
sets on the small étale site of `X` presented as the restriction of a spaces-étale sheaf `H`,
and let `M ⊗_{𝒪_X} 𝒦_X` for `f^*M` map to `G` — for instance by a sheafification.  Then the
rule `m ⊗ a ↦ (f^*m) ⊗ (f^♯a)` becomes a morphism of presheaves on the small étale site of `Y`
from `M ⊗_{𝒪_Y} 𝒦_Y` into the direct image of `H`. -/
noncomputable def meromorphicSectionSheafDescendedHom
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)))
    (H : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
    (i : G ≅ (comparisonRestriction B S hS X).obj H)
    (α : meromorphicSectionModuleSetUp B S hS X.1 X.2
      ((modulePullback B S hS f).obj M) ⟶ G.obj) :
    meromorphicSectionModuleSetUp B S hS Y.1 Y.2 M ⟶
      ((spacesDirectImageRestriction B S hS f).obj H).obj :=
  descendedHomPresheaf B S hS f G _ H i
    (FMap.compSource B S hS f (fmapMeromorphicSectionsSheafUp B S hS f M hf) α)

set_option synthInstance.maxHeartbeats 400000 in
-- instance synthesis through the sheafification and direct-image functors is slow
/-- **Stacks 0ENC, part (1).**  When pullbacks of meromorphic functions are defined for `f`,
there is a canonical map on global meromorphic sections

`Γ(Y, 𝒦_Y(M)) ⟶ Γ(X, 𝒦_X(f^*M))`

with `𝒦(M)` the sheaf of meromorphic sections of Stacks 0EN5,
`AlgebraicGeometry.Space.meromorphicSectionSheaf`, and a meromorphic section a global section of
it, `AlgebraicGeometry.Space.MeromorphicSection`.

It is the chartwise rule `m ⊗ a ↦ (f^*m) ⊗ (f^♯a)` of
`AlgebraicGeometry.Space.chartPullbackMeromorphicSectionsSheaf`, carried along three
identifications: the descent of Stacks 03G4 for a presheaf of sections on the target
(`AlgebraicGeometry.Space.meromorphicSectionSheafDescendedHom`), the extension of a morphism
into a sheaf over the sheafification of its source
(`AlgebraicGeometry.Space.sheafifyForgetHomEquiv`), and the identification of the global
sections of a direct image with those of the sheaf
(`AlgebraicGeometry.Space.equivSectionsSpacesDirectImage`).

Only the additive structure of `M ⊗_{𝒪} 𝒦` is used, so the map is produced on the underlying
sets and nothing in the construction is a map of abelian groups.  That it is nonetheless
additive and `𝒦`-semilinear is
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_add` and
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_smul_chartDiagram`, proved from its
values; `AlgebraicGeometry.Space.pullbackMeromorphicSection_add` is global additivity against
the group structure on global sections. -/
@[stacks 0ENC "part (1): the global map Γ(Y, 𝒦_Y(F)) ⟶ Γ(X, 𝒦_X(f^*F)) on \
AlgebraicGeometry.Space.MeromorphicSection, the meromorphic sections of Stacks 0EN5 as the \
library spells them -- global sections of the sheafification of F ⊗_𝒪 𝒦. \
AlgebraicGeometry.Space.pullbackSheafifiedRegularSections is the same map for the other \
description in Stacks 0EN5, the sheafification of the presheaf of sectionwise localizations. \
Additivity and semilinearity of this map are \
AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_add and \
AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_smul_chartDiagram, and global \
additivity is AlgebraicGeometry.Space.pullbackMeromorphicSection_add; part (2) for an \
invertible module is \
AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection"]
noncomputable def pullbackMeromorphicSection :
    MeromorphicSection.{u, u} B S hS Y.1 Y.2 M →
      MeromorphicSection.{u, u} B S hS X.1 X.2 ((modulePullback B S hS f).obj M) :=
  let GX := meromorphicSectionSheafSet B S hS X.1 X.2 ((modulePullback B S hS f).obj M)
  let H := (comparisonRestriction B S hS X).objPreimage GX
  let i := ((comparisonRestriction B S hS X).objObjPreimageIso GX).symm
  let α : meromorphicSectionModuleSetUp B S hS X.1 X.2
      ((modulePullback B S hS f).obj M) ⟶ GX.obj :=
    Functor.whiskerRight (toSheafify (SmallEtale.topology B S hS X.1)
      (meromorphicSectionModuleUp B S hS X.1 X.2 ((modulePullback B S hS f).obj M)))
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let Ψ := (sheafifyForgetHomEquiv B S hS Y.1
      (meromorphicSectionModuleUp B S hS Y.1 Y.2 M)
      ((spacesDirectImageRestriction B S hS f).obj H)).symm
    (meromorphicSectionSheafDescendedHom B S hS f M hf GX H i α)
  fun s ↦
    ((Functor.sectionsFunctor _).map i.inv.hom)
      (equivSectionsSpacesDirectImage B S hS f H
        (((Functor.sectionsFunctor _).map Ψ) s))

end GlobalMap

end AlgebraicGeometry.Space

end
