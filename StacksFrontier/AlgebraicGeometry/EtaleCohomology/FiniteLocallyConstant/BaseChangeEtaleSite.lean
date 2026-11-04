module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.BaseChangeRepresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.CategoryTheory.Equivalence.ConjugateSquare

/-!
# Stacks 0DV6 on Mathlib's small étale site

Stacks Tag 0DV6 says that the dictionaries of Tag 0DV5 commute with pullback along a morphism of
connected schemes, the action being reindexed along the induced homomorphism of fundamental
groups. It is proved in `BaseChangeRepresentable.lean` on the small étale site of Stacks 021B,
`AlgebraicGeometry.SmallEtale.topology`. The étale-cohomology files of this library work with
Mathlib's choice-free presentation `AlgebraicGeometry.Scheme.smallEtaleTopology`, which is where
Tag 0DV5 itself was carried in `SmallEtaleSitePresentation.lean`. This file carries Tag 0DV6
across the same comparison, for sheaves of sets and for sheaves of `Λ`-modules over a finite
ring.

## Main definitions

* `AlgebraicGeometry.etaleSiteSheafPullbackType` and
  `AlgebraicGeometry.etaleSiteSheafPullbackModule`: inverse image along base change on Mathlib's
  small étale site, for sheaves of sets and for sheaves of `Λ`-modules.
* `AlgebraicGeometry.etaleSiteFiniteLocallyConstantSheafPullback` and
  `AlgebraicGeometry.etaleSiteFiniteTypeLocallyConstantModuleSheafPullback`: those inverse images
  read on the finite locally constant sheaves of sets and on the finite type locally constant
  sheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.finiteLocallyConstantSheafEquivPullbackIso` and
  `AlgebraicGeometry.finiteTypeLocallyConstantSheafEquivPullbackIso`: the equivalences of the two
  presentations of the small étale site commute with inverse image, on the finite locally
  constant subcategories.
* Stacks Tag 0DV6 for sheaves of sets, on Mathlib's small étale site:
  `AlgebraicGeometry.nonempty_finiteLocallyConstantSetsEquivalenceEtaleSite_pullbackIso`
* Stacks Tag 0DV6 for sheaves of `Λ`-modules over a finite ring, on Mathlib's small étale site:
  `AlgebraicGeometry.nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso`

## Implementation notes

*The ambient square.* The comparison of the two inverse images across the two presentations is
`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`, which takes the two left adjoints
as arguments because a left adjoint of a direct image is determined only up to isomorphism. The
representative chosen here for Mathlib's presentation is the one built by a left Kan extension,
`CategoryTheory.Functor.sheafPullbackConstruction.sheafPullback`, since that is the construction
whose existence is available on `AlgebraicGeometry.Scheme.Etale`; for the presentation of
Stacks 021B it is the abstract `CategoryTheory.Functor.sheafPullback` already used by
`AlgebraicGeometry.finiteLocallyConstantSheafPullback` and
`AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafPullback`.

*That the predicates are preserved.* Inverse image on Mathlib's site preserves finite local
constancy because the ambient square identifies it, after restriction along the embedding, with
inverse image on the site of Stacks 021B, where the preservation is Stacks Tag 093R. This is the
only place the square is used objectwise; `AlgebraicGeometry.sheafEquivInverseSheafPullbackTypeIso`
and `AlgebraicGeometry.sheafEquivInverseSheafPullbackModuleIso` are that reading.

*The descent to the subcategories.* All four functors of the square of subcategories are
`CategoryTheory.ObjectProperty.lift`s, so each composed with the inclusion of the ambient sheaves
is an equality of functors — for the two inverse images by construction, and for the two
horizontal equivalences because the `functor` field of
`CategoryTheory.Equivalence.congrFullSubcategory` is again a lift.
`CategoryTheory.Functor.fullyFaithfulCancelRight` therefore descends the ambient isomorphism to
the subcategories.

*Composing with the dictionary.* Tag 0DV5 on Mathlib's site is the dictionary of Stacks 021B read
through the comparison of subcategories, so Tag 0DV6 on Mathlib's site is Tag 0DV6 on the site of
Stacks 021B joined to the square above with its horizontal edges reversed, which is
`CategoryTheory.Equivalence.conjugateSquare`. Only the existence of the comparison is asserted,
because that is the form in which Tag 0DV6 is available on the site of Stacks 021B.

*What is not here.* Tag 0DV6 for sheaves of abelian groups is not carried across, because Tag
0DV5 part (2) itself is not available on Mathlib's small étale site: the Mathlib-site dictionaries
are `AlgebraicGeometry.finiteLocallyConstantSetsEquivalenceEtaleSite` and
`AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite`, and
`AlgebraicGeometry.finiteLocallyConstantAbelianSheafEquivalence` has no Mathlib-site companion,
so there is no square for it to be a statement about.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 0DV5](https://stacks.math.columbia.edu/tag/0DV5)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ConstantSheaf Stacks.GroupCohomology
open scoped FintypeCatDiscrete

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : Y ⟶ X)

attribute [local instance] ModuleCat.hasLimitsOfSize

/-! ### Sheaves of sets -/

/-- A square of functors commuting up to isomorphism across an equivalence, reversed along the
equivalence and composed with a second commuting square. -/
private theorem nonempty_iso_comp_inverse_of_iso
    {C C' D D' S T : Type*} [Category C] [Category C'] [Category D] [Category D'] [Category S]
    [Category T] (EX : C ≌ C') (EY : D ≌ D') (G : C ⥤ S) (H : D ⥤ T) (P : C ⥤ D) (Q : C' ⥤ D')
    (R : S ⥤ T) (β : EX.functor ⋙ Q ≅ P ⋙ EY.functor) (α : G ⋙ R ≅ P ⋙ H) :
    Nonempty ((EX.inverse ⋙ G) ⋙ R ≅ Q ⋙ EY.inverse ⋙ H) :=
  ⟨Functor.associator EX.inverse G R ≪≫ Functor.isoWhiskerLeft EX.inverse α ≪≫
    (Functor.associator EX.inverse P H).symm ≪≫
    Functor.isoWhiskerRight (Equivalence.conjugateSquare EX EY β) H ≪≫
    Functor.associator Q EY.inverse H⟩

section Sets

/-- Inverse image along base change on Mathlib's small étale site, for sheaves of sets. This is
the left adjoint built by a left Kan extension followed by sheafification, which is the
construction available on `AlgebraicGeometry.Scheme.Etale`. -/
public abbrev etaleSiteSheafPullbackType :
    Sheaf X.obj.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf Y.obj.smallEtaleTopology (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)) (Type (u + 1))
    X.obj.smallEtaleTopology Y.obj.smallEtaleTopology

/-- The inverse-image/direct-image adjunction on Mathlib's small étale site, for sheaves of
sets. -/
public def etaleSiteSheafPullbackTypeAdjunction :
    etaleSiteSheafPullbackType B f ⊣
      (Stacks.EtaleCohomology.smallEtaleBaseChange
        (B.inclusion.map f)).sheafPushforwardContinuous (Type (u + 1))
        X.obj.smallEtaleTopology Y.obj.smallEtaleTopology :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- **The equivalence of the sheaves of sets of the two presentations of the small étale site
commutes with inverse image along base change.** -/
public def sheafEquivSheafPullbackTypeIso :
    (SmallEtale.sheafEquiv B X.obj X.property (Type (u + 1))).functor ⋙
        etaleSiteSheafPullbackType B f ≅
      smallEtaleSheafPullbackType B f ⋙
        (SmallEtale.sheafEquiv B Y.obj Y.property (Type (u + 1))).functor :=
  SmallEtale.sheafEquivPullbackBaseChangeIso B f (Type (u + 1))
    (etaleSiteSheafPullbackTypeAdjunction B f)
    (Functor.sheafAdjunctionContinuous (smallEtaleBaseChange B f) (Type (u + 1))
      (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2))

/-- **The comparison of the two inverse images, read with the equivalences reversed, on a single
sheaf of sets.** The restriction to the site of Stacks 021B of the inverse image of a sheaf of
sets on Mathlib's small étale site is the inverse image of its restriction. -/
public def sheafEquivInverseSheafPullbackTypeIso
    (F : Sheaf X.obj.smallEtaleTopology (Type (u + 1))) :
    (SmallEtale.sheafEquiv B Y.obj Y.property (Type (u + 1))).inverse.obj
        ((etaleSiteSheafPullbackType B f).obj F) ≅
      (smallEtaleSheafPullbackType B f).obj
        ((SmallEtale.sheafEquiv B X.obj X.property (Type (u + 1))).inverse.obj F) :=
  (SmallEtale.sheafEquiv B Y.obj Y.property (Type (u + 1))).inverse.mapIso
      ((etaleSiteSheafPullbackType B f).mapIso
        ((SmallEtale.sheafEquiv B X.obj X.property (Type (u + 1))).counitIso.app F).symm ≪≫
      (sheafEquivSheafPullbackTypeIso B f).app
        ((SmallEtale.sheafEquiv B X.obj X.property (Type (u + 1))).inverse.obj F)) ≪≫
    ((SmallEtale.sheafEquiv B Y.obj Y.property (Type (u + 1))).unitIso.app _).symm

/-- **Inverse image on Mathlib's small étale site preserves finite local constancy of a sheaf of
sets.** The condition transports to the site of Stacks 021B by
`AlgebraicGeometry.SmallEtale.isFiniteLocallyConstant_sheafEquiv_inverse_iff`, where inverse image
preserves it by Stacks Tag 093R, and the two inverse images correspond by
`AlgebraicGeometry.sheafEquivInverseSheafPullbackTypeIso`. -/
public theorem isFiniteLocallyConstant_etaleSiteSheafPullbackType
    (F : Sheaf X.obj.smallEtaleTopology (Type (u + 1)))
    (hF : IsFiniteLocallyConstant X.obj.smallEtaleTopology F) :
    IsFiniteLocallyConstant Y.obj.smallEtaleTopology
      ((etaleSiteSheafPullbackType B f).obj F) := by
  refine (SmallEtale.isFiniteLocallyConstant_sheafEquiv_inverse_iff B Y _).mp ?_
  refine ObjectProperty.prop_of_iso
    (P := fun G : Sheaf (SmallEtale.topology B Y.1 Y.2) (Type (u + 1)) ↦
      IsFiniteLocallyConstant (SmallEtale.topology B Y.1 Y.2) G)
    (sheafEquivInverseSheafPullbackTypeIso B f F).symm ?_
  exact ((finiteLocallyConstantSheafPullback B f).obj
    ⟨_, (SmallEtale.isFiniteLocallyConstant_sheafEquiv_inverse_iff B X F).mpr hF⟩).property

/-- Inverse image along base change on the finite locally constant sheaves of sets of Mathlib's
small étale site. -/
public def etaleSiteFiniteLocallyConstantSheafPullback :
    ObjectProperty.FullSubcategory
        (fun F : Sheaf X.obj.smallEtaleTopology (Type (u + 1)) ↦
          IsFiniteLocallyConstant X.obj.smallEtaleTopology F) ⥤
      ObjectProperty.FullSubcategory
        (fun F : Sheaf Y.obj.smallEtaleTopology (Type (u + 1)) ↦
          IsFiniteLocallyConstant Y.obj.smallEtaleTopology F) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ etaleSiteSheafPullbackType B f)
    fun F ↦ isFiniteLocallyConstant_etaleSiteSheafPullbackType B f F.1 F.2

/-- **Inverse image on the finite locally constant sheaves of sets of Mathlib's small étale site
is the inverse image of sheaves of sets.** -/
public theorem etaleSiteFiniteLocallyConstantSheafPullback_comp_ι :
    etaleSiteFiniteLocallyConstantSheafPullback B f ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ etaleSiteSheafPullbackType B f := rfl

/-- The upper-left composite of the square of subcategories for sheaves of sets, read on the
ambient sheaves: both the comparison of the two presentations and the inverse image on Mathlib's
site are lifts along the inclusions. -/
public theorem finiteLocallyConstantSheafEquivEtaleSitePullback_comp_ι :
    ((SmallEtale.finiteLocallyConstantSheafEquiv B X).functor ⋙
        etaleSiteFiniteLocallyConstantSheafPullback B f) ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙
        ((SmallEtale.sheafEquiv B X.obj X.property (Type (u + 1))).functor ⋙
          etaleSiteSheafPullbackType B f) := rfl

/-- The lower-right composite of the square of subcategories for sheaves of sets, read on the
ambient sheaves. -/
public theorem finiteLocallyConstantSheafPullbackSheafEquiv_comp_ι :
    ObjectProperty.ι _ ⋙
        (smallEtaleSheafPullbackType B f ⋙
          (SmallEtale.sheafEquiv B Y.obj Y.property (Type (u + 1))).functor) =
      (finiteLocallyConstantSheafPullback B f ⋙
        (SmallEtale.finiteLocallyConstantSheafEquiv B Y).functor) ⋙ ObjectProperty.ι _ := rfl

/-- **The two categories of finite locally constant sheaves of sets are identified compatibly
with inverse image.** The ambient square
`AlgebraicGeometry.sheafEquivSheafPullbackTypeIso` descends to the subcategories, because the
composites of all four functors with the inclusion of the ambient sheaves are the ambient ones
and that inclusion is fully faithful. -/
public def finiteLocallyConstantSheafEquivPullbackIso :
    (SmallEtale.finiteLocallyConstantSheafEquiv B X).functor ⋙
        etaleSiteFiniteLocallyConstantSheafPullback B f ≅
      finiteLocallyConstantSheafPullback B f ⋙
        (SmallEtale.finiteLocallyConstantSheafEquiv B Y).functor :=
  Functor.fullyFaithfulCancelRight
    (ObjectProperty.ι
      (fun F : Sheaf Y.obj.smallEtaleTopology (Type (u + 1)) ↦
        IsFiniteLocallyConstant Y.obj.smallEtaleTopology F))
    (eqToIso (finiteLocallyConstantSheafEquivEtaleSitePullback_comp_ι B f) ≪≫
      Functor.isoWhiskerLeft (ObjectProperty.ι _) (sheafEquivSheafPullbackTypeIso B f) ≪≫
      eqToIso (finiteLocallyConstantSheafPullbackSheafEquiv_comp_ι B f))

/-- **Stacks Project, Tag 0DV6 for sheaves of sets, on Mathlib's small étale site.** Let
`f : Y ⟶ X` be a morphism of connected schemes and let `y` be a geometric point of `Y`, with
image `x = f(y)`. Then the square

```
  finite locally constant sheaves of sets on Y_étale  ←──  finite π₁(X, x)-sets
                        ↑                                          ↑
                     f^{-1}                                   restriction
                        │                                          │
  finite locally constant sheaves of sets on X_étale  ──→  finite π₁(X, x)-sets
```

commutes, where the sites are `AlgebraicGeometry.Scheme.smallEtaleTopology`, the horizontal
arrows are `AlgebraicGeometry.finiteLocallyConstantSetsEquivalenceEtaleSite`, the left vertical
arrow is the inverse image of sheaves of sets
(`AlgebraicGeometry.etaleSiteFiniteLocallyConstantSheafPullback_comp_ι`) and the right vertical
arrow reindexes the action along the homomorphism `π₁(Y, y) ⟶ π₁(X, x)` induced by `f`.

The dictionary on Mathlib's site is the dictionary on the site of Stacks 021B read through
`AlgebraicGeometry.SmallEtale.finiteLocallyConstantSheafEquiv`, so this is
`AlgebraicGeometry.nonempty_finiteLocallyConstantSetsEquivalence_pullbackIso` joined to
`AlgebraicGeometry.finiteLocallyConstantSheafEquivPullbackIso` with its horizontal edges
reversed. Only the existence of the comparison is asserted, because that is the form in which
Tag 0DV6 is available on the site of Stacks 021B. -/
public theorem nonempty_finiteLocallyConstantSetsEquivalenceEtaleSite_pullbackIso
    [ConnectedSpace X.1] [ConnectedSpace Y.1] (y : GeometricPoint Y.1) :
    Nonempty
      ((finiteLocallyConstantSetsEquivalenceEtaleSite B X (y.map f.hom)).functor ⋙
          ContAction.res FintypeCat.{u + 1} (etaleFundamentalGroupMap f.hom y) ≅
        etaleSiteFiniteLocallyConstantSheafPullback B f ⋙
          (finiteLocallyConstantSetsEquivalenceEtaleSite B Y y).functor) := by
  obtain ⟨α⟩ := nonempty_finiteLocallyConstantSetsEquivalence_pullbackIso B f y
  exact nonempty_iso_comp_inverse_of_iso _ _ _ _ _ _ _
    (finiteLocallyConstantSheafEquivPullbackIso B f) α

end Sets

/-! ### Sheaves of modules -/

section Modules

variable (Λ : Type r) [Ring Λ]

/-- Inverse image along base change on Mathlib's small étale site, for sheaves of
`Λ`-modules. -/
public abbrev etaleSiteSheafPullbackModule :
    Sheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf Y.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)) (ModuleCat.{u + 1} Λ)
    X.obj.smallEtaleTopology Y.obj.smallEtaleTopology

/-- The inverse-image/direct-image adjunction on Mathlib's small étale site, for sheaves of
`Λ`-modules. -/
public def etaleSiteSheafPullbackModuleAdjunction :
    etaleSiteSheafPullbackModule B f Λ ⊣
      (Stacks.EtaleCohomology.smallEtaleBaseChange
        (B.inclusion.map f)).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
        X.obj.smallEtaleTopology Y.obj.smallEtaleTopology :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- **The equivalence of the sheaves of `Λ`-modules of the two presentations of the small étale
site commutes with inverse image along base change.** -/
public def sheafEquivSheafPullbackModuleIso :
    (SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor ⋙
        etaleSiteSheafPullbackModule B f Λ ≅
      (smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2) ⋙
        (SmallEtale.sheafEquiv B Y.obj Y.property (ModuleCat.{u + 1} Λ)).functor :=
  SmallEtale.sheafEquivPullbackBaseChangeIso B f (ModuleCat.{u + 1} Λ)
    (etaleSiteSheafPullbackModuleAdjunction B f Λ)
    (Functor.sheafAdjunctionContinuous (smallEtaleBaseChange B f) (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2))

/-- **The comparison of the two inverse images, read with the equivalences reversed, on a single
sheaf of `Λ`-modules.** -/
public def sheafEquivInverseSheafPullbackModuleIso
    (F : Sheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (SmallEtale.sheafEquiv B Y.obj Y.property (ModuleCat.{u + 1} Λ)).inverse.obj
        ((etaleSiteSheafPullbackModule B f Λ).obj F) ≅
      ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
          (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2)).obj
        ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).inverse.obj F) :=
  (SmallEtale.sheafEquiv B Y.obj Y.property (ModuleCat.{u + 1} Λ)).inverse.mapIso
      ((etaleSiteSheafPullbackModule B f Λ).mapIso
        ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).counitIso.app F).symm ≪≫
      (sheafEquivSheafPullbackModuleIso B f Λ).app
        ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).inverse.obj F)) ≪≫
    ((SmallEtale.sheafEquiv B Y.obj Y.property (ModuleCat.{u + 1} Λ)).unitIso.app _).symm

variable [Finite Λ] [ConnectedSpace X.1] [ConnectedSpace Y.1]

omit [ConnectedSpace X.1] [ConnectedSpace Y.1] in
/-- **Inverse image on Mathlib's small étale site preserves Tag 03RW's condition on a sheaf of
`Λ`-modules.** The condition transports to the site of Stacks 021B by
`AlgebraicGeometry.SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff`, where inverse
image preserves it because over a finite ring it is finite local constancy
(`AlgebraicGeometry.isFiniteTypeLocallyConstant_eq_isFiniteLocallyConstant`) and so Stacks
Tag 093R applies, and the two inverse images correspond by
`AlgebraicGeometry.sheafEquivInverseSheafPullbackModuleIso`. -/
public theorem isFiniteTypeLocallyConstant_etaleSiteSheafPullbackModule
    (F : Sheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsFiniteTypeLocallyConstant Λ X.obj.smallEtaleTopology F) :
    IsFiniteTypeLocallyConstant Λ Y.obj.smallEtaleTopology
      ((etaleSiteSheafPullbackModule B f Λ).obj F) := by
  refine (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B Y Λ _).mp ?_
  refine ObjectProperty.prop_of_iso
    (P := fun G : Sheaf (SmallEtale.topology B Y.1 Y.2) (ModuleCat.{u + 1} Λ) ↦
      IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B Y.1 Y.2) G)
    (sheafEquivInverseSheafPullbackModuleIso B f Λ F).symm ?_
  exact ((finiteTypeLocallyConstantModuleSheafPullback B f Λ).obj
    ⟨_, (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_inverse_iff B X Λ F).mpr hF⟩).property

/-- Inverse image along base change on the finite type locally constant sheaves of `Λ`-modules of
Mathlib's small étale site. -/
public def etaleSiteFiniteTypeLocallyConstantModuleSheafPullback :
    ObjectProperty.FullSubcategory
        (fun F : Sheaf X.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ X.obj.smallEtaleTopology F) ⥤
      ObjectProperty.FullSubcategory
        (fun F : Sheaf Y.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
          IsFiniteTypeLocallyConstant Λ Y.obj.smallEtaleTopology F) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ etaleSiteSheafPullbackModule B f Λ)
    fun F ↦ isFiniteTypeLocallyConstant_etaleSiteSheafPullbackModule B f Λ F.1 F.2

omit [ConnectedSpace X.1] [ConnectedSpace Y.1] in
/-- **Inverse image on the finite type locally constant module sheaves of Mathlib's small étale
site is the inverse image of sheaves of `Λ`-modules.** -/
public theorem etaleSiteFiniteTypeLocallyConstantModuleSheafPullback_comp_ι :
    etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙ etaleSiteSheafPullbackModule B f Λ := rfl

omit [ConnectedSpace X.1] [ConnectedSpace Y.1] in
/-- The upper-left composite of the square of subcategories for sheaves of `Λ`-modules, read on
the ambient sheaves. -/
public theorem finiteTypeLocallyConstantSheafEquivEtaleSitePullback_comp_ι :
    ((SmallEtale.finiteTypeLocallyConstantSheafEquiv B X Λ).functor ⋙
        etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ) ⋙ ObjectProperty.ι _ =
      ObjectProperty.ι _ ⋙
        ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)).functor ⋙
          etaleSiteSheafPullbackModule B f Λ) := rfl

omit [ConnectedSpace X.1] [ConnectedSpace Y.1] in
/-- The lower-right composite of the square of subcategories for sheaves of `Λ`-modules, read on
the ambient sheaves. -/
public theorem finiteTypeLocallyConstantModuleSheafPullbackSheafEquiv_comp_ι :
    ObjectProperty.ι _ ⋙
        ((smallEtaleBaseChange B f).sheafPullback (ModuleCat.{u + 1} Λ)
            (SmallEtale.topology B X.1 X.2) (SmallEtale.topology B Y.1 Y.2) ⋙
          (SmallEtale.sheafEquiv B Y.obj Y.property (ModuleCat.{u + 1} Λ)).functor) =
      (finiteTypeLocallyConstantModuleSheafPullback B f Λ ⋙
        (SmallEtale.finiteTypeLocallyConstantSheafEquiv B Y Λ).functor) ⋙
          ObjectProperty.ι _ := rfl

/-- **The two categories of finite type locally constant sheaves of `Λ`-modules are identified
compatibly with inverse image.** -/
public def finiteTypeLocallyConstantSheafEquivPullbackIso :
    (SmallEtale.finiteTypeLocallyConstantSheafEquiv B X Λ).functor ⋙
        etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ ≅
      finiteTypeLocallyConstantModuleSheafPullback B f Λ ⋙
        (SmallEtale.finiteTypeLocallyConstantSheafEquiv B Y Λ).functor :=
  Functor.fullyFaithfulCancelRight
    (ObjectProperty.ι
      (fun F : Sheaf Y.obj.smallEtaleTopology (ModuleCat.{u + 1} Λ) ↦
        IsFiniteTypeLocallyConstant Λ Y.obj.smallEtaleTopology F))
    (eqToIso (finiteTypeLocallyConstantSheafEquivEtaleSitePullback_comp_ι B f Λ) ≪≫
      Functor.isoWhiskerLeft (ObjectProperty.ι _) (sheafEquivSheafPullbackModuleIso B f Λ) ≪≫
      eqToIso (finiteTypeLocallyConstantModuleSheafPullbackSheafEquiv_comp_ι B f Λ))

/-- **Stacks Project, Tag 0DV6 for sheaves of modules over a finite ring, on Mathlib's small
étale site.** Let `Λ` be a finite ring, let `f : Y ⟶ X` be a morphism of connected schemes and
let `y` be a geometric point of `Y`, with image `x = f(y)`. Then the square

```
  finite type locally constant Λ-module sheaves on X_étale  ──→  finite Λ-π₁(X, x)-modules
                        │                                                 │
                     f^{-1}                                          restriction
                        ↓                                                 ↓
  finite type locally constant Λ-module sheaves on Y_étale  ──→  finite Λ-π₁(Y, y)-modules
```

commutes, where the sites are `AlgebraicGeometry.Scheme.smallEtaleTopology`, the horizontal
arrows are `AlgebraicGeometry.finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite`, the left
vertical arrow is the inverse image of sheaves of `Λ`-modules
(`AlgebraicGeometry.etaleSiteFiniteTypeLocallyConstantModuleSheafPullback_comp_ι`) and the right
vertical arrow reindexes the action along the homomorphism `π₁(Y, y) ⟶ π₁(X, x)` induced by `f`.

The dictionary on Mathlib's site is the dictionary on the site of Stacks 021B read through
`AlgebraicGeometry.SmallEtale.finiteTypeLocallyConstantSheafEquiv`, so this is
`AlgebraicGeometry.nonempty_finiteTypeLocallyConstantModuleSheafEquivalence_pullbackIso` joined to
`AlgebraicGeometry.finiteTypeLocallyConstantSheafEquivPullbackIso` with its horizontal edges
reversed. Only the existence of the comparison is asserted, because that is the form in which
Tag 0DV6 is available on the site of Stacks 021B. -/
public theorem nonempty_finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite_pullbackIso
    (y : GeometricPoint Y.1) :
    Nonempty
      ((finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B X
            (y.map f.hom) Λ).functor ⋙
          finiteTypeContinuousModuleRes Λ (etaleFundamentalGroupMap f.hom y) ≅
        etaleSiteFiniteTypeLocallyConstantModuleSheafPullback B f Λ ⋙
          (finiteTypeLocallyConstantModuleSheafEquivalenceEtaleSite B Y y Λ).functor) := by
  obtain ⟨α⟩ := nonempty_finiteTypeLocallyConstantModuleSheafEquivalence_pullbackIso B f Λ y
  exact nonempty_iso_comp_inverse_of_iso _ _ _ _ _ _ _
    (finiteTypeLocallyConstantSheafEquivPullbackIso B f Λ) α

end Modules

end AlgebraicGeometry

end
