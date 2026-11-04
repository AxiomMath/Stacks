module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.ForgetfulInclusionCohomologyPresheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparisonDef
import StacksCore.Tactic.StacksAttribute

/-!
# Module-valued derived sections on a ringed site

Let `(C, O)` be a ringed site. The forgetful functor from sheaves of `O`-modules to presheaves
of `O`-modules is left exact, so it has right derived functors, and the value of the `p`-th one
on an object `U` of the site is the `p`-th right derived functor of module-valued sections over
`U`. The identification keeps the `O(U)`-module structure, is the one induced by evaluating an
injective resolution, is compatible with restriction of scalars along a morphism of the site,
and is compatible with restriction of sections. After forgetting the module structure the same
derived presheaf is the cohomology presheaf of the underlying abelian sheaf.

## Main definitions

* `Stacks.Cohomology.SiteDerivedForget.rightDerivedForgetEvaluationIso`: the comparison between
  evaluation of the derived inclusion and module-valued derived sections.
* `Stacks.Cohomology.SiteDerivedForget.rightDerivedForgetRestrictedEvaluationIso`: the same
  comparison after restriction of scalars along a morphism `U ⟶ V` of the site.
* `Stacks.Cohomology.SiteDerivedForget.rightDerivedEvaluationRestrictScalarsIso`: restriction of
  scalars commutes with the cohomology of a complex of modules, hence with derived evaluation.
* `Stacks.Cohomology.SiteDerivedForget.derivedForgetCohomologyEvaluationIso`: sections over `U`
  of the derived inclusion, read as abelian groups, are `Ext` out of the free abelian sheaf on
  `yoneda.obj U`.
* `Stacks.Cohomology.SiteDerivedForget.rightDerivedForgetCohomologyIso`: the derived inclusion,
  read as a presheaf of abelian groups, is the cohomology presheaf.

## Main results

* `Stacks.Cohomology.SiteDerivedForget.rightDerivedForgetEvaluationIso_cocycles` fixes the
  comparison by its action on every injective resolution; in particular it does not depend on
  the chosen resolution.
* `Stacks.Cohomology.SiteDerivedForget.rightDerivedForgetRestrictedEvaluationIso_eq` identifies
  the restricted comparison with scalar restriction of the unrestricted one, so that nothing is
  chosen independently after restricting scalars.
* `Stacks.Cohomology.SiteDerivedForget.rightDerivedForgetEvaluationIso_naturality` records
  module-linear compatibility with restriction from `V` to `U`.
* `Stacks.Cohomology.SiteDerivedForget.sectionsCorep_naturality` and
  `Stacks.Cohomology.SiteDerivedForget.compCorepresentation_naturality` are the two
  compatibilities in the object of the site that the 03FD comparison needs in order to be
  assembled into an isomorphism of presheaves.
* `Stacks.Cohomology.SiteDerivedForget.rightDerivedForgetCohomologyIso_naturality` records
  compatibility of that isomorphism with restriction along every morphism of the site.

## Implementation notes

The homological input is `Stacks.Cohomology.DerivedForget.rightDerivedCompIso`: for a left exact
`F` and an exact `G` one has `F.rightDerived p ⋙ G ≅ (F ⋙ G).rightDerived p`, because both sides
are computed from the same injective resolution and `G` commutes with taking homology. Here `F`
is the forgetful functor and `G` is evaluation at `U`, possibly followed by restriction of
scalars. The facts about that comparison which the statements below need — its naturality in
`G`, its behaviour under composing the second functor, and its value read off an arbitrary
injective resolution — are proved here, since elsewhere the comparison is only used on the site
of a topological space, where no such reading is needed.

The abelian-group-valued half goes through Stacks 03FD over an object of the site. Sections over
`U` of an abelian sheaf are corepresented by the free abelian sheaf on `yoneda.obj U`
(`Stacks.Cohomology.Locality.eFun`), and `ModuleSheafCohomology.comparisonIso` compares deriving
sections of a module sheaf with forgetting and deriving there. Reading its target as `Ext` out of
that free abelian sheaf is `ModuleSheafCohomology.extFunctorObjIsoRightDerived`, and `Ext` out of
the free abelian sheaf on `yoneda.obj U` is by definition the value of Mathlib's cohomology
presheaf at `U`. Assembling the objectwise comparisons into a morphism of presheaves needs those
three identifications to be natural in `U`; the first is
`Stacks.Cohomology.Locality.eFun_naturality`, the second is
`ModuleSheafCohomology.tensorSheafHomIso_naturality`, and they feed
`ModuleSheafCohomology.comparisonIso_naturality` and
`ModuleSheafCohomology.extFunctorObjIsoRightDerived_naturality`.

Left exactness of the inclusion is Mathlib's instance
`SheafOfModules.Finite.forgetPreservesFiniteLimits`, which is where that claim of the tag is
recorded rather than being restated here, and the Grothendieck abelian instances for
sheaves of modules at an independent module universe come from
`Stacks.SheafOfModules.sheafModulesGrothendieck`, so no hypothesis on the ringed site is needed.
The universes of the site, of its morphisms and of the sections of its structure sheaf are all
specialized to one universe `u`, which is the generality in which the sheaves-of-modules
evaluation functors below are stated.

Three steps compare morphisms across `(F ⋙ G).mapHomologicalComplex` and
`F.mapHomologicalComplex ⋙ G.mapHomologicalComplex`, which are definitionally but not
syntactically equal, so `rw` and `simp only` refuse to act on them. Each is therefore carried
out by `change` at a type written out in full, or by a term built from `Eq.trans` and `congrArg`,
rather than by rewriting through the identification.

## References

* [Stacks Project, Tag 06YK](https://stacks.math.columbia.edu/tag/06YK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Cohomology.DerivedForget

universe u

/-! ### Left exactness of the forgetful functor

The first claim of 06YK, that forgetting the sheaf condition on a sheaf of modules over a ringed
site is left exact, is already Mathlib's instance, so it is claimed there rather than restated.
-/

add_to_stacks 06YK "left exactness" SheafOfModules.Finite.forgetPreservesFiniteLimits

namespace Stacks.Cohomology.SiteDerivedForget

/-! ### The comparison for a composite, on an arbitrary injective resolution -/

/-- `rightDerivedCompIso` is natural in the second functor: a natural transformation `α : G ⟶ H`
induces a commuting square with the natural transformation `NatTrans.rightDerived` induces from
whiskering `α` by `F`. -/
private theorem rightDerivedCompIso_naturality
    {A : Type*} {B : Type*} {C : Type*}
    [Category A] [Category B] [Category C] [Abelian A] [HasInjectiveResolutions A]
    [Abelian B] [Abelian C] (F : A ⥤ B) [F.Additive]
    {G H : B ⥤ C} [G.Additive] [H.Additive] [G.PreservesHomology] [H.PreservesHomology]
    [(F ⋙ G).Additive] [(F ⋙ H).Additive] (α : G ⟶ H) (p : ℕ) (X : A) :
    α.app ((F.rightDerived p).obj X) ≫ (rightDerivedCompIso F H p).hom.app X =
      (rightDerivedCompIso F G p).hom.app X ≫
        (NatTrans.rightDerived (Functor.whiskerLeft F α) p).app X := by
  unfold rightDerivedCompIso
  dsimp [NatTrans.rightDerived, NatTrans.rightDerivedToHomotopyCategory]
  let K := ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((injectiveResolutions A).obj X).as)
  unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
  simp only [Functor.comp_obj]
  unfold HomotopyCategory.homologyFunctor
  show α.app (K.sc p).homology ≫ ((K.sc p).mapHomologyIso H).inv =
    ((K.sc p).mapHomologyIso G).inv ≫
      ShortComplex.homologyMap ((K.sc p).mapNatTrans α)
  simp only [NatTrans.app_homology, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- `rightDerivedCompIso` for a composite second functor `G ⋙ H` is the comparison for `G`,
pushed forward by `H`, followed by the comparison for `H`. -/
private theorem rightDerivedCompIso_comp
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [HasInjectiveResolutions A] [Abelian B] [Abelian C] [Abelian D]
    (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive] [G.PreservesHomology]
    (H : C ⥤ D) [H.Additive] [H.PreservesHomology] [(G ⋙ H).PreservesHomology]
    (p : ℕ) (X : A) :
    (rightDerivedCompIso F (G ⋙ H) p).hom.app X =
      H.map ((rightDerivedCompIso F G p).hom.app X) ≫
        (rightDerivedCompIso (F ⋙ G) H p).hom.app X := by
  unfold rightDerivedCompIso
  dsimp [Functor.rightDerived, Functor.rightDerivedToHomotopyCategory,
    HomotopyCategory.homologyFunctor]
  unfold HomotopyCategory.homologyFunctor
  exact ShortComplex.mapHomologyIso_comp_inv _ G H

/-- `rightDerivedCompIso` read on an arbitrary injective resolution `I`: the comparison is the
one induced by applying `G` to the homology of `F` applied to `I`. -/
private theorem rightDerivedCompIso_app
    {A : Type*} {B : Type*} {C : Type*}
    [Category A] [Category B] [Category C] [Abelian A] [HasInjectiveResolutions A]
    [Abelian B] [Abelian C] (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    [G.PreservesHomology] (p : ℕ) {X : A} (I : InjectiveResolution X) :
    (rightDerivedCompIso F G p).hom.app X ≫ (I.isoRightDerivedObj (F ⋙ G) p).hom =
      G.map (I.isoRightDerivedObj F p).hom ≫
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc p).mapHomologyIso
          G).inv := by
  obtain ⟨φ, hφ⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℕ)).map_surjective I.iso.hom
  show (rightDerivedCompIso F G p).hom.app X ≫
      (HomotopyCategory.homologyFunctor C (ComplexShape.up ℕ) p).map
          (((F ⋙ G).mapHomotopyCategory (ComplexShape.up ℕ)).map I.iso.hom ≫
            (((F ⋙ G).mapHomotopyCategoryFactors (ComplexShape.up ℕ)).app I.cocomplex).hom) ≫
        ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℕ) p).app
            (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).hom =
    G.map
        ((HomotopyCategory.homologyFunctor B (ComplexShape.up ℕ) p).map
            ((F.mapHomotopyCategory (ComplexShape.up ℕ)).map I.iso.hom ≫
              ((F.mapHomotopyCategoryFactors (ComplexShape.up ℕ)).app I.cocomplex).hom) ≫
          ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℕ) p).app
              ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).hom) ≫
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc p).mapHomologyIso G).inv
  rw [← hφ]
  with_unfolding_all
    show ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution X).cocomplex).sc p).mapHomologyIso G).inv ≫
        (HomologicalComplex.homologyMap
          (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).map φ ≫ 𝟙 _) p ≫ 𝟙 _) =
      G.map (HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ ≫ 𝟙 _) p ≫ 𝟙 _) ≫
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc p).mapHomologyIso
          G).inv
  simp only [Category.comp_id]
  with_unfolding_all
    exact (congrArg (fun z =>
          ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
            (injectiveResolution X).cocomplex).sc p).mapHomologyIso G).inv ≫ z)
        (Category.comp_id (HomologicalComplex.homologyMap
          (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).map φ) p))).trans
      (ShortComplex.mapHomologyIso_inv_naturality
        ((HomologicalComplex.shortComplexFunctor B (ComplexShape.up ℕ) p).map
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map φ)) G).symm

/-- `rightDerivedCompIso` written as the chain of comparisons supplied by an arbitrary
injective resolution: apply `G` to the computation of `F.rightDerived p` on `I`, compare the
homology of the image complex with the image of the homology, and read the result back as
`(F ⋙ G).rightDerived p`. -/
private theorem rightDerivedCompIso_hom_app_chain
    {A : Type*} {B : Type*} {C : Type*}
    [Category A] [Category B] [Category C] [Abelian A] [HasInjectiveResolutions A]
    [Abelian B] [Abelian C] (F : A ⥤ B) [F.Additive] (G : B ⥤ C) [G.Additive]
    [G.PreservesHomology] (p : ℕ) {X : A} (I : InjectiveResolution X) :
    (rightDerivedCompIso F G p).hom.app X =
      (G.mapIso (I.isoRightDerivedObj F p)).hom ≫
      (G.mapIso ((HomologicalComplex.homologyFunctorIso _ _ p).app
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex))).hom ≫
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc p).mapHomologyIso
        G).inv ≫
      ((HomologicalComplex.homologyFunctorIso _ _ p).app
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex))).inv ≫
      (I.isoRightDerivedObj (F ⋙ G) p).inv := by
  have hB : (G.mapIso ((HomologicalComplex.homologyFunctorIso _ _ p).app
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex))).hom = 𝟙 _ := G.map_id _
  have hD : ((HomologicalComplex.homologyFunctorIso _ _ p).app
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex))).inv = 𝟙 _ := rfl
  have hcollapse : ∀ {W Y Z T : C} (α : W ⟶ Y) (β : Y ⟶ Z) (γ : Z ⟶ T),
      α ≫ 𝟙 Y ≫ (β ≫ 𝟙 Z ≫ γ) = α ≫ (β ≫ γ) := fun α β γ =>
    congrArg (fun z => α ≫ z)
      ((Category.id_comp _).trans (congrArg (fun z => β ≫ z) (Category.id_comp γ)))
  rw [hB, hD]
  refine Eq.trans ?_ (hcollapse _ _ _).symm
  exact (Category.comp_id _).symm.trans
    ((congrArg (fun m => (rightDerivedCompIso F G p).hom.app X ≫ m)
        (I.isoRightDerivedObj (F ⋙ G) p).hom_inv_id.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ (I.isoRightDerivedObj (F ⋙ G) p).inv)
            (rightDerivedCompIso_app F G p I)).trans (Category.assoc _ _ _))))

/-! ### Module-valued derived sections -/

/-- The forgetful functor from sheaves of modules on a ringed site to presheaves of modules is
additive. This is Mathlib's instance, supplied by name rather than by instance search: the ring
sheaf of a ringed site is a reducible abbreviation for an anonymous-constructor term, through
which search does not reach Mathlib's instance, although the instance does apply to it. -/
local instance forget_additive (X : RingedSite.{u, u, u}) :
    (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
  SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)

/-- Evaluation of a sheaf of modules at an object of a ringed site is additive: a morphism of
sheaves of modules is a morphism of the underlying presheaves, and addition of morphisms is
defined on those, so additivity holds by definition. -/
public instance evaluation_additive (X : RingedSite.{u, u, u}) (U : X.C) :
    (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).Additive where
  map_add := rfl

/-! ### The covering set of 06YK

Stacks 06YK is a tag of eight claims, and all eight are claimed here: left exactness of the
forgetful functor on Mathlib's instance above, the module-valued comparison and its three
coherences in this section, and the abelian-group-valued comparison and its naturality in the
last section.
-/

/-- Evaluation at `U` of the derived inclusion of module sheaves into module presheaves
is canonically the module-valued right derived functor of sections over `U`. -/
@[stacks 06YK "module-valued derived sections", sga "4 V 2.4.2" "(X), special case"]
public noncomputable def rightDerivedForgetEvaluationIso (X : RingedSite.{u, u, u})
    (U : X.C) (p : ℕ) :
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).rightDerived p ⋙
        PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U) ≅
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).rightDerived p := by
  let P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj :=
    SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let G := PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)
  have : G.PreservesHomology := Functor.preservesHomologyOfExact G
  exact rightDerivedCompIso P G p

/-- The comparison is the one induced by evaluating the cocycles of an injective
resolution. In particular it is independent of the chosen resolution. -/
@[stacks 06YK "canonical comparison on injective resolutions"]
public theorem rightDerivedForgetEvaluationIso_cocycles (X : RingedSite.{u, u, u})
    (U : X.C) (p : ℕ) (F : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (I : InjectiveResolution F) :
    let P := SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    let E := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
    let G := PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)
    let K := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    (rightDerivedForgetEvaluationIso X U p).hom.app F =
      (G.mapIso (I.isoRightDerivedObj P p)).hom ≫
      (G.mapIso ((HomologicalComplex.homologyFunctorIso _ _ p).app K)).hom ≫
      ((K.sc p).mapHomologyIso G).inv ≫
      ((HomologicalComplex.homologyFunctorIso _ _ p).app
        ((G.mapHomologicalComplex _).obj K)).inv ≫
      (I.isoRightDerivedObj E p).inv := by
  intro P E G K
  have : G.PreservesHomology := Functor.preservesHomologyOfExact G
  exact rightDerivedCompIso_hom_app_chain P G p I

/-- The derived inclusion followed by evaluation at `U` and restriction of scalars to
`O(V)` agrees with derived sections at `U` viewed as `O(V)`-modules. -/
@[stacks 06YK "derived sections after scalar restriction"]
public noncomputable def rightDerivedForgetRestrictedEvaluationIso
    (X : RingedSite.{u, u, u}) {U V : X.C} (f : U ⟶ V) (p : ℕ) :
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).rightDerived p ⋙
        (PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U) ⋙
          ModuleCat.restrictScalars
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom) ≅
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U) ⋙
        ModuleCat.restrictScalars
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom).rightDerived p := by
  let E := PresheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)
  let R : ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) ⥤
      ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)) :=
    ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom
  have : (E ⋙ R).PreservesHomology :=
    (E ⋙ R).preservesHomology_of_preservesMonos_and_cokernels
  exact rightDerivedCompIso (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (E ⋙ R) p

/-- Restricting scalars commutes canonically with the cohomology of a complex of
modules, hence with derived evaluation. -/
public noncomputable def rightDerivedEvaluationRestrictScalarsIso
    (X : RingedSite.{u, u, u}) {U V : X.C} (f : U ⟶ V) (p : ℕ)
    (F : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom).obj
        (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op U)).rightDerived p).obj F) ≅
      ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U) ⋙
        ModuleCat.restrictScalars
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom).rightDerived p).obj F :=
  let I := injectiveResolution F
  let E := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)
  let G : ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) ⥤
      ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)) :=
    ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom
  let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have : G.PreservesHomology := G.preservesHomology_of_preservesMonos_and_cokernels
  G.mapIso (I.isoRightDerivedObj E p) ≪≫
    G.mapIso ((HomologicalComplex.homologyFunctorIso _ _ p).app K) ≪≫
    ((K.sc p).mapHomologyIso G).symm ≪≫
    ((HomologicalComplex.homologyFunctorIso _ _ p).app
      ((G.mapHomologicalComplex _).obj K)).symm ≪≫
    (I.isoRightDerivedObj (E ⋙ G) p).symm

/-- The restricted comparison is obtained from the same module-valued comparison,
not chosen independently after restriction of scalars. -/
@[stacks 06YK "scalar-restriction coherence"]
public theorem rightDerivedForgetRestrictedEvaluationIso_eq
    (X : RingedSite.{u, u, u}) {U V : X.C} (f : U ⟶ V) (p : ℕ)
    (F : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (rightDerivedForgetRestrictedEvaluationIso X f p).hom.app F =
      (ModuleCat.restrictScalars
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom).map
        ((rightDerivedForgetEvaluationIso X U p).hom.app F) ≫
      (rightDerivedEvaluationRestrictScalarsIso X f p F).hom := by
  let P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj :=
    SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let G := PresheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)
  let R : ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) ⥤
      ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V)) :=
    ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom
  have : G.PreservesHomology := Functor.preservesHomologyOfExact G
  have : R.PreservesHomology := R.preservesHomology_of_preservesMonos_and_cokernels
  have : (G ⋙ R).PreservesHomology :=
    (G ⋙ R).preservesHomology_of_preservesMonos_and_cokernels
  have h : (rightDerivedEvaluationRestrictScalarsIso X f p F).hom =
      (rightDerivedCompIso (P ⋙ G) R p).hom.app F :=
    (rightDerivedCompIso_hom_app_chain (P ⋙ G) R p (injectiveResolution F)).symm
  rw [h]
  exact rightDerivedCompIso_comp P G R p F

/-- The module-valued comparison commutes with restriction from `V` to `U`, with the
target sections viewed as modules over the ring of sections on `V`. -/
@[stacks 06YK "module-valued restriction compatibility"]
public theorem rightDerivedForgetEvaluationIso_naturality (X : RingedSite.{u, u, u})
    (p : ℕ) (F : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U V : X.C} (f : U ⟶ V) :
    (PresheafOfModules.restriction (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj f.op).app
        (((SheafOfModules.forget
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).rightDerived p).obj F) ≫
      (rightDerivedForgetRestrictedEvaluationIso X f p).hom.app F =
    (rightDerivedForgetEvaluationIso X V p).hom.app F ≫
      (NatTrans.rightDerived
        (Functor.whiskerLeft (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (PresheafOfModules.restriction
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj f.op)) p).app F := by
  let P : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj :=
    SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let GV := PresheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op V)
  let GU := PresheafOfModules.evaluation.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U) ⋙
    ModuleCat.restrictScalars ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op).hom
  have : GV.PreservesHomology := Functor.preservesHomologyOfExact GV
  have : GU.PreservesHomology := GU.preservesHomology_of_preservesMonos_and_cokernels
  exact rightDerivedCompIso_naturality P
    (PresheafOfModules.restriction (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj f.op) p F

/-! ### The abelian-group-valued comparison: Stacks 03FD over each object of the site -/

/-- The functor of sections over `U` on abelian sheaves is additive. -/
local instance evalSectionsAdditive (X : RingedSite.{u, u, u}) (U : X.Cᵒᵖ) :
    ((sheafSections X.J Ab.{u}).obj U).Additive where
  map_add := rfl

/-- The functor of sections over `U` on abelian sheaves preserves finite limits. -/
local instance evalSectionsPreservesFiniteLimits (X : RingedSite.{u, u, u}) (U : X.Cᵒᵖ) :
    PreservesFiniteLimits ((sheafSections X.J Ab.{u}).obj U) :=
  preservesFiniteLimits_of_natIso
    (sheafSectionsNatIsoEvaluation X.J Ab.{u} (X := U.unop)).symm

attribute [local instance] ModuleSheafCohomology.toSheaf_preservesFiniteColimits

/-- Sections over `U` of the underlying presheaf of abelian groups of a presheaf of modules. -/
public abbrev presheafSections (X : RingedSite.{u, u, u}) (U : X.Cᵒᵖ) :
    PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⥤ AddCommGrpCat.{u} :=
  PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ⋙
    (evaluation X.Cᵒᵖ AddCommGrpCat.{u}).obj U

/-- The free abelian sheaf on `yoneda.obj U`, which corepresents sections over `U`. -/
public abbrev freeSheaf (X : RingedSite.{u, u, u}) (U : X.C) : Sheaf X.J AddCommGrpCat.{u} :=
  Stacks.Cohomology.Locality.freeYonedaSheaf (J := X.J) U

/-- The corepresentation of sections over `U` by `freeSheaf U`. -/
public abbrev sectionsCorep (X : RingedSite.{u, u, u}) (U : X.C) :
    (sheafSections X.J Ab.{u}).obj (op U) ≅ preadditiveCoyoneda.obj (op (freeSheaf X U)) :=
  (Stacks.Cohomology.Locality.eFun (J := X.J) U).symm

/-- `sectionsCorep` is natural in the object of the site: restriction of sections corresponds to
precomposition with the induced map of free abelian sheaves. -/
public theorem sectionsCorep_naturality (X : RingedSite.{u, u, u}) {U V : X.C} (a : V ⟶ U) :
    (sheafSections X.J Ab.{u}).map a.op ≫ (Stacks.Cohomology.Locality.eFun (J := X.J) V).inv =
      (Stacks.Cohomology.Locality.eFun (J := X.J) U).inv ≫
        preadditiveCoyoneda.map (Stacks.Cohomology.Locality.freeYonedaMap (J := X.J) a).op := by
  rw [Iso.comp_inv_eq, Category.assoc,
    Stacks.Cohomology.Locality.eFun_naturality (J := X.J) a, Iso.inv_hom_id_assoc]
  rfl

/-- The module sheaf corepresenting module-valued sections over `U`. -/
public abbrev moduleCorepObject (X : RingedSite.{u, u, u}) (U : X.C) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
    (ModuleSheafCohomology.tensorPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
      (Stacks.Cohomology.Locality.freeYonedaPsh (C := X.C) U))

/-- Morphisms out of `moduleCorepObject U` are, after forgetting the module structure, morphisms
out of `freeSheaf U`. -/
public abbrev moduleCorep (X : RingedSite.{u, u, u}) (U : X.C) :
    preadditiveCoyoneda.obj (op (moduleCorepObject X U)) ≅
      SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        preadditiveCoyoneda.obj (op (freeSheaf X U)) :=
  ModuleSheafCohomology.tensorSheafHomIso X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (Stacks.Cohomology.Locality.freeYonedaPsh (C := X.C) U)

/-- The map of corepresenting module sheaves induced by a morphism of the site. -/
public abbrev moduleCorepMap (X : RingedSite.{u, u, u}) {U V : X.C} (a : V ⟶ U) :
    moduleCorepObject X V ⟶ moduleCorepObject X U :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
    (ModuleSheafCohomology.tensorPresheafMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
      (Stacks.Cohomology.Locality.freeYonedaPshMap (C := X.C) a))

/-- The acyclicity input of Stacks 03FD here: the underlying abelian sheaf of an injective module
sheaf has no higher `Ext` out of `freeSheaf U`. -/
public theorem extVanishing (X : RingedSite.{u, u, u}) (U : X.C)
    (I : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [Injective I] (n : ℕ)
    (e : Abelian.Ext.{u} (freeSheaf X U)
      ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj I) (n + 1)) :
    e = 0 :=
  ModuleSheafCohomology.ext_eq_zero_of_injective_toSheaf X.J
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) I U n e

/-- The corepresentation of the composite (forget, then sections over `U`) is natural in the
object of the site. This is the second compatibility that
`ModuleSheafCohomology.comparisonIso_naturality` consumes. -/
public theorem compCorepresentation_naturality (X : RingedSite.{u, u, u}) {U V : X.C}
    (a : V ⟶ U) :
    Functor.whiskerLeft (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          ((sheafSections X.J Ab.{u}).map a.op) ≫
        (ModuleSheafCohomology.compCorepresentation
          (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          ((sheafSections X.J Ab.{u}).obj (op V)) (freeSheaf X V) (sectionsCorep X V)
          (moduleCorepObject X V) (moduleCorep X V)).hom =
      (ModuleSheafCohomology.compCorepresentation
        (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          ((sheafSections X.J Ab.{u}).obj (op U)) (freeSheaf X U) (sectionsCorep X U)
          (moduleCorepObject X U) (moduleCorep X U)).hom ≫
        preadditiveCoyoneda.map (moduleCorepMap X a).op := by
  have hb : preadditiveCoyoneda.map (moduleCorepMap X a).op ≫ (moduleCorep X V).hom =
      (moduleCorep X U).hom ≫ Functor.whiskerLeft
        (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (preadditiveCoyoneda.map (Stacks.Cohomology.Locality.freeYonedaMap (J := X.J) a).op) :=
    ModuleSheafCohomology.tensorSheafHomIso_naturality X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (Stacks.Cohomology.Locality.freeYonedaPshMap (C := X.C) a)
  dsimp only [ModuleSheafCohomology.compCorepresentation, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, sectionsCorep_naturality,
    Functor.whiskerLeft_comp, Category.assoc, Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Category.assoc, hb, Iso.inv_hom_id_assoc]

/-- **Stacks 03FD over an object of the site**, in the corepresentation used here: deriving
sections over `U` of a module sheaf agrees with forgetting the module structure and deriving
sections over `U` of the underlying abelian sheaf. -/
@[ega "0 12.1.1" "partial"]
public noncomputable def moduleSectionsComparison (X : RingedSite.{u, u, u}) (U : X.C) (p : ℕ) :
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        (sheafSections X.J Ab.{u}).obj (op U)).rightDerived p ≅
      SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        ((sheafSections X.J Ab.{u}).obj (op U)).rightDerived p :=
  ModuleSheafCohomology.comparisonIso
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    ((sheafSections X.J Ab.{u}).obj (op U)) (freeSheaf X U) (sectionsCorep X U)
    (moduleCorepObject X U) (moduleCorep X U) (fun I _ n e => extVanishing X U I n e) p

/-- Sections over `U` of the `p`-th derived inclusion of module sheaves into module presheaves,
read as abelian groups, are `Ext` in degree `p` out of the free abelian sheaf on
`yoneda.obj U`. -/
public noncomputable def derivedForgetCohomologyEvaluationIso (X : RingedSite.{u, u, u})
    (U : X.Cᵒᵖ) (p : ℕ) :
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).rightDerived p ⋙
      presheafSections X U ≅
      SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        Abelian.extFunctorObj (freeSheaf X U.unop) p := by
  have : (presheafSections X U).PreservesHomology :=
    Functor.preservesHomologyOfExact (presheafSections X U)
  exact rightDerivedCompIso (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (presheafSections X U) p ≪≫
    moduleSectionsComparison X U.unop p ≪≫
    (Functor.isoWhiskerLeft (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ModuleSheafCohomology.extFunctorObjIsoRightDerived
        ((sheafSections X.J Ab.{u}).obj (op U.unop)) (freeSheaf X U.unop)
        (sectionsCorep X U.unop) p)).symm

/-- `derivedForgetCohomologyEvaluationIso` commutes with restriction along a morphism of the
site: the three comparisons it is built from are natural in the object of the site. -/
public theorem derivedForgetCohomologyEvaluationIso_naturality (X : RingedSite.{u, u, u})
    (p : ℕ) (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {U V : X.Cᵒᵖ} (f : U ⟶ V) :
    (((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).obj
        (((SheafOfModules.forget
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).rightDerived p).obj F)).map f) ≫
      (derivedForgetCohomologyEvaluationIso X V p).hom.app F =
    (derivedForgetCohomologyEvaluationIso X U p).hom.app F ≫
      (ModuleSheafCohomology.extPrecomp
        (Stacks.Cohomology.Locality.freeYonedaMap (J := X.J) f.unop) p).app
          ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj F) := by
  have : ∀ W, (presheafSections X W).PreservesHomology := fun W =>
    Functor.preservesHomologyOfExact (presheafSections X W)
  set P := SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  set T := SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  set a := f.unop
  set rho := (sheafSections X.J Ab.{u}).map f
  set alpha : presheafSections X U ⟶ presheafSections X V :=
    Functor.whiskerLeft
      (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
      ((evaluation X.Cᵒᵖ AddCommGrpCat.{u}).map f)
  let e (W : X.Cᵒᵖ) := ModuleSheafCohomology.extFunctorObjIsoRightDerived
    ((sheafSections X.J Ab.{u}).obj W) (freeSheaf X W.unop) (sectionsCorep X W.unop) p
  have h1 : alpha.app ((P.rightDerived p).obj F) ≫
      (rightDerivedCompIso P (presheafSections X V) p).hom.app F =
      (rightDerivedCompIso P (presheafSections X U) p).hom.app F ≫
        (NatTrans.rightDerived (Functor.whiskerLeft T rho) p).app F :=
    rightDerivedCompIso_naturality P alpha p F
  have h2 : (NatTrans.rightDerived (Functor.whiskerLeft T rho) p).app F ≫
      (moduleSectionsComparison X V.unop p).hom.app F =
      (moduleSectionsComparison X U.unop p).hom.app F ≫
        (NatTrans.rightDerived rho p).app (T.obj F) :=
    NatTrans.congr_app (ModuleSheafCohomology.comparisonIso_naturality T rho
    (Stacks.Cohomology.Locality.freeYonedaMap (J := X.J) a)
    (sectionsCorep X V.unop) (sectionsCorep X U.unop) (moduleCorepMap X a)
    (moduleCorep X V.unop) (moduleCorep X U.unop)
    (fun I _ n e => extVanishing X V.unop I n e) (fun I _ n e => extVanishing X U.unop I n e)
    (sectionsCorep_naturality X a) (compCorepresentation_naturality X a) p) F
  have h3 := NatTrans.congr_app
    (ModuleSheafCohomology.extFunctorObjIsoRightDerived_naturality
      (Stacks.Cohomology.Locality.freeYonedaMap (J := X.J) a)
      (sectionsCorep X V.unop) (sectionsCorep X U.unop) rho
      (sectionsCorep_naturality X a) p) (T.obj F)
  simp only [NatTrans.comp_app] at h3
  have h3' : (NatTrans.rightDerived rho p).app (T.obj F) ≫ (e V).inv.app (T.obj F) =
      (e U).inv.app (T.obj F) ≫
        (ModuleSheafCohomology.extPrecomp
          (Stacks.Cohomology.Locality.freeYonedaMap (J := X.J) a) p).app (T.obj F) := by
    rw [← cancel_epi ((e U).hom.app (T.obj F)), ← Category.assoc, ← h3,
      Category.assoc, Iso.hom_inv_id_app, Category.comp_id, Iso.hom_inv_id_app_assoc]
  have h4 : (NatTrans.rightDerived (Functor.whiskerLeft T rho) p).app F ≫
      ((moduleSectionsComparison X V.unop p).hom.app F ≫ (e V).inv.app (T.obj F)) =
      (moduleSectionsComparison X U.unop p).hom.app F ≫
        ((e U).inv.app (T.obj F) ≫
          (ModuleSheafCohomology.extPrecomp
            (Locality.freeYonedaMap (J := X.J) a) p).app (T.obj F)) := by
    rw [← Category.assoc, h2, Category.assoc, h3']
  change alpha.app ((P.rightDerived p).obj F) ≫ (_ ≫ _ ≫ (e V).inv.app _) =
    (_ ≫ _ ≫ (e U).inv.app _) ≫ _
  rw [← Category.assoc, h1]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (rightDerivedCompIso P (presheafSections X U) p).hom.app F ≫ z) h4).trans
      (by simp only [Category.assoc]; rfl))

/-- The right derived functor of the inclusion of module sheaves in module presheaves, viewed as
a presheaf of abelian groups, is canonically the cohomology presheaf. This is natural both in the
coefficient sheaf and in objects of the site. -/
@[stacks 06YK "higher derived functors",
  sga "4 IV 4.8" "more general",
  sga "4 V 2.4.2" "special case"]
public noncomputable def rightDerivedForgetCohomologyIso (X : RingedSite.{u, u, u}) (p : ℕ) :
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).rightDerived p ⋙
        PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj ≅
      SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        Sheaf.cohomologyPresheafFunctor X.J p :=
  NatIso.ofComponents (fun F => NatIso.ofComponents
    (fun U => (derivedForgetCohomologyEvaluationIso X U p).app F)
    (fun {_ _} f => derivedForgetCohomologyEvaluationIso_naturality X p F f))
    (fun {_ _} φ => by
      ext U x
      exact ConcreteCategory.congr_hom
        ((derivedForgetCohomologyEvaluationIso X U p).hom.naturality φ) x)

/-- The canonical identification of the derived presheaf with the cohomology presheaf commutes
with restriction along any morphism of the site. -/
@[stacks 06YK "compatibility with restriction"]
public theorem rightDerivedForgetCohomologyIso_naturality (X : RingedSite.{u, u, u}) (p : ℕ)
    (F : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {U V : X.C} (f : U ⟶ V) :
    (((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).obj
      (((SheafOfModules.forget
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).rightDerived p).obj F)).map f.op) ≫
        ((rightDerivedForgetCohomologyIso X p).hom.app F).app (op U) =
      ((rightDerivedForgetCohomologyIso X p).hom.app F).app (op V) ≫
        (((Sheaf.cohomologyPresheafFunctor X.J p).obj
          ((SheafOfModules.toSheaf
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj F)).map f.op) :=
  ((rightDerivedForgetCohomologyIso X p).hom.app F).naturality f.op

end Stacks.Cohomology.SiteDerivedForget

end
