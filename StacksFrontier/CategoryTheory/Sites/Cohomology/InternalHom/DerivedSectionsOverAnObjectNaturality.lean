module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SectionsKInjectiveNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsNaturality
import StacksCore.Tactic.StacksAttribute

/-!
# Naturality of Stacks 08JA over an object of the site

Let `(C, O)` be a ringed site and `U` an object of `C`. **Stacks 08JA** identifies the
degree-zero hypercohomology over `U` of the derived internal Hom `RSheafHom(L, M)` with the
group of morphisms `L|_U ⟶ M|_U` in `D(O|_U)`; that identification is
`AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv`. This file proves the two clauses
that
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedSectionsOnDerivedObjects.lean`
recorded as owed for it — naturality in both variables, and the agreement with the
identification built directly from a K-flat and a K-injective complex — which were already
available for the global identification in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsNaturality`.

The two steps the global argument needs and the local one did not have were the naturality of
`Stacks.Cohomology.ModuleSections.sectionsKInjectiveIso`, now in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SectionsKInjectiveNaturality`, and
the calculus-of-fractions argument carried through
`AlgebraicGeometry.RingedSite.restrictComplex`, whose target is a morphism group of `D(O|_U)`
rather than of `D(O)`. Both are supplied here.

## Main definitions

* `AlgebraicGeometry.RingedSite.restrictComplexDerivedMap`: a morphism between the classes of
  two complexes of `O`-modules, restricted to `C/U` and read again as a morphism between the
  classes of the restricted complexes. This is what lets the fraction argument be run inside
  `D(O|_U)`: the restriction functor on derived categories does not act on classes of complexes
  on the nose, only up to `CategoryTheory.Functor.mapDerivedCategoryFactors`.
* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsFunctor`:
  `(L, M) ↦ H⁰(U, RSheafHom(L, M))` as a bifunctor on `D(O)`.
* `AlgebraicGeometry.RingedSite.modelSectionsOverObjectEquiv`: Stacks 08JA over `U`, at a model.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquivOfKInjectiveHom_naturality`: Stacks
  08JA over `U`, at a K-injective internal Hom complex, is natural in both variables for
  morphisms of complexes.
* `AlgebraicGeometry.RingedSite.modelSectionsOverObjectEquiv_naturality`: the identification at
  models is natural for an arbitrary morphism of `D(O)` in each variable.
* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_naturality`: **Stacks 08JA over an
  object of the site is natural in both variables.**
* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_eq_ofKFlat`: on the class of a
  K-flat complex and the class of a K-injective complex the identification agrees, up to the
  comparison of the restriction functor with degreewise restriction, with the identification
  built directly from those complexes.

## What this file does not contain

The **mate statement** for [Stacks, Tag 08DL] — that the comparison
`R𝓗om_O(L, M)|_U ⟶ R𝓗om_{O|_U}(L|_U, M|_U)` which 08DL asserts to be an isomorphism is the mate
`Stacks.Cohomology.SliceDerivedSheafHom.derivedSheafHomRestrictionTranspose` of the slice tensor
comparison — is still not proved. What the module documentation of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/SliceDerivedSheafHomMateSquare.lean`
named as its blocker, the identification of Stacks 08JA over an object of the site, is what this
file supplies; the square itself, read on sections over `U` against
`AlgebraicGeometry.RingedSite.derivedHomRestriction_model`, remains to be checked and nothing
here asserts it.

## Implementation notes

Three of the rewrites this argument wants are not affordable, and the structure of the file is
shaped by that. The terms involved — the uncurried derived internal Hom bifunctor composed with
derived sections over `U`, and the two identifications coerced through `DFunLike` — are large,
and `rw` must try to unify its pattern against every subterm with a matching head. When two
*different* identifications occur in one goal, matching one against the other unfolds
`AlgebraicGeometry.RingedSite.kFlatModel` and `AlgebraicGeometry.RingedSite.kInjectiveModel`,
which are `Classical.choose` of existence statements, and the elaborator's budget is gone. Since
raising the heartbeat limit is not permitted here, the rewrites are kept away from each other
instead:

* the cancellation at the end of `modelSectionsOverObjectEquiv_naturality` is performed by
  `eq_of_fraction`, a statement about six abstract morphisms of an abstract category, so that
  the only contact with the heavy terms is one first-order match at `exact`;
* in `derivedSheafHomSectionsEquiv_naturality` the two identifications are brought together only
  after the naturality at models has been rewritten into one side, which `conv_lhs` confines to
  that side;
* `restrictComplexDerivedMap_conj` is applied to the hypothesis rather than to the goal.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

/- The abelian structure on sheaves of modules is Mathlib's `SheafOfModules.instAbelian`, the one
the derived sections functors and their comparisons used here are stated with; the alternative
instance of `SiteModules` would produce a different model of the derived category. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (X : RingedSite.{u, u, u}) (U : X.C)

/-! ### Stacks 08JA over an object, at a model, naturally in morphisms of complexes -/

section AtAModel

variable (A A' I I' :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  [I.IsKInjective] [I'.IsKInjective]
  [((sheafHomComplex X A I).obj).IsKInjective]
  [((sheafHomComplex X A' I').obj).IsKInjective]

/-- The first three of the four comparisons
`derivedSheafHomSectionsEquivOfKInjectiveHom` is built from: the degree-zero hypercohomology
over `U` of `RSheafHom(A, I)` is the degree-zero cohomology of the complex of sections over `U`
of the internal Hom complex. -/
def derivedSheafHomSectionsHomologyIso :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
            (DerivedCategory.Q.obj I))) ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).obj
        (sectionComplex X (sheafHomComplex X A I).obj U) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).mapIso
          (derivedSheafHomComparison X A I) ≪≫
        (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).symm) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).app
      (sectionComplex X (sheafHomComplex X A I).obj U)

/-- **The first three comparisons are natural in both variables** for morphisms of complexes:
`homMap k m` acts on the degree-zero cohomology of the complex of sections over `U` exactly as
the derived internal Hom of the classes of `k` and `m` acts on degree-zero hypercohomology over
`U`. -/
theorem derivedSheafHomSectionsHomologyIso_naturality (k : A' ⟶ A) (m : I ⟶ I') :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
                (DerivedCategory.Q.obj I) ≫
              ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
                (DerivedCategory.Q.map m))) ≫
        (derivedSheafHomSectionsHomologyIso X U A' I').hom =
      (derivedSheafHomSectionsHomologyIso X U A I).hom ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0).map
          (sectionComplexMap X U (homMap X k m)) := by
  have h1 := derivedSheafHomComparison_naturality X k m
  have h2 : DerivedCategory.Q.map (sectionComplexMap X U (homMap X k m)) ≫
        (sectionsKInjectiveIso X U ((sheafHomComplex X A' I').obj)).hom =
      (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).hom ≫
        (Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (DerivedCategory.Q.map (homMap X k m)) :=
    sectionsKInjectiveIso_naturality X U _ _ (homMap X k m)
  have h2' : (Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (DerivedCategory.Q.map (homMap X k m)) ≫
        (sectionsKInjectiveIso X U ((sheafHomComplex X A' I').obj)).inv =
      (sectionsKInjectiveIso X U ((sheafHomComplex X A I).obj)).inv ≫
        DerivedCategory.Q.map (sectionComplexMap X U (homMap X k m)) := by
    rw [Iso.comp_inv_eq, Category.assoc, h2, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  have h3 := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.naturality
    (sectionComplexMap X U (homMap X k m))
  have h1F := congrArg (fun t => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
    ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map t)) h1
  have h2F := congrArg
    (fun t => (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map t) h2'
  dsimp only [derivedSheafHomSectionsHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.comp_map, Iso.app_hom] at h3 ⊢
  simp only [Functor.map_comp, Category.assoc] at h1F h2F h3 ⊢
  rw [reassoc_of% h1F, reassoc_of% h2F, h3]

/-- `derivedSheafHomSectionsEquivOfKInjectiveHom` is the first three comparisons followed by
Stacks 0A94 over an object. -/
theorem derivedSheafHomSectionsEquivOfKInjectiveHom_apply
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomSectionsEquivOfKInjectiveHom X U A I z =
      sheafHomSectionHomologyEquivDerivedCategoryHom X A I U
        ((derivedSheafHomSectionsHomologyIso X U A I).hom z) := rfl

/-- **Stacks 08JA over an object, at a K-injective internal Hom complex, is natural in both
variables** for morphisms of complexes: for `k : A' ⟶ A` and `m : I ⟶ I'` the identification
carries the derived internal Hom of the classes of `k` and `m` to precomposition with the class
of `k|_U` and postcomposition with the class of `m|_U`.

This is the model-level naturality of Stacks 08JA over an object. What it does *not* give is
naturality for an arbitrary morphism of `D(O)`: a morphism `Q A' ⟶ Q A` between classes of
complexes that are not K-injective is not the class of a morphism of complexes, so extending
this square to all of `D(O)` needs the calculus of fractions, which is
`modelSectionsOverObjectEquiv_naturality` below. -/
theorem derivedSheafHomSectionsEquivOfKInjectiveHom_naturality (k : A' ⟶ A) (m : I ⟶ I')
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomSectionsEquivOfKInjectiveHom X U A' I'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
                (DerivedCategory.Q.obj I) ≫
              ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
                (DerivedCategory.Q.map m))) z) =
      DerivedCategory.Q.map (restrictComplexMap X U k) ≫
        derivedSheafHomSectionsEquivOfKInjectiveHom X U A I z ≫
          DerivedCategory.Q.map (restrictComplexMap X U m) := by
  have key : (derivedSheafHomSectionsHomologyIso X U A' I').hom
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
              (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map k).op).app
                  (DerivedCategory.Q.obj I) ≫
                ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A'))).map
                  (DerivedCategory.Q.map m))) z) =
        HomologicalComplex.homologyMap (sectionComplexMap X U (homMap X k m)) 0
          ((derivedSheafHomSectionsHomologyIso X U A I).hom z) :=
    ConcreteCategory.congr_hom
      (derivedSheafHomSectionsHomologyIso_naturality X U A A' I I' k m) z
  rw [derivedSheafHomSectionsEquivOfKInjectiveHom_apply, key,
    derivedSheafHomSectionsEquivOfKInjectiveHom_apply]
  exact sheafHomSectionHomologyEquivDerivedCategoryHom_naturality X k m U _

end AtAModel

/-! ### Transporting a morphism of `D(O)` to the restricted complexes -/

section Transport

variable {A B D :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
variable [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

/-- A morphism between the classes of two complexes of `O`-modules, restricted to the site over
`U` and read again as a morphism between the classes of the restricted complexes.

The restriction functor on derived categories sends the class of a complex to an object
isomorphic to, but not equal to, the class of the degreewise restriction; the two are compared
by `CategoryTheory.Functor.mapDerivedCategoryFactors`, and this definition conjugates by it. -/
def restrictComplexDerivedMap
    (ψ : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B) :
    DerivedCategory.Q.obj (restrictComplex X A U) ⟶
      DerivedCategory.Q.obj (restrictComplex X B U) :=
  ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    U).mapDerivedCategoryFactors.app A).inv ≫
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      U).mapDerivedCategory.map ψ ≫
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategoryFactors.app B).hom

/-- The transport of the class of a morphism of complexes is the class of its restriction. -/
theorem restrictComplexDerivedMap_Q_map (k : A ⟶ B) :
    restrictComplexDerivedMap X U (DerivedCategory.Q.map k) =
      DerivedCategory.Q.map (restrictComplexMap X U k) := by
  dsimp only [restrictComplexDerivedMap, Iso.app_inv, Iso.app_hom]
  rw [Functor.mapDerivedCategoryFactors_hom_naturality, ← Category.assoc]
  simp only [Iso.inv_hom_id_app]
  rfl

/-- The transport is compatible with composition. -/
theorem restrictComplexDerivedMap_comp
    (ψ : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B)
    (χ : DerivedCategory.Q.obj B ⟶ DerivedCategory.Q.obj D) :
    restrictComplexDerivedMap X U (ψ ≫ χ) =
      restrictComplexDerivedMap X U ψ ≫ restrictComplexDerivedMap X U χ := by
  dsimp only [restrictComplexDerivedMap, Iso.app_inv, Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

/-- The transport of an isomorphism is an isomorphism. -/
instance isIso_restrictComplexDerivedMap
    (ψ : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B) [IsIso ψ] :
    IsIso (restrictComplexDerivedMap X U ψ) := by
  dsimp only [restrictComplexDerivedMap]; infer_instance

end Transport

/-! ### Stacks 08JA over an object, for arbitrary objects of the derived category -/

section Models

variable [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- `(L, M) ↦ H⁰(U, RSheafHom(L, M))`, the source of Stacks 08JA over `U`, as a bifunctor on
`D(O)`: the derived internal Hom uncurried, followed by derived sections over `U` and
degree-zero cohomology. -/
def derivedSheafHomSectionsFunctor :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      AddCommGrpCat.{u} :=
  Functor.uncurry.obj (derivedSheafHomBifunctor X) ⋙
    Stacks.Cohomology.Localization.derivedSectionsOverObject X U ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0

variable [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

/-- Stacks 08JA over `U`, at a model: a K-flat complex in the first variable and a K-injective
complex in the second. -/
def modelSectionsOverObjectEquiv (a : homModels X) :
    ((derivedSheafHomSectionsFunctor X U).obj (modelPair X a) : Type u) ≃+
      (DerivedCategory.Q.obj (restrictComplex X a.1.1 U) ⟶
        DerivedCategory.Q.obj (restrictComplex X a.2.1 U)) :=
  haveI := a.2.2
  derivedSheafHomSectionsEquivOfKFlat X U a.1.1 a.2.1 a.1.2

/-- **The identification at models is natural for morphisms of complexes.** This is
`derivedSheafHomSectionsEquivOfKInjectiveHom_naturality` read at the bifunctor
`derivedSheafHomSectionsFunctor`. -/
theorem modelSectionsOverObjectEquiv_complexMap (a b : homModels X)
    (k : b.1.1 ⟶ a.1.1) (m : a.2.1 ⟶ b.2.1)
    (z : ((derivedSheafHomSectionsFunctor X U).obj (modelPair X a) : Type u)) :
    modelSectionsOverObjectEquiv X U b
        ((derivedSheafHomSectionsFunctor X U).map
          (((DerivedCategory.Q.map k).op, DerivedCategory.Q.map m) :
            modelPair X a ⟶ modelPair X b) z) =
      restrictComplexDerivedMap X U (DerivedCategory.Q.map k) ≫
        modelSectionsOverObjectEquiv X U a z ≫
          restrictComplexDerivedMap X U (DerivedCategory.Q.map m) := by
  have := a.2.2
  have := b.2.2
  have := isKInjective_sheafHomComplex_of_isKFlat X a.1.1 a.2.1 a.1.2
  have := isKInjective_sheafHomComplex_of_isKFlat X b.1.1 b.2.1 b.1.2
  rw [restrictComplexDerivedMap_Q_map, restrictComplexDerivedMap_Q_map]
  exact derivedSheafHomSectionsEquivOfKInjectiveHom_naturality X U a.1.1 b.1.1 a.2.1 b.2.1
    k m z

/-- The cancellation of a fraction, stated about abstract morphisms of an abstract category.

Running it on the terms it is applied to would make `rw` unfold two different identifications
against each other; here the only contact with them is one first-order match. -/
private theorem eq_of_fraction {E : Type*} [Category E]
    {A B C A' B' C' : E} (rA : B ⟶ A) (rI : A' ⟶ B')
    (sA : C ⟶ B) (tA : C ⟶ A) (sI : B' ⟶ C') (tI : A' ⟶ C')
    [IsIso sA] [IsIso sI] (u : A ⟶ A') (v : B ⟶ B')
    (h1 : sA ≫ rA = tA) (h2 : rI ≫ sI = tI)
    (hb : tA ≫ u ≫ tI = sA ≫ v ≫ sI) :
    v = rA ≫ u ≫ rI := by
  rw [← h1, ← h2] at hb
  simp only [Category.assoc] at hb
  have h := (cancel_epi sA).1 hb
  refine ((cancel_mono sI).1 ?_).symm
  simpa only [Category.assoc] using h

/-- The naturality at models, once both components of the morphism have been written as
fractions with a common apex model `c`. -/
private theorem modelSectionsOverObjectEquiv_naturality_of_legs (a b c : homModels X)
    (φ : modelPair X a ⟶ modelPair X b)
    (sA : c.1.1 ⟶ b.1.1) (tA : c.1.1 ⟶ a.1.1)
    (sI : b.2.1 ⟶ c.2.1) (tI : a.2.1 ⟶ c.2.1)
    [IsIso (DerivedCategory.Q.map sA)] [IsIso (DerivedCategory.Q.map sI)]
    (h1 : DerivedCategory.Q.map sA ≫ φ.1.unop = DerivedCategory.Q.map tA)
    (h2 : φ.2 ≫ DerivedCategory.Q.map sI = DerivedCategory.Q.map tI)
    (z : ((derivedSheafHomSectionsFunctor X U).obj (modelPair X a) : Type u)) :
    modelSectionsOverObjectEquiv X U b ((derivedSheafHomSectionsFunctor X U).map φ z) =
      restrictComplexDerivedMap X U φ.1.unop ≫
        modelSectionsOverObjectEquiv X U a z ≫ restrictComplexDerivedMap X U φ.2 := by
  have hb := modelSectionsOverObjectEquiv_complexMap X U b c sA sI
    ((derivedSheafHomSectionsFunctor X U).map φ z)
  have ha := modelSectionsOverObjectEquiv_complexMap X U a c tA tI z
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hb
  have hcomp : φ ≫ (((DerivedCategory.Q.map sA).op, DerivedCategory.Q.map sI) :
        modelPair X b ⟶ modelPair X c) =
      (((DerivedCategory.Q.map tA).op, DerivedCategory.Q.map tI) :
        modelPair X a ⟶ modelPair X c) :=
    Prod.ext (Quiver.Hom.unop_inj h1) h2
  rw [hcomp, ha] at hb
  have h1' : restrictComplexDerivedMap X U (DerivedCategory.Q.map sA) ≫
        restrictComplexDerivedMap X U φ.1.unop =
      restrictComplexDerivedMap X U (DerivedCategory.Q.map tA) := by
    rw [← restrictComplexDerivedMap_comp, h1]
  have h2' : restrictComplexDerivedMap X U φ.2 ≫
        restrictComplexDerivedMap X U (DerivedCategory.Q.map sI) =
      restrictComplexDerivedMap X U (DerivedCategory.Q.map tI) := by
    rw [← restrictComplexDerivedMap_comp, h2]
  exact eq_of_fraction (restrictComplexDerivedMap X U φ.1.unop)
    (restrictComplexDerivedMap X U φ.2)
    (restrictComplexDerivedMap X U (DerivedCategory.Q.map sA))
    (restrictComplexDerivedMap X U (DerivedCategory.Q.map tA))
    (restrictComplexDerivedMap X U (DerivedCategory.Q.map sI))
    (restrictComplexDerivedMap X U (DerivedCategory.Q.map tI))
    (modelSectionsOverObjectEquiv X U a z)
    (modelSectionsOverObjectEquiv X U b ((derivedSheafHomSectionsFunctor X U).map φ z))
    h1' h2' hb

/-- **The identification at models over `U` is natural for an arbitrary morphism of `D(O)` in
each variable.** Each of the two components of the morphism is factored as a fraction through a
third complex, contravariantly in the first slot and covariantly in the second; the apex is made
into a model by a K-flat resolution in the first slot and the K-injective resolution in the
second. Both legs of the resulting pair of fractions are then classes of morphisms of complexes,
where naturality is `modelSectionsOverObjectEquiv_complexMap`, and the denominator is
invertible. -/
theorem modelSectionsOverObjectEquiv_naturality (a b : homModels X)
    (φ : modelPair X a ⟶ modelPair X b)
    (z : ((derivedSheafHomSectionsFunctor X U).obj (modelPair X a) : Type u)) :
    modelSectionsOverObjectEquiv X U b ((derivedSheafHomSectionsFunctor X U).map φ z) =
      restrictComplexDerivedMap X U φ.1.unop ≫
        modelSectionsOverObjectEquiv X U a z ≫ restrictComplexDerivedMap X U φ.2 := by
  obtain ⟨A₀, sk, hsk, gk, hk⟩ := DerivedCategory.right_fac φ.1.unop
  obtain ⟨I₀, gi, si, hsi, hi⟩ := DerivedCategory.left_fac φ.2
  obtain ⟨AF, qA, hAF, hqA⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X A₀
  have := hqA
  have := hsk
  have := hsi
  have : IsIso (DerivedCategory.Q.map (qA ≫ sk)) := by
    rw [Functor.map_comp]; infer_instance
  have : IsIso (DerivedCategory.Q.map (si ≫ (kInjectiveAugmentation X).app I₀)) := by
    rw [Functor.map_comp]; infer_instance
  refine modelSectionsOverObjectEquiv_naturality_of_legs X U a b
    (⟨AF, hAF⟩, ⟨(kInjectiveResolution X).obj I₀, inferInstance⟩) φ (qA ≫ sk) (qA ≫ gk)
    (si ≫ (kInjectiveAugmentation X).app I₀) (gi ≫ (kInjectiveAugmentation X).app I₀) ?_ ?_ z
  · rw [Functor.map_comp, Functor.map_comp, hk, Category.assoc, IsIso.hom_inv_id_assoc]
  · rw [Functor.map_comp, Functor.map_comp, hi, Category.assoc, IsIso.inv_hom_id_assoc]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The transport of a morphism of `D(O)` conjugated by chosen representatives is that morphism
restricted to `C/U`, conjugated by `restrictModelIso`. -/
theorem restrictComplexDerivedMap_conj
    {L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) (eB : DerivedCategory.Q.obj B ≅ M) (f : L ⟶ M) :
    restrictComplexDerivedMap X U (eA.hom ≫ f ≫ eB.inv) =
      (restrictModelIso X U eA).hom ≫
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.map f ≫
          (restrictModelIso X U eB).inv := by
  dsimp only [restrictComplexDerivedMap, restrictModelIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_inv,
    Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc]

/-- `derivedSheafHomSectionsEquiv` is the identification at the chosen model, transported along
the chosen representatives. -/
theorem derivedSheafHomSectionsEquiv_apply
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomSectionsEquiv X U L M z =
      ((restrictModelIso X U (kFlatModelIso X L)).inv ≫
          modelSectionsOverObjectEquiv X U (chosenHomModel X L M)
            ((derivedSheafHomSectionsFunctor X U).map (chosenHomModelMap X L M) z)) ≫
        (restrictModelIso X U (kInjectiveModelIso X M)).hom := rfl

/-- **Stacks 08JA over an object of the site is natural in both variables.** For arbitrary
morphisms `f : L' ⟶ L` and `g : M ⟶ M'` of `D(O)`, the identification of the degree-zero
hypercohomology over `U` of `RSheafHom(L, M)` with `Hom_{D(O|_U)}(L|_U, M|_U)` carries the
derived internal Hom of `f` and `g` to precomposition with `f|_U` and postcomposition with
`g|_U`. -/
@[stacks 08JA "sections over an object, naturality in both variables"]
theorem derivedSheafHomSectionsEquiv_naturality
    {L L' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : L' ⟶ L) (g : M ⟶ M')
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomSectionsEquiv X U L' M'
        ((derivedSheafHomSectionsFunctor X U).map
          ((f.op, g) : ((op L, M) :
              (DerivedCategory
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
              DerivedCategory (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
              (op L', M')) z) =
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategory.map f ≫
        derivedSheafHomSectionsEquiv X U L M z ≫
          (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategory.map g := by
  have hψ : ((f.op, g) : ((op L, M) :
      (DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
      DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
      (op L', M')) ≫
        chosenHomModelMap X L' M' =
      chosenHomModelMap X L M ≫
        ((((kFlatModelIso X L').hom ≫ f ≫ (kFlatModelIso X L).inv).op,
          (kInjectiveModelIso X M).hom ≫ g ≫ (kInjectiveModelIso X M').inv) :
          modelPair X (chosenHomModel X L M) ⟶ modelPair X (chosenHomModel X L' M')) := by
    refine Prod.ext ?_ ?_
    · apply Quiver.Hom.unop_inj
      simp [Category.assoc]
    · simp [Category.assoc]
  have hnat := modelSectionsOverObjectEquiv_naturality X U (chosenHomModel X L M)
    (chosenHomModel X L' M')
    ((((kFlatModelIso X L').hom ≫ f ≫ (kFlatModelIso X L).inv).op,
        (kInjectiveModelIso X M).hom ≫ g ≫ (kInjectiveModelIso X M').inv) :
      modelPair X (chosenHomModel X L M) ⟶ modelPair X (chosenHomModel X L' M'))
    ((derivedSheafHomSectionsFunctor X U).map (chosenHomModelMap X L M) z)
  rw [Quiver.Hom.unop_op, restrictComplexDerivedMap_conj, restrictComplexDerivedMap_conj] at hnat
  have hL := derivedSheafHomSectionsEquiv_apply X U L M z
  have hL' := derivedSheafHomSectionsEquiv_apply X U L' M'
    ((derivedSheafHomSectionsFunctor X U).map
      ((f.op, g) : ((op L, M) :
          (DerivedCategory
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
          DerivedCategory (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
          (op L', M')) z)
  have hmerge : (derivedSheafHomSectionsFunctor X U).map (chosenHomModelMap X L' M')
        ((derivedSheafHomSectionsFunctor X U).map
          ((f.op, g) : ((op L, M) :
              (DerivedCategory
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
              DerivedCategory (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
              (op L', M')) z) =
      (derivedSheafHomSectionsFunctor X U).map
          ((((kFlatModelIso X L').hom ≫ f ≫ (kFlatModelIso X L).inv).op,
              (kInjectiveModelIso X M).hom ≫ g ≫ (kInjectiveModelIso X M').inv) :
            modelPair X (chosenHomModel X L M) ⟶ modelPair X (chosenHomModel X L' M'))
        ((derivedSheafHomSectionsFunctor X U).map (chosenHomModelMap X L M) z) := by
    have := congrArg (fun t => (derivedSheafHomSectionsFunctor X U).map t
      (show ((derivedSheafHomSectionsFunctor X U).obj (op L, M) : Type u) from z)) hψ
    rw [Functor.map_comp, Functor.map_comp] at this
    exact this
  have hstep := congrArg
    (fun w => modelSectionsOverObjectEquiv X U (chosenHomModel X L' M') w) hmerge
  rw [hL', hL]
  conv_lhs => rw [hstep.trans hnat]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- **Stacks 08JA over an object is the identification at *any* model, not only at the chosen
one.** The chosen representatives of `Q A` and `Q I` are different complexes, so this is a
statement and not a definitional unfolding; it is the naturality at models applied to the
comparison morphism between the given model and the chosen one.

The two sides live in different, canonically isomorphic, Hom groups: the identification of
`derivedSheafHomSectionsEquiv` has the image of the objects under the restriction functor on
derived categories for its target, and the identification at a model has the classes of the
degreewise restrictions. They are compared by
`CategoryTheory.Functor.mapDerivedCategoryFactors`. -/
theorem derivedSheafHomSectionsEquiv_eq_modelSectionsOverObjectEquiv (a : homModels X)
    (z : ((derivedSheafHomSectionsFunctor X U).obj (modelPair X a) : Type u)) :
    derivedSheafHomSectionsEquiv X U (DerivedCategory.Q.obj a.1.1)
          (DerivedCategory.Q.obj a.2.1) z =
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategoryFactors.app a.1.1).hom ≫
        modelSectionsOverObjectEquiv X U a z ≫
          ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategoryFactors.app a.2.1).inv := by
  have hnat := modelSectionsOverObjectEquiv_naturality X U a
    (chosenHomModel X (DerivedCategory.Q.obj a.1.1) (DerivedCategory.Q.obj a.2.1))
    (chosenHomModelMap X (DerivedCategory.Q.obj a.1.1) (DerivedCategory.Q.obj a.2.1)) z
  have hL := derivedSheafHomSectionsEquiv_apply X U (DerivedCategory.Q.obj a.1.1)
    (DerivedCategory.Q.obj a.2.1) z
  rw [hL]
  conv_lhs => rw [hnat]
  dsimp only [restrictComplexDerivedMap, restrictModelIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_inv,
    Iso.app_hom, Quiver.Hom.unop_op]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id]
  simp

/-- **Stacks 08JA over an object, at a K-flat source and a K-injective target, is the
identification built from those complexes.** This is
`derivedSheafHomSectionsEquiv_eq_modelSectionsOverObjectEquiv` spelled at a pair of
complexes. -/
theorem derivedSheafHomSectionsEquiv_eq_ofKFlat
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective]
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    derivedSheafHomSectionsEquiv X U (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) z =
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        U).mapDerivedCategoryFactors.app A).hom ≫
        derivedSheafHomSectionsEquivOfKFlat X U A I hA z ≫
          ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            U).mapDerivedCategoryFactors.app I).inv :=
  derivedSheafHomSectionsEquiv_eq_modelSectionsOverObjectEquiv X U
    (⟨A, hA⟩, ⟨I, inferInstance⟩) z

end Models

end AlgebraicGeometry.RingedSite

end
