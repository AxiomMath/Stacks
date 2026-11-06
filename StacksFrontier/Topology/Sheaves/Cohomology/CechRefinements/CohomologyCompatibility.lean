module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.RefinementDerivedCompatibility
public import StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.CechCohomologyOfPushforward
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechRefinements.DerivedSectionsScalarComparison
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.DerivedGlobalSectionsViaResolutions
public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.DegreeZeroAndTheSheafCondition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Compatibility of Čech refinement with derived global sections

Let `f : X ⟶ Y` be a morphism of ringed spaces, let `φ : f^* G ⟶ F` be an `f`-map of sheaves of
modules, and let an open covering `U` of `X` refine the inverse image of an open covering `V` of
`Y`. [Stacks, Tag 01FD] is the statement that the Čech refinement map commutes with the
canonical comparisons of [Stacks, Tag 01EQ] from the Čech complex of a covering to derived
global sections, the source read over `Γ(Y, 𝒪_Y)` and the right-hand vertical arrow being the
functorial map of [Stacks, Tag 01F9]. This file proves it, together with its reading on
cohomology.

The mathematical input is assembled elsewhere: the Čech refinement map on total complexes and
its two augmentation squares, the Čech acyclicity of pushforwards of injectives, and the
presentation of the functorial map as the roof of [Stacks, Tag 01FB]. What is done here is the
identification of the two resolution comparisons on derived global sections -- the one built in
[Stacks, Tag 01EQ] out of the unit of the right derived functor and the one built in
[Stacks, Tag 01FB] out of the resolution map -- and the assembly of the square out of it.

## Main results

* `Stacks.Cohomology.CechRefinement.cechToDerivedGlobalSections_naturality_of_refinement` is
  [Stacks, Tag 01FD]: the commutative square in the bounded-below derived category of modules
  over the global sections of the structure sheaf of the target.
* `Stacks.Cohomology.CechRefinement.cechCohomologyToCohomology_naturality_of_refinement` is the
  same square read through the `p`-th homology, i.e. on Čech and sheaf cohomology.
* `DerivedCategory.Plus.ι_map_qhHomMk`: a morphism out of a complex concentrated in degree
  zero, read in the bounded-below derived category, is its image under the unbounded
  localization functor.
* `CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit_app_comp_resolutionIso_hom`: the
  derived-functor unit at an injective resolution, followed by the resolution comparison of
  [Stacks, Tag 01FB], is the identity.
* `Stacks.Cohomology.CechDerived.injectiveResolutionToDerivedGlobalSections_comp_resolutionIso`:
  the same statement for the identification of [Stacks, Tag 01EQ].
* `Stacks.Cohomology.scalarRestrictionUnit_resolution`: the derived scalar-restriction unit at
  an injective resolution inverts the resolution comparison for the composite of global
  sections with restriction of scalars.

## Implementation notes

The bounded-below derived category is a full subcategory of the unbounded one, and the
comparisons `DerivedCategory.Plus.quotientCompQhIso` and
`DerivedCategory.Plus.singleFunctorIsoCompQh` are obtained from the unbounded ones by
cancelling that embedding; the first three lemmas record that their images under the embedding
are the unbounded comparisons, which is what makes the two resolution comparisons comparable at
all. Every rearrangement that crosses the embedding is hoisted into a lemma stated on
variables, so that the two definitionally equal spellings of a junction object never have to be
reconciled by `rw`.

The same discipline runs through the assembly. The reduction of the square to the commutative
square on the total complexes is `Stacks.Cohomology.CechRefinement.main_reduction`, stated on
fifteen abstract morphisms, and the degree-zero content of the lifting square of
[Stacks, Tag 01FB] is `Stacks.Cohomology.CechRefinement.hom_f_zero_of_single_lift`, stated for
an abstract additive functor: the comparisons of `HomologicalComplex.single` with
`CategoryTheory.Functor.mapHomologicalComplex` are not matched by `rw` at the concrete
spellings, but their abstract statements are instantiated by unification. The choices of
resolutions are made once, in the proof of the tagged theorem, and everything else is a lemma
taking them as parameters, so that no single elaboration carries the whole square.

## References

* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
* [Stacks Project, Tag 01EQ](https://stacks.math.columbia.edu/tag/01EQ)
* [Stacks Project, Tag 01FB](https://stacks.math.columbia.edu/tag/01FB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape Opposite
open TopologicalSpace

universe v v' w w' u u'

namespace DerivedCategory.Plus

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **The bounded-below factorization of the localization functor through the homotopy category
is the unbounded one.** Both sides compare the two readings of a bounded-below cochain complex
in the derived category; the bounded-below one is obtained from the unbounded one by cancelling
the fully faithful embedding, so its image under that embedding is the unbounded one. -/
lemma ι_map_quotientCompQhIso_hom_app (K : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.map ((quotientCompQhIso A).hom.app K) =
      (DerivedCategory.quotientCompQhIso A).hom.app K.obj :=
  rfl

/-- The inverse form of `DerivedCategory.Plus.ι_map_quotientCompQhIso_hom_app`. -/
lemma ι_map_quotientCompQhIso_inv_app (K : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.map ((quotientCompQhIso A).inv.app K) =
      (DerivedCategory.quotientCompQhIso A).inv.app K.obj := by
  refine (cancel_epi (DerivedCategory.Plus.ι.map ((quotientCompQhIso A).hom.app K))).mp ?_
  rw [← DerivedCategory.Plus.ι.map_comp, Iso.hom_inv_id_app, DerivedCategory.Plus.ι.map_id,
    ι_map_quotientCompQhIso_hom_app]
  exact ((DerivedCategory.quotientCompQhIso A).hom_inv_id_app K.obj).symm

/-- **The bounded-below factorization of the single functor through the homotopy category is
the unbounded one**, read through the fully faithful embedding of the bounded-below derived
category. -/
lemma ι_map_singleFunctorIsoCompQh_hom_app (Z : A) :
    DerivedCategory.Plus.ι.map ((singleFunctorIsoCompQh A 0).hom.app Z) =
      (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app Z := by
  have hstep : DerivedCategory.Plus.ι.map ((singleFunctorIsoCompQh A 0).hom.app Z) =
      𝟙 _ ≫ (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app Z ≫
        DerivedCategory.Qh.map
          ((HomotopyCategory.Plus.singleFunctorCompιIso A 0).inv.app Z) ≫ 𝟙 _ := by
    rw [singleFunctorIsoCompQh, Functor.fullyFaithfulCancelRight_hom_app,
      CategoryTheory.Functor.map_preimage]
    rfl
  have hz : DerivedCategory.Qh.map
      ((HomotopyCategory.Plus.singleFunctorCompιIso A 0).inv.app Z) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  rw [hstep, hz]
  exact (Category.id_comp _).trans ((congrArg _ (Category.id_comp _)).trans (Category.comp_id _))

/-- **A morphism out of a complex concentrated in degree zero, read in the bounded-below
derived category, is its image under the unbounded localization functor.** This pins
`DerivedCategory.Plus.qhHomMk` down, and is how the comparison of a sheaf of modules with an
injective resolution used by [Stacks, Tag 01EQ] is identified with the one used by
[Stacks, Tag 01FB]. -/
lemma ι_map_qhHomMk (Z : A) {K : CochainComplex A ℤ} (hK : CochainComplex.plus A K)
    (u : (CochainComplex.singleFunctor A 0).obj Z ⟶ K) :
    DerivedCategory.Plus.ι.map (qhHomMk Z hK u) ≫
        (DerivedCategory.quotientCompQhIso A).hom.app K =
      DerivedCategory.Q.map u := by
  have h1 := ι_map_singleFunctorIsoCompQh_hom_app (A := A) Z
  have h4 : DerivedCategory.Plus.ι.map (qhHomMk Z hK u) =
      (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app Z ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map u) :=
    (DerivedCategory.Plus.ι.map_comp _ _).trans
      (congrArg (fun z => z ≫ DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map u)) h1)
  have hkey : (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app Z ≫
      (DerivedCategory.quotientCompQhIso A).hom.app
        ((CochainComplex.singleFunctor A 0).obj Z) = 𝟙 _ := by
    have hq : (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app Z =
        (DerivedCategory.quotientCompQhIso A).inv.app
          ((CochainComplex.singleFunctor A 0).obj Z) ≫ 𝟙 _ := rfl
    rw [hq, Category.comp_id]
    exact (DerivedCategory.quotientCompQhIso A).inv_hom_id_app _
  refine Eq.trans
    (congrArg (fun z => z ≫ (DerivedCategory.quotientCompQhIso A).hom.app K) h4) ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg
    (fun z => (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app Z ≫ z)
    (DerivedCategory.quotientCompQhIso_hom_naturality u)) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ DerivedCategory.Q.map u) hkey) ?_
  exact Category.id_comp _

end DerivedCategory.Plus

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B] [EnoughInjectives A]

/-- **The derived-functor unit at an injective resolution inverts the resolution comparison.**
Let `I` be an injective resolution of `Z[0]` and let `w` be the comparison of `Z[0]` with the
image of `I` in the bounded-below derived category, pinned by the hypothesis `hw` that it is
the localized resolution map. Then the unit of this file at `I`, followed by the image under
the right derived functor of `w⁻¹`, is the inverse of
`CategoryTheory.Functor.rightDerivedFunctorPlusInjectiveResolutionIso`.

This is the identification required by [Stacks, Tag 01FD]: the comparison of the Čech complex
with derived global sections of [Stacks, Tag 01EQ] is built from this unit, and the comparisons
of [Stacks, Tag 01FB] from `rightDerivedFunctorPlusInjectiveResolutionIso`. -/
lemma mapCochainComplexPlusDerivedUnit_app_comp_map_eq_resolutionIso_inv
    (T : A ⥤ B) [T.Additive] (Z : A)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj Z))
    (w : (DerivedCategory.Plus.singleFunctor A 0).obj Z ≅
      DerivedCategory.Plus.Q.obj ⟨I.cocomplex, I.boundedBelow⟩)
    (hw : DerivedCategory.Plus.ι.map w.hom = DerivedCategory.Q.map I.ι) :
    DerivedCategory.Plus.ι.map ((mapCochainComplexPlusDerivedUnit T).app
          ⟨I.cocomplex, I.boundedBelow⟩ ≫ T.rightDerivedFunctorPlus.map w.inv) =
      (T.rightDerivedFunctorPlusInjectiveResolutionIso Z I).inv := by
  have hwhom : w.hom = (CochainComplex.InjectiveResolution.qhIso Z I).hom ≫
      (DerivedCategory.Plus.quotientCompQhIso A).hom.app ⟨I.cocomplex, I.boundedBelow⟩ := by
    refine DerivedCategory.Plus.ι.map_injective (hw.trans ?_)
    refine Eq.symm ((DerivedCategory.Plus.ι.map_comp _ _).trans ?_)
    refine Eq.trans (congrArg (fun z => DerivedCategory.Plus.ι.map
        (CochainComplex.InjectiveResolution.qhIso Z I).hom ≫ z)
      (DerivedCategory.Plus.ι_map_quotientCompQhIso_hom_app
        (⟨I.cocomplex, I.boundedBelow⟩ : CochainComplex.Plus A))) ?_
    exact DerivedCategory.Plus.ι_map_qhHomMk Z I.boundedBelow I.ι
  have hwinv : w.inv = (DerivedCategory.Plus.quotientCompQhIso A).inv.app
        ⟨I.cocomplex, I.boundedBelow⟩ ≫
      (CochainComplex.InjectiveResolution.qhIso Z I).inv := by
    have h1 : w.hom ≫ ((DerivedCategory.Plus.quotientCompQhIso A).inv.app
        ⟨I.cocomplex, I.boundedBelow⟩ ≫
          (CochainComplex.InjectiveResolution.qhIso Z I).inv) = 𝟙 _ := by
      rw [hwhom]
      simp
    exact (IsIso.inv_eq_of_hom_inv_id w.hom_inv_id).symm.trans
      (IsIso.inv_eq_of_hom_inv_id h1)
  have hcancel : T.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.quotientCompQhIso A).hom.app
          ⟨I.cocomplex, I.boundedBelow⟩) ≫
      T.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.quotientCompQhIso A).inv.app
            ⟨I.cocomplex, I.boundedBelow⟩ ≫
          (CochainComplex.InjectiveResolution.qhIso Z I).inv) =
      T.rightDerivedFunctorPlus.map (CochainComplex.InjectiveResolution.qhIso Z I).inv := by
    rw [← CategoryTheory.Functor.map_comp, ← Category.assoc,
      (DerivedCategory.Plus.quotientCompQhIso A).hom_inv_id_app, Category.id_comp]
  have hA : (mapCochainComplexPlusDerivedUnit T).app ⟨I.cocomplex, I.boundedBelow⟩ ≫
        T.rightDerivedFunctorPlus.map w.inv =
      (DerivedCategory.Plus.quotientCompQhIso B).inv.app
          (T.mapCochainComplexPlus.obj ⟨I.cocomplex, I.boundedBelow⟩) ≫
        T.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient A).obj ⟨I.cocomplex, I.boundedBelow⟩) ≫
          T.rightDerivedFunctorPlus.map
            (CochainComplex.InjectiveResolution.qhIso Z I).inv := by
    rw [mapCochainComplexPlusDerivedUnit_app, hwinv]
    refine (Category.assoc _ _ _).trans ?_
    refine congrArg (fun z => (DerivedCategory.Plus.quotientCompQhIso B).inv.app
        (T.mapCochainComplexPlus.obj ⟨I.cocomplex, I.boundedBelow⟩) ≫ z)
      ((Category.assoc _ _ _).trans (congrArg (fun z =>
        T.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient A).obj ⟨I.cocomplex, I.boundedBelow⟩) ≫ z) hcancel))
  have hQh : (T.mapHomologicalComplexQhIso I.boundedBelow).inv =
      (DerivedCategory.quotientCompQhIso B).inv.app
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cocomplex) := by
    have hstep : (T.mapHomologicalComplexQhIso I.boundedBelow).inv =
        (DerivedCategory.quotientCompQhIso B).inv.app
            ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cocomplex) ≫
          DerivedCategory.Qh.map ((T.mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app I.cocomplex) := rfl
    have hz : DerivedCategory.Qh.map ((T.mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv.app I.cocomplex) = 𝟙 _ := CategoryTheory.Functor.map_id _ _
    rw [hstep, hz]
    exact Category.comp_id _
  refine Eq.trans (congrArg DerivedCategory.Plus.ι.map hA) ?_
  refine (DerivedCategory.Plus.ι.map_comp _ _).trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ DerivedCategory.Plus.ι.map
    (T.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient A).obj ⟨I.cocomplex, I.boundedBelow⟩) ≫
      T.rightDerivedFunctorPlus.map (CochainComplex.InjectiveResolution.qhIso Z I).inv))
    ((DerivedCategory.Plus.ι_map_quotientCompQhIso_inv_app
      (T.mapCochainComplexPlus.obj ⟨I.cocomplex, I.boundedBelow⟩)).trans hQh.symm)) ?_
  refine Eq.trans (congrArg (fun z => (T.mapHomologicalComplexQhIso I.boundedBelow).inv ≫ z)
    (DerivedCategory.Plus.ι.map_comp _ _)) ?_
  exact (Category.assoc _ _ _).symm

/-- **The derived-functor unit at an injective resolution, followed by the resolution
comparison, is the identity.** This is the form in which [Stacks, Tag 01FD] consumes
`CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit_app_comp_map_eq_resolutionIso_inv`. -/
lemma mapCochainComplexPlusDerivedUnit_app_comp_resolutionIso_hom
    (T : A ⥤ B) [T.Additive] (Z : A)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor A 0).obj Z))
    (w : (DerivedCategory.Plus.singleFunctor A 0).obj Z ≅
      DerivedCategory.Plus.Q.obj ⟨I.cocomplex, I.boundedBelow⟩)
    (hw : DerivedCategory.Plus.ι.map w.hom = DerivedCategory.Q.map I.ι) :
    DerivedCategory.Plus.ι.map ((mapCochainComplexPlusDerivedUnit T).app
          ⟨I.cocomplex, I.boundedBelow⟩ ≫ T.rightDerivedFunctorPlus.map w.inv) ≫
        (T.rightDerivedFunctorPlusInjectiveResolutionIso Z I).hom = 𝟙 _ :=
  (congrArg (fun z => z ≫ (T.rightDerivedFunctorPlusInjectiveResolutionIso Z I).hom)
    (mapCochainComplexPlusDerivedUnit_app_comp_map_eq_resolutionIso_inv T Z I w hw)).trans
    (T.rightDerivedFunctorPlusInjectiveResolutionIso Z I).inv_hom_id

end CategoryTheory.Functor

namespace Stacks.Cohomology.CechDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Reassociation of a four-fold composite, stated on variables so that it can be applied at
the two definitionally equal spellings of a junction object without any transport. -/
private lemma assoc₄ {D : Type*} [Category* D] {W₀ W₁ W₂ W₃ W₄ : D}
    (p : W₀ ⟶ W₁) (q : W₁ ⟶ W₂) (r : W₂ ⟶ W₃) (s : W₃ ⟶ W₄) :
    (p ≫ q ≫ r) ≫ s = p ≫ q ≫ r ≫ s := by
  rw [Category.assoc, Category.assoc]

variable {X : Type u} [TopologicalSpace X]
  (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} O)]

omit [EnoughInjectives (SheafOfModules.{u} O)] in
/-- **The comparison of a sheaf of modules with an injective resolution is the localized
resolution map.** This is the hypothesis under which
`CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit_app_comp_resolutionIso_hom` applies to
the resolution comparison of [Stacks, Tag 01EQ]. -/
lemma ι_map_injectiveResolutionIso_hom (F : SheafOfModules.{u} O) (J : InjectiveResolution F) :
    DerivedCategory.Plus.ι.map (injectiveResolutionIso O F J).hom =
      DerivedCategory.Q.map (CategoryTheory.InjectiveResolution.toCochainComplex F J).ι :=
  rfl

/-- **The identification of the sections of an injective resolution with derived sections is
the derived-functor unit at the resolution.** The transformation of [Stacks, Tag 01EQ] is built
from the unit of the right derived functor of sections and the resolution comparison, which is
exactly `CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit` followed by the image of the
inverse of that comparison. -/
lemma injectiveResolutionToDerivedGlobalSections_eq_derivedUnit
    (F : SheafOfModules.{u} O) (J : InjectiveResolution F) :
    injectiveResolutionToDerivedGlobalSections O U F J =
      DerivedCategory.Plus.ι.map
        ((Functor.mapCochainComplexPlusDerivedUnit
              (SheafOfModules.evaluation.{u} O (op U))).app
            ⟨J.cochainComplex, 0, inferInstance⟩ ≫
          (SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus.map
            (injectiveResolutionIso O F J).inv) := by
  have h2 : (DerivedCategory.Plus.quotientCompQhIso (SheafOfModules.{u} O)).hom.app
        (⟨J.cochainComplex, 0, inferInstance⟩ : CochainComplex.Plus (SheafOfModules.{u} O)) =
      ObjectProperty.homMk ((DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} O)).hom.app J.cochainComplex) :=
    ObjectProperty.hom_ext _ (DerivedCategory.Plus.ι_map_quotientCompQhIso_hom_app _)
  have h1 : (DerivedCategory.Plus.quotientCompQhIso _).inv.app
        ((SheafOfModules.evaluation.{u} O (op U)).mapCochainComplexPlus.obj
          (⟨J.cochainComplex, 0, inferInstance⟩ : CochainComplex.Plus (SheafOfModules.{u} O))) =
      ObjectProperty.homMk ((DerivedCategory.quotientCompQhIso _).inv.app
        (((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J.cochainComplex)) :=
    ObjectProperty.hom_ext _ (DerivedCategory.Plus.ι_map_quotientCompQhIso_inv_app _)
  symm
  rw [Functor.mapCochainComplexPlusDerivedUnit_app, h1, h2]
  exact assoc₄ _ _ _ _

/-- **The identification of the sections of an injective resolution with derived sections
inverts the resolution comparison of [Stacks, Tag 01FB].** -/
lemma injectiveResolutionToDerivedGlobalSections_comp_resolutionIso
    (F : SheafOfModules.{u} O) (J : InjectiveResolution F) :
    injectiveResolutionToDerivedGlobalSections O U F J ≫
        ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlusInjectiveResolutionIso F
          (CategoryTheory.InjectiveResolution.toCochainComplex F J)).hom = 𝟙 _ :=
  (congrArg (fun z => z ≫
      ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlusInjectiveResolutionIso F
        (CategoryTheory.InjectiveResolution.toCochainComplex F J)).hom)
    (injectiveResolutionToDerivedGlobalSections_eq_derivedUnit O U F J)).trans
    (Functor.mapCochainComplexPlusDerivedUnit_app_comp_resolutionIso_hom
      (SheafOfModules.evaluation.{u} O (op U)) F
      (CategoryTheory.InjectiveResolution.toCochainComplex F J)
      (injectiveResolutionIso O F J) (ι_map_injectiveResolutionIso_hom O F J))

section Comparison

variable {Ic : Type u} (Ui : Ic → Opens X) (hUi : U = ⨆ i, Ui i)
  {τ : cechComplexPlusFunctor O U Ui hUi ⋙ DerivedCategory.Plus.Q ⟶
    derivedGlobalSectionsFunctor O U}
  (F : SheafOfModules.{u} O) (JF : InjectiveResolution F)
  (cF : CechResolutionComparison O U Ui hUi τ F JF)

/-- **The localized augmentation of a Čech resolution comparison is invertible**, being the
isomorphism recorded in the structure. This is the hypothesis under which [Stacks, Tag 01FD]
inverts it. -/
lemma isIso_Q_map_cechResolutionComparison_α : IsIso (DerivedCategory.Q.map cF.α) := by
  rw [← cF.αIso_hom]
  infer_instance

/-- **A Čech resolution comparison presents the transformation as a roof.** This is the
`comparison` field of `Stacks.Cohomology.CechDerived.CechResolutionComparison` with the
structure's isomorphism replaced by the inverse of the localized augmentation, which is the
form in which [Stacks, Tag 01FD] consumes it. -/
lemma cechResolutionComparison_app_hom [IsIso (DerivedCategory.Q.map cF.α)] :
    (τ.app F).hom = DerivedCategory.Q.map cF.β ≫ inv (DerivedCategory.Q.map cF.α) ≫
      injectiveResolutionToDerivedGlobalSections O U F JF := by
  refine cF.comparison.trans ?_
  refine congrArg (fun z ↦ DerivedCategory.Q.map cF.β ≫ z ≫
    injectiveResolutionToDerivedGlobalSections O U F JF) ?_
  have h : DerivedCategory.Q.map cF.α ≫ cF.αIso.inv = 𝟙 _ := by
    rw [← cF.αIso_hom]
    exact cF.αIso.hom_inv_id
  exact (IsIso.inv_eq_of_hom_inv_id h).symm

/-- **The second augmentation of a Čech resolution comparison is `β` at the augmentation of the
resolution**, since both are determined by their components. -/
lemma cechResolutionComparison_β_eq :
    cF.β = cechBeta O U Ui hUi JF.cochainComplex (CechTotalComparison.resolutionAug JF)
      (CechTotalComparison.resolutionAug_comp_d JF) :=
  HomologicalComplex.hom_ext _ _ fun p ↦ (cF.β_f p).trans
    (cechBeta_f O U Ui hUi JF.cochainComplex _ _ p).symm

/-- **The first augmentation of a Čech resolution comparison is the total Čech
augmentation**, since both are determined by their components. -/
lemma cechResolutionComparison_α_eq
    (hJF : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((cechComplexNatFunctor O U Ui hUi).obj (JF.cochainComplex.X q)).homology n)) :
    cF.α = cechTotalAugmentation O U Ui hUi JF.cochainComplex hJF :=
  eq_cechTotalAugmentation O U Ui hUi JF.cochainComplex hJF cF.α cF.α_f

end Comparison

end

end Stacks.Cohomology.CechDerived

namespace Stacks.Cohomology

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local implicit_reducible] TopCat.Sheaf

/-- The four-term rearrangement used by `Stacks.Cohomology.scalarRestrictionUnit_resolution`,
stated on variables so that it can be instantiated at the two definitionally equal spellings of
the junction objects without any transport. -/
private lemma comp_eq_of_unit_comp_of_naturality {D : Type*} [Category* D]
    {V₀ V₁ V₂ V₃ V₄ V₅ : D}
    (a₁ : V₀ ⟶ V₁) (a₂ : V₁ ⟶ V₂) (a₃ : V₂ ⟶ V₃) (a₄ : V₃ ⟶ V₄)
    (b₁ : V₀ ⟶ V₅) (b₂ : V₅ ⟶ V₂) (b₃ : V₅ ⟶ V₄) (b₄ : V₄ ⟶ V₃)
    (hcomp : b₁ ≫ b₂ = a₁ ≫ a₂) (hnat : b₃ ≫ b₄ = b₂ ≫ a₃) (hid : b₄ ≫ a₄ = 𝟙 V₄) :
    a₁ ≫ (a₂ ≫ a₃) ≫ a₄ = b₁ ≫ b₃ := by
  rw [Category.assoc, ← reassoc_of% hcomp, ← reassoc_of% hnat, hid, Category.comp_id]

/-- The rearrangement of a roof against a four-fold composite used by
`Stacks.Cohomology.scalarRestrictionUnit_cechResolution`, stated on variables. -/
private lemma roof_rearrange {D : Type*} [Category* D] {W₀ W₁ W₂ W₃ W₄ W₅ W₆ : D}
    (p : W₀ ⟶ W₁) (q : W₁ ⟶ W₂) (r : W₀ ⟶ W₃) (s : W₃ ⟶ W₄) (t : W₄ ⟶ W₂)
    (m : W₂ ⟶ W₅) (n : W₅ ⟶ W₆) (h : p ≫ q = r ≫ s ≫ t) :
    p ≫ (q ≫ m) ≫ n = r ≫ s ≫ t ≫ m ≫ n := by
  rw [Category.assoc, reassoc_of% h]

/-- The cancellation of a split tail inside a three-fold composite, stated on variables. -/
private lemma assoc_comp_id {D : Type*} [Category* D] {W₀ W₁ W₂ W₃ : D}
    (r : W₀ ⟶ W₁) (s : W₁ ⟶ W₂) (w : W₂ ⟶ W₃) (g : W₃ ⟶ W₂) (h : w ≫ g = 𝟙 W₂) :
    (r ≫ s ≫ w) ≫ g = r ≫ s := by
  rw [Category.assoc, Category.assoc, h, Category.comp_id]

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (Modules X)]

/-- **The derived scalar-restriction unit at an injective resolution inverts the resolution
comparison.** The unit of the derived restriction of scalars at the sections of an injective
resolution of `F`, followed by the image under that derived functor of the comparison of
[Stacks, Tag 01EQ] and by the comparison of [Stacks, Tag 01EZ], is the inverse of the
resolution comparison of [Stacks, Tag 01FB] for the composite of global sections with
restriction of scalars. This is the first of the two scalar-restriction identifications used by
[Stacks, Tag 01FD]. -/
theorem scalarRestrictionUnit_resolution (F : Modules X) (J : InjectiveResolution F) :
    (scalarRestrictionUnit f ((moduleGlobalSections X).mapCochainComplexPlus.obj
            ⟨J.cochainComplex, 0, inferInstance⟩) ≫
          (restrictGlobalScalars f).rightDerivedFunctorPlus.map
            (ObjectProperty.homMk (CechDerived.injectiveResolutionToDerivedGlobalSections
              (ringCatSheaf X) ⊤ F J)) ≫
          (derivedSectionsScalarComparison f).hom.app
            ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)).hom ≫
        (derivedModuleGlobalSectionsAlongResolutionIso f
          (CategoryTheory.InjectiveResolution.toCochainComplex F J)).hom = 𝟙 _ := by
  have hτ : (ObjectProperty.homMk (CechDerived.injectiveResolutionToDerivedGlobalSections
          (ringCatSheaf X) ⊤ F J) :
        DerivedCategory.Plus.Q.obj ((moduleGlobalSections X).mapCochainComplexPlus.obj
            ⟨J.cochainComplex, 0, inferInstance⟩) ⟶
          (derivedModuleGlobalSections X).obj
            ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)) =
      (Functor.mapCochainComplexPlusDerivedUnit (moduleGlobalSections X)).app
          ⟨J.cochainComplex, 0, inferInstance⟩ ≫
        (moduleGlobalSections X).rightDerivedFunctorPlus.map
          (CechDerived.injectiveResolutionIso (ringCatSheaf X) F J).inv :=
    ObjectProperty.hom_ext _ (CechDerived.injectiveResolutionToDerivedGlobalSections_eq_derivedUnit
      (ringCatSheaf X) ⊤ F J)
  have hcomp := Functor.mapCochainComplexPlusDerivedUnit_comp (moduleGlobalSections X)
    (restrictGlobalScalars f)
    (Functor.rightDerivedFunctorPlusComp (moduleGlobalSections X)
      (restrictGlobalScalars f))
    (Functor.rightDerivedFunctorPlusComp_fac (moduleGlobalSections X)
      (restrictGlobalScalars f))
    (⟨J.cochainComplex, 0, inferInstance⟩ : CochainComplex.Plus (Modules X))
  have hnat := (derivedSectionsScalarComparison f).inv.naturality
    (CechDerived.injectiveResolutionIso (ringCatSheaf X) F J).inv
  have hid := (derivedSectionsScalarComparison f).inv_hom_id_app
    ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)
  have hplus : scalarRestrictionUnit f ((moduleGlobalSections X).mapCochainComplexPlus.obj
          ⟨J.cochainComplex, 0, inferInstance⟩) ≫
        (restrictGlobalScalars f).rightDerivedFunctorPlus.map
          (ObjectProperty.homMk (CechDerived.injectiveResolutionToDerivedGlobalSections
            (ringCatSheaf X) ⊤ F J)) ≫
        (derivedSectionsScalarComparison f).hom.app
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F) =
      (Functor.mapCochainComplexPlusDerivedUnit
            (moduleGlobalSections X ⋙ restrictGlobalScalars f)).app
          ⟨J.cochainComplex, 0, inferInstance⟩ ≫
        (moduleGlobalSections X ⋙ restrictGlobalScalars f).rightDerivedFunctorPlus.map
          (CechDerived.injectiveResolutionIso (ringCatSheaf X) F J).inv := by
    refine Eq.trans (congrArg (fun z => scalarRestrictionUnit f
        ((moduleGlobalSections X).mapCochainComplexPlus.obj
          ⟨J.cochainComplex, 0, inferInstance⟩) ≫
        (restrictGlobalScalars f).rightDerivedFunctorPlus.map z ≫
        (derivedSectionsScalarComparison f).hom.app
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)) hτ) ?_
    refine Eq.trans (congrArg (fun z => scalarRestrictionUnit f
        ((moduleGlobalSections X).mapCochainComplexPlus.obj
          ⟨J.cochainComplex, 0, inferInstance⟩) ≫ z ≫
        (derivedSectionsScalarComparison f).hom.app
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F))
      (CategoryTheory.Functor.map_comp (restrictGlobalScalars f).rightDerivedFunctorPlus
        ((Functor.mapCochainComplexPlusDerivedUnit (moduleGlobalSections X)).app
          ⟨J.cochainComplex, 0, inferInstance⟩)
        ((moduleGlobalSections X).rightDerivedFunctorPlus.map
          (CechDerived.injectiveResolutionIso (ringCatSheaf X) F J).inv))) ?_
    exact comp_eq_of_unit_comp_of_naturality _ _ _ _ _ _ _ _ hcomp hnat hid
  refine Eq.trans (congrArg (fun z => z.hom ≫
    (derivedModuleGlobalSectionsAlongResolutionIso f
      (CategoryTheory.InjectiveResolution.toCochainComplex F J)).hom) hplus) ?_
  exact Functor.mapCochainComplexPlusDerivedUnit_app_comp_resolutionIso_hom
    (moduleGlobalSections X ⋙ restrictGlobalScalars f) F
    (CategoryTheory.InjectiveResolution.toCochainComplex F J)
    (CechDerived.injectiveResolutionIso (ringCatSheaf X) F J)
    (CechDerived.ι_map_injectiveResolutionIso_hom (ringCatSheaf X) F J)

/-- **The derived scalar-restriction unit at a Čech resolution comparison.** The comparison of
[Stacks, Tag 01EQ], presented at the resolution comparison `cX` as the roof `Q(β) ≫ Q(α)⁻¹`
followed by the identification of the sections of the resolution with derived sections, is
carried by the derived scalar-restriction unit to the corresponding roof of the termwise
restrictions. This is the second scalar-restriction identification used by
[Stacks, Tag 01FD]. -/
private lemma scalarRestrictionUnit_cechResolution
    {I : Type u} (U : I → Opens X.carrier) (hU : (⊤ : Opens X.carrier) = ⨆ i, U i)
    (F : Modules X) (JX : InjectiveResolution F)
    (cX : CechDerived.CechResolutionComparison (ringCatSheaf X) ⊤ U hU
      (CechDerived.cechToDerivedGlobalSections (ringCatSheaf X) ⊤ U hU) F JX)
    [IsIso (DerivedCategory.Q.map cX.α)]
    [IsIso (DerivedCategory.Q.map
      (((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map cX.α))] :
    (scalarRestrictionUnit f
            ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F) ≫
          (restrictGlobalScalars f).rightDerivedFunctorPlus.map (ObjectProperty.homMk
            (DerivedCategory.Q.map cX.β ≫ inv (DerivedCategory.Q.map cX.α) ≫
              CechDerived.injectiveResolutionToDerivedGlobalSections
                (ringCatSheaf X) ⊤ F JX)) ≫
          (derivedSectionsScalarComparison f).hom.app
            ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)).hom ≫
        (derivedModuleGlobalSectionsAlongResolutionIso f
          (CategoryTheory.InjectiveResolution.toCochainComplex F JX)).hom =
      DerivedCategory.Q.map
          (((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map cX.β) ≫
        inv (DerivedCategory.Q.map
          (((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map cX.α)) := by
  have hTX : CochainComplex.plus (ModuleCat.{u} ((ringCatSheaf X).obj.obj (op ⊤)))
      ((CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
        (ComplexShape.up ℤ)) :=
    ⟨0, CechDerived.isStrictlyGE_total_cechBicomplex (ringCatSheaf X) ⊤ U hU
      JX.cochainComplex 0⟩
  have hA : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map
      (ObjectProperty.homMk cX.α :
        (moduleGlobalSections X).mapCochainComplexPlus.obj
            ⟨JX.cochainComplex, 0, inferInstance⟩ ⟶
          ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
            (ComplexShape.up ℤ), hTX⟩))) :=
    inferInstanceAs (IsIso (DerivedCategory.Q.map cX.α))
  have hA' : IsIso (DerivedCategory.Plus.Q.map
      (ObjectProperty.homMk cX.α :
        (moduleGlobalSections X).mapCochainComplexPlus.obj
            ⟨JX.cochainComplex, 0, inferInstance⟩ ⟶
          ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
            (ComplexShape.up ℤ), hTX⟩)) :=
    isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  have hB : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map
      ((restrictGlobalScalars f).mapCochainComplexPlus.map
        (ObjectProperty.homMk cX.α :
          (moduleGlobalSections X).mapCochainComplexPlus.obj
              ⟨JX.cochainComplex, 0, inferInstance⟩ ⟶
            ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
              (ComplexShape.up ℤ), hTX⟩)))) :=
    inferInstanceAs (IsIso (DerivedCategory.Q.map
      (((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map cX.α)))
  have hB' : IsIso (DerivedCategory.Plus.Q.map
      ((restrictGlobalScalars f).mapCochainComplexPlus.map
        (ObjectProperty.homMk cX.α :
          (moduleGlobalSections X).mapCochainComplexPlus.obj
              ⟨JX.cochainComplex, 0, inferInstance⟩ ⟶
            ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
              (ComplexShape.up ℤ), hTX⟩))) :=
    isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  have hi : (inv (DerivedCategory.Plus.Q.map
        ((restrictGlobalScalars f).mapCochainComplexPlus.map
          (ObjectProperty.homMk cX.α :
            (moduleGlobalSections X).mapCochainComplexPlus.obj
                ⟨JX.cochainComplex, 0, inferInstance⟩ ⟶
              ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
                (ComplexShape.up ℤ), hTX⟩)))).hom =
      inv (DerivedCategory.Q.map
        (((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map cX.α)) :=
    DerivedCategory.Plus.ι.map_inv _
  have hi0 : (inv (DerivedCategory.Plus.Q.map
        (ObjectProperty.homMk cX.α :
          (moduleGlobalSections X).mapCochainComplexPlus.obj
              ⟨JX.cochainComplex, 0, inferInstance⟩ ⟶
            ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
              (ComplexShape.up ℤ), hTX⟩))).hom =
      inv (DerivedCategory.Q.map cX.α) :=
    DerivedCategory.Plus.ι.map_inv _
  have he : (ObjectProperty.homMk
        (DerivedCategory.Q.map cX.β ≫ inv (DerivedCategory.Q.map cX.α) ≫
          CechDerived.injectiveResolutionToDerivedGlobalSections (ringCatSheaf X) ⊤ F JX) :
      DerivedCategory.Plus.Q.obj
          ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F) ⟶
        (derivedModuleGlobalSections X).obj
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)) =
      (DerivedCategory.Plus.Q.map
            (ObjectProperty.homMk cX.β :
              (CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F ⟶
                ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
                  (ComplexShape.up ℤ), hTX⟩) ≫
          inv (DerivedCategory.Plus.Q.map
            (ObjectProperty.homMk cX.α :
              (moduleGlobalSections X).mapCochainComplexPlus.obj
                  ⟨JX.cochainComplex, 0, inferInstance⟩ ⟶
                ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
                  (ComplexShape.up ℤ), hTX⟩))) ≫
        ObjectProperty.homMk (CechDerived.injectiveResolutionToDerivedGlobalSections
          (ringCatSheaf X) ⊤ F JX) := by
    apply ObjectProperty.hom_ext
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (fun z => DerivedCategory.Q.map cX.β ≫ z ≫
      CechDerived.injectiveResolutionToDerivedGlobalSections (ringCatSheaf X) ⊤ F JX) hi0.symm
  have hr := Functor.mapCochainComplexPlusDerivedUnit_roof (restrictGlobalScalars f)
    (ObjectProperty.homMk cX.α :
      (moduleGlobalSections X).mapCochainComplexPlus.obj
          ⟨JX.cochainComplex, 0, inferInstance⟩ ⟶
        ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
          (ComplexShape.up ℤ), hTX⟩)
    (ObjectProperty.homMk cX.β :
      (CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F ⟶
        ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
          (ComplexShape.up ℤ), hTX⟩)
  have hplus : scalarRestrictionUnit f
          ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F) ≫
        (restrictGlobalScalars f).rightDerivedFunctorPlus.map (ObjectProperty.homMk
          (DerivedCategory.Q.map cX.β ≫ inv (DerivedCategory.Q.map cX.α) ≫
            CechDerived.injectiveResolutionToDerivedGlobalSections
              (ringCatSheaf X) ⊤ F JX)) ≫
        (derivedSectionsScalarComparison f).hom.app
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F) =
      DerivedCategory.Plus.Q.map ((restrictGlobalScalars f).mapCochainComplexPlus.map
          (ObjectProperty.homMk cX.β :
            (CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F ⟶
              ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
                (ComplexShape.up ℤ), hTX⟩)) ≫
        inv (DerivedCategory.Plus.Q.map
          ((restrictGlobalScalars f).mapCochainComplexPlus.map
            (ObjectProperty.homMk cX.α :
              (moduleGlobalSections X).mapCochainComplexPlus.obj
                  ⟨JX.cochainComplex, 0, inferInstance⟩ ⟶
                ⟨(CechDerived.cechBicomplex (ringCatSheaf X) ⊤ U hU JX.cochainComplex).total
                  (ComplexShape.up ℤ), hTX⟩))) ≫
        (scalarRestrictionUnit f ((moduleGlobalSections X).mapCochainComplexPlus.obj
            ⟨JX.cochainComplex, 0, inferInstance⟩) ≫
          (restrictGlobalScalars f).rightDerivedFunctorPlus.map
            (ObjectProperty.homMk (CechDerived.injectiveResolutionToDerivedGlobalSections
              (ringCatSheaf X) ⊤ F JX)) ≫
          (derivedSectionsScalarComparison f).hom.app
            ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)) := by
    refine Eq.trans (congrArg (fun z => scalarRestrictionUnit f
        ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F) ≫ z ≫
        (derivedSectionsScalarComparison f).hom.app
          ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F))
      ((congrArg (restrictGlobalScalars f).rightDerivedFunctorPlus.map he).trans
        (CategoryTheory.Functor.map_comp _ _ _))) ?_
    exact roof_rearrange _ _ _ _ _ _ _ hr
  refine Eq.trans (congrArg (fun z => z.hom ≫
    (derivedModuleGlobalSectionsAlongResolutionIso f
      (CategoryTheory.InjectiveResolution.toCochainComplex F JX)).hom) hplus) ?_
  refine Eq.trans (assoc_comp_id _ _ _ _ (scalarRestrictionUnit_resolution f F JX)) ?_
  exact congrArg (fun z => DerivedCategory.Q.map
    (((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map cX.β) ≫ z) hi

end

end Stacks.Cohomology

namespace Stacks.Cohomology.CechRefinement

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local implicit_reducible] TopCat.Sheaf

-- The Čech-acyclicity inputs are stated at `structureSheafRing X`, the injective resolutions
-- and the pushforward complex at `Modules X = SheafOfModules (ringCatSheaf X)`, i.e. at
-- `(sheafCompose _ (forget₂ _ _)).obj X.sheaf`.  The two are the same category, but
-- `Injective` and the zero morphism are found by instance search, which must therefore be able
-- to unfold the two Mathlib definitions standing between the survivor's explicit-constructor
-- reduct and that one.
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- The commutative square of [Stacks, Tag 01FD] on the total complexes, stated on variables:
two roofs out of `A` agree as soon as the four squares relating them commute. -/
private lemma commutativeSquare_of_totalComparison {D : Type*} [Category* D]
    {A B T P Q' Z W : D} (γ : A ⟶ B) (β : B ⟶ T) (α : P ⟶ T) (αP : P ⟶ Q')
    (t : Q' ⟶ T) (s : P ⟶ Z) (αJ : Z ⟶ W) (r : Q' ⟶ W) (δ : A ⟶ Q') (b : A ⟶ W)
    [IsIso α] [IsIso αP]
    (hδ : δ ≫ t = γ ≫ β) (hP : αP ≫ t = α) (hS : αP ≫ r = s ≫ αJ) (hJ : δ ≫ r = b) :
    γ ≫ β ≫ inv α ≫ s ≫ αJ = b := by
  have ht : t ≫ inv α ≫ αP = 𝟙 Q' := by
    apply (cancel_epi αP).mp
    rw [← Category.assoc, ← Category.assoc, hP]
    simp only [IsIso.hom_inv_id, Category.id_comp, Category.comp_id]
  rw [← hS, ← reassoc_of% hδ, reassoc_of% ht]
  exact hJ

/-- The reduction of the compatibility of [Stacks, Tag 01FD] to the commutative square on the
total complexes, stated on variables so that no `rw` has to cross the embedding of the
bounded-below derived category. -/
private lemma main_reduction {D : Type*} [Category* D]
    {m₀ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ : D}
    (qγ : m₀ ⟶ m₁) (w : m₁ ⟶ m₂) (ty : m₀ ⟶ m₃) (mm : m₃ ⟶ m₂) (g : m₂ ⟶ m₄)
    (qβ : m₁ ⟶ m₅) (qα : m₄ ⟶ m₅) (hi : m₃ ⟶ m₆) (irY : m₆ ⟶ m₃)
    (qcYβ : m₀ ⟶ m₇) (qcYα : m₆ ⟶ m₇) (qsYβ : m₆ ⟶ m₈) (qsYJ : m₄ ⟶ m₈)
    (qαJ : m₈ ⟶ m₉) (qtotB : m₇ ⟶ m₉)
    [IsIso g] [IsIso qα] [IsIso qcYα] [IsIso qsYJ] [IsIso qαJ]
    (hW : w ≫ g = qβ ≫ inv qα)
    (hM : mm ≫ g = hi ≫ qsYβ ≫ inv qsYJ)
    (hTY : ty = qcYβ ≫ inv qcYα ≫ irY)
    (hcan : irY ≫ hi = 𝟙 m₆)
    (hYD : qcYα ≫ qtotB = qsYβ ≫ qαJ)
    (hfinal : qγ ≫ qβ ≫ inv qα ≫ qsYJ ≫ qαJ = qcYβ ≫ qtotB) :
    qγ ≫ w = ty ≫ mm := by
  refine (cancel_mono g).mp ?_
  calc (qγ ≫ w) ≫ g = qγ ≫ qβ ≫ inv qα := by rw [Category.assoc, hW]
    _ = qcYβ ≫ inv qcYα ≫ qsYβ ≫ inv qsYJ := by
        refine (cancel_mono qsYJ).mp ((cancel_mono qαJ).mp ?_)
        simp only [Category.assoc, IsIso.inv_hom_id_assoc]
        rw [hfinal, ← hYD, IsIso.inv_hom_id_assoc]
    _ = (qcYβ ≫ inv qcYα ≫ irY) ≫ hi ≫ qsYβ ≫ inv qsYJ := by
        simp only [Category.assoc]
        rw [reassoc_of% hcan]
    _ = ty ≫ mm ≫ g := by rw [hTY, hM]
    _ = (ty ≫ mm) ≫ g := (Category.assoc _ _ _).symm

/-- **The degree-zero content of a lifting square between resolutions concentrated in degree
zero.** Let `P` be an additive functor, let `u : G ⟶ P F`, let `ιI`, `ιJ` be maps out of the
complexes concentrated in degree zero on `F` and `G`, let `ιK` be a map out of the termwise
image of `I`, and let `β` make the square of [Stacks, Tag 01FB] commute. Reading that square in
degree zero and cancelling the two comparisons of a complex concentrated in degree zero with its
value there identifies the two augmentations of the total Čech complexes used by
[Stacks, Tag 01FD].

Stated on abstract morphisms of abstract categories: in the application the two sides live in
the category of sheaves of modules, where the comparisons of
`CategoryTheory.Functor.mapHomologicalComplex` with
`HomologicalComplex.single` are not matched by `rw`. -/
private lemma hom_f_zero_of_single_lift {A : Type*} [Category* A] [Abelian A]
    {B : Type*} [Category* B] [Abelian B] (P : A ⥤ B) [P.Additive] {F : A} {G : B}
    (u : G ⟶ P.obj F) {I : CochainComplex A ℤ} {J K : CochainComplex B ℤ}
    (ιI : (CochainComplex.singleFunctor A 0).obj F ⟶ I)
    (ιJ : (CochainComplex.singleFunctor B 0).obj G ⟶ J)
    (ιK : (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ K) (β : J ⟶ K)
    (hβ : ιJ ≫ β = (CochainComplex.singleFunctor B 0).map u ≫
      (HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) 0).inv.app F ≫
        (P.mapHomologicalComplex (ComplexShape.up ℤ)).map ιI ≫ ιK) :
    ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).inv ≫ ιJ.f 0) ≫ β.f 0 =
      (u ≫ P.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ ιI.f 0)) ≫
        ιK.f 0 := by
  have h0 := congrArg (fun k ↦ HomologicalComplex.Hom.f k 0) hβ
  simp only [HomologicalComplex.comp_f] at h0
  have h1 : ((CochainComplex.singleFunctor B 0).map u).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).hom ≫ u ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (P.obj F)).inv :=
    HomologicalComplex.single_map_f_self (ComplexShape.up ℤ) 0 u
  have h2 : ((HomologicalComplex.singleMapHomologicalComplex P
          (ComplexShape.up ℤ) 0).inv.app F).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (P.obj F)).hom ≫
        P.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv :=
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self P (ComplexShape.up ℤ) 0 F
  have h3 : (((P.mapHomologicalComplex (ComplexShape.up ℤ)).map ιI).f 0) = P.map (ιI.f 0) := rfl
  rw [h1, h2, h3] at h0
  rw [Category.assoc, h0, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Transport of a factorization along a functor, stated on variables. -/
private lemma map_comp_eq_map {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂]
    (T : C₁ ⥤ C₂) {A B D : C₁} (a : A ⟶ B) (b : B ⟶ D) (a' : A ⟶ D) (h : a ≫ b = a') :
    T.map a ≫ T.map b = T.map a' :=
  (T.map_comp a b).symm.trans (congrArg T.map h)

/-- **Restriction of scalars along the homomorphism of rings of global sections preserves
homology**, being the identity on underlying abelian groups and hence exact. This is what makes
the localized augmentation of a Čech resolution comparison invertible after restriction of
scalars, as [Stacks, Tag 01FD] needs. -/
private lemma preservesHomology_restrictGlobalScalars {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (restrictGlobalScalars f).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ fun S hS =>
    (ShortComplex.moduleCat_exact_iff (S.map (restrictGlobalScalars f))).2
      ((ShortComplex.moduleCat_exact_iff S).1 hS)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {Ix Jy : Type u} (U : Ix → Opens X.carrier) (V : Jy → Opens Y.carrier)
  (hU : (⊤ : Opens X.carrier) = ⨆ i, U i) (hV : (⊤ : Opens Y.carrier) = ⨆ j, V j)
  (F : Modules X) (G : Modules Y)
  (φ : (RingedSpaceModuleAdjunction.modulePullback f).obj G ⟶ F)
  (c : Ix → Jy) (hc : ∀ i, U i ≤ (Opens.map f.hom.base).obj (V (c i)))
  [HasSheafify (Opens.grothendieckTopology (X : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (X : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify (Opens.grothendieckTopology (Y : TopCat)) AddCommGrpCat]
  [(Opens.grothendieckTopology (Y : TopCat)).WEqualsLocallyBijective AddCommGrpCat]
  [EnoughInjectives (Modules X)] [EnoughInjectives (Modules Y)]

/-- **The compatibility of [Stacks, Tag 01FD] at a chosen set of resolutions.** The two
resolutions of `F` and `G`, an injective resolution `J'` of the pushforward of the first, a lift
`β` of the adjoint of the `f`-map, and Čech resolution comparisons on the two spaces, assemble
the square of `Stacks.Cohomology.CechRefinement.main_reduction`. -/
private lemma naturality_of_refinement_of_resolutions
    (JX : InjectiveResolution F) (JY : InjectiveResolution G)
    (J' : CochainComplex.InjectiveResolution
      (modulePushforwardComplex f JX.cochainComplex))
    [CochainComplex.IsStrictlyGE J'.cocomplex 0]
    (β : JY.cochainComplex ⟶ J'.cocomplex)
    (hβ : JY.ι' ≫ β =
      (CochainComplex.singleFunctor (Modules Y) 0).map
          (RingedSpaceModuleAdjunction.homEquiv f F G φ) ≫
        (HomologicalComplex.singleMapHomologicalComplex
            (RingedSpaceModuleAdjunction.modulePushforward f)
            (ComplexShape.up ℤ) 0).inv.app F ≫
        ((RingedSpaceModuleAdjunction.modulePushforward f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (CategoryTheory.InjectiveResolution.toCochainComplex F JX).ι ≫ J'.ι)
    (cX : CechDerived.CechResolutionComparison (ringCatSheaf X) ⊤ U hU
      (CechDerived.cechToDerivedGlobalSections (ringCatSheaf X) ⊤ U hU) F JX)
    (cY : CechDerived.CechResolutionComparison (ringCatSheaf Y) ⊤ V hV
      (CechDerived.cechToDerivedGlobalSections (ringCatSheaf Y) ⊤ V hV) G JY) :
    DerivedCategory.Plus.Q.map
          (ObjectProperty.homMk (cechComplexRefinementMapInt f F G φ U V hU hV c hc) :
            (CechDerived.cechComplexPlusFunctor (ringCatSheaf Y) ⊤ V hV).obj G ⟶
              (restrictGlobalScalars f).mapCochainComplexPlus.obj
                ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F)) ≫
        (scalarRestrictionUnit f
              ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F) ≫
            (restrictGlobalScalars f).rightDerivedFunctorPlus.map
              ((CechDerived.cechToDerivedGlobalSections (ringCatSheaf X) ⊤ U hU).app F) ≫
            (derivedSectionsScalarComparison f).hom.app
              ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)) =
      (CechDerived.cechToDerivedGlobalSections (ringCatSheaf Y) ⊤ V hV).app G ≫
        derivedModuleGlobalSectionsMap f φ := by
  have hXinj : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((CechDerived.cechComplexNatFunctor (ringCatSheaf X) ⊤ U hU).obj
        (JX.cochainComplex.X q)).homology n) := fun q n hn =>
    CechSheaf.isZero_cechComplex_homology_of_injective ⊤ U hU (JX.cochainComplex.X q) n hn
  have hPinj : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((CechDerived.cechComplexNatFunctor (ringCatSheaf Y) ⊤ V hV).obj
        ((modulePushforwardComplex f JX.cochainComplex).X q)).homology n) := fun q n hn =>
    isZero_cechComplexNat_homology_pushforward_injective f (JX.cochainComplex.X q) V hV n hn
  have hJinj : ∀ (q : ℤ) (n : ℕ), 0 < n →
      IsZero (((CechDerived.cechComplexNatFunctor (ringCatSheaf Y) ⊤ V hV).obj
        (J'.cocomplex.X q)).homology n) := fun q n hn =>
    CechSheaf.isZero_cechComplex_homology_of_injective ⊤ V hV (J'.cocomplex.X q) n hn
  have hiP : (RingedSpaceModuleAdjunction.homEquiv f F G φ ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).map
          (CechTotalComparison.resolutionAug JX)) ≫
      (modulePushforwardComplex f JX.cochainComplex).d 0 1 = 0 := by
    change (_ ≫ (RingedSpaceModuleAdjunction.modulePushforward f).map _) ≫
      (RingedSpaceModuleAdjunction.modulePushforward f).map (JX.cochainComplex.d 0 1) = 0
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp,
      CechTotalComparison.resolutionAug_comp_d JX, CategoryTheory.Functor.map_zero, comp_zero]
  have hiβ : (CechTotalComparison.resolutionAug JY ≫ β.f 0) ≫ J'.cocomplex.d 0 1 = 0 := by
    rw [Category.assoc, β.comm 0 1, ← Category.assoc,
      CechTotalComparison.resolutionAug_comp_d JY, zero_comp]
  have hlift : CechTotalComparison.resolutionAug JY ≫ β.f 0 =
      (RingedSpaceModuleAdjunction.homEquiv f F G φ ≫
        (RingedSpaceModuleAdjunction.modulePushforward f).map
          (CechTotalComparison.resolutionAug JX)) ≫ J'.ι.f 0 :=
    hom_f_zero_of_single_lift (RingedSpaceModuleAdjunction.modulePushforward f)
      (RingedSpaceModuleAdjunction.homEquiv f F G φ)
      (CategoryTheory.InjectiveResolution.toCochainComplex F JX).ι JY.ι' J'.ι β hβ
  have hβXeq := CechDerived.cechResolutionComparison_β_eq (ringCatSheaf X) ⊤ U hU F JX cX
  have hαXeq := CechDerived.cechResolutionComparison_α_eq (ringCatSheaf X) ⊤ U hU F JX cX hXinj
  have hβYeq := CechDerived.cechResolutionComparison_β_eq (ringCatSheaf Y) ⊤ V hV G JY cY
  have hisoY : IsIso (DerivedCategory.Q.map cY.α) :=
    CechDerived.isIso_Q_map_cechResolutionComparison_α (ringCatSheaf Y) ⊤ V hV G JY cY
  have hqX : QuasiIso cX.α := (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
    (CechDerived.isIso_Q_map_cechResolutionComparison_α (ringCatSheaf X) ⊤ U hU F JX cX)
  have hPH : (restrictGlobalScalars f).PreservesHomology :=
    preservesHomology_restrictGlobalScalars f
  have hisoRX : IsIso (DerivedCategory.Q.map
      (((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map cX.α)) :=
    inferInstance
  have hisoαP : IsIso (DerivedCategory.Q.map (CechDerived.cechTotalAugmentation
      (ringCatSheaf Y) ⊤ V hV (modulePushforwardComplex f JX.cochainComplex) hPinj)) :=
    inferInstance
  have hisoαJ : IsIso (DerivedCategory.Q.map (CechDerived.cechTotalAugmentation
      (ringCatSheaf Y) ⊤ V hV J'.cocomplex hJinj)) :=
    inferInstance
  have hqJ' : QuasiIso (((moduleGlobalSections Y).mapHomologicalComplex
      (ComplexShape.up ℤ)).map J'.ι) :=
    quasiIso_moduleGlobalSections_map_pushforwardResolution f
      (CategoryTheory.InjectiveResolution.toCochainComplex F JX) J'
  have hisoJ' : IsIso (DerivedCategory.Q.map (((moduleGlobalSections Y).mapHomologicalComplex
      (ComplexShape.up ℤ)).map J'.ι)) :=
    inferInstance
  -- the four commutative squares on the total complexes
  have hδ1 : CechDerived.cechBeta (ringCatSheaf Y) ⊤ V hV
          (modulePushforwardComplex f JX.cochainComplex)
          (RingedSpaceModuleAdjunction.homEquiv f F G φ ≫
            (RingedSpaceModuleAdjunction.modulePushforward f).map
              (CechTotalComparison.resolutionAug JX)) hiP ≫
        cechTotalRefinementMap f U V hU hV c hc JX.cochainComplex =
      cechComplexRefinementMapInt f F G φ U V hU hV c hc ≫
        ((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map cX.β :=
    (cechBeta_cechTotalRefinementMap f U V hU hV c hc φ JX.cochainComplex
      (CechTotalComparison.resolutionAug JX)
      (CechTotalComparison.resolutionAug_comp_d JX) _ hiP rfl).trans
      (congrArg (fun z ↦ cechComplexRefinementMapInt f F G φ U V hU hV c hc ≫
        ((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map z) hβXeq.symm)
  have hP1 : CechDerived.cechTotalAugmentation (ringCatSheaf Y) ⊤ V hV
          (modulePushforwardComplex f JX.cochainComplex) hPinj ≫
        cechTotalRefinementMap f U V hU hV c hc JX.cochainComplex =
      ((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map cX.α :=
    (cechTotalAugmentation_cechTotalRefinementMap f U V hU hV c hc JX.cochainComplex
      hXinj hPinj).trans
      (congrArg (fun z ↦ ((restrictGlobalScalars f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map z) hαXeq.symm)
  have hS0 := CechDerived.cechTotalAugmentation_naturality (ringCatSheaf Y) ⊤ V hV J'.ι
    (CechDerived.cechTotalAugmentation (ringCatSheaf Y) ⊤ V hV
      (modulePushforwardComplex f JX.cochainComplex) hPinj)
    (CechDerived.cechTotalAugmentation (ringCatSheaf Y) ⊤ V hV J'.cocomplex hJinj)
    (CechDerived.cechTotalAugmentation_f (ringCatSheaf Y) ⊤ V hV _ hPinj)
    (CechDerived.cechTotalAugmentation_f (ringCatSheaf Y) ⊤ V hV _ hJinj)
  have hYD0 := CechDerived.cechTotalAugmentation_naturality (ringCatSheaf Y) ⊤ V hV β cY.α
    (CechDerived.cechTotalAugmentation (ringCatSheaf Y) ⊤ V hV J'.cocomplex hJinj) cY.α_f
    (CechDerived.cechTotalAugmentation_f (ringCatSheaf Y) ⊤ V hV _ hJinj)
  have hJ1 := CechDerived.cechBeta_comp_cechTotalMap_id (ringCatSheaf Y) ⊤ V hV
    JY.cochainComplex J'.cocomplex (CechTotalComparison.resolutionAug JY)
    (CechTotalComparison.resolutionAug_comp_d JY) _ hiβ β rfl
  have hJ2 := CechDerived.cechBeta_comp_cechTotalMap_id (ringCatSheaf Y) ⊤ V hV
    (modulePushforwardComplex f JX.cochainComplex) J'.cocomplex _ hiP _ hiβ J'.ι hlift.symm
  have hJ0 : CechDerived.cechBeta (ringCatSheaf Y) ⊤ V hV
          (modulePushforwardComplex f JX.cochainComplex)
          (RingedSpaceModuleAdjunction.homEquiv f F G φ ≫
            (RingedSpaceModuleAdjunction.modulePushforward f).map
              (CechTotalComparison.resolutionAug JX)) hiP ≫
        CechDerived.cechTotalMap (ringCatSheaf Y) ⊤ V hV J'.ι =
      cY.β ≫ CechDerived.cechTotalMap (ringCatSheaf Y) ⊤ V hV β :=
    hJ2.trans (hJ1.symm.trans (congrArg
      (fun z ↦ z ≫ CechDerived.cechTotalMap (ringCatSheaf Y) ⊤ V hV β) hβYeq.symm))
  -- the same squares in the derived category
  have hδQ := Stacks.Cohomology.CechDegreeZero.map_comp_eq_map_comp DerivedCategory.Q _ _ _ _ hδ1
  have hPQ := map_comp_eq_map DerivedCategory.Q _ _ _ hP1
  have hSQ := Stacks.Cohomology.CechDegreeZero.map_comp_eq_map_comp DerivedCategory.Q _ _ _ _ hS0
  have hYDQ := Stacks.Cohomology.CechDegreeZero.map_comp_eq_map_comp DerivedCategory.Q _ _ _ _ hYD0
  have hJQ := Stacks.Cohomology.CechDegreeZero.map_comp_eq_map_comp DerivedCategory.Q _ _ _ _ hJ0
  have hfinal := @commutativeSquare_of_totalComparison _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ hisoRX hisoαP hδQ hPQ hSQ hJQ
  -- the two scalar-restriction identifications and the two resolution comparisons
  have hτX : (CechDerived.cechToDerivedGlobalSections (ringCatSheaf X) ⊤ U hU).app F =
      ObjectProperty.homMk (DerivedCategory.Q.map cX.β ≫ inv (DerivedCategory.Q.map cX.α) ≫
        CechDerived.injectiveResolutionToDerivedGlobalSections (ringCatSheaf X) ⊤ F JX) :=
    ObjectProperty.hom_ext _
      (CechDerived.cechResolutionComparison_app_hom (ringCatSheaf X) ⊤ U hU F JX cX)
  have hW' : (scalarRestrictionUnit f
            ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F) ≫
          (restrictGlobalScalars f).rightDerivedFunctorPlus.map
            ((CechDerived.cechToDerivedGlobalSections (ringCatSheaf X) ⊤ U hU).app F) ≫
          (derivedSectionsScalarComparison f).hom.app
            ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)).hom ≫
        (derivedModuleGlobalSectionsAlongResolutionIso f
          (CategoryTheory.InjectiveResolution.toCochainComplex F JX)).hom =
      DerivedCategory.Q.map
          (((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map cX.β) ≫
        inv (DerivedCategory.Q.map
          (((restrictGlobalScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map cX.α)) :=
    Eq.trans (congrArg (fun z ↦ (scalarRestrictionUnit f
          ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F) ≫
        (restrictGlobalScalars f).rightDerivedFunctorPlus.map z ≫
          (derivedSectionsScalarComparison f).hom.app
            ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)).hom ≫
        (derivedModuleGlobalSectionsAlongResolutionIso f
          (CategoryTheory.InjectiveResolution.toCochainComplex F JX)).hom) hτX)
      (scalarRestrictionUnit_cechResolution f U hU F JX cX)
  have hM := (derivedModuleGlobalSectionsMap_eq_injectiveResolutionGlobalSectionsMap f φ
    (CategoryTheory.InjectiveResolution.toCochainComplex F JX)
    (CategoryTheory.InjectiveResolution.toCochainComplex G JY) J' β hβ).symm
  simp only [ObjectProperty.ι_map] at hM
  have hTY := CechDerived.cechResolutionComparison_app_hom (ringCatSheaf Y) ⊤ V hV G JY cY
  have hcan := CechDerived.injectiveResolutionToDerivedGlobalSections_comp_resolutionIso
    (ringCatSheaf Y) ⊤ G JY
  apply ObjectProperty.hom_ext
  have hisoG : IsIso ((derivedModuleGlobalSectionsAlongResolutionIso f
    (CategoryTheory.InjectiveResolution.toCochainComplex F JX)).hom) := inferInstance
  exact @main_reduction _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hisoG hisoRX hisoY hisoJ' hisoαJ hW' hM hTY hcan hYDQ hfinal

/-- **[Stacks, Tag 01FD].** Let `f : X ⟶ Y` be a morphism of ringed spaces, let `φ : f^* G ⟶ F`
be an `f`-map of sheaves of modules, let `U` be an open covering of `X`, let `V` be an open
covering of `Y` and let `c` be a refinement function, so that `U i ⊆ f⁻¹(V (c i))`. Then the
Čech refinement map `γ` of [Stacks, Tag 01FD], followed by the comparison of [Stacks, Tag 01EQ]
on `X` read over `Γ(Y, 𝒪_Y)`, agrees with the comparison of [Stacks, Tag 01EQ] on `Y` followed
by the functorial map on derived global sections of [Stacks, Tag 01F9].

All four corners are read in the bounded-below derived category of `Γ(Y, 𝒪_Y)`-modules, so the
left-hand side carries the unit `Stacks.Cohomology.scalarRestrictionUnit` of derived restriction
of scalars and the comparison `Stacks.Cohomology.derivedSectionsScalarComparison` of
[Stacks, Tag 01EZ]. -/
@[stacks 01FD "derived_compatibility", ega "0 12.1.4" "(12.1.4.2)"]
theorem cechToDerivedGlobalSections_naturality_of_refinement :
    DerivedCategory.Plus.Q.map
          (ObjectProperty.homMk (cechComplexRefinementMapInt f F G φ U V hU hV c hc) :
            (CechDerived.cechComplexPlusFunctor (ringCatSheaf Y) ⊤ V hV).obj G ⟶
              (restrictGlobalScalars f).mapCochainComplexPlus.obj
                ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F)) ≫
        (scalarRestrictionUnit f
              ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F) ≫
            (restrictGlobalScalars f).rightDerivedFunctorPlus.map
              ((CechDerived.cechToDerivedGlobalSections (ringCatSheaf X) ⊤ U hU).app F) ≫
            (derivedSectionsScalarComparison f).hom.app
              ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)) =
      (CechDerived.cechToDerivedGlobalSections (ringCatSheaf Y) ⊤ V hV).app G ≫
        derivedModuleGlobalSectionsMap f φ := by
  classical
  obtain ⟨cX⟩ := CechDerived.nonempty_cechResolutionComparison (ringCatSheaf X) ⊤ U hU F
    (InjectiveResolution.of F)
  obtain ⟨cY⟩ := CechDerived.nonempty_cechResolutionComparison (ringCatSheaf Y) ⊤ V hV G
    (InjectiveResolution.of G)
  obtain ⟨J', -, _⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE 0
    (modulePushforwardComplex f (InjectiveResolution.of F).cochainComplex)
  have hmono : ∀ n, Mono ((CategoryTheory.InjectiveResolution.toCochainComplex G
      (InjectiveResolution.of G)).ι.f n) := fun n ↦
    CategoryTheory.InjectiveResolution.mono_ι'_f G (InjectiveResolution.of G) n
  obtain ⟨β, hβ⟩ := exists_pushforwardInjectiveResolutionLift f φ
    (CategoryTheory.InjectiveResolution.toCochainComplex F (InjectiveResolution.of F))
    (CategoryTheory.InjectiveResolution.toCochainComplex G (InjectiveResolution.of G)) J'
  exact naturality_of_refinement_of_resolutions f U V hU hV F G φ c hc
    (InjectiveResolution.of F) (InjectiveResolution.of G) J' β hβ cX cY

/-- Expansion of a functor applied to a four-fold composite, stated on variables. -/
private lemma map_comp₄ {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂] (T : C₁ ⥤ C₂)
    {A₀ A₁ A₂ A₃ A₄ : C₁} (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (e : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) :
    T.map a ≫ T.map b ≫ T.map e ≫ T.map d = T.map (a ≫ b ≫ e ≫ d) := by
  rw [← T.map_comp, ← T.map_comp, ← T.map_comp]

/-- **[Stacks, Tag 01FD] on cohomology.** The canonical maps from Čech cohomology to sheaf
cohomology of [Stacks, Tag 01EQ] commute with an `f`-map and a refinement of the inverse-image
covering: this is
`Stacks.Cohomology.CechRefinement.cechToDerivedGlobalSections_naturality_of_refinement` read
through the `p`-th homology of the bounded-below derived category. All four corners are modules
over `Γ(Y, 𝒪_Y)`, so the source comparison carries the derived restriction-of-scalars unit. -/
@[stacks 01FD "cohomology_compatibility", ega "0 12.1.4" "(12.1.4.2)"]
theorem cechCohomologyToCohomology_naturality_of_refinement (p : ℤ) :
    (DerivedCategory.Plus.homologyFunctor
            (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤))) p).map
          (DerivedCategory.Plus.Q.map
            (ObjectProperty.homMk (cechComplexRefinementMapInt f F G φ U V hU hV c hc) :
              (CechDerived.cechComplexPlusFunctor (ringCatSheaf Y) ⊤ V hV).obj G ⟶
                (restrictGlobalScalars f).mapCochainComplexPlus.obj
                  ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F))) ≫
        (DerivedCategory.Plus.homologyFunctor
              (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤))) p).map
            (scalarRestrictionUnit f
              ((CechDerived.cechComplexPlusFunctor (ringCatSheaf X) ⊤ U hU).obj F)) ≫
          (DerivedCategory.Plus.homologyFunctor
                (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤))) p).map
              ((restrictGlobalScalars f).rightDerivedFunctorPlus.map
                ((CechDerived.cechToDerivedGlobalSections (ringCatSheaf X) ⊤ U hU).app F)) ≫
            (DerivedCategory.Plus.homologyFunctor
                (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤))) p).map
              ((derivedSectionsScalarComparison f).hom.app
                ((DerivedCategory.Plus.singleFunctor (Modules X) 0).obj F)) =
      (CechDerived.cechCohomologyToCohomology (ringCatSheaf Y) ⊤ V hV p).app G ≫
        (DerivedCategory.Plus.homologyFunctor
            (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤))) p).map
          (derivedModuleGlobalSectionsMap f φ) := by
  have hCech : (CechDerived.cechCohomologyToCohomology (ringCatSheaf Y) ⊤ V hV p).app G =
      (DerivedCategory.Plus.homologyFunctor
          (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤))) p).map
        ((CechDerived.cechToDerivedGlobalSections (ringCatSheaf Y) ⊤ V hV).app G) := by
    change (Functor.associator
        (CechDerived.cechComplexPlusFunctor (ringCatSheaf Y) ⊤ V hV)
        DerivedCategory.Plus.Q
        (DerivedCategory.Plus.homologyFunctor _ p)).inv.app G ≫
      (Functor.whiskerRight
        (CechDerived.cechToDerivedGlobalSections (ringCatSheaf Y) ⊤ V hV)
        (DerivedCategory.Plus.homologyFunctor _ p)).app G = _
    rw [Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp]
  refine (map_comp₄ _ _ _ _ _).trans ?_
  refine (congrArg (DerivedCategory.Plus.homologyFunctor
    (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤))) p).map
      (cechToDerivedGlobalSections_naturality_of_refinement f U V hU hV F G φ c hc)).trans ?_
  refine (CategoryTheory.Functor.map_comp _ _ _).trans ?_
  exact congrArg (fun z ↦ z ≫ (DerivedCategory.Plus.homologyFunctor
    (ModuleCat ((ringCatSheaf Y).obj.obj (op ⊤))) p).map
      (derivedModuleGlobalSectionsMap f φ)) hCech.symm

end

end Stacks.Cohomology.CechRefinement

end
