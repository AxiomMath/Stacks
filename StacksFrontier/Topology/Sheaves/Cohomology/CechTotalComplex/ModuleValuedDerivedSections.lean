module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.FunctorialInjectiveResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.Injectives.Sheaf.ModulesOnRingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueModulesAreAcyclic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.DerivedGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleValuedTotalComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The total Čech complex and derived sections, over the ring of sections

Let `(X, O_X)` be a ringed space, let `U` be an open subset and write `A = O_X(U)`; at `U = ⊤`
this is `A = Γ(X, O_X)`.  For a bounded below complex `K^•` of `O_X`-modules and an open covering
`Ui : I → Opens X` of `U` there is a canonical map

`Tot(Č^•(Ui, K^•)) ⟶ RΓ(U, K^•)`

in the derived category `D(A)`, natural in `K^•`, whose composite with the augmentation of
[Stacks, Tag 07M9] is the canonical map `Γ(U, K^•) ⟶ RΓ(U, K^•)` -- so that it is in particular
independent of the covering.  It is an isomorphism when the terms of `K^•` have flasque underlying
abelian sheaves.

## Main definitions

* `Stacks.Cech.Linear.totalCechDerivedFunctor`: the total Čech complex of a bounded below complex,
  in `D(A)`.
* `Stacks.Cech.Linear.derivedSectionsFunctor`: derived sections `RΓ(U, -)`, in `D(A)`.
* `Stacks.Cech.Linear.sectionsDerivedFunctor`: the ordinary complex of sections, in `D(A)`.
* `Stacks.Cech.Linear.sectionsToDerived`: the unit map `Γ(U, K^•) ⟶ RΓ(U, K^•)`.
* `Stacks.Cech.Linear.CechToDerivedSectionsSystem`: the comparison maps for all coverings of `U`
  at once, together with their compatibilities.

## Main results

* `Stacks.Cech.Linear.cechToDerivedSections`: the canonical system of comparison maps exists.
  This is the module-coefficient form of [Stacks, Tag 08BN].
* `Stacks.Cech.Linear.CechToDerivedSectionsSystem.map_eq_of_injective_resolution`: every
  comparison map is computed by any bounded below injective resolution.
* `Stacks.Cech.Linear.isIso_comparisons_of_isFlasque`: on a bounded below complex of flasque
  modules the augmentation, the comparison and their composite are all isomorphisms in `D(A)`,
  that is `Γ(U, K^•) = Tot(Č^•(Ui, K^•)) = RΓ(U, K^•)`.

## Implementation notes

The whole file is the module-coefficient shadow of `Stacks.Cech.cechToDerivedGlobalSections`,
which is the same construction with values in `D(Ab)`: everywhere that file uses global sections
of the underlying abelian sheaf, `Stacks.Cech.abelianGlobalSections`, this one uses
`SheafOfModules.evaluation O (op U)`, and everywhere it uses the abelian-group-valued total Čech
complex this one uses `Stacks.Cech.Linear.totalCechComplexFunctor`.  Only the input to the first
step of the construction had to be reproved, namely that the augmentation is a
quasi-isomorphism on a bounded below complex of injectives -- that is
`Stacks.Cech.Linear.quasiIso_sectionsToTotalCech_of_injective`; the functorial bounded below
injective resolution, which is a statement about the abelian category of sheaves of modules and
not about any sections functor, is reused from there.

`RΓ(U, -)` is taken to be the bounded below right derived functor
`(SheafOfModules.evaluation O (op U)).rightDerivedFunctorPlus` of Mathlib, as both the `D(Ab)`
form of [Stacks, Tag 08BN] and the single-sheaf
`Stacks.Cohomology.CechDerived.derivedGlobalSectionsFunctor` do.  It is a different *model* of
derived sections from the unbounded
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen`, which is the total right derived
functor of the same sections functor along K-injective resolutions; the two agree on bounded below
complexes, but that comparison is not made here and nothing below depends on it.

The comparison is built by the usual two-step argument: on a bounded below complex of injectives
the augmentation is already invertible in the derived category, and a general bounded below
complex is replaced by its functorial injective resolution.  Naturality of the three
transformations involved makes the composite independent of all choices, which is what
`map_eq_of_injective_resolution` records.  Compatibility with the augmentation is the `sections`
field of the system, and it is what makes the comparison independent of the covering, which is the
`sections_comp` field.

For a bounded below complex of flasque modules two of the three maps are invertible for reasons of
their own -- the augmentation by
`Stacks.Cech.Linear.quasiIso_sectionsToTotalCech_of_isFlasque`, and the unit
`Γ(U, K^•) ⟶ RΓ(U, K^•)` by Leray's acyclicity lemma [Stacks, Tag 015E] applied to the right
acyclicity of a flasque module for sections, [Stacks, Tag 09SY] -- and the third is then not
proved separately: the `sections` field says the first followed by the comparison is the second.
The unit is written out as the composite of its five factors, four of which are components of
natural isomorphisms, so that only the right-acyclicity input has to be supplied.

Neither the spectral sequence that [Stacks, Tag 08BN] also asserts nor the compatibility with the
refinement map of [Stacks, Tag 08BM] is proved here; the latter would need the refinement
transformation for the module-valued Čech complex, which does not exist yet.  The spectral
sequence is proved at *abelian* coefficients, over `X` and for a covering of `X`, by
`Stacks.Cech.exists_cechSpectralSequence`.  The module-valued form over an arbitrary open is not
a consequence of that: what this file proves is a generalisation of the abelian comparison, not
a case of it.

The ringed space is arbitrary. Sheafification of
abelian presheaves on the site of opens and the identification of the maps it inverts with the
locally bijective ones are theorems about that site; they are recorded as local instances at the
top rather than as hypotheses on `X`, so that the statements below -- in particular the
tagged `cechToDerivedSections` -- hold for every ringed space.

The space, the structure sheaf, the modules and the index type of the cover share one universe, as
the module-valued Čech API is stated at.

## References

* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 09SY](https://stacks.math.columbia.edu/tag/09SY)
* [Stacks Project, Tag 01DU](https://stacks.math.columbia.edu/tag/01DU)
* [Stacks Project, Tag 0141](https://stacks.math.columbia.edu/tag/0141)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf (SectionRing abSheaf)

universe u

namespace Stacks.Cech.Linear

variable (X : TopCat.{u}) (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {I : Type u} (U : Opens X) (Ui : I → Opens X) (hU : U = ⨆ i, Ui i)

/-- Sheafification of abelian presheaves on the site of opens of `X` exists. -/
local instance hasSheafifyOpens :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance

/-- On the site of opens of `X`, the morphisms of abelian presheaves inverted by sheafification
are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveOpens :
    (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The three functors to the derived category of `O_X(U)`-modules -/

/-- **The total Čech complex of a bounded below complex, viewed in `D(O_X(U))`.** -/
def totalCechDerivedFunctor :
    CochainComplex.Plus (SheafOfModules.{u} O) ⥤
      DerivedCategory (ModuleCat.{u} (SectionRing O U)) :=
  CochainComplex.Plus.ι _ ⋙ totalCechComplexFunctor X O U Ui hU ⋙ DerivedCategory.Q

/-- **Derived sections `RΓ(U, -)` of a bounded below complex, viewed in `D(O_X(U))`.** -/
def derivedSectionsFunctor :
    CochainComplex.Plus (SheafOfModules.{u} O) ⥤
      DerivedCategory (ModuleCat.{u} (SectionRing O U)) :=
  DerivedCategory.Plus.Q ⋙
    (SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι

/-- **The ordinary complex of sections over `U`, viewed in `D(O_X(U))`.** -/
def sectionsDerivedFunctor :
    CochainComplex.Plus (SheafOfModules.{u} O) ⥤
      DerivedCategory (ModuleCat.{u} (SectionRing O U)) :=
  CochainComplex.Plus.ι _ ⋙ sectionsComplexFunctor X O U ⋙ DerivedCategory.Q

/-- **The augmentation of [Stacks, Tag 07M9], followed by passage to the derived category.** -/
def sectionsToTotalCechDerived :
    sectionsDerivedFunctor X O U ⟶ totalCechDerivedFunctor X O U Ui hU :=
  Functor.whiskerRight
    (Functor.whiskerLeft (CochainComplex.Plus.ι _) (sectionsToTotalCech X O U Ui hU))
    DerivedCategory.Q

/-! ### The unit from ordinary to derived sections -/

/-- Sections of a bounded below complex, computed in the homotopy category of `O_X(U)`-modules
through the bounded below homotopy category, agree with the complex of sections. -/
def sectionsHomotopyBridgeIso :
    HomotopyCategory.Plus.quotient (SheafOfModules.{u} O) ⋙
        (SheafOfModules.evaluation.{u} O (op U)).mapHomotopyCategoryPlus ⋙
          HomotopyCategory.Plus.ι (ModuleCat.{u} (SectionRing O U)) ≅
      CochainComplex.Plus.ι (SheafOfModules.{u} O) ⋙
        (SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ) ⋙
          HomotopyCategory.quotient (ModuleCat.{u} (SectionRing O U)) (up ℤ) := by
  refine NatIso.ofComponents (fun K => ?_) ?_
  · change
      (HomotopyCategory.Plus.ι (ModuleCat.{u} (SectionRing O U))).obj
          ((SheafOfModules.evaluation.{u} O (op U)).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} O)).obj K)) ≅
        (HomotopyCategory.quotient (ModuleCat.{u} (SectionRing O U)) (up ℤ)).obj
          (((SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj K.1)
    exact ((SheafOfModules.evaluation.{u} O (op U)).mapHomotopyCategory (up ℤ)).mapIso
        ((HomotopyCategory.Plus.quotientCompιIso (SheafOfModules.{u} O)).app K) ≪≫
      ((SheafOfModules.evaluation.{u} O (op U)).mapHomotopyCategoryFactors (up ℤ)).app K.1
  · intro K L f
    cat_disch

/-- **The canonical map from the ordinary complex of sections to derived sections**, as a natural
transformation: the unit of the right derived functor, read through the three identifications that
relate the localisation of the complex of sections to the value of the derived functor. -/
def sectionsToDerivedNat :
    sectionsDerivedFunctor X O U ⟶ derivedSectionsFunctor X O U :=
  Functor.whiskerLeft
      (CochainComplex.Plus.ι (SheafOfModules.{u} O) ⋙
        (SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ))
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} (SectionRing O U))).inv ≫
    Functor.whiskerRight (sectionsHomotopyBridgeIso X O U).inv
      (DerivedCategory.Qh (C := ModuleCat.{u} (SectionRing O U))) ≫
    Functor.whiskerLeft
      (HomotopyCategory.Plus.quotient (SheafOfModules.{u} O) ⋙
        (SheafOfModules.evaluation.{u} O (op U)).mapHomotopyCategoryPlus)
      (DerivedCategory.Plus.QhCompιIsoιCompQh (ModuleCat.{u} (SectionRing O U))).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (HomotopyCategory.Plus.quotient (SheafOfModules.{u} O))
        (SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlusUnit)
      DerivedCategory.Plus.ι ≫
    Functor.whiskerRight
      (Functor.whiskerRight
        (StacksDraft.DerivedSectionsComparison.quotientQhIsoQ (SheafOfModules.{u} O)).hom
        (SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus)
      DerivedCategory.Plus.ι

/-- The canonical map from the ordinary complex of sections to derived sections. -/
def sectionsToDerived (K : CochainComplex.Plus (SheafOfModules.{u} O)) :
    (sectionsDerivedFunctor X O U).obj K ⟶ (derivedSectionsFunctor X O U).obj K :=
  (sectionsToDerivedNat X O U).app K

/-! ### The comparison map -/

/-- The augmentation is invertible in the derived category once it is a quasi-isomorphism on
the underlying complex of a bounded below complex. -/
private theorem isIso_sectionsToTotalCechDerived_of_quasiIso
    (K : CochainComplex.Plus (SheafOfModules.{u} O))
    (h : ∀ (a : ℤ) [K.1.IsStrictlyGE a],
      QuasiIso ((sectionsToTotalCech X O U Ui hU).app K.1)) :
    IsIso ((sectionsToTotalCechDerived X O U Ui hU).app K) := by
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff _ K.1).mp K.2
  have := h a
  change IsIso (DerivedCategory.Q.map ((sectionsToTotalCech X O U Ui hU).app K.1))
  infer_instance

/-- **On a bounded below complex of injectives the augmentation is invertible in the derived
category.**  This is the first step of the construction. -/
theorem isIso_sectionsToTotalCechDerived_of_injective
    (L : CochainComplex.Plus (SheafOfModules.{u} O))
    (hL : ∀ n : ℤ, Injective (L.1.X n)) :
    IsIso ((sectionsToTotalCechDerived X O U Ui hU).app L) :=
  isIso_sectionsToTotalCechDerived_of_quasiIso X O U Ui hU L fun a _ =>
    quasiIso_sectionsToTotalCech_of_injective X O U Ui hU L.1 a hL

/-- Derived sections invert quasi-isomorphisms of bounded below complexes. -/
instance derivedSectionsFunctor_map_isIso
    {K L : CochainComplex.Plus (SheafOfModules.{u} O)} (f : K ⟶ L) [QuasiIso f.hom] :
    IsIso ((derivedSectionsFunctor X O U).map f) := by
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map f)) := by
    change IsIso (DerivedCategory.Q.map f.hom)
    infer_instance
  have : IsIso (DerivedCategory.Plus.Q.map f) :=
    isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  dsimp [derivedSectionsFunctor]
  infer_instance

/-- On the functorial injective resolution of [Stacks, Tag 0141] the augmentation is invertible in
the derived category, since the resolving complex has injective terms. -/
theorem isIso_sectionsToTotalCechDerived_injectiveResolution
    (K : CochainComplex.Plus (SheafOfModules.{u} O)) :
    IsIso ((sectionsToTotalCechDerived X O U Ui hU).app
      ((Stacks.Cech.injectiveResolutionFunctor X O).obj K)) := by
  refine isIso_sectionsToTotalCechDerived_of_injective X O U Ui hU _ fun n => ?_
  change Injective ((InjectiveObject.ι (SheafOfModules.{u} O)).obj _)
  infer_instance

/-- **On the functorial injective resolution, the augmentation is an isomorphism.** -/
def injectiveResolutionCechComparisonIso :
    Stacks.Cech.injectiveResolutionFunctor X O ⋙ sectionsDerivedFunctor X O U ≅
      Stacks.Cech.injectiveResolutionFunctor X O ⋙ totalCechDerivedFunctor X O U Ui hU :=
  NatIso.ofComponents
    (fun K =>
      haveI := isIso_sectionsToTotalCechDerived_injectiveResolution X O U Ui hU K
      asIso ((sectionsToTotalCechDerived X O U Ui hU).app
        ((Stacks.Cech.injectiveResolutionFunctor X O).obj K)))
    (fun _ => (sectionsToTotalCechDerived X O U Ui hU).naturality _)

/-- The component of `injectiveResolutionCechComparisonIso` at `K` is the augmentation
`sectionsToTotalCechDerived` evaluated at the injective resolution of `K`. -/
@[simp]
theorem injectiveResolutionCechComparisonIso_hom_app
    (K : CochainComplex.Plus (SheafOfModules.{u} O)) :
    (injectiveResolutionCechComparisonIso X O U Ui hU).hom.app K =
      (sectionsToTotalCechDerived X O U Ui hU).app
        ((Stacks.Cech.injectiveResolutionFunctor X O).obj K) :=
  rfl

/-- **Derived sections are computed by the functorial injective resolution.** -/
def derivedSectionsResolutionIso :
    derivedSectionsFunctor X O U ≅
      Stacks.Cech.injectiveResolutionFunctor X O ⋙ derivedSectionsFunctor X O U := by
  let β := Functor.whiskerRight (Stacks.Cech.injectiveResolutionUnit X O)
    (derivedSectionsFunctor X O U)
  refine NatIso.ofComponents (fun K => ?_) ?_
  · have hα : IsIso (DerivedCategory.Plus.Q.map
        ((Stacks.Cech.injectiveResolutionUnit X O).app K)) := by
      have hm : IsIso (DerivedCategory.Plus.ι.map
          (DerivedCategory.Plus.Q.map ((Stacks.Cech.injectiveResolutionUnit X O).app K))) := by
        change IsIso (DerivedCategory.Q.map
          ((Stacks.Cech.injectiveResolutionUnit X O).app K).hom)
        exact Localization.inverts (DerivedCategory.Q)
          (HomologicalComplex.quasiIso (C := SheafOfModules.{u} O)
            (c := ComplexShape.up ℤ)) _ (Stacks.Cech.injectiveResolution_quasiIso X O K)
      exact isIso_of_fully_faithful (DerivedCategory.Plus.ι)
        (DerivedCategory.Plus.Q.map ((Stacks.Cech.injectiveResolutionUnit X O).app K))
    have hβ : IsIso (β.app K) := by
      dsimp [β, derivedSectionsFunctor]
      infer_instance
    exact asIso (β.app K)
  · intro K L f
    exact β.naturality f

/-- **The comparison map from the total Čech complex to derived sections, for one covering**:
resolve, invert the injective augmentation, take the unit, and undo the resolution. -/
def totalCechToDerivedSections :
    totalCechDerivedFunctor X O U Ui hU ⟶ derivedSectionsFunctor X O U :=
  (Functor.leftUnitor (totalCechDerivedFunctor X O U Ui hU)).inv ≫
    Functor.whiskerRight (Stacks.Cech.injectiveResolutionUnit X O)
      (totalCechDerivedFunctor X O U Ui hU) ≫
    (injectiveResolutionCechComparisonIso X O U Ui hU).symm.hom ≫
    Functor.whiskerLeft (Stacks.Cech.injectiveResolutionFunctor X O)
      (sectionsToDerivedNat X O U) ≫
    (derivedSectionsResolutionIso X O U).symm.hom

/-- The components of the comparison map: resolve, invert the injective augmentation, take the
unit, and undo the resolution. -/
theorem totalCechToDerivedSections_app (K : CochainComplex.Plus (SheafOfModules.{u} O)) :
    (totalCechToDerivedSections X O U Ui hU).app K =
      (totalCechDerivedFunctor X O U Ui hU).map
          ((Stacks.Cech.injectiveResolutionUnit X O).app K) ≫
        (injectiveResolutionCechComparisonIso X O U Ui hU).inv.app K ≫
          (sectionsToDerivedNat X O U).app
            ((Stacks.Cech.injectiveResolutionFunctor X O).obj K) ≫
            (derivedSectionsResolutionIso X O U).inv.app K := by
  rw [totalCechToDerivedSections]
  simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.id_comp]

/-- **The comparison map is compatible with the augmentation of [Stacks, Tag 07M9]**: after it,
the composite is the unit map from ordinary to derived sections. -/
theorem sectionsToTotalCechDerived_comp_totalCechToDerivedSections
    (K : CochainComplex.Plus (SheafOfModules.{u} O)) :
    (sectionsToTotalCechDerived X O U Ui hU).app K ≫
        (totalCechToDerivedSections X O U Ui hU).app K =
      sectionsToDerived X O U K := by
  let F := totalCechDerivedFunctor X O U Ui hU
  let K' := (Stacks.Cech.injectiveResolutionFunctor X O).obj K
  let η := (Stacks.Cech.injectiveResolutionUnit X O).app K
  let β := injectiveResolutionCechComparisonIso X O U Ui hU
  let ρ := derivedSectionsResolutionIso X O U
  have hcech : (sectionsToTotalCechDerived X O U Ui hU).app K ≫ F.map η =
      (sectionsDerivedFunctor X O U).map η ≫
        (sectionsToTotalCechDerived X O U Ui hU).app K' :=
    ((sectionsToTotalCechDerived X O U Ui hU).naturality η).symm
  have hβ : (sectionsToTotalCechDerived X O U Ui hU).app K' ≫ β.inv.app K = 𝟙 _ :=
    β.hom_inv_id_app K
  change (sectionsToTotalCechDerived X O U Ui hU).app K ≫
    (Functor.leftUnitor F).inv.app K ≫ (𝟭 _ ⋙ F).map η ≫
      β.inv.app K ≫ (sectionsToDerivedNat X O U).app K' ≫ ρ.inv.app K = _
  have hγ' : (sectionsDerivedFunctor X O U).map η ≫
      (sectionsToDerivedNat X O U).app K' =
    (sectionsToDerivedNat X O U).app K ≫ (derivedSectionsFunctor X O U).map η :=
    (sectionsToDerivedNat X O U).naturality η
  have hρ : (derivedSectionsFunctor X O U).map η = ρ.hom.app K := rfl
  calc
    _ = ((sectionsDerivedFunctor X O U).map η ≫
        (sectionsToTotalCechDerived X O U Ui hU).app K') ≫ β.inv.app K ≫
          (sectionsToDerivedNat X O U).app K' ≫ ρ.inv.app K := by
      simp only [Functor.leftUnitor_inv_app, Functor.comp_map, Functor.id_map]
      rw [Category.id_comp, ← Category.assoc, hcech]
    _ = (sectionsDerivedFunctor X O U).map η ≫
        (sectionsToDerivedNat X O U).app K' ≫ ρ.inv.app K := by
      rw [Category.assoc,
        ← Category.assoc ((sectionsToTotalCechDerived X O U Ui hU).app K'), hβ,
        Category.id_comp]
    _ = (sectionsToDerivedNat X O U).app K ≫
        (derivedSectionsFunctor X O U).map η ≫ ρ.inv.app K := by
      rw [← Category.assoc, hγ', Category.assoc]
    _ = (sectionsToDerivedNat X O U).app K := by
      rw [hρ, ρ.hom_inv_id_app, Category.comp_id]

/-! ### The system of comparison maps -/

/-- A functorial comparison from the total Čech complex to derived sections over `U`,
simultaneously for all open coverings of `U`.  The last two fields express compatibility with the
augmentation of [Stacks, Tag 07M9] and the independence of the covering that it implies. -/
structure CechToDerivedSectionsSystem where
  /-- The comparison for a particular open covering of `U`. -/
  map {J : Type u} (V : J → Opens X) (hV : U = ⨆ i, V i) :
    totalCechDerivedFunctor X O U V hV ⟶ derivedSectionsFunctor X O U
  /-- After the augmentation of [Stacks, Tag 07M9], the comparison is the canonical unit map from
  ordinary sections to derived sections. -/
  sections {J : Type u} (V : J → Opens X) (hV : U = ⨆ i, V i)
      (K : CochainComplex.Plus (SheafOfModules.{u} O)) :
    (sectionsToTotalCechDerived X O U V hV).app K ≫ (map V hV).app K =
      sectionsToDerived X O U K
  /-- Consequently, the composite from ordinary sections is independent of the covering. -/
  sections_comp {J J' : Type u} (V : J → Opens X) (hV : U = ⨆ i, V i)
      (W : J' → Opens X) (hW : U = ⨆ i, W i) :
    sectionsToTotalCechDerived X O U V hV ≫ map V hV =
      sectionsToTotalCechDerived X O U W hW ≫ map W hW

/-- **Any bounded below injective resolution computes the comparison**: apply the Čech functor to
the resolution map, invert the injective augmentation, and identify sections of the resolution
with derived sections. -/
theorem CechToDerivedSectionsSystem.map_eq_of_injective_resolution
    (S : CechToDerivedSectionsSystem X O U) {J : Type u}
    (V : J → Opens X) (hV : U = ⨆ i, V i)
    {K L : CochainComplex.Plus (SheafOfModules.{u} O)} (f : K ⟶ L) [QuasiIso f.hom]
    (hL : ∀ n : ℤ, Injective (L.1.X n)) :
    letI := isIso_sectionsToTotalCechDerived_of_injective X O U V hV L hL
    (S.map V hV).app K =
      (totalCechDerivedFunctor X O U V hV).map f ≫
        inv ((sectionsToTotalCechDerived X O U V hV).app L) ≫
          sectionsToDerived X O U L ≫ inv ((derivedSectionsFunctor X O U).map f) := by
  have := isIso_sectionsToTotalCechDerived_of_injective X O U V hV L hL
  rw [← cancel_mono ((derivedSectionsFunctor X O U).map f),
    Category.assoc, Category.assoc, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, ← (S.map V hV).naturality f]
  congr 1
  exact ((IsIso.inv_comp_eq _).2 (S.sections V hV L).symm).symm

/-- **Stacks 08BN, the comparison map with module coefficients.**  For a ringed space `(X, O_X)`
and an open subset `U` the total Čech complex of a bounded below complex of `O_X`-modules has a
canonical map to its derived sections over `U`, a morphism of `D(O_X(U))` functorial in the
complex and compatible with the augmentation of [Stacks, Tag 07M9] -- hence independent of the
covering. -/
@[stacks 08BN "the tag's comparison map, generalised to module coefficients over an arbitrary \
open: for a ringed space `(X, O_X)` and an open `U`, the total Čech complex of a bounded below \
complex of `O_X`-modules maps canonically to its derived sections in `D(O_X(U))`, functorially \
in the complex and compatibly with the Tag 07M9 augmentation, simultaneously for every open \
covering of `U`. The tag's own statement -- the comparison over `X`, compatible with both the \
Tag 07M9 and the Tag 08BM maps, together with the tag's spectral sequence -- is \
`Stacks.Cech.cechToDerivedGlobalSections` and `Stacks.Cech.exists_cechSpectralSequence`, \
conjoined at the lemma's three inputs by \
`Stacks.Cech.exists_cechToDerivedComparison_and_cechSpectralSequence`"]
def cechToDerivedSections : CechToDerivedSectionsSystem X O U where
  map V hV := totalCechToDerivedSections X O U V hV
  sections V hV K :=
    sectionsToTotalCechDerived_comp_totalCechToDerivedSections X O U V hV K
  sections_comp V hV W hW := by
    ext K
    exact (sectionsToTotalCechDerived_comp_totalCechToDerivedSections X O U V hV K).trans
      (sectionsToTotalCechDerived_comp_totalCechToDerivedSections X O U W hW K).symm

/-! ### Flasque complexes -/

/-- The canonical map from ordinary to derived sections, written out as the composite of its five
factors. -/
private theorem sectionsToDerivedNat_app_factors
    (K : CochainComplex.Plus (SheafOfModules.{u} O)) :
    (sectionsToDerivedNat X O U).app K =
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} (SectionRing O U))).inv.app
          ((CochainComplex.Plus.ι (SheafOfModules.{u} O) ⋙
            (SheafOfModules.evaluation.{u} O (op U)).mapHomologicalComplex (up ℤ)).obj K) ≫
        (DerivedCategory.Qh (C := ModuleCat.{u} (SectionRing O U))).map
          ((sectionsHomotopyBridgeIso X O U).inv.app K) ≫
        (DerivedCategory.Plus.QhCompιIsoιCompQh (ModuleCat.{u} (SectionRing O U))).inv.app
          ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} O) ⋙
            (SheafOfModules.evaluation.{u} O (op U)).mapHomotopyCategoryPlus).obj K) ≫
        (DerivedCategory.Plus.ι (C := ModuleCat.{u} (SectionRing O U))).map
          ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} O)).obj K)) ≫
        (DerivedCategory.Plus.ι (C := ModuleCat.{u} (SectionRing O U))).map
          ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlus.map
            ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ
              (SheafOfModules.{u} O)).hom.app K)) :=
  rfl

/-- **A bounded below complex whose terms are right acyclic for sections over `U` computes derived
sections there.**  This is Leray's acyclicity lemma [Stacks, Tag 015E] read through the four
natural isomorphisms that relate the localisation of the complex of sections to the value of the
derived functor. -/
theorem isIso_sectionsToDerived_of_rightAcyclic
    (K : CochainComplex.Plus (SheafOfModules.{u} O))
    (hK : ∀ n : ℤ, (SheafOfModules.evaluation.{u} O (op U)).rightAcyclic (K.1.X n)) :
    IsIso ((sectionsToDerivedNat X O U).app K) := by
  have hunit : IsIso ((SheafOfModules.evaluation.{u} O (op U)).rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} O)).obj K)) :=
    CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic _ K.1 K.2 hK
  rw [sectionsToDerivedNat_app_factors X O U K]
  have := hunit
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_
    (IsIso.comp_isIso' ?_ ?_)))
  · exact Iso.isIso_hom (((DerivedCategory.quotientCompQhIso _).app _).symm)
  · infer_instance
  · infer_instance
  · infer_instance
  · have : IsIso ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ
        (SheafOfModules.{u} O)).hom.app K) := Iso.isIso_hom (_ : _ ≅ _)
    exact Functor.map_isIso _ _

/-- **Ordinary sections of a bounded below complex of flasque modules compute derived sections.**
Every term is right acyclic for sections over `U` by [Stacks, Tag 09SY], so Leray's acyclicity
lemma applies. -/
theorem isIso_sectionsToDerived_of_isFlasque
    (K : CochainComplex.Plus (SheafOfModules.{u} O))
    (hfl : ∀ n : ℤ, (abSheaf (K.1.X n)).IsFlasque) :
    IsIso (sectionsToDerived X O U K) :=
  isIso_sectionsToDerived_of_rightAcyclic X O U K fun n =>
    Stacks.Cohomology.FlasqueAcyclic.rightAcyclic_evaluation_of_isFlasque O (K.1.X n) U (hfl n)

/-- **On a bounded below complex of flasque modules the augmentation is invertible in the derived
category.** -/
theorem isIso_sectionsToTotalCechDerived_of_isFlasque
    (K : CochainComplex.Plus (SheafOfModules.{u} O))
    (hfl : ∀ n : ℤ, (abSheaf (K.1.X n)).IsFlasque) :
    IsIso ((sectionsToTotalCechDerived X O U Ui hU).app K) :=
  isIso_sectionsToTotalCechDerived_of_quasiIso X O U Ui hU K fun a _ =>
    quasiIso_sectionsToTotalCech_of_isFlasque X O U Ui hU K.1 a hfl

/-- **The total Čech complex of a bounded below complex of flasque modules computes its derived
sections**, for every open covering.  Two of the three maps in
`Γ(U, K^•) ⟶ Tot(Č^•(Ui, K^•)) ⟶ RΓ(U, K^•)` are invertible for reasons of their own, which gives
the third. -/
theorem isIso_totalCechToDerivedSections_app_of_isFlasque
    (K : CochainComplex.Plus (SheafOfModules.{u} O))
    (hfl : ∀ n : ℤ, (abSheaf (K.1.X n)).IsFlasque) :
    IsIso ((totalCechToDerivedSections X O U Ui hU).app K) := by
  have haug := isIso_sectionsToTotalCechDerived_of_isFlasque X O U Ui hU K hfl
  have hunit := isIso_sectionsToDerived_of_isFlasque X O U K hfl
  have hcomp : IsIso ((sectionsToTotalCechDerived X O U Ui hU).app K ≫
      (totalCechToDerivedSections X O U Ui hU).app K) := by
    rw [sectionsToTotalCechDerived_comp_totalCechToDerivedSections]
    exact hunit
  exact IsIso.of_isIso_comp_left ((sectionsToTotalCechDerived X O U Ui hU).app K) _

/-- **For a bounded below complex `K^•` of `O_X`-modules with flasque underlying abelian sheaves
and any open covering `Ui` of `U` one has `Γ(U, K^•) = Tot(Č^•(Ui, K^•)) = RΓ(U, K^•)` in
`D(O_X(U))`**: the augmentation of [Stacks, Tag 07M9], the comparison of [Stacks, Tag 08BN] and
their composite, the unit `Γ(U, K^•) ⟶ RΓ(U, K^•)`, are all isomorphisms. -/
theorem isIso_comparisons_of_isFlasque
    (K : CochainComplex.Plus (SheafOfModules.{u} O))
    (hfl : ∀ n : ℤ, (abSheaf (K.1.X n)).IsFlasque) :
    IsIso ((sectionsToTotalCechDerived X O U Ui hU).app K) ∧
      IsIso (((cechToDerivedSections X O U).map Ui hU).app K) ∧
        IsIso (sectionsToDerived X O U K) :=
  ⟨isIso_sectionsToTotalCechDerived_of_isFlasque X O U Ui hU K hfl,
    isIso_totalCechToDerivedSections_app_of_isFlasque X O U Ui hU K hfl,
    isIso_sectionsToDerived_of_isFlasque X O U K hfl⟩

end Stacks.Cech.Linear

end
