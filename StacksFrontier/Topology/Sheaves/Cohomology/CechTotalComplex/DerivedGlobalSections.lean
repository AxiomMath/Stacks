module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSectionsComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.FunctorialInjectiveResolution
public import StacksFrontier.Homology.Injectives.Sheaf.ModulesOnRingedSite
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.InjectiveQuasiIso
import StacksCore.Tactic.StacksAttribute

/-!
# The total Čech complex of a complex and derived global sections

Let `(X, O_X)` be a ringed space and let `U : I → Opens X` be an open covering of `X`. For a
bounded below complex `F^•` of `O_X`-modules there is a canonical map

`Tot(Č^•(U, F^•)) ⟶ RΓ(X, F^•)`,

functorial in `F^•`, compatible with the augmentation of Tag 07M9 and with the refinement map
of Tag 08BM.

## Main definitions

* `Stacks.Cech.abelianGlobalSections`: global sections of the abelian sheaf underlying a sheaf
  of modules.
* `Stacks.Cech.cechDerivedFunctor`: the total Čech complex of a bounded below complex, in
  `D(Ab)`.
* `Stacks.Cech.derivedGlobalSectionsFunctor`: derived global sections, in `D(Ab)`.
* `Stacks.Cech.globalSectionsToDerived`: the unit map from ordinary to derived global sections.
* `Stacks.Cech.CechToDerivedGlobalSectionsSystem`: the comparison maps for all coverings at
  once, together with their compatibilities.

## Main results

* `Stacks.Cech.cechToDerivedGlobalSections`: the canonical system of comparison maps exists.
* `Stacks.Cech.CechToDerivedGlobalSectionsSystem.map_eq_of_injective_resolution`: every
  comparison map is computed by any bounded below injective resolution.

## Implementation notes

The target is placed in the unbounded derived category through the fully faithful inclusion
`D⁺(Ab) ⥤ D(Ab)`, which avoids choosing a lower bound for the total complex. Functoriality in
the coefficient complex is part of the natural-transformation structure, so it is not a
separate assertion; compatibility with Tag 07M9 is the `globalSections` field, which
identifies the composite with the unit of the right derived functor and hence makes it
independent of the covering, and compatibility with Tag 08BM is the `refinement` field.

The comparison is built by the usual two-step argument. On a bounded below complex of
injectives the Čech augmentation is already a quasi-isomorphism — that is
`quasiIso_globalSectionsToCech_of_injective` — so it is invertible in the derived category;
for a general bounded below complex one goes through a *functorial* bounded below injective
resolution, which exists because sheaves of modules on a site have functorial injective
embeddings (Tag 01DU) and a functorial injective embedding induces a functorial injective
resolution of bounded below complexes (Tag 0141). Naturality of the three transformations
involved then makes the composite independent of all choices, which is what
`map_eq_of_injective_resolution` records.

Only the comparison map and its two compatibilities are proved here, which is why the tag
carries the comment naming that half. The spectral sequence that Tag 08BN also asserts is
`Stacks.Cech.exists_cechSpectralSequence`.

The ringed space is arbitrary. Sheafification of abelian presheaves on the site of opens and
the identification of the maps it inverts with the locally bijective ones, which the right
derived functor of global sections needs, are theorems about that site, found by instance
search.

The common universe is the one the existing total Čech complex API is stated at.

## References

* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 08BM](https://stacks.math.columbia.edu/tag/08BM)
* [Stacks Project, Tag 01DU](https://stacks.math.columbia.edu/tag/01DU)
* [Stacks Project, Tag 0141](https://stacks.math.columbia.edu/tag/0141)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

universe u

namespace Stacks.Cech

variable (X : TopCat.{u})

attribute [local instance] HasDerivedCategory.standard

/-- Global sections of the abelian sheaf underlying a sheaf of modules. -/
noncomputable def abelianGlobalSections
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)

/-- The functor `abelianGlobalSections X R` is additive. -/
instance abelianGlobalSections_additive
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    (abelianGlobalSections X R).Additive := by
  dsimp [abelianGlobalSections]
  infer_instance

/-- The total Čech complex of a bounded below complex, viewed in `D(Ab)`. -/
noncomputable def cechDerivedFunctor
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {I : Type u}
    (U : I → Opens X) :
    CochainComplex.Plus (SheafOfModules.{u} R) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CochainComplex.Plus.ι _ ⋙ underlyingPresheafComplexFunctor X R ⋙
    cechTotalComplexFunctor U ⋙ DerivedCategory.Q

/-- Derived global sections of a bounded below complex, viewed in `D(Ab)`. -/
noncomputable def derivedGlobalSectionsFunctor
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    CochainComplex.Plus (SheafOfModules.{u} R) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  DerivedCategory.Plus.Q ⋙
    (abelianGlobalSections X R).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι

/-- The ordinary global-sections complex, viewed in `D(Ab)`. -/
noncomputable def globalSectionsDerivedFunctor
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    CochainComplex.Plus (SheafOfModules.{u} R) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  CochainComplex.Plus.ι _ ⋙ underlyingPresheafComplexFunctor X R ⋙
    globalSectionsComplexFunctor X ⋙ DerivedCategory.Q

/-- The augmentation of Tag 07M9, followed by passage to the derived category. -/
noncomputable def globalSectionsToCechDerived
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {I : Type u}
    (U : I → Opens X) :
    globalSectionsDerivedFunctor X R ⟶ cechDerivedFunctor X R U :=
  Functor.whiskerRight
    (Functor.whiskerLeft
      (CochainComplex.Plus.ι _ ⋙ underlyingPresheafComplexFunctor X R)
      (globalSectionsToCech X U))
    DerivedCategory.Q

/-- Global sections of a bounded below complex, computed in the homotopy category of abelian
groups through the bounded below homotopy category, agree with the global-sections complex. -/
noncomputable def globalSectionsHomotopyBridgeIso
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    HomotopyCategory.Plus.quotient (SheafOfModules.{u} R) ⋙
        (abelianGlobalSections X R).mapHomotopyCategoryPlus ⋙
          HomotopyCategory.Plus.ι AddCommGrpCat.{u} ≅
      CochainComplex.Plus.ι (SheafOfModules.{u} R) ⋙
        (abelianGlobalSections X R).mapHomologicalComplex (up ℤ) ⋙
          HomotopyCategory.quotient AddCommGrpCat.{u} (up ℤ) := by
  refine NatIso.ofComponents (fun K => ?_) ?_
  · change
      (HomotopyCategory.Plus.ι AddCommGrpCat.{u}).obj
          ((abelianGlobalSections X R).mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} R)).obj K)) ≅
        (HomotopyCategory.quotient AddCommGrpCat.{u} (up ℤ)).obj
          (((abelianGlobalSections X R).mapHomologicalComplex (up ℤ)).obj K.1)
    exact ((abelianGlobalSections X R).mapHomotopyCategory (up ℤ)).mapIso
        ((HomotopyCategory.Plus.quotientCompιIso (SheafOfModules.{u} R)).app K) ≪≫
      ((abelianGlobalSections X R).mapHomotopyCategoryFactors (up ℤ)).app K.1
  · intro K L f
    cat_disch

/-- **The canonical map from the ordinary global-sections complex to derived global sections**,
as a natural transformation: the unit of the right derived functor, read through the three
identifications that relate the localisation of the complex of global sections to the value of
the derived functor. -/
noncomputable def globalSectionsToDerivedNat
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    globalSectionsDerivedFunctor X R ⟶ derivedGlobalSectionsFunctor X R :=
  Functor.whiskerLeft
      (CochainComplex.Plus.ι (SheafOfModules.{u} R) ⋙
        (abelianGlobalSections X R).mapHomologicalComplex (up ℤ))
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u}).inv ≫
    Functor.whiskerRight (globalSectionsHomotopyBridgeIso X R).inv
      (DerivedCategory.Qh (C := AddCommGrpCat.{u})) ≫
    Functor.whiskerLeft
      (HomotopyCategory.Plus.quotient (SheafOfModules.{u} R) ⋙
        (abelianGlobalSections X R).mapHomotopyCategoryPlus)
      (DerivedCategory.Plus.QhCompιIsoιCompQh AddCommGrpCat.{u}).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (HomotopyCategory.Plus.quotient (SheafOfModules.{u} R))
        (abelianGlobalSections X R).rightDerivedFunctorPlusUnith)
      DerivedCategory.Plus.ι ≫
    Functor.whiskerRight
      (Functor.whiskerRight
        (StacksDraft.DerivedSectionsComparison.quotientQhIsoQ (SheafOfModules.{u} R)).hom
        (abelianGlobalSections X R).rightDerivedFunctorPlus)
      DerivedCategory.Plus.ι

/-- The canonical map from the ordinary global-sections complex to derived global sections. -/
noncomputable def globalSectionsToDerived
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (K : CochainComplex.Plus (SheafOfModules.{u} R)) :
    (globalSectionsDerivedFunctor X R).obj K ⟶
      (derivedGlobalSectionsFunctor X R).obj K :=
  (globalSectionsToDerivedNat X R).app K

/-- The map of total Čech complexes induced by a refinement, after passage to the derived
category. -/
noncomputable def cechRefinementDerived
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {I J : Type u} (U : I → Opens X) (V : J → Opens X)
    (t : FormalCoproduct.mk J V ⟶ FormalCoproduct.mk I U) :
    cechDerivedFunctor X R U ⟶ cechDerivedFunctor X R V := by
  let e := cechTotalComplexRefinement U V t
  let := e.preservesZeroU
  let := e.preservesZeroV
  let := e.hasTotal
  exact Functor.whiskerRight
    (Functor.whiskerLeft
      (CochainComplex.Plus.ι _ ⋙ underlyingPresheafComplexFunctor X R) e.map)
    DerivedCategory.Q

/-- The augmentation into the derived Čech complex commutes with refinement. -/
@[reassoc]
theorem globalSectionsToCechDerived_refinement
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {I J : Type u} (U : I → Opens X) (V : J → Opens X)
    (t : FormalCoproduct.mk J V ⟶ FormalCoproduct.mk I U) :
    globalSectionsToCechDerived X R U ≫ cechRefinementDerived X R U V t =
      globalSectionsToCechDerived X R V := by
  let e := cechTotalComplexRefinement U V t
  let := e.preservesZeroU
  let := e.preservesZeroV
  let := e.hasTotal
  apply NatTrans.ext
  funext K
  have h := NatTrans.congr_app
    (globalSectionsToCech_refinement_map X U V t e)
    ((underlyingPresheafComplexFunctor X R).obj K.1)
  exact (DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map h)

/-- A functorial comparison from the total Čech complex to derived global sections,
simultaneously for all open coverings. The last two fields express compatibility with the
augmentation of Tag 07M9 and with the refinement transformation of Tag 08BM. -/
structure CechToDerivedGlobalSectionsSystem
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) where
  /-- The comparison for a particular open covering. -/
  map {I : Type u} (U : I → Opens X) (hU : ⊤ = iSup U) :
    cechDerivedFunctor X R U ⟶ derivedGlobalSectionsFunctor X R
  /-- After the augmentation of Tag 07M9, the comparison is the canonical unit map from
  ordinary global sections to derived global sections. -/
  globalSections {I : Type u}
      (U : I → Opens X) (hU : ⊤ = iSup U)
      (K : CochainComplex.Plus (SheafOfModules.{u} R)) :
    (globalSectionsToCechDerived X R U).app K ≫ (map U hU).app K =
      globalSectionsToDerived X R K
  /-- Consequently, the composite from ordinary global sections is independent of the
  covering. -/
  globalSections_comp {I J : Type u}
      (U : I → Opens X) (hU : ⊤ = iSup U)
      (V : J → Opens X) (hV : ⊤ = iSup V) :
    globalSectionsToCechDerived X R U ≫ map U hU =
      globalSectionsToCechDerived X R V ≫ map V hV
  /-- Restriction along a refinement does not change the comparison map. -/
  refinement {I J : Type u}
      (U : I → Opens X) (hU : ⊤ = iSup U)
      (V : J → Opens X) (hV : ⊤ = iSup V)
      (t : FormalCoproduct.mk J V ⟶ FormalCoproduct.mk I U) :
    cechRefinementDerived X R U V t ≫ map V hV = map U hU

/-- On a bounded below complex of injectives the Čech augmentation is invertible in the derived
category. This is the first step of the construction. -/
theorem isIso_globalSectionsToCechDerived_of_injective
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {I : Type u}
    (U : I → Opens X) (hU : ⊤ = iSup U)
    (L : CochainComplex.Plus (SheafOfModules.{u} R))
    (hL : ∀ n : ℤ, Injective (L.1.X n)) :
    IsIso ((globalSectionsToCechDerived X R U).app L) := by
  have := quasiIso_globalSectionsToCech_of_injective X U hU L.1 L.2 hL
  show IsIso (DerivedCategory.Q.map
    ((globalSectionsToCech X U).app ((underlyingPresheafComplexFunctor X R).obj L.1)))
  infer_instance

/-- Derived global sections invert quasi-isomorphisms of bounded below complexes. -/
instance derivedGlobalSectionsFunctor_map_isIso
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    {K L : CochainComplex.Plus (SheafOfModules.{u} R)}
    (f : K ⟶ L) [QuasiIso f.hom] :
    IsIso ((derivedGlobalSectionsFunctor X R).map f) := by
  have : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map f)) := by
    change IsIso (DerivedCategory.Q.map f.hom)
    infer_instance
  have : IsIso (DerivedCategory.Plus.Q.map f) :=
    isIso_of_reflects_iso _ DerivedCategory.Plus.ι
  dsimp [derivedGlobalSectionsFunctor]
  infer_instance

/-- Any bounded below injective resolution computes the comparison: apply the Čech functor to
the resolution map, invert the injective Čech augmentation, and identify global sections of the
resolution with derived global sections. -/
theorem CechToDerivedGlobalSectionsSystem.map_eq_of_injective_resolution
    {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (S : CechToDerivedGlobalSectionsSystem X R) {I : Type u}
    (U : I → Opens X) (hU : ⊤ = iSup U)
    {K L : CochainComplex.Plus (SheafOfModules.{u} R)}
    (f : K ⟶ L) [QuasiIso f.hom]
    (hL : ∀ n : ℤ, Injective (L.1.X n)) :
    letI := isIso_globalSectionsToCechDerived_of_injective X R U hU L hL
    (S.map U hU).app K =
      (cechDerivedFunctor X R U).map f ≫
        inv ((globalSectionsToCechDerived X R U).app L) ≫
          globalSectionsToDerived X R L ≫
            inv ((derivedGlobalSectionsFunctor X R).map f) := by
  have := isIso_globalSectionsToCechDerived_of_injective X R U hU L hL
  have hf : Mono ((derivedGlobalSectionsFunctor X R).map f) :=
    (derivedGlobalSectionsFunctor_map_isIso X R f).mono_of_iso
  rw [← cancel_mono ((derivedGlobalSectionsFunctor X R).map f),
    Category.assoc, Category.assoc, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, ← (S.map U hU).naturality f]
  congr 1
  exact ((IsIso.inv_comp_eq _).2 (S.globalSections U hU L).symm).symm

/-! ### A functorial injective resolution of bounded below complexes -/

/-- A functorial injective resolution of bounded below complexes of sheaves of modules, from
the functorial injective embeddings of Tag 01DU through Tag 0141. -/
noncomputable def injectiveResolutionData
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    Σ' F : CochainComplex.Plus (SheafOfModules.{u} R) ⥤
      CochainComplex.Plus (InjectiveObject (SheafOfModules.{u} R)),
      Σ' α : 𝟭 (CochainComplex.Plus (SheafOfModules.{u} R)) ⟶
        F ⋙ (InjectiveObject.ι (SheafOfModules.{u} R)).mapCochainComplexPlus,
        ∀ K, CochainComplex.Plus.quasiIso _ (α.app K) := by
  have hem := StacksDraft.DerivedSectionsComparison.exists_injectiveEmbeddingData
    (SheafOfModules.{u} R)
    (Stacks.Injectives.sheafOfModules_hasFunctorialInjectiveEmbeddings
      (Opens.grothendieckTopology X) R)
  let J := Classical.choose hem
  have hJ := Classical.choose_spec hem
  let η := Classical.choose hJ
  have hres :=
    (CochainComplex.Plus.exists_functorial_injective_resolution_and_exists_resolutionFunctor
      (C := SheafOfModules.{u} R)).1 J η (Classical.choose_spec hJ)
  let F := Classical.choose hres
  have hF := Classical.choose_spec hres
  let α := Classical.choose hF
  exact ⟨F, α, Classical.choose_spec hF⟩

/-- The functorial injective resolution of a bounded below complex of sheaves of modules. -/
noncomputable def injectiveResolutionFunctor
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    CochainComplex.Plus (SheafOfModules.{u} R) ⥤
      CochainComplex.Plus (SheafOfModules.{u} R) :=
  (injectiveResolutionData X R).1 ⋙
    (InjectiveObject.ι (SheafOfModules.{u} R)).mapCochainComplexPlus

/-- The resolution map into the functorial injective resolution. -/
noncomputable def injectiveResolutionUnit
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    𝟭 (CochainComplex.Plus (SheafOfModules.{u} R)) ⟶ injectiveResolutionFunctor X R :=
  (injectiveResolutionData X R).2.1

/-- The resolution map is a quasi-isomorphism. -/
theorem injectiveResolution_quasiIso
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (K : CochainComplex.Plus (SheafOfModules.{u} R)) :
    CochainComplex.Plus.quasiIso _ ((injectiveResolutionUnit X R).app K) :=
  (injectiveResolutionData X R).2.2 K

/-! ### The comparison map -/


/-- On the functorial injective resolution the Čech augmentation is invertible in the derived
category, since the resolving complex has injective terms. -/
theorem isIso_globalSectionsToCechDerived_injectiveResolution
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {I : Type u}
    (U : I → Opens X) (hU : ⊤ = iSup U)
    (K : CochainComplex.Plus (SheafOfModules.{u} R)) :
    IsIso ((globalSectionsToCechDerived X R U).app
      ((injectiveResolutionFunctor X R).obj K)) := by
  refine isIso_globalSectionsToCechDerived_of_injective X R U hU _ fun n => ?_
  show Injective ((InjectiveObject.ι (SheafOfModules.{u} R)).obj _)
  infer_instance

/-- On the functorial injective resolution, the Čech augmentation is an isomorphism. -/
noncomputable def injectiveResolutionCechComparisonIso
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {I : Type u}
    (U : I → Opens X) (hU : ⊤ = iSup U) :
    injectiveResolutionFunctor X R ⋙ globalSectionsDerivedFunctor X R ≅
      injectiveResolutionFunctor X R ⋙ cechDerivedFunctor X R U :=
  NatIso.ofComponents
    (fun K =>
      haveI := isIso_globalSectionsToCechDerived_injectiveResolution X R U hU K
      asIso ((globalSectionsToCechDerived X R U).app
        ((injectiveResolutionFunctor X R).obj K)))
    (fun _ => (globalSectionsToCechDerived X R U).naturality _)

/-- The component at `K` of `injectiveResolutionCechComparisonIso` is the Čech augmentation
`globalSectionsToCechDerived` at the functorial injective resolution of `K`. -/
@[simp]
theorem injectiveResolutionCechComparisonIso_hom_app
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {I : Type u}
    (U : I → Opens X) (hU : ⊤ = iSup U)
    (K : CochainComplex.Plus (SheafOfModules.{u} R)) :
    (injectiveResolutionCechComparisonIso X R U hU).hom.app K =
      (globalSectionsToCechDerived X R U).app
        ((injectiveResolutionFunctor X R).obj K) :=
  rfl

/-- Derived global sections are computed by the functorial injective resolution. -/
noncomputable def derivedGlobalSectionsResolutionIso
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    derivedGlobalSectionsFunctor X R ≅
      injectiveResolutionFunctor X R ⋙ derivedGlobalSectionsFunctor X R := by
  let β := Functor.whiskerRight (injectiveResolutionUnit X R)
    (derivedGlobalSectionsFunctor X R)
  refine NatIso.ofComponents (fun K => ?_) ?_
  · have hα : IsIso (DerivedCategory.Plus.Q.map
        ((injectiveResolutionUnit X R).app K)) := by
      have hm : IsIso (DerivedCategory.Plus.ι.map
          (DerivedCategory.Plus.Q.map ((injectiveResolutionUnit X R).app K))) := by
        change IsIso (DerivedCategory.Q.map ((injectiveResolutionUnit X R).app K).hom)
        exact Localization.inverts (DerivedCategory.Q)
          (HomologicalComplex.quasiIso (C := SheafOfModules.{u} R)
            (c := ComplexShape.up ℤ)) _ (injectiveResolution_quasiIso X R K)
      exact isIso_of_fully_faithful (DerivedCategory.Plus.ι)
        (DerivedCategory.Plus.Q.map ((injectiveResolutionUnit X R).app K))
    have hβ : IsIso (β.app K) := by
      dsimp [β, derivedGlobalSectionsFunctor]
      infer_instance
    exact asIso (β.app K)
  · exact fun f => β.naturality f

/-- The comparison map from the total Čech complex to derived global sections, for one
covering: resolve, invert the injective Čech augmentation, take the unit, and undo the
resolution. -/
noncomputable def cechToDerivedComparison
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {I : Type u}
    (U : I → Opens X) (hU : ⊤ = iSup U) :
    cechDerivedFunctor X R U ⟶ derivedGlobalSectionsFunctor X R :=
  (Functor.leftUnitor (cechDerivedFunctor X R U)).inv ≫
    Functor.whiskerRight (injectiveResolutionUnit X R) (cechDerivedFunctor X R U) ≫
    (injectiveResolutionCechComparisonIso X R U hU).symm.hom ≫
    Functor.whiskerLeft (injectiveResolutionFunctor X R) (globalSectionsToDerivedNat X R) ≫
    (derivedGlobalSectionsResolutionIso X R).symm.hom

/-- The components of the comparison map: resolve, invert the injective Čech augmentation, take
the unit, and undo the resolution. -/
theorem cechToDerivedComparison_app
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {I : Type u}
    (U : I → Opens X) (hU : ⊤ = iSup U)
    (K : CochainComplex.Plus (SheafOfModules.{u} R)) :
    (cechToDerivedComparison X R U hU).app K =
      (cechDerivedFunctor X R U).map ((injectiveResolutionUnit X R).app K) ≫
        (injectiveResolutionCechComparisonIso X R U hU).inv.app K ≫
          (globalSectionsToDerivedNat X R).app ((injectiveResolutionFunctor X R).obj K) ≫
            (derivedGlobalSectionsResolutionIso X R).inv.app K := by
  rw [cechToDerivedComparison]
  simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Category.id_comp]

/-- The comparison map is compatible with the augmentation of Tag 07M9: after it, the composite
is the unit map from ordinary to derived global sections. -/
theorem globalSectionsToCechDerived_comp_cechToDerivedComparison
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {I : Type u}
    (U : I → Opens X) (hU : ⊤ = iSup U)
    (K : CochainComplex.Plus (SheafOfModules.{u} R)) :
    (globalSectionsToCechDerived X R U).app K ≫ (cechToDerivedComparison X R U hU).app K =
      globalSectionsToDerived X R K := by
  let F := cechDerivedFunctor X R U
  let K' := (injectiveResolutionFunctor X R).obj K
  let η := (injectiveResolutionUnit X R).app K
  let β := injectiveResolutionCechComparisonIso X R U hU
  let ρ := derivedGlobalSectionsResolutionIso X R
  have hcech : (globalSectionsToCechDerived X R U).app K ≫ F.map η =
      (globalSectionsDerivedFunctor X R).map η ≫
        (globalSectionsToCechDerived X R U).app K' :=
    ((globalSectionsToCechDerived X R U).naturality η).symm
  have hβ : (globalSectionsToCechDerived X R U).app K' ≫ β.inv.app K = 𝟙 _ :=
    β.hom_inv_id_app K
  show (globalSectionsToCechDerived X R U).app K ≫
    (Functor.leftUnitor F).inv.app K ≫ (𝟭 _ ⋙ F).map η ≫
      β.inv.app K ≫ (globalSectionsToDerivedNat X R).app K' ≫
        ρ.inv.app K = _
  have hγ' : (globalSectionsDerivedFunctor X R).map η ≫
      (globalSectionsToDerivedNat X R).app K' =
    (globalSectionsToDerivedNat X R).app K ≫
      (derivedGlobalSectionsFunctor X R).map η :=
    (globalSectionsToDerivedNat X R).naturality η
  have hρ : (derivedGlobalSectionsFunctor X R).map η = ρ.hom.app K := rfl
  calc
    _ = ((globalSectionsDerivedFunctor X R).map η ≫
        (globalSectionsToCechDerived X R U).app K') ≫ β.inv.app K ≫
          (globalSectionsToDerivedNat X R).app K' ≫ ρ.inv.app K := by
      simp only [Functor.leftUnitor_inv_app, Functor.comp_map, Functor.id_map]
      rw [Category.id_comp, ← Category.assoc, hcech]
    _ = (globalSectionsDerivedFunctor X R).map η ≫
        (globalSectionsToDerivedNat X R).app K' ≫ ρ.inv.app K := by
      rw [Category.assoc, ← Category.assoc ((globalSectionsToCechDerived X R U).app K'),
        hβ, Category.id_comp]
    _ = (globalSectionsToDerivedNat X R).app K ≫
        (derivedGlobalSectionsFunctor X R).map η ≫ ρ.inv.app K := by
      rw [← Category.assoc, hγ', Category.assoc]
    _ = (globalSectionsToDerivedNat X R).app K := by
      rw [hρ, ρ.hom_inv_id_app, Category.comp_id]

/-- The comparison map is compatible with the refinement map of Tag 08BM. -/
theorem cechRefinementDerived_comp_cechToDerivedComparison
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) {I J : Type u}
    (U : I → Opens X) (hU : ⊤ = iSup U) (V : J → Opens X) (hV : ⊤ = iSup V)
    (t : FormalCoproduct.mk J V ⟶ FormalCoproduct.mk I U) :
    cechRefinementDerived X R U V t ≫ cechToDerivedComparison X R V hV =
      cechToDerivedComparison X R U hU := by
  let δ := cechRefinementDerived X R U V t
  let βU := injectiveResolutionCechComparisonIso X R U hU
  let βV := injectiveResolutionCechComparisonIso X R V hV
  ext K
  have haug : βU.hom.app K ≫ δ.app ((injectiveResolutionFunctor X R).obj K) =
      βV.hom.app K := by
    rw [injectiveResolutionCechComparisonIso_hom_app,
      injectiveResolutionCechComparisonIso_hom_app]
    exact NatTrans.congr_app (globalSectionsToCechDerived_refinement X R U V t) _
  have hβ : δ.app ((injectiveResolutionFunctor X R).obj K) ≫ βV.inv.app K =
      βU.inv.app K :=
    ((βV.app K).comp_inv_eq).2 ((βU.app K).eq_inv_comp.2 haug)
  have hδ : δ.app K ≫
        (cechDerivedFunctor X R V).map ((injectiveResolutionUnit X R).app K) =
      (cechDerivedFunctor X R U).map ((injectiveResolutionUnit X R).app K) ≫
        δ.app ((injectiveResolutionFunctor X R).obj K) :=
    (δ.naturality ((injectiveResolutionUnit X R).app K)).symm
  rw [NatTrans.comp_app, cechToDerivedComparison_app, cechToDerivedComparison_app,
    ← Category.assoc, hδ, Category.assoc,
    ← Category.assoc (δ.app ((injectiveResolutionFunctor X R).obj K)), hβ]

/-- **Tag 08BN, the comparison map.** For a ringed space `(X, O_X)` the total Čech complex of a
bounded below complex of `O_X`-modules has a canonical map to its derived global sections,
functorial in the complex, compatible with the augmentation of Tag 07M9 — hence independent of
the covering — and compatible with the refinement map of Tag 08BM. -/
@[stacks 08BN "the tag's comparison map: the total Čech complex of a bounded below complex of \
`O_X`-modules maps canonically to its derived global sections, functorially in the complex -- the \
map is a morphism of functors on bounded below complexes -- and compatibly both with the Tag \
07M9 augmentation and with the Tag 08BM refinement map, simultaneously for every open covering \
of `X`. The tag's spectral sequence `E_2^{p,q} = H^p(Tot(Č(U, H^q(F))))` abutting to \
`H^{p+q}(X, F)` is `Stacks.Cech.exists_cechSpectralSequence`, and the two halves are asserted \
together at the lemma's own three inputs by \
`Stacks.Cech.exists_cechToDerivedComparison_and_cechSpectralSequence`"]
noncomputable def cechToDerivedGlobalSections
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    CechToDerivedGlobalSectionsSystem X R where
  map U hU := cechToDerivedComparison X R U hU
  globalSections U hU K :=
    globalSectionsToCechDerived_comp_cechToDerivedComparison X R U hU K
  globalSections_comp U hU V hV := by
    ext K
    exact (globalSectionsToCechDerived_comp_cechToDerivedComparison X R U hU K).trans
      (globalSectionsToCechDerived_comp_cechToDerivedComparison X R V hV K).symm
  refinement U hU V hV t :=
    cechRefinementDerived_comp_cechToDerivedComparison X R U hU V hV t

end Stacks.Cech
