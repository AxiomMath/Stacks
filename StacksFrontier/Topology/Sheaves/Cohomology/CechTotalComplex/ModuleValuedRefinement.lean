module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.LinearCupProductRefinement
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductComparisonBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleValuedDerivedSections

/-!
# Refinement of coverings and the comparison of total Čech complexes with derived sections

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings and put
`A = Γ(X, 𝒪_X)`.  A refinement `V ⟶ U` of open coverings of `X`, given by `c : J → I` with
`V j ⊆ U (c j)`, induces a map of total Čech complexes `Tot(Č(U, K)) ⟶ Tot(Č(V, K))` of
complexes of `A`-modules, natural in the complex `K` of `𝒪_X`-modules.  This file records that
it is compatible with the augmentation of [Stacks, Tag 07M9] and hence with the comparison map
`Tot(Č(U, K)) ⟶ RΓ(X, K)` of [Stacks, Tag 08BN] (at module coefficients): refining does not
change the comparison.

## Main definitions

* `Stacks.Cech.Refinement.coverRefinementHom`: the morphisms of the slice over `X` given by a
  refinement.
* `Stacks.Cech.Refinement.cechRefinement`: the refinement map of total Čech complexes of a
  complex of `𝒪_X`-modules.

## Main results

* `Stacks.Cech.Refinement.sectionsToTotalCech_comp_cechRefinement`: compatibility with the
  augmentation.
* `Stacks.Cech.Refinement.cechRefinement_comp_totalCechToDerivedSections`: compatibility with
  the comparison to derived sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex Stacks.Cohomology.CechSheaf
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cech.ModuleCupProduct (CoeffRing sectionsComplexFunctor)

universe u

namespace Stacks.Cech.Refinement

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- **The commutative ring structure on the sections of `𝒪_X`**, built on the ring structure the
section ring of `ringSheaf 𝒪_X` already carries, so that the two agree at instance
transparency: the modules over the commutative ring are literally those over the ring. -/
@[reducible]
def sectionCommRing (W : Opens X) : CommRing (SectionRing (ringSheaf O) W) :=
  @CommRing.mk _ (inferInstance : Ring (SectionRing (ringSheaf O) W))
    (fun a b => mul_comm (G := O.obj.obj (op W)) a b)

/-- Sections over the opens of `X`, on complexes of `𝒪_X`-modules. -/
noncomputable abbrev sectionsComplex :
    CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ ⥤
      CochainComplex (Stacks.Cech.LinearCupProduct.PresheafModules.{u} (Over (⊤ : Opens X))
        (SectionRing (ringSheaf O) ⊤)) ℤ :=
  sectionsComplexFunctor O ⊤

variable {I J : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) (V : J → Opens X) (hV : ⊤ = ⨆ j, V j)
  (c : J → I) (hc : ∀ j, V j ≤ U (c j))

/-- The morphism `V j ⟶ U (c j)` of the slice over `X` given by a refinement. -/
def coverRefinementHom (j : J) : coverObject V hV j ⟶ coverObject U hU (c j) :=
  Over.homMk (homOfLE (hc j))

/-- The total Čech complex of the comparison with derived sections is the total Čech complex of
the sections presheaves over the ring of global sections. -/
theorem totalCechComplexFunctor_eq :
    Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU =
      sectionsComplex O ⋙ Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤) :=
  (Stacks.Cech.ModuleCupProduct.totalCechComplexFunctorA_eq O ⊤ U hU).symm

/-- The refinement map of the integer-indexed Čech complexes of `𝒪_X`-modules. -/
noncomputable def cechIntRefinement :
    Stacks.Cohomology.CechDerived.cechComplexIntFunctor (ringSheaf O) ⊤ U hU ⟶
      Stacks.Cohomology.CechDerived.cechComplexIntFunctor (ringSheaf O) ⊤ V hV :=
  Functor.whiskerLeft (sectionsPresheafFunctor (R := ringSheaf O) ⊤)
    (Stacks.Cech.LinearCupProduct.cechIntRefinement (coverObject U hU) (coverObject V hV)
      (SectionRing (ringSheaf O) ⊤) c (coverRefinementHom U hU V hV c hc))

/-- **The refinement map of total Čech complexes** `Tot(Č(U, K)) ⟶ Tot(Č(V, K))`, natural in the
complex `K` of `𝒪_X`-modules. -/
noncomputable def cechRefinement :
    Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU ⟶
      Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ V hV :=
  letI : (Stacks.Cohomology.CechDerived.cechComplexIntFunctor
      (ringSheaf O) ⊤ U hU).PreservesZeroMorphisms :=
    Stacks.Cohomology.CechDerived.preservesZeroMorphisms_cechComplexIntFunctor
      (ringSheaf O) ⊤ U hU
  letI : (Stacks.Cohomology.CechDerived.cechComplexIntFunctor
      (ringSheaf O) ⊤ V hV).PreservesZeroMorphisms :=
    Stacks.Cohomology.CechDerived.preservesZeroMorphisms_cechComplexIntFunctor
      (ringSheaf O) ⊤ V hV
  Functor.whiskerRight
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (cechIntRefinement O U hU V hV c hc) (up ℤ))
      (HomologicalComplex₂.flipFunctor (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) (up ℤ) (up ℤ)))
    (HomologicalComplex₂.totalFunctor (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) (up ℤ) (up ℤ)
      (up ℤ))

/-- On the degree-zero Čech cochains the refinement map carries the restriction of a global
section to the members of `U` to its restriction to the members of `V`. -/
theorem cechDegreeZeroRestriction_comp_cechRefinement
    (F : SheafOfModules.{u} (ringSheaf O)) :
    Stacks.Cohomology.CechDerived.cechDegreeZeroRestriction (ringSheaf O) ⊤ U hU F ≫
        (Stacks.Cech.LinearCupProduct.cechRefinement (coverObject U hU) (coverObject V hV)
          (SectionRing (ringSheaf O) ⊤) c (coverRefinementHom U hU V hV c hc)
          ((sectionsPresheafFunctor (R := ringSheaf O) ⊤).obj F)).f 0 =
      Stacks.Cohomology.CechDerived.cechDegreeZeroRestriction (ringSheaf O) ⊤ V hV F := by
  refine hom_ext (coverObject V hV) _ fun x => ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _
    (Stacks.Cech.LinearCupProduct.cechRefinement_f_comp_π _ _ _ _ _ _ 0 x)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker (Stacks.Cohomology.CechDerived.cechDegreeZeroRestriction_comp_π
    (ringSheaf O) ⊤ U hU F (c ∘ x)) _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Stacks.Cohomology.CechDerived.cechDegreeZeroRestriction_comp_π
    (ringSheaf O) ⊤ V hV F x).symm
  refine whisker_eq _ ((Functor.map_comp (sectionsPresheaf ⊤ F) _ _).symm.trans ?_)
  exact congrArg (sectionsPresheaf ⊤ F).map (congrArg Quiver.Hom.op (Subsingleton.elim _ _))

/-- The refinement map on a homogeneous summand of the total Čech complex. -/
theorem ιTotal_cechRefinement (K : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ)
    (p a n : ℤ) (h : p + a = n) :
    (Stacks.Cohomology.CechDerived.cechBicomplex (ringSheaf O) ⊤ U hU K).flip.ιTotal (up ℤ)
        p a n h ≫ ((cechRefinement O U hU V hV c hc).app K).f n =
      ((cechIntRefinement O U hU V hV c hc).app (K.X a)).f p ≫
        (Stacks.Cohomology.CechDerived.cechBicomplex (ringSheaf O) ⊤ V hV K).flip.ιTotal (up ℤ)
          p a n h := by
  exact Stacks.Cech.LinearCupProduct.ιTotal_totalCechRefinement
    (coverObject U hU) (coverObject V hV) (SectionRing (ringSheaf O) ⊤)
    c (coverRefinementHom U hU V hV c hc) ((sectionsComplex O).obj K) p a n h

/-- The refinement map of the integer-indexed Čech complexes in degree zero. -/
theorem cechIntRefinement_app_f_zero (F : SheafOfModules.{u} (ringSheaf O)) :
    ((cechIntRefinement O U hU V hV c hc).app F).f 0 =
      (HomologicalComplex.extendXIso _ embeddingUpNat (i := 0) rfl).hom ≫
        (Stacks.Cech.LinearCupProduct.cechRefinement (coverObject U hU) (coverObject V hV)
          (SectionRing (ringSheaf O) ⊤) c (coverRefinementHom U hU V hV c hc)
          ((sectionsPresheafFunctor (R := ringSheaf O) ⊤).obj F)).f 0 ≫
        (HomologicalComplex.extendXIso _ embeddingUpNat (i := 0) rfl).inv :=
  HomologicalComplex.extendMap_f _ embeddingUpNat rfl

/-- **The refinement map is compatible with the augmentation of [Stacks, Tag 07M9]**: a global
section restricted to the members of `U` and then refined is its restriction to the members of
`V`. -/
theorem sectionsToTotalCech_comp_cechRefinement
    (K : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) :
    (Stacks.Cech.Linear.sectionsToTotalCech X (ringSheaf O) ⊤ U hU).app K ≫
        (cechRefinement O U hU V hV c hc).app K =
      (Stacks.Cech.Linear.sectionsToTotalCech X (ringSheaf O) ⊤ V hV).app K := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine (HomologicalComplex.comp_f _ _ n).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (ιTotal_cechRefinement O U hU V hV c hc K 0 n n (by simp))).trans ?_
  refine (Category.assoc _ _ _).symm.trans (eq_whisker ?_ _)
  refine (whisker_eq _ (cechIntRefinement_app_f_zero O U hU V hV c hc (K.X n))).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (Iso.inv_hom_id_assoc _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact eq_whisker (cechDegreeZeroRestriction_comp_cechRefinement O U hU V hV c hc (K.X n)) _

/-- The refinement map of total Čech complexes, in the derived category of `A`-modules. -/
noncomputable def cechRefinementDerived :
    Stacks.Cech.Linear.totalCechDerivedFunctor X (ringSheaf O) ⊤ U hU ⟶
      Stacks.Cech.Linear.totalCechDerivedFunctor X (ringSheaf O) ⊤ V hV :=
  Functor.whiskerRight
    (Functor.whiskerLeft (CochainComplex.Plus.ι _) (cechRefinement O U hU V hV c hc))
    DerivedCategory.Q

/-- The augmentation into the derived total Čech complex commutes with refinement. -/
theorem sectionsToTotalCechDerived_comp_cechRefinementDerived :
    Stacks.Cech.Linear.sectionsToTotalCechDerived X (ringSheaf O) ⊤ U hU ≫
        cechRefinementDerived O U hU V hV c hc =
      Stacks.Cech.Linear.sectionsToTotalCechDerived X (ringSheaf O) ⊤ V hV := by
  ext K
  exact (DerivedCategory.Q.map_comp _ _).symm.trans
    (congrArg DerivedCategory.Q.map (sectionsToTotalCech_comp_cechRefinement O U hU V hV c hc K.1))

/-- **Refinement does not change the comparison with derived sections**: the comparison map of
[Stacks, Tag 08BN] for `V`, precomposed with the refinement map, is the comparison map for
`U`. -/
theorem cechRefinementDerived_comp_totalCechToDerivedSections :
    cechRefinementDerived O U hU V hV c hc ≫
        Stacks.Cech.Linear.totalCechToDerivedSections X (ringSheaf O) ⊤ V hV =
      Stacks.Cech.Linear.totalCechToDerivedSections X (ringSheaf O) ⊤ U hU := by
  let δ := cechRefinementDerived O U hU V hV c hc
  let βU := Stacks.Cech.Linear.injectiveResolutionCechComparisonIso X (ringSheaf O) ⊤ U hU
  let βV := Stacks.Cech.Linear.injectiveResolutionCechComparisonIso X (ringSheaf O) ⊤ V hV
  ext K
  have haug : βU.hom.app K ≫ δ.app ((Stacks.Cech.injectiveResolutionFunctor X _).obj K) =
      βV.hom.app K := by
    rw [Stacks.Cech.Linear.injectiveResolutionCechComparisonIso_hom_app,
      Stacks.Cech.Linear.injectiveResolutionCechComparisonIso_hom_app]
    exact NatTrans.congr_app
      (sectionsToTotalCechDerived_comp_cechRefinementDerived O U hU V hV c hc) _
  have hβ : δ.app ((Stacks.Cech.injectiveResolutionFunctor X _).obj K) ≫ βV.inv.app K =
      βU.inv.app K := by
    rw [← cancel_epi (βU.hom.app K), ← Category.assoc, haug, βU.hom_inv_id_app,
      βV.hom_inv_id_app]
  have hδ : δ.app K ≫
        (Stacks.Cech.Linear.totalCechDerivedFunctor X (ringSheaf O) ⊤ V hV).map
          ((Stacks.Cech.injectiveResolutionUnit X _).app K) =
      (Stacks.Cech.Linear.totalCechDerivedFunctor X (ringSheaf O) ⊤ U hU).map
          ((Stacks.Cech.injectiveResolutionUnit X _).app K) ≫
        δ.app ((Stacks.Cech.injectiveResolutionFunctor X _).obj K) :=
    (δ.naturality ((Stacks.Cech.injectiveResolutionUnit X _).app K)).symm
  rw [NatTrans.comp_app, Stacks.Cech.Linear.totalCechToDerivedSections_app,
    Stacks.Cech.Linear.totalCechToDerivedSections_app, ← Category.assoc, hδ, Category.assoc,
    ← Category.assoc (δ.app ((Stacks.Cech.injectiveResolutionFunctor X _).obj K)), hβ]

/-- The refinement map of total Čech complexes of `𝒪_X`-modules is the refinement map of the total
Čech complexes of their sections presheaves. -/
theorem cechRefinement_eq :
    cechRefinement O U hU V hV c hc =
      eqToHom (totalCechComplexFunctor_eq O U hU) ≫
        Functor.whiskerLeft (sectionsComplex O)
          (Stacks.Cech.LinearCupProduct.totalCechRefinement (coverObject U hU) (coverObject V hV)
            (SectionRing (ringSheaf O) ⊤) c (coverRefinementHom U hU V hV c hc)) ≫
        eqToHom (totalCechComplexFunctor_eq O V hV).symm := by
  ext K : 2
  simp only [NatTrans.comp_app, eqToHom_app, Functor.whiskerLeft_app]
  rfl

end Stacks.Cech.Refinement

end
