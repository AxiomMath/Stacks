module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusBoundary
public import StacksFrontier.Algebra.Homology.CupProductBoundaryDelta
public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.ModuleValuedRefinement
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AcyclicCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.LongExactSequence
public import StacksFrontier.Algebra.Homology.TotalComplexShortExact

/-!
# Hypercohomology of complexes of `𝒪_X`-modules, its boundary maps, and Čech cocycles

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings and put
`A = Γ(X, 𝒪_X)`.  For a bounded below complex `K` of `𝒪_X`-modules its hypercohomology is
`Hⁿ(X, K) = Hⁿ(RΓ(X, K))`, an `A`-module.  A short exact sequence `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` of
bounded below complexes gives a distinguished triangle `K₁ ⟶ K₂ ⟶ K₃ ⟶ K₁[1]` and hence boundary
maps `∂ : Hⁿ(X, K₃) ⟶ Hⁿ⁺¹(X, K₁)` (with the conventions of Derived Categories, Section 014P:
the boundary map of a short exact sequence of complexes is the one of the snake lemma).

The main result computes `∂` on Čech cocycles: if `α₂` is a degree `n` cochain of the total Čech
complex `Tot(Č(𝒰, K₂))` of an open covering whose image `ᾱ₂` in `Tot(Č(𝒰, K₃))` is a cocycle,
and `α₁` is a cocycle of `Tot(Č(𝒰, K₁))` with image `d(α₂)`, then the class of `α₁` in
`Hⁿ⁺¹(X, K₁)` is `∂` of the class of `ᾱ₂` in `Hⁿ(X, K₃)`, the classes being taken through the
comparison `Tot(Č(𝒰, -)) ⟶ RΓ(X, -)` of [Stacks, Tag 08BN].

## Main definitions

* `Stacks.Cech.Hypercohomology.hypercohomology`: `Hⁿ(X, K)`.
* `Stacks.Cech.Hypercohomology.boundary`: the boundary map `Hⁿ(X, K₃) ⟶ Hⁿ⁺¹(X, K₁)` of a short
  exact sequence of bounded below complexes.
* `Stacks.Cech.Hypercohomology.cechClass`: the map from the cohomology of the total Čech complex
  of a covering to hypercohomology.

## Main results

* `Stacks.Cech.Hypercohomology.boundary_naturality`: the boundary maps are natural in the short
  exact sequence.
* `Stacks.Cech.Hypercohomology.cechClass_boundary`: the boundary map on Čech cocycles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.RightDerivedBoundary
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- `Stacks.Cohomology.CechDerived.additive_evaluation` at the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling of the sheaf of rings, which is the spelling
the module-valued Čech API is stated at.  Instance search does not find the general instance at
that spelling: `ringSheaf` is reducible, so a goal about `ringSheaf O` is keyed on the composite
`O.obj ⋙ forget₂ CommRingCat RingCat` it unfolds to, while the general instance is keyed on a
sheaf of rings.  It is recorded as a local instance only, so no new instance leaves this file. -/
local instance additive_evaluation_ringSheaf :
    (SheafOfModules.evaluation.{u} (ringSheaf O) (op (⊤ : Opens X))).Additive :=
  Stacks.Cohomology.CechDerived.additive_evaluation (ringSheaf O) ⊤

/-- **The hypercohomology `Hⁿ(X, K) = Hⁿ(RΓ(X, K))`** of a bounded below complex of
`𝒪_X`-modules, an `A`-module for `A = Γ(X, 𝒪_X)`. -/
def hypercohomology (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ) :
    ModuleCat.{u} (SectionRing (ringSheaf O) ⊤) :=
  (DerivedCategory.homologyFunctor _ n).obj
    ((Stacks.Cech.Linear.derivedSectionsFunctor X (ringSheaf O) ⊤).obj K)

/-- Hypercohomology of a morphism of complexes. -/
def hypercohomologyMap {K L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (f : K ⟶ L) (n : ℤ) : hypercohomology O K n ⟶ hypercohomology O L n :=
  (DerivedCategory.homologyFunctor _ n).map
    ((Stacks.Cech.Linear.derivedSectionsFunctor X (ringSheaf O) ⊤).map f)

/-- The connecting morphism `RΓ(X, K₃) ⟶ RΓ(X, K₁)[1]` of the image under `RΓ(X, -)` of the
distinguished triangle of a short exact sequence of bounded below complexes. -/
def boundaryD (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) :
    (Stacks.Cech.Linear.derivedSectionsFunctor X (ringSheaf O) ⊤).obj S.X₃ ⟶
      ((Stacks.Cech.Linear.derivedSectionsFunctor X (ringSheaf O) ⊤).obj S.X₁)⟦(1 : ℤ)⟧ :=
  Functor.mapδ ((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.ι) (plusδ S hS)

/-- **The boundary map `∂ : Hⁿ(X, K₃) ⟶ Hⁿ⁺¹(X, K₁)`** of a short exact sequence
`0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` of bounded below complexes of `𝒪_X`-modules: the connecting morphism of
the long exact cohomology sequence of the distinguished triangle
`RΓ(X, K₁) ⟶ RΓ(X, K₂) ⟶ RΓ(X, K₃) ⟶ RΓ(X, K₁)[1]`. -/
def boundary (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    hypercohomology O S.X₃ n₀ ⟶ hypercohomology O S.X₁ n₁ :=
  (DerivedCategory.homologyFunctor _ 0).shiftMap (boundaryD O S hS) n₀ n₁ (by omega)

/-- Two squares pasted, stated with every object and morphism a variable. -/
theorem comp_comp_eq_of_eq {C : Type*} [Category* C] {a b c d e f : C} (x : a ⟶ b) (y : b ⟶ c)
    (z : c ⟶ d) (y' : a ⟶ e) (w : e ⟶ c) (z' : e ⟶ f) (v : f ⟶ d) (h₁ : x ≫ y = y' ≫ w)
    (h₂ : w ≫ z = z' ≫ v) : x ≫ y ≫ z = (y' ≫ z') ≫ v := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- `plusδ` is natural in the short exact sequence. -/
theorem plusδ_naturality {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {S S' : ShortComplex (CochainComplex.Plus A)} (hS : (toSC S).ShortExact)
    (hS' : (toSC S').ShortExact) (φ : S ⟶ S') :
    plusδ S hS ≫ (DerivedCategory.Plus.Q.map φ.τ₁)⟦(1 : ℤ)⟧' =
      DerivedCategory.Plus.Q.map φ.τ₃ ≫ plusδ S' hS' := by
  refine Functor.mapδ_cancel DerivedCategory.Plus.ι _ _ _ _ ?_
  rw [mapδ_ι_plusδ, mapδ_ι_plusδ]
  exact DerivedCategory.triangleOfSESδ_naturality hS hS'
    ((CochainComplex.Plus.ι A).mapShortComplex.map φ)

/-- **The boundary maps are natural in the short exact sequence**, before taking cohomology. -/
theorem boundaryD_naturality
    {S S' : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))}
    (hS : (toSC S).ShortExact) (hS' : (toSC S').ShortExact) (φ : S ⟶ S') :
    boundaryD O S hS ≫
        ((Stacks.Cech.Linear.derivedSectionsFunctor X (ringSheaf O) ⊤).map φ.τ₁)⟦(1 : ℤ)⟧' =
      (Stacks.Cech.Linear.derivedSectionsFunctor X (ringSheaf O) ⊤).map φ.τ₃ ≫
        boundaryD O S' hS' :=
  Functor.mapδ_naturality _ _ _ _ _ (plusδ_naturality hS hS' φ)

/-- **The boundary maps are natural in the short exact sequence.** -/
theorem boundary_naturality
    {S S' : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))}
    (hS : (toSC S).ShortExact) (hS' : (toSC S').ShortExact) (φ : S ⟶ S') (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) :
    boundary O S hS n₀ n₁ h ≫ hypercohomologyMap O φ.τ₁ n₁ =
      hypercohomologyMap O φ.τ₃ n₀ ≫ boundary O S' hS' n₀ n₁ h :=
  (Functor.shiftMap_comp _ _ _ _ _ _).symm.trans
    ((congrArg (fun g => (DerivedCategory.homologyFunctor _ 0).shiftMap g n₀ n₁ (by omega))
      (boundaryD_naturality O hS hS' φ)).trans (Functor.shiftMap_comp' _ _ _ _ _ _))

end Stacks.Cech.Hypercohomology

namespace Stacks.Cech.Hypercohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus
  CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit
attribute [local instance] additive_evaluation_ringSheaf

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- The inverse of `Stacks.Cech.Linear.sectionsHomotopyBridgeIso` is the identity at every
bounded below complex. -/
theorem sectionsHomotopyBridgeIso_inv_app
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) :
    (Stacks.Cech.Linear.sectionsHomotopyBridgeIso X (ringSheaf O) ⊤).inv.app K = 𝟙 _ := rfl

/-- The canonical map from ordinary to derived sections is the canonical map `unitD` of the
right derived functor of sections. -/
theorem sectionsToDerived_eq_unitD
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) :
    Stacks.Cech.Linear.sectionsToDerived X (ringSheaf O) ⊤ K =
      unitD (SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)) K := by
  have h : Stacks.Cech.Linear.sectionsToDerived X (ringSheaf O) ⊤ K =
      (DerivedCategory.quotientCompQhIso _).inv.app
          (((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).mapHomologicalComplex
            (up ℤ)).obj K.obj) ≫
        DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ ≫
        DerivedCategory.Plus.ι.map
          ((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient _).obj K)) ≫
        DerivedCategory.Plus.ι.map
          ((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus.map
            ((StacksDraft.DerivedSectionsComparison.quotientQhIsoQ _).hom.app K)) := rfl
  rw [h, CategoryTheory.Functor.map_id]
  exact whisker_eq _ ((Category.id_comp _).trans (Category.id_comp _))

/-- **On a short exact sequence which stays short exact on sections, the canonical map from
ordinary to derived sections carries the connecting morphism of the sequence of sections to the
boundary map.** -/
theorem triangleOfSESδ_comp_sectionsToDerived
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact)
    (hΓS : ((toSC S).map ((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).mapHomologicalComplex
      (up ℤ))).ShortExact) :
    DerivedCategory.triangleOfSESδ hΓS ≫
        (Stacks.Cech.Linear.sectionsToDerived X (ringSheaf O) ⊤ S.X₁)⟦(1 : ℤ)⟧' =
      Stacks.Cech.Linear.sectionsToDerived X (ringSheaf O) ⊤ S.X₃ ≫ boundaryD O S hS := by
  rw [sectionsToDerived_eq_unitD, sectionsToDerived_eq_unitD]
  exact triangleOfSESδ_comp_unitD _ S hS hΓS

section Cech

variable {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)

/-- `Stacks.Cohomology.CechAcyclic.additive_sectionsPresheafFunctor` at the
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling of the sheaf of rings: the functor of sections
over `⊤` is additive. -/
local instance additive_sectionsPresheafFunctor_ringSheaf :
    (Stacks.Cohomology.CechSheaf.sectionsPresheafFunctor
      (R := ringSheaf O) (⊤ : Opens X)).Additive :=
  Stacks.Cohomology.CechAcyclic.additive_sectionsPresheafFunctor (ringSheaf O) ⊤

/-- The total Čech complex functor of the open cover `U` is additive. -/
instance additive_totalCechComplexFunctor :
    (Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).Additive := by
  dsimp only [Stacks.Cech.Linear.totalCechComplexFunctor,
    Stacks.Cohomology.CechDerived.cechComplexIntFunctor,
    Stacks.Cohomology.CechDerived.cechComplexNatFunctor,
    Stacks.Cohomology.CechSheaf.cechComplexFunctorOfCover]
  infer_instance

/-- The `ℤ`-indexed Čech complex functor of the open cover `U` is additive. -/
instance additive_cechComplexIntFunctor :
    (Stacks.Cohomology.CechDerived.cechComplexIntFunctor (ringSheaf O) ⊤ U hU).Additive := by
  dsimp only [Stacks.Cohomology.CechDerived.cechComplexIntFunctor,
    Stacks.Cohomology.CechDerived.cechComplexNatFunctor,
    Stacks.Cohomology.CechSheaf.cechComplexFunctorOfCover]
  infer_instance

/-- The degreewise splitting of a short exact sequence of complexes with injective first term,
transported along any additive functor. -/
private theorem nonempty_splitting_map_eval
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (hinj : ∀ n, Injective (S.X₁.obj.X n))
    {D : Type*} [Category* D] [Preadditive D] (F : SheafOfModules.{u} (ringSheaf O) ⥤ D)
    [F.Additive] (q : ℤ) :
    Nonempty (((toSC S).map (HomologicalComplex.eval _ (up ℤ) q ⋙ F)).Splitting) := by
  have hq := hS.map_of_exact (HomologicalComplex.eval _ (up ℤ) q)
  have : Injective ((toSC S).map (HomologicalComplex.eval _ (up ℤ) q)).X₁ := hinj q
  exact ⟨hq.splittingOfInjective.map F⟩

/-- **The total Čech complexes of a short exact sequence of complexes whose first term has
injective terms form a short exact sequence**: the sequence is split in each degree, and the Čech
complex functor and the totalization preserve such splittings. -/
theorem shortExact_totalCech_of_injective
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (hinj : ∀ n, Injective (S.X₁.obj.X n)) :
    ((toSC S).map
      (Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU)).ShortExact := by
  let T := (toSC S).map
    ((Stacks.Cohomology.CechDerived.cechComplexIntFunctor (ringSheaf O) ⊤ U
        hU).mapHomologicalComplex
      (up ℤ) ⋙ HomologicalComplex₂.flipFunctor _ (up ℤ) (up ℤ))
  have σ : ∀ p q,
      (T.map (HomologicalComplex.eval _ _ p ⋙ HomologicalComplex.eval _ _ q)).Splitting :=
    fun p q => (nonempty_splitting_map_eval O S hS hinj
      (Stacks.Cohomology.CechDerived.cechComplexIntFunctor (ringSheaf O) ⊤ U hU ⋙
        HomologicalComplex.eval _ _ p) q).some
  exact HomologicalComplex₂.shortExact_total_of_splitting (c₁₂ := up ℤ) T σ

/-- **The class in hypercohomology of a cohomology class of the total Čech complex**, through the
comparison `Tot(Č(𝒰, K)) ⟶ RΓ(X, K)` of [Stacks, Tag 08BN]. -/
def cechClass (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ) :
    ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).obj K.obj).homology n ⟶
      hypercohomology O K n :=
  (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫
    (DerivedCategory.homologyFunctor _ n).map
      ((Stacks.Cech.Linear.totalCechToDerivedSections X (ringSheaf O) ⊤ U hU).app K)

/-- `cechClass` is natural in the complex. -/
@[reassoc]
theorem cechClass_naturality {K L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (f : K ⟶ L) (n : ℤ) :
    HomologicalComplex.homologyMap
        ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).map f.hom) n ≫
        cechClass O U hU L n =
      cechClass O U hU K n ≫ hypercohomologyMap O f n := by
  dsimp only [cechClass, hypercohomologyMap]
  have h1 := (DerivedCategory.homologyFunctorFactors
    (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) n).inv.naturality
      ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).map f.hom)
  have h2 := (Stacks.Cech.Linear.totalCechToDerivedSections X (ringSheaf O) ⊤ U hU).naturality f
  have h3 := congrArg (DerivedCategory.homologyFunctor
    (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) n).map h2
  simp only [Functor.map_comp] at h3
  exact comp_comp_eq_of_eq _ _ _ _ _ _ _ h1 h3

/-- **Sections of a short exact sequence of complexes whose first term has injective terms form a
short exact sequence**: the sequence is split in each degree. -/
theorem shortExact_sections_of_injective
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (hinj : ∀ n, Injective (S.X₁.obj.X n)) :
    ((toSC S).map ((SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)).mapHomologicalComplex
      (up ℤ))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun q =>
    (nonempty_splitting_map_eval O S hS hinj
      (SheafOfModules.evaluation.{u} (ringSheaf O) (op ⊤)) q).some.shortExact

/-- The rearrangement in `totalCechToDerivedSections_comp_boundaryD_of_injective`, stated with
every object and morphism a variable. -/
theorem cancel_aux {C : Type*} [Category* C] {x y z w v v' : C} (a₃ : x ⟶ y) (c₃ : y ⟶ z)
    (Δ : z ⟶ w) (s₃ : x ⟶ z) (hs₃ : a₃ ≫ c₃ = s₃) (δΓ : x ⟶ v) (s₁ : v ⟶ w)
    (h : δΓ ≫ s₁ = s₃ ≫ Δ) (a₁ : v ⟶ v') (c₁ : v' ⟶ w) (hs₁ : a₁ ≫ c₁ = s₁) (δC : y ⟶ v')
    (hnat : δΓ ≫ a₁ = a₃ ≫ δC) [Epi a₃] : c₃ ≫ Δ = δC ≫ c₁ := by
  refine (cancel_epi a₃).1 ?_
  rw [← Category.assoc, hs₃, ← h, ← hs₁, ← Category.assoc, hnat, Category.assoc]

/-- **On a short exact sequence of bounded below complexes with injective terms, the comparison
of [Stacks, Tag 08BN] carries the connecting morphism of the sequence of total Čech complexes to
the boundary map.** -/
theorem totalCechToDerivedSections_comp_boundaryD_of_injective
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (hinj₁ : ∀ n, Injective (S.X₁.obj.X n))
    (hinj₃ : ∀ n, Injective (S.X₃.obj.X n)) :
    (Stacks.Cech.Linear.totalCechToDerivedSections X (ringSheaf O) ⊤ U hU).app S.X₃ ≫
        boundaryD O S hS =
      DerivedCategory.triangleOfSESδ (shortExact_totalCech_of_injective O U hU S hS hinj₁) ≫
        ((Stacks.Cech.Linear.totalCechToDerivedSections X (ringSheaf O) ⊤ U hU).app
          S.X₁)⟦(1 : ℤ)⟧' := by
  have hΓS := shortExact_sections_of_injective O S hS hinj₁
  have hnat := DerivedCategory.triangleOfSESδ_naturality hΓS
    (shortExact_totalCech_of_injective O U hU S hS hinj₁)
    ((toSC S).mapNatTrans (Stacks.Cech.Linear.sectionsToTotalCech X (ringSheaf O) ⊤ U hU))
  have h := triangleOfSESδ_comp_sectionsToDerived O S hS hΓS
  have hs₃ := Stacks.Cech.Linear.sectionsToTotalCechDerived_comp_totalCechToDerivedSections X
    (ringSheaf O) ⊤ U hU S.X₃
  have hs₁ := congrArg (fun g => g⟦(1 : ℤ)⟧')
    (Stacks.Cech.Linear.sectionsToTotalCechDerived_comp_totalCechToDerivedSections X
      (ringSheaf O) ⊤ U hU S.X₁)
  simp only [Functor.map_comp] at hs₁
  have := Stacks.Cech.Linear.isIso_sectionsToTotalCechDerived_of_injective X (ringSheaf O) ⊤ U hU
    S.X₃ hinj₃
  exact cancel_aux _ _ _ _ hs₃ _ _ h _ _ hs₁ _ hnat

/-- A square of natural isomorphisms inverted, stated with every object and morphism a
variable. -/
theorem inv_app_comp_eq {C D : Type*} [Category* C] [Category* D] {F G F' G' : C ⥤ D}
    (e : F ≅ G) (e' : F' ≅ G') {X Y : C} (x : G.obj X ⟶ G'.obj Y) (y : F.obj X ⟶ F'.obj Y)
    (h : e.hom.app X ≫ x = y ≫ e'.hom.app Y) : e.inv.app X ≫ y = x ≫ e'.inv.app Y := by
  rw [← cancel_mono (e'.hom.app Y), Category.assoc, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, ← h, Iso.inv_hom_id_app_assoc]

/-- The pasting in `cechClass_boundary_of_injective`, stated with every object and morphism a
variable. -/
theorem paste_aux {C : Type*} [Category* C] {a b c d e f : C} (fi₃ : a ⟶ b) (H₃ : b ⟶ c)
    (sΔ : c ⟶ d) (scomp : b ⟶ d) (hcomp : H₃ ≫ sΔ = scomp) (sδC : b ⟶ e) (H₁ : e ⟶ d)
    (hcomp' : scomp = sδC ≫ H₁) (δ : a ⟶ f) (fi₁ : f ⟶ e) (hfac : fi₃ ≫ sδC = δ ≫ fi₁) :
    fi₃ ≫ H₃ ≫ sΔ = δ ≫ fi₁ ≫ H₁ := by
  rw [hcomp, hcomp', ← Category.assoc, hfac, Category.assoc]

/-- **On a short exact sequence of bounded below complexes with injective terms, the Čech classes
carry the connecting morphism of the sequence of total Čech complexes to the boundary map of
hypercohomology.** -/
theorem cechClass_boundary_of_injective
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (hinj₁ : ∀ n, Injective (S.X₁.obj.X n))
    (hinj₃ : ∀ n, Injective (S.X₃.obj.X n)) (n : ℤ) :
    cechClass O U hU S.X₃ n ≫ boundary O S hS n (n + 1) rfl =
      (shortExact_totalCech_of_injective O U hU S hS hinj₁).δ n (n + 1) rfl ≫
        cechClass O U hU S.X₁ (n + 1) := by
  have hC := shortExact_totalCech_of_injective O U hU S hS hinj₁
  have hfac : (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫
      DerivedCategory.HomologySequence.δ (DerivedCategory.triangleOfSES hC) n (n + 1) rfl =
      hC.δ n (n + 1) rfl ≫ (DerivedCategory.homologyFunctorFactors _ (n + 1)).inv.app _ :=
    inv_app_comp_eq (DerivedCategory.homologyFunctorFactors _ n)
      (DerivedCategory.homologyFunctorFactors _ (n + 1)) _ _
      (DerivedCategory.homologySequenceδ_triangleOfSES hC n (n + 1) rfl)
  have hc := totalCechToDerivedSections_comp_boundaryD_of_injective O U hU S hS hinj₁ hinj₃
  exact paste_aux _ _ _ _ (Functor.shiftMap_comp' _ _ _ _ _ _).symm _ _
    ((congrArg (fun g => (DerivedCategory.homologyFunctor _ 0).shiftMap g n (n + 1) (by omega))
      hc).trans (Functor.shiftMap_comp _ _ _ _ _ _)) _ _ hfac

/-- The class of a cocycle in the cohomology of a complex. -/
def cocycleClass {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ} {P : C}
    (n : ℤ) (x : P ⟶ K.X n) (hx : x ≫ K.d n (n + 1) = 0) : P ⟶ K.homology n :=
  K.liftCycles x (n + 1) (CochainComplex.next ℤ n) hx ≫ K.homologyπ n

/-- The class of a cocycle pushed along a morphism of complexes. -/
@[reassoc]
theorem cocycleClass_comp_homologyMap {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) {P : C} (n : ℤ) (x : P ⟶ K.X n)
    (hx : x ≫ K.d n (n + 1) = 0) :
    cocycleClass n x hx ≫ HomologicalComplex.homologyMap φ n =
      cocycleClass n (x ≫ φ.f n) (by rw [Category.assoc, φ.comm, reassoc_of% hx, zero_comp]) := by
  dsimp only [cocycleClass]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]

/-- **A short exact sequence of bounded below complexes maps to one of injective resolutions**:
the first and third terms of the target have injective terms, and the first component of the map
is a quasi-isomorphism. -/
theorem exists_shortExact_injective_hom
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) :
    ∃ (SI : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))) (φ : S ⟶ SI),
      (toSC SI).ShortExact ∧ (∀ n, Injective (SI.X₁.obj.X n)) ∧
        (∀ n, Injective (SI.X₃.obj.X n)) ∧ QuasiIso φ.τ₁.hom := by
  obtain ⟨a, ha⟩ := (CochainComplex.plus_iff _ S.X₂.obj).mp S.X₂.property
  have : (toSC S).X₂.IsStrictlyGE a := ha
  obtain ⟨b, hb⟩ := (CochainComplex.plus_iff _ S.X₁.obj).mp S.X₁.property
  have : (toSC S).X₁.IsStrictlyGE b := hb
  obtain ⟨R₁, -, -⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE b (toSC S).X₁
  obtain ⟨R₂, R₃, f, g, w, hR, -, h₁, h₂⟩ := hS.exists_shortExact_injectiveResolution a R₁
  exact ⟨ShortComplex.mk (X₁ := ⟨R₁.cocomplex, R₁.boundedBelow⟩)
      (X₂ := ⟨R₂.cocomplex, R₂.boundedBelow⟩) (X₃ := ⟨R₃.cocomplex, R₃.boundedBelow⟩)
      (ObjectProperty.homMk f) (ObjectProperty.homMk g) (ObjectProperty.hom_ext _ w),
    { τ₁ := ObjectProperty.homMk R₁.ι
      τ₂ := ObjectProperty.homMk R₂.ι
      τ₃ := ObjectProperty.homMk R₃.ι
      comm₁₂ := ObjectProperty.hom_ext _ h₁
      comm₂₃ := ObjectProperty.hom_ext _ h₂ }, hR, R₁.injective, R₃.injective, R₁.quasiIso⟩

/-- **The boundary map of hypercohomology on Čech cocycles.**  Let
`0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` be a short exact sequence of bounded below complexes of `𝒪_X`-modules
and `𝒰` an open covering of `X`.  If `α₂` is a degree `n` cochain of `Tot(Č(𝒰, K₂))` whose image
`ᾱ₂` in `Tot(Č(𝒰, K₃))` is a cocycle, and `α₁` is a cocycle of `Tot(Č(𝒰, K₁))` whose image in
`Tot(Č(𝒰, K₂))` is `d(α₂)`, then the class of `α₁` in `Hⁿ⁺¹(X, K₁)` is `∂` of the class of `ᾱ₂`
in `Hⁿ(X, K₃)`. -/
theorem cechClass_boundary
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) {P : ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)}
    (α₂ : P ⟶ ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).obj
      S.X₂.obj).X n)
    (α₁ : P ⟶ ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).obj
      S.X₁.obj).X (n + 1))
    (hα₃ : (α₂ ≫ ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).map
      S.g.hom).f n) ≫ ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).obj
        S.X₃.obj).d n (n + 1) = 0)
    (hα₁ : α₁ ≫ ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).obj
      S.X₁.obj).d (n + 1) (n + 1 + 1) = 0)
    (hα : α₁ ≫ ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU).map
      S.f.hom).f (n + 1) = α₂ ≫ ((Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U
        hU).obj S.X₂.obj).d n (n + 1)) :
    cocycleClass (n + 1) α₁ hα₁ ≫ cechClass O U hU S.X₁ (n + 1) =
      cocycleClass n _ hα₃ ≫ cechClass O U hU S.X₃ n ≫ boundary O S hS n (n + 1) rfl := by
  obtain ⟨SI, φ, hSI, hinj₁, hinj₃, hq⟩ := exists_shortExact_injective_hom O S hS
  let T := Stacks.Cech.Linear.totalCechComplexFunctor X (ringSheaf O) ⊤ U hU
  have hC := shortExact_totalCech_of_injective O U hU SI hSI hinj₁
  have key := cechClass_boundary_of_injective O U hU SI hSI hinj₁ hinj₃ n
  have : IsIso ((Stacks.Cech.Linear.derivedSectionsFunctor X (ringSheaf O) ⊤).map φ.τ₁) :=
    Stacks.Cech.Linear.derivedSectionsFunctor_map_isIso X (ringSheaf O) ⊤ φ.τ₁
  have hiso : IsIso (hypercohomologyMap O φ.τ₁ (n + 1)) :=
    Functor.map_isIso (DerivedCategory.homologyFunctor _ (n + 1)) _
  have hx₂ : (α₂ ≫ (T.map φ.τ₂.hom).f n) ≫ (T.map SI.g.hom).f n =
      (α₂ ≫ (T.map S.g.hom).f n) ≫ (T.map φ.τ₃.hom).f n := by
    rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f,
      ← T.map_comp, ← T.map_comp]
    exact congrArg (fun z => α₂ ≫ (T.map z).f n) (congrArg (fun z => z.hom) φ.comm₂₃)
  have hx₁ : (α₁ ≫ (T.map φ.τ₁.hom).f (n + 1)) ≫ (T.map SI.f.hom).f (n + 1) =
      (α₂ ≫ (T.map φ.τ₂.hom).f n) ≫ (T.obj SI.X₂.obj).d n (n + 1) := by
    rw [Category.assoc, ← HomologicalComplex.comp_f, ← T.map_comp,
      show φ.τ₁.hom ≫ SI.f.hom = S.f.hom ≫ φ.τ₂.hom from congrArg (fun z => z.hom) φ.comm₁₂,
      T.map_comp, HomologicalComplex.comp_f, ← Category.assoc, hα, Category.assoc, Category.assoc,
      (T.map φ.τ₂.hom).comm]
  have hx₃ : ((α₂ ≫ (T.map S.g.hom).f n) ≫ (T.map φ.τ₃.hom).f n) ≫
      (T.obj SI.X₃.obj).d n (n + 1) = 0 := by
    rw [Category.assoc, (T.map φ.τ₃.hom).comm, ← Category.assoc, hα₃, zero_comp]
  have hsnake : cocycleClass (n + 1) (α₁ ≫ (T.map φ.τ₁.hom).f (n + 1))
      (by rw [Category.assoc, (T.map φ.τ₁.hom).comm, ← Category.assoc, hα₁, zero_comp]) =
      cocycleClass n _ hx₃ ≫ hC.δ n (n + 1) rfl :=
    Stacks.CupProduct.liftCycles_homologyπ_eq_δ hC n _ hx₃ _ hx₂ _ hx₁
  rw [← cancel_mono (hypercohomologyMap O φ.τ₁ (n + 1))]
  calc (cocycleClass (n + 1) α₁ hα₁ ≫ cechClass O U hU S.X₁ (n + 1)) ≫
        hypercohomologyMap O φ.τ₁ (n + 1)
      = cocycleClass (n + 1) α₁ hα₁ ≫ HomologicalComplex.homologyMap (T.map φ.τ₁.hom) (n + 1) ≫
          cechClass O U hU SI.X₁ (n + 1) := by rw [Category.assoc, cechClass_naturality]
    _ = cocycleClass n _ hx₃ ≫ hC.δ n (n + 1) rfl ≫ cechClass O U hU SI.X₁ (n + 1) := by
          rw [cocycleClass_comp_homologyMap_assoc, hsnake, Category.assoc]
    _ = cocycleClass n _ hx₃ ≫ cechClass O U hU SI.X₃ n ≫ boundary O SI hSI n (n + 1) rfl := by
          rw [key]
    _ = cocycleClass n _ hα₃ ≫ HomologicalComplex.homologyMap (T.map φ.τ₃.hom) n ≫
          cechClass O U hU SI.X₃ n ≫ boundary O SI hSI n (n + 1) rfl := by
          rw [cocycleClass_comp_homologyMap_assoc]
    _ = cocycleClass n _ hα₃ ≫ cechClass O U hU S.X₃ n ≫ hypercohomologyMap O φ.τ₃ n ≫
          boundary O SI hSI n (n + 1) rfl := by
          rw [cechClass_naturality_assoc]
    _ = (cocycleClass n _ hα₃ ≫ cechClass O U hU S.X₃ n ≫ boundary O S hS n (n + 1) rfl) ≫
          hypercohomologyMap O φ.τ₁ (n + 1) := by
          rw [← boundary_naturality O hS hSI φ]
          simp only [Category.assoc]

end Cech

end Stacks.Cech.Hypercohomology
