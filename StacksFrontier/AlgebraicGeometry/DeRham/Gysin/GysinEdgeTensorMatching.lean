module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.HodgeCohomologyModuleBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ConormalWedgeProjectionRank
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinHodgeConormal
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinWedgeTopDegree
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.Bilinear
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgeHomology
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEdgePullback
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.ConormalWedgeExtension

/-!
# The wedge pairing of Tag 0G88 across the Gysin edge morphisms

(statement file; proof to be supplied)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.SupportedComplexes
open Stacks.DeRham.CohomologicalGysin
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.GlobalKunneth (baseSections baseRing)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open AlgebraicGeometry.SheafOfModules (moduleDerived canonicalPairingModule tensorBifunctorNat
  baseRingedSpace multiplicationInt)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.DeRham.GysinCupHodge

open _root_.Stacks.DerivedCategory _root_.CategoryTheory.DerivedCategory

/-- The algebra of `singleNatHomologyIso_inv_formsGysinEdgeFront`, at variables. -/
private lemma iota_chase {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D) {M' L' : D}
    {P S₁ S₂ R : C} (i₁ : M' ⟶ H.obj S₁) (m : P ≅ S₁) (s : S₁ ⟶ S₂) (fr : S₂ ⟶ R)
    (i₂ : L' ⟶ H.obj S₂) (φ : M' ⟶ L') (ψ : L' ⟶ H.obj R)
    (hn : φ ≫ i₂ = i₁ ≫ H.map s) (hf : i₂ ≫ H.map fr = ψ) :
    (i₁ ≫ H.map m.inv) ≫ H.map (m.hom ≫ s ≫ fr) = φ ≫ ψ := by
  rw [H.map_comp, H.map_comp, Category.assoc, ← Category.assoc (H.map m.inv), ← H.map_comp,
    Iso.inv_hom_id, H.map_id, Category.id_comp, ← Category.assoc, ← hn, Category.assoc, hf]

/-- The algebra of `edgeTensorMatching_conormalWedge`, at variables. -/
private lemma final_chase {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D) {P T₀ T₁ T₂ R : C}
    {A B : D} (e : H.obj P ≅ A) (μ : A ⟶ B) (s : H.obj T₁ ≅ B) (L : P ⟶ R) (t : P ⟶ T₀)
    (m : T₀ ⟶ T₁) (n₁ : T₁ ⟶ T₂) (n₂ : T₂ ⟶ R) (j : B ⟶ H.obj R)
    (hcore : e.inv ≫ H.map L = μ ≫ j)
    (hread : H.map (t ≫ m) ≫ s.hom = e.hom ≫ μ) (hiota : s.inv ≫ H.map (n₁ ≫ n₂) = j) :
    H.map L = H.map (t ≫ m ≫ n₁ ≫ n₂) := by
  have h₁ : H.map L = e.hom ≫ μ ≫ j := by rw [← hcore, Iso.hom_inv_id_assoc]
  have h₂ : H.map (t ≫ m) = (e.hom ≫ μ) ≫ s.inv := by rw [← hread, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [h₁, ← hiota, ← Category.assoc t, H.map_comp _ (n₁ ≫ n₂), h₂]
  simp only [Category.assoc]

/-- The algebra of `edgeMulReadOff_naturality_left`, at variables. -/
private lemma readOff_left_chase {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {P P' R : C} {a a' : D} (rA : H.obj P ≅ a) (rA' : H.obj P' ≅ a') (φ : a ⟶ a') (t : P ⟶ P')
    (eA' : P' ⟶ R) (eA : P ⟶ R) (hr : H.map t ≫ rA'.hom = rA.hom ≫ φ) (he : t ≫ eA' = eA) :
    φ ≫ rA'.inv ≫ H.map eA' = rA.inv ≫ H.map eA := by
  rw [← he, H.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp, ← Category.assoc, ← hr, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The algebra of `edgeMulReadOff_unit`, at variables. -/
private lemma readOff_unit_chase {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {P M R : C} {a b : D} (rd : H.obj P ≅ a) (s : H.obj M ≅ b) (lam : P ⟶ M) (l : a ⟶ b)
    (k : M ⟶ R) (hlam : H.map lam ≫ s.hom = rd.hom ≫ l) :
    rd.inv ≫ H.map (lam ≫ k) = l ≫ s.inv ≫ H.map k := by
  rw [H.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, ← hlam, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The algebra of the core read-off, at variables. -/
private lemma assoc_cancel_chase {C : Type*} [Category* C] {P Q R Q' S : C} (a : P ⟶ Q)
    (b : Q ⟶ R) (c : R ⟶ Q') (d : Q' ⟶ S) (e : Q ⟶ Q') (h : b ≫ c = e) :
    (a ≫ b ≫ c) ≫ d = a ≫ e ≫ d := by
  rw [← h]; simp only [Category.assoc]

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules
  AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

section Geometric

open AlgebraicGeometry.Scheme.Hom Stacks.Gysin
open Stacks.AlgebraicGeometry.ConormalEquations (ConormalRank)
open Stacks.Perfect.SupportedFraction (supportCohomologySheafFunctor)

variable {Z X S : Scheme.{u}}

/-- The Gysin edge morphism at `Ω^n_{X/S}`, with its source in the spelling of the target of the
Gysin map of Tag 0G86. -/
def formsGysinEdge (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c : ℕ) (n : ℤ)
    (hvan : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π n)))) :
    (DerivedCategory.singleFunctor X.Modules (c : ℤ)).obj
        ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
          (relativeDifferentialForms π n)) ⟶
      (DerivedCategory.singleFunctor X.Modules ((0 : ℕ) : ℤ)).obj (relativeDifferentialForms π n) :=
  (DerivedCategory.singleFunctor X.Modules (c : ℤ)).map
      ((Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso (isClosed_range_base i)
        (c : ℤ)).app (relativeDifferentialForms π n)).hom ≫
    supportedGysinEdge (Set.range i.base) i.isClosedEmbedding.isClosed_range (c : ℤ)
      ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj (relativeDifferentialForms π n)) hvan

open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)

/-- The front half of `formsGysinEdge`: the identification of the two spellings of `i_*ℋ^c_Z`,
followed by the canonical map `i_*ℋ^c_Z(Ω^n)[-c] ⟶ i_*Rℋ_Z(Ω^n)`. -/
def formsGysinEdgeFront (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c : ℕ) (n : ℤ)
    (hvan : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π n)))) :
    (DerivedCategory.singleFunctor X.Modules (c : ℤ)).obj
        ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
          (relativeDifferentialForms π n)) ⟶
      (derivedSupportedPushforward X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range).obj
        ((DerivedCategory.singleFunctor X.Modules ((0 : ℕ) : ℤ)).obj
          (relativeDifferentialForms π n)) :=
  (DerivedCategory.singleFunctor X.Modules (c : ℤ)).map
      ((Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso (isClosed_range_base i)
        (c : ℤ)).app (relativeDifferentialForms π n)).hom ≫
    Stacks.DeRham.GysinCohomologyBaseChange.supportedGysinEdgeFront (Set.range i.base)
      i.isClosedEmbedding.isClosed_range (c : ℤ)
      ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj (relativeDifferentialForms π n)) hvan

/-- The Gysin edge morphism is its front followed by the canonical map of Tag 0G72. -/
theorem formsGysinEdge_eq (i : Z ⟶ X) [IsClosedImmersion i] (π : X ⟶ S) (c : ℕ) (n : ℤ)
    (hvan : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π n)))) :
    letI := pushforward_preservesFiniteLimits X.toRingedSpace (Set.range i.base)
    letI := pushforward_preservesFiniteColimits X.toRingedSpace (Set.range i.base)
      i.isClosedEmbedding.isClosed_range
    formsGysinEdge i π c n hvan = formsGysinEdgeFront i π c n hvan ≫
      (derivedPushforwardAdjunction X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range).counit.app _ := by
  unfold formsGysinEdge formsGysinEdgeFront
  rw [Stacks.DeRham.GysinCohomologyBaseChange.supportedGysinEdge_eq]
  exact (Category.assoc _ _ _).symm

/-- **The front of the Gysin edge morphism reads off as the identity in degree `c`.** -/
theorem singleNatHomologyIso_inv_formsGysinEdgeFront (i : Z ⟶ X) [IsClosedImmersion i]
    (π : X ⟶ S) (c : ℕ) (n : ℤ)
    (hvan : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π n)))) :
    (singleNatHomologyIso (X := X.toRingedSpace) _ c).inv ≫
      (DerivedCategory.homologyFunctor _ (c : ℤ)).map
        ((moduleDerivedSingleIso _ c).hom ≫ formsGysinEdgeFront i π c n hvan) = 𝟙 _ := by
  let := pushforward_preservesFiniteLimits X.toRingedSpace (Set.range i.base)
  let := pushforward_preservesFiniteColimits X.toRingedSpace (Set.range i.base)
    i.isClosedEmbedding.isClosed_range
  have hf := Stacks.DeRham.GysinCohomologyBaseChange.supportedGysinEdgeFrontHomology_eq
    (Set.range i.base) i.isClosedEmbedding.isClosed_range (c : ℤ)
    ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj (relativeDifferentialForms π n)) hvan
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (c : ℤ)).inv.naturality
    ((Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso (isClosed_range_base i)
      (c : ℤ)).app (relativeDifferentialForms π n)).hom
  simp only [Functor.id_map, Functor.comp_map] at hn
  unfold Stacks.DeRham.GysinCohomologyBaseChange.supportedGysinEdgeFrontHomology at hf
  exact (iota_chase (DerivedCategory.homologyFunctor X.Modules (c : ℤ)) _ _ _ _ _ _ _ hn hf).trans
    (Iso.hom_inv_id_app _ _)

section ReadOff

variable {Y : RingedSpace.{u, u}} (T : Set Y.carrier) (hT : IsClosed T) (c : ℕ)

/-- **The degree-`c` read-off of the edge map of Tag 0G75 along a multiplication `w`.** -/
def edgeMulReadOff
    {A L N G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)}
    (w : ((sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj L ⟶ N)
    (sL : (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y))
        (c : ℤ)).obj G ⟶
      (derivedSupportedPushforward Y T hT).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y))
          ((0 : ℕ) : ℤ)).obj L)) :
    ((sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj G ⟶
      (DerivedCategory.homologyFunctor _ (c : ℤ)).obj ((derivedSupportedPushforward Y T hT).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y))
          ((0 : ℕ) : ℤ)).obj N)) :=
  (@asIso _ _ _ _ (edgeReadOff A G c) (isIso_edgeReadOff A G c)).inv ≫
    (DerivedCategory.homologyFunctor _ (c : ℤ)).map (edgeMatchingLeft T hT c w sL)

/-- The read-off is natural in the target of the multiplication. -/
theorem edgeMulReadOff_comp
    {A L N N' G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)}
    (w : ((sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj L ⟶ N) (g : N ⟶ N')
    (sL : (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y))
        (c : ℤ)).obj G ⟶
      (derivedSupportedPushforward Y T hT).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y))
          ((0 : ℕ) : ℤ)).obj L)) :
    edgeMulReadOff T hT c (w ≫ g) sL = edgeMulReadOff T hT c w sL ≫
      (DerivedCategory.homologyFunctor _ (c : ℤ)).map ((derivedSupportedPushforward Y T hT).map
        ((DerivedCategory.singleFunctor _ ((0 : ℕ) : ℤ)).map g)) := by
  unfold edgeMulReadOff
  rw [edgeMatchingLeft_comp, Functor.map_comp, Category.assoc]

/-- The read-off is natural in the left factor. -/
theorem edgeMulReadOff_naturality_left
    {A A' L N G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)} (f : A ⟶ A')
    (w : ((sheafTensor.{u, u, u, u, u} Y.sheaf).obj A').obj L ⟶ N)
    (sL : (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y))
        (c : ℤ)).obj G ⟶
      (derivedSupportedPushforward Y T hT).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y))
          ((0 : ℕ) : ℤ)).obj L)) :
    ((sheafTensor.{u, u, u, u, u} Y.sheaf).map f).app G ≫ edgeMulReadOff T hT c w sL =
      edgeMulReadOff T hT c (((sheafTensor.{u, u, u, u, u} Y.sheaf).map f).app L ≫ w) sL := by
  unfold edgeMulReadOff
  exact readOff_left_chase _ _ _ _ _ _ _ (edgeReadOff_naturality f c)
    (edgeMatchingLeft_naturality_left T hT c f w sL)

/-- **The read-off with `𝒪` on the left, along the left unitor.** -/
theorem edgeMulReadOff_unit
    {L G : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.sheaf)}
    (sL : (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y))
        (c : ℤ)).obj G ⟶
      (derivedSupportedPushforward Y T hT).obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y))
          ((0 : ℕ) : ℤ)).obj L))
    (W : DerivedCategory (_root_.SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace Y T))))
    (e : letI := pushforward_preservesFiniteLimits Y T
      letI := pushforward_preservesFiniteColimits Y T hT
      (modulePushforward (closedSubsetInclusion Y T)).mapDerivedCategory.obj W ≅
        (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (structureSheafRing Y))
          (c : ℤ)).obj G) :
    edgeMulReadOff T hT c (sheafLeftUnitor L).hom sL =
      (sheafLeftUnitor G).hom ≫ (singleNatHomologyIso G c).inv ≫
        (DerivedCategory.homologyFunctor _ (c : ℤ)).map
          ((moduleDerivedSingleIso G c).hom ≫ sL) := by
  unfold edgeMulReadOff
  rw [edgeMatchingLeft_unit T hT c sL W e]
  have hlam := (congrArg (fun t => (DerivedCategory.homologyFunctor _ (c : ℤ)).map t ≫
      (singleNatHomologyIso G c).hom)
    ((derivedLeftUnitor_app_Q (X := Y) ((singleNat G c).extend ComplexShape.embeddingUpNat)).trans
      (congrArg (fun t => _ ≫ DerivedCategory.Q.map t)
        (multiplicationInt_singleTensorMult_leftUnitor G c).symm))).trans
    (homologyMap_toTensor_singleTensorMult (sheafLeftUnitor G).hom c)
  exact readOff_unit_chase _ _ _ _ _ _ hlam

end ReadOff

/-- **(core) The degree-`c` read-off of the multiplication of Tag 0G75 at the wedge of forms is the
wedge pairing of Tag 0G88.** -/
theorem edgeReadOff_inv_edgeMatchingLeft (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) [Smooth π] {c : ℕ} (_hE : ConormalRank i c)
    (p : ℕ)
    (hvanL : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π (c : ℤ))))) :
    (@asIso _ _ _ _ (edgeReadOff (X := X.toRingedSpace) (relativeDifferentialForms π (p : ℤ))
        ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
          (relativeDifferentialForms π (c : ℤ))) c) (isIso_edgeReadOff _ _ c)).inv ≫
      (DerivedCategory.homologyFunctor _ (c : ℤ)).map
        (edgeMatchingLeft (Set.range i.base) i.isClosedEmbedding.isClosed_range c
          (SheafOfModules.GradedAlgebra.mulSheaf (relativeDifferentialFormsAlgebra π) (p : ℤ)
            (c : ℤ)) (formsGysinEdgeFront i π c (c : ℤ) hvanL)) =
      Stacks.RingedSpace.ofBilinearSheaf (conormalWedgePair i π c p) := by
  let := pushforward_preservesFiniteLimits X.toRingedSpace (Set.range i.base)
  let := pushforward_preservesFiniteColimits X.toRingedSpace (Set.range i.base)
    i.isClosedEmbedding.isClosed_range
  show edgeMulReadOff (Set.range i.base) i.isClosedEmbedding.isClosed_range c _ _ = _
  -- the unit law for the source of the edge
  have hunit := fun (L : X.Modules) (sL' : (DerivedCategory.singleFunctor X.Modules (c : ℤ)).obj
      ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
        (relativeDifferentialForms π (c : ℤ))) ⟶
      (derivedSupportedPushforward X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range).obj
        ((DerivedCategory.singleFunctor X.Modules ((0 : ℕ) : ℤ)).obj L)) =>
    edgeMulReadOff_unit (Y := X.toRingedSpace) (Set.range i.base)
      i.isClosedEmbedding.isClosed_range c (L := L) sL'
      ((DerivedCategory.singleFunctor _ (c : ℤ)).obj
        (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
          i.isClosedEmbedding.isClosed_range (c : ℤ)
          ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj (relativeDifferentialForms π (c : ℤ)))))
      (((modulePushforward (closedSubsetInclusion X.toRingedSpace
          (Set.range i.base))).mapDerivedCategorySingleFunctor (c : ℤ)).app _ ≪≫
        (DerivedCategory.singleFunctor _ (c : ℤ)).mapIso
          ((Stacks.Perfect.GysinLocalCohomology.supportCohomologySheafFunctorIso
            (isClosed_range_base i) (c : ℤ)).app (relativeDifferentialForms π (c : ℤ))).symm)
  have hiota := singleNatHomologyIso_inv_formsGysinEdgeFront i π c (c : ℤ) hvanL
  -- (B) on the section given by a form over an open
  have hB : ∀ (V : X.Opens) (ω : Γ(relativeDifferentialForms π (p : ℤ), V)),
      ((sheafTensor.{u, u, u, u, u} X.sheaf).map (extendedSectionHom π p V ω)).app
          ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
            (relativeDifferentialForms π (c : ℤ))) ≫
        edgeMulReadOff (Set.range i.base) i.isClosedEmbedding.isClosed_range c
          (Stacks.RingedSpace.ofBilinearSheaf (extendedFormWedgePair π c p V))
          (formsGysinEdgeFront i π c (c : ℤ) hvanL) =
      (sheafLeftUnitor _).hom ≫ (supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map
        (localFormWedgeExt π p V ω) := by
    intro V ω
    refine (edgeMulReadOff_naturality_left (Y := X.toRingedSpace) _ _ c
      (extendedSectionHom π p V ω) _ _).trans ?_
    refine (congrArg (fun t => edgeMulReadOff (Y := X.toRingedSpace) (Set.range i.base)
      i.isClosedEmbedding.isClosed_range c t (formsGysinEdgeFront i π c (c : ℤ) hvanL))
      (extendedSectionHom_tensor_extendedFormWedge π c p V ω)).trans ?_
    refine (edgeMulReadOff_comp (Y := X.toRingedSpace) _ _ c _ _ _).trans ?_
    refine (congrArg (· ≫ _) (hunit _ (formsGysinEdgeFront i π c (c : ℤ) hvanL))).trans ?_
    exact (assoc_cancel_chase _ _ _ _ _ hiota).trans (congrArg (_ ≫ ·) (Category.id_comp _))
  -- (A) the read-off followed by the unit of an open
  have hA : ∀ V : X.Opens,
      edgeMulReadOff (Set.range i.base) i.isClosedEmbedding.isClosed_range c
          (SheafOfModules.GradedAlgebra.mulSheaf (relativeDifferentialFormsAlgebra π) (p : ℤ)
            (c : ℤ)) (formsGysinEdgeFront i π c (c : ℤ) hvanL) ≫
        (supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map
          (openUnit V (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))) =
      ((sheafTensor.{u, u, u, u, u} X.sheaf).map
          (openUnit V (relativeDifferentialForms π (p : ℤ)))).app
          ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
            (relativeDifferentialForms π (c : ℤ))) ≫
        edgeMulReadOff (Set.range i.base) i.isClosedEmbedding.isClosed_range c
          (Stacks.RingedSpace.ofBilinearSheaf (extendedFormWedgePair π c p V))
          (formsGysinEdgeFront i π c (c : ℤ) hvanL) := by
    intro V
    refine (edgeMulReadOff_comp (Y := X.toRingedSpace) _ _ c _ _ _).symm.trans ?_
    refine (congrArg (fun t => edgeMulReadOff (Y := X.toRingedSpace) (Set.range i.base)
      i.isClosedEmbedding.isClosed_range c t (formsGysinEdgeFront i π c (c : ℤ) hvanL))
      (openUnit_tensor_extendedFormWedge π c p V).symm).trans ?_
    exact (edgeMulReadOff_naturality_left (Y := X.toRingedSpace) _ _ c _ _ _).symm
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := X.sheaf)
    (F := relativeDifferentialForms π (p : ℤ))
    (G := (supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
      (relativeDifferentialForms π (c : ℤ))) fun U ω t => ?_
  have := isIso_restrictFunctor_map_supportCohomology_openUnit U.unop (isClosed_range_base i)
    (isClosed_preimage_range_base i U.unop) (c : ℤ)
    (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))
  refine app_injective_of_isIso_restrictFunctor_map U.unop
    ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map
      (openUnit U.unop (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))) ?_
  have e₁ := congrArg (fun φ => φ.val.app U ((PresheafOfModules.tensorSheafUnit
    (relativeDifferentialForms π (p : ℤ)) ((supportCohomologySheafFunctor (isClosed_range_base i)
      (c : ℤ)).obj (relativeDifferentialForms π (c : ℤ)))).app U (ω ⊗ₜ t))) (hA U.unop)
  let one : (unitModule X.toRingedSpace).val.obj U :=
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf).obj.obj U)
  have e₂ := sheafTensor_map_app_tensorSheafUnit
    (openUnit U.unop (relativeDifferentialForms π (p : ℤ))) U ω t
  have e₃ : (openUnit U.unop (relativeDifferentialForms π (p : ℤ))).val.app U ω =
      (extendedSectionHom π p U.unop ω).val.app U one :=
    (one_smul _ _).symm.trans (extendedSectionHom_app π p U.unop ω U.unop one).symm
  have e₄ := sheafTensor_map_app_tensorSheafUnit (extendedSectionHom π p U.unop ω) U one t
  have e₅ := congrArg (fun φ => φ.val.app U ((PresheafOfModules.tensorSheafUnit
    (unitModule X.toRingedSpace) ((supportCohomologySheafFunctor (isClosed_range_base i)
      (c : ℤ)).obj (relativeDifferentialForms π (c : ℤ)))).app U (one ⊗ₜ t))) (hB U.unop ω)
  have e₆ := sheafLeftUnitor_hom_apply (X := X.toRingedSpace)
    ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
      (relativeDifferentialForms π (c : ℤ))) U one t
  have e₇ := Stacks.RingedSpace.ofBilinearSheaf_unit_tmul (Y := X.toRingedSpace)
    (conormalWedgePair i π c p) U ω t
  have e₈ := conormalWedgePair_app i π c p U.unop ω t
  have e₉ := supportCohomology_localFormWedgeExt_app i π p U.unop ω U.unop le_rfl t
  refine e₁.trans ?_
  refine (congrArg (fun a => (edgeMulReadOff (Y := X.toRingedSpace) (Set.range i.base)
      i.isClosedEmbedding.isClosed_range c
      (Stacks.RingedSpace.ofBilinearSheaf (extendedFormWedgePair π c p U.unop))
      (formsGysinEdgeFront i π c (c : ℤ) hvanL)).val.app U a)
    ((e₂.trans (congrArg (fun a => (PresheafOfModules.tensorSheafUnit
      ((Scheme.Modules.pushforward (Scheme.Opens.ι U.unop)).obj
        ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι U.unop)).obj
          (relativeDifferentialForms π (p : ℤ))))
      ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
        (relativeDifferentialForms π (c : ℤ)))).app U (a ⊗ₜ t)) e₃)).trans e₄.symm)).trans ?_
  refine e₅.trans ?_
  refine (congrArg (fun a => ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map
    (localFormWedgeExt π p U.unop ω)).val.app U a) (e₆.trans (one_smul _ t))).trans ?_
  refine e₉.trans ?_
  exact congrArg (fun a => ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).map
    (openUnit U.unop (relativeDifferentialForms π ((p : ℤ) + (c : ℤ))))).app U.unop a)
    (e₈.symm.trans e₇.symm)

/-- **(D4) The wedge pairing of Tag 0G88 matches the wedge of forms across the Gysin edge
morphisms** (Cohomology, Remark 0G76 and Lemma 0G77 for the Gysin class). -/
theorem edgeTensorMatching_conormalWedge (i : Z ⟶ X) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] (π : X ⟶ S) [Smooth π] {c : ℕ} (hE : ConormalRank i c)
    (p : ℕ)
    (hvanL : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π (c : ℤ)))))
    (hvanM : ∀ j : ℤ, j < (c : ℤ) →
      IsZero (localCohomologySheafOfComplex X.toRingedSpace (Set.range i.base)
        i.isClosedEmbedding.isClosed_range j ((DerivedCategory.singleFunctor _ (0 : ℤ)).obj
          (relativeDifferentialForms π ((p : ℤ) + (c : ℤ)))))) :
    EdgeTensorMatching (X := X.toRingedSpace) c
      (SheafOfModules.GradedAlgebra.mulSheaf (relativeDifferentialFormsAlgebra π) (p : ℤ) (c : ℤ))
      (Stacks.RingedSpace.ofBilinearSheaf (conormalWedgePair i π c p))
      (formsGysinEdge i π c (c : ℤ) hvanL) (formsGysinEdge i π c ((p : ℤ) + (c : ℤ)) hvanM) := by
  let := pushforward_preservesFiniteLimits X.toRingedSpace (Set.range i.base)
  let := pushforward_preservesFiniteColimits X.toRingedSpace (Set.range i.base)
    i.isClosedEmbedding.isClosed_range
  rw [formsGysinEdge_eq, formsGysinEdge_eq]
  refine edgeTensorMatching_of_eq (X := X.toRingedSpace) (Set.range i.base)
    i.isClosedEmbedding.isClosed_range c _ _ _ _ ?_
  have h₀ := isLE_moduleDerived_singleNat (X := X.toRingedSpace)
    (relativeDifferentialForms π (p : ℤ)) 0
  have h₁ := isLE_moduleDerived_singleNat (X := X.toRingedSpace)
    ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
      (relativeDifferentialForms π (c : ℤ))) c
  have hle := Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor X.sheaf
    (moduleDerived (A := X.sheaf) (singleNat (X := X.toRingedSpace)
      (relativeDifferentialForms π (p : ℤ)) 0))
    (moduleDerived (A := X.sheaf) (singleNat (X := X.toRingedSpace)
      ((supportCohomologySheafFunctor (isClosed_range_base i) (c : ℤ)).obj
        (relativeDifferentialForms π (c : ℤ))) c)) 0 (c : ℤ)
  rw [zero_add] at hle
  have hge := Stacks.DeRham.GysinCohomologyBaseChange.isGE_derivedSupportedPushforward
    (Set.range i.base) i.isClosedEmbedding.isClosed_range (c : ℤ) _ hvanM
  refine DerivedCategory.eq_of_isLE_of_isGE_of_homologyFunctor_map_eq (c : ℤ) _ _ ?_
  have hcore := edgeReadOff_inv_edgeMatchingLeft i π hE p hvanL
  have hread := homologyMap_toTensor_singleTensorMult (X := X.toRingedSpace)
    (Stacks.RingedSpace.ofBilinearSheaf (conormalWedgePair i π c p)) c
  have hiota := singleNatHomologyIso_inv_formsGysinEdgeFront i π c ((p : ℤ) + (c : ℤ)) hvanM
  dsimp only [edgeMatchingRight]
  exact final_chase _ _ _ _ _ _ _ _ _ _ ((hcore.trans (Category.comp_id _).symm)) hread hiota



end Geometric

end StandardModel

end Stacks.DeRham.GysinCupHodge
