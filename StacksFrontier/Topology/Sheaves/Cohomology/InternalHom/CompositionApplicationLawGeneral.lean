module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.CompositionApplicationLaw
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionConstruction

/-!
# Applying a composite is applying the factors in turn

Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be objects of `D(O_X)`.  For the
composition morphism `cmp : RSheafHom(L, M) ⊗^L RSheafHom(K, L) ⟶ RSheafHom(K, M)` of
Stacks 0A8V and the application morphisms `ε` of Stacks 08J8,

`(cmp ⊗ 1_K) ≫ ε_{K,M} = α ≫ (1 ⊗ ε_{K,L}) ≫ ε_{L,M}`.

On K-injective models of `L` and `M` this is
`Stacks.SheafOfModules.derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_model`;
both sides are natural in `K` and `M` and dinatural in `L`, so the identity is carried to
arbitrary objects along the model isomorphisms.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_space`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

section Abstract

variable {C : Type*} [Category C] (F : C ⥤ C ⥤ C)

/-- Transport of the composition law along an isomorphism of the target object. -/
private lemma transport_target {HLM HLM' HKL HKM HKM' K L M M' : C}
    (comp : (F.obj HLM).obj HKL ⟶ HKM) (comp' : (F.obj HLM').obj HKL ⟶ HKM')
    (εKM : (F.obj HKM).obj K ⟶ M) (εKM' : (F.obj HKM').obj K ⟶ M') (εKL : (F.obj HKL).obj K ⟶ L)
    (εLM : (F.obj HLM).obj L ⟶ M) (εLM' : (F.obj HLM').obj L ⟶ M')
    (α : (F.obj ((F.obj HLM).obj HKL)).obj K ⟶ (F.obj HLM).obj ((F.obj HKL).obj K))
    (α' : (F.obj ((F.obj HLM').obj HKL)).obj K ⟶ (F.obj HLM').obj ((F.obj HKL).obj K))
    (m : M ⟶ M') (mK : HKM ⟶ HKM') (mL : HLM ⟶ HLM') [IsIso mL]
    (hcomp : comp ≫ mK = (F.map mL).app HKL ≫ comp')
    (hεK : (F.map mK).app K ≫ εKM' = εKM ≫ m) (hεL : (F.map mL).app L ≫ εLM' = εLM ≫ m)
    (hα : (F.map ((F.map mL).app HKL)).app K ≫ α' = α ≫ (F.map mL).app ((F.obj HKL).obj K))
    (h : (F.map comp).app K ≫ εKM = α ≫ (F.obj HLM).map εKL ≫ εLM) :
    (F.map comp').app K ≫ εKM' = α' ≫ (F.obj HLM').map εKL ≫ εLM' := by
  rw [← cancel_epi ((F.map ((F.map mL).app HKL)).app K)]
  rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, ← hcomp, Functor.map_comp,
    NatTrans.comp_app, Category.assoc, hεK, reassoc_of% h, reassoc_of% hα,
    ← NatTrans.naturality_assoc, hεL]

/-- Transport of the composition law along an isomorphism of the intermediate object. -/
private lemma transport_middle {HLM HL'M HKL HKL' HKM K L L' M : C}
    (comp : (F.obj HLM).obj HKL ⟶ HKM) (comp' : (F.obj HL'M).obj HKL' ⟶ HKM)
    (εKM : (F.obj HKM).obj K ⟶ M) (εKL : (F.obj HKL).obj K ⟶ L) (εKL' : (F.obj HKL').obj K ⟶ L')
    (εLM : (F.obj HLM).obj L ⟶ M) (εL'M : (F.obj HL'M).obj L' ⟶ M)
    (α : (F.obj ((F.obj HLM).obj HKL)).obj K ⟶ (F.obj HLM).obj ((F.obj HKL).obj K))
    (αm : (F.obj ((F.obj HL'M).obj HKL)).obj K ⟶ (F.obj HL'M).obj ((F.obj HKL).obj K))
    (α' : (F.obj ((F.obj HL'M).obj HKL')).obj K ⟶ (F.obj HL'M).obj ((F.obj HKL').obj K))
    (l : L ⟶ L') (lK : HKL ⟶ HKL') (lM : HL'M ⟶ HLM) [IsIso lK]
    (hcomp : (F.obj HL'M).map lK ≫ comp' = (F.map lM).app HKL ≫ comp)
    (hεK : (F.map lK).app K ≫ εKL' = εKL ≫ l)
    (hεM : (F.obj HL'M).map l ≫ εL'M = (F.map lM).app L ≫ εLM)
    (hα₁ : (F.map ((F.map lM).app HKL)).app K ≫ α = αm ≫ (F.map lM).app ((F.obj HKL).obj K))
    (hα₂ : (F.map ((F.obj HL'M).map lK)).app K ≫ α' = αm ≫ (F.obj HL'M).map ((F.map lK).app K))
    (h : (F.map comp).app K ≫ εKM = α ≫ (F.obj HLM).map εKL ≫ εLM) :
    (F.map comp').app K ≫ εKM = α' ≫ (F.obj HL'M).map εKL' ≫ εL'M := by
  rw [← cancel_epi ((F.map ((F.obj HL'M).map lK)).app K)]
  rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, hcomp, Functor.map_comp,
    NatTrans.comp_app, Category.assoc, h, reassoc_of% hα₁, reassoc_of% hα₂,
    ← Functor.map_comp_assoc, hεK, Functor.map_comp_assoc, hεM, NatTrans.naturality_assoc]

/-- Transport of the composition law along an isomorphism of the source object. -/
private lemma transport_source {HLM HKL HK'L HKM HK'M K K' L M : C}
    (comp : (F.obj HLM).obj HKL ⟶ HKM) (comp' : (F.obj HLM).obj HK'L ⟶ HK'M)
    (εKM : (F.obj HKM).obj K ⟶ M) (εK'M : (F.obj HK'M).obj K' ⟶ M)
    (εKL : (F.obj HKL).obj K ⟶ L) (εK'L : (F.obj HK'L).obj K' ⟶ L)
    (εLM : (F.obj HLM).obj L ⟶ M)
    (α : (F.obj ((F.obj HLM).obj HKL)).obj K ⟶ (F.obj HLM).obj ((F.obj HKL).obj K))
    (αm : (F.obj ((F.obj HLM).obj HKL)).obj K' ⟶ (F.obj HLM).obj ((F.obj HKL).obj K'))
    (α' : (F.obj ((F.obj HLM).obj HK'L)).obj K' ⟶ (F.obj HLM).obj ((F.obj HK'L).obj K'))
    (k : K' ⟶ K) (kM : HKM ⟶ HK'M) (kL : HKL ⟶ HK'L) [IsIso kL] [IsIso k]
    (hcomp : comp ≫ kM = (F.obj HLM).map kL ≫ comp')
    (hεM : (F.obj HKM).map k ≫ εKM = (F.map kM).app K' ≫ εK'M)
    (hεL : (F.obj HKL).map k ≫ εKL = (F.map kL).app K' ≫ εK'L)
    (hα₁ : (F.obj _).map k ≫ α = αm ≫ (F.obj HLM).map ((F.obj HKL).map k))
    (hα₂ : (F.map ((F.obj HLM).map kL)).app K' ≫ α' = αm ≫ (F.obj HLM).map ((F.map kL).app K'))
    (h : (F.map comp).app K ≫ εKM = α ≫ (F.obj HLM).map εKL ≫ εLM) :
    (F.map comp').app K' ≫ εK'M = α' ≫ (F.obj HLM).map εK'L ≫ εLM := by
  rw [← cancel_epi ((F.map ((F.obj HLM).map kL)).app K')]
  rw [← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, ← hcomp, Functor.map_comp,
    NatTrans.comp_app, Category.assoc, ← hεM, ← NatTrans.naturality_assoc, h, reassoc_of% hα₁,
    reassoc_of% hα₂, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hεL]

end Abstract

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **Applying a composite is applying the two factors in turn**, as a proposition: for objects
`K`, `L`, `M` of `D(O_X)`, the composition morphism `cmp` of Stacks 0A8V and the application
morphisms `ε` of Stacks 08J8 satisfy `(cmp ⊗ 1) ≫ ε_{K,M} = α ≫ (1 ⊗ ε_{K,L}) ≫ ε_{L,M}`. -/
def CompositionApplicationLaw (K L M : DerivedCategory (StructureSheafModules Rc)) : Prop :=
  ((derivedTensor Rc).map (derivedSheafHomComposition Rc K L M)).app K ≫
      derivedSheafHomCounit Rc K M =
    derivedAssociatorHom Rc _ _ _ ≫
      ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj M)).map
        (derivedSheafHomCounit Rc K L) ≫ derivedSheafHomCounit Rc L M

/-- **Stacks 08DI, naturality in the target, at a ringed space.** -/
theorem derivedSheafHomTensorEquiv_naturality_target
    (A B : DerivedCategory (StructureSheafModules Rc))
    {Z Z' : DerivedCategory (StructureSheafModules Rc)} (m : Z ⟶ Z')
    (h : A ⟶ ((derivedSheafHom Rc).obj (op B)).obj Z) :
    derivedSheafHomTensorEquiv Rc A B Z' (h ≫ ((derivedSheafHom Rc).obj (op B)).map m) =
      derivedSheafHomTensorEquiv Rc A B Z h ≫ m := by
  rw [derivedSheafHomTensorEquiv_eq Rc A B Z, derivedSheafHomTensorEquiv_eq Rc A B Z',
    RingedSite.derivedCurryHomEquiv_naturality_target (ringedSite Rc) m h]

/-- The application morphism is natural in its target. -/
theorem derivedSheafHomCounit_naturality_target (K : DerivedCategory (StructureSheafModules Rc))
    {M M' : DerivedCategory (StructureSheafModules Rc)} (m : M ⟶ M') :
    ((derivedTensor Rc).map (((derivedSheafHom Rc).obj (op K)).map m)).app K ≫
        derivedSheafHomCounit Rc K M' =
      derivedSheafHomCounit Rc K M ≫ m := by
  rw [Stacks.SheafOfModules.derivedTensor_map_app_comp_derivedSheafHomCounit,
    derivedSheafHomCounit_eq, ← derivedSheafHomTensorEquiv_naturality_target]
  exact congrArg (fun t => derivedSheafHomTensorEquiv Rc _ K M' t) (Category.id_comp _).symm

/-- The application morphism is dinatural in its source. -/
theorem derivedSheafHomCounit_dinaturality_source
    {K K' : DerivedCategory (StructureSheafModules Rc)} (k : K' ⟶ K)
    (M : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op K)).obj M)).map k ≫
        derivedSheafHomCounit Rc K M =
      ((derivedTensor Rc).map (((derivedSheafHom Rc).map k.op).app M)).app K' ≫
        derivedSheafHomCounit Rc K' M := by
  rw [derivedSheafHomCounit_whiskerLeft_eq,
    Stacks.SheafOfModules.derivedTensor_map_app_comp_derivedSheafHomCounit]

/-- The composition morphism of Stacks 0A8V is natural in its target. -/
theorem derivedSheafHomComposition_naturality_target'
    (K L : DerivedCategory (StructureSheafModules Rc))
    {M M' : DerivedCategory (StructureSheafModules Rc)} (m : M ⟶ M') :
    derivedSheafHomComposition Rc K L M ≫ ((derivedSheafHom Rc).obj (op K)).map m =
      ((derivedTensor Rc).map (((derivedSheafHom Rc).obj (op L)).map m)).app
          (((derivedSheafHom Rc).obj (op K)).obj L) ≫
        derivedSheafHomComposition Rc K L M' := by
  have h := derivedSheafHomComposition_natural_target Rc K L m
  simp only [derivedSheafHomMap, derivedTensorMap, RingedSite.derivedSheafHomMap,
    RingedSite.derivedTensorMap, CategoryTheory.Functor.map_id, op_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id] at h
  exact h

/-- The composition morphism of Stacks 0A8V is dinatural in its intermediate object. -/
theorem derivedSheafHomComposition_dinaturality_middle'
    (K : DerivedCategory (StructureSheafModules Rc))
    {L L' : DerivedCategory (StructureSheafModules Rc)} (l : L ⟶ L')
    (M : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L')).obj M)).map
          (((derivedSheafHom Rc).obj (op K)).map l) ≫
        derivedSheafHomComposition Rc K L' M =
      ((derivedTensor Rc).map (((derivedSheafHom Rc).map l.op).app M)).app
          (((derivedSheafHom Rc).obj (op K)).obj L) ≫
        derivedSheafHomComposition Rc K L M := by
  have h := derivedSheafHomComposition_dinatural_middle Rc K l M
  simp only [derivedSheafHomMap, derivedTensorMap, RingedSite.derivedSheafHomMap,
    RingedSite.derivedTensorMap, CategoryTheory.Functor.map_id, op_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id] at h
  exact h

/-- The composition morphism of Stacks 0A8V is natural in its source. -/
theorem derivedSheafHomComposition_naturality_source'
    {K K' : DerivedCategory (StructureSheafModules Rc)} (k : K' ⟶ K)
    (L M : DerivedCategory (StructureSheafModules Rc)) :
    derivedSheafHomComposition Rc K L M ≫ ((derivedSheafHom Rc).map k.op).app M =
      ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj M)).map
          (((derivedSheafHom Rc).map k.op).app L) ≫
        derivedSheafHomComposition Rc K' L M := by
  have h := derivedSheafHomComposition_natural_source Rc k L M
  simp only [derivedSheafHomMap, derivedTensorMap, RingedSite.derivedSheafHomMap,
    RingedSite.derivedTensorMap, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id] at h
  exact h

/-- The associativity constraint of `D(O_X)` is natural in its first variable. -/
theorem derivedAssociatorHom_naturality_first {A A' : DerivedCategory (StructureSheafModules Rc)}
    (a : A' ⟶ A) (B D : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).map (((derivedTensor Rc).map a).app B)).app D ≫
        derivedAssociatorHom Rc A B D =
      derivedAssociatorHom Rc A' B D ≫ ((derivedTensor Rc).map a).app _ := by
  simpa [derivedWhiskerLeft, derivedWhiskerRight] using
    derivedAssociatorHom_naturality Rc a (𝟙 B) (𝟙 D)

/-- The associativity constraint of `D(O_X)` is natural in its second variable. -/
theorem derivedAssociatorHom_naturality_second (A : DerivedCategory (StructureSheafModules Rc))
    {B B' : DerivedCategory (StructureSheafModules Rc)} (b : B' ⟶ B)
    (D : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).map (((derivedTensor Rc).obj A).map b)).app D ≫
        derivedAssociatorHom Rc A B D =
      derivedAssociatorHom Rc A B' D ≫
        ((derivedTensor Rc).obj A).map (((derivedTensor Rc).map b).app D) := by
  simpa [derivedWhiskerLeft, derivedWhiskerRight] using
    derivedAssociatorHom_naturality Rc (𝟙 A) b (𝟙 D)

/-- The associativity constraint of `D(O_X)` is natural in its third variable. -/
theorem derivedAssociatorHom_naturality_third (A B : DerivedCategory (StructureSheafModules Rc))
    {D D' : DerivedCategory (StructureSheafModules Rc)} (d : D' ⟶ D) :
    ((derivedTensor Rc).obj (((derivedTensor Rc).obj A).obj B)).map d ≫
        derivedAssociatorHom Rc A B D =
      derivedAssociatorHom Rc A B D' ≫
        ((derivedTensor Rc).obj A).map (((derivedTensor Rc).obj B).map d) := by
  simpa [derivedWhiskerLeft, derivedWhiskerRight] using
    derivedAssociatorHom_naturality Rc (𝟙 A) (𝟙 B) d

/-- The composition law on K-injective models, as
`Stacks.SheafOfModules.CompositionApplicationLaw`. -/
theorem compositionApplicationLaw_model (P J I : CochainComplex (StructureSheafModules Rc) ℤ)
    [J.IsKInjective] [I.IsKInjective] :
    CompositionApplicationLaw Rc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J)
      (DerivedCategory.Q.obj I) :=
  derivedSheafHomComposition_whiskerRight_comp_derivedSheafHomCounit_model Rc P J I

/-- The composition law is transported along an isomorphism of the target. -/
theorem compositionApplicationLaw_of_iso_target (K L : DerivedCategory (StructureSheafModules Rc))
    {M M' : DerivedCategory (StructureSheafModules Rc)} (m : M ⟶ M') [IsIso m]
    (h : CompositionApplicationLaw Rc K L M) : CompositionApplicationLaw Rc K L M' :=
  transport_target (derivedTensor Rc) _ _ _ _ _ _ _ _ _ m
    (((derivedSheafHom Rc).obj (op K)).map m) (((derivedSheafHom Rc).obj (op L)).map m)
    (derivedSheafHomComposition_naturality_target' Rc K L m)
    (derivedSheafHomCounit_naturality_target Rc K m)
    (derivedSheafHomCounit_naturality_target Rc L m)
    (derivedAssociatorHom_naturality_first Rc _ _ _) h

/-- The composition law is transported along an isomorphism of the intermediate object. -/
theorem compositionApplicationLaw_of_iso_middle (K : DerivedCategory (StructureSheafModules Rc))
    {L L' : DerivedCategory (StructureSheafModules Rc)} (l : L ⟶ L') [IsIso l]
    (M : DerivedCategory (StructureSheafModules Rc))
    (h : CompositionApplicationLaw Rc K L M) : CompositionApplicationLaw Rc K L' M :=
  transport_middle (derivedTensor Rc) _ _ _ _ _ _ _ _ _ _ l
    (((derivedSheafHom Rc).obj (op K)).map l) (((derivedSheafHom Rc).map l.op).app M)
    (derivedSheafHomComposition_dinaturality_middle' Rc K l M)
    (derivedSheafHomCounit_naturality_target Rc K l)
    (derivedSheafHomCounit_dinaturality_source Rc l M)
    (derivedAssociatorHom_naturality_first Rc _ _ _)
    (derivedAssociatorHom_naturality_second Rc _ _ _) h

/-- The composition law is transported along an isomorphism of the source. -/
theorem compositionApplicationLaw_of_iso_source
    {K K' : DerivedCategory (StructureSheafModules Rc)} (k : K' ⟶ K) [IsIso k]
    (L M : DerivedCategory (StructureSheafModules Rc))
    (h : CompositionApplicationLaw Rc K L M) : CompositionApplicationLaw Rc K' L M :=
  transport_source (derivedTensor Rc) _ _ _ _ _ _ _ _ _ _ k
    (((derivedSheafHom Rc).map k.op).app M) (((derivedSheafHom Rc).map k.op).app L)
    (derivedSheafHomComposition_naturality_source' Rc k L M)
    (derivedSheafHomCounit_dinaturality_source Rc k M)
    (derivedSheafHomCounit_dinaturality_source Rc k L)
    (derivedAssociatorHom_naturality_third Rc _ _ _)
    (derivedAssociatorHom_naturality_second Rc _ _ _) h

/-- **Applying a composite is applying the two factors in turn.**  For objects `K`, `L`, `M` of
`D(O_X)`, the composition morphism `cmp` of Stacks 0A8V and the application morphisms `ε` of
Stacks 08J8 satisfy

`(cmp ⊗ 1_K) ≫ ε_{K,M} = α ≫ (1 ⊗ ε_{K,L}) ≫ ε_{L,M}`. -/
theorem compositionApplicationLaw (K L M : DerivedCategory (StructureSheafModules Rc)) :
    CompositionApplicationLaw Rc K L M := by
  have _ : ∀ A, (show CochainComplex (StructureSheafModules Rc) ℤ
      from RingedSite.kInjectiveModel (ringedSite Rc) A).IsKInjective := fun A =>
    RingedSite.isKInjective_kInjectiveModel (ringedSite Rc) A
  have e : ∀ A, DerivedCategory.Q.obj (show CochainComplex (StructureSheafModules Rc) ℤ
      from RingedSite.kInjectiveModel (ringedSite Rc) A) ≅ A :=
    RingedSite.kInjectiveModelIso (ringedSite Rc)
  have h := compositionApplicationLaw_model Rc (RingedSite.kInjectiveModel (ringedSite Rc) K)
    (RingedSite.kInjectiveModel (ringedSite Rc) L) (RingedSite.kInjectiveModel (ringedSite Rc) M)
  have h₁ := compositionApplicationLaw_of_iso_target Rc _ _ (e M).hom h
  have h₂ := compositionApplicationLaw_of_iso_middle Rc _ (e L).hom M h₁
  exact compositionApplicationLaw_of_iso_source Rc (e K).inv L M h₂

end Stacks.SheafOfModules

end
