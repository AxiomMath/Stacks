module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.ExtensionOfScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibleHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalars

/-!
# Restriction of scalars of constructible étale sheaves of modules

Let `f : R →+* S` be a surjective homomorphism of Noetherian rings. Restriction of scalars along
`f` carries a constructible sheaf of `S`-modules on the small étale site of a scheme to a
constructible sheaf of `R`-modules: on each stratum of a constructible stratification it commutes
with inverse image and with the constant sheaf functor, and a finitely generated `S`-module is
finitely generated over `R`. This is the change of coefficient ring `Λ ⟶ Λ/ℓΛ` in the proof of
Stacks 0GKW.

The proof mirrors `Stacks.EtaleCohomology.isConstructibleModuleSheaf_extendScalars` (Stacks
0GKB): restriction of scalars is left adjoint to coextension of scalars, which preserves
sheaves, so restriction of scalars commutes with sheafification and, by uniqueness of left
adjoints, with inverse images along continuous functors.

## Main results

* `Stacks.EtaleCohomology.isConstructibleModuleSheaf_restrictScalars`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u w r s v c

namespace CategoryTheory

/-- Restriction of scalars of a sheaf of modules, applied sectionwise. -/
public abbrev restrictScalarsSheaf {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) {R : Type r} {S : Type s} [CommRing R] [CommRing S] (f : R →+* S) :
    Sheaf J (ModuleCat.{max r s w} S) ⥤ Sheaf J (ModuleCat.{max r s w} R) :=
  letI : Limits.PreservesLimitsOfSize.{v, max c v}
      (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f).rightAdjoint_preservesLimits
  letI : J.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩
  sheafCompose J (ModuleCat.restrictScalars.{max r s w, r, s} f)

private lemma hasSheafCompose_coextendScalars {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C) {R : Type r} {S : Type s} [CommRing R] [CommRing S] (f : R →+* S) :
    J.HasSheafCompose (ModuleCat.coextendScalars.{r, s, max r s w} f) := by
  let : Limits.PreservesLimitsOfSize.{v, max c v}
      (ModuleCat.coextendScalars.{r, s, max r s w} f) :=
    (ModuleCat.restrictCoextendScalarsAdj.{max r s w, r, s} f).rightAdjoint_preservesLimits
  exact ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩

private noncomputable def restrictScalarsConstantSheafIso'
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    [HasWeakSheafify J (ModuleCat.{max r s w} R)]
    [HasWeakSheafify J (ModuleCat.{max r s w} S)]
    (f : R →+* S) (E : ModuleCat.{max r s w} S) :
    (restrictScalarsSheaf.{w} J f).obj ((constantSheaf J (ModuleCat.{max r s w} S)).obj E) ≅
      (constantSheaf J (ModuleCat.{max r s w} R)).obj
        ((ModuleCat.restrictScalars.{max r s w, r, s} f).obj E) := by
  letI : J.HasSheafCompose (ModuleCat.coextendScalars.{r, s, max r s w} f) :=
    hasSheafCompose_coextendScalars J f
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{max r s w, r, s} f)
  letI : Limits.PreservesLimitsOfSize.{v, max c v}
      (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f).rightAdjoint_preservesLimits
  letI : J.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩
  exact (sheafToPresheaf J (ModuleCat.{max r s w} R)).preimageIso
    ((sheafifyComposeIso J (ModuleCat.restrictScalars.{max r s w, r, s} f)
      ((Functor.const Cᵒᵖ).obj E)).symm ≪≫
    (sheafification J (ModuleCat.{max r s w} R)).mapIso
      (Functor.constComp Cᵒᵖ E (ModuleCat.restrictScalars.{max r s w, r, s} f)))

private noncomputable def sheafPullbackRestrictScalarsAppIso
    {C D : Type c} [Category.{v} C] [Category.{v} D]
    (G : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [Functor.IsContinuous G J K]
    {R : Type r} {S : Type s} [CommRing R] [CommRing S] (f : R →+* S)
    [HasWeakSheafify J (ModuleCat.{max r s w} R)]
    [HasWeakSheafify K (ModuleCat.{max r s w} R)]
    [(G.sheafPushforwardContinuous (ModuleCat.{max r s w} R) J K).IsRightAdjoint]
    [(G.sheafPushforwardContinuous (ModuleCat.{max r s w} S) J K).IsRightAdjoint]
    (F : Sheaf J (ModuleCat.{max r s w} S)) :
    (restrictScalarsSheaf.{w} K f).obj ((G.sheafPullback (ModuleCat.{max r s w} S) J K).obj F) ≅
      (G.sheafPullback (ModuleCat.{max r s w} R) J K).obj
        ((restrictScalarsSheaf.{w} J f).obj F) := by
  let T := ModuleCat.coextendScalars.{r, s, max r s w} f
  letI : J.HasSheafCompose T := hasSheafCompose_coextendScalars J f
  letI : K.HasSheafCompose T := hasSheafCompose_coextendScalars K f
  letI : Limits.PreservesLimitsOfSize.{v, max c v}
      (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    (ModuleCat.extendRestrictScalarsAdj.{max r s w, r, s} f).rightAdjoint_preservesLimits
  letI : J.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf J P _ hP⟩
  letI : K.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f) :=
    ⟨fun P hP => Presheaf.isSheaf_comp_of_isSheaf K P _ hP⟩
  let adjSheaf : ∀ (L : GrothendieckTopology C) [L.HasSheafCompose T]
      [L.HasSheafCompose (ModuleCat.restrictScalars.{max r s w, r, s} f)],
      sheafCompose L (ModuleCat.restrictScalars.{max r s w, r, s} f) ⊣ sheafCompose L T :=
    fun L _ _ => ((ModuleCat.restrictCoextendScalarsAdj.{max r s w, r, s} f).whiskerRight
      Cᵒᵖ).restrictFullyFaithful (fullyFaithfulSheafToPresheaf L _)
      (fullyFaithfulSheafToPresheaf L _) (Iso.refl _) (Iso.refl _)
  let adjSheafK : sheafCompose K (ModuleCat.restrictScalars.{max r s w, r, s} f) ⊣
      sheafCompose K T :=
    ((ModuleCat.restrictCoextendScalarsAdj.{max r s w, r, s} f).whiskerRight
      Dᵒᵖ).restrictFullyFaithful (fullyFaithfulSheafToPresheaf K _)
      (fullyFaithfulSheafToPresheaf K _) (Iso.refl _) (Iso.refl _)
  let pR := G.sheafAdjunctionContinuous (ModuleCat.{max r s w} R) J K
  let pS := G.sheafAdjunctionContinuous (ModuleCat.{max r s w} S) J K
  let rightIso :
      G.sheafPushforwardContinuous (ModuleCat.{max r s w} R) J K ⋙ sheafCompose J T ≅
        sheafCompose K T ⋙ G.sheafPushforwardContinuous (ModuleCat.{max r s w} S) J K :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  exact (Adjunction.leftAdjointUniq (pS.comp adjSheafK)
    (((adjSheaf J).comp pR).ofNatIsoRight rightIso)).app F

end CategoryTheory

namespace Stacks.ConstantSheaf

private theorem isFiniteTypeLocallyConstant_restrictScalars
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    {R : Type r} {S : Type s} [CommRing R] [CommRing S]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max r s w} R)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max r s w} S)]
    (f : R →+* S) (hf : Function.Surjective f) (F : Sheaf J (ModuleCat.{max r s w} S))
    (hF : IsFiniteTypeLocallyConstant S J F) :
    IsFiniteTypeLocallyConstant R J ((restrictScalarsSheaf.{w} J f).obj F) := by
  intro U
  rcases hF U with ⟨I, V, g, hg, hV⟩
  refine ⟨I, V, g, hg, fun i => ?_⟩
  rcases hV i with ⟨E, hE, ⟨e⟩⟩
  refine ⟨(ModuleCat.restrictScalars.{max r s w, r, s} f).obj E, ?_, ⟨?_⟩⟩
  · rw [ModuleCat.isFG_iff] at hE ⊢
    let _ : Algebra R S := f.toAlgebra
    let _ : Module R E := ((ModuleCat.restrictScalars.{max r s w, r, s} f).obj E).isModule
    have : IsScalarTower R S E := .of_algebraMap_smul fun _ _ => rfl
    have : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) hf
    exact Module.Finite.trans S E
  · exact (restrictScalarsConstantSheafIso' (J.over (V i)) f E).symm ≪≫
      (restrictScalarsSheaf.{w} (J.over (V i)) f).mapIso e ≪≫
      (NatIso.ofComponents (F := J.overPullback (ModuleCat.{max r s w} S) (V i) ⋙
          restrictScalarsSheaf.{w} (J.over (V i)) f)
        (G := restrictScalarsSheaf.{w} J f ⋙ J.overPullback (ModuleCat.{max r s w} R) (V i))
        (fun _ => Iso.refl _) (fun _ => rfl)).app F

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

open Stacks.ConstantSheaf

/-- **Restriction of scalars along a surjective homomorphism of Noetherian rings preserves
constructibility** of sheaves of modules on the small étale site. -/
public theorem isConstructibleModuleSheaf_restrictScalars
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (R : Type r) (S : Type s) [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (f : R →+* S) (hf : Function.Surjective f)
    [HasWeakSheafify (SmallEtale.topology B X.1 X.property) (ModuleCat.{max r s w} R)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max r s w} R)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{max r s w} R)]
    [∀ (A T : B.Scheme) (g : T ⟶ A),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{max r s w} S)
        (SmallEtale.topology B A.1 A.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{max r s w} S)]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{max r s w} S))
    (hF : IsConstructibleModuleSheaf B X S F) :
    IsConstructibleModuleSheaf B X R
      ((restrictScalarsSheaf.{w} (SmallEtale.topology B X.1 X.property) f).obj F) := by
  intro U
  rcases hF U with ⟨stratification, hstratification⟩
  refine ⟨stratification, fun i => ?_⟩
  let J := SmallEtale.topology B (stratification.piece i).1 (stratification.piece i).property
  let : HasWeakSheafify J (ModuleCat.{max r s w} R) :=
    AlgebraicGeometry.SmallEtale.hasWeakSheafify_of_overTerminal J _
      (SmallEtale.finalIsTerminal B (stratification.piece i).1 (stratification.piece i).property)
  exact isFiniteTypeLocallyConstant_congr J R
    (sheafPullbackRestrictScalarsAppIso
      (AlgebraicGeometry.smallEtaleBaseChange B (stratification.inclusion i))
      (SmallEtale.topology B X.1 X.property) J f F)
    (isFiniteTypeLocallyConstant_restrictScalars J f hf _ (hstratification i))

section EtaleModules

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **Restriction of scalars along a surjection of Noetherian rings preserves constructibility
on Mathlib's small étale site.** -/
public theorem isConstructibleEtaleModule_restrictScalars (B : BigEtaleSite.{u}) (X : B.Scheme)
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] [IsNoetherianRing Λ] [IsNoetherianRing Λ']
    (ρ : Λ →+* Λ') (hρ : Function.Surjective ρ) (F : EtaleModules.{u, 0} Λ' X.obj)
    (hF : IsBigSiteConstructibleEtaleModule B X Λ' F) :
    IsBigSiteConstructibleEtaleModule B X Λ ((etaleModuleRestrictScalars ρ X.obj).obj F) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X Λ
  exact isConstructibleModuleSheaf_restrictScalars.{u, u + 1} B X Λ Λ' ρ hρ _ hF

end EtaleModules

end Stacks.EtaleCohomology

end
