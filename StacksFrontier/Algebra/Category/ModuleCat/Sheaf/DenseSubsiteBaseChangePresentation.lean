module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteBaseChange
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.GlobalSections

/-!
# Presented sheaves of modules are of the form `M^a`

In the setting of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DenseSubsiteBaseChange.lean`,
let `v : C ⥤ C'` be a dense subsite, `X` a terminal object of `C` whose image is terminal in
`C'`, and suppose the base change presheaves `U ↦ R(v U) ⊗_{R(v X)} M` are sheaves. Then the
rule `M ↦ M^a` is fully faithful, carries `R(v X)` to the structure sheaf and preserves colimits;
so every sheaf of `R`-modules with a global presentation `R^{(K)} ⟶ R^{(I)} ⟶ N ⟶ 0` is
`M^a` for `M` the cokernel of the corresponding map of free `R(v X)`-modules.

## Main results

* `Stacks.DenseSubsiteBaseChange.associatedSheafFullyFaithful`: `M ↦ M^a` is fully faithful.
* `Stacks.DenseSubsiteBaseChange.associatedSheafUnitIso`: `R(v X)^a` is the structure sheaf.
* `Stacks.DenseSubsiteBaseChange.exists_iso_associatedSheaf_of_presentation`: **a sheaf of
  modules with a global presentation is `M^a` for some module `M`.**
* `Stacks.DenseSubsiteBaseChange.nonempty_presentation_associatedSheaf`: conversely, **every
  `M^a` has a presentation**, the image of the presentation of `M` by its elements.
-/

@[expose] public section

universe w u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DenseSubsiteModules Stacks.TerminalBaseChange

namespace Stacks.DenseSubsiteBaseChange

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {J : GrothendieckTopology C} {K : GrothendieckTopology C'}
  {v : C ⥤ C'} [v.IsDenseSubsite J K]
  {R : Sheaf K RingCat.{w}} [CommSections (ringRestriction J K v R).obj]
  {X : C} {hX : IsTerminal X} (h : BaseChangeIsSheaf J K v R hX)
  [(v.sheafPushforwardContinuous AddCommGrpCat.{w} J K).IsEquivalence]

/-- The sections of `M^a` over `v X` are `M`. -/
noncomputable def associatedSheafEvaluationSelfIso :
    associatedSheaf h ⋙ SheafOfModules.evaluation.{w} R (op (v.obj X)) ≅ 𝟭 _ :=
  associatedSheafEvaluationIso h X ≪≫
    eqToIso (congrArg ModuleCat.extendScalars.{w, w, w} (rho_self _ _)) ≪≫
    ModuleCat.extendScalarsId _

/-- **The rule `M ↦ M^a` is fully faithful.** -/
noncomputable def associatedSheafFullyFaithful : (associatedSheaf h).FullyFaithful :=
  (associatedSheafAdj h).fullyFaithfulLOfCompIsoId (associatedSheafEvaluationSelfIso h)

variable (hT : IsTerminal (v.obj X))

/-- **`R(v X)^a` is the structure sheaf**, when `v X` is terminal in `C'`. -/
noncomputable def associatedSheafUnitIso :
    (associatedSheaf h).obj
        (ModuleCat.of ((ringRestriction J K v R).obj.obj (op X))
          ((ringRestriction J K v R).obj.obj (op X))) ≅
      SheafOfModules.unit R := by
  let M₀ := ModuleCat.of ((ringRestriction J K v R).obj.obj (op X))
    ((ringRestriction J K v R).obj.obj (op X))
  let ev : SheafOfModules.{w} R ⥤ ModuleCat.{w} ((ringRestriction J K v R).obj.obj (op X)) :=
    SheafOfModules.evaluation.{w} R (op (v.obj X))
  let u := (associatedSheafAdj h).unit.app M₀
  let x : ((associatedSheaf h).obj M₀).val.obj (op (v.obj X)) :=
    u.hom (1 : (ringRestriction J K v R).obj.obj (op X))
  let hom : (associatedSheaf h).obj M₀ ⟶ SheafOfModules.unit R :=
    ((associatedSheafAdj h).homEquiv _ _).symm (𝟙 _)
  let inv : SheafOfModules.unit R ⟶ (associatedSheaf h).obj M₀ :=
    (Stacks.SectionRingGeometric.unitHomAddEquiv hT _).symm x
  have hinv : (inv.val.app (op (v.obj X))).hom (1 : R.obj.obj (op (v.obj X))) = x :=
    (Stacks.SectionRingGeometric.unitHomAddEquiv hT _).apply_symm_apply x
  have hhom : u ≫ ev.map hom = 𝟙 _ :=
    ((associatedSheafAdj h).homEquiv_unit _ _ hom).symm.trans (Equiv.apply_symm_apply _ _)
  have hhom₁ : (ev.map hom).hom x = (1 : R.obj.obj (op (v.obj X))) :=
    congrArg (fun f => f.hom (1 : (ringRestriction J K v R).obj.obj (op X))) hhom
  refine ⟨hom, inv, ?_, ?_⟩
  · apply ((associatedSheafAdj h).homEquiv _ _).injective
    rw [(associatedSheafAdj h).homEquiv_unit, (associatedSheafAdj h).homEquiv_unit]
    ext1
    refine LinearMap.ext_ring ?_
    change (ev.map inv).hom ((ev.map hom).hom x) = (ev.map (𝟙 _)).hom x
    rwa [hhom₁, ev.map_id]
  · apply (Stacks.SectionRingGeometric.unitHomAddEquiv hT _).injective
    change (ev.map hom).hom ((inv.val.app (op (v.obj X))).hom (1 : R.obj.obj (op (v.obj X)))) =
      (1 : R.obj.obj (op (v.obj X)))
    rwa [hinv]

/-- The functor `M ↦ M^a` preserves colimits, being a left adjoint. -/
private theorem preservesColimitsOfSize_associatedSheaf :
    PreservesColimitsOfSize.{0, 0} (associatedSheaf h) :=
  have := (associatedSheafAdj h).isLeftAdjoint
  preservesColimitsOfSize_shrink _

variable [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]

include hT in
/-- The free sheaf of modules on `I` is `(R(v X)^{(I)})^a`. -/
noncomputable def associatedSheafFreeIso (I : Type w) :
    (associatedSheaf h).obj (∐ fun _ : I ↦ ModuleCat.of ((ringRestriction J K v R).obj.obj (op X))
        ((ringRestriction J K v R).obj.obj (op X))) ≅ SheafOfModules.free I :=
  haveI : HasCoproducts.{w} (PresheafOfModules.{w} R.obj) := fun I ↦
    PresheafOfModules.hasColimitsOfShape (R := R.obj) (J := Discrete I)
  haveI : HasCoproducts.{w} (SheafOfModules.{w} R) := fun I ↦
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      R (Discrete I)
  PreservesCoproduct.iso (associatedSheaf h) _ ≪≫
    Sigma.mapIso (fun _ ↦ associatedSheafUnitIso h hT)

include hT in
/-- **A sheaf of modules with a global presentation is `M^a`** for `M` the cokernel of the
corresponding map of free modules over `R(v X)`. -/
theorem exists_iso_associatedSheaf_of_presentation {N : SheafOfModules.{w} R}
    (p : N.Presentation) :
    ∃ M : ModuleCat.{w} ((ringRestriction J K v R).obj.obj (op X)),
      Nonempty (N ≅ (associatedSheaf h).obj M) := by
  let ff := associatedSheafFullyFaithful h
  have := preservesColimitsOfSize_associatedSheaf h
  let a : SheafOfModules.free p.relations.I ⟶ SheafOfModules.free p.generators.I :=
    (SheafOfModules.freeHomEquiv _).symm p.relations.s ≫ kernel.ι p.generators.π
  let α := ff.preimage ((associatedSheafFreeIso h hT _).hom ≫ a ≫
    (associatedSheafFreeIso h hT _).inv)
  refine ⟨cokernel α, ⟨?_⟩⟩
  refine (p.isColimit.coconePointUniqueUpToIso (cokernelIsCokernel a)) ≪≫ ?_ ≪≫
    (PreservesCokernel.iso (associatedSheaf h) α).symm
  refine cokernel.mapIso _ _ (associatedSheafFreeIso h hT _).symm
    (associatedSheafFreeIso h hT _).symm ?_
  rw [ff.map_preimage]
  simp [a]

/-- The morphism from the free module on the elements of a module onto it. -/
noncomputable def freeElementsπ {A : RingCat.{w}} (M : ModuleCat.{w} A) :
    (∐ fun _ : M ↦ ModuleCat.of A A) ⟶ M :=
  Sigma.desc fun m ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)

/-- The morphism `freeElementsπ M` is an epimorphism. -/
instance freeElementsπ_epi {A : RingCat.{w}} (M : ModuleCat.{w} A) : Epi (freeElementsπ M) := by
  rw [ModuleCat.epi_iff_surjective]
  intro m
  refine ⟨(Sigma.ι (fun _ : M ↦ ModuleCat.of A A) m).hom (1 : A), ?_⟩
  exact (congrArg (fun φ ↦ φ.hom (1 : A))
    (Sigma.ι_comp_desc (fun m ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton A M m)) m)).trans
    (one_smul A m)

/-- The kernel of `freeElementsπ`. -/
noncomputable abbrev freeElementsKer {A : RingCat.{w}} (M : ModuleCat.{w} A) : ModuleCat.{w} A :=
  kernel (freeElementsπ M)

/-- The morphism from the free module on the elements of the kernel of `freeElementsπ M` to the
free module on the elements of `M`, induced by the inclusion of that kernel. -/
noncomputable def freeElementsRel {A : RingCat.{w}} (M : ModuleCat.{w} A) :
    (∐ fun _ : freeElementsKer M ↦ ModuleCat.of A A) ⟶
      (∐ fun _ : M ↦ ModuleCat.of A A) :=
  freeElementsπ (freeElementsKer M) ≫ kernel.ι _

/-- The composite `freeElementsRel M ≫ freeElementsπ M` is zero. -/
lemma freeElementsRel_π {A : RingCat.{w}} (M : ModuleCat.{w} A) :
    freeElementsRel M ≫ freeElementsπ M = 0 := by
  simp [freeElementsRel]

/-- `freeElementsπ` is a cokernel of `freeElementsRel`. -/
noncomputable def isColimitFreeElements {A : RingCat.{w}} (M : ModuleCat.{w} A) :
    IsColimit (CokernelCofork.ofπ (freeElementsπ M) (freeElementsRel_π M)) :=
  isCokernelEpiComp (c := CokernelCofork.ofπ _ (kernel.condition (freeElementsπ M)))
    (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)) _ rfl

include hT in
/-- **The sheaf `M^a` has a presentation**: the free presentation of `M` by its elements and the
elements of the kernel, pushed through `M ↦ M^a`. -/
theorem nonempty_presentation_associatedSheaf
    (M : ModuleCat.{w} ((ringRestriction J K v R).obj.obj (op X))) :
    Nonempty ((associatedSheaf h).obj M).Presentation := by
  have := preservesColimitsOfSize_associatedSheaf h
  let eG := associatedSheafFreeIso h hT M
  let eR := associatedSheafFreeIso h hT (freeElementsKer M)
  let f : SheafOfModules.free (freeElementsKer M) ⟶ SheafOfModules.free M :=
    eR.inv ≫ (associatedSheaf h).map (freeElementsRel M) ≫ eG.hom
  let g : SheafOfModules.free M ⟶ (associatedSheaf h).obj M :=
    eG.inv ≫ (associatedSheaf h).map (freeElementsπ M)
  have hfg : f ≫ g = 0 := by
    simp only [f, g, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, freeElementsRel_π,
      Functor.map_zero, comp_zero]
  refine ⟨SheafOfModules.presentationOfIsCokernelFree f g hfg ?_⟩
  refine IsCokernel.ofIso _
    (CokernelCofork.mapIsColimit _ (isColimitFreeElements M) (associatedSheaf h))
    _ eR eG (Iso.refl _) ?_ ?_
  · simp [f]
  · simp [g]

end Stacks.DenseSubsiteBaseChange

end
