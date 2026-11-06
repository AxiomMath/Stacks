module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.Filtered
public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.LeftExact
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.ModuleActionEquivalence
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.RightExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Right exact functors on a module category

Let `A` be a ring and let `B` be an additive category with arbitrary coproducts and cokernels.
Right exact functors from right `A`-modules to `B` which preserve arbitrary coproducts are
classified by objects of `B` equipped with an action of `A`.

## Main definitions

* `ModuleCat.RightExactCoproductPreservingFunctor` is the category of right exact functors that
  preserve arbitrary coproducts.
* `ModuleCat.regularModuleFunctor` regards the right regular module as an additive functor from
  the one-object preadditive category attached to `A`.
* `ModuleCat.functorToRingActions` sends such a functor to its value on the regular module,
  with its natural `A`-action.

## Main results

* `ModuleCat.functorToRingActions_isEquivalence`: that functor is an equivalence.

## Implementation notes

Right `A`-modules are represented as left `Aᵐᵒᵖ`-modules. An additive functor
`SingleObj A ⥤ B` is precisely a pair consisting of an object `K` and a ring homomorphism
`A →+* End K`, and its natural transformations are the morphisms intertwining these actions;
this is what identifies `CategoryTheory.AdditiveFunctor (SingleObj A) B` with
`ModuleCat.ModuleAction A B`.

The equivalence is obtained by composing three: restriction to the finitely presented modules,
which is an equivalence because a right exact coproduct-preserving functor is determined by its
filtered-colimit extension; the evaluation equivalence of
`ModuleCat.evaluationFunctor_isEquivalence`; and the identification of objects with an action
with additive functors out of `SingleObj A`.

## References

* [Stacks Project, Tag 0GNQ](https://stacks.math.columbia.edu/tag/0GNQ)
-/

@[expose] public section

namespace ModuleCat

universe w v u

open CategoryTheory CategoryTheory.Limits

variable (A : Type u) [Ring A]
variable (B : Type v) [Category.{w} B] [Preadditive B]
  [HasCoproducts.{u} B] [HasCokernels B]

/-- Right multiplication by `A` on itself, encoded as a left `Aᵐᵒᵖ`-module, is a left
multiplication endomorphism. -/
public def regularModuleLeftMul (a : A) :
    ModuleCat.of Aᵐᵒᵖ A ⟶ ModuleCat.of Aᵐᵒᵖ A :=
  ModuleCat.ofHom
    { toFun := fun x => a * x
      map_add' := mul_add a
      map_smul' := fun r x => by
        change a * (x * r.unop) = (a * x) * r.unop
        rw [mul_assoc] }

/-- Left multiplication by `1` is the identity of the right regular module. -/
@[simp]
public lemma regularModuleLeftMul_one : regularModuleLeftMul A 1 = 𝟙 _ := by
  ext
  simp [regularModuleLeftMul]

/-- Left multiplication by `b * a` is left multiplication by `a` followed by left
multiplication by `b`. -/
@[simp]
public lemma regularModuleLeftMul_comp (a b : A) :
    regularModuleLeftMul A (b * a) = regularModuleLeftMul A a ≫ regularModuleLeftMul A b := by
  ext
  simp [regularModuleLeftMul, mul_assoc]

/-- The right regular `A`-module, together with all its endomorphisms coming from left
multiplication. -/
public def regularModuleFunctor : SingleObj A ⥤ ModuleCat.{u} Aᵐᵒᵖ where
  obj _ := ModuleCat.of Aᵐᵒᵖ A
  map a := regularModuleLeftMul A a
  map_id _ := regularModuleLeftMul_one A
  map_comp a b := regularModuleLeftMul_comp A a b

/-- The regular module functor is additive, since left multiplication is additive in the
multiplier. -/
public instance : (regularModuleFunctor A).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact add_mul f g x

/-- The property that a functor is right exact and preserves arbitrary coproducts. -/
public def isRightExactAndPreservesCoproducts :
    ObjectProperty (ModuleCat.{u} Aᵐᵒᵖ ⥤ B) := fun F =>
  PreservesFiniteColimits F ∧
    ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F

/-- The category of right exact, arbitrary-coproduct-preserving functors from right
`A`-modules to `B`. -/
public abbrev RightExactCoproductPreservingFunctor :=
  (isRightExactAndPreservesCoproducts A B).FullSubcategory

/-- A right exact functor out of right `A`-modules is additive. -/
public instance (F : RightExactCoproductPreservingFunctor A B) : F.obj.Additive := by
  let : HasZeroObject B := Preadditive.hasZeroObject_of_hasCoproduct B
  exact rightExactFunctor_le_additiveFunctor (ModuleCat.{u} Aᵐᵒᵖ) B F.obj F.property.1

/-- The ring action encoded by an additive functor out of the one-object category of `A`. -/
public def ringAction (G : SingleObj A ⥤+ B) :
    A →+* End (G.obj.obj (SingleObj.star A)) :=
  { toFun a := End.of (G.obj.map a)
    map_one' := by ext; exact G.obj.map_id _
    map_mul' a b := by ext; exact G.obj.map_comp b a
    map_zero' := by ext; exact G.obj.map_zero _ _
    map_add' _ _ := by ext; exact G.obj.map_add }

/-- Restriction to the right regular module.  On objects this sends `F` to `F(A)`, equipped
with the action whose value at `a` is `F` applied to left multiplication by `a`. -/
public def functorToRingActions :
    RightExactCoproductPreservingFunctor A B ⥤ SingleObj A ⥤+ B :=
  (additiveFunctor (SingleObj A) B).lift
    ((ObjectProperty.ι (isRightExactAndPreservesCoproducts A B)) ⋙
      (Functor.whiskeringLeft (SingleObj A) (ModuleCat.{u} Aᵐᵒᵖ) B).obj
        (regularModuleFunctor A))
    (fun F => by
      change (regularModuleFunctor A ⋙ F.obj).Additive
      infer_instance)

omit [HasCokernels B] in
/-- The ring action on `F(A)` sends `a` to `F` applied to left multiplication by `a`. -/
@[simp]
public lemma ringAction_functorToRingActions_obj
    (F : RightExactCoproductPreservingFunctor A B) (a : A) :
    ringAction A B ((functorToRingActions A B).obj F) a =
      End.of (F.obj.map (regularModuleLeftMul A a)) := rfl

private lemma finitelyPresentedModule_le_isFinitelyPresentable (R : Type u) [Ring R] :
    finitelyPresentedModule.{u, u} R ≤
      ObjectProperty.isFinitelyPresentable.{u} (ModuleCat.{u} R) :=
  fun M hM => finitePresentation_isFinitelyPresentable.{u, u} R M hM

omit [Preadditive B] [HasCoproducts.{u} B] in
private lemma rightExactCoproductFunctor_preservesFilteredColimits
    (F : RightExactCoproductPreservingFunctor A B) :
    PreservesFilteredColimitsOfSize.{u, u} F.obj := by
  let (J : Type u) : PreservesColimitsOfShape (Discrete J) F.obj := F.property.2 J
  let : PreservesFiniteColimits F.obj := F.property.1
  let : PreservesColimitsOfShape WalkingParallelPair F.obj := inferInstance
  let : PreservesColimitsOfSize.{u, u} F.obj :=
    preservesColimits_of_preservesCoequalizers_and_coproducts F.obj
  infer_instance

private def restrictToFinitelyPresented :
  RightExactCoproductPreservingFunctor A B ⥤
      (FPModule A ⥤ᵣ B) where
  obj F := by
    letI : PreservesFiniteColimits F.obj := F.property.1
    letI : PreservesFiniteColimits (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι :=
      fpModuleInclusion_preservesFiniteColimits A
    exact ⟨(finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι.comp F.obj, comp_preservesFiniteColimits _ _⟩
  map {F G} η :=
    ObjectProperty.homMk
      (Functor.whiskerLeft (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι η.hom)
  map_id F := by
    ext X
    rfl
  map_comp f g := by
    ext X
    rfl

private noncomputable def rightExactFunctorFilteredExtension
    (F : FPModule A ⥤ᵣ B) :
    FilteredColimitExtension.{u, u, v, w} Aᵐᵒᵖ F.obj := by
  letI : HasCoequalizers B := Preadditive.hasCoequalizers_of_hasCokernels
  letI : HasColimitsOfSize.{u, u} B := has_colimits_of_hasCoequalizers_and_coproducts
  letI : HasFiniteCoproducts B := hasFiniteCoproducts_of_hasCoproducts (C := B)
  letI : HasFiniteBiproducts B := HasFiniteBiproducts.of_hasFiniteCoproducts
  letI : PreservesFiniteColimits F.obj := F.property
  letI : F.obj.Additive := rightExactFunctor_additive A B F
  exact filteredColimitExtension Aᵐᵒᵖ F.obj

private noncomputable def extendRightExactFunctor
    (F : FPModule A ⥤ᵣ B) : RightExactCoproductPreservingFunctor A B := by
  letI : HasCoequalizers B := Preadditive.hasCoequalizers_of_hasCokernels
  letI : HasColimitsOfSize.{u, u} B := has_colimits_of_hasCoequalizers_and_coproducts
  letI : HasFiniteCoproducts B := hasFiniteCoproducts_of_hasCoproducts (C := B)
  letI : HasFiniteBiproducts B := HasFiniteBiproducts.of_hasFiniteCoproducts
  letI : PreservesFiniteColimits F.obj := F.property
  letI : F.obj.Additive := rightExactFunctor_additive A B F
  let E := rightExactFunctorFilteredExtension A B F
  letI : PreservesFiniteColimits E.functor :=
    @filteredColimitExtension_preservesFiniteColimits.{u, u, v, w}
      Aᵐᵒᵖ inferInstance B inferInstance inferInstance inferInstance inferInstance
      F.obj E F.property
  exact ⟨E.functor, inferInstance, fun J => extension_preserves_discrete_coproducts.{u, u} Aᵐᵒᵖ E J⟩

/-- Natural transformations between filtered-colimit-preserving functors out of `Aᵐᵒᵖ`-modules
are uniquely determined by their restriction to the finitely presented modules. -/
private theorem existsUnique_natTrans_whiskerLeft {D : Type*} [Category D]
    {F₁ F₂ : ModuleCat.{u} Aᵐᵒᵖ ⥤ D} [PreservesFilteredColimitsOfSize.{u, u} F₁]
    (β : (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι ⋙ F₁ ⟶
      (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι ⋙ F₂) :
    ∃! φ : F₁ ⟶ F₂, Functor.whiskerLeft (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι φ = β :=
  ObjectProperty.existsUnique_natTrans_of_preservesFilteredColimits
    (finitelyPresentedModule.{u, u} Aᵐᵒᵖ)
    (finitelyPresentedModule_le_isFinitelyPresentable Aᵐᵒᵖ)
    (ind_finitelyPresentedModule.{u, u} Aᵐᵒᵖ) F₁ F₂ β

private noncomputable def extendRightExactFunctorMap
    {F G : FPModule A ⥤ᵣ B} (α : F ⟶ G) :
    extendRightExactFunctor A B F ⟶ extendRightExactFunctor A B G := by
  let E₁ := rightExactFunctorFilteredExtension A B F
  let E₂ := rightExactFunctorFilteredExtension A B G
  letI : PreservesFilteredColimitsOfSize.{u, u} E₁.functor := E₁.preservesFilteredColimits
  letI : PreservesFilteredColimitsOfSize.{u, u} E₂.functor := E₂.preservesFilteredColimits
  let β : (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι ⋙ E₁.functor ⟶
      (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι ⋙ E₂.functor :=
    E₁.iso.hom ≫ α.hom ≫ E₂.iso.inv
  let h := existsUnique_natTrans_whiskerLeft A β
  exact ObjectProperty.homMk (Classical.choose h.exists)

private lemma extendRightExactFunctorMap_restrict
    {F G : FPModule A ⥤ᵣ B} (α : F ⟶ G) :
    Functor.whiskerLeft (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι
    (extendRightExactFunctorMap A B α).hom =
        (rightExactFunctorFilteredExtension A B F).iso.hom ≫
          α.hom ≫
          (rightExactFunctorFilteredExtension A B G).iso.inv := by
  classical
  let E₁ := rightExactFunctorFilteredExtension A B F
  let E₂ := rightExactFunctorFilteredExtension A B G
  let : PreservesFilteredColimitsOfSize.{u, u} E₁.functor := E₁.preservesFilteredColimits
  let : PreservesFilteredColimitsOfSize.{u, u} E₂.functor := E₂.preservesFilteredColimits
  let β : (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι ⋙ E₁.functor ⟶
      (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι ⋙ E₂.functor :=
    E₁.iso.hom ≫ α.hom ≫ E₂.iso.inv
  let h := existsUnique_natTrans_whiskerLeft A β
  show Functor.whiskerLeft (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι
      (Classical.choose h.exists) = β
  exact Classical.choose_spec h.exists

/-- Cancel a two-sided inverse pair sitting in the middle of a five-fold composite. Stated
separately so that it can be applied as a term: the composites it is used on carry objects that
`rw` and `simp` cannot see through. -/
private lemma assoc_cancel_mid {C : Type*} [Category C] {W X Y Z T U : C}
    (a : W ⟶ X) (f : X ⟶ Y) (i : Y ⟶ Z) (h : Z ⟶ Y) (g : Y ⟶ T) (k : T ⟶ U)
    (hih : i ≫ h = CategoryStruct.id Y) :
    (a ≫ f ≫ i) ≫ h ≫ g ≫ k = a ≫ (f ≫ g) ≫ k := by
  simp only [Category.assoc]
  rw [← Category.assoc i h, hih, Category.id_comp]

/-- Cancel a two-sided inverse pair at the tail of a composite. Stated separately for the same
reason as `ModuleCat.assoc_cancel_mid`. -/
private lemma assoc_cancel_tail {C : Type*} [Category C] {W X Y Z : C}
    (a : W ⟶ X) (f : X ⟶ Y) (i : Y ⟶ Z) (h : Z ⟶ Y)
    (hih : i ≫ h = CategoryStruct.id Y) :
    (a ≫ f ≫ i) ≫ h = a ≫ f := by
  simp only [Category.assoc]
  rw [hih, Category.comp_id]

private noncomputable def extendRightExactFunctorFunctor :
    (FPModule A ⥤ᵣ B) ⥤ RightExactCoproductPreservingFunctor A B where
  obj := extendRightExactFunctor A B
  map α := extendRightExactFunctorMap A B α
  map_id F := by
    let E := rightExactFunctorFilteredExtension A B F
    let : PreservesFilteredColimitsOfSize.{u, u} E.functor := E.preservesFilteredColimits
    apply ObjectProperty.hom_ext
    let idα := (𝟙 F.obj)
    let β := E.iso.hom ≫ idα ≫ E.iso.inv
    let h := existsUnique_natTrans_whiskerLeft A β
    dsimp [extendRightExactFunctorMap]
    symm
    apply h.unique
    · ext X
      simp [β, idα, E, extendRightExactFunctor, rightExactFunctorFilteredExtension]
    · exact Classical.choose_spec h.exists
  map_comp {F G H} f g := by
    let E₁ := rightExactFunctorFilteredExtension A B F
    let E₂ := rightExactFunctorFilteredExtension A B G
    let E₃ := rightExactFunctorFilteredExtension A B H
    let : PreservesFilteredColimitsOfSize.{u, u} E₁.functor := E₁.preservesFilteredColimits
    let : PreservesFilteredColimitsOfSize.{u, u} E₂.functor := E₂.preservesFilteredColimits
    let : PreservesFilteredColimitsOfSize.{u, u} E₃.functor := E₃.preservesFilteredColimits
    let β := E₁.iso.hom ≫ (f ≫ g).hom ≫ E₃.iso.inv
    let h := existsUnique_natTrans_whiskerLeft A β
    apply ObjectProperty.hom_ext
    dsimp [extendRightExactFunctorMap]
    symm
    apply h.unique
    · ext X
      have hf := congrArg (fun τ => τ.app X) (extendRightExactFunctorMap_restrict A B f)
      have hg := congrArg (fun τ => τ.app X) (extendRightExactFunctorMap_restrict A B g)
      dsimp at hf hg
      have hf' := by simpa only [ObjectProperty.ι_obj] using hf
      have hg' := by simpa only [ObjectProperty.ι_obj] using hg
      change (extendRightExactFunctorMap A B f).hom.app X.obj ≫
          (extendRightExactFunctorMap A B g).hom.app X.obj = β.app X
      rw [hf', hg']
      simp only [β, E₁, E₃, NatTrans.comp_app]
      exact assoc_cancel_mid _ _ _ _ _ _ (Iso.inv_hom_id_app E₂.iso X)
    · exact Classical.choose_spec h.exists

private def moduleActionToAdditiveFunctor :
  ModuleAction A B ⥤ (SingleObj A ⥤+ B) where
  obj K := by
    let F := SingleObj.functor K.action.toMonoidHom
    letI : F.Additive := ⟨by
      intro X Y f g
      simp [F, SingleObj.functor, K.action.map_add]⟩
    exact AdditiveFunctor.of F
  map f := ObjectProperty.homMk (SingleObj.natTrans f.hom f.comm)
  map_id K := by
    ext
    rfl
  map_comp f g := by
    ext
    rfl

private def additiveFunctorToModuleAction :
    (SingleObj A ⥤+ B) ⥤ ModuleAction A B where
  obj F := ⟨F.obj.obj (SingleObj.star A), ringAction A B F⟩
  map f := ⟨f.hom.app (SingleObj.star A), fun a => f.hom.naturality a⟩
  map_id F := by
    apply ModuleAction.Hom.ext
    rfl
  map_comp f g := by
    apply ModuleAction.Hom.ext
    rfl

omit [HasCoproducts.{u} B] [HasCokernels B] in
private lemma moduleActionToAdditiveFunctor_isEquivalence :
    (moduleActionToAdditiveFunctor (A := A) (B := B)).IsEquivalence := by
  apply Functor.IsEquivalence.mk'
    (additiveFunctorToModuleAction (A := A) (B := B))
  · refine NatIso.ofComponents (fun K => by
      dsimp [moduleActionToAdditiveFunctor, additiveFunctorToModuleAction, ringAction]
      exact Iso.refl K) ?_
    intro K L f
    dsimp [moduleActionToAdditiveFunctor, additiveFunctorToModuleAction, ringAction,
      SingleObj.functor]
    -- Both sides are `f` composed with an identity, but the two spellings of `f` differ by a
    -- structure eta the rewriting tactics will not perform, so the identities are cancelled as
    -- terms.
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · refine NatIso.ofComponents (fun F => ObjectProperty.isoMk _ ?_) ?_
    · refine NatIso.ofComponents (fun X => Iso.refl (F.obj.obj (SingleObj.star A))) ?_
      intro X Y f
      cases X
      cases Y
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    intro F G f
    dsimp [moduleActionToAdditiveFunctor, additiveFunctorToModuleAction, ringAction]
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext X
    cases X
    dsimp [Quiver.SingleObj.star, SingleObj.functor]
    simp only [SingleObj.natTrans]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

private noncomputable def filteredColimitExtensionOfAllFunctor
    (F : RightExactCoproductPreservingFunctor A B) :
    FilteredColimitExtension Aᵐᵒᵖ
      ((restrictToFinitelyPresented A B).obj F).obj := by
  letI : PreservesFilteredColimitsOfSize.{u, u} F.obj :=
    rightExactCoproductFunctor_preservesFilteredColimits A B F
  exact ⟨F.obj, inferInstance, Iso.refl _⟩

private noncomputable def extendRestrictionIso
    (F : RightExactCoproductPreservingFunctor A B) :
    (extendRightExactFunctorFunctor A B).obj
        ((restrictToFinitelyPresented A B).obj F) ≅ F := by
  let E₁ := rightExactFunctorFilteredExtension A B
    ((restrictToFinitelyPresented A B).obj F)
  let E₂ := filteredColimitExtensionOfAllFunctor A B F
  let h := FilteredColimitExtension.existsUnique_iso Aᵐᵒᵖ E₁ E₂
  exact ObjectProperty.isoMk _ (Classical.choose h.exists)

private noncomputable def restrictionExtensionUnitIso :
    𝟭 (FPModule A ⥤ᵣ B) ≅
      extendRightExactFunctorFunctor A B ⋙ restrictToFinitelyPresented A B := by
  refine NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (rightExactFunctorFilteredExtension A B F).iso.symm) ?_
  intro F G f
  apply ObjectProperty.hom_ext
  ext X
  let E₁ := rightExactFunctorFilteredExtension A B F
  let E₂ := rightExactFunctorFilteredExtension A B G
  change f.hom.app X ≫ E₂.iso.inv.app X =
    E₁.iso.inv.app X ≫ (extendRightExactFunctorMap A B f).hom.app X.obj
  have hf : (extendRightExactFunctorMap A B f).hom.app X.obj =
      E₁.iso.hom.app X ≫ f.hom.app X ≫ E₂.iso.inv.app X := by
    simpa [Functor.whiskerLeft_app, ObjectProperty.ι_obj] using
      congrArg (fun τ => τ.app X) (extendRightExactFunctorMap_restrict A B f)
  rw [hf]
  exact (Iso.inv_hom_id_app_assoc E₁.iso X _).symm

private noncomputable def restrictionExtensionCounitIso :
    restrictToFinitelyPresented A B ⋙ extendRightExactFunctorFunctor A B ≅
      𝟭 (RightExactCoproductPreservingFunctor A B) := by
  refine NatIso.ofComponents (fun F => extendRestrictionIso A B F) ?_
  intro F G f
  let E₁ := rightExactFunctorFilteredExtension A B ((restrictToFinitelyPresented A B).obj F)
  let E₂ := rightExactFunctorFilteredExtension A B ((restrictToFinitelyPresented A B).obj G)
  let e₁ := extendRestrictionIso A B F
  let e₂ := extendRestrictionIso A B G
  let α := (restrictToFinitelyPresented A B).map f
  let ext := extendRightExactFunctorMap A B α
  let β : (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι ⋙ E₁.functor ⟶
      (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι ⋙ E₂.functor :=
    E₁.iso.hom ≫ α.hom ≫ E₂.iso.inv
  let h := existsUnique_natTrans_whiskerLeft A β
  have hext : Functor.whiskerLeft (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι ext.hom = β := by
    simpa [ext, β, α] using extendRightExactFunctorMap_restrict A B α
  have he₁ : Functor.whiskerLeft (finitelyPresentedModule Aᵐᵒᵖ).ι
      e₁.hom.hom =
        (E₁.iso ≪≫ (filteredColimitExtensionOfAllFunctor A B F).iso.symm).hom :=
    Classical.choose_spec
      (FilteredColimitExtension.existsUnique_iso Aᵐᵒᵖ E₁
        (filteredColimitExtensionOfAllFunctor A B F)).exists
  have he₂ : Functor.whiskerLeft (finitelyPresentedModule Aᵐᵒᵖ).ι
      e₂.hom.hom =
        (E₂.iso ≪≫ (filteredColimitExtensionOfAllFunctor A B G).iso.symm).hom :=
    Classical.choose_spec
      (FilteredColimitExtension.existsUnique_iso Aᵐᵒᵖ E₂
        (filteredColimitExtensionOfAllFunctor A B G)).exists
  have hcancel (X : ModuleCat.{u} Aᵐᵒᵖ) :
      e₂.inv.hom.app X ≫ e₂.hom.hom.app X = 𝟙 (G.obj.obj X) := by
    simpa only [NatTrans.comp_app, NatTrans.id_app] using
      congrArg (fun q => q.app X) (ObjectProperty.isoInv_hom_id_hom e₂)
  have hcomp : Functor.whiskerLeft (finitelyPresentedModule Aᵐᵒᵖ).ι
      (e₁.hom.hom ≫ f.hom ≫ e₂.inv.hom) = β := by
    ext X
    -- `(filteredColimitExtensionOfAllFunctor _ _ _).iso` is `Iso.refl`, so the second factor
    -- of the right-hand side of `he₁` and `he₂` is an identity; `simp` cannot see that through
    -- the definition, while `Eq.trans` only has to check it up to definitional equality.
    have h₁ : e₁.hom.hom.app X.obj = E₁.iso.hom.app X :=
      (congrArg (fun τ => τ.app X) he₁).trans (Category.comp_id _)
    have h₂ : e₂.hom.hom.app X.obj = E₂.iso.hom.app X :=
      (congrArg (fun τ => τ.app X) he₂).trans (Category.comp_id _)
    have hq : e₂.inv.hom.app X.obj ≫ E₂.iso.hom.app X = 𝟙 (G.obj.obj X.obj) :=
      h₂ ▸ hcancel X.obj
    have h₂inv : e₂.inv.hom.app X.obj = E₂.iso.inv.app X :=
      (Iso.comp_hom_eq_id (E₂.iso.app X)).mp hq
    simp only [Functor.whiskerLeft_app, NatTrans.comp_app]
    change e₁.hom.hom.app X.obj ≫ f.hom.app X.obj ≫ e₂.inv.hom.app X.obj = β.app X
    rw [h₁, h₂inv]
    rfl
  have heq : ext.hom = e₁.hom.hom ≫ f.hom ≫ e₂.inv.hom := h.unique hext hcomp
  apply ObjectProperty.hom_ext
  ext X
  change ext.hom.app X ≫ e₂.hom.hom.app X =
    e₁.hom.hom.app X ≫ f.hom.app X
  rw [heq]
  simp only [NatTrans.comp_app]
  exact assoc_cancel_tail _ _ _ _ (hcancel X)

/-- Evaluation on the right regular module, with its natural `A`-action, classifies right exact
functors which preserve arbitrary coproducts. -/
@[stacks 0GNQ, ega "III 7.2.6"]
public lemma functorToRingActions_isEquivalence :
    (functorToRingActions A B).IsEquivalence := by
  let : HasFiniteCoproducts B := hasFiniteCoproducts_of_hasCoproducts (C := B)
  let : HasFiniteBiproducts B := HasFiniteBiproducts.of_hasFiniteCoproducts
  let : (restrictToFinitelyPresented A B).IsEquivalence :=
    Functor.IsEquivalence.mk' (extendRightExactFunctorFunctor A B)
      (restrictionExtensionCounitIso A B).symm (restrictionExtensionUnitIso A B).symm
  let : (evaluationFunctor A B).IsEquivalence :=
    evaluationFunctor_isEquivalence A B
  let : (moduleActionToAdditiveFunctor (A := A) (B := B)).IsEquivalence :=
    moduleActionToAdditiveFunctor_isEquivalence (A := A) (B := B)
  show (restrictToFinitelyPresented A B ⋙ evaluationFunctor A B ⋙
    moduleActionToAdditiveFunctor (A := A) (B := B)).IsEquivalence
  infer_instance

end ModuleCat
