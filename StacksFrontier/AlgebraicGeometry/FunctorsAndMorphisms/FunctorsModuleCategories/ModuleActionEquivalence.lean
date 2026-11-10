module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsModuleCategories.ModuleAction
public import StacksCore.Tactic.StacksAttribute

/-!
# Right exact functors on finitely presented modules are tensor products

Evaluation on the rank-one free module is an equivalence from the category of right exact
functors on finitely presented right `A`-modules to the category of objects of `B` equipped
with an `A`-action. The inverse sends an object with an action to the functor that tensors
with it.

## Main results

* `ModuleCat.evaluationFunctor_isEquivalence`: evaluation is an equivalence of categories.

## Implementation notes

The tensor functor attached to an object `K` with an `A`-action is built as a partial left
adjoint: the functor `X ↦ Hom(K, X)`, with its `A`-action, has a left adjoint defined at every
finitely presented module, because that holds for the rank-one free module by direct
computation and is inherited along the finite coproducts and cokernels that present a finitely
presented module. Right exactness of that tensor functor comes from the same presentation.

The comparison between a right exact functor and the tensor functor on its value at the
rank-one free module is an isomorphism on that module by construction, hence on finite free
modules and then on all finitely presented modules by induction along presentations. That
induction is `ModuleCat.finitePresentation_induction`.

## References

* [Stacks Project, Tag 0GNN](https://stacks.math.columbia.edu/tag/0GNN)
-/

@[expose] public section

namespace ModuleCat

universe w v u

open CategoryTheory CategoryTheory.Limits

private abbrev evaluationObject (A : Type u) (B : Type v) [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (F : FPModule A ⥤ᵣ B) : ModuleAction A B := by
  letI : F.obj.Additive := rightExactFunctor_additive A B F
  exact
    { carrier := F.obj.obj (regularModule A)
      action :=
        ({ F.obj.mapEnd (regularModule A) with
            map_zero' := End.ext (F.obj.map_zero _ _)
            map_add' := fun _ _ ↦ End.ext F.obj.map_add } :
          End (regularModule A) →+* End (F.obj.obj (regularModule A))).comp
            (regularAction A) }

private def regularLinearEquiv (A : Type u) [Ring A] :
    A ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ where
  toFun := MulOpposite.op
  invFun := MulOpposite.unop
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private abbrev finiteFreeModule (A : Type u) [Ring A] (n : ℕ) : FPModule A :=
  ⟨ModuleCat.of Aᵐᵒᵖ (Fin n → Aᵐᵒᵖ),
    (finitelyPresentedModule_iff Aᵐᵒᵖ _).2 inferInstance⟩

private def finiteFreeCofan (A : Type u) [Ring A] (n : ℕ) :
    Cofan (fun _ : Fin n ↦ regularModule A) :=
  Cofan.mk (finiteFreeModule A n) (fun i ↦ InducedCategory.homMk (ModuleCat.ofHom
    ((LinearMap.single Aᵐᵒᵖ (fun _ : Fin n ↦ Aᵐᵒᵖ) i).comp
      (regularLinearEquiv A).toLinearMap)))

private def finiteFreeCofanIsColimit (A : Type u) [Ring A] (n : ℕ) :
    IsColimit (finiteFreeCofan A n) := by
  classical
  refine Cofan.IsColimit.mk _ (fun t ↦ InducedCategory.homMk (ModuleCat.ofHom
    (∑ i : Fin n, (t.inj i).hom.hom.comp
      ((regularLinearEquiv A).symm.toLinearMap.comp (LinearMap.proj i))))) ?_ ?_
  · intro t i
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    simp [finiteFreeCofan, Pi.single_apply, apply_ite]
  · intro t m hm
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    change (m.hom.hom : (Fin n → Aᵐᵒᵖ) →ₗ[Aᵐᵒᵖ] t.pt.obj) =
      ∑ i : Fin n, (t.inj i).hom.hom.comp
        ((regularLinearEquiv A).symm.toLinearMap.comp (LinearMap.proj i))
    apply LinearMap.pi_ext (φ := fun _ : Fin n ↦ Aᵐᵒᵖ)
    intro i a
    have hi : m.hom.hom (Pi.single i a) =
        (t.inj i).hom.hom ((regularLinearEquiv A).symm.toLinearMap a) :=
      congrArg (fun f ↦ f.hom.hom ((regularLinearEquiv A).symm.toLinearMap a)) (hm i)
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Pi.single_apply, apply_ite, map_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    convert hi using 1

private lemma finitePresentation_induction (A : Type u) [Ring A]
    (P : FPModule A → Prop) (hfree : ∀ n, P (finiteFreeModule A n))
    (hcoker : ∀ {X Y Z : FPModule A} (f : X ⟶ Y) (g : Y ⟶ Z)
      (h : f ≫ g = 0), IsColimit (CokernelCofork.ofπ g h) → P X → P Y → P Z)
    (M : FPModule A) : P M := by
  have := M.property
  obtain ⟨n, m, f, g, hf, hg⟩ := Module.FinitePresentation.exists_fin' Aᵐᵒᵖ M.obj
  let f' : finiteFreeModule A n ⟶ M := InducedCategory.homMk (ModuleCat.ofHom f)
  let g' : finiteFreeModule A m ⟶ finiteFreeModule A n :=
    InducedCategory.homMk (ModuleCat.ofHom g)
  have h : g' ≫ f' = 0 := by
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact hg.apply_apply_eq_zero x
  apply hcoker g' f' h _ (hfree m) (hfree n)
  apply isColimitOfReflects (ObjectProperty.ι _)
  refine (isColimitMapCoconeCoforkEquiv' (ObjectProperty.ι _) h).symm ?_
  exact ModuleCat.isColimitCokernelCofork (ModuleCat.ofHom g) (ModuleCat.ofHom f) hg hf

private noncomputable def actionHomFunctor {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] (K : ModuleAction A B) :
    B ⥤ ModuleCat.{max u w} Aᵐᵒᵖ :=
  preadditiveCoyonedaObj K.carrier ⋙
    ModuleCat.restrictScalars (RingHom.op K.action) ⋙
      ModuleCat.uliftFunctor.{u} Aᵐᵒᵖ

private lemma preadditiveCoyoneda_smul {B : Type v} [Category.{w} B] [Preadditive B]
    {X Y : B} (e : End X) (f : X ⟶ Y) :
    (MulOpposite.op e : (End X)ᵐᵒᵖ) • f = e.asHom ≫ f := rfl

private abbrev liftedModuleInclusion (A : Type u) [Ring A] :
    FPModule A ⥤ ModuleCat.{max u w} Aᵐᵒᵖ :=
  ObjectProperty.ι _ ⋙ ModuleCat.uliftFunctor.{w} Aᵐᵒᵖ

universe u₁ u₂ u₃ u₄

private noncomputable def regularLinearMapEquiv {R : Type u₁} [Ring R]
    {M : Type u₂} [AddCommGroup M] [Module R M] : (R →ₗ[R] M) ≃ M where
  toFun f := f 1
  invFun m := LinearMap.smulRight LinearMap.id m
  left_inv f := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.smulRight_apply, LinearMap.id_apply]
    simpa using (f.map_smul x (1 : R)).symm
  right_inv m := by simp

private def linearMapArrowCongr {R : Type u₁} [Ring R]
    {M₁ : Type u₂} {M₂ : Type u₃} {N₁ : Type u₄} {N₂ : Type*}
    [AddCommGroup M₁] [AddCommGroup M₂]
    [AddCommGroup N₁] [AddCommGroup N₂] [Module R M₁] [Module R M₂]
    [Module R N₁] [Module R N₂] (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : N₁ ≃ₗ[R] N₂) :
    (M₁ →ₗ[R] N₁) ≃ (M₂ →ₗ[R] N₂) where
  toFun f := e₂.toLinearMap.comp (f.comp e₁.symm.toLinearMap)
  invFun f := e₂.symm.toLinearMap.comp (f.comp e₁.toLinearMap)
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

private noncomputable def regularHom {A : Type u} [Ring A] {M : FPModule A}
    (x : M.obj) : regularModule A ⟶ M :=
  InducedCategory.homMk (ModuleCat.ofHom
    ((LinearMap.smulRight LinearMap.id x).comp (regularLinearEquiv A).toLinearMap))

private lemma regularHom_apply {A : Type u} [Ring A] {M : FPModule A}
    (x : M.obj) (a : A) : (regularHom x).hom.hom a = (MulOpposite.op a : Aᵐᵒᵖ) • x :=
  rfl

private lemma regularHom_add {A : Type u} [Ring A] {M : FPModule A}
    (x y : M.obj) : regularHom (x + y) = regularHom x + regularHom y := by
  apply InducedCategory.hom_ext
  apply ModuleCat.homAddEquiv.injective
  apply LinearMap.ext
  intro a
  change (regularHom (x + y)).hom.hom a =
    ((regularHom x).hom.hom + (regularHom y).hom.hom) a
  rw [LinearMap.add_apply, regularHom_apply]
  exact smul_add (MulOpposite.op a) x y

private lemma regularHom_smul {A : Type u} [Ring A] {M : FPModule A}
    (a : A) (x : M.obj) : regularHom ((MulOpposite.op a : Aᵐᵒᵖ) • x) =
      (regularEnd A a).asHom ≫ regularHom x := by
  apply InducedCategory.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  simp [regularHom, regularEnd, regularLinearEquiv, LinearMap.comp_apply,
    LinearMap.smulRight_apply, LinearMap.mulLeft_apply, MulOpposite.op_mul,
    mul_smul]

private lemma regularHom_comp {A : Type u} [Ring A] {M N : FPModule A}
    (f : M ⟶ N) (x : M.obj) :
    regularHom x ≫ f = regularHom (f.hom.hom x) := by
  apply InducedCategory.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change f.hom.hom ((MulOpposite.op a : Aᵐᵒᵖ) • x) =
    (MulOpposite.op a : Aᵐᵒᵖ) • f.hom.hom x
  exact f.hom.hom.map_smul (MulOpposite.op a) x

private lemma regularHom_one {A : Type u} [Ring A] :
    regularHom (1 : (regularModule A).obj) = 𝟙 (regularModule A) := by
  apply InducedCategory.hom_ext
  apply ModuleCat.hom_ext
  ext
  simp [regularHom, regularLinearEquiv, LinearMap.comp_apply,
    LinearMap.smulRight_apply]

private noncomputable def actionHomRegularEquiv {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] (K : ModuleAction A B) (X : B) :
    ((liftedModuleInclusion A).obj (regularModule A) ⟶ (actionHomFunctor K).obj X) ≃
      (K.carrier ⟶ X) := by
  let H := (preadditiveCoyonedaObj K.carrier ⋙
    ModuleCat.restrictScalars (RingHom.op K.action)).obj X
  let e₁ : ULift.{w} A ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ :=
    (ULift.moduleEquiv : ULift.{w} A ≃ₗ[Aᵐᵒᵖ] A).trans (regularLinearEquiv A)
  let e₂ : ULift.{u} H ≃ₗ[Aᵐᵒᵖ] H := ULift.moduleEquiv
  exact ModuleCat.homEquiv.trans
    ((linearMapArrowCongr e₁ e₂).trans
    ((regularLinearMapEquiv (R := Aᵐᵒᵖ) (M := H)).trans
      (Equiv.refl (K.carrier ⟶ X))))

private lemma actionHomRegularEquiv_apply {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] (K : ModuleAction A B) (X : B)
    (f : (liftedModuleInclusion A).obj (regularModule A) ⟶ (actionHomFunctor K).obj X) :
    actionHomRegularEquiv K X f = (f.hom (ULift.up (1 : A))).down :=
  rfl

private noncomputable def actionHomRegularCorepresentableBy {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] (K : ModuleAction A B) :
    (actionHomFunctor K ⋙ coyoneda.obj (Opposite.op
      ((liftedModuleInclusion A).obj (regularModule A)))).CorepresentableBy K.carrier where
  homEquiv := (actionHomRegularEquiv K _).symm
  homEquiv_comp f g := by
    apply (actionHomRegularEquiv K _).injective
    change _ = (actionHomRegularEquiv K _) _
    simp only [Equiv.apply_symm_apply]
    change g ≫ f = (((actionHomRegularEquiv K _).symm g).hom ⟨(1 : A)⟩).down ≫ f
    exact congrArg (· ≫ f) ((actionHomRegularEquiv K _).apply_symm_apply g).symm

/-- The canonical element of `Hom(K, K)` is sent to the identity by the unit at `1`. -/
private lemma actionHomRegular_unit_one {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] (K : ModuleAction A B) :
    ((actionHomRegularCorepresentableBy K).homEquiv (𝟙 K.carrier)).hom (ULift.up (1 : A)) =
      ULift.up (𝟙 K.carrier) := by
  apply ULift.ext
  change actionHomRegularEquiv K K.carrier
    ((actionHomRegularCorepresentableBy K).homEquiv (𝟙 K.carrier)) = 𝟙 K.carrier
  simp [actionHomRegularCorepresentableBy]

private noncomputable def unitModuleHom {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (F : FPModule A ⥤ᵣ B) (M : FPModule A) :
    (liftedModuleInclusion A).obj M ⟶
      (actionHomFunctor (evaluationObject A B F)).obj (F.obj.obj M) := by
  let K := evaluationObject A B F
  let H := (preadditiveCoyonedaObj K.carrier ⋙
    ModuleCat.restrictScalars (RingHom.op K.action)).obj (F.obj.obj M)
  letI : F.obj.Additive := rightExactFunctor_additive A B F
  let φ : M.obj →ₗ[Aᵐᵒᵖ] H :=
    { toFun := fun x ↦ F.obj.map (regularHom x)
      map_add' := by
        intro x y
        rw [regularHom_add, F.obj.map_add]
        rfl
      map_smul' := by
        intro r x
        rw [← MulOpposite.op_unop r, regularHom_smul, F.obj.map_comp]
        rfl }
  let e₁ : ULift.{w} M.obj ≃ₗ[Aᵐᵒᵖ] M.obj := ULift.moduleEquiv
  let e₂ : ULift.{u} H ≃ₗ[Aᵐᵒᵖ] H := ULift.moduleEquiv
  exact ModuleCat.ofHom (e₂.symm.toLinearMap.comp (φ.comp e₁.toLinearMap))

private lemma actionHom_leftAdjointObjIsDefined {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (K : ModuleAction A B) (M : FPModule A) :
    (actionHomFunctor K).leftAdjointObjIsDefined ((liftedModuleInclusion A).obj M) := by
  have : HasCoequalizers B := Preadditive.hasCoequalizers_of_hasCokernels
  have := fpModuleInclusion_preservesFiniteColimits A
  have key {J : Type} [SmallCategory J] [FinCategory J] [HasColimitsOfShape J B]
      {R : J ⥤ FPModule A} {c : Cocone R} (hc : IsColimit c)
      (h : ∀ j, (actionHomFunctor K).leftAdjointObjIsDefined
        ((liftedModuleInclusion A).obj (R.obj j))) :
      (actionHomFunctor K).leftAdjointObjIsDefined ((liftedModuleInclusion A).obj c.pt) :=
    Functor.leftAdjointObjIsDefined_of_isColimit
      (isColimitOfPreserves (ModuleCat.uliftFunctor.{w} Aᵐᵒᵖ)
        (isColimitOfPreserves (ObjectProperty.ι _) hc)) h
  refine finitePresentation_induction A
    (fun M ↦ (actionHomFunctor K).leftAdjointObjIsDefined ((liftedModuleInclusion A).obj M))
    (fun n ↦ key (finiteFreeCofanIsColimit A n) fun _ ↦
      (actionHomRegularCorepresentableBy K).isCorepresentable)
    (fun f g h hc hX hY ↦ key hc ?_) M
  rintro (_ | _)
  exacts [hX, hY]

private noncomputable abbrev actionTensorSource {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (K : ModuleAction A B) : FPModule A ⥤ (actionHomFunctor K).PartialLeftAdjointSource :=
  ObjectProperty.lift (actionHomFunctor K).leftAdjointObjIsDefined
    (liftedModuleInclusion A) (actionHom_leftAdjointObjIsDefined K)

@[implicit_reducible]
private noncomputable def actionTensorFunctor {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (K : ModuleAction A B) : FPModule A ⥤ B :=
  actionTensorSource K ⋙ (actionHomFunctor K).partialLeftAdjoint

private noncomputable def partialLeftAdjointMapCoconeIsColimit
    {C : Type*} {D : Type*} [Category C] [Category D] (H : D ⥤ C)
    {J : Type*} [Category J] {R : J ⥤ H.PartialLeftAdjointSource} {c : Cocone R}
    (hc : IsColimit ((ObjectProperty.ι _).mapCocone c)) :
    IsColimit (H.partialLeftAdjoint.mapCocone c) := by
  let d (s : Cocone (R ⋙ H.partialLeftAdjoint)) : Cocone (R ⋙ ObjectProperty.ι _) :=
    ⟨H.obj s.pt,
      { app := fun j ↦ H.partialLeftAdjointHomEquiv (s.ι.app j)
        naturality := fun j j' f ↦ by
          dsimp
          rw [Category.comp_id]
          exact (H.partialLeftAdjointHomEquiv_map_comp (R.map f) (s.ι.app j')).symm.trans
            (congrArg H.partialLeftAdjointHomEquiv (s.w f)) }⟩
  refine
    { desc := fun s ↦ H.partialLeftAdjointHomEquiv.symm (hc.desc (d s))
      fac := ?_
      uniq := ?_ }
  · intro s j
    apply H.partialLeftAdjointHomEquiv.injective
    change H.partialLeftAdjointHomEquiv
      (H.partialLeftAdjointMap (c.ι.app j) ≫ _) = _
    rw [H.partialLeftAdjointHomEquiv_map_comp, Equiv.apply_symm_apply]
    exact hc.fac (d s) j
  · intro s m hm
    apply H.partialLeftAdjointHomEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply hc.hom_ext
    intro j
    rw [hc.fac]
    change (c.ι.app j).hom ≫ H.partialLeftAdjointHomEquiv m = _
    exact (H.partialLeftAdjointHomEquiv_map_comp (c.ι.app j) m).symm.trans
      (congrArg H.partialLeftAdjointHomEquiv (hm j))

private lemma actionTensorFunctor_preservesFiniteColimits {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (K : ModuleAction A B) : PreservesFiniteColimits (actionTensorFunctor K) := by
  have : PreservesFiniteColimits (finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι :=
    fpModuleInclusion_preservesFiniteColimits A
  have : PreservesFiniteColimits
      ((finitelyPresentedModule.{u, u} Aᵐᵒᵖ).ι ⋙ ModuleCat.uliftFunctor.{w} Aᵐᵒᵖ) :=
    comp_preservesFiniteColimits _ _
  refine ⟨fun J _ _ ↦ ⟨?_⟩⟩
  intro R
  refine ⟨fun {c} hc ↦ ⟨?_⟩⟩
  exact partialLeftAdjointMapCoconeIsColimit (actionHomFunctor K)
    (c := (actionTensorSource K).mapCocone c)
    (isColimitOfPreserves (liftedModuleInclusion A) hc)

private noncomputable def actionTensorRightExactFunctor {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (K : ModuleAction A B) : FPModule A ⥤ᵣ B :=
  ⟨actionTensorFunctor K,
    actionTensorFunctor_preservesFiniteColimits K⟩

private noncomputable def actionHomNatTransCore {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] {K L : ModuleAction A B}
    (f : ModuleAction.Hom K L) :
    (preadditiveCoyonedaObj L.carrier ⋙
      ModuleCat.restrictScalars (RingHom.op L.action)) ⟶
      (preadditiveCoyonedaObj K.carrier ⋙
      ModuleCat.restrictScalars (RingHom.op K.action)) :=
    { app := fun X =>
        let M : ModuleCat Aᵐᵒᵖ :=
          (ModuleCat.restrictScalars (RingHom.op L.action)).obj
            ((preadditiveCoyonedaObj L.carrier).obj X)
        let N : ModuleCat Aᵐᵒᵖ :=
          (ModuleCat.restrictScalars (RingHom.op K.action)).obj
            ((preadditiveCoyonedaObj K.carrier).obj X)
        letI : Module Aᵐᵒᵖ (L.carrier ⟶ X) := M.isModule
        letI : Module Aᵐᵒᵖ (K.carrier ⟶ X) := N.isModule
        let φ : (L.carrier ⟶ X) →ₗ[Aᵐᵒᵖ] (K.carrier ⟶ X) :=
          { toFun := fun g => f.hom ≫ g
            map_add' := fun _ _ => Preadditive.comp_add _ _ _ _ _ _
            map_smul' := by
              intro r g
              change f.hom ≫ (MulOpposite.op (L.action r.unop) • g) =
                MulOpposite.op (K.action r.unop) • (f.hom ≫ g)
              rw [preadditiveCoyoneda_smul, preadditiveCoyoneda_smul, ← Category.assoc,
                ← Category.assoc, f.comm] }
        ModuleCat.ofHom (X := M) (Y := N) φ
      naturality := by
        intro X Y g
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro h
        change f.hom ≫ (h ≫ g) = (f.hom ≫ h) ≫ g
        exact (Category.assoc _ _ _).symm }

private noncomputable def actionHomNatTrans {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] {K L : ModuleAction A B}
    (f : ModuleAction.Hom K L) : actionHomFunctor L ⟶ actionHomFunctor K :=
  Functor.whiskerRight (actionHomNatTransCore f)
    (ModuleCat.uliftFunctor.{u} Aᵐᵒᵖ)

private lemma actionHomNatTransCore_id {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] (K : ModuleAction A B) :
    actionHomNatTransCore (𝟙 K) = 𝟙 _ := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  dsimp [actionHomNatTransCore]
  change (𝟙 K.carrier) ≫ x = x
  exact Category.id_comp x

private lemma actionHomNatTransCore_comp {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] {K L P : ModuleAction A B}
    (f : K ⟶ L) (g : L ⟶ P) :
    actionHomNatTransCore (f ≫ g) = actionHomNatTransCore g ≫ actionHomNatTransCore f := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  dsimp [actionHomNatTransCore]
  change (f.hom ≫ g.hom) ≫ x = f.hom ≫ (g.hom ≫ x)
  exact Category.assoc _ _ _

private lemma actionHomNatTrans_id {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] (K : ModuleAction A B) :
    actionHomNatTrans (𝟙 K) = 𝟙 (actionHomFunctor K) := by
  change Functor.whiskerRight (actionHomNatTransCore (𝟙 K))
      (ModuleCat.uliftFunctor.{u} Aᵐᵒᵖ) =
    𝟙 ((preadditiveCoyonedaObj K.carrier ⋙
      ModuleCat.restrictScalars (RingHom.op K.action)) ⋙
        ModuleCat.uliftFunctor.{u} Aᵐᵒᵖ)
  rw [actionHomNatTransCore_id, Functor.whiskerRight_id']

private lemma actionHomNatTrans_comp {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] {K L P : ModuleAction A B}
    (f : K ⟶ L) (g : L ⟶ P) :
    actionHomNatTrans (f ≫ g) = actionHomNatTrans g ≫ actionHomNatTrans f := by
  change Functor.whiskerRight (actionHomNatTransCore (f ≫ g))
      (ModuleCat.uliftFunctor.{u} Aᵐᵒᵖ) =
    Functor.whiskerRight (actionHomNatTransCore g)
        (ModuleCat.uliftFunctor.{u} Aᵐᵒᵖ) ≫
      Functor.whiskerRight (actionHomNatTransCore f)
        (ModuleCat.uliftFunctor.{u} Aᵐᵒᵖ)
  rw [actionHomNatTransCore_comp, Functor.whiskerRight_comp]

private noncomputable def actionTensorMapApp {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    {K L : ModuleAction A B} (f : ModuleAction.Hom K L) (M : FPModule A) :
    (actionTensorFunctor K).obj M ⟶ (actionTensorFunctor L).obj M := by
  let HK := actionHomFunctor K
  let HL := actionHomFunctor L
  let SK := actionTensorSource K
  let SL := actionTensorSource L
  let YL := HL.partialLeftAdjointObj (SL.obj M)
  let u : (SL.obj M).obj ⟶ HL.obj YL :=
    HL.partialLeftAdjointHomEquiv (𝟙 YL)
  exact HK.partialLeftAdjointHomEquiv.symm
    (u ≫ (actionHomNatTrans f).app YL)

/-- Under the partial adjunction bijection, `actionTensorMapApp f M` is the unit of `L` at `M`
followed by the component of `actionHomNatTrans f`. -/
private lemma partialLeftAdjointHomEquiv_actionTensorMapApp {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    {K L : ModuleAction A B} (f : ModuleAction.Hom K L) (M : FPModule A) :
    (actionHomFunctor K).partialLeftAdjointHomEquiv (actionTensorMapApp f M) =
      (actionHomFunctor L).partialLeftAdjointHomEquiv (X := (actionTensorSource L).obj M)
          (𝟙 _) ≫ (actionHomNatTrans f).app _ :=
  Equiv.apply_symm_apply _ _

/-- The unit of the partial adjunction followed by `H.map a` is the transpose of `a`. -/
private lemma partialLeftAdjointHomEquiv_id_comp_map {C : Type*} {D : Type*} [Category C]
    [Category D] (H : D ⥤ C) {X : H.PartialLeftAdjointSource} {Y : D}
    (a : H.partialLeftAdjointObj X ⟶ Y) :
    H.partialLeftAdjointHomEquiv (𝟙 _) ≫ H.map a = H.partialLeftAdjointHomEquiv a := by
  rw [← H.partialLeftAdjointHomEquiv_comp, Category.id_comp]

private noncomputable def actionTensorMap {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    {K L : ModuleAction A B} (f : ModuleAction.Hom K L) :
    actionTensorFunctor K ⟶ actionTensorFunctor L where
  app := actionTensorMapApp f
  naturality := by
    intro M N g
    let HK := actionHomFunctor K
    let HL := actionHomFunctor L
    let q := HL.partialLeftAdjointMap ((actionTensorSource L).map g)
    have hunit : HL.partialLeftAdjointHomEquiv (𝟙 _) ≫ HL.map q =
        ((actionTensorSource L).map g).hom ≫ HL.partialLeftAdjointHomEquiv (𝟙 _) :=
      (partialLeftAdjointHomEquiv_id_comp_map HL q).trans (HL.partialLeftAdjointHomEquiv_map _)
    apply HK.partialLeftAdjointHomEquiv.injective
    change HK.partialLeftAdjointHomEquiv
        ((actionTensorFunctor K).map g ≫ actionTensorMapApp f N) =
      HK.partialLeftAdjointHomEquiv (actionTensorMapApp f M ≫ (actionTensorFunctor L).map g)
    erw [HK.partialLeftAdjointHomEquiv_map_comp, HK.partialLeftAdjointHomEquiv_comp,
      partialLeftAdjointHomEquiv_actionTensorMapApp, partialLeftAdjointHomEquiv_actionTensorMapApp]
    erw [Category.assoc, ← (actionHomNatTrans f).naturality q, reassoc_of% hunit]
    rfl

private lemma actionTensorMapApp_id {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (K : ModuleAction A B) (M : FPModule A) :
    actionTensorMapApp (𝟙 K) M = 𝟙 ((actionTensorFunctor K).obj M) := by
  apply (actionHomFunctor K).partialLeftAdjointHomEquiv.injective
  rw [partialLeftAdjointHomEquiv_actionTensorMapApp, actionHomNatTrans_id]
  simp
  rfl

private lemma actionTensorMapApp_comp {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    {K L P : ModuleAction A B} (f : K ⟶ L) (g : L ⟶ P) (M : FPModule A) :
    actionTensorMapApp f M ≫ actionTensorMapApp g M =
      actionTensorMapApp (f ≫ g) M := by
  apply (actionHomFunctor K).partialLeftAdjointHomEquiv.injective
  erw [Functor.partialLeftAdjointHomEquiv_comp, partialLeftAdjointHomEquiv_actionTensorMapApp f M,
    partialLeftAdjointHomEquiv_actionTensorMapApp (f ≫ g) M, actionHomNatTrans_comp,
    Category.assoc, ← (actionHomNatTrans f).naturality, ← Category.assoc,
    partialLeftAdjointHomEquiv_id_comp_map, partialLeftAdjointHomEquiv_actionTensorMapApp g M]
  rfl

private noncomputable def actionTensorRightExactFunctor' {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B] :
    ModuleAction A B ⥤ (FPModule A ⥤ᵣ B) where
  obj := actionTensorRightExactFunctor
  map f := InducedCategory.homMk (actionTensorMap f)
  map_id K := by
    apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext M
    exact actionTensorMapApp_id K M
  map_comp f g := by
    apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext M
    exact (actionTensorMapApp_comp f g M).symm

private noncomputable def actionTensorRegularIso {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (K : ModuleAction A B) : (actionTensorFunctor K).obj (regularModule A) ≅ K.carrier := by
  letI : (actionHomFunctor K ⋙ coyoneda.obj (Opposite.op
      ((liftedModuleInclusion A).obj (regularModule A)))).IsCorepresentable :=
    actionHom_leftAdjointObjIsDefined K (regularModule A)
  exact (actionHomFunctor K ⋙ coyoneda.obj (Opposite.op
    ((liftedModuleInclusion A).obj (regularModule A)))).corepresentableBy.uniqueUpToIso
      (actionHomRegularCorepresentableBy K)

private lemma corepresentable_uniqueUpToIso_homEquiv {C : Type*} [Category C]
    {R : C ⥤ Type*} {X Y : C} (e : R.CorepresentableBy X)
    (e' : R.CorepresentableBy Y) :
    e.homEquiv (e.uniqueUpToIso e').hom = e'.homEquiv (𝟙 Y) := by
  rw [Functor.CorepresentableBy.uniqueUpToIso_hom]
  simp only [Coyoneda.fullyFaithful_preimage]
  change e.homEquiv (e.homEquiv.symm (e'.homEquiv (𝟙 Y))) = _
  exact Equiv.apply_symm_apply _ _

private lemma actionTensorRegularIso_homEquiv {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (K : ModuleAction A B) :
    (actionHomFunctor K).partialLeftAdjointHomEquiv (actionTensorRegularIso K).hom =
      (actionHomRegularCorepresentableBy K).homEquiv (𝟙 K.carrier) := by
  have : (actionHomFunctor K ⋙ coyoneda.obj (Opposite.op
      ((liftedModuleInclusion A).obj (regularModule A)))).IsCorepresentable :=
    actionHom_leftAdjointObjIsDefined K (regularModule A)
  let R := actionHomFunctor K ⋙
    coyoneda.obj (Opposite.op ((liftedModuleInclusion A).obj (regularModule A)))
  let e₁ : R.CorepresentableBy ((actionTensorFunctor K).obj (regularModule A)) := by
    let := actionHom_leftAdjointObjIsDefined K (regularModule A)
    exact R.corepresentableBy
  change e₁.homEquiv (e₁.uniqueUpToIso (actionHomRegularCorepresentableBy K)).hom = _
  exact corepresentable_uniqueUpToIso_homEquiv e₁ (actionHomRegularCorepresentableBy K)

private lemma actionTensorRegularIso_comm {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (K : ModuleAction A B) (a : A) :
    (actionTensorFunctor K).map (regularEnd A a).asHom ≫ (actionTensorRegularIso K).hom =
      (actionTensorRegularIso K).hom ≫ (K.action a).asHom := by
  let H := actionHomFunctor K
  let L := actionTensorSource K
  apply H.partialLeftAdjointHomEquiv.injective
  erw [H.partialLeftAdjointHomEquiv_map_comp, H.partialLeftAdjointHomEquiv_comp,
    actionTensorRegularIso_homEquiv]
  apply (actionHomRegularEquiv K K.carrier).injective
  rw [actionHomRegularEquiv_apply, actionHomRegularEquiv_apply]
  let u := (actionHomRegularCorepresentableBy K).homEquiv (𝟙 K.carrier)
  let x₁ : (liftedModuleInclusion A).obj (regularModule A) := ULift.up (1 : A)
  let xa : (liftedModuleInclusion A).obj (regularModule A) := ULift.up a
  have hux : u.hom x₁ = ULift.up (𝟙 K.carrier) := actionHomRegular_unit_one K
  have hsmul :
      (MulOpposite.op a • u.hom x₁).down =
        (RingHom.op K.action (MulOpposite.op a) : (End K.carrier)ᵐᵒᵖ) • (u.hom x₁).down := by
    rfl
  have ha : (u.hom xa).down = (K.action a).asHom := by
    have hx : xa = (MulOpposite.op a : Aᵐᵒᵖ) • x₁ := by
      change ULift.up a = (MulOpposite.op a : Aᵐᵒᵖ) • ULift.up (1 : A)
      ext
      change a = (MulOpposite.op a : Aᵐᵒᵖ) • (1 : A)
      rw [op_smul_eq_mul]
      simp
    have hfirst : (u.hom xa).down = (MulOpposite.op a • u.hom x₁).down := by
      rw [hx]
      exact congrArg ULift.down (u.hom.map_smul _ x₁)
    have hsecond : (MulOpposite.op a • u.hom x₁).down = (K.action a).asHom := by
      rw [hsmul, hux]
      change (MulOpposite.op (K.action a) : (End K.carrier)ᵐᵒᵖ) •
        (𝟙 K.carrier) = _
      rw [preadditiveCoyoneda_smul]
      simp
    exact hfirst.trans hsecond
  change (u.hom (((L.map (regularEnd A a).asHom).hom.hom) x₁)).down =
    ((H.map (K.action a).asHom).hom (u.hom x₁)).down
  have hL : ((L.map (regularEnd A a).asHom).hom.hom) x₁ = xa := by
    change ULift.up ((regularEnd A a).asHom.hom.hom (1 : A)) = ULift.up a
    congr 1
    simp [regularEnd, LinearMap.mulLeft_apply]
  rw [hL, ha, hux]
  exact (Category.id_comp (K.action a).asHom).symm

private def moduleActionIsoOfIso {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] {K L : ModuleAction A B}
    (e : K.carrier ≅ L.carrier)
    (h : ∀ a, (K.action a).asHom ≫ e.hom = e.hom ≫ (L.action a).asHom) : K ≅ L where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, fun a ↦ by rw [Iso.comp_inv_eq, Category.assoc, h a, Iso.inv_hom_id_assoc]⟩
  hom_inv_id := ModuleAction.Hom.ext e.hom_inv_id
  inv_hom_id := ModuleAction.Hom.ext e.inv_hom_id

private noncomputable def actionTensorUnitIsoObj {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (K : ModuleAction A B) :
    K ≅ (evaluationFunctor A B).obj (actionTensorRightExactFunctor K) := by
  let e := actionTensorRegularIso K
  apply moduleActionIsoOfIso e.symm
  intro a
  change (K.action a).asHom ≫ e.inv = e.inv ≫ (actionTensorFunctor K).map (regularEnd A a).asHom
  rw [Iso.comp_inv_eq, Category.assoc, actionTensorRegularIso_comm K a, Iso.inv_hom_id_assoc]

private lemma actionHomRegularCanonical_naturality {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] {K L : ModuleAction A B}
    (f : K ⟶ L) :
    (actionHomRegularCorepresentableBy L).homEquiv (𝟙 L.carrier) ≫
        (actionHomNatTrans f).app L.carrier =
      (actionHomRegularCorepresentableBy K).homEquiv (𝟙 K.carrier) ≫
        (actionHomFunctor K).map f.hom := by
  let uL := (actionHomRegularCorepresentableBy L).homEquiv (𝟙 L.carrier)
  let uK := (actionHomRegularCorepresentableBy K).homEquiv (𝟙 K.carrier)
  let x₁ : (liftedModuleInclusion A).obj (regularModule A) := ULift.up (1 : A)
  have huL' : uL.hom x₁ = ULift.up (𝟙 L.carrier) := actionHomRegular_unit_one L
  have huK' : uK.hom x₁ = ULift.up (𝟙 K.carrier) := actionHomRegular_unit_one K
  change uL ≫ (actionHomNatTrans f).app L.carrier =
    uK ≫ (actionHomFunctor K).map f.hom
  apply (actionHomRegularEquiv K L.carrier).injective
  change ((uL ≫ (actionHomNatTrans f).app L.carrier).hom x₁).down =
    ((uK ≫ (actionHomFunctor K).map f.hom).hom x₁).down
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply, huL', huK']
  have hpre : ((actionHomNatTrans f).app L.carrier).hom
      (ULift.up (𝟙 L.carrier)) = ULift.up (f.hom ≫ 𝟙 L.carrier) := by
    dsimp [actionHomNatTrans, Functor.whiskerRight, ModuleCat.uliftFunctor,
      actionHomNatTransCore]
    rfl
  have hpost : ((actionHomFunctor K).map f.hom).hom
      (ULift.up (𝟙 K.carrier)) = ULift.up (𝟙 K.carrier ≫ f.hom) := by
    dsimp [actionHomFunctor, ModuleCat.uliftFunctor, ModuleCat.restrictScalars,
      ModuleCat.RestrictScalars.map', preadditiveCoyonedaObj]
    rfl
  change (((actionHomNatTrans f).app L.carrier).hom
      (ULift.up (𝟙 L.carrier))).down =
    (((actionHomFunctor K).map f.hom).hom
      (ULift.up (𝟙 K.carrier))).down
  rw [hpre, hpost]
  change f.hom ≫ 𝟙 L.carrier = 𝟙 K.carrier ≫ f.hom
  simp

private lemma actionTensorMapApp_regular_naturality {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    {K L : ModuleAction A B} (f : K ⟶ L) :
    actionTensorMapApp f (regularModule A) ≫ (actionTensorRegularIso L).hom =
      (actionTensorRegularIso K).hom ≫ f.hom := by
  apply (actionHomFunctor K).partialLeftAdjointHomEquiv.injective
  erw [Functor.partialLeftAdjointHomEquiv_comp, partialLeftAdjointHomEquiv_actionTensorMapApp,
    Category.assoc, ← (actionHomNatTrans f).naturality, ← Category.assoc,
    partialLeftAdjointHomEquiv_id_comp_map, actionTensorRegularIso_homEquiv L,
    actionHomRegularCanonical_naturality f, Functor.partialLeftAdjointHomEquiv_comp,
    actionTensorRegularIso_homEquiv K]

private noncomputable def actionTensorUnitIso {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B] :
    𝟭 (ModuleAction A B) ≅
      actionTensorRightExactFunctor' (A := A) (B := B) ⋙ evaluationFunctor A B :=
  NatIso.ofComponents actionTensorUnitIsoObj (by
    intro K L f
    apply ModuleAction.Hom.ext
    let eK := actionTensorRegularIso K
    let eL := actionTensorRegularIso L
    let t := actionTensorMapApp f (regularModule A)
    change f.hom ≫ eL.inv = eK.inv ≫ t
    rw [Iso.comp_inv_eq, Category.assoc, actionTensorMapApp_regular_naturality f]
    change f.hom = eK.inv ≫ eK.hom ≫ f.hom
    simp)

private lemma unitModuleHom_apply {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (F : FPModule A ⥤ᵣ B) (M : FPModule A) (x : ULift.{w} M.obj) :
    ((unitModuleHom F M).hom x).down = F.obj.map (regularHom x.down) := by
  change ULift.down
    (ULift.up (F.obj.map (regularHom x.down)) :
      ULift.{u} (F.obj.obj (regularModule A) ⟶ F.obj.obj M)) = _
  rfl

private lemma unitModuleHom_naturality {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (F : FPModule A ⥤ᵣ B) {M N : FPModule A} (f : M ⟶ N) :
    unitModuleHom F M ≫
        (actionHomFunctor (evaluationObject A B F)).map (F.obj.map f) =
      (liftedModuleInclusion A).map f ≫ unitModuleHom F N := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  change F.obj.map (regularHom x.down) ≫ F.obj.map f =
    F.obj.map (regularHom (f.hom.hom x.down))
  rw [← F.obj.map_comp, regularHom_comp]

private noncomputable def actionTensorComparisonHom {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
  (F : FPModule A ⥤ᵣ B) (M : FPModule A) :
  (actionTensorFunctor (evaluationObject A B F)).obj M ⟶ F.obj.obj M :=
  (actionHomFunctor (evaluationObject A B F)).partialLeftAdjointHomEquiv.symm
    (unitModuleHom F M)

private noncomputable def actionTensorComparison {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
  (F : FPModule A ⥤ᵣ B) :
    actionTensorFunctor (evaluationObject A B F) ⟶ F.obj :=
  { app := actionTensorComparisonHom F
    naturality := by
      intro M N f
      let H := actionHomFunctor (evaluationObject A B F)
      dsimp [actionTensorComparisonHom, actionTensorFunctor, Functor.partialLeftAdjoint]
      apply H.partialLeftAdjointHomEquiv.injective
      rw [H.partialLeftAdjointHomEquiv_map_comp,
        H.partialLeftAdjointHomEquiv_comp]
      dsimp [H]
      simp only [Equiv.apply_symm_apply]
      change (liftedModuleInclusion A).map f ≫ unitModuleHom F N =
        unitModuleHom F M ≫
          (actionHomFunctor (evaluationObject A B F)).map (F.obj.map f)
      exact (unitModuleHom_naturality F f).symm }

/-- The comparison map corresponds to `unitModuleHom` under the partial adjunction bijection. -/
private lemma partialLeftAdjointHomEquiv_actionTensorComparison {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (F : FPModule A ⥤ᵣ B) (M : FPModule A) :
    (actionHomFunctor (evaluationObject A B F)).partialLeftAdjointHomEquiv
      ((actionTensorComparison F).app M) = unitModuleHom F M :=
  Equiv.apply_symm_apply _ _

private lemma unitModuleHom_regular_equiv {A : Type u} {B : Type v} [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (F : FPModule A ⥤ᵣ B) :
    unitModuleHom F (regularModule A) =
      (actionHomRegularEquiv (evaluationObject A B F)
        (F.obj.obj (regularModule A))).symm (𝟙 (F.obj.obj (regularModule A))) := by
  unfold evaluationObject
  apply (actionHomRegularEquiv (evaluationObject A B F)
    (F.obj.obj (regularModule A))).injective
  rw [actionHomRegularEquiv_apply, unitModuleHom_apply, regularHom_one, F.obj.map_id]
  unfold evaluationObject
  exact (Equiv.apply_symm_apply _ _).symm

private lemma actionTensorComparison_regular_isIso {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (F : FPModule A ⥤ᵣ B) :
    IsIso ((actionTensorComparison F).app (regularModule A)) := by
  have : (actionHomFunctor (evaluationObject A B F) ⋙ coyoneda.obj (Opposite.op
      ((liftedModuleInclusion A).obj (regularModule A)))).IsCorepresentable :=
    actionHom_leftAdjointObjIsDefined (evaluationObject A B F) (regularModule A)
  have hunit : unitModuleHom F (regularModule A) =
      (actionHomRegularCorepresentableBy (evaluationObject A B F)).homEquiv
        (𝟙 (F.obj.obj (regularModule A))) := by
    simpa [actionHomRegularCorepresentableBy] using unitModuleHom_regular_equiv F
  have h : actionTensorComparisonHom F (regularModule A) =
      (actionTensorRegularIso (evaluationObject A B F)).hom := by
    apply (actionHomFunctor (evaluationObject A B F)).partialLeftAdjointHomEquiv.injective
    unfold actionTensorComparisonHom
    simp only [Equiv.apply_symm_apply]
    exact hunit.trans (actionTensorRegularIso_homEquiv (evaluationObject A B F)).symm
  change IsIso (actionTensorComparisonHom F (regularModule A))
  rw [h]
  infer_instance

private lemma actionTensorComparison_app_isIso {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (F : FPModule A ⥤ᵣ B) (M : FPModule A) :
    IsIso ((actionTensorComparison F).app M) := by
  let K := evaluationObject A B F
  let η := actionTensorComparison F
  have : PreservesFiniteColimits (actionTensorFunctor K) :=
    actionTensorFunctor_preservesFiniteColimits K
  have : PreservesFiniteColimits F.obj := F.property
  have key {J : Type} [SmallCategory J] [FinCategory J] {D : J ⥤ FPModule A} {c : Cocone D}
      (hc : IsColimit c) (h : ∀ j, IsIso (η.app (D.obj j))) : IsIso (η.app c.pt) := by
    have : ∀ j, IsIso ((Functor.whiskerLeft D η).app j) := h
    have : IsIso (Functor.whiskerLeft D η) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit D η c hc
  refine finitePresentation_induction A (fun M ↦ IsIso (η.app M))
    (fun n ↦ key (finiteFreeCofanIsColimit A n) fun _ ↦
      actionTensorComparison_regular_isIso F)
    (fun f g hfg hc hX hY ↦ key hc ?_) M
  rintro (_ | _)
  exacts [hX, hY]

private lemma unitModuleHom_naturality_rightExactMap {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (F G : FPModule A ⥤ᵣ B) (τ : F ⟶ G) (M : FPModule A) :
    unitModuleHom G M ≫
        (actionHomNatTrans ((evaluationFunctor A B).map τ)).app (G.obj.obj M) =
      unitModuleHom F M ≫
        (actionHomFunctor (evaluationObject A B F)).map (τ.hom.app M) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  change τ.hom.app (regularModule A) ≫ G.obj.map (regularHom x.down) =
    F.obj.map (regularHom x.down) ≫ τ.hom.app M
  exact (τ.hom.naturality (regularHom x.down)).symm

private noncomputable def actionTensorComparisonIsoObj {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (F : FPModule A ⥤ᵣ B) :
    (actionTensorRightExactFunctor' (A := A) (B := B)).obj
      ((evaluationFunctor A B).obj F) ≅ F := by
  let η := actionTensorComparison F
  let T := (actionTensorRightExactFunctor' (A := A) (B := B)).obj
    ((evaluationFunctor A B).obj F)
  let e : T.obj ≅ F.obj :=
    NatIso.ofComponents (fun M => by
      let h : IsIso (η.app M) := by
        dsimp [η]
        exact actionTensorComparison_app_isIso F M
      exact
        { hom := η.app M
          inv := Classical.choose h.out
          hom_inv_id := (Classical.choose_spec h.out).1
          inv_hom_id := (Classical.choose_spec h.out).2 }) (by
      intro M N f
      exact η.naturality f)
  exact InducedCategory.isoMk e

private lemma actionTensorComparison_naturality_rightExactMap {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
    (F G : FPModule A ⥤ᵣ B) (τ : F ⟶ G) (M : FPModule A) :
    actionTensorMapApp ((evaluationFunctor A B).map τ) M ≫
        (actionTensorComparison G).app M =
      (actionTensorComparison F).app M ≫ τ.hom.app M := by
  let HK := actionHomFunctor (evaluationObject A B F)
  let α := (evaluationFunctor A B).map τ
  apply HK.partialLeftAdjointHomEquiv.injective
  erw [Functor.partialLeftAdjointHomEquiv_comp, partialLeftAdjointHomEquiv_actionTensorMapApp,
    Category.assoc, ← (actionHomNatTrans α).naturality, ← Category.assoc,
    partialLeftAdjointHomEquiv_id_comp_map, partialLeftAdjointHomEquiv_actionTensorComparison,
    Functor.partialLeftAdjointHomEquiv_comp, partialLeftAdjointHomEquiv_actionTensorComparison]
  exact unitModuleHom_naturality_rightExactMap F G τ M

private noncomputable def actionTensorComparisonIso {A : Type u} {B : Type v}
    [Ring A] [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B] :
    (evaluationFunctor A B) ⋙ actionTensorRightExactFunctor' (A := A) (B := B) ≅
      𝟭 (FPModule A ⥤ᵣ B) :=
  NatIso.ofComponents actionTensorComparisonIsoObj (by
    intro F G τ
    apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext M
    exact actionTensorComparison_naturality_rightExactMap F G τ M)

/-- Evaluation on the rank-one free module, with its natural action, classifies right
exact functors on finitely presented modules. -/
@[stacks 0GNN]
public lemma evaluationFunctor_isEquivalence (A : Type u) (B : Type v) [Ring A]
    [Category.{w} B] [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B] :
    (evaluationFunctor A B).IsEquivalence :=
  Functor.IsEquivalence.mk'
    (actionTensorRightExactFunctor' (A := A) (B := B))
    (actionTensorComparisonIso (A := A) (B := B)).symm
    (actionTensorUnitIso (A := A) (B := B)).symm

end ModuleCat
