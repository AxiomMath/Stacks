module

public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# The internal Hom of abelian sheaves out of a fixed sheaf, and its left adjoint

Let `(C, K)` be a site and `G` an abelian sheaf. The internal Hom `ℋom(G, -)` of abelian
sheaves (`internalHomSheaf`) is a functor in its second variable, and it has a left adjoint:
the sheafification of the sectionwise tensor product `X ↦ (U ↦ G(U) ⊗_ℤ X(U))`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct Abelian

universe v u w'

namespace Stacks.AbelianInternalHom

variable {C : Type u} [Category.{v} C]

section Presheaf

variable (G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v})

/-- Postcomposition with `g : F ⟶ F'` on the internal Hom presheaf out of `G`. -/
def internalHomPresheafMapRight {F F' : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (g : F ⟶ F') :
    internalHomPresheaf G F ⟶ internalHomPresheaf G F' where
  app U := AddCommGrpCat.ofHom
    { toFun := fun a => a ≫ Functor.whiskerLeft (Over.forget U.unop).op g
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  naturality U U' f := by
    ext a
    rfl

/-- **The internal Hom presheaf `ℋom(G, -)`, as a functor of its second variable.** -/
@[simps obj]
def internalHomPresheafRightFunctor :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) where
  obj F := internalHomPresheaf G F
  map g := internalHomPresheafMapRight G g
  map_id F := by ext; rfl
  map_comp f g := by ext; rfl

/-- **The sectionwise tensor product `X ↦ (U ↦ G(U) ⊗_ℤ X(U))`** of abelian presheaves. -/
@[simps obj]
def presheafTensorObj (X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} where
  obj U := AddCommGrpCat.of (G.obj U ⊗[ℤ] X.obj U)
  map f := AddCommGrpCat.ofHom
    (TensorProduct.map (G.map f).hom.toIntLinearMap (X.map f).hom.toIntLinearMap).toAddMonoidHom
  map_id U := by
    ext t
    induction t using TensorProduct.inductionOn with
    | tmul g x => simp
    | add a b ha hb => simp_all
  map_comp f f' := by
    ext t
    induction t using TensorProduct.inductionOn with
    | tmul g x => simp
    | add a b ha hb => simp_all

/-- Two maps out of a sectionwise tensor product agree as soon as they agree on pure tensors. -/
lemma presheafTensorObj_hom_ext {X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} {U : Cᵒᵖ}
    {M : AddCommGrpCat.{max u v}} {f g : (presheafTensorObj G X).obj U ⟶ M}
    (h : ∀ (a : G.obj U) (b : X.obj U), f.hom (a ⊗ₜ[ℤ] b) = g.hom (a ⊗ₜ[ℤ] b)) : f = g :=
  AddCommGrpCat.hom_ext (AddMonoidHom.toIntLinearMap_injective (TensorProduct.ext' h))

/-- **The sectionwise tensor product `G ⊗_ℤ -`**, as an endofunctor of abelian presheaves. -/
@[simps obj]
def presheafTensor : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) where
  obj X := presheafTensorObj G X
  map {X Y} f :=
    { app U := AddCommGrpCat.ofHom
        ((f.app U).hom.toIntLinearMap.lTensor (G.obj U)).toAddMonoidHom
      naturality U U' a := presheafTensorObj_hom_ext G fun g x => by
        change (G.map a) g ⊗ₜ[ℤ] (f.app U') ((X.map a) x) =
          (G.map a) g ⊗ₜ[ℤ] Y.map a (f.app U x)
        rw [← ConcreteCategory.comp_apply, f.naturality, ConcreteCategory.comp_apply] }
  map_id X := NatTrans.ext (funext fun _ => presheafTensorObj_hom_ext G fun _ _ => rfl)
  map_comp f f' := NatTrans.ext (funext fun _ => presheafTensorObj_hom_ext G fun _ _ => rfl)

variable {G}

/-- The local morphism `G|_U ⟶ I|_U` attached to a section `x ∈ X(U)` by a pairing
`φ : G ⊗ X ⟶ I`: over `h : W ⟶ U` it sends `g` to `φ(g ⊗ x|_W)`. -/
def pairingLocal {X I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (φ : presheafTensorObj G X ⟶ I)
    (U : Cᵒᵖ) (x : X.obj U) : (Over.forget U.unop).op ⋙ G ⟶ (Over.forget U.unop).op ⋙ I where
  app W := AddCommGrpCat.ofHom
    { toFun := fun g => (φ.app (op W.unop.left)).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op x)
      map_zero' := by
        rw [TensorProduct.zero_tmul]
        exact (φ.app (op W.unop.left)).hom.map_zero
      map_add' := fun a b => by
        rw [TensorProduct.add_tmul]
        exact (φ.app (op W.unop.left)).hom.map_add _ _ }
  naturality W W' a := by
    ext g
    have h := ConcreteCategory.congr_hom (φ.naturality a.unop.left.op)
      (g ⊗ₜ[ℤ] X.map W.unop.hom.op x)
    change (φ.app (op W'.unop.left)).hom
        (G.map a.unop.left.op g ⊗ₜ[ℤ] X.map W'.unop.hom.op x) =
      (I.map a.unop.left.op).hom
        ((φ.app (op W.unop.left)).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op x))
    have e : X.map W'.unop.hom.op x = X.map a.unop.left.op (X.map W.unop.hom.op x) := by
      rw [← Over.w a.unop, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rwa [e]

/-- Over `h : W ⟶ U`, the local morphism `pairingLocal φ U x` sends `g` to `φ(g ⊗ x|_W)`. -/
lemma pairingLocal_app_apply {X I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (φ : presheafTensorObj G X ⟶ I) (U : Cᵒᵖ) (x : X.obj U) (W : (Over U.unop)ᵒᵖ)
    (g : G.obj (op W.unop.left)) :
    ((pairingLocal φ U x).app W).hom g =
      (φ.app (op W.unop.left)).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op x) := rfl

/-- The map of presheaves `X ⟶ ℋom(G, I)` transposed from a pairing `G ⊗ X ⟶ I`. -/
def pairingTranspose {X I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (φ : presheafTensorObj G X ⟶ I) :
    X ⟶ internalHomPresheaf G I where
  app U := AddCommGrpCat.ofHom
    { toFun := fun x => pairingLocal φ U x
      map_zero' := by
        refine NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun g => ?_))
        change (φ.app _).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op 0) = 0
        rw [map_zero, TensorProduct.tmul_zero]
        exact (φ.app _).hom.map_zero
      map_add' := fun a b => by
        refine NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun g => ?_))
        change (φ.app _).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op (a + b)) =
          (φ.app _).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op a) +
            (φ.app _).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op b)
        rw [map_add, TensorProduct.tmul_add]
        exact (φ.app _).hom.map_add _ _ }
  naturality U U' f := by
    ext x
    refine NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun g => ?_))
    change (φ.app _).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op (X.map f x)) =
      (φ.app _).hom (g ⊗ₜ[ℤ] X.map (W.unop.hom ≫ f.unop).op x)
    rw [op_comp, X.map_comp, ConcreteCategory.comp_apply]
    rfl

/-- The pairing `G ⊗ X ⟶ I` attached to a map of presheaves `ψ : X ⟶ ℋom(G, I)`:
`g ⊗ x ↦ ψ(x)(g)` over each object, evaluated at the identity of that object. -/
def pairingUntranspose {X I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (ψ : X ⟶ internalHomPresheaf G I) : presheafTensorObj G X ⟶ I where
  app U := AddCommGrpCat.ofHom (TensorProduct.lift (LinearMap.mk₂ ℤ
    (fun (g : G.obj U) (x : X.obj U) =>
      ((ψ.app U x).app (op (Over.mk (𝟙 U.unop)))).hom g)
    (fun a b x => map_add _ a b)
    (fun n a x => map_zsmul _ n a)
    (fun g a b => by rw [map_add]; rfl)
    (fun n g x => by rw [map_zsmul]; rfl))).toAddMonoidHom
  naturality U U' f := presheafTensorObj_hom_ext G fun g x => by
    change ((ψ.app U' (X.map f x)).app (op (Over.mk (𝟙 U'.unop)))).hom (G.map f g) =
      I.map f (((ψ.app U x).app (op (Over.mk (𝟙 U.unop)))).hom g)
    have hψ := ConcreteCategory.congr_hom (ψ.naturality f) x
    rw [ConcreteCategory.comp_apply] at hψ
    rw [hψ]
    exact ConcreteCategory.congr_hom
      ((ψ.app U x).naturality (Over.homMk (U := Over.mk (𝟙 U'.unop ≫ f.unop))
        (V := Over.mk (𝟙 U.unop)) f.unop (by simp)).op) g

/-- On a pure tensor, `pairingUntranspose ψ` sends `g ⊗ x` to `ψ(x)(g)` evaluated at the
identity of `U`. -/
lemma pairingUntranspose_app_tmul {X I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (ψ : X ⟶ internalHomPresheaf G I) (U : Cᵒᵖ) (g : G.obj U) (x : X.obj U) :
    ((pairingUntranspose ψ).app U).hom (g ⊗ₜ[ℤ] x) =
      ((ψ.app U x).app (op (Over.mk (𝟙 U.unop)))).hom g := rfl

/-- **The pairing bijection** `Hom(G ⊗ X, I) ≃ Hom(X, ℋom(G, I))` for abelian presheaves. -/
def pairingEquiv (X I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    (presheafTensorObj G X ⟶ I) ≃ (X ⟶ internalHomPresheaf G I) where
  toFun := pairingTranspose
  invFun := pairingUntranspose
  left_inv φ := NatTrans.ext (funext fun U => presheafTensorObj_hom_ext G fun g x => by
    change (φ.app U).hom (g ⊗ₜ[ℤ] X.map (𝟙 U.unop).op x) = (φ.app U).hom (g ⊗ₜ[ℤ] x)
    rw [op_id, X.map_id]
    rfl)
  right_inv ψ := by
    ext U x
    refine NatTrans.ext (funext fun W => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun g => ?_))
    change ((ψ.app (op W.unop.left) (X.map W.unop.hom.op x)).app
      (op (Over.mk (𝟙 W.unop.left)))).hom g = ((ψ.app U x).app W).hom g
    have hψ := ConcreteCategory.congr_hom (ψ.naturality W.unop.hom.op) x
    rw [ConcreteCategory.comp_apply] at hψ
    rw [hψ]
    have hn := ConcreteCategory.congr_hom ((ψ.app U x).naturality
      (Over.homMk (U := W.unop) (V := Over.mk (𝟙 W.unop.left ≫ W.unop.hom))
        (𝟙 W.unop.left) (by simp)).op) g
    change ((ψ.app U x).app W).hom (G.map (𝟙 W.unop.left).op g) =
      I.map (𝟙 W.unop.left).op _ at hn
    rw [op_id, G.map_id, I.map_id] at hn
    exact hn.symm

variable (G)

/-- **`G ⊗_ℤ -` is left adjoint to `ℋom(G, -)`** on abelian presheaves. -/
def presheafTensorAdj : presheafTensor G ⊣ internalHomPresheafRightFunctor G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := pairingEquiv
      homEquiv_naturality_left_symm := fun f g =>
        NatTrans.ext (funext fun _ => presheafTensorObj_hom_ext G fun _ _ => rfl)
      homEquiv_naturality_right := fun f g => by ext; rfl }

end Presheaf

section Sheaf

variable (K : GrothendieckTopology C) (G : Sheaf K AddCommGrpCat.{max u v})

/-- **The internal Hom `ℋom(G, -)` of abelian sheaves**, as a functor of its second variable;
its value at `F` is `internalHomSheaf K G F`. -/
@[simps obj]
def internalHomRightFunctor :
    Sheaf K AddCommGrpCat.{max u v} ⥤ Sheaf K AddCommGrpCat.{max u v} where
  obj F := internalHomSheaf K G F
  map g := ⟨internalHomPresheafMapRight G.obj g.hom⟩
  map_id F := Sheaf.hom_ext ((internalHomPresheafRightFunctor G.obj).map_id F.obj)
  map_comp f g := Sheaf.hom_ext ((internalHomPresheafRightFunctor G.obj).map_comp f.hom g.hom)

variable [HasSheafify K AddCommGrpCat.{max u v}]

/-- **The sheafified sectionwise tensor product `X ↦ (G ⊗_ℤ X)^#`** of abelian sheaves. -/
abbrev sheafTensor : Sheaf K AddCommGrpCat.{max u v} ⥤ Sheaf K AddCommGrpCat.{max u v} :=
  sheafToPresheaf K _ ⋙ presheafTensor G.obj ⋙ presheafToSheaf K _

/-- **`(G ⊗_ℤ -)^#` is left adjoint to `ℋom(G, -)`** on abelian sheaves. -/
def sheafTensorAdj : sheafTensor K G ⊣ internalHomRightFunctor K G :=
  Adjunction.restrictFullyFaithful
    (iC := sheafToPresheaf K AddCommGrpCat.{max u v}) (iD := 𝟭 _)
    ((presheafTensorAdj G.obj).comp (sheafificationAdjunction K _))
    (fullyFaithfulSheafToPresheaf K _) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- **`(G ⊗_ℤ -)^#` keeps the inclusion of a short exact sequence with sectionwise
torsion-free quotient a monomorphism.** -/
lemma mono_sheafTensor_map (S : ShortComplex (Sheaf K AddCommGrpCat.{max u v}))
    (hS : S.ShortExact) (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X)) :
    Mono ((sheafTensor K G).map S.f) := by
  have := hS.mono_f
  have (U : Cᵒᵖ) : Mono (((presheafTensor G.obj).map S.f.hom).app U) := by
    have := hP U
    let E := sheafToPresheaf K AddCommGrpCat.{max u v} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj U
    have hE := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp
      inferInstance S hS
    rw [AddCommGrpCat.mono_iff_injective]
    exact ModuleSheafCohomology.lTensor_injective_of_exact_of_isTorsionFree
      (S.f.hom.app U).hom.toIntLinearMap (S.g.hom.app U).hom.toIntLinearMap
      ((AddCommGrpCat.mono_iff_injective _).mp hE.2)
      ((ShortComplex.ab_exact_iff_function_exact (S.map E)).mp hE.1) (G.obj.obj U)
  have : Mono ((presheafTensor G.obj).map S.f.hom) := NatTrans.mono_of_mono_app _
  change Mono ((presheafToSheaf K _).map ((presheafTensor G.obj).map S.f.hom))
  infer_instance

variable [HasExt.{w'} (Sheaf K AddCommGrpCat.{max u v})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{max u v})]

/-- **`ℋom(G, I)` is `Ext`-acyclic against every sectionwise torsion-free abelian sheaf**, for
an injective abelian sheaf `I` and an arbitrary abelian sheaf `G`. -/
lemma ext_internalHomSheaf_eq_zero_of_isTorsionFree (I : Sheaf K AddCommGrpCat.{max u v})
    [Injective I] (X : Sheaf K AddCommGrpCat.{max u v})
    (hX : ∀ U, Module.IsTorsionFree ℤ (X.obj.obj U)) (n : ℕ)
    (e : Ext.{w'} X (internalHomSheaf K G I) (n + 1)) : e = 0 :=
  ModuleSheafCohomology.ext_eq_zero_of_adjunction (sheafTensor K G)
    (internalHomRightFunctor K G) (sheafTensorAdj K G)
    (fun F => ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U))
    (fun f _ hY => ModuleSheafCohomology.isTorsionFree_of_mono K f hY)
    (ModuleSheafCohomology.exists_isTorsionFree_epi K)
    (fun S hS hP => mono_sheafTensor_map K G S hS hP) I n X hX e

/-- **`Hⁿ⁺¹(ℋom(G, I)) = 0`** for an injective abelian sheaf `I` and any abelian sheaf `G`. -/
lemma subsingleton_H_internalHomSheaf (I : Sheaf K AddCommGrpCat.{max u v}) [Injective I]
    (n : ℕ) : Subsingleton (Sheaf.H.{w'} (internalHomSheaf K G I) (n + 1)) := by
  refine ⟨fun a b => ?_⟩
  have hX : ∀ U, Module.IsTorsionFree ℤ
      (((constantSheaf K AddCommGrpCat.{max u v}).obj
        (AddCommGrpCat.of (ULift ℤ))).obj.obj U) :=
    ModuleSheafCohomology.isTorsionFree_sheafify K _ (fun U => by
      change Module.IsTorsionFree ℤ (ULift ℤ)
      exact Function.Injective.moduleIsTorsionFree (fun x : ULift ℤ => x.down)
        ULift.down_injective (fun _ _ => rfl))
  rw [ext_internalHomSheaf_eq_zero_of_isTorsionFree K G I _ hX n a,
    ext_internalHomSheaf_eq_zero_of_isTorsionFree K G I _ hX n b]

end Sheaf

end Stacks.AbelianInternalHom
