module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# The internal Hom of sheaves of `A`-modules out of a fixed sheaf, and its left adjoint

Let `(C, K)` be a site, `A` a commutative ring and `G` a sheaf of `A`-modules. The abelian sheaf
underlying the internal Hom `ℋom_A(G, -)` (`Stacks.ConstantSheaf.moduleSheafHom`) has a left
adjoint from abelian sheaves: the sheafification of the sectionwise tensor product
`X ↦ (U ↦ G(U) ⊗_ℤ X(U))`, with `A` acting on `G`. This left adjoint keeps the inclusion of a
short exact sequence with sectionwise torsion-free quotient a monomorphism, so the argument of
Tag 03FD applies: `Hⁿ⁺¹(ℋom_A(G, I)) = 0` for every injective sheaf of `A`-modules `I`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct Abelian

universe w v u w'

namespace Stacks.ModuleInternalHom

variable {C : Type u} [Category.{v} C] (A : Type w) [CommRing A]

section Presheaf

variable (G : Cᵒᵖ ⥤ ModuleCat.{max u v} A)

/-- **The sectionwise tensor product `X ↦ (U ↦ G(U) ⊗_ℤ X(U))`**, a presheaf of `A`-modules. -/
@[simps obj]
def presheafTensorObj (X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) : Cᵒᵖ ⥤ ModuleCat.{max u v} A where
  obj U := ModuleCat.of A (G.obj U ⊗[ℤ] X.obj U)
  map f := ModuleCat.ofHom
    (TensorProduct.AlgebraTensorModule.map (G.map f).hom (X.map f).hom.toIntLinearMap)
  map_id U := ModuleCat.hom_ext (TensorProduct.AlgebraTensorModule.ext fun g x => by
    simp)
  map_comp f f' := ModuleCat.hom_ext (TensorProduct.AlgebraTensorModule.ext fun g x => by
    simp)

/-- Two maps out of a sectionwise tensor product agree as soon as they agree on pure tensors. -/
lemma presheafTensorObj_hom_ext {X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} {U : Cᵒᵖ}
    {M : ModuleCat.{max u v} A} {f g : (presheafTensorObj A G X).obj U ⟶ M}
    (h : ∀ (a : G.obj U) (b : X.obj U), f.hom (a ⊗ₜ[ℤ] b) = g.hom (a ⊗ₜ[ℤ] b)) : f = g :=
  ModuleCat.hom_ext (TensorProduct.AlgebraTensorModule.ext h)

/-- **The sectionwise tensor product `G ⊗_ℤ -`**, from abelian presheaves to presheaves of
`A`-modules. -/
@[simps obj]
def presheafTensor : (Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) ⥤ (Cᵒᵖ ⥤ ModuleCat.{max u v} A) where
  obj X := presheafTensorObj A G X
  map {X Y} f :=
    { app U := ModuleCat.ofHom
        (TensorProduct.AlgebraTensorModule.lTensor A (G.obj U) (f.app U).hom.toIntLinearMap)
      naturality U U' a := presheafTensorObj_hom_ext A G fun g x => by
        change (G.map a) g ⊗ₜ[ℤ] (f.app U') ((X.map a) x) =
          (G.map a) g ⊗ₜ[ℤ] Y.map a (f.app U x)
        rw [← ConcreteCategory.comp_apply, f.naturality, ConcreteCategory.comp_apply] }
  map_id X := NatTrans.ext (funext fun _ => presheafTensorObj_hom_ext A G fun _ _ => rfl)
  map_comp f f' := NatTrans.ext (funext fun _ => presheafTensorObj_hom_ext A G fun _ _ => rfl)

end Presheaf

section Pairing

variable (K : GrothendieckTopology C)

/-- The presheaf of abelian groups underlying `ℋom_A(G, I)`. -/
abbrev homPresheafAb (G I : Sheaf K (ModuleCat.{max u v} A)) : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (Stacks.ConstantSheaf.moduleSheafHom K A G I).obj ⋙
    forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}

variable {K A} {G I : Sheaf K (ModuleCat.{max u v} A)} {X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}

/-- A section of `ℋom_A(G, I)` over `U`, as the morphism of sheaves on the slice it is. -/
abbrev homPresheafAbSection {U : Cᵒᵖ} (a : (homPresheafAb A K G I).obj U) :
    (K.overPullback (ModuleCat.{max u v} A) U.unop).obj G ⟶
      (K.overPullback (ModuleCat.{max u v} A) U.unop).obj I := a

/-- The component over `h : W ⟶ U` of the local morphism attached to `x ∈ X(U)` by a pairing
`φ : G ⊗ X ⟶ I`: `g ↦ φ(g ⊗ x|_W)`. -/
def pairingLocalLinear (φ : presheafTensorObj A G.obj X ⟶ I.obj) (U : Cᵒᵖ) (x : X.obj U)
    (W : (Over U.unop)ᵒᵖ) :
    (G.obj.obj (op W.unop.left) : Type (max u v)) →ₗ[A]
      (I.obj.obj (op W.unop.left) : Type (max u v)) where
  toFun g := (φ.app (op W.unop.left)).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op x)
  map_add' a b := by
    rw [TensorProduct.add_tmul]
    exact (φ.app (op W.unop.left)).hom.map_add _ _
  map_smul' r a := (φ.app (op W.unop.left)).hom.map_smul r (a ⊗ₜ[ℤ] X.map W.unop.hom.op x)

/-- The local morphism `G|_U ⟶ I|_U` attached to a section `x ∈ X(U)` by a pairing
`φ : G ⊗ X ⟶ I`: over `h : W ⟶ U` it sends `g` to `φ(g ⊗ x|_W)`. -/
def pairingLocal (φ : presheafTensorObj A G.obj X ⟶ I.obj) (U : Cᵒᵖ) (x : X.obj U) :
    (K.overPullback (ModuleCat.{max u v} A) U.unop).obj G ⟶
      (K.overPullback (ModuleCat.{max u v} A) U.unop).obj I :=
  ObjectProperty.homMk
    { app W := ModuleCat.ofHom (pairingLocalLinear φ U x W)
      naturality W W' a := by
        ext g
        have h := ConcreteCategory.congr_hom (φ.naturality a.unop.left.op)
          (g ⊗ₜ[ℤ] X.map W.unop.hom.op x)
        change (φ.app (op W'.unop.left)).hom
            (G.obj.map a.unop.left.op g ⊗ₜ[ℤ] X.map W'.unop.hom.op x) =
          (I.obj.map a.unop.left.op).hom
            ((φ.app (op W.unop.left)).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op x))
        have e : X.map W'.unop.hom.op x = X.map a.unop.left.op (X.map W.unop.hom.op x) := by
          rw [← Over.w a.unop, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
        rw [e]
        exact h }

/-- The component of `pairingLocal φ U x` over `W ⟶ U` sends `g` to `φ(g ⊗ x|_W)`. -/
lemma pairingLocal_hom_app_apply (φ : presheafTensorObj A G.obj X ⟶ I.obj) (U : Cᵒᵖ)
    (x : X.obj U) (W : (Over U.unop)ᵒᵖ) (g : G.obj.obj (op W.unop.left)) :
    ((pairingLocal φ U x).hom.app W).hom g =
      (φ.app (op W.unop.left)).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op x) := rfl

/-- The map of presheaves `X ⟶ ℋom_A(G, I)` transposed from a pairing `G ⊗ X ⟶ I`. -/
def pairingTranspose (φ : presheafTensorObj A G.obj X ⟶ I.obj) : X ⟶ homPresheafAb A K G I where
  app U := AddCommGrpCat.ofHom
    { toFun := fun x => pairingLocal φ U x
      map_zero' := by
        refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W => ModuleCat.hom_ext
          (LinearMap.ext fun (g : G.obj.obj (op W.unop.left)) => ?_)))
        change (φ.app _).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op 0) = 0
        rw [map_zero, TensorProduct.tmul_zero]
        exact (φ.app _).hom.map_zero
      map_add' := fun a b => by
        refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W => ModuleCat.hom_ext
          (LinearMap.ext fun (g : G.obj.obj (op W.unop.left)) => ?_)))
        change (φ.app _).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op (a + b)) =
          (φ.app _).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op a) +
            (φ.app _).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op b)
        rw [map_add, TensorProduct.tmul_add]
        exact (φ.app _).hom.map_add _ _ }
  naturality U U' f := by
    ext x
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W => ModuleCat.hom_ext
      (LinearMap.ext fun (g : G.obj.obj (op W.unop.left)) => ?_)))
    change (φ.app _).hom (g ⊗ₜ[ℤ] X.map W.unop.hom.op (X.map f x)) =
      (φ.app _).hom (g ⊗ₜ[ℤ] X.map (W.unop.hom ≫ f.unop).op x)
    rw [op_comp, X.map_comp, ConcreteCategory.comp_apply]
    rfl

/-- The bilinear map `(g, x) ↦ ψ(x)(g)` over `U`, for `ψ : X ⟶ ℋom_A(G, I)`. -/
def pairingBilinear (ψ : X ⟶ homPresheafAb A K G I) (U : Cᵒᵖ) :
    (G.obj.obj U : Type (max u v)) →ₗ[A] (X.obj U : Type (max u v)) →ₗ[ℤ]
      (I.obj.obj U : Type (max u v)) :=
  LinearMap.mk₂' A ℤ
    (fun (g : G.obj.obj U) (x : X.obj U) =>
      ((homPresheafAbSection ((ψ.app U).hom x)).hom.app (op (Over.mk (𝟙 U.unop)))).hom g)
    (fun a b x =>
      ((homPresheafAbSection ((ψ.app U).hom x)).hom.app (op (Over.mk (𝟙 U.unop)))).hom.map_add a b)
    (fun r a x =>
      ((homPresheafAbSection ((ψ.app U).hom x)).hom.app (op (Over.mk (𝟙 U.unop)))).hom.map_smul r a)
    (fun g a b => by rw [map_add]; rfl)
    (fun n g x => by rw [map_zsmul]; rfl)

/-- The pairing `G ⊗ X ⟶ I` attached to a map of presheaves `ψ : X ⟶ ℋom_A(G, I)`:
`g ⊗ x ↦ ψ(x)(g)` over each object, evaluated at the identity of that object. -/
def pairingUntranspose (ψ : X ⟶ homPresheafAb A K G I) : presheafTensorObj A G.obj X ⟶ I.obj where
  app U := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lift (pairingBilinear ψ U))
  naturality U U' f := presheafTensorObj_hom_ext A G.obj fun g x => by
    change ((homPresheafAbSection ((ψ.app U').hom (X.map f x))).hom.app
        (op (Over.mk (𝟙 U'.unop)))).hom (G.obj.map f g) =
      (I.obj.map f).hom (((homPresheafAbSection ((ψ.app U).hom x)).hom.app
        (op (Over.mk (𝟙 U.unop)))).hom g)
    have hψ := ConcreteCategory.congr_hom (ψ.naturality f) x
    rw [ConcreteCategory.comp_apply] at hψ
    rw [hψ]
    exact ConcreteCategory.congr_hom
      ((homPresheafAbSection ((ψ.app U).hom x)).hom.naturality
        (Over.homMk (U := Over.mk (𝟙 U'.unop ≫ f.unop)) (V := Over.mk (𝟙 U.unop)) f.unop
          (by simp)).op) g

/-- Over `U`, `pairingUntranspose ψ` sends `g ⊗ x` to `ψ(x)(g)`, evaluated at the identity of
`U`. -/
lemma pairingUntranspose_app_tmul (ψ : X ⟶ homPresheafAb A K G I) (U : Cᵒᵖ) (g : G.obj.obj U)
    (x : X.obj U) :
    ((pairingUntranspose ψ).app U).hom (g ⊗ₜ[ℤ] x) =
      ((homPresheafAbSection ((ψ.app U).hom x)).hom.app (op (Over.mk (𝟙 U.unop)))).hom g := rfl

variable (G I X) in
/-- **The pairing bijection** `Hom_A(G ⊗ X, I) ≃ Hom_ℤ(X, ℋom_A(G, I))`. -/
def pairingEquiv : (presheafTensorObj A G.obj X ⟶ I.obj) ≃ (X ⟶ homPresheafAb A K G I) where
  toFun := pairingTranspose
  invFun := pairingUntranspose
  left_inv φ := NatTrans.ext (funext fun U => presheafTensorObj_hom_ext A G.obj fun g x => by
    change (φ.app U).hom (g ⊗ₜ[ℤ] X.map (𝟙 U.unop).op x) = (φ.app U).hom (g ⊗ₜ[ℤ] x)
    rw [op_id, CategoryTheory.Functor.map_id]
    rfl)
  right_inv ψ := by
    ext U x
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W => ModuleCat.hom_ext
      (LinearMap.ext fun (g : G.obj.obj (op W.unop.left)) => ?_)))
    change ((homPresheafAbSection ((ψ.app (op W.unop.left)).hom (X.map W.unop.hom.op x))).hom.app
      (op (Over.mk (𝟙 W.unop.left)))).hom g =
        ((homPresheafAbSection ((ψ.app U).hom x)).hom.app W).hom g
    have hψ := ConcreteCategory.congr_hom (ψ.naturality W.unop.hom.op) x
    rw [ConcreteCategory.comp_apply] at hψ
    rw [hψ]
    have hn := ConcreteCategory.congr_hom ((homPresheafAbSection ((ψ.app U).hom x)).hom.naturality
      (Over.homMk (U := W.unop) (V := Over.mk (𝟙 W.unop.left ≫ W.unop.hom))
        (𝟙 W.unop.left) (by simp)).op) g
    change ((homPresheafAbSection ((ψ.app U).hom x)).hom.app W).hom
        (G.obj.map (𝟙 W.unop.left).op g) =
      (I.obj.map (𝟙 W.unop.left).op).hom _ at hn
    rw [op_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at hn
    exact hn.symm

end Pairing

section Sheaf

variable (K : GrothendieckTopology C) (G : Sheaf K (ModuleCat.{max u v} A))

/-- **The abelian sheaf `ℋom_A(G, I)`**, as a functor of `I`. -/
@[simps obj]
def homAbFunctor : Sheaf K (ModuleCat.{max u v} A) ⥤ Sheaf K AddCommGrpCat.{max u v} where
  obj I := (sheafCompose K (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v})).obj
    (Stacks.ConstantSheaf.moduleSheafHom K A G I)
  map g := (sheafCompose K (forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v})).map
    (Stacks.ConstantSheaf.moduleSheafHomMap K A (𝟙 G) g)
  map_id I := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext
      (AddMonoidHom.ext fun (α : (K.overPullback (ModuleCat.{max u v} A) U.unop).obj G ⟶
        (K.overPullback (ModuleCat.{max u v} A) U.unop).obj I) => ?_)))
    change (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫ α ≫
      (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 I) = α
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id]
  map_comp {I₁ I₂ I₃} f g := by
    refine Sheaf.hom_ext (NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext
      (AddMonoidHom.ext fun (α : (K.overPullback (ModuleCat.{max u v} A) U.unop).obj G ⟶
        (K.overPullback (ModuleCat.{max u v} A) U.unop).obj I₁) => ?_)))
    change (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫ α ≫
        (K.overPullback (ModuleCat.{max u v} A) U.unop).map (f ≫ g) =
      (K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫
        ((K.overPullback (ModuleCat.{max u v} A) U.unop).map (𝟙 G) ≫ α ≫
          (K.overPullback (ModuleCat.{max u v} A) U.unop).map f) ≫
        (K.overPullback (ModuleCat.{max u v} A) U.unop).map g
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp, Category.assoc]

/-- `pairingUntranspose` is natural in the presheaf: precomposing with `f : X' ⟶ X` corresponds
to precomposing the pairing with `G ⊗ f`. -/
lemma pairingUntranspose_comp_left {X X' : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {I : Sheaf K (ModuleCat.{max u v} A)} (f : X' ⟶ X) (g : X ⟶ homPresheafAb A K G I) :
    pairingUntranspose (f ≫ g) = (presheafTensor A G.obj).map f ≫ pairingUntranspose g :=
  NatTrans.ext (funext fun _ => presheafTensorObj_hom_ext A G.obj fun _ _ => rfl)

/-- `pairingTranspose` is natural in the sheaf: postcomposing a pairing with `k : I ⟶ I'`
corresponds to postcomposing its transpose with `ℋom_A(G, k)`. -/
lemma pairingTranspose_comp_right {X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {I I' : Sheaf K (ModuleCat.{max u v} A)} (φ : presheafTensorObj A G.obj X ⟶ I.obj)
    (k : I ⟶ I') :
    pairingTranspose (φ ≫ k.hom) =
      pairingTranspose φ ≫ ((homAbFunctor A K G).map k).hom := rfl

variable [HasSheafify K (ModuleCat.{max u v} A)]

/-- `(G ⊗_ℤ -)^#` is left adjoint to `ℋom_A(G, -)` with values in abelian presheaves. -/
def presheafTensorSheafifyAdj :
    presheafTensor A G.obj ⋙ presheafToSheaf K (ModuleCat.{max u v} A) ⊣
      homAbFunctor A K G ⋙ sheafToPresheaf K AddCommGrpCat.{max u v} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X I =>
        ((sheafificationAdjunction K (ModuleCat.{max u v} A)).homEquiv _ I).trans
          (pairingEquiv G I X)
      homEquiv_naturality_left_symm := fun {X' X I} f g => by
        have h1 := pairingUntranspose_comp_left A K G (I := I) f (g : X ⟶ homPresheafAb A K G I)
        have h2 :=
          (sheafificationAdjunction K (ModuleCat.{max u v} A)).homEquiv_naturality_left_symm
            ((presheafTensor A G.obj).map f) (pairingUntranspose (g : X ⟶ homPresheafAb A K G I))
        exact (congrArg (((sheafificationAdjunction K (ModuleCat.{max u v} A)).homEquiv _ I).symm)
          h1).trans h2
      homEquiv_naturality_right := fun {X I I'} φ k => by
        have h := (sheafificationAdjunction K (ModuleCat.{max u v} A)).homEquiv_naturality_right
          (φ : (presheafToSheaf K _).obj (presheafTensorObj A G.obj X) ⟶ I) k
        exact (congrArg pairingTranspose h).trans (pairingTranspose_comp_right A K G _ k) }

/-- **The sheafified sectionwise tensor product `X ↦ (G ⊗_ℤ X)^#`**, from abelian sheaves to
sheaves of `A`-modules. -/
abbrev sheafTensor : Sheaf K AddCommGrpCat.{max u v} ⥤ Sheaf K (ModuleCat.{max u v} A) :=
  sheafToPresheaf K _ ⋙ presheafTensor A G.obj ⋙ presheafToSheaf K _

/-- **`(G ⊗_ℤ -)^#` is left adjoint to `ℋom_A(G, -)`**, the latter read in abelian sheaves. -/
def sheafTensorAdj : sheafTensor A K G ⊣ homAbFunctor A K G :=
  Adjunction.restrictFullyFaithful
    (iC := sheafToPresheaf K AddCommGrpCat.{max u v}) (iD := 𝟭 _)
    (presheafTensorSheafifyAdj A K G)
    (fullyFaithfulSheafToPresheaf K _) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- **`(G ⊗_ℤ -)^#` keeps the inclusion of a short exact sequence with sectionwise
torsion-free quotient a monomorphism.** -/
lemma mono_sheafTensor_map (S : ShortComplex (Sheaf K AddCommGrpCat.{max u v}))
    (hS : S.ShortExact) (hP : ∀ X, Module.IsTorsionFree ℤ (S.X₃.obj.obj X)) :
    Mono ((sheafTensor A K G).map S.f) := by
  have := hS.mono_f
  have hpre : Mono ((presheafTensor A G.obj).map S.f.hom) := by
    have (U : Cᵒᵖ) : Mono (((presheafTensor A G.obj).map S.f.hom).app U) := by
      have := hP U
      let E := sheafToPresheaf K AddCommGrpCat.{max u v} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj U
      have hE := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono E).mp
        inferInstance S hS
      rw [ModuleCat.mono_iff_injective]
      exact ModuleSheafCohomology.lTensor_injective_of_exact_of_isTorsionFree
        (S.f.hom.app U).hom.toIntLinearMap (S.g.hom.app U).hom.toIntLinearMap
        ((AddCommGrpCat.mono_iff_injective _).mp hE.2)
        ((ShortComplex.ab_exact_iff_function_exact (S.map E)).mp hE.1) (G.obj.obj U)
    exact NatTrans.mono_of_mono_app _
  change Mono ((presheafToSheaf K _).map ((presheafTensor A G.obj).map S.f.hom))
  infer_instance

variable [HasSheafify K AddCommGrpCat.{max u v}] [HasExt.{w'} (Sheaf K AddCommGrpCat.{max u v})]
  [HasInjectiveResolutions (Sheaf K AddCommGrpCat.{max u v})]

/-- **`Hⁿ⁺¹(ℋom_A(G, I)) = 0`** for an injective sheaf of `A`-modules `I` and any sheaf of
`A`-modules `G`, the cohomology being that of the underlying abelian sheaf. -/
lemma subsingleton_H_homAbFunctor (I : Sheaf K (ModuleCat.{max u v} A)) [Injective I] (n : ℕ) :
    Subsingleton (Sheaf.H.{w'} ((homAbFunctor A K G).obj I) (n + 1)) := by
  have hX : ∀ U, Module.IsTorsionFree ℤ
      (((constantSheaf K AddCommGrpCat.{max u v}).obj
        (AddCommGrpCat.of (ULift ℤ))).obj.obj U) :=
    ModuleSheafCohomology.isTorsionFree_sheafify K _ (fun U => by
      change Module.IsTorsionFree ℤ (ULift ℤ)
      exact Function.Injective.moduleIsTorsionFree (fun x : ULift ℤ => x.down)
        ULift.down_injective (fun _ _ => rfl))
  have key := fun (e : Ext.{w'} _ ((homAbFunctor A K G).obj I) (n + 1)) =>
    ModuleSheafCohomology.ext_eq_zero_of_adjunction (sheafTensor A K G) (homAbFunctor A K G)
      (sheafTensorAdj A K G) (fun F => ∀ U, Module.IsTorsionFree ℤ (F.obj.obj U))
      (fun f _ hY => ModuleSheafCohomology.isTorsionFree_of_mono K f hY)
      (ModuleSheafCohomology.exists_isTorsionFree_epi K)
      (fun S hS hP => mono_sheafTensor_map A K G S hS hP) I n _ hX e
  exact ⟨fun a b => (key a).trans (key b).symm⟩

end Sheaf

end Stacks.ModuleInternalHom
