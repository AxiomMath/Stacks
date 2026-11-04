module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.CategoryTheory.Sites.Modules.SheafTensorDescNaturality

/-!
# The internal hom of sheaves of modules represents morphisms out of a tensor product

Let `R` be a commutative ring and `(C, J)` a site whose objects live one universe above its
morphisms (the shape of the small étale site of a scheme). For sheaves `F`, `G` of `R`-modules,
`Stacks.ConstantSheaf.moduleSheafHom J R F G` is the sheaf `𝓗om(F, G)` whose sections over `U`
are the morphisms `F|_U ⟶ G|_U` on the slice site. Its **evaluation**
`𝓗om(F, G) ⊗ F ⟶ G`, `(α, x) ↦ α(x)`, exhibits it as an internal hom from `F` to `G` for the
tensor product of sheaves `CategoryTheory.Sheaf.monoidalCategory`: for every sheaf `T`,

`(T ⟶ 𝓗om(F, G)) → (T ⊗ F ⟶ G)`,  `g ↦ (g ▷ F) ≫ ev`

is a bijection. The inverse sends `b : T ⊗ F ⟶ G` to the morphism whose value at a section `t`
of `T` over `U` is the morphism `F|_U ⟶ G|_U` given over `W ⟶ U` by `x ↦ b(t|_W ⊗ x)`.

## Main definitions

* `Stacks.ConstantSheaf.moduleSheafHomEvaluation`: the evaluation `𝓗om(F, G) ⊗ F ⟶ G`.
* `Stacks.ConstantSheaf.moduleSheafHomCurry`: the morphism `T ⟶ 𝓗om(F, G)` attached to
  `T ⊗ F ⟶ G`.

## Main results

* `CategoryTheory.Sheaf.eq_tensorDesc`: every morphism out of a tensor product of sheaves of
  modules is `CategoryTheory.Sheaf.tensorDesc` of its bilinear components.
* `Stacks.ConstantSheaf.tensorHomBijective_moduleSheafHomEvaluation`: **`𝓗om(F, G)` with its
  evaluation is an internal hom from `F` to `G`.**
* `Stacks.ConstantSheaf.moduleSheafHomMap_whiskerRight_comp_moduleSheafHomEvaluation`: the
  evaluation is natural in `G`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C} {R : Type} [CommRing R]

attribute [local instance] monoidalCategory

variable [(J.W (A := ModuleCat.{u + 1} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{u + 1} R)]

/-- The tensor product of two sheaves of modules is the sheafification of the sectionwise tensor
product of the underlying presheaves. -/
def tensorIsoSheafifyTensor (F G : Sheaf J (ModuleCat.{u + 1} R)) :
    F ⊗ G ≅ (presheafToSheaf J (ModuleCat.{u + 1} R)).obj (F.obj ⊗ G.obj) :=
  (sheafificationIso F ⊗ᵢ sheafificationIso G) ≪≫
    Functor.Monoidal.μIso (presheafToSheaf J (ModuleCat.{u + 1} R)) F.obj G.obj

/-- The morphism of presheaves out of the sectionwise tensor product underlying a morphism out
of the tensor product of sheaves. -/
def tensorPresheafComponent {F G H : Sheaf J (ModuleCat.{u + 1} R)} (b : F ⊗ G ⟶ H) :
    F.obj ⊗ G.obj ⟶ H.obj :=
  (sheafificationAdjunction J (ModuleCat.{u + 1} R)).homEquiv _ _
    ((tensorIsoSheafifyTensor F G).inv ≫ b)

/-- `CategoryTheory.Sheaf.tensorDesc β` is the composite of the identification of `F ⊗ G` with
the sheafified sectionwise tensor product and the sheafification of
`CategoryTheory.Sheaf.presheafTensorDesc β`. -/
theorem tensorDesc_eq_comp {F G H : Sheaf J (ModuleCat.{u + 1} R)}
    (β : ∀ U, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β U a b) = β V (F.obj.map f a) (G.obj.map f b)) :
    tensorDesc.{u + 1, u, u + 1, 0} β hβ = (tensorIsoSheafifyTensor F G).hom ≫
      ((sheafificationAdjunction J (ModuleCat.{u + 1} R)).homEquiv _ _).symm
        (presheafTensorDesc.{u + 1, u, u + 1, 0} β hβ) :=
  rfl

/-- The presheaf component of `CategoryTheory.Sheaf.tensorDesc β` is the sectionwise
`CategoryTheory.Sheaf.presheafTensorDesc β`. -/
theorem tensorPresheafComponent_tensorDesc {F G H : Sheaf J (ModuleCat.{u + 1} R)}
    (β : ∀ U, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β U a b) = β V (F.obj.map f a) (G.obj.map f b)) :
    tensorPresheafComponent (tensorDesc.{u + 1, u, u + 1, 0} β hβ) =
      presheafTensorDesc.{u + 1, u, u + 1, 0} β hβ := by
  rw [tensorPresheafComponent, tensorDesc_eq_comp, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- The presheaf component of `b ≫ w` is the presheaf component of `b` followed by `w`. -/
theorem tensorPresheafComponent_comp {F G H H' : Sheaf J (ModuleCat.{u + 1} R)} (b : F ⊗ G ⟶ H)
    (w : H ⟶ H') : tensorPresheafComponent (b ≫ w) = tensorPresheafComponent b ≫ w.hom := by
  rw [tensorPresheafComponent, tensorPresheafComponent, ← Category.assoc,
    Adjunction.homEquiv_naturality_right]
  rfl

/-- A morphism out of a tensor product of sheaves of modules is determined by its presheaf
component. -/
theorem tensor_hom_ext_presheafComponent {F G H : Sheaf J (ModuleCat.{u + 1} R)}
    {b b' : F ⊗ G ⟶ H} (h : tensorPresheafComponent b = tensorPresheafComponent b') : b = b' :=
  (cancel_epi (tensorIsoSheafifyTensor F G).inv).1
    (((sheafificationAdjunction J (ModuleCat.{u + 1} R)).homEquiv _ _).injective h)

/-- The bilinear components of a morphism out of a tensor product of sheaves of modules: its
presheaf component on pure tensors. -/
def tensorBilinear {F G H : Sheaf J (ModuleCat.{u + 1} R)} (b : F ⊗ G ⟶ H) (U : Cᵒᵖ) :
    F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U :=
  (TensorProduct.mk R (F.obj.obj U) (G.obj.obj U)).compr₂ ((tensorPresheafComponent b).app U).hom

/-- The bilinear component of `b` at `U` sends `(a, c)` to the presheaf component of `b` at `U`
applied to `a ⊗ₜ c`. -/
theorem tensorBilinear_apply {F G H : Sheaf J (ModuleCat.{u + 1} R)} (b : F ⊗ G ⟶ H) (U : Cᵒᵖ)
    (a : F.obj.obj U) (c : G.obj.obj U) :
    tensorBilinear b U a c = ((tensorPresheafComponent b).app U).hom (a ⊗ₜ c) :=
  rfl

/-- The bilinear components of `b` commute with restriction along `f : U ⟶ V`. -/
theorem tensorBilinear_naturality {F G H : Sheaf J (ModuleCat.{u + 1} R)} (b : F ⊗ G ⟶ H)
    {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (c : G.obj.obj U) :
    H.obj.map f (tensorBilinear b U a c) =
      tensorBilinear b V (F.obj.map f a) (G.obj.map f c) :=
  (ConcreteCategory.congr_hom ((tensorPresheafComponent b).naturality f) (a ⊗ₜ c)).symm

/-- **Every morphism out of a tensor product of sheaves of modules is
`CategoryTheory.Sheaf.tensorDesc` of its bilinear components.** -/
theorem eq_tensorDesc {F G H : Sheaf J (ModuleCat.{u + 1} R)} (b : F ⊗ G ⟶ H) :
    b = tensorDesc.{u + 1, u, u + 1, 0} (tensorBilinear b)
      (fun f a c => tensorBilinear_naturality b f a c) := by
  refine tensor_hom_ext_presheafComponent ?_
  rw [tensorPresheafComponent_tensorDesc]
  exact NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| TensorProduct.ext' fun a c => rfl

/-- `CategoryTheory.Sheaf.tensorDesc` depends only on the values of the bilinear family. -/
theorem tensorDesc_congr {F G H : Sheaf J (ModuleCat.{u + 1} R)}
    {β β' : ∀ U, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U}
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β U a b) = β V (F.obj.map f a) (G.obj.map f b))
    (hβ' : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β' U a b) = β' V (F.obj.map f a) (G.obj.map f b))
    (h : ∀ U a b, β U a b = β' U a b) :
    tensorDesc.{u + 1, u, u + 1, 0} β hβ = tensorDesc.{u + 1, u, u + 1, 0} β' hβ' := by
  obtain rfl : β = β' := funext fun U => LinearMap.ext₂ (h U)
  rfl

/-- The bilinear family of `CategoryTheory.Sheaf.tensorDesc β` is `β`. -/
theorem tensorDesc_apply_eq_of_eq {F G H : Sheaf J (ModuleCat.{u + 1} R)}
    {β β' : ∀ U, F.obj.obj U →ₗ[R] G.obj.obj U →ₗ[R] H.obj.obj U}
    (hβ : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β U a b) = β V (F.obj.map f a) (G.obj.map f b))
    (hβ' : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (a : F.obj.obj U) (b : G.obj.obj U),
      H.obj.map f (β' U a b) = β' V (F.obj.map f a) (G.obj.map f b))
    (h : tensorDesc.{u + 1, u, u + 1, 0} β hβ = tensorDesc.{u + 1, u, u + 1, 0} β' hβ')
    (U : Cᵒᵖ) (a : F.obj.obj U) (b : G.obj.obj U) : β U a b = β' U a b := by
  have h' := congrArg tensorPresheafComponent h
  rw [tensorPresheafComponent_tensorDesc, tensorPresheafComponent_tensorDesc] at h'
  exact ConcreteCategory.congr_hom (congrArg (fun φ : F.obj ⊗ G.obj ⟶ H.obj => φ.app U) h') (a ⊗ₜ b)

end CategoryTheory.Sheaf

namespace Stacks.ConstantSheaf

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) (R : Type) [CommRing R]

section Evaluation

variable (F G : Sheaf J (ModuleCat.{u + 1} R))

/-- A section of `𝓗om(F, G)` over `X` at an object `W` of the slice over `X` is its restriction
to `W.left`, read at the identity of `W.left`. -/
theorem moduleSheafHom_hom_app_eq_map {X : C} (α : (moduleSheafHom J R F G).obj.obj (op X))
    (W : Over X) :
    α.hom.app (op W) =
      ((moduleSheafHom J R F G).obj.map W.hom.op α).hom.app (op (Over.mk (𝟙 W.left))) := by
  rw [moduleSheafHom_obj_map_apply]
  exact (CategoryTheory.presheafHom_map_app (𝟙 W.left) W.hom W.hom (Category.id_comp _)
    α.hom).symm

/-- The evaluation of a section of `𝓗om(F, G)` on a section of `F` over the same object. -/
def moduleSheafHomPairing (U : Cᵒᵖ) :
    (moduleSheafHom J R F G).obj.obj U →ₗ[R] F.obj.obj U →ₗ[R] G.obj.obj U where
  toFun α := (α.hom.app (op (Over.mk (𝟙 U.unop)))).hom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The pairing of a section `α` of `𝓗om(F, G)` over `U` with `x` is `α` evaluated at the identity
of `U`, applied to `x`. -/
theorem moduleSheafHomPairing_apply (U : Cᵒᵖ) (α : (moduleSheafHom J R F G).obj.obj U)
    (x : F.obj.obj U) :
    moduleSheafHomPairing J R F G U α x = (α.hom.app (op (Over.mk (𝟙 U.unop)))).hom x :=
  rfl

/-- The pairing of `𝓗om(F, G)` with `F` commutes with restriction along `f : U ⟶ V`. -/
theorem moduleSheafHomPairing_map {U V : Cᵒᵖ} (f : U ⟶ V)
    (α : (moduleSheafHom J R F G).obj.obj U) (x : F.obj.obj U) :
    G.obj.map f (moduleSheafHomPairing J R F G U α x) =
      moduleSheafHomPairing J R F G V ((moduleSheafHom J R F G).obj.map f α) (F.obj.map f x) := by
  have hα : F.obj.map f ≫ α.hom.app (op (Over.mk f.unop)) =
      α.hom.app (op (Over.mk (𝟙 U.unop))) ≫ G.obj.map f :=
    α.hom.naturality (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 U.unop)).op
  rw [moduleSheafHomPairing_apply, moduleSheafHomPairing_apply,
    show ((moduleSheafHom J R F G).obj.map f α).hom.app (op (Over.mk (𝟙 V.unop))) = _ from
      (moduleSheafHom_hom_app_eq_map J R F G α (Over.mk f.unop)).symm]
  exact (ConcreteCategory.congr_hom hα x).symm

/-- Two maps into `𝓗om(F, G)` are equal if their pairings with `F` agree. -/
theorem moduleSheafHom_hom_ext {T : Sheaf J (ModuleCat.{u + 1} R)}
    {g g' : T ⟶ moduleSheafHom J R F G}
    (h : ∀ U a x, moduleSheafHomPairing J R F G U ((g.hom.app U).hom a) x =
      moduleSheafHomPairing J R F G U ((g'.hom.app U).hom a) x) : g = g' := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  refine ModuleCat.hom_ext (LinearMap.ext fun (x : F.obj.obj (op W.unop.left)) => ?_)
  have hn : ∀ ψ : T ⟶ moduleSheafHom J R F G,
      (moduleSheafHom J R F G).obj.map W.unop.hom.op ((ψ.hom.app U).hom a) =
        (ψ.hom.app (op W.unop.left)).hom (T.obj.map W.unop.hom.op a) := fun ψ =>
    (ConcreteCategory.congr_hom (ψ.hom.naturality W.unop.hom.op) a).symm
  rw [moduleSheafHom_hom_app_eq_map J R F G ((g.hom.app U).hom a) W.unop,
    moduleSheafHom_hom_app_eq_map J R F G ((g'.hom.app U).hom a) W.unop, hn g, hn g']
  exact h (op W.unop.left) _ x

attribute [local instance] Sheaf.monoidalCategory

variable [(J.W (A := ModuleCat.{u + 1} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{u + 1} R)]

/-- **The evaluation `𝓗om(F, G) ⊗ F ⟶ G`**, `(α, x) ↦ α(x)`. -/
def moduleSheafHomEvaluation : moduleSheafHom J R F G ⊗ F ⟶ G :=
  Sheaf.tensorDesc.{u + 1, u, u + 1, 0} (moduleSheafHomPairing J R F G)
    (fun f a b => moduleSheafHomPairing_map J R F G f a b)

end Evaluation

section Curry

attribute [local instance] Sheaf.monoidalCategory

variable [(J.W (A := ModuleCat.{u + 1} R)).IsMonoidal] [HasWeakSheafify J (ModuleCat.{u + 1} R)]
variable {J R} {T F G : Sheaf J (ModuleCat.{u + 1} R)}

/-- The morphism `F|_U ⟶ G|_U` attached to `b : T ⊗ F ⟶ G` and a section `t` of `T` over `U`:
over `W ⟶ U` it is `x ↦ b(t|_W ⊗ x)`. -/
def moduleSheafHomCurrySection (b : T ⊗ F ⟶ G) {U : C} (t : T.obj.obj (op U)) :
    (J.overPullback (ModuleCat.{u + 1} R) U).obj F ⟶
      (J.overPullback (ModuleCat.{u + 1} R) U).obj G :=
  ⟨{ app := fun W => ModuleCat.ofHom
        (Sheaf.tensorBilinear b (op W.unop.left) (T.obj.map W.unop.hom.op t))
     naturality := fun W W' φ => by
       refine ModuleCat.hom_ext (LinearMap.ext fun (x : F.obj.obj (op W.unop.left)) => ?_)
       have hw : φ.unop.left ≫ W.unop.hom = W'.unop.hom := Over.w φ.unop
       have ht : T.obj.map W'.unop.hom.op t =
           T.obj.map φ.unop.left.op (T.obj.map W.unop.hom.op t) := by
         rw [← hw, op_comp, CategoryTheory.Functor.map_comp]
         rfl
       change Sheaf.tensorBilinear b (op W'.unop.left) (T.obj.map W'.unop.hom.op t)
           (F.obj.map φ.unop.left.op x) =
         G.obj.map φ.unop.left.op
           (Sheaf.tensorBilinear b (op W.unop.left) (T.obj.map W.unop.hom.op t) x)
       rw [Sheaf.tensorBilinear_naturality, ht] }⟩

/-- Over `W ⟶ U`, `Stacks.ConstantSheaf.moduleSheafHomCurrySection b t` sends `x` to the bilinear
component of `b` applied to `t|_W` and `x`. -/
theorem moduleSheafHomCurrySection_app_apply (b : T ⊗ F ⟶ G) {U : C} (t : T.obj.obj (op U))
    (W : (Over U)ᵒᵖ) (x : F.obj.obj (op W.unop.left)) :
    ((moduleSheafHomCurrySection b t).hom.app W).hom x =
      Sheaf.tensorBilinear b (op W.unop.left) (T.obj.map W.unop.hom.op t) x :=
  rfl

/-- **The morphism `T ⟶ 𝓗om(F, G)` attached to `b : T ⊗ F ⟶ G`**: a section `t` over `U` goes
to the morphism `F|_U ⟶ G|_U`, `x ↦ b(t|_W ⊗ x)` over `W ⟶ U`. -/
def moduleSheafHomCurry (b : T ⊗ F ⟶ G) : T ⟶ moduleSheafHom J R F G :=
  ⟨{ app := fun U => ModuleCat.ofHom
        { toFun := fun t => moduleSheafHomCurrySection b t
          map_add' := fun t t' => by
            apply Sheaf.hom_ext
            apply NatTrans.ext
            funext W
            refine ModuleCat.hom_ext (LinearMap.ext fun (x : F.obj.obj (op W.unop.left)) => ?_)
            change Sheaf.tensorBilinear b (op W.unop.left) (T.obj.map W.unop.hom.op (t + t')) x =
              Sheaf.tensorBilinear b (op W.unop.left) (T.obj.map W.unop.hom.op t) x +
                Sheaf.tensorBilinear b (op W.unop.left) (T.obj.map W.unop.hom.op t') x
            rw [map_add, LinearMap.map_add₂]
          map_smul' := fun r t => by
            apply Sheaf.hom_ext
            apply NatTrans.ext
            funext W
            refine ModuleCat.hom_ext (LinearMap.ext fun (x : F.obj.obj (op W.unop.left)) => ?_)
            change Sheaf.tensorBilinear b (op W.unop.left) (T.obj.map W.unop.hom.op (r • t)) x =
              r • Sheaf.tensorBilinear b (op W.unop.left) (T.obj.map W.unop.hom.op t) x
            rw [map_smul, LinearMap.map_smul₂] }
     naturality := fun U V f => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro t
       apply Sheaf.hom_ext
       apply NatTrans.ext
       funext W
       refine ModuleCat.hom_ext (LinearMap.ext fun (x : F.obj.obj (op W.unop.left)) => ?_)
       have ht : T.obj.map (W.unop.hom ≫ f.unop).op t =
           T.obj.map W.unop.hom.op (T.obj.map f t) := by
         rw [op_comp, CategoryTheory.Functor.map_comp]
         rfl
       change Sheaf.tensorBilinear b (op W.unop.left) (T.obj.map W.unop.hom.op (T.obj.map f t)) x =
         Sheaf.tensorBilinear b (op W.unop.left) (T.obj.map (W.unop.hom ≫ f.unop).op t) x
       rw [ht] }⟩

/-- The value of `Stacks.ConstantSheaf.moduleSheafHomCurry b` at a section `t` of `T` over `U` is
`Stacks.ConstantSheaf.moduleSheafHomCurrySection b t`. -/
theorem moduleSheafHomCurry_app_apply (b : T ⊗ F ⟶ G) (U : Cᵒᵖ) (t : T.obj.obj U) :
    ((moduleSheafHomCurry b).hom.app U).hom t = moduleSheafHomCurrySection b (U := U.unop) t :=
  rfl

variable (J R F G)

/-- Precomposing the evaluation with `g ▷ F` is `CategoryTheory.Sheaf.tensorDesc` of the
pairing read through `g`. -/
theorem whiskerRight_comp_moduleSheafHomEvaluation (g : T ⟶ moduleSheafHom J R F G) :
    g ▷ F ≫ moduleSheafHomEvaluation J R F G =
      Sheaf.tensorDesc.{u + 1, u, u + 1, 0}
        (fun U => (moduleSheafHomPairing J R F G U).comp (g.hom.app U).hom)
        (fun {U V} f a b => (moduleSheafHomPairing_map J R F G f ((g.hom.app U).hom a) b).trans
          (congrArg (fun z => moduleSheafHomPairing J R F G V z (F.obj.map f b))
            (ConcreteCategory.congr_hom (g.hom.naturality f) a).symm)) :=
  Sheaf.whiskerRight_tensorDesc.{u + 1, u, u + 1, 0} g _ _

/-- **The evaluation is natural in the target**: `𝓗om(F, w) ⊗ F ≫ ev = ev ≫ w`. -/
theorem moduleSheafHomMap_whiskerRight_comp_moduleSheafHomEvaluation
    {G' : Sheaf J (ModuleCat.{u + 1} R)} (w : G ⟶ G') :
    moduleSheafHomMap J R (𝟙 F) w ▷ F ≫ moduleSheafHomEvaluation J R F G' =
      moduleSheafHomEvaluation J R F G ≫ w := by
  apply Sheaf.tensor_hom_ext_presheafComponent
  rw [whiskerRight_comp_moduleSheafHomEvaluation, Sheaf.tensorPresheafComponent_comp,
    moduleSheafHomEvaluation, Sheaf.tensorPresheafComponent_tensorDesc,
    Sheaf.tensorPresheafComponent_tensorDesc]
  exact NatTrans.ext <| funext fun U => ModuleCat.hom_ext <| TensorProduct.ext' fun α x => rfl

/-- **`𝓗om(F, G)` with its evaluation is an internal hom from `F` to `G`**: for every sheaf `T`,
`g ↦ (g ▷ F) ≫ ev` is a bijection `(T ⟶ 𝓗om(F, G)) ≃ (T ⊗ F ⟶ G)`, with inverse
`Stacks.ConstantSheaf.moduleSheafHomCurry`. -/
theorem tensorHomBijective_moduleSheafHomEvaluation :
    ∀ T : Sheaf J (ModuleCat.{u + 1} R), Function.Bijective
      fun g : T ⟶ moduleSheafHom J R F G => g ▷ F ≫ moduleSheafHomEvaluation J R F G := by
  intro T
  refine ⟨fun g g' hgg' => ?_, fun b => ⟨moduleSheafHomCurry b, ?_⟩⟩
  · refine moduleSheafHom_hom_ext J R F G fun U a x => ?_
    simp only [whiskerRight_comp_moduleSheafHomEvaluation] at hgg'
    exact Sheaf.tensorDesc_apply_eq_of_eq _ _ hgg' U a x
  · show _ ▷ F ≫ moduleSheafHomEvaluation J R F G = b
    rw [whiskerRight_comp_moduleSheafHomEvaluation]
    refine Eq.trans ?_ (Sheaf.eq_tensorDesc b).symm
    refine Sheaf.tensorDesc_congr _ _ fun U a x => ?_
    show Sheaf.tensorBilinear b (op U.unop) (T.obj.map (𝟙 U.unop).op a) x =
      Sheaf.tensorBilinear b U a x
    have ha : T.obj.map (𝟙 U.unop).op a = a := ConcreteCategory.congr_hom (T.obj.map_id U) a
    exact congrArg (fun z => Sheaf.tensorBilinear b U z x) ha

end Curry

end Stacks.ConstantSheaf

end
