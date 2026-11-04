module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Free sheaves of modules on coproducts of representables

Let `(C, J)` be a site, `S` a sheaf of rings on it and `V : ι → C` a family of objects indexed by
a type `ι` in the universe of the sections. The free sheaf of `S`-modules on the coproduct of the
presheaves represented by the `V i` corepresents the functor `M ↦ ∏ᵢ M(V i)`. Consequently:

* every left adjoint of the pushforward `SheafOfModules.pushforward φ` along a continuous functor
  `Φ : C ⥤ D` sends it to the free sheaf of modules on the coproduct of the presheaves represented
  by the `Φ (V i)` (`leftAdjointObjFreeSigmaYonedaIso`);
* on an essentially small site every sheaf of modules is a quotient of such a free sheaf of
  modules (`exists_epi_freeSigmaYoneda`).

## Main definitions

* `Stacks.SheafOfModules.SigmaYoneda.sigmaYoneda`: the coproduct of the presheaves of sets
  represented by the `V i`.
* `Stacks.SheafOfModules.SigmaYoneda.freeSigmaYoneda`: the sheafification of the free presheaf of
  modules on it.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace Stacks.SheafOfModules.SigmaYoneda

universe u u₁ u₂

section Presheaf

variable {C : Type u₁} [Category.{u} C] {ι : Type u} (V : ι → C)

/-- The coproduct of the presheaves of sets represented by the objects `V i`: its sections over
`W` are the pairs of an index `i` and a morphism `W ⟶ V i`. -/
abbrev sigmaYoneda : Cᵒᵖ ⥤ Type u where
  obj W := Σ i, (W.unop ⟶ V i)
  map f := ↾fun x ↦ ⟨x.1, f.unop ≫ x.2⟩

/-- The restriction along `f : W ⟶ W'` of a section `⟨i, g⟩` of `sigmaYoneda V` is
`⟨i, f.unop ≫ g⟩`. -/
@[simp]
theorem sigmaYoneda_map_apply {W W' : Cᵒᵖ} (f : W ⟶ W') (x : (sigmaYoneda V).obj W) :
    (sigmaYoneda V).map f x = ⟨x.1, f.unop ≫ x.2⟩ :=
  rfl

/-- A morphism out of the coproduct of the presheaves represented by the `V i` is a family of
sections over the `V i` (the Yoneda lemma). -/
def homEquiv (X : Cᵒᵖ ⥤ Type u) : (sigmaYoneda V ⟶ X) ≃ ∀ i, X.obj (op (V i)) where
  toFun f i := f.app (op (V i)) ⟨i, 𝟙 _⟩
  invFun x :=
    { app W := ↾fun y ↦ X.map y.2.op (x y.1)
      naturality W W' f := by
        ext y
        simp }
  left_inv f := by
    ext W ⟨i, g⟩
    exact (NatTrans.naturality_apply f g.op ⟨i, 𝟙 _⟩).symm.trans
      (congrArg (f.app W) (congrArg (Sigma.mk i) (Category.comp_id g)))
  right_inv x := by
    funext i
    simp

/-- The family of sections of `Y` attached to `f ≫ g` is the image under `g` of the family
attached to `f`. -/
theorem homEquiv_comp {X Y : Cᵒᵖ ⥤ Type u} (f : sigmaYoneda V ⟶ X) (g : X ⟶ Y) (i : ι) :
    homEquiv V Y (f ≫ g) i = g.app _ (homEquiv V X f i) :=
  rfl

end Presheaf

section Sheaf

variable {C : Type u₁} [Category.{u} C] {J : GrothendieckTopology C} (S : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {ι : Type u} (V : ι → C)

/-- The free sheaf of `S`-modules on the coproduct of the presheaves represented by the `V i`. -/
def freeSigmaYoneda : SheafOfModules.{u} S :=
  (PresheafOfModules.sheafification (𝟙 S.obj)).obj
    ((PresheafOfModules.free S.obj).obj (sigmaYoneda V))

/-- **The universal property of `freeSigmaYoneda`**: a morphism out of it is a family of
sections over the `V i`. -/
def freeSigmaYonedaHomEquiv (M : SheafOfModules.{u} S) :
    (freeSigmaYoneda S V ⟶ M) ≃ ∀ i, M.val.obj (op (V i)) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).homEquiv _ M).trans
    (PresheafOfModules.freeHomEquiv.trans (homEquiv V _))

/-- The family of sections of `N` attached to `f ≫ g` is the image under `g` of the family
attached to `f`. -/
theorem freeSigmaYonedaHomEquiv_comp {M N : SheafOfModules.{u} S} (f : freeSigmaYoneda S V ⟶ M)
    (g : M ⟶ N) (i : ι) :
    freeSigmaYonedaHomEquiv S V N (f ≫ g) i = g.val.app _ (freeSigmaYonedaHomEquiv S V M f i) :=
  rfl

end Sheaf

section LeftAdjoint

variable {C : Type u₁} [Category.{u} C] {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{u} D] {K : GrothendieckTopology D}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {Φ : C ⥤ D} {_ : Φ.IsContinuous J K} {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (Φ.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  {E : SheafOfModules.{u} S ⥤ SheafOfModules.{u} R} (adj : E ⊣ SheafOfModules.pushforward.{u} φ)
  {ι : Type u} (V : ι → C)

/-- The bijection `Hom(E(free(∐ yV)), M) ≃ Hom(free(∐ yΦV), M)`, natural in `M`. -/
def leftAdjointHomEquiv (M : SheafOfModules.{u} R) :
    (E.obj (freeSigmaYoneda S V) ⟶ M) ≃ (freeSigmaYoneda R (fun i ↦ Φ.obj (V i)) ⟶ M) :=
  (adj.homEquiv _ M).trans ((freeSigmaYonedaHomEquiv S V _).trans
    (freeSigmaYonedaHomEquiv R (fun i ↦ Φ.obj (V i)) M).symm)

/-- `leftAdjointHomEquiv` sends `f` to the morphism out of the free sheaf of modules on the
`Φ (V i)` whose family of sections is that of the adjoint transpose of `f`. -/
theorem leftAdjointHomEquiv_apply (M : SheafOfModules.{u} R)
    (f : E.obj (freeSigmaYoneda S V) ⟶ M) :
    leftAdjointHomEquiv φ adj V M f = (freeSigmaYonedaHomEquiv R (fun i ↦ Φ.obj (V i)) M).symm
      (freeSigmaYonedaHomEquiv S V _ (adj.homEquiv _ M f)) :=
  rfl

/-- The family of sections attached to `leftAdjointHomEquiv φ adj V M f` is the family of sections
attached to the adjoint transpose of `f`. -/
theorem freeSigmaYonedaHomEquiv_leftAdjointHomEquiv (M : SheafOfModules.{u} R)
    (f : E.obj (freeSigmaYoneda S V) ⟶ M) :
    freeSigmaYonedaHomEquiv R (fun i ↦ Φ.obj (V i)) M (leftAdjointHomEquiv φ adj V M f) =
      freeSigmaYonedaHomEquiv S V _ (adj.homEquiv _ M f) :=
  Equiv.apply_symm_apply _ _

/-- The bijection `leftAdjointHomEquiv` is natural in the target sheaf of modules. -/
theorem leftAdjointHomEquiv_comp {M N : SheafOfModules.{u} R}
    (f : E.obj (freeSigmaYoneda S V) ⟶ M) (g : M ⟶ N) :
    leftAdjointHomEquiv φ adj V N (f ≫ g) = leftAdjointHomEquiv φ adj V M f ≫ g := by
  apply (freeSigmaYonedaHomEquiv R (fun i ↦ Φ.obj (V i)) N).injective
  funext i
  rw [freeSigmaYonedaHomEquiv_comp, freeSigmaYonedaHomEquiv_leftAdjointHomEquiv,
    freeSigmaYonedaHomEquiv_leftAdjointHomEquiv, Adjunction.homEquiv_naturality_right,
    freeSigmaYonedaHomEquiv_comp]
  rfl

/-- **A left adjoint of the pushforward of sheaves of modules sends the free sheaf of modules on
a coproduct of representables to the free sheaf of modules on the coproduct of the images.** -/
def leftAdjointObjFreeSigmaYonedaIso :
    E.obj (freeSigmaYoneda S V) ≅ freeSigmaYoneda R (fun i ↦ Φ.obj (V i)) where
  hom := (leftAdjointHomEquiv φ adj V _).symm (𝟙 _)
  inv := leftAdjointHomEquiv φ adj V _ (𝟙 _)
  hom_inv_id := by
    apply (leftAdjointHomEquiv φ adj V _).injective
    rw [leftAdjointHomEquiv_comp, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    rw [← leftAdjointHomEquiv_comp, Category.id_comp, Equiv.apply_symm_apply]

end LeftAdjoint

section Cover

variable {C : Type u₁} [Category.{u} C] {J : GrothendieckTopology C} (S : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **On an essentially small site every sheaf of modules is a quotient of a free sheaf of
modules on a coproduct of representables**, indexed by a type in the universe of the sections. -/
theorem exists_epi_freeSigmaYoneda [EssentiallySmall.{u} C] (M : SheafOfModules.{u} S) :
    ∃ (ι : Type u) (V : ι → C) (p : freeSigmaYoneda S V ⟶ M), Epi p := by
  let e := equivSmallModel.{u} C
  let V : (Σ j : SmallModel.{u} C, M.val.obj (op (e.inverse.obj j))) → C :=
    fun x ↦ e.inverse.obj x.1
  let q : (PresheafOfModules.free S.obj).obj (sigmaYoneda V) ⟶
      (SheafOfModules.forget S ⋙ PresheafOfModules.restrictScalars (𝟙 S.obj)).obj M :=
    PresheafOfModules.freeHomEquiv.symm ((homEquiv V _).symm fun x ↦ x.2)
  have hq : Epi q := by
    refine PresheafOfModules.epi_of_surjective (fun W m ↦ ?_)
    let c := e.unitIso.app W.unop
    refine ⟨ModuleCat.freeMk ⟨⟨e.functor.obj W.unop, M.val.map c.inv.op m⟩, c.hom⟩,
      (ModuleCat.freeDesc_apply _ _).trans ?_⟩
    have key : ∀ {X Y : C} (c : X ≅ Y) (x : M.val.presheaf.obj (op X)),
        M.val.presheaf.map c.hom.op (M.val.presheaf.map c.inv.op x) = x := fun c x ↦ by
      rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp,
        Iso.hom_inv_id, op_id, CategoryTheory.Functor.map_id]
      rfl
    exact key c m
  have : IsIso ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).counit.app M) :=
    NatIso.isIso_app_of_isIso _ M
  exact ⟨_, V, (PresheafOfModules.sheafification (𝟙 S.obj)).map q ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).counit.app M,
    epi_comp' (Functor.map_epi _ _) inferInstance⟩

end Cover

end Stacks.SheafOfModules.SigmaYoneda
