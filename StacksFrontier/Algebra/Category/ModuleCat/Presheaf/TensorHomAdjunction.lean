module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomTensorCurrying
import StacksCore.Tactic.StacksAttribute

/-!
# The tensor--internal-Hom adjunction for presheaves of modules

Let `O` be a presheaf of commutative rings on a category `C`. For presheaves of `O`-modules
`F`, `G`, `H`, morphisms out of the tensor product are canonically identified with morphisms
into the internal Hom presheaf of Stacks 03EM,

`Hom(F ⊗_O G, H) = Hom(F, Hom_O(G, H))`,

naturally in `F` and in `H`. This clause of Stacks 03EO is recorded here as an adjunction:
tensoring on the right by `G` is left adjoint to internal Hom out of `G`.

The correspondence is the currying isomorphism of Stacks 03EO one slice up. A morphism
`F ⊗ G ⟶ H` restricts to each slice `C/U`, and the currying isomorphism turns that restriction
into a morphism `F|_U ⟶ Hom_O(G, H)|_U`; evaluating at the identity of the slice gives the
global morphism `F ⟶ Hom_O(G, H)`, and reading the construction backwards inverts it.

## Main definitions

* `Stacks.PresheafOfModules.InternalHom.curryGlobal` and `uncurryGlobal`: the two mutually
  inverse maps, with `presheafTensorHomEquivAux` the resulting bijection.
* `Stacks.PresheafOfModules.InternalHom.presheafTensorHomAdjunction`: the adjunction.

## Main results

* `Stacks.PresheafOfModules.InternalHom.presheafTensorHomEquiv`: the hom-equivalence the
  adjunction supplies.
* `Stacks.PresheafOfModules.InternalHom.presheafTensorHomEquiv_apply`: on sections it is the
  usual currying formula, which pins the equivalence down.

## Implementation notes

Global currying is obtained from the slice-level `currySectionMap` of Stacks 03EO at the
identity `𝟙 U`, so its `O(U)`-linearity is inherited rather than re-proved; `curryGlobalMap`
is exactly that specialization. Uncurrying is `TensorProduct.lift` of the composite of two
honest linear maps, `evalAtIdLinear` after `globalHomApplyLinear`, so its bilinearity is also
free.

The retyping discipline of `TensorInternalHomCurrying` is continued here: `globalTensorHom`
presents a global morphism out of `F ⊗ G` as a `LinearMap` on an honest `TensorProduct`,
`globalTmul` is a pure tensor read as a section of `F ⊗ G`, and `ofGlobalHom` /
`ofGlobalTensorHom` go the other way. Each is a definition whose body is its own argument, so
the identification is checked once at default transparency, where it is available.

The structure presheaf and its modules are valued in universe `max u v w`, where the extra
parameter `w` allows their size to exceed that of the underlying category. The common ring
and module universe is the one required by Mathlib's monoidal structure on presheaves of modules.

Only the `presheaf_tensor_hom_adjunction` clause of Stacks 03EO is proved here; the sheaf
analogue is a separate statement. That clause's covering set is exactly
`presheafTensorHomAdjunction` and `presheafTensorHomEquiv_apply`, which carry the tag; the
intermediate retyping helpers do not. Both carry the independent universes `v`, `u` and `w`, and
`internalHomSecondFunctor` is instantiated at `.{v, u, max u v w, u}`.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

namespace Stacks.PresheafOfModules.InternalHom

universe v u w

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{max u v w})
variable (F G H : _root_.PresheafOfModules.{max u v w} (Oforget O))

/-- A global morphism out of a tensor product, retyped as a linear map on an honest tensor
product of plain sections. -/
noncomputable def globalTensorHom (b : F ⊗ G ⟶ H) (W : C) :
    TensorProduct (O.obj (op W)) (F.obj (op W)) (G.obj (op W)) →ₗ[O.obj (op W)]
      H.obj (op W) :=
  (b.app (op W)).hom

/-- A pure tensor of plain sections, as a section of `F ⊗ G`. -/
noncomputable def globalTmul (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) : (F ⊗ G).obj X :=
  x ⊗ₜ[O.obj X] y

/-- A linear map of plain sections, as a morphism of the sections themselves. -/
noncomputable def ofGlobalHom (M N : _root_.PresheafOfModules.{max u v w} (Oforget O)) (X : Cᵒᵖ)
    (b : M.obj X →ₗ[O.obj X] N.obj X) : M.obj X ⟶ N.obj X :=
  letI : Module ((Oforget O).obj X) (M.obj X) := (M.obj X).isModule
  letI : Module ((Oforget O).obj X) (N.obj X) := (N.obj X).isModule
  letI : AddCommGroup (M.obj X) := (M.obj X).isAddCommGroup
  letI : AddCommGroup (N.obj X) := (N.obj X).isAddCommGroup
  ConcreteCategory.ofHom (C := ModuleCat ((Oforget O).obj X)) b

/-- A linear map on an honest tensor product, as a morphism out of `F ⊗ G`. -/
noncomputable def ofGlobalTensorHom (X : Cᵒᵖ)
    (b : TensorProduct (O.obj X) (F.obj X) (G.obj X) →ₗ[O.obj X] H.obj X) :
    (F ⊗ G).obj X ⟶ H.obj X :=
  letI : Module ((Oforget O).obj X) ((F ⊗ G).obj X) := ((F ⊗ G).obj X).isModule
  letI : Module ((Oforget O).obj X) (H.obj X) := (H.obj X).isModule
  letI : AddCommGroup ((F ⊗ G).obj X) := ((F ⊗ G).obj X).isAddCommGroup
  letI : AddCommGroup (H.obj X) := (H.obj X).isAddCommGroup
  ConcreteCategory.ofHom (C := ModuleCat ((Oforget O).obj X)) b

/-- Two morphisms out of `F ⊗ G` agree as soon as they agree on pure tensors. -/
theorem globalTensor_hom_ext {X : Cᵒᵖ} {Z : ModuleCat ((Oforget O).obj X)}
    {φ ψ : (F ⊗ G).obj X ⟶ Z}
    (h : ∀ (x : F.obj X) (y : G.obj X),
      φ.hom (globalTmul O F G X x y) = ψ.hom (globalTmul O F G X x y)) : φ = ψ := by
  refine ModuleCat.hom_ext (LinearMap.ext fun t ↦ ?_)
  induction t using TensorProduct.induction_on with
  | zero => exact (map_zero φ.hom).trans (map_zero ψ.hom).symm
  | tmul x y => exact h x y
  | add t t' ht ht' =>
      have hsum : φ.hom t + φ.hom t' = ψ.hom t + ψ.hom t' := by rw [ht, ht']
      exact (map_add φ.hom t t').trans (hsum.trans (map_add ψ.hom t t').symm)

/-- Restricting a global morphism to a slice does not change its values on pure tensors. -/
theorem restrTensorHom_restrFun_map (b : F ⊗ G ⟶ H) (U : C) {W : C} (h : W ⟶ U)
    (x : F.obj (op W)) (y : G.obj (op W)) :
    restrTensorHom O F G H U ((restrFun O U).map b) h (x ⊗ₜ y) =
      globalTensorHom O F G H b W (x ⊗ₜ y) := rfl

/-- Global currying, as an `O(U)`-linear map on sections. -/
noncomputable def curryGlobalMap (b : F ⊗ G ⟶ H) (U : C) :
    F.obj (op U) →ₗ[O.obj (op U)] (internalHom O G H).obj (op U) :=
  currySectionMap O F G H U ((restrFun O U).map b) (𝟙 U)

/-- Unfolding `curryGlobalMap`: it evaluates `b` on the restriction of `x` tensored with `y`. -/
theorem curryGlobalMap_apply (b : F ⊗ G ⟶ H) (U : C) (x : F.obj (op U)) {T : C} (q : T ⟶ U)
    (y : G.obj (op T)) :
    sectionOfRestr O H U q
        (((curryGlobalMap O F G H b U x).app (op (Over.mk q))).hom
          (restrSection O G U q y)) =
      globalTensorHom O F G H b T (F.restrictₛₗ q.op x ⊗ₜ y) := by
  show curryValueMap O F G H U ((restrFun O U).map b) (𝟙 U) x q y = _
  rw [curryValueMap_apply, Category.comp_id, restrTensorHom_restrFun_map]

/-- The restriction maps of the internal Hom presheaf are the re-indexing maps `homRestr`. -/
theorem internalHom_restrictₛₗ {S S' : C} (k : S' ⟶ S) (α : internalHomObj O G H S) :
    (internalHom O G H).restrictₛₗ k.op α = homRestr O G H k α := rfl

/-- Global currying commutes with restriction of the base. -/
theorem curryGlobalMap_restrict (b : F ⊗ G ⟶ H) {S S' : C} (k : S' ⟶ S) (x : F.obj (op S)) :
    curryGlobalMap O F G H b S' (F.restrictₛₗ k.op x) =
      homRestr O G H k (curryGlobalMap O F G H b S x) := by
  refine _root_.PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
  rw [homRestr_app_apply O G H k (curryGlobalMap O F G H b S x) W y]
  refine (curryGlobalMap_apply O F G H b S' (F.restrictₛₗ k.op x) W.unop.hom y).trans
    (Eq.trans ?_ (curryGlobalMap_apply O F G H b S x (W.unop.hom ≫ k) y).symm)
  rw [op_comp, restrictₛₗ_comp_apply]

/-- Global currying: a morphism `F ⊗ G ⟶ H` becomes a morphism `F ⟶ Hom_O(G, H)`. -/
noncomputable def curryGlobal (b : F ⊗ G ⟶ H) : F ⟶ internalHom O G H :=
  _root_.PresheafOfModules.Hom.mk
    (fun X ↦ ofGlobalHom O F (internalHom O G H) X (curryGlobalMap O F G H b X.unop))
    (fun {X Y} f ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      exact curryGlobalMap_restrict O F G H b f.unop x)

/-- Applying a morphism into the internal Hom presheaf, as an `O(W)`-linear map. -/
noncomputable def globalHomApplyLinear (a : F ⟶ internalHom O G H) (W : C) :
    F.obj (op W) →ₗ[O.obj (op W)] internalHomObj O G H W :=
  (a.app (op W)).hom

/-- Global uncurrying as a bilinear map, by construction. -/
noncomputable def uncurryGlobalBilin (a : F ⟶ internalHom O G H) (W : C) :
    F.obj (op W) →ₗ[O.obj (op W)] G.obj (op W) →ₗ[O.obj (op W)] H.obj (op W) :=
  (evalAtIdLinear O G H W).comp (globalHomApplyLinear O F G H a W)

/-- Global uncurrying on the tensor product of plain sections. -/
noncomputable def uncurryGlobalTensorMap (a : F ⟶ internalHom O G H) (W : C) :
    TensorProduct (O.obj (op W)) (F.obj (op W)) (G.obj (op W)) →ₗ[O.obj (op W)]
      H.obj (op W) :=
  TensorProduct.lift (uncurryGlobalBilin O F G H a W)

/-- Unfolding `uncurryGlobalTensorMap` on a pure tensor: evaluate at the identity of the
slice. -/
theorem uncurryGlobalTensorMap_tmul (a : F ⟶ internalHom O G H) (W : C)
    (x : F.obj (op W)) (y : G.obj (op W)) :
    uncurryGlobalTensorMap O F G H a W (x ⊗ₜ y) =
      sectionOfRestr O H W (𝟙 W)
        ((((a.app (op W)).hom x).app (op (Over.mk (𝟙 W)))).hom
          (restrSection O G W (𝟙 W) y)) := rfl

/-- A morphism into the internal Hom presheaf commutes with restriction, via `homRestr`. -/
private theorem hom_restrictₛₗ_internalHom (a : F ⟶ internalHom O G H) {S S' : C} (k : S' ⟶ S)
    (x : F.obj (op S)) :
    (a.app (op S')).hom (F.restrictₛₗ k.op x) = homRestr O G H k ((a.app (op S)).hom x) :=
  (naturality_restrictₛₗ O a k.op x).trans (internalHom_restrictₛₗ O G H k _)

/-- `uncurryGlobalTensorMap` is compatible with restriction. -/
theorem uncurryGlobalTensorMap_restrict (a : F ⟶ internalHom O G H) {S S' : C} (k : S' ⟶ S)
    (x : F.obj (op S)) (y : G.obj (op S)) :
    uncurryGlobalTensorMap O F G H a S'
        (F.restrictₛₗ k.op x ⊗ₜ G.restrictₛₗ k.op y) =
      H.restrictₛₗ k.op (uncurryGlobalTensorMap O F G H a S (x ⊗ₜ y)) := by
  have hα := restrMorphism_nat O G H ((a.app (op S)).hom x) (𝟙 S) k y
  rw [Category.comp_id] at hα
  have hr := homRestr_section O G H k ((a.app (op S)).hom x) (𝟙 S')
    (G.restrictₛₗ k.op y)
  rw [Category.id_comp] at hr
  rw [uncurryGlobalTensorMap_tmul, uncurryGlobalTensorMap_tmul,
    hom_restrictₛₗ_internalHom]
  exact hr.trans hα

/-- Global uncurrying, inverse to `curryGlobal`. -/
noncomputable def uncurryGlobal (a : F ⟶ internalHom O G H) : F ⊗ G ⟶ H :=
  _root_.PresheafOfModules.Hom.mk
    (fun X ↦ ofGlobalTensorHom O F G H X (uncurryGlobalTensorMap O F G H a X.unop))
    (fun {X Y} f ↦ by
      refine globalTensor_hom_ext O F G ?_
      intro x y
      exact uncurryGlobalTensorMap_restrict O F G H a f.unop x y)

/-- Global uncurrying undoes global currying. -/
theorem uncurryGlobal_curryGlobal (b : F ⊗ G ⟶ H) :
    uncurryGlobal O F G H (curryGlobal O F G H b) = b := by
  apply _root_.PresheafOfModules.hom_ext
  intro X
  refine globalTensor_hom_ext O F G ?_
  intro x y
  show uncurryGlobalTensorMap O F G H (curryGlobal O F G H b) X.unop (x ⊗ₜ y) =
    globalTensorHom O F G H b X.unop (x ⊗ₜ y)
  rw [uncurryGlobalTensorMap_tmul]
  show sectionOfRestr O H X.unop (𝟙 X.unop)
      (((curryGlobalMap O F G H b X.unop x).app (op (Over.mk (𝟙 X.unop)))).hom
        (restrSection O G X.unop (𝟙 X.unop) y)) = _
  rw [curryGlobalMap_apply, op_id, restrictₛₗ_id]

/-- Currying an uncurried morphism recovers its values on sections. -/
theorem curryGlobalMap_uncurryGlobal (a : F ⟶ internalHom O G H) (S : C) (x : F.obj (op S))
    {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    sectionOfRestr O H S q
        (((curryGlobalMap O F G H (uncurryGlobal O F G H a) S x).app
          (op (Over.mk q))).hom (restrSection O G S q y)) =
      sectionOfRestr O H S q
        ((((a.app (op S)).hom x).app (op (Over.mk q))).hom (restrSection O G S q y)) := by
  have hr := homRestr_section O G H q ((a.app (op S)).hom x) (𝟙 T) y
  rw [Category.id_comp] at hr
  rw [curryGlobalMap_apply]
  show uncurryGlobalTensorMap O F G H a T (F.restrictₛₗ q.op x ⊗ₜ y) = _
  rw [uncurryGlobalTensorMap_tmul, hom_restrictₛₗ_internalHom]
  exact hr

/-- Global currying undoes global uncurrying. -/
theorem curryGlobal_uncurryGlobal (a : F ⟶ internalHom O G H) :
    curryGlobal O F G H (uncurryGlobal O F G H a) = a := by
  refine _root_.PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    _root_.PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext <| LinearMap.ext fun y ↦ ?_
  exact curryGlobalMap_uncurryGlobal O F G H a X.unop x W.unop.hom y

/-- The tensor--internal-Hom correspondence on morphisms. -/
noncomputable def presheafTensorHomEquivAux : (F ⊗ G ⟶ H) ≃ (F ⟶ internalHom O G H) where
  toFun := curryGlobal O F G H
  invFun := uncurryGlobal O F G H
  left_inv := uncurryGlobal_curryGlobal O F G H
  right_inv := curryGlobal_uncurryGlobal O F G H

/-- Uncurrying is natural in the first tensor factor. -/
theorem uncurryGlobalTensorMap_comp_left {F' : _root_.PresheafOfModules.{max u v w} (Oforget O)}
    (f : F' ⟶ F) (a : F ⟶ internalHom O G H) (W : C) (x : F'.obj (op W))
    (y : G.obj (op W)) :
    uncurryGlobalTensorMap O F' G H (f ≫ a) W (x ⊗ₜ y) =
      uncurryGlobalTensorMap O F G H a W (f.app (op W) x ⊗ₜ y) := rfl

/-- Postcomposing a global morphism applies the postcomposed map to its values. -/
theorem globalTensorHom_comp_right (b : F ⊗ G ⟶ H)
    {H' : _root_.PresheafOfModules.{max u v w} (Oforget O)} (h : H ⟶ H') (W : C)
    (x : F.obj (op W)) (y : G.obj (op W)) :
    globalTensorHom O F G H' (b ≫ h) W (x ⊗ₜ y) =
      h.app (op W) (globalTensorHom O F G H b W (x ⊗ₜ y)) := rfl

/-- Postcomposition on internal Hom, read on plain sections. -/
theorem internalHomMapRight_section (M : _root_.PresheafOfModules.{max u v w} (Oforget O))
    {N N' : _root_.PresheafOfModules.{max u v w} (Oforget O)} (hh : N ⟶ N') (U : C)
    (α : (restrFun O U).obj M ⟶ (restrFun O U).obj N) {T : C} (q : T ⟶ U)
    (w : M.obj (op T)) :
    sectionOfRestr O N' U q
        (((((internalHomMapRight O M hh).app (op U)).hom α).app (op (Over.mk q))).hom
          (restrSection O M U q w)) =
      hh.app (op T) (sectionOfRestr O N U q
        ((α.app (op (Over.mk q))).hom (restrSection O M U q w))) := rfl

section Adjunction

/-- **Stacks 03EO.** Tensoring on the right by `G` is left adjoint to the internal-Hom functor
with source `G`. Packaging the canonical correspondence as an adjunction records its
naturality in both remaining variables. -/
@[stacks 03EO "presheaf_tensor_hom_adjunction"]
noncomputable def presheafTensorHomAdjunction :
    (tensoringRight (_root_.PresheafOfModules.{max u v w} (Oforget O))).obj G ⊣
      internalHomSecondFunctor.{v, u, max u v w, u} O G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F' H' ↦ presheafTensorHomEquivAux O F' G H'
      homEquiv_naturality_left_symm := by
        intro F₁ F₂ H₁ f a
        apply _root_.PresheafOfModules.hom_ext
        intro X
        refine globalTensor_hom_ext O F₁ G ?_
        intro x y
        exact uncurryGlobalTensorMap_comp_left O F₂ G H₁ f a X.unop x y
      homEquiv_naturality_right := by
        intro F₁ H₁ H₂ b h
        apply _root_.PresheafOfModules.hom_ext
        intro X
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply _root_.PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro y
        have hl := curryGlobalMap_apply O F₁ G H₂ (b ≫ h) X.unop x W.unop.hom y
        have hr := curryGlobalMap_apply O F₁ G H₁ b X.unop x W.unop.hom y
        have hc : globalTensorHom O F₁ G H₂ (b ≫ h) W.unop.left
              (F₁.restrictₛₗ W.unop.hom.op x ⊗ₜ y) =
            h.app (op W.unop.left) (globalTensorHom O F₁ G H₁ b W.unop.left
              (F₁.restrictₛₗ W.unop.hom.op x ⊗ₜ y)) :=
          globalTensorHom_comp_right O F₁ G H₁ b h W.unop.left _ y
        refine hl.trans (hc.trans (Eq.trans ?_
          (internalHomMapRight_section O G h X.unop
            (curryGlobalMap O F₁ G H₁ b X.unop x) W.unop.hom y).symm))
        exact congrArg (h.app (op W.unop.left)) hr.symm }

end Adjunction

/-- The canonical tensor--internal-Hom equivalence on morphisms supplied by
`presheafTensorHomAdjunction`. -/
noncomputable def presheafTensorHomEquiv : (F ⊗ G ⟶ H) ≃ (F ⟶ internalHom O G H) :=
  (presheafTensorHomAdjunction O G).homEquiv F H

/-- **Stacks 03EO.** The hom-equivalence of `presheafTensorHomAdjunction` is the canonical
currying map: on sections it sends `b` to the map taking `x` and `y` to `b (x ⊗ y)`. -/
@[stacks 03EO "presheaf_tensor_hom_adjunction"]
theorem presheafTensorHomEquiv_apply (b : F ⊗ G ⟶ H) (U : C) (x : F.obj (op U))
    {T : C} (q : T ⟶ U) (y : G.obj (op T)) :
    sectionOfRestr O H U q
        (((((presheafTensorHomEquiv O F G H b).app (op U)).hom x).app
          (op (Over.mk q))).hom (restrSection O G U q y)) =
      globalTensorHom O F G H b T (F.restrictₛₗ q.op x ⊗ₜ y) := by
  have h : presheafTensorHomEquiv O F G H b = curryGlobal O F G H b := rfl
  rw [h]
  exact curryGlobalMap_apply O F G H b U x q y

end Stacks.PresheafOfModules.InternalHom

end
