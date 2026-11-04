module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomVariance
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.Tensor
import StacksCore.Tactic.StacksAttribute

/-!
# The tensor--internal-Hom adjunction for presheaves of modules, at a free ring universe

Stacks 03EO, presheaf case: for presheaves of `O`-modules `F`, `G`, `H` there is a canonical
bijection `Hom(F ⊗_O G, H) = Hom(F, Hom_O(G, H))`, natural in `F` and `H`, so tensoring on the
right by `G` is left adjoint to internal Hom out of `G`.  This file proves it **with the
universe `w` of the sections of `O` independent of the universes `u`, `v` of the site**.

`Stacks.PresheafOfModules.InternalHom.presheafTensorHomAdjunction`
(`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/TensorHomAdjunction.lean`) is the same clause
with the ring universe pinned to `max u v w`, because it is stated over Mathlib's monoidal
structure on presheaves of modules, which exists only when the module universe equals the ring
universe.  The small Zariski and small étale sites of a scheme are
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`: their structure sheaf has sections in `u`, one
universe *below* the objects of the site, and so is out of reach of that statement.  Here the
tensor product is the canonical objectwise one, `PresheafOfModules.tensorObj`, whose factor and
ring universes are independent, and the left adjoint is
`(PresheafOfModules.tensorBifunctor O).flip.obj G`.  The module universe is `max u v w`: the
internal Hom of Stacks 03EM raises a module universe `m` to `max u v m`, so only a module universe
absorbing `max u v` puts both sides of the clause in one category.

The construction is the one of the pinned clause, at the free universe: global currying is the
slice-level `currySectionMap` at the identity `𝟙 U`, and uncurrying is `TensorProduct.lift` of
evaluation at the identity of the slice.  The slice-level currying layer, `restrSection` through
`homRestr_section`, is stated at a free module universe `t`.

## Main results

* `Stacks.PresheafOfModules.InternalHom.FreeUniverse.presheafTensorHomAdjunction`: tensoring on
  the right by `G` is left adjoint to `internalHomSecondFunctor O G`, at a free ring universe.
* `Stacks.PresheafOfModules.InternalHom.FreeUniverse.presheafTensorHomEquiv_apply`: its
  hom-equivalence is the canonical currying map.

## Implementation notes

As in `StacksFrontier/Algebra/Category/ModuleCat/Presheaf/InternalHomTensorCurrying.lean`, the
sections of a restricted presheaf are the plain sections only after unfolding `restrFun`, which
instance search and `rw` do not do; `restrSection`, `sectionOfRestr`, `ofRestrHom`,
`restrTensorHom` and their global analogues retype once, at default transparency, so that every
`TensorProduct` lemma applies downstream with no friction.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory Opposite

open scoped TensorProduct

namespace Stacks.PresheafOfModules.InternalHom.FreeUniverse

universe t w v u

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-! ### Currying on sections, at an arbitrary module universe -/

section FreeModuleUniverse

/-- Restriction of a section is semilinear for the `CommRingCat`-valued structure presheaf. -/
theorem restrictₛₗ_smul (M : _root_.PresheafOfModules.{t} (Oforget O)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (r : O.obj X) (m : M.obj X) :
    M.restrictₛₗ f (r • m) = (O.map f).hom r • M.restrictₛₗ f m :=
  M.map_smul f r m

variable (M N : _root_.PresheafOfModules.{t} (Oforget O))


/-- A section of `M` over `W`, read as a section of `M|_U` over `h : W ⟶ U`. -/
noncomputable def restrSection
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (M : _root_.PresheafOfModules.{t} (Oforget O)) (U : C) {W : C} (h : W ⟶ U) (x : M.obj (op W)) :
    ((restrFun O U).obj M).obj (op (Over.mk h)) := x

/-- A section of `M|_U` over `h : W ⟶ U`, read as a section of `M` over `W`. -/
noncomputable def sectionOfRestr
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (M : _root_.PresheafOfModules.{t} (Oforget O)) (U : C) {W : C} (h : W ⟶ U)
    (x : ((restrFun O U).obj M).obj (op (Over.mk h))) : M.obj (op W) := x

/-- A linear map of plain sections, read as a map of restricted sections. -/
noncomputable def ofRestrHom (U : C) (V : (Over U)ᵒᵖ)
    (b : M.obj (op V.unop.left) →ₗ[O.obj (op V.unop.left)] N.obj (op V.unop.left)) :
    ((restrFun O U).obj M).obj V ⟶ ((restrFun O U).obj N).obj V :=
  letI : Module ((ORestr O U).obj V) (((restrFun O U).obj M).obj V) :=
    (((restrFun O U).obj M).obj V).isModule
  letI : Module ((ORestr O U).obj V) (((restrFun O U).obj N).obj V) :=
    (((restrFun O U).obj N).obj V).isModule
  letI : AddCommGroup (((restrFun O U).obj M).obj V) :=
    (((restrFun O U).obj M).obj V).isAddCommGroup
  letI : AddCommGroup (((restrFun O U).obj N).obj V) :=
    (((restrFun O U).obj N).obj V).isAddCommGroup
  ConcreteCategory.ofHom (C := ModuleCat ((ORestr O U).obj V)) b

variable (F G H : _root_.PresheafOfModules.{t} (Oforget O)) (U : C)

/-- A slice-level morphism out of a restricted tensor product, retyped at `h : W ⟶ U` as a
linear map on the honest tensor product of the plain sections over `W`. -/
noncomputable def restrTensorHom
    (a : (restrFun O U).obj (F.tensorObj G) ⟶ (restrFun O U).obj H) {W : C} (h : W ⟶ U) :
    TensorProduct (O.obj (op W)) (F.obj (op W)) (G.obj (op W)) →ₗ[O.obj (op W)]
      H.obj (op W) :=
  (a.app (op (Over.mk h))).hom

/-- A pure tensor of plain sections over `W`, as a section of `(F.tensorObj G)|_U` over
`h : W ⟶ U`. -/
noncomputable def restrTmul (U : C) {W : C} (h : W ⟶ U)
    (x : F.obj (op W)) (y : G.obj (op W)) :
    ((restrFun O U).obj (F.tensorObj G)).obj (op (Over.mk h)) :=
  x ⊗ₜ[O.obj (op W)] y

/-- Naturality of a slice-level morphism, on pure tensors of plain sections. -/
theorem restrTensorHom_nat
    (a : (restrFun O U).obj (F.tensorObj G) ⟶ (restrFun O U).obj H) {W W' : C} (h : W ⟶ U)
    (k : W' ⟶ W) (x : F.obj (op W)) (y : G.obj (op W)) :
    restrTensorHom O F G H U a (k ≫ h)
        (F.restrictₛₗ k.op x ⊗ₜ G.restrictₛₗ k.op y) =
      H.restrictₛₗ k.op (restrTensorHom O F G H U a h (x ⊗ₜ y)) :=
  congrArg (sectionOfRestr O H U (k ≫ h))
    (_root_.PresheafOfModules.naturality_apply a
      ((Over.homMk k : (Over.mk (k ≫ h) : Over U) ⟶ Over.mk h).op)
      (restrTmul O F G U h x y))

/-- The curried map at the second slice depth: over `q : T ⟶ S`, send `y` to the value of
`a` on the restriction of `x` tensored with `y`. -/
noncomputable def curryValueMap
    (a : (restrFun O U).obj (F.tensorObj G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) :
    G.obj (op T) →ₗ[O.obj (op T)] H.obj (op T) :=
  (restrTensorHom O F G H U a (q ≫ p)).comp
    (TensorProduct.mk (O.obj (op T)) (F.obj (op T)) (G.obj (op T)) (F.restrictₛₗ q.op x))

/-- Unfolding `curryValueMap`: it evaluates `a` on the restriction of `x` tensored with `y`. -/
theorem curryValueMap_apply
    (a : (restrFun O U).obj (F.tensorObj G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    curryValueMap O F G H U a p x q y =
      restrTensorHom O F G H U a (q ≫ p) (F.restrictₛₗ q.op x ⊗ₜ y) := rfl

/-- `curryValueMap` is additive in the section of `F`. -/
theorem curryValueMap_add_left
    (a : (restrFun O U).obj (F.tensorObj G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x x' : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    curryValueMap O F G H U a p (x + x') q y =
      curryValueMap O F G H U a p x q y + curryValueMap O F G H U a p x' q y := by
  rw [curryValueMap_apply, curryValueMap_apply, curryValueMap_apply, map_add,
    TensorProduct.add_tmul, map_add]

/-- `curryValueMap` is semilinear in the section of `F`. -/
theorem curryValueMap_smul_left
    (a : (restrFun O U).obj (F.tensorObj G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (r : O.obj (op S)) (x : F.obj (op S)) {T : C} (q : T ⟶ S)
    (y : G.obj (op T)) :
    curryValueMap O F G H U a p (r • x) q y =
      (O.map q.op).hom r • curryValueMap O F G H U a p x q y := by
  rw [curryValueMap_apply, curryValueMap_apply, restrictₛₗ_smul,
    ← TensorProduct.smul_tmul', map_smul]

/-- `curryValueMap` is compatible with restriction in the second slice. -/
theorem curryValueMap_restrict
    (a : (restrFun O U).obj (F.tensorObj G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T T' : C} (q : T ⟶ S) (k : T' ⟶ T)
    (y : G.obj (op T)) :
    curryValueMap O F G H U a p x (k ≫ q) (G.restrictₛₗ k.op y) =
      H.restrictₛₗ k.op (curryValueMap O F G H U a p x q y) := by
  rw [curryValueMap_apply, curryValueMap_apply, Category.assoc, op_comp,
    _root_.PresheafOfModules.restrictₛₗ_comp_apply]
  exact restrTensorHom_nat O F G H U a (q ≫ p) k (F.restrictₛₗ q.op x) y

/-- Currying of `a` at a section `x` of `F` over `p : S ⟶ U`: a morphism `G|_S ⟶ H|_S`. -/
noncomputable def currySectionValue
    (a : (restrFun O U).obj (F.tensorObj G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) :
    (restrFun O S).obj G ⟶ (restrFun O S).obj H :=
  _root_.PresheafOfModules.Hom.mk
    (fun Y ↦ ofRestrHom O G H S Y (curryValueMap O F G H U a p x Y.unop.hom))
    (fun {Y Z} f ↦ ModuleCat.hom_ext <| LinearMap.ext fun y ↦ by
      have hw : f.unop.left ≫ Y.unop.hom = Z.unop.hom := Over.w f.unop
      have h := curryValueMap_restrict O F G H U a p x Y.unop.hom f.unop.left y
      rwa [hw] at h)

/-- Currying on sections over `p : S ⟶ U`, as an `O(S)`-linear map into the internal Hom. -/
noncomputable def currySectionMap
    (a : (restrFun O U).obj (F.tensorObj G) ⟶ (restrFun O U).obj H) {S : C} (p : S ⟶ U) :
    F.obj (op S) →ₗ[O.obj (op S)] (internalHom O G H).obj (op S) where
  toFun x := currySectionValue O F G H U a p x
  map_add' x x' := _root_.PresheafOfModules.hom_ext fun Y ↦ ModuleCat.hom_ext <|
    LinearMap.ext fun y ↦ curryValueMap_add_left O F G H U a p x x' Y.unop.hom y
  map_smul' r x := _root_.PresheafOfModules.hom_ext fun Y ↦ ModuleCat.hom_ext <|
    LinearMap.ext fun y ↦ curryValueMap_smul_left O F G H U a p r x Y.unop.hom y

/-- Restricting an internal-Hom section re-indexes the slice. -/
theorem homRestr_section
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (G H : _root_.PresheafOfModules.{t} (Oforget O)) {T S : C} (k : T ⟶ S)
    (α : (restrFun O S).obj G ⟶ (restrFun O S).obj H) {W : C} (q : W ⟶ T)
    (w : G.obj (op W)) :
    sectionOfRestr O H T q
        (((homRestr O G H k α).app (op (Over.mk q))).hom (restrSection O G T q w)) =
      sectionOfRestr O H S (q ≫ k)
        ((α.app (op (Over.mk (q ≫ k)))).hom (restrSection O G S (q ≫ k) w)) := rfl

/-- Naturality of a slice-level morphism `G|_S ⟶ H|_S`, on plain sections. -/
theorem restrMorphism_nat
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (G H : _root_.PresheafOfModules.{t} (Oforget O))
    {S : C} (α : (restrFun O S).obj G ⟶ (restrFun O S).obj H)
    {T T' : C} (q : T ⟶ S) (k : T' ⟶ T) (y : G.obj (op T)) :
    sectionOfRestr O H S (k ≫ q)
        ((α.app (op (Over.mk (k ≫ q)))).hom
          (restrSection O G S (k ≫ q) (G.restrictₛₗ k.op y))) =
      H.restrictₛₗ k.op
        (sectionOfRestr O H S q ((α.app (op (Over.mk q))).hom (restrSection O G S q y))) :=
  congrArg (sectionOfRestr O H S (k ≫ q))
    (_root_.PresheafOfModules.naturality_apply α
      ((Over.homMk k : (Over.mk (k ≫ q) : Over S) ⟶ Over.mk q).op)
      (restrSection O G S q y))

/-- Applying a re-indexed internal-Hom section. -/
theorem homRestr_app_apply {T S : C} (k : T ⟶ S)
    (φ : (restrFun O S).obj M ⟶ (restrFun O S).obj N)
    (V : (Over T)ᵒᵖ) (w : ((restrFun O T).obj M).obj V) :
    ((homRestr O M N k φ).app V).hom w =
      (φ.app (op (Over.mk (V.unop.hom ≫ k)))).hom w := rfl

end FreeModuleUniverse

/-! ### The adjunction, at module universe `max u v w` -/

variable (F G H : _root_.PresheafOfModules.{max u v w} (Oforget O))


/-- Evaluating an internal-Hom section at the identity of its slice, as an `O(S)`-linear
map. -/
noncomputable def evalAtIdLinear
    (O : Cᵒᵖ ⥤ CommRingCat.{w}) (G H : _root_.PresheafOfModules.{max u v w} (Oforget O)) (S : C) :
    internalHomObj O G H S →ₗ[O.obj (op S)]
      (G.obj (op S) →ₗ[O.obj (op S)] H.obj (op S)) where
  toFun α := (α.app (op (Over.mk (𝟙 S)))).hom
  map_add' _ _ := rfl
  map_smul' r α := by
    apply LinearMap.ext
    intro y
    change (((α ≫ multEndoHom O H S r).app (op (Over.mk (𝟙 S)))).hom
      (restrSection O G S (𝟙 S) y) : H.obj (op S)) = _
    change fRestr O S r (op (Over.mk (𝟙 S))) •
      ((α.app (op (Over.mk (𝟙 S)))).hom (restrSection O G S (𝟙 S) y) : H.obj (op S)) = _
    have hr : fRestr O S r (op (Over.mk (𝟙 S))) = r := by
      change ((Oforget O).map (𝟙 (op S))).hom r = r
      rw [CategoryTheory.Functor.map_id]
      rfl
    rw [hr]
    rfl

/-- A global morphism out of a tensor product, retyped as a linear map on an honest tensor
product of plain sections. -/
noncomputable def globalTensorHom (b : F.tensorObj G ⟶ H) (W : C) :
    TensorProduct (O.obj (op W)) (F.obj (op W)) (G.obj (op W)) →ₗ[O.obj (op W)]
      H.obj (op W) :=
  (b.app (op W)).hom

/-- A pure tensor of plain sections, as a section of `F ⊗ G`. -/
noncomputable def globalTmul (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    (F.tensorObj G).obj X :=
  x ⊗ₜ[O.obj X] y

/-- A linear map of plain sections, as a morphism of the sections themselves. -/
noncomputable def ofGlobalHom
    (O : Cᵒᵖ ⥤ CommRingCat.{w}) (M N : _root_.PresheafOfModules.{max u v w} (Oforget O)) (X : Cᵒᵖ)
    (b : M.obj X →ₗ[O.obj X] N.obj X) : M.obj X ⟶ N.obj X :=
  letI : Module ((Oforget O).obj X) (M.obj X) := (M.obj X).isModule
  letI : Module ((Oforget O).obj X) (N.obj X) := (N.obj X).isModule
  letI : AddCommGroup (M.obj X) := (M.obj X).isAddCommGroup
  letI : AddCommGroup (N.obj X) := (N.obj X).isAddCommGroup
  ConcreteCategory.ofHom (C := ModuleCat ((Oforget O).obj X)) b

/-- A linear map on an honest tensor product, as a morphism out of `F ⊗ G`. -/
noncomputable def ofGlobalTensorHom (X : Cᵒᵖ)
    (b : TensorProduct (O.obj X) (F.obj X) (G.obj X) →ₗ[O.obj X] H.obj X) :
    (F.tensorObj G).obj X ⟶ H.obj X :=
  letI : Module ((Oforget O).obj X) ((F.tensorObj G).obj X) :=
    ((F.tensorObj G).obj X).isModule
  letI : Module ((Oforget O).obj X) (H.obj X) := (H.obj X).isModule
  letI : AddCommGroup ((F.tensorObj G).obj X) :=
    ((F.tensorObj G).obj X).isAddCommGroup
  letI : AddCommGroup (H.obj X) := (H.obj X).isAddCommGroup
  ConcreteCategory.ofHom (C := ModuleCat ((Oforget O).obj X)) b

/-- Two morphisms out of `F ⊗ G` agree as soon as they agree on pure tensors. -/
theorem globalTensor_hom_ext {X : Cᵒᵖ} {Z : ModuleCat ((Oforget O).obj X)}
    {φ ψ : (F.tensorObj G).obj X ⟶ Z}
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
theorem restrTensorHom_restrFun_map (b : F.tensorObj G ⟶ H) (U : C) {W : C} (h : W ⟶ U)
    (x : F.obj (op W)) (y : G.obj (op W)) :
    restrTensorHom O F G H U ((restrFun O U).map b) h (x ⊗ₜ y) =
      globalTensorHom O F G H b W (x ⊗ₜ y) := rfl

/-- Global currying, as an `O(U)`-linear map on sections. -/
noncomputable def curryGlobalMap (b : F.tensorObj G ⟶ H) (U : C) :
    F.obj (op U) →ₗ[O.obj (op U)] (internalHom O G H).obj (op U) :=
  currySectionMap O F G H U ((restrFun O U).map b) (𝟙 U)

/-- Unfolding `curryGlobalMap`: it evaluates `b` on the restriction of `x` tensored with `y`. -/
theorem curryGlobalMap_apply (b : F.tensorObj G ⟶ H) (U : C) (x : F.obj (op U))
    {T : C} (q : T ⟶ U) (y : G.obj (op T)) :
    sectionOfRestr O H U q
        (((curryGlobalMap O F G H b U x).app (op (Over.mk q))).hom
          (restrSection O G U q y)) =
      globalTensorHom O F G H b T (F.restrictₛₗ q.op x ⊗ₜ y) := by
  show curryValueMap O F G H U ((restrFun O U).map b) (𝟙 U) x q y = _
  rw [curryValueMap_apply, Category.comp_id, restrTensorHom_restrFun_map]

/-- The restriction maps of the internal Hom presheaf are the re-indexing maps `homRestr`. -/
theorem internalHom_restrictₛₗ
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (G H : _root_.PresheafOfModules.{max u v w} (Oforget O))
    {S S' : C} (k : S' ⟶ S) (α : internalHomObj O G H S) :
    (internalHom O G H).restrictₛₗ k.op α = homRestr O G H k α := rfl

/-- Global currying commutes with restriction of the base. -/
theorem curryGlobalMap_restrict (b : F.tensorObj G ⟶ H) {S S' : C} (k : S' ⟶ S)
    (x : F.obj (op S)) :
    curryGlobalMap O F G H b S' (F.restrictₛₗ k.op x) =
      homRestr O G H k (curryGlobalMap O F G H b S x) := by
  apply _root_.PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rw [homRestr_app_apply O G H k (curryGlobalMap O F G H b S x) W y]
  refine (curryGlobalMap_apply O F G H b S' (F.restrictₛₗ k.op x) W.unop.hom y).trans
    (Eq.trans ?_ (curryGlobalMap_apply O F G H b S x (W.unop.hom ≫ k) y).symm)
  rw [op_comp, _root_.PresheafOfModules.restrictₛₗ_comp_apply]

/-- Global currying: a morphism `F ⊗ G ⟶ H` becomes a morphism `F ⟶ Hom_O(G, H)`. -/
noncomputable def curryGlobal (b : F.tensorObj G ⟶ H) : F ⟶ internalHom O G H :=
  _root_.PresheafOfModules.Hom.mk
    (fun X ↦ ofGlobalHom O F (internalHom O G H) X (curryGlobalMap O F G H b X.unop))
    (fun f ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦
      curryGlobalMap_restrict O F G H b f.unop x)

/-- Applying a morphism into the internal Hom presheaf, as an `O(W)`-linear map. -/
noncomputable def globalHomApplyLinear
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (F G H : _root_.PresheafOfModules.{max u v w} (Oforget O)) (a : F ⟶ internalHom O G H) (W : C) :
    F.obj (op W) →ₗ[O.obj (op W)] internalHomObj O G H W :=
  (a.app (op W)).hom

/-- Global uncurrying as a bilinear map, by construction. -/
noncomputable def uncurryGlobalBilin
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (F G H : _root_.PresheafOfModules.{max u v w} (Oforget O)) (a : F ⟶ internalHom O G H) (W : C) :
    F.obj (op W) →ₗ[O.obj (op W)] G.obj (op W) →ₗ[O.obj (op W)] H.obj (op W) :=
  (evalAtIdLinear O G H W).comp (globalHomApplyLinear O F G H a W)

/-- Global uncurrying on the tensor product of plain sections. -/
noncomputable def uncurryGlobalTensorMap
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (F G H : _root_.PresheafOfModules.{max u v w} (Oforget O)) (a : F ⟶ internalHom O G H) (W : C) :
    TensorProduct (O.obj (op W)) (F.obj (op W)) (G.obj (op W)) →ₗ[O.obj (op W)]
      H.obj (op W) :=
  TensorProduct.lift (uncurryGlobalBilin O F G H a W)

/-- Unfolding `uncurryGlobalTensorMap` on a pure tensor: evaluate at the identity of the
slice. -/
theorem uncurryGlobalTensorMap_tmul
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (F G H : _root_.PresheafOfModules.{max u v w} (Oforget O)) (a : F ⟶ internalHom O G H) (W : C)
    (x : F.obj (op W)) (y : G.obj (op W)) :
    uncurryGlobalTensorMap O F G H a W (x ⊗ₜ y) =
      sectionOfRestr O H W (𝟙 W)
        ((((a.app (op W)).hom x).app (op (Over.mk (𝟙 W)))).hom
          (restrSection O G W (𝟙 W) y)) := rfl

/-- A morphism into the internal Hom presheaf sends restrictions to re-indexed sections. -/
private theorem app_restrictₛₗ_homRestr (a : F ⟶ internalHom O G H) {S S' : C} (k : S' ⟶ S)
    (x : F.obj (op S)) :
    (a.app (op S')).hom (F.restrictₛₗ k.op x) = homRestr O G H k ((a.app (op S)).hom x) :=
  (_root_.PresheafOfModules.naturality_apply a k.op x).trans (internalHom_restrictₛₗ O G H k _)

/-- `uncurryGlobalTensorMap` is compatible with restriction. -/
theorem uncurryGlobalTensorMap_restrict
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (F G H : _root_.PresheafOfModules.{max u v w} (Oforget O))
    (a : F ⟶ internalHom O G H) {S S' : C} (k : S' ⟶ S)
    (x : F.obj (op S)) (y : G.obj (op S)) :
    uncurryGlobalTensorMap O F G H a S'
        (F.restrictₛₗ k.op x ⊗ₜ G.restrictₛₗ k.op y) =
      H.restrictₛₗ k.op (uncurryGlobalTensorMap O F G H a S (x ⊗ₜ y)) := by
  have hα := restrMorphism_nat O G H ((a.app (op S)).hom x) (𝟙 S) k y
  rw [Category.comp_id] at hα
  have hr := homRestr_section O G H k ((a.app (op S)).hom x) (𝟙 S')
    (G.restrictₛₗ k.op y)
  rw [Category.id_comp] at hr
  rw [uncurryGlobalTensorMap_tmul, uncurryGlobalTensorMap_tmul, app_restrictₛₗ_homRestr]
  exact hr.trans hα

/-- Global uncurrying, inverse to `curryGlobal`. -/
noncomputable def uncurryGlobal (a : F ⟶ internalHom O G H) : F.tensorObj G ⟶ H :=
  _root_.PresheafOfModules.Hom.mk
    (fun X ↦ ofGlobalTensorHom O F G H X (uncurryGlobalTensorMap O F G H a X.unop))
    (fun f ↦ globalTensor_hom_ext O F G fun x y ↦
      uncurryGlobalTensorMap_restrict O F G H a f.unop x y)

/-- Global uncurrying undoes global currying. -/
theorem uncurryGlobal_curryGlobal (b : F.tensorObj G ⟶ H) :
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
  rw [curryGlobalMap_apply, op_id, _root_.PresheafOfModules.restrictₛₗ_id_apply]

/-- Currying an uncurried morphism recovers its values on sections. -/
theorem curryGlobalMap_uncurryGlobal
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (F G H : _root_.PresheafOfModules.{max u v w} (Oforget O))
    (a : F ⟶ internalHom O G H) (S : C) (x : F.obj (op S))
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
  rwa [uncurryGlobalTensorMap_tmul, app_restrictₛₗ_homRestr]

/-- Global currying undoes global uncurrying. -/
theorem curryGlobal_uncurryGlobal
    (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (F G H : _root_.PresheafOfModules.{max u v w} (Oforget O)) (a : F ⟶ internalHom O G H) :
    curryGlobal O F G H (uncurryGlobal O F G H a) = a :=
  _root_.PresheafOfModules.hom_ext fun X ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    _root_.PresheafOfModules.hom_ext fun W ↦ ModuleCat.hom_ext <| LinearMap.ext fun y ↦
      curryGlobalMap_uncurryGlobal O F G H a X.unop x W.unop.hom y

/-- The tensor--internal-Hom correspondence on morphisms. -/
noncomputable def presheafTensorHomEquivAux :
    (F.tensorObj G ⟶ H) ≃ (F ⟶ internalHom O G H) where
  toFun := curryGlobal O F G H
  invFun := uncurryGlobal O F G H
  left_inv := uncurryGlobal_curryGlobal O F G H
  right_inv := curryGlobal_uncurryGlobal O F G H

/-- Uncurrying is natural in the first tensor factor. -/
theorem uncurryGlobalTensorMap_comp_left
    (O : Cᵒᵖ ⥤ CommRingCat.{w}) (F G H : _root_.PresheafOfModules.{max u v w} (Oforget O))
    {F' : _root_.PresheafOfModules.{max u v w} (Oforget O)}
    (f : F' ⟶ F) (a : F ⟶ internalHom O G H) (W : C) (x : F'.obj (op W))
    (y : G.obj (op W)) :
    uncurryGlobalTensorMap O F' G H (f ≫ a) W (x ⊗ₜ y) =
      uncurryGlobalTensorMap O F G H a W (f.app (op W) x ⊗ₜ y) := rfl

/-- Postcomposing a global morphism applies the postcomposed map to its values. -/
theorem globalTensorHom_comp_right (b : F.tensorObj G ⟶ H)
    {H' : _root_.PresheafOfModules.{max u v w} (Oforget O)} (h : H ⟶ H') (W : C)
    (x : F.obj (op W)) (y : G.obj (op W)) :
    globalTensorHom O F G H' (b ≫ h) W (x ⊗ₜ y) =
      h.app (op W) (globalTensorHom O F G H b W (x ⊗ₜ y)) := rfl

/-- Postcomposition on internal Hom, read on plain sections. -/
theorem internalHomMapRight_section
    (O : Cᵒᵖ ⥤ CommRingCat.{w}) (M : _root_.PresheafOfModules.{max u v w} (Oforget O))
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
@[stacks 03EO "presheaf_tensor_hom_adjunction, with the universe of the sections of the \
structure presheaf independent of the universes of the site"]
noncomputable def presheafTensorHomAdjunction :
    (_root_.PresheafOfModules.tensorBifunctor O).flip.obj G ⊣
      internalHomSecondFunctor.{v, u, w, w} O G :=
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
noncomputable def presheafTensorHomEquiv :
    (F.tensorObj G ⟶ H) ≃ (F ⟶ internalHom O G H) :=
  (presheafTensorHomAdjunction O G).homEquiv F H

/-- **Stacks 03EO.** The hom-equivalence of `presheafTensorHomAdjunction` is the canonical
currying map: on sections it sends `b` to the map taking `x` and `y` to `b (x ⊗ y)`. -/
@[stacks 03EO "presheaf_tensor_hom_adjunction, with the universe of the sections of the \
structure presheaf independent of the universes of the site"]
theorem presheafTensorHomEquiv_apply (b : F.tensorObj G ⟶ H) (U : C) (x : F.obj (op U))
    {T : C} (q : T ⟶ U) (y : G.obj (op T)) :
    sectionOfRestr O H U q
        (((((presheafTensorHomEquiv O F G H b).app (op U)).hom x).app
          (op (Over.mk q))).hom (restrSection O G U q y)) =
      globalTensorHom O F G H b T (F.restrictₛₗ q.op x ⊗ₜ y) := by
  have h : presheafTensorHomEquiv O F G H b = curryGlobal O F G H b := rfl
  rw [h]
  exact curryGlobalMap_apply O F G H b U x q y

end Stacks.PresheafOfModules.InternalHom.FreeUniverse

end
