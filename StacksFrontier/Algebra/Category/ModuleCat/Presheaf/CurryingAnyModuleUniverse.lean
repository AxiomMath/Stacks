module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomTensorCurrying

/-!
# Currying on sections of presheaves of modules, in any module universe

Let `O` be a presheaf of commutative rings on a category `C : Type u` with `[Category.{v} C]`, and
let `F`, `G`, `H` be presheaves of `O`-modules with values in an arbitrary universe `w`. A morphism
`(F ⊗ G)|_U ⟶ H|_U` gives, on sections, linear maps `F(W) → (G|_W ⟶ H|_W)` compatible with
restriction; likewise for a global morphism `F ⊗ G ⟶ H`. These are the section-level currying
maps of the presheaf clause of [Stacks, Tag 03EO], with the module universe free.

## Main definitions

* `Stacks.PresheafOfModules.InternalHom.AnyUniverse.curryValueMap`,
  `Stacks.PresheafOfModules.InternalHom.AnyUniverse.currySectionMap`: slice-level currying.
* `Stacks.PresheafOfModules.InternalHom.AnyUniverse.curryGlobalMap`: global currying on sections.
* `Stacks.PresheafOfModules.InternalHom.AnyUniverse.evalAtIdLinear`: evaluation of an
  internal-Hom section at the identity of its slice.

## References

* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

namespace Stacks.PresheafOfModules.InternalHom.AnyUniverse

universe v u w

variable {C : Type u} [Category.{v} C]

section Slice

variable (O : Cᵒᵖ ⥤ CommRingCat)

/-- Iterated restriction of a section. -/
theorem restrictₛₗ_comp_apply (M : _root_.PresheafOfModules.{w} (Oforget O)) {X Y Z : Cᵒᵖ}
    (i : X ⟶ Y) (j : Y ⟶ Z) (x : M.obj X) :
    M.restrictₛₗ (i ≫ j) x = M.restrictₛₗ j (M.restrictₛₗ i x) :=
  M.map_comp_apply i j x

/-- Restriction of a section is semilinear for the `CommRingCat`-valued structure presheaf. -/
theorem restrictₛₗ_smul (M : _root_.PresheafOfModules.{w} (Oforget O)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (r : O.obj X) (m : M.obj X) :
    M.restrictₛₗ f (r • m) = (O.map f).hom r • M.restrictₛₗ f m :=
  M.map_smul f r m

/-- Restriction along an identity is the identity. -/
theorem restrictₛₗ_id (M : _root_.PresheafOfModules.{w} (Oforget O)) {X : Cᵒᵖ} (x : M.obj X) :
    M.restrictₛₗ (𝟙 X) x = x := by
  simp only [_root_.PresheafOfModules.restrictₛₗ_apply]
  exact congrFun (congrArg (fun f ↦ (ModuleCat.Hom.hom f).toFun) (M.map_id X)) x

/-- Applying a re-indexed internal-Hom section. -/
theorem homRestr_app_apply (M N : _root_.PresheafOfModules.{w} (Oforget O))
    {T S : C} (k : T ⟶ S) (φ : (restrFun O S).obj M ⟶ (restrFun O S).obj N)
    (V : (Over T)ᵒᵖ) (w : ((restrFun O T).obj M).obj V) :
    ((homRestr O M N k φ).app V).hom w =
      (φ.app (op (Over.mk (V.unop.hom ≫ k)))).hom w := rfl

section SectionUniverse

/-! ### The slice-level currying maps -/

/-- A section of `M` over `W`, read as a section of `M|_U` over `h : W ⟶ U`. -/
noncomputable def restrSection
    (M : _root_.PresheafOfModules.{w} (Oforget O)) (U : C) {W : C} (h : W ⟶ U) (x : M.obj (op W)) :
    ((restrFun O U).obj M).obj (op (Over.mk h)) := x

/-- A section of `M|_U` over `h : W ⟶ U`, read as a section of `M` over `W`. -/
noncomputable def sectionOfRestr
    (M : _root_.PresheafOfModules.{w} (Oforget O)) (U : C) {W : C} (h : W ⟶ U)
    (x : ((restrFun O U).obj M).obj (op (Over.mk h))) : M.obj (op W) := x

/-- A linear map of plain sections, read as a map of restricted sections. -/
noncomputable def ofRestrHom
    (M N : _root_.PresheafOfModules.{w} (Oforget O)) (U : C) (V : (Over U)ᵒᵖ)
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

/-- A slice-level morphism out of a restricted tensor product, retyped at `h : W ⟶ U` as a
linear map on the honest tensor product of the plain sections over `W`. -/
noncomputable def restrTensorHom
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) {W : C} (h : W ⟶ U) :
    TensorProduct (O.obj (op W)) (F.obj (op W)) (G.obj (op W)) →ₗ[O.obj (op W)]
      H.obj (op W) :=
  (a.app (op (Over.mk h))).hom

/-- A pure tensor of plain sections over `W`, as a section of `(F ⊗ G)|_U` over `h : W ⟶ U`. -/
noncomputable def restrTmul
    (F G : _root_.PresheafOfModules.{w} (Oforget O)) (U : C) {W : C} (h : W ⟶ U)
    (x : F.obj (op W)) (y : G.obj (op W)) :
    ((restrFun O U).obj (F ⊗ G)).obj (op (Over.mk h)) :=
  x ⊗ₜ[O.obj (op W)] y

/-- Naturality of a slice-level morphism, on pure tensors of plain sections. -/
theorem restrTensorHom_nat
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) {W W' : C} (h : W ⟶ U)
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
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) :
    G.obj (op T) →ₗ[O.obj (op T)] H.obj (op T) :=
  (restrTensorHom O F G H U a (q ≫ p)).comp
    (TensorProduct.mk (O.obj (op T)) (F.obj (op T)) (G.obj (op T)) (F.restrictₛₗ q.op x))

/-- Unfolding `curryValueMap`: it evaluates `a` on the restriction of `x` tensored with `y`. -/
theorem curryValueMap_apply
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    curryValueMap O F G H U a p x q y =
      restrTensorHom O F G H U a (q ≫ p) (F.restrictₛₗ q.op x ⊗ₜ y) := rfl

/-- `curryValueMap` is additive in the section of `F`. -/
theorem curryValueMap_add_left
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x x' : F.obj (op S)) {T : C} (q : T ⟶ S) (y : G.obj (op T)) :
    curryValueMap O F G H U a p (x + x') q y =
      curryValueMap O F G H U a p x q y + curryValueMap O F G H U a p x' q y := by
  rw [curryValueMap_apply, curryValueMap_apply, curryValueMap_apply, map_add,
    TensorProduct.add_tmul, map_add]

/-- `curryValueMap` is semilinear in the section of `F`. -/
theorem curryValueMap_smul_left
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (r : O.obj (op S)) (x : F.obj (op S)) {T : C} (q : T ⟶ S)
    (y : G.obj (op T)) :
    curryValueMap O F G H U a p (r • x) q y =
      (O.map q.op).hom r • curryValueMap O F G H U a p x q y := by
  rw [curryValueMap_apply, curryValueMap_apply, restrictₛₗ_smul,
    ← TensorProduct.smul_tmul', map_smul]

/-- `curryValueMap` is compatible with restriction in the second slice. -/
theorem curryValueMap_restrict
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) {T T' : C} (q : T ⟶ S) (k : T' ⟶ T)
    (y : G.obj (op T)) :
    curryValueMap O F G H U a p x (k ≫ q) (G.restrictₛₗ k.op y) =
      H.restrictₛₗ k.op (curryValueMap O F G H U a p x q y) := by
  rw [curryValueMap_apply, curryValueMap_apply, Category.assoc, op_comp,
    restrictₛₗ_comp_apply]
  exact restrTensorHom_nat O F G H U a (q ≫ p) k (F.restrictₛₗ q.op x) y

/-- Currying of `a` at a section `x` of `F` over `p : S ⟶ U`: a morphism `G|_S ⟶ H|_S`. -/
noncomputable def currySectionValue
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S : C} (p : S ⟶ U) (x : F.obj (op S)) :
    (restrFun O S).obj G ⟶ (restrFun O S).obj H :=
  _root_.PresheafOfModules.Hom.mk
    (fun Y ↦ ofRestrHom O G H S Y (curryValueMap O F G H U a p x Y.unop.hom))
    (fun {Y Z} f ↦ by
      ext y
      have h := curryValueMap_restrict O F G H U a p x Y.unop.hom f.unop.left y
      rwa [Over.w f.unop] at h)

/-- Currying on sections over `p : S ⟶ U`, as an `O(S)`-linear map into the internal Hom. -/
noncomputable def currySectionMap
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H) {S : C} (p : S ⟶ U) :
    F.obj (op S) →ₗ[O.obj (op S)] (internalHom O G H).obj (op S) where
  toFun x := currySectionValue O F G H U a p x
  map_add' x x' := by
    refine _root_.PresheafOfModules.hom_ext fun Y ↦ ?_
    ext y
    exact curryValueMap_add_left O F G H U a p x x' Y.unop.hom y
  map_smul' r x := by
    refine _root_.PresheafOfModules.hom_ext fun Y ↦ ?_
    ext y
    exact curryValueMap_smul_left O F G H U a p r x Y.unop.hom y

/-- Restricting an internal-Hom section re-indexes the slice. -/
theorem homRestr_section
    (G H : _root_.PresheafOfModules.{w} (Oforget O)) {T S : C} (k : T ⟶ S)
    (α : (restrFun O S).obj G ⟶ (restrFun O S).obj H) {W : C} (q : W ⟶ T)
    (w : G.obj (op W)) :
    sectionOfRestr O H T q
        (((homRestr O G H k α).app (op (Over.mk q))).hom (restrSection O G T q w)) =
      sectionOfRestr O H S (q ≫ k)
        ((α.app (op (Over.mk (q ≫ k)))).hom (restrSection O G S (q ≫ k) w)) := rfl

/-- Restricting the base of `curryValueMap` reindexes the slice. -/
theorem curryValueMap_base_restrict
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S S' : C} (p : S ⟶ U) (k : S' ⟶ S) (x : F.obj (op S)) {T : C} (q : T ⟶ S')
    (y : G.obj (op T)) :
    curryValueMap O F G H U a (k ≫ p) (F.restrictₛₗ k.op x) q y =
      curryValueMap O F G H U a p x (q ≫ k) y := by
  rw [curryValueMap_apply, curryValueMap_apply, Category.assoc, op_comp,
    restrictₛₗ_comp_apply]

/-- Restricting the base of `currySectionValue` is restriction of internal-Hom sections. -/
theorem currySectionValue_base_restrict
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (U : C)
    (a : (restrFun O U).obj (F ⊗ G) ⟶ (restrFun O U).obj H)
    {S S' : C} (p : S ⟶ U) (k : S' ⟶ S) (x : F.obj (op S)) :
    currySectionValue O F G H U a (k ≫ p) (F.restrictₛₗ k.op x) =
      homRestr O G H k (currySectionValue O F G H U a p x) := by
  ext W w
  exact curryValueMap_base_restrict O F G H U a p k x W.unop.hom w

/-- Evaluating an internal-Hom section at the identity of its slice, as an `O(S)`-linear
map. -/
noncomputable def evalAtIdLinear
    (G H : _root_.PresheafOfModules.{w} (Oforget O)) (S : C) :
    internalHomObj O G H S →ₗ[O.obj (op S)]
      (G.obj (op S) →ₗ[O.obj (op S)] H.obj (op S)) where
  toFun α := (α.app (op (Over.mk (𝟙 S)))).hom
  map_add' _ _ := rfl
  map_smul' r α := by
    ext y
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

/-- Naturality of a slice-level morphism `G|_S ⟶ H|_S`, on plain sections. -/
theorem restrMorphism_nat
    (G H : _root_.PresheafOfModules.{w} (Oforget O)) {S : C}
    (α : (restrFun O S).obj G ⟶ (restrFun O S).obj H)
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

end SectionUniverse

end Slice

section Global

/-! ### Global currying on sections -/

variable (O : Cᵒᵖ ⥤ CommRingCat.{w})

/-- A global morphism out of a tensor product, retyped as a linear map on an honest tensor
product of plain sections. -/
noncomputable def globalTensorHom
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (b : F ⊗ G ⟶ H) (W : C) :
    TensorProduct (O.obj (op W)) (F.obj (op W)) (G.obj (op W)) →ₗ[O.obj (op W)]
      H.obj (op W) :=
  (b.app (op W)).hom

/-- A pure tensor of plain sections, as a section of `F ⊗ G`. -/
noncomputable def globalTmul
    (F G : _root_.PresheafOfModules.{w} (Oforget O)) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    (F ⊗ G).obj X :=
  x ⊗ₜ[O.obj X] y

/-- A linear map of plain sections, as a morphism of the sections themselves. -/
noncomputable def ofGlobalHom (M N : _root_.PresheafOfModules.{w} (Oforget O)) (X : Cᵒᵖ)
    (b : M.obj X →ₗ[O.obj X] N.obj X) : M.obj X ⟶ N.obj X :=
  letI : Module ((Oforget O).obj X) (M.obj X) := (M.obj X).isModule
  letI : Module ((Oforget O).obj X) (N.obj X) := (N.obj X).isModule
  letI : AddCommGroup (M.obj X) := (M.obj X).isAddCommGroup
  letI : AddCommGroup (N.obj X) := (N.obj X).isAddCommGroup
  ConcreteCategory.ofHom (C := ModuleCat ((Oforget O).obj X)) b

/-- A linear map on an honest tensor product, as a morphism out of `F ⊗ G`. -/
noncomputable def ofGlobalTensorHom
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (X : Cᵒᵖ)
    (b : TensorProduct (O.obj X) (F.obj X) (G.obj X) →ₗ[O.obj X] H.obj X) :
    (F ⊗ G).obj X ⟶ H.obj X :=
  letI : Module ((Oforget O).obj X) ((F ⊗ G).obj X) := ((F ⊗ G).obj X).isModule
  letI : Module ((Oforget O).obj X) (H.obj X) := (H.obj X).isModule
  letI : AddCommGroup ((F ⊗ G).obj X) := ((F ⊗ G).obj X).isAddCommGroup
  letI : AddCommGroup (H.obj X) := (H.obj X).isAddCommGroup
  ConcreteCategory.ofHom (C := ModuleCat ((Oforget O).obj X)) b

/-- Two morphisms out of `F ⊗ G` agree as soon as they agree on pure tensors. -/
theorem globalTensor_hom_ext
    (F G : _root_.PresheafOfModules.{w} (Oforget O)) {X : Cᵒᵖ} {Z : ModuleCat ((Oforget O).obj X)}
    {φ ψ : (F ⊗ G).obj X ⟶ Z}
    (h : ∀ (x : F.obj X) (y : G.obj X),
      φ.hom (globalTmul O F G X x y) = ψ.hom (globalTmul O F G X x y)) : φ = ψ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add t t' ht ht' =>
      have hsum : φ.hom t + φ.hom t' = ψ.hom t + ψ.hom t' := by rw [ht, ht']
      exact (map_add φ.hom t t').trans (hsum.trans (map_add ψ.hom t t').symm)

/-- Restricting a global morphism to a slice does not change its values on pure tensors. -/
theorem restrTensorHom_restrFun_map
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (b : F ⊗ G ⟶ H) (U : C) {W : C} (h : W ⟶ U)
    (x : F.obj (op W)) (y : G.obj (op W)) :
    restrTensorHom O F G H U ((restrFun O U).map b) h (x ⊗ₜ y) =
      globalTensorHom O F G H b W (x ⊗ₜ y) := rfl

/-- Global currying, as an `O(U)`-linear map on sections. -/
noncomputable def curryGlobalMap
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (b : F ⊗ G ⟶ H) (U : C) :
    F.obj (op U) →ₗ[O.obj (op U)] (internalHom O G H).obj (op U) :=
  currySectionMap O F G H U ((restrFun O U).map b) (𝟙 U)

/-- Unfolding `curryGlobalMap`: it evaluates `b` on the restriction of `x` tensored with `y`. -/
theorem curryGlobalMap_apply
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (b : F ⊗ G ⟶ H) (U : C) (x : F.obj (op U))
    {T : C} (q : T ⟶ U)
    (y : G.obj (op T)) :
    sectionOfRestr O H U q
        (((curryGlobalMap O F G H b U x).app (op (Over.mk q))).hom
          (restrSection O G U q y)) =
      globalTensorHom O F G H b T (F.restrictₛₗ q.op x ⊗ₜ y) := by
  change curryValueMap O F G H U ((restrFun O U).map b) (𝟙 U) x q y = _
  rw [curryValueMap_apply, Category.comp_id, restrTensorHom_restrFun_map]

/-- The restriction maps of the internal Hom presheaf are the re-indexing maps `homRestr`. -/
theorem internalHom_restrictₛₗ
    (G H : _root_.PresheafOfModules.{w} (Oforget O)) {S S' : C} (k : S' ⟶ S)
    (α : internalHomObj O G H S) :
    (internalHom O G H).restrictₛₗ k.op α = homRestr O G H k α := rfl

/-- Global currying commutes with restriction of the base. -/
theorem curryGlobalMap_restrict
    (F G H : _root_.PresheafOfModules.{w} (Oforget O)) (b : F ⊗ G ⟶ H) {S S' : C} (k : S' ⟶ S)
    (x : F.obj (op S)) :
    curryGlobalMap O F G H b S' (F.restrictₛₗ k.op x) =
      homRestr O G H k (curryGlobalMap O F G H b S x) := by
  refine _root_.PresheafOfModules.hom_ext fun W ↦ ?_
  ext y
  rw [homRestr_app_apply O G H k (curryGlobalMap O F G H b S x) W y]
  refine (curryGlobalMap_apply O F G H b S' (F.restrictₛₗ k.op x) W.unop.hom y).trans
    (Eq.trans ?_ (curryGlobalMap_apply O F G H b S x (W.unop.hom ≫ k) y).symm)
  rw [op_comp, restrictₛₗ_comp_apply]

end Global

end Stacks.PresheafOfModules.InternalHom.AnyUniverse

end
