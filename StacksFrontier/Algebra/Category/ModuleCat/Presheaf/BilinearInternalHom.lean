module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Algebras
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnitULift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

/-!
# Bilinear maps and morphisms into the internal Hom presheaf

Let `O` be a presheaf of commutative rings on a category `C` and let `K`, `G`, `H` be presheaves
of `O`-modules.  An `O`-bilinear map `K × G → H`, given on sections, is the same thing as a
morphism of presheaves of modules `K ⟶ Hom_O(G, H)` into the internal Hom presheaf of
Stacks 03EM: a bilinear map `b` is sent to the morphism whose value at a section `x` of `K` over
`U` is the morphism `G|_U ⟶ H|_U` given over `V → U` by `y ↦ b(x|_V, y)`, and a morphism `a` is
sent to the bilinear map `(x, y) ↦ a(x)(y)` read at the identity of the slice.

This is the presheaf half of Stacks 03EO in its bilinear form.  Its point is that the universes
are independent: the internal Hom of two presheaves of modules with sections in `m` on a
category with objects in `Type u` and morphisms in `Type v` has sections in `max u v m`, and the
statement here only asks `K` to live in that universe; nothing ties the module universe `m` to
the universes of `C`, as the monoidal-category version
`Stacks.PresheafOfModules.InternalHom.presheafTensorHomAdjunction` must.

## Main definitions

* `Stacks.PresheafOfModules.curryBilinear`: the morphism `K ⟶ Hom_O(G, H)` of a bilinear map.
* `Stacks.PresheafOfModules.uncurryBilinear`: the bilinear map of a morphism `K ⟶ Hom_O(G, H)`.
* `Stacks.PresheafOfModules.bilinearEquivHomInternalHom`: the two are inverse.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u w m

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {K : _root_.PresheafOfModules.{max u v m} (Oforget O)}
  {G H : _root_.PresheafOfModules.{m} (Oforget O)}

/-- A linear map of the sections over the object underlying `V`, read as a morphism of the
sections of the restrictions to the slice site.  The two module structures agree, the
restriction to the slice being a restriction of scalars along an identity. -/
def ofRestrLinearMap {M N : _root_.PresheafOfModules.{m} (Oforget O)} (U : C) (V : (Over U)ᵒᵖ)
    (f : M.obj (op V.unop.left) →ₗ[O.obj (op V.unop.left)] N.obj (op V.unop.left)) :
    ((restrFun O U).obj M).obj V ⟶ ((restrFun O U).obj N).obj V :=
  letI : Module ((ORestr O U).obj V) (((restrFun O U).obj M).obj V) :=
    (((restrFun O U).obj M).obj V).isModule
  letI : Module ((ORestr O U).obj V) (((restrFun O U).obj N).obj V) :=
    (((restrFun O U).obj N).obj V).isModule
  letI : AddCommGroup (((restrFun O U).obj M).obj V) :=
    (((restrFun O U).obj M).obj V).isAddCommGroup
  letI : AddCommGroup (((restrFun O U).obj N).obj V) :=
    (((restrFun O U).obj N).obj V).isAddCommGroup
  ConcreteCategory.ofHom (C := ModuleCat ((ORestr O U).obj V)) f

/-- The morphism `ofRestrLinearMap U V f` acts on sections as `f`. -/
theorem ofRestrLinearMap_apply {M N : _root_.PresheafOfModules.{m} (Oforget O)} (U : C)
    (V : (Over U)ᵒᵖ)
    (f : M.obj (op V.unop.left) →ₗ[O.obj (op V.unop.left)] N.obj (op V.unop.left))
    (y : M.obj (op V.unop.left)) : (ofRestrLinearMap U V f).hom y = f y := rfl

/-- The morphism `G|_U ⟶ H|_U` attached by a bilinear map `b` to a section `x` of `K` over `U`:
over `V → U` it is `y ↦ b(x|_V, y)`. -/
def curryBilinearSection (b : BilinearMap K G H) (U : C) (x : K.obj (op U)) :
    (restrFun O U).obj G ⟶ (restrFun O U).obj H where
  app V := ofRestrLinearMap U V
    { toFun := fun y => b.app (op V.unop.left) (K.map V.unop.hom.op x) y
      map_add' := fun y y' => map_add _ y y'
      map_smul' := fun r y => b.map_smul_right _ r _ y }
  naturality {V V'} g := by
    ext y
    have hK : K.map g.unop.left.op (K.map V.unop.hom.op x) = K.map V'.unop.hom.op x := by
      rw [← K.map_comp_apply, ← op_comp, Over.w g.unop]
    exact (congrArg (fun z => b.app (op V'.unop.left) z (G.map g.unop.left.op y)) hK).symm.trans
      (b.naturality g.unop.left.op _ y).symm

/-- Over `V → U`, the morphism `curryBilinearSection b U x` sends `y` to `b(x|_V, y)`. -/
theorem curryBilinearSection_app_apply (b : BilinearMap K G H) (U : C) (x : K.obj (op U))
    (V : (Over U)ᵒᵖ) (y : G.obj (op V.unop.left)) :
    ((curryBilinearSection b U x).app V).hom y = b.app (op V.unop.left) (K.map V.unop.hom.op x) y :=
  rfl

/-- A bilinear map is additive in its first argument after restriction along `f : V ⟶ U`:
`b((x + x')|_V, y) = b(x|_V, y) + b(x'|_V, y)`. -/
theorem curryBilinear_add_left (b : BilinearMap K G H) {U V : C} (f : V ⟶ U)
    (x x' : K.obj (op U)) (y : G.obj (op V)) :
    b.app (op V) (K.map f.op (x + x')) y =
      b.app (op V) (K.map f.op x) y + b.app (op V) (K.map f.op x') y :=
  (congrArg (fun z => b.app (op V) z y) (map_add (K.map f.op).hom x x')).trans
    (DFunLike.congr_fun (map_add (b.app (op V)) _ _) y)

/-- For `r` in `O(U)` and `f : V ⟶ U`, `b((r • x)|_V, y) = r|_V • b(x|_V, y)`. -/
theorem curryBilinear_smul_left (b : BilinearMap K G H) {U V : C} (f : V ⟶ U)
    (r : (Oforget O).obj (op U)) (x : K.obj (op U)) (y : G.obj (op V)) :
    b.app (op V) (K.map f.op (r • x)) y =
      ((Oforget O).map f.op).hom r • b.app (op V) (K.map f.op x) y :=
  (congrArg (fun z => b.app (op V) z y) (K.map_smul f.op r x)).trans
    (b.map_smul_left (op V) _ _ y)

/-- The morphisms `G|_U ⟶ H|_U` attached to the sections of `K` over `U` depend `O(U)`-linearly
on the section. -/
def curryBilinearLinear (b : BilinearMap K G H) (U : C) :
    K.obj (op U) →ₗ[(Oforget O).obj (op U)] internalHomObj O G H U where
  toFun := curryBilinearSection b U
  map_add' x x' := by
    refine _root_.PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    exact curryBilinear_add_left b V.unop.hom x x' y
  map_smul' r x := by
    refine _root_.PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    exact curryBilinear_smul_left b V.unop.hom r x y

/-- **Currying a bilinear map.**  The morphism `K ⟶ Hom_O(G, H)` sending a section `x` of `K`
over `U` to the morphism `G|_U ⟶ H|_U` given over `V → U` by `y ↦ b(x|_V, y)`. -/
def curryBilinear (b : BilinearMap K G H) : K ⟶ internalHom O G H where
  app X := ConcreteCategory.ofHom (C := ModuleCat ((Oforget O).obj X))
    (curryBilinearLinear b X.unop)
  naturality {X Y} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine _root_.PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
    change b.app (op V.unop.left) (K.map V.unop.hom.op (K.map f x)) y =
      b.app (op V.unop.left) (K.map (V.unop.hom ≫ f.unop).op x) y
    rw [op_comp, Quiver.Hom.op_unop, K.map_comp_apply]

/-- The value of a morphism `G|_U ⟶ H|_U` over an object `p : W ⟶ U` of the slice, as a map of
plain sections. -/
def evalOver {U : C} (α : (restrFun O U).obj G ⟶ (restrFun O U).obj H) {W : C} (p : W ⟶ U)
    (y : G.obj (op W)) : H.obj (op W) :=
  (α.app (op (Over.mk p))).hom y

/-- `evalOver α p y` depends only on the morphism `p`, so equal morphisms give equal values. -/
theorem evalOver_congr {U : C} (α : (restrFun O U).obj G ⟶ (restrFun O U).obj H) {W : C}
    {p q : W ⟶ U} (h : p = q) (y : G.obj (op W)) : evalOver α p y = evalOver α q y := by
  subst h
  rfl

/-- A morphism of presheaves of modules on the slice commutes with restriction along a
morphism `k` of the slice from `Over.mk (k ≫ p)` to `Over.mk p`. -/
theorem evalOver_restrict {U : C} (α : (restrFun O U).obj G ⟶ (restrFun O U).obj H) {W W' : C}
    (p : W ⟶ U) (k : W' ⟶ W) (y : G.obj (op W)) :
    evalOver α (k ≫ p) (G.map k.op y) = H.map k.op (evalOver α p y) :=
  congrArg (fun φ => φ.hom y) (α.naturality (Over.homMk k : Over.mk (k ≫ p) ⟶ Over.mk p).op)

/-- The restriction map of the ring presheaf `Oforget O` along the identity of `U` is the identity
on `O(U)`. -/
theorem oforget_map_id_apply (U : C) (r : (Oforget O).obj (op U)) :
    ((Oforget O).map (𝟙 U).op).hom r = r :=
  (congrArg (fun φ => RingCat.Hom.hom φ r) ((Oforget O).map_id (op U))).trans rfl

/-- **Uncurrying a morphism into the internal Hom.**  The bilinear map `(x, y) ↦ a(x)(y)`, the
value of the morphism `a(x) : G|_U ⟶ H|_U` at the identity of the slice. -/
def uncurryBilinear (a : K ⟶ internalHom O G H) : BilinearMap K G H where
  app X := AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
      (fun y => evalOver (C := C) (O := O) ((a.app X).hom x) (𝟙 X.unop) y)
      (fun y y' => map_add _ y y'))
    (fun x x' => by
      ext y
      exact congrArg (fun α => evalOver α (𝟙 X.unop) y) (map_add (a.app X).hom x x'))
  map_smul_left X r x y :=
    (congrArg (fun α => evalOver α (𝟙 X.unop) y) (map_smul (a.app X).hom r x)).trans
      (congrArg (fun s => s • evalOver ((a.app X).hom x) (𝟙 X.unop) y)
        (oforget_map_id_apply X.unop r))
  map_smul_right X r x y :=
    LinearMap.map_smul ((((a.app X).hom x).app (op (Over.mk (𝟙 X.unop)))).hom) r y
  naturality {X Y} f x y := by
    have hnat : (a.app Y).hom (K.map f x) = homRestr O G H f.unop ((a.app X).hom x) :=
      congrArg (fun φ => φ.hom x) (a.naturality f)
    refine (evalOver_restrict ((a.app X).hom x) (𝟙 X.unop) f.unop y).symm.trans ?_
    refine (evalOver_congr _ ((Category.comp_id f.unop).trans
      (Category.id_comp f.unop).symm) _).trans ?_
    exact congrArg (fun α => evalOver α (𝟙 Y.unop) (G.map f y)) hnat.symm

/-- The bilinear map `uncurryBilinear a` sends `(x, y)` to the value of `a(x)` at the identity
of the slice, applied to `y`. -/
theorem uncurryBilinear_app (a : K ⟶ internalHom O G H) (X : Cᵒᵖ) (x : K.obj X)
    (y : G.obj X) :
    (uncurryBilinear a).app X x y = evalOver ((a.app X).hom x) (𝟙 X.unop) y :=
  rfl

/-- Uncurrying the curried morphism of a bilinear map `b` recovers `b`. -/
theorem uncurryBilinear_curryBilinear (b : BilinearMap K G H) :
    uncurryBilinear (curryBilinear b) = b := by
  ext X x y
  exact congrArg (fun z => b.app X z y)
    ((congrArg (fun φ => (ConcreteCategory.hom φ) x) (K.map_id X)).trans rfl)

/-- Currying the uncurried bilinear map of a morphism `a : K ⟶ Hom_O(G, H)` recovers `a`. -/
theorem curryBilinear_uncurryBilinear (a : K ⟶ internalHom O G H) :
    curryBilinear (uncurryBilinear a) = a := by
  refine _root_.PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  refine _root_.PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  have hnat : (a.app (op V.unop.left)).hom (K.map V.unop.hom.op x) =
      homRestr O G H V.unop.hom ((a.app X).hom x) :=
    congrArg (fun φ => φ.hom x) (a.naturality V.unop.hom.op)
  refine (congrArg (fun α => evalOver α (𝟙 V.unop.left) y) hnat).trans ?_
  exact evalOver_congr ((a.app X).hom x) (Category.id_comp V.unop.hom) y

/-- **Stacks 03EO, presheaf case, bilinear form.**  Bilinear maps `K × G → H` correspond to
morphisms `K ⟶ Hom_O(G, H)` into the internal Hom presheaf, by currying. -/
def bilinearEquivHomInternalHom : BilinearMap K G H ≃ (K ⟶ internalHom O G H) where
  toFun := curryBilinear
  invFun := uncurryBilinear
  left_inv := uncurryBilinear_curryBilinear
  right_inv := curryBilinear_uncurryBilinear

end Stacks.PresheafOfModules

namespace Stacks.BilinearMap

universe t w₁ w₂ w₃

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
  {M : _root_.PresheafOfModules.{w₁} R} {N : _root_.PresheafOfModules.{w₂} R}
  {P : _root_.PresheafOfModules.{w₃} R}

/-- A bilinear map out of `M × N`, read as a bilinear map out of `ULift M × N`. -/
def ulift (b : BilinearMap M N P) :
    BilinearMap ((Stacks.SheafOfModules.presheafULift.{t} R).obj M) N P where
  app X := AddMonoidHom.mk' (fun x => b.app X x.down) (fun x x' => map_add (b.app X) x.down x'.down)
  map_smul_left X r x y := b.map_smul_left X r x.down y
  map_smul_right X r x y := b.map_smul_right X r x.down y
  naturality f x y := b.naturality f x.down y

/-- A bilinear map out of `ULift M × N`, read as a bilinear map out of `M × N`. -/
def ofULift (b : BilinearMap ((Stacks.SheafOfModules.presheafULift.{t} R).obj M) N P) :
    BilinearMap M N P where
  app X := AddMonoidHom.mk' (fun x => b.app X (ULift.up x))
    (fun x x' => map_add (b.app X) (ULift.up x) (ULift.up x'))
  map_smul_left X r x y := b.map_smul_left X r (ULift.up x) y
  map_smul_right X r x y := b.map_smul_right X r (ULift.up x) y
  naturality f x y := b.naturality f (ULift.up x) y

/-- Bilinear maps out of `M × N` and out of `ULift M × N` are the same thing. -/
def uliftEquiv : BilinearMap M N P ≃
    BilinearMap ((Stacks.SheafOfModules.presheafULift.{t} R).obj M) N P where
  toFun := ulift
  invFun := ofULift
  left_inv _ := rfl
  right_inv _ := rfl

end Stacks.BilinearMap
