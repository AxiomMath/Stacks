module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DGCategory

/-!
# Restriction of right differential graded modules along a functor

Let `F : E ⥤ C` be a functor of differential graded categories over a commutative ring `R` and
let `M` be a right differential graded `C`-module. The *restriction* `F^* M` of `M` along `F`
is the right differential graded `E`-module whose value at an object `e` is the value of `M` at
`F e`, with the differential of `M` unchanged and with a homogeneous morphism `f` of `E` acting
through its image `F f` in `C`. No structure is invented: every homogeneous part, every
differential and every action of `F^* M` is literally one of `M`, and the axioms of `F^* M` are
the axioms of `M` after rewriting `F (d f)`, `F (g ∘ f)`, `F (f + g)`, `F (c • f)` and `F 1`
with the corresponding fields of `F`.

A homogeneous morphism of right differential graded `C`-modules restricts componentwise, and
this makes restriction a functor of differential graded categories
`Mod^dg(C) ⥤ Mod^dg(E)`.

For the one-object differential graded subcategory `E = C(K, K)` of
`StacksFrontier.CategoryTheory.DifferentialGraded.EndomorphismDGCategory` this restriction is
evaluation at `K`; that case is
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Evaluation`.

## Main definitions

* `DGCategory.RightModule.restrict`: the restricted right differential graded `E`-module.
* `DGCategory.RightModule.restrictHom`: the restriction of a homogeneous morphism.
* `DGCategory.restrictDGFunctor`: restriction as a functor of differential graded categories
  `Mod^dg(C) ⥤ Mod^dg(E)`.

## Main results

* `DGCategory.RightModule.restrict_obj`, `DGCategory.RightModule.restrict_d` and
  `DGCategory.RightModule.restrict_act`: the homogeneous parts, the differential and the action
  of the restriction.
* `DGCategory.RightModule.app_restrictHom`: the value of a restricted homogeneous morphism.
* `DGCategory.restrictDGFunctor_obj` and `DGCategory.restrictDGFunctor_map`.

## Implementation notes

The degrees of a right differential graded module are prescribed parameters rather than
canonical sums, so restriction introduces no transport at all: the index `⟨e, i, j, h⟩` of a
component of a graded map over `E` becomes the index `⟨F e, i, j, h⟩` over `C` with the *same*
degree equation, and the whole of `DGCategory.restrictDGFunctor` is therefore discharged by
reflexivity.

The object universe of `E` must be that of `C` for the two categories of modules to be
differential graded categories at the same universe levels, which is what a functor of
differential graded categories between them requires; this is why
`DGCategory.endDGCategory` takes its single object in the object universe of `C`.
-/

@[expose] public section

namespace DGCategory

universe w v u r

namespace RightModule

variable {R : Type r} [CommRing R] {E C : DGCategory.{v, u} R}

/-! ### The restricted module -/

/-- The *restriction* `F^* M` of a right differential graded `C`-module `M` along a functor
`F : E ⥤ C` of differential graded categories: its value at an object `e` of `E` is the value
of `M` at `F e`, its differential is that of `M`, and a homogeneous morphism `f` of `E` acts
through `F f`. -/
@[implicit_reducible]
def restrict (F : DGFunctor E C) (M : RightModule.{w} C) : RightModule.{w} E where
  obj e i := M.obj (F.obj e) i
  addCommGroup e i := M.addCommGroup (F.obj e) i
  module e i := M.module (F.obj e) i
  d := fun {_ _ _} h a => M.d h a
  d_add := fun {_ _ _} h a b => M.d_add h a b
  d_smul := fun {_ _ _} h c a => M.d_smul h c a
  d_d := fun {_ _ _ _} h₁ h₂ a => M.d_d h₁ h₂ a
  act := fun {_ _ _ _ _} h a f => M.act h a (F.map f)
  act_add_left := fun {_ _ _ _ _} h a b f => M.act_add_left h a b (F.map f)
  act_add_right := fun {_ _ _ _ _} h a f g =>
    (congrArg (M.act h a) (F.map_add f g)).trans (M.act_add_right h a (F.map f) (F.map g))
  act_smul_left := fun {_ _ _ _ _} h c a f => M.act_smul_left h c a (F.map f)
  act_smul_right := fun {_ _ _ _ _} h c a f =>
    (congrArg (M.act h a) (F.map_smul c f)).trans (M.act_smul_right h c a (F.map f))
  leibniz := fun {_ _ _ _ _ _} h hl a f => by
    simpa only [F.map_d] using M.leibniz h hl a (F.map f)
  assoc := fun {_ _ _ _ _ _ _ _ _} h₁ h₂ h₃ h₄ a g f => by
    simpa only [F.map_comp] using M.assoc h₁ h₂ h₃ h₄ a (F.map g) (F.map f)
  act_id := fun {x _} a => by simpa only [F.map_id] using M.act_id (x := F.obj x) a

/-- The degree-`i` part of `F^* M` at `e` is the degree-`i` part of `M` at `F e`. -/
@[simp] theorem restrict_obj (F : DGFunctor E C) (M : RightModule.{w} C) (e : E.Obj) (i : ℤ) :
    (restrict F M).obj e i = M.obj (F.obj e) i := rfl

/-- The differential of `F^* M` is the differential of `M`. -/
@[simp] theorem restrict_d (F : DGFunctor E C) (M : RightModule.{w} C) {e : E.Obj} {i j : ℤ}
    (h : i + 1 = j) (a : (restrict F M).obj e i) : (restrict F M).d h a = M.d h a := rfl

/-- The action of `F^* M` is the action of `M` on the image morphism. -/
@[simp] theorem restrict_act (F : DGFunctor E C) (M : RightModule.{w} C) {e e' : E.Obj}
    {m n k : ℤ} (h : m + n = k) (a : (restrict F M).obj e' m) (f : E.Hom e e' n) :
    (restrict F M).act h a f = M.act h a (F.map f) := rfl

/-- The transport along an equality of degrees in `F^* M` is that of `M`. -/
theorem restrict_objCast (F : DGFunctor E C) (M : RightModule.{w} C) (e : E.Obj) {i j : ℤ}
    (h : i = j) (a : (restrict F M).obj e i) :
    (restrict F M).objCast e h a = M.objCast (F.obj e) h a := by subst h; rfl

/-! ### The restriction of a homogeneous morphism -/

variable {M N P : RightModule.{w} C} {p : ℤ}

/-- The underlying graded map of the restriction of a homogeneous morphism: its components at
the objects in the image of `F`. -/
def restrictHomFun (F : DGFunctor E C) (φ : HomogeneousMap M N p) :
    GradedMap (restrict F M) (restrict F N) p := fun T =>
  φ.1 ⟨F.obj T.x, T.i, T.j, T.hij⟩

/-- The restriction of a homogeneous morphism `φ : M ⟶ N` of degree `p` along a functor
`F : E ⥤ C` of differential graded categories, as a homogeneous morphism
`F^* M ⟶ F^* N` of degree `p`. Its compatibility with the action of `E` is the compatibility
of `φ` with the action of `C` on the image morphism. -/
def restrictHom (F : DGFunctor E C) (φ : HomogeneousMap M N p) :
    HomogeneousMap (restrict F M) (restrict F N) p :=
  ⟨restrictHomFun F φ, fun _ _ _ _ _ _ _ hij hik hjl hkl a f =>
    app_act φ hij hik hjl hkl a (F.map f)⟩

/-- The value of a restricted homogeneous morphism is the value of the morphism. -/
@[simp] theorem app_restrictHom (F : DGFunctor E C) (φ : HomogeneousMap M N p) {e : E.Obj}
    {i j : ℤ} (h : i + p = j) (a : (restrict F M).obj e i) :
    app (restrictHom F φ) h a = app φ h a := rfl

end RightModule

/-! ### Restriction as a functor of differential graded categories -/

variable {R : Type r} [CommRing R] {E C : DGCategory.{v, u} R}

/-- **Restriction along a functor of differential graded categories**, as a functor of
differential graded categories `Mod^dg(C) ⥤ Mod^dg(E)`: it sends a right differential graded
`C`-module `M` to its restriction `F^* M` and a homogeneous morphism to its restriction, in
the same degree and with no sign. -/
def restrictDGFunctor (F : DGFunctor E C) :
    DGFunctor (rightModuleCategory.{w} C) (rightModuleCategory.{w} E) where
  obj M := RightModule.restrict F M
  map φ := RightModule.restrictHom F φ
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_d _ := rfl
  map_comp _ _ _ := rfl
  map_id _ := rfl

/-- Restriction sends a right differential graded module to its restriction. -/
@[simp] theorem restrictDGFunctor_obj (F : DGFunctor E C) (M : RightModule.{w} C) :
    (restrictDGFunctor.{w} F).obj M = RightModule.restrict F M := rfl

/-- Restriction sends a homogeneous morphism to its restriction. -/
@[simp] theorem restrictDGFunctor_map (F : DGFunctor E C) {M N : RightModule.{w} C} {p : ℤ}
    (φ : (rightModuleCategory.{w} C).Hom M N p) :
    (restrictDGFunctor.{w} F).map φ = RightModule.restrictHom F φ := rfl

end DGCategory
