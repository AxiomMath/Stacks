module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DGCategory

/-!
# The representable right differential graded modules

Let `C` be a differential graded category over a commutative ring `R` and let `X` be an object
of `C`. The homogeneous morphisms into `X` form a right differential graded `C`-module
`h_X = C(-, X)`: the degree-`i` part at an object `y` is `C.Hom y X i`, the differential is the
differential of the Hom modules of `C`, and the right action of a homogeneous morphism is
composition. The module axioms are the axioms of `C` verbatim — associativity of the action is
`DGCategory.assoc`, the graded Leibniz rule is `DGCategory.leibniz` — which is the point of
defining a right module by its action rather than as a functor on the opposite differential
graded category, where a Koszul sign would intervene.

Postcomposition makes `X ↦ h_X` a functor of differential graded categories from `C` to the
differential graded category `Mod^dg(C)` of right differential graded `C`-modules. The induced
ordinary functors on the category of complexes and on the homotopy category are then
`DGCategory.DGFunctor.onComp` and `DGCategory.DGFunctor.onK` of Tag 09L8 applied to it.

## Main definitions

* `DGCategory.yonedaRightModule`: the representable right differential graded module
  `h_X = C(-, X)`.
* `DGCategory.yonedaPostcomp`: postcomposition with a homogeneous morphism, as a homogeneous
  morphism `h_X ⟶ h_Y` of the same degree.
* `DGCategory.yonedaDGFunctor`: the functor of differential graded categories
  `X ↦ h_X`, from `C` to `Mod^dg(C)`.

## Main results

* `DGCategory.yonedaRightModule_obj`, `DGCategory.yonedaRightModule_d` and
  `DGCategory.yonedaRightModule_act`: the module is `C.Hom - X`, with the differential and the
  composition of `C`.
* `DGCategory.app_yonedaPostcomp`: postcomposition is composition.
* `DGCategory.yonedaDGFunctor_obj` and `DGCategory.yonedaDGFunctor_map`.

## Implementation notes

Because the degrees of the action and of the differential of a right module are prescribed
parameters, the fields of `DGCategory.yonedaRightModule` that involve the differential are
discharged by substituting the degree equation and then applying the corresponding axiom of
`C`; the fields that involve only the action are the axioms of `C` with no adjustment at all.

The one place where a transport is unavoidable is the compatibility of postcomposition with the
differential, where the graded Leibniz rule of `C` produces a composite in the degree
`(i + m) + 1` while the statement prescribes a degree `j` with `i + (m + 1) = j`. The private
lemma `DGCategory.objCast_comp` moves a composite between two such degrees, and is proved by
substituting both equations.
-/

@[expose] public section

namespace DGCategory

universe v u r

variable {R : Type r} [CommRing R] (C : DGCategory.{v, u} R)

/-! ### The representable module -/

/-- The representable right differential graded module `h_X = C(-, X)`: at an object `y` its
degree-`i` part is the degree-`i` morphisms `y ⟶ X`, the differential is that of `C`, and a
homogeneous morphism `f : z ⟶ y` acts by precomposition `a ↦ a ∘ f`. -/
@[implicit_reducible]
def yonedaRightModule (X : C.Obj) : RightModule.{v} C where
  obj y i := C.Hom y X i
  addCommGroup y i := C.addCommGroup y X i
  module y i := C.module y X i
  d h a := C.d' h a
  d_add h a b := by subst h; exact C.d_add a b
  d_smul h c a := by subst h; exact C.d_smul c a
  d_d h₁ h₂ a := by subst h₁; subst h₂; exact C.d_d a
  act h a f := C.comp h a f
  act_add_left h a b f := C.comp_add_left h a b f
  act_add_right h a f g := C.comp_add_right h a f g
  act_smul_left h c a f := C.comp_smul_left h c a f
  act_smul_right h c a f := C.comp_smul_right h c a f
  leibniz h hl a f := by subst hl; exact C.leibniz h a f
  assoc h₁ h₂ h₃ h₄ a g f := C.assoc h₁ h₂ h₃ h₄ a g f
  act_id a := C.comp_id a

/-- The degree-`i` part of `h_X` at `y` is `C.Hom y X i`. -/
@[simp] theorem yonedaRightModule_obj (X y : C.Obj) (i : ℤ) :
    (yonedaRightModule C X).obj y i = C.Hom y X i := rfl

/-- The differential of `h_X` is the differential of the Hom modules of `C`. -/
@[simp] theorem yonedaRightModule_d (X y : C.Obj) {i j : ℤ} (h : i + 1 = j)
    (a : (yonedaRightModule C X).obj y i) : (yonedaRightModule C X).d h a = C.d' h a := rfl

/-- The right action of a homogeneous morphism on `h_X` is composition in `C`. -/
@[simp] theorem yonedaRightModule_act (X : C.Obj) {y z : C.Obj} {m n k : ℤ} (h : m + n = k)
    (a : (yonedaRightModule C X).obj z m) (f : C.Hom y z n) :
    (yonedaRightModule C X).act h a f = C.comp h a f := rfl

/-- The differential of `C` at a reflexivity proof of degrees. -/
theorem d'_rfl {x y : C.Obj} {n : ℤ} (f : C.Hom x y n) : C.d' rfl f = C.d f := rfl

/-- Two composites of the same pair of morphisms, landing in equal degrees, agree after the
transport of `DGCategory.RightModule.objCast`. -/
private theorem objCast_comp {X Y z : C.Obj} {m i k k' : ℤ} (h : m + i = k) (h' : m + i = k')
    (e : k = k') (g : C.Hom X Y m) (a : (yonedaRightModule C X).obj z i) :
    (yonedaRightModule C Y).objCast z e (C.comp h g a) = C.comp h' g a := by
  subst h; subst e; rfl

/-! ### Postcomposition -/

/-- The underlying graded map of postcomposition with a homogeneous morphism. -/
def yonedaPostcompFun {X Y : C.Obj} {m : ℤ} (f : C.Hom X Y m) :
    RightModule.GradedMap (yonedaRightModule C X) (yonedaRightModule C Y) m := fun T =>
  { toFun := fun a => C.comp (show m + T.i = T.j by have := T.hij; omega) f a
    map_add' := fun a b => C.comp_add_right _ f a b
    map_smul' := fun c a => C.comp_smul_right _ c f a }

/-- Postcomposition with a degree-`m` homogeneous morphism `f : X ⟶ Y`, as a degree-`m`
homogeneous morphism `h_X ⟶ h_Y` of right differential graded `C`-modules. Its compatibility
with the right action is associativity of composition in `C`. -/
def yonedaPostcomp {X Y : C.Obj} {m : ℤ} (f : C.Hom X Y m) :
    RightModule.HomogeneousMap (yonedaRightModule C X) (yonedaRightModule C Y) m := by
  refine ⟨yonedaPostcompFun C f, ?_⟩
  intro z w i j n k l hij hik hjl hkl a g
  exact C.assoc hik (show m + k = l by omega) (show m + i = j by omega) hjl f a g

/-- Postcomposition with `f` sends a homogeneous morphism `a` to the composite `f ∘ a`. -/
@[simp] theorem app_yonedaPostcomp {X Y : C.Obj} {m : ℤ} (f : C.Hom X Y m) {z : C.Obj}
    {i j : ℤ} (h : i + m = j) (a : (yonedaRightModule C X).obj z i) :
    RightModule.app (yonedaPostcomp C f) h a = C.comp (show m + i = j by omega) f a :=
  rfl

/-! ### The functor of differential graded categories -/

/-- The functor of differential graded categories `X ↦ h_X = C(-, X)`, from `C` to the
differential graded category of right differential graded `C`-modules. -/
def yonedaDGFunctor : DGFunctor C (rightModuleCategory.{v} C) where
  obj X := yonedaRightModule C X
  map f := yonedaPostcomp C f
  map_add {X Y m} f g := by
    refine RightModule.hom_ext fun z i j e a => ?_
    rw [app_yonedaPostcomp, RightModule.add_app, app_yonedaPostcomp, app_yonedaPostcomp,
      C.comp_add_left]
  map_smul {X Y m} c f := by
    refine RightModule.hom_ext fun z i j e a => ?_
    rw [app_yonedaPostcomp, RightModule.smul_app, app_yonedaPostcomp, C.comp_smul_left]
  map_d {X Y m} f := by
    refine RightModule.hom_ext fun z i j e a => ?_
    rw [app_yonedaPostcomp, rightModuleCategory_d, RightModule.app_homD, app_yonedaPostcomp,
      app_yonedaPostcomp,
      ← RightModule.objCast_d (yonedaRightModule C Y) (show i + m + 1 = j by omega),
      show (yonedaRightModule C Y).d rfl (C.comp (show m + i = i + m by omega) f a) =
          C.d (C.comp (show m + i = i + m by omega) f a) from rfl,
      show (yonedaRightModule C X).d (rfl : i + 1 = i + 1) a = C.d a from rfl,
      C.leibniz (show m + i = i + m by omega) f a, RightModule.objCast_add,
      RightModule.objCast_smul,
      objCast_comp C (show m + 1 + i = i + m + 1 by omega) (show m + 1 + i = j by omega)
        (show i + m + 1 = j by omega),
      objCast_comp C (show m + (i + 1) = i + m + 1 by omega) (show m + (i + 1) = j by omega)
        (show i + m + 1 = j by omega)]
    abel
  map_comp {X Y Z m n k} h g f := by
    refine RightModule.hom_ext fun w i j e a => ?_
    rw [app_yonedaPostcomp, rightModuleCategory_comp, RightModule.app_homComp,
      app_yonedaPostcomp, app_yonedaPostcomp]
    exact (C.assoc (show n + i = i + n by omega) (show m + (i + n) = j by omega) h
      (show k + i = j by omega) g f a).symm
  map_id X := by
    refine RightModule.hom_ext fun z i j e a => ?_
    rw [app_yonedaPostcomp, rightModuleCategory_id, RightModule.app_homId]
    have hid := objCast_comp C (show (0 : ℤ) + i = i by omega)
      (show (0 : ℤ) + i = j by omega) (show i = j by omega) (C.id X) a
    rw [C.id_comp] at hid
    exact hid.symm

/-- The functor `yonedaDGFunctor` sends an object `X` to `h_X = C(-, X)`. -/
@[simp] theorem yonedaDGFunctor_obj (X : C.Obj) :
    (yonedaDGFunctor C).obj X = yonedaRightModule C X := rfl

/-- The functor `yonedaDGFunctor` sends a homogeneous morphism `f` to postcomposition with `f`. -/
@[simp] theorem yonedaDGFunctor_map {X Y : C.Obj} {m : ℤ} (f : C.Hom X Y m) :
    (yonedaDGFunctor C).map f = yonedaPostcomp C f := rfl

end DGCategory
