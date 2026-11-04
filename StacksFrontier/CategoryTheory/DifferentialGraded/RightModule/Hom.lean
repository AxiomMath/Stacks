module

public import StacksFrontier.Algebra.DifferentialGraded.Sign
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Defs

/-!
# Homogeneous morphisms of right differential graded modules

Let `C` be a differential graded category over a commutative ring `R` and let `M` and `N` be
right differential graded `C`-modules. A *homogeneous morphism of degree `p`* from `M` to `N` is
a family of `R`-linear maps `M x i → N x j`, one for every object `x` and every pair of degrees
with `i + p = j`, commuting with the right action of `C`. These form an `R`-module, and the
graded commutator with the differentials of `M` and `N` is a differential on them.

## Main definitions

* `DGCategory.RightModule.GradedMap`: degree-`p` families of `R`-linear maps, with no
  compatibility imposed.
* `DGCategory.RightModule.homSubmodule` and `DGCategory.RightModule.HomogeneousMap`: the
  `R`-submodule of those commuting with the action, and its elements.
* `DGCategory.RightModule.app`: the value of a homogeneous morphism.
* `DGCategory.RightModule.homD`: the differential `d φ = d_N ∘ φ - (-1)^p φ ∘ d_M`.

## Main results

* `DGCategory.RightModule.app_act`: a homogeneous morphism commutes with the right action.
* `DGCategory.RightModule.app_homD`: the value of the differential.
* `DGCategory.RightModule.homD_add`, `DGCategory.RightModule.homD_smul` and
  `DGCategory.RightModule.homD_homD`: the differential is `R`-linear and squares to zero.

## Implementation notes

A homogeneous morphism is a subtype of a `Pi` type rather than a structure, so that the additive
group and the `R`-module structure on morphisms of a fixed degree are the ones Mathlib already
puts on `Pi` types and on a `Submodule`; this is the device
`DifferentialGradedModule.homogeneousMapSubmodule` uses in the one-object case.

The target degree of each component is a parameter constrained by a proof rather than the
canonical `i + p`, which is what makes composition and the differential free of transports. The
price is that an identity between two values at *propositionally* equal degrees is not a
reflexivity: the lemmas `DGCategory.RightModule.act_d`, `DGCategory.RightModule.act_app` and
`DGCategory.RightModule.app_objCast` are the normalisations that move such a value back to the
canonical degree, and they are all proved by substituting the degree equation.
-/

@[expose] public section

namespace DGCategory.RightModule

universe w v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-- The Koszul sign is multiplicative in the degree, in the spelling `(-1) ^ n.natAbs` used by
`DGCategory.leibniz` and `DGCategory.RightModule.leibniz`. -/
theorem neg_one_pow_natAbs_add (m n : ℤ) :
    (-1 : R) ^ (m + n).natAbs = (-1 : R) ^ m.natAbs * (-1 : R) ^ n.natAbs :=
  DifferentialGraded.gradedSign_add m n

/-! ### Normalising a value at a prescribed degree -/

variable (M : RightModule.{w} C)

/-- A differential reaching a prescribed degree, inside an action, is the canonical one. -/
theorem act_d {x y : C.Obj} {m m' n l : ℤ} (hm : m + 1 = m') (h : m' + n = l)
    (h' : m + 1 + n = l) (a : M.obj y m) (f : C.Hom x y n) :
    M.act h (M.d hm a) f = M.act h' (M.d rfl a) f := by subst hm; rfl

variable {M}

/-! ### Graded maps and homogeneous morphisms -/

/-- The index of a component of a degree-`p` graded map: an object of `C` together with a
source and a target degree differing by `p`. -/
structure Index (C : DGCategory.{v, u} R) (p : ℤ) : Type u where
  /-- The object of `C` at which the component sits. -/
  x : C.Obj
  /-- The source degree. -/
  i : ℤ
  /-- The target degree. -/
  j : ℤ
  /-- The target degree exceeds the source degree by `p`. -/
  hij : i + p = j

/-- Degree-`p` graded maps from `M` to `N`: for every object `x` and every pair of degrees with
`i + p = j`, an `R`-linear map `M x i → N x j`. No compatibility with the action is imposed. -/
abbrev GradedMap (M N : RightModule.{w} C) (p : ℤ) : Type (max u w) :=
  ∀ T : Index C p, M.obj T.x T.i →ₗ[R] N.obj T.x T.j

/-- The `R`-submodule of degree-`p` graded maps commuting with the right action of `C`. -/
def homSubmodule (M N : RightModule.{w} C) (p : ℤ) :
    Submodule R (∀ T : Index C p, M.obj T.x T.i →ₗ[R] N.obj T.x T.j) where
  carrier := {φ | ∀ (x y : C.Obj) (i j n k l : ℤ) (hij : i + p = j) (hik : i + n = k)
    (hjl : j + n = l) (hkl : k + p = l) (a : M.obj y i) (f : C.Hom x y n),
    φ ⟨x, k, l, hkl⟩ (M.act hik a f) = N.act hjl (φ ⟨y, i, j, hij⟩ a) f}
  zero_mem' := by
    intro x y i j n k l hij hik hjl hkl a f
    simp
  add_mem' := by
    intro φ ψ hφ hψ x y i j n k l hij hik hjl hkl a f
    simp only [Pi.add_apply, LinearMap.add_apply]
    rw [hφ x y i j n k l hij hik hjl hkl a f, hψ x y i j n k l hij hik hjl hkl a f,
      N.act_add_left]
  smul_mem' := by
    intro c φ hφ x y i j n k l hij hik hjl hkl a f
    simp only [Pi.smul_apply, LinearMap.smul_apply]
    rw [hφ x y i j n k l hij hik hjl hkl a f, N.act_smul_left]

/-- Degree-`p` homogeneous morphisms of right differential graded `C`-modules. -/
abbrev HomogeneousMap (M N : RightModule.{w} C) (p : ℤ) := homSubmodule M N p

variable {N P : RightModule.{w} C} {p : ℤ}

/-- The value of a homogeneous morphism of degree `p` on a degree-`i` element, in a prescribed
degree `j`. -/
def app (φ : HomogeneousMap M N p) {x : C.Obj} {i j : ℤ} (h : i + p = j) (a : M.obj x i) :
    N.obj x j := φ.1 ⟨x, i, j, h⟩ a

/-- The component of a homogeneous morphism at an index is its value at that index's degrees. -/
@[simp] theorem coe_apply (φ : HomogeneousMap M N p) (T : Index C p) (a : M.obj T.x T.i) :
    φ.1 T a = app φ T.hij a := by cases T; rfl

/-- Two homogeneous morphisms of the same degree are equal if their values agree everywhere. -/
@[ext] theorem hom_ext {φ ψ : HomogeneousMap M N p}
    (h : ∀ (x : C.Obj) (i j : ℤ) (e : i + p = j) (a : M.obj x i), app φ e a = app ψ e a) :
    φ = ψ :=
  Subtype.ext (funext fun T => LinearMap.ext fun a => by
    cases T; exact h _ _ _ _ a)

/-- The value of a homogeneous morphism is additive. -/
@[simp] theorem app_add (φ : HomogeneousMap M N p) {x : C.Obj} {i j : ℤ} (h : i + p = j)
    (a b : M.obj x i) : app φ h (a + b) = app φ h a + app φ h b := map_add _ _ _

/-- The value of a homogeneous morphism commutes with scalar multiplication. -/
@[simp] theorem app_smul (φ : HomogeneousMap M N p) {x : C.Obj} {i j : ℤ} (h : i + p = j)
    (c : R) (a : M.obj x i) : app φ h (c • a) = c • app φ h a := map_smul _ _ _

/-- A homogeneous morphism sends zero to zero. -/
@[simp] theorem app_zero (φ : HomogeneousMap M N p) {x : C.Obj} {i j : ℤ} (h : i + p = j) :
    app φ h (0 : M.obj x i) = 0 := map_zero _

/-- The value of a homogeneous morphism commutes with subtraction. -/
@[simp] theorem app_sub (φ : HomogeneousMap M N p) {x : C.Obj} {i j : ℤ} (h : i + p = j)
    (a b : M.obj x i) : app φ h (a - b) = app φ h a - app φ h b := map_sub _ _ _

/-- The zero homogeneous morphism has value zero. -/
@[simp] theorem zero_app {x : C.Obj} {i j : ℤ} (h : i + p = j) (a : M.obj x i) :
    app (0 : HomogeneousMap M N p) h a = 0 := rfl

/-- The value of a sum of homogeneous morphisms is the sum of their values. -/
@[simp] theorem add_app (φ ψ : HomogeneousMap M N p) {x : C.Obj} {i j : ℤ} (h : i + p = j)
    (a : M.obj x i) : app (φ + ψ) h a = app φ h a + app ψ h a := rfl

/-- The value of a scalar multiple of a homogeneous morphism is the scalar multiple of its
value. -/
@[simp] theorem smul_app (c : R) (φ : HomogeneousMap M N p) {x : C.Obj} {i j : ℤ}
    (h : i + p = j) (a : M.obj x i) : app (c • φ) h a = c • app φ h a := rfl

/-- The value of the negative of a homogeneous morphism is the negative of its value. -/
@[simp] theorem neg_app (φ : HomogeneousMap M N p) {x : C.Obj} {i j : ℤ} (h : i + p = j)
    (a : M.obj x i) : app (-φ) h a = -app φ h a := rfl

/-- The value of a difference of homogeneous morphisms is the difference of their values. -/
@[simp] theorem sub_app (φ ψ : HomogeneousMap M N p) {x : C.Obj} {i j : ℤ} (h : i + p = j)
    (a : M.obj x i) : app (φ - ψ) h a = app φ h a - app ψ h a := rfl

/-- A homogeneous morphism commutes with the right action of `C`. -/
theorem app_act (φ : HomogeneousMap M N p) {x y : C.Obj} {i j n k l : ℤ} (hij : i + p = j)
    (hik : i + n = k) (hjl : j + n = l) (hkl : k + p = l) (a : M.obj y i) (f : C.Hom x y n) :
    app φ hkl (M.act hik a f) = N.act hjl (app φ hij a) f :=
  φ.2 x y i j n k l hij hik hjl hkl a f

/-- A value at a prescribed degree, under the differential, is the value at the canonical
degree. -/
theorem d_app (φ : HomogeneousMap M N p) {x : C.Obj} {i j l : ℤ} (hij : i + p = j)
    (h : j + 1 = l) (h' : i + p + 1 = l) (a : M.obj x i) :
    N.d h (app φ hij a) = N.d h' (app φ rfl a) := by subst hij; rfl

/-- A value at a prescribed degree, inside an action, is the value at the canonical degree. -/
theorem act_app (φ : HomogeneousMap M N p) {x y : C.Obj} {i j n l : ℤ} (hij : i + p = j)
    (h : j + n = l) (h' : i + p + n = l) (a : M.obj y i) (f : C.Hom x y n) :
    N.act h (app φ hij a) f = N.act h' (app φ rfl a) f := by subst hij; rfl

/-- A homogeneous morphism absorbs a transport of the source degree. -/
theorem app_objCast (φ : HomogeneousMap M N p) {x : C.Obj} {i i' j : ℤ} (hi : i = i')
    (h : i' + p = j) (h' : i + p = j) (a : M.obj x i) :
    app φ h (M.objCast x hi a) = app φ h' a := by subst hi; rfl

/-! ### The differential of a homogeneous morphism -/

/-- The underlying graded map of the differential of a homogeneous morphism. -/
def homDFun (φ : HomogeneousMap M N p) : GradedMap M N (p + 1) := fun T =>
  (N.dLinear (show T.i + p + 1 = T.j by have := T.hij; omega)).comp
      (φ.1 ⟨T.x, T.i, T.i + p, rfl⟩) -
    (-1 : R) ^ p.natAbs •
      (φ.1 ⟨T.x, T.i + 1, T.j, by have := T.hij; omega⟩).comp
        (M.dLinear (rfl : T.i + 1 = T.i + 1))

/-- The component of `homDFun φ` on `a` is `d_N (φ a) - (-1)^p φ (d_M a)`. -/
theorem homDFun_apply (φ : HomogeneousMap M N p) (x : C.Obj) (i j : ℤ) (h : i + (p + 1) = j)
    (a : M.obj x i) :
    homDFun φ ⟨x, i, j, h⟩ a =
      N.d (show i + p + 1 = j by omega) (app φ rfl a) -
        (-1 : R) ^ p.natAbs • app φ (show i + 1 + p = j by omega) (M.d rfl a) :=
  rfl

/-- The differential of a homogeneous morphism of degree `p`: the graded commutator
`d_N ∘ φ - (-1)^p φ ∘ d_M`, a homogeneous morphism of degree `p + 1`. -/
def homD (φ : HomogeneousMap M N p) : HomogeneousMap M N (p + 1) := by
  refine ⟨homDFun φ, ?_⟩
  intro x y i j n k l hij hik hjl hkl a f
  rw [homDFun_apply, homDFun_apply]
  have h1 : app φ (rfl : k + p = k + p) (M.act hik a f) =
      N.act (show i + p + n = k + p by omega) (app φ (rfl : i + p = i + p) a) f :=
    app_act φ rfl hik (by omega) rfl a f
  have h2 : M.d (rfl : k + 1 = k + 1) (M.act hik a f) =
      M.act (show i + 1 + n = k + 1 by omega) (M.d rfl a) f +
        (-1 : R) ^ i.natAbs • M.act (show i + (n + 1) = k + 1 by omega) a (C.d f) :=
    M.leibniz hik rfl a f
  have h3 : app φ (show k + 1 + p = l by omega)
        (M.act (show i + 1 + n = k + 1 by omega) (M.d rfl a) f) =
      N.act (show i + 1 + p + n = l by omega) (app φ (rfl : i + 1 + p = i + 1 + p) (M.d rfl a))
        f :=
    app_act φ rfl (by omega) (by omega) (by omega) (M.d rfl a) f
  have h4 : app φ (show k + 1 + p = l by omega)
        (M.act (show i + (n + 1) = k + 1 by omega) a (C.d f)) =
      N.act (show i + p + (n + 1) = l by omega) (app φ (rfl : i + p = i + p) a) (C.d f) :=
    app_act φ rfl (by omega) (by omega) (by omega) a (C.d f)
  rw [h1, N.leibniz (show i + p + n = k + p by omega) (show k + p + 1 = l by omega), h2,
    app_add, app_smul, h3, h4, N.act_sub_left, N.act_smul_left,
    act_d N (show i + p + 1 = j by omega) hjl (show i + p + 1 + n = l by omega),
    act_app φ (show i + 1 + p = j by omega) hjl (show i + 1 + p + n = l by omega)]
  rw [show (i + p).natAbs = (i + p).natAbs from rfl]
  rw [neg_one_pow_natAbs_add (R := R) i p]
  ring_nf
  module

/-- The value of `homD φ` on `a` is `d_N (φ a) - (-1)^p φ (d_M a)`. -/
@[simp] theorem app_homD (φ : HomogeneousMap M N p) {x : C.Obj} {i j : ℤ}
    (h : i + (p + 1) = j) (a : M.obj x i) :
    app (homD φ) h a =
      N.d (show i + p + 1 = j by omega) (app φ rfl a) -
        (-1 : R) ^ p.natAbs • app φ (show i + 1 + p = j by omega) (M.d rfl a) :=
  rfl

/-- The differential of homogeneous morphisms is additive. -/
theorem homD_add (φ ψ : HomogeneousMap M N p) : homD (φ + ψ) = homD φ + homD ψ := by
  ext x i j e a
  simp only [app_homD, add_app, N.d_add, smul_add]
  abel

/-- The differential of homogeneous morphisms commutes with scalar multiplication. -/
theorem homD_smul (c : R) (φ : HomogeneousMap M N p) : homD (c • φ) = c • homD φ := by
  ext x i j e a
  simp only [app_homD, smul_app, N.d_smul, smul_sub, smul_comm c]

/-- The differential squares to zero. -/
theorem homD_homD (φ : HomogeneousMap M N p) : homD (homD φ) = 0 := by
  ext x i j e a
  rw [app_homD, app_homD, app_homD, zero_app, N.d_sub, N.d_smul,
    N.d_d (show i + p + 1 = i + (p + 1) by omega) (show i + (p + 1) + 1 = j by omega),
    d_app φ (show i + 1 + p = i + (p + 1) by omega) (show i + (p + 1) + 1 = j by omega)
      (show i + 1 + p + 1 = j by omega),
    M.d_d (rfl : i + 1 = i + 1) (rfl : i + 1 + 1 = i + 1 + 1), app_zero, smul_zero, sub_zero]
  have hs : (-1 : R) ^ (p + 1).natAbs = -((-1 : R) ^ p.natAbs) :=
    DifferentialGraded.gradedSign_succ p
  rw [hs]
  module

end DGCategory.RightModule
