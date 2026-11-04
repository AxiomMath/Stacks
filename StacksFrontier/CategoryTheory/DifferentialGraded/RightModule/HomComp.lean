module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Hom

/-!
# Composition of homogeneous morphisms of right differential graded modules

Homogeneous morphisms of right differential graded `C`-modules compose, degreewise and without
a sign, and the identity of a module is the homogeneous morphism of degree zero that transports
an element along the equality `i + 0 = j` of degrees. This file proves the identities that make
these data a differential graded category: bilinearity, the graded Leibniz rule for
`DGCategory.RightModule.homD`, associativity, unitality, and the closedness of the identity.

## Main definitions

* `DGCategory.RightModule.homComp`: the composition of homogeneous morphisms.
* `DGCategory.RightModule.homId`: the identity homogeneous morphism, of degree zero.

## Main results

* `DGCategory.RightModule.homComp_add_left`, `DGCategory.RightModule.homComp_add_right`,
  `DGCategory.RightModule.homComp_smul_left` and
  `DGCategory.RightModule.homComp_smul_right`: composition is `R`-bilinear.
* `DGCategory.RightModule.homD_homComp`: the graded Leibniz rule.
* `DGCategory.RightModule.homComp_assoc`, `DGCategory.RightModule.homId_homComp`,
  `DGCategory.RightModule.homComp_homId` and `DGCategory.RightModule.homD_homId`.

## Implementation notes

Composition evaluates the inner morphism at its canonical target degree and the outer one at the
prescribed degree, so that no transport appears in the definition. Every proof below therefore
begins by moving a value at a prescribed degree back to the canonical one, with
`DGCategory.RightModule.app_app`, `DGCategory.RightModule.app_d`,
`DGCategory.RightModule.d_app` or `DGCategory.RightModule.objCast_app`; each of these is proved
by substituting the degree equation, after which the two sides are the same term.
-/

@[expose] public section

namespace DGCategory.RightModule

universe w v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}
variable {M N P Q : RightModule.{w} C} {m n p : ℤ}

/-! ### Further normalisations at a prescribed degree -/

/-- A differential at a prescribed degree, inside a value, is the canonical differential. -/
theorem app_d (φ : HomogeneousMap M N p) {x : C.Obj} {i i' j : ℤ} (hi : i + 1 = i')
    (h : i' + p = j) (h' : i + 1 + p = j) (a : M.obj x i) :
    app φ h (M.d hi a) = app φ h' (M.d rfl a) := by subst hi; rfl

/-- A value at a prescribed degree, inside a value, is the value at the canonical degree. -/
theorem app_app (ψ : HomogeneousMap N P m) (φ : HomogeneousMap M N n) {x : C.Obj}
    {i j l : ℤ} (hij : i + n = j) (h : j + m = l) (h' : i + n + m = l) (a : M.obj x i) :
    app ψ h (app φ hij a) = app ψ h' (app φ rfl a) := by subst hij; rfl

/-- A value at the canonical degree, transported to a prescribed one, is the value there. -/
@[simp] theorem objCast_app (φ : HomogeneousMap M N p) {x : C.Obj} {i j : ℤ} (h : i + p = j)
    (a : M.obj x i) : N.objCast x h (app φ rfl a) = app φ h a := by subst h; rfl

/-! ### Composition -/

/-- The underlying graded map of the composition of two homogeneous morphisms. -/
def homCompFun (h : m + n = p) (ψ : HomogeneousMap N P m) (φ : HomogeneousMap M N n) :
    GradedMap M P p := fun T =>
  (ψ.1 ⟨T.x, T.i + n, T.j, by have := T.hij; omega⟩).comp (φ.1 ⟨T.x, T.i, T.i + n, rfl⟩)

/-- The underlying graded map of `homComp h ψ φ` evaluates `φ` at the canonical degree and `ψ` at
the prescribed one. -/
theorem homCompFun_apply (h : m + n = p) (ψ : HomogeneousMap N P m)
    (φ : HomogeneousMap M N n) (x : C.Obj) (i j : ℤ) (e : i + p = j) (a : M.obj x i) :
    homCompFun h ψ φ ⟨x, i, j, e⟩ a =
      app ψ (show i + n + m = j by omega) (app φ rfl a) :=
  rfl

/-- The composition of a degree-`m` and a degree-`n` homogeneous morphism, of the prescribed
degree `p = m + n`. -/
def homComp (h : m + n = p) (ψ : HomogeneousMap N P m) (φ : HomogeneousMap M N n) :
    HomogeneousMap M P p := by
  refine ⟨homCompFun h ψ φ, ?_⟩
  intro x y i j n' k l hij hik hjl hkl a f
  rw [homCompFun_apply, homCompFun_apply,
    app_act φ rfl hik (show i + n + n' = k + n by omega) rfl a f,
    app_act ψ rfl (show i + n + n' = k + n by omega)
      (show i + n + m + n' = l by omega) (show k + n + m = l by omega) _ f,
    act_app ψ (show i + n + m = j by omega) hjl (show i + n + m + n' = l by omega)]

/-- The value of `homComp h ψ φ` at a prescribed degree is the value of `ψ` at the value of `φ` at
its canonical degree. -/
@[simp] theorem app_homComp (h : m + n = p) (ψ : HomogeneousMap N P m)
    (φ : HomogeneousMap M N n) {x : C.Obj} {i j : ℤ} (e : i + p = j) (a : M.obj x i) :
    app (homComp h ψ φ) e a = app ψ (show i + n + m = j by omega) (app φ rfl a) :=
  rfl

/-! ### The identity -/

/-- The underlying graded map of the identity homogeneous morphism. -/
def homIdFun (M : RightModule.{w} C) : GradedMap M M 0 := fun T =>
  M.objCast T.x (show T.i = T.j by have := T.hij; omega)

/-- The underlying graded map of `homId M` transports an element along the equality of degrees. -/
theorem homIdFun_apply (M : RightModule.{w} C) (x : C.Obj) (i j : ℤ) (e : i + 0 = j)
    (a : M.obj x i) : homIdFun M ⟨x, i, j, e⟩ a = M.objCast x (show i = j by omega) a :=
  rfl

/-- The identity homogeneous morphism of a right differential graded module, of degree zero. -/
def homId (M : RightModule.{w} C) : HomogeneousMap M M 0 := by
  refine ⟨homIdFun M, ?_⟩
  intro x y i j n k l hij hik hjl hkl a f
  rw [homIdFun_apply, homIdFun_apply]
  exact (M.act_objCast (show i = j by omega) (show k = l by omega) hik hjl a f).symm

/-- At a prescribed degree, `homId M` transports an element along the equality of degrees. -/
@[simp] theorem app_homId (M : RightModule.{w} C) {x : C.Obj} {i j : ℤ} (e : i + 0 = j)
    (a : M.obj x i) : app (homId M) e a = M.objCast x (show i = j by omega) a :=
  rfl

/-! ### Bilinearity of composition -/

/-- Composition is additive in the outer morphism. -/
theorem homComp_add_left (h : m + n = p) (ψ₁ ψ₂ : HomogeneousMap N P m)
    (φ : HomogeneousMap M N n) :
    homComp h (ψ₁ + ψ₂) φ = homComp h ψ₁ φ + homComp h ψ₂ φ := by
  ext x i j e a
  simp

/-- Composition is additive in the inner morphism. -/
theorem homComp_add_right (h : m + n = p) (ψ : HomogeneousMap N P m)
    (φ₁ φ₂ : HomogeneousMap M N n) :
    homComp h ψ (φ₁ + φ₂) = homComp h ψ φ₁ + homComp h ψ φ₂ := by
  ext x i j e a
  simp

/-- Composition commutes with scalar multiplication of the outer morphism. -/
theorem homComp_smul_left (h : m + n = p) (c : R) (ψ : HomogeneousMap N P m)
    (φ : HomogeneousMap M N n) : homComp h (c • ψ) φ = c • homComp h ψ φ := by
  ext x i j e a
  simp

/-- Composition commutes with scalar multiplication of the inner morphism. -/
theorem homComp_smul_right (h : m + n = p) (c : R) (ψ : HomogeneousMap N P m)
    (φ : HomogeneousMap M N n) : homComp h ψ (c • φ) = c • homComp h ψ φ := by
  ext x i j e a
  simp

/-! ### The graded Leibniz rule -/

/-- The differential of a composite obeys the graded Leibniz rule. -/
theorem homD_homComp (h : m + n = p) (ψ : HomogeneousMap N P m) (φ : HomogeneousMap M N n) :
    homD (homComp h ψ φ) =
      homComp (show m + 1 + n = p + 1 by omega) (homD ψ) φ +
        (-1 : R) ^ m.natAbs • homComp (show m + (n + 1) = p + 1 by omega) ψ (homD φ) := by
  ext x i j e a
  rw [app_homD, app_homComp, app_homComp, add_app, smul_app, app_homComp, app_homComp,
    app_homD, app_homD, app_sub, app_smul,
    d_app ψ (show i + n + m = i + p by omega) (show i + p + 1 = j by omega)
      (show i + n + m + 1 = j by omega),
    app_d ψ (show i + n + 1 = i + (n + 1) by omega) (show i + (n + 1) + m = j by omega)
      (show i + n + 1 + m = j by omega),
    app_app ψ φ (show i + 1 + n = i + (n + 1) by omega) (show i + (n + 1) + m = j by omega)
      (show i + 1 + n + m = j by omega)]
  have hk : (-1 : R) ^ p.natAbs = (-1 : R) ^ m.natAbs * (-1 : R) ^ n.natAbs := by
    rw [← h]; exact neg_one_pow_natAbs_add m n
  rw [hk]
  module

/-! ### Associativity and unitality -/

/-- Composition of homogeneous morphisms is associative. -/
theorem homComp_assoc {l q s : ℤ} (h₁ : m + n = p) (h₂ : l + p = s) (h₃ : l + m = q)
    (h₄ : q + n = s) (χ : HomogeneousMap P Q l) (ψ : HomogeneousMap N P m)
    (φ : HomogeneousMap M N n) :
    homComp h₂ χ (homComp h₁ ψ φ) = homComp h₄ (homComp h₃ χ ψ) φ := by
  ext x i j e a
  rw [app_homComp, app_homComp, app_homComp, app_homComp,
    app_app χ ψ (show i + n + m = i + p by omega) (show i + p + l = j by omega)
      (show i + n + m + l = j by omega)]

/-- The identity is a left unit for composition. -/
@[simp] theorem homId_homComp (φ : HomogeneousMap M N n) :
    homComp (zero_add n) (homId N) φ = φ := by
  ext x i j e a
  rw [app_homComp, app_homId, objCast_app]

/-- The identity is a right unit for composition. -/
@[simp] theorem homComp_homId (φ : HomogeneousMap M N n) :
    homComp (add_zero n) φ (homId M) = φ := by
  ext x i j e a
  rw [app_homComp, app_homId,
    app_objCast φ (show i = i + 0 by omega) (show i + 0 + n = j by omega) e]

/-- The identity is closed. -/
@[simp] theorem homD_homId (M : RightModule.{w} C) : homD (homId M) = 0 := by
  ext x i j e a
  rw [app_homD, app_homId, app_homId, zero_app,
    M.d_objCast (show i = i + 0 by omega) (show i + 0 + 1 = j by omega)
      (show i + 1 = j by omega),
    M.objCast_d (show i + 1 = j by omega)]
  simp

end DGCategory.RightModule
