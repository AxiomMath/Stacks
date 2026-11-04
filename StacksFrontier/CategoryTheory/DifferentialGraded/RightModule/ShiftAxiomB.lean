module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.ShiftFunctorStrict
public import StacksFrontier.CategoryTheory.DifferentialGraded.Triangulated

/-!
# Axiom (B) for the differential graded category of right differential graded modules

Let `C` be a differential graded category over a commutative ring `R`. This file assembles
axiom (B) of Tag 09P6 — `DGCategory.ShiftAxiomB` — for the differential graded category
`Mod^dg(C)` of right differential graded `C`-modules: the shift functors on `Mod^dg(C)`, the
induced shifts on its category of complexes and on its homotopy category, and the
identification of the degree-`(k + n)` morphisms `M ⟶ N` with the degree-`k` morphisms
`M ⟶ N⟦n⟧`.

That identification is the obvious one: a homogeneous morphism `M ⟶ N` of degree `k + n`
takes a degree-`i` element to a degree-`(i + k + n)` element, which is a degree-`(i + k)`
element of `N⟦n⟧`. No sign is introduced; the signs of axiom (B) all come from the shift of
*morphisms*, which carries the Koszul sign `(-1)^{np}` on a morphism of degree `p`, and from
the sign `(-1)^n` on the differential of `N⟦n⟧`.

## Main definitions

* `DGCategory.RightModule.toShiftEquiv`: the `R`-linear identification
  `Hom(M, N)^{k + n} ≃ Hom(M, N⟦n⟧)^k`.
* `DGCategory.rightModuleShiftAxiomB`: axiom (B) for `Mod^dg(C)`.

## Main results

* `DGCategory.RightModule.toShiftHom_homD`,
  `DGCategory.RightModule.toShiftHom_homComp_right` and
  `DGCategory.RightModule.toShiftHom_homComp_left`: the three compatibilities of that
  identification with the differential and with composition on either side.
* `DGCategory.strictHasShift`: a shift on an ordinary category assembled from strict
  equalities of functors.

## Implementation notes

The shift on `Comp(Mod^dg(C))` and on `K(Mod^dg(C))` is built from `eqToIso` applied to the
*equalities* of functors proved in
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.ShiftFunctorStrict`, so that the
clauses `DGCategory.ShiftAxiomB.compShift_functor` and `DGCategory.ShiftAxiomB.kShift_functor`
hold by reflexivity.

The inverse of `DGCategory.RightModule.toShiftEquiv` evaluates a morphism at the *canonical*
target degree `i + k` and then transports along `i + k + n = j`, rather than evaluating at
`j - n`; this keeps the single transport at the outside, where
`DGCategory.RightModule.objCast_app` and `DGCategory.RightModule.act_objCast` absorb it.
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe w v u r

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

namespace RightModule

/-! ### Transports absorbed by a homogeneous morphism -/

/-- A value transported to a prescribed target degree is the value there. -/
theorem objCast_app' {M N : RightModule.{w} C} {p : ℤ} (φ : HomogeneousMap M N p) {x : C.Obj}
    {i j j' : ℤ} (h : i + p = j) (hj : j = j') (h' : i + p = j') (a : M.obj x i) :
    N.objCast x hj (app φ h a) = app φ h' a := by
  subst h; subst hj; rfl

/-! ### Moving a degree into the shift of the target -/

variable {M N P : RightModule.{w} C}

/-- The underlying graded map of the identification `Hom(M, N)^{k + n} ≃ Hom(M, N⟦n⟧)^k`: the
morphism itself, read in the shifted target. -/
def toShiftFun (n : ℤ) {k : ℤ} (φ : HomogeneousMap M N (k + n)) :
    GradedMap M (shift N n) k := fun T =>
  φ.1 ⟨T.x, T.i, T.j + n, by have := T.hij; omega⟩

/-- On a degree-`i` element, `toShiftFun n φ` with target degree `j` is the value of `φ` at
target degree `j + n`. -/
theorem toShiftFun_apply (n : ℤ) {k : ℤ} (φ : HomogeneousMap M N (k + n)) (x : C.Obj)
    (i j : ℤ) (e : i + k = j) (a : M.obj x i) :
    toShiftFun n φ ⟨x, i, j, e⟩ a = app φ (show i + (k + n) = j + n by omega) a :=
  rfl

/-- A degree-`(k + n)` homogeneous morphism `M ⟶ N`, read as a degree-`k` homogeneous morphism
`M ⟶ N⟦n⟧`. -/
def toShiftHom (n : ℤ) {k : ℤ} (φ : HomogeneousMap M N (k + n)) :
    HomogeneousMap M (shift N n) k := by
  refine ⟨toShiftFun n φ, ?_⟩
  intro x y i j q c l hij hik hjl hkl a f
  rw [toShiftFun_apply, toShiftFun_apply, shift_act]
  exact app_act φ (show i + (k + n) = j + n by omega) hik
    (show j + n + q = l + n by omega) (show c + (k + n) = l + n by omega) a f

/-- The value of `toShiftHom n φ` at target degree `j` is the value of `φ` at target degree
`j + n`. -/
@[simp] theorem app_toShiftHom (n : ℤ) {k : ℤ} (φ : HomogeneousMap M N (k + n)) {x : C.Obj}
    {i j : ℤ} (e : i + k = j) (a : M.obj x i) :
    app (toShiftHom n φ) e a = app φ (show i + (k + n) = j + n by omega) a :=
  rfl

/-- The underlying graded map of the inverse identification. -/
def ofShiftFun (n : ℤ) {k : ℤ} (ψ : HomogeneousMap M (shift N n) k) :
    GradedMap M N (k + n) := fun T =>
  (N.objCast T.x (show T.i + k + n = T.j by have := T.hij; omega)).comp
    (ψ.1 ⟨T.x, T.i, T.i + k, rfl⟩)

/-- On a degree-`i` element, `ofShiftFun n ψ` is the value of `ψ` at target degree `i + k`,
transported to target degree `j = i + k + n`. -/
theorem ofShiftFun_apply (n : ℤ) {k : ℤ} (ψ : HomogeneousMap M (shift N n) k) (x : C.Obj)
    (i j : ℤ) (e : i + (k + n) = j) (a : M.obj x i) :
    ofShiftFun n ψ ⟨x, i, j, e⟩ a =
      N.objCast x (show i + k + n = j by omega) (app ψ (rfl : i + k = i + k) a) :=
  rfl

/-- A degree-`k` homogeneous morphism `M ⟶ N⟦n⟧`, read as a degree-`(k + n)` homogeneous
morphism `M ⟶ N`. -/
def ofShiftHom (n : ℤ) {k : ℤ} (ψ : HomogeneousMap M (shift N n) k) :
    HomogeneousMap M N (k + n) := by
  refine ⟨ofShiftFun n ψ, ?_⟩
  intro x y i j q c l hij hik hjl hkl a f
  rw [ofShiftFun_apply, ofShiftFun_apply,
    app_act ψ (rfl : i + k = i + k) hik (show i + k + q = c + k by omega)
      (rfl : c + k = c + k) a f, shift_act,
    N.act_objCast (show i + k + n = j by omega) (show c + k + n = l by omega)
      (show i + k + n + q = c + k + n by omega) hjl (app ψ (rfl : i + k = i + k) a) f]

/-- The value of `ofShiftHom n ψ` at target degree `j` is the value of `ψ` at target degree
`i + k`, transported along `i + k + n = j`. -/
@[simp] theorem app_ofShiftHom (n : ℤ) {k : ℤ} (ψ : HomogeneousMap M (shift N n) k)
    {x : C.Obj} {i j : ℤ} (e : i + (k + n) = j) (a : M.obj x i) :
    app (ofShiftHom n ψ) e a =
      N.objCast x (show i + k + n = j by omega) (app ψ (rfl : i + k = i + k) a) :=
  rfl

/-- The `R`-linear identification of the degree-`(k + n)` morphisms `M ⟶ N` with the degree-`k`
morphisms `M ⟶ N⟦n⟧`. -/
def toShiftEquiv (n : ℤ) (M N : RightModule.{w} C) (k : ℤ) :
    HomogeneousMap M N (k + n) ≃ₗ[R] HomogeneousMap M (shift N n) k where
  toFun := toShiftHom n
  map_add' φ ψ := by ext x i j e a; rfl
  map_smul' c φ := by ext x i j e a; rfl
  invFun := ofShiftHom n
  left_inv φ := by
    ext x i j e a
    rw [app_ofShiftHom, app_toShiftHom,
      objCast_app' φ (show i + (k + n) = i + k + n by omega)
        (show i + k + n = j by omega) e a]
  right_inv ψ := by
    ext x i j e a
    rw [app_toShiftHom, app_ofShiftHom,
      ← shift_objCast N n x (show i + k = j by omega) (app ψ (rfl : i + k = i + k) a),
      objCast_app]

/-! ### Compatibility with the differential and with composition -/

/-- The value of a morphism whose degree has been transported along an equality. -/
theorem app_dPrime {p q : ℤ} (e : p + 1 = q) (φ : HomogeneousMap M N p) {x : C.Obj}
    {i j : ℤ} (h : i + q = j) (a : M.obj x i) :
    app ((rightModuleCategory.{w} C).d' e φ) h a =
      app (homD φ) (show i + (p + 1) = j by omega) a := by
  subst e; rfl

/-- The identification turns the differential of `Mod^dg(C)` into `(-1)^n` times the
differential: the sign is the one carried by the differential of `N⟦n⟧`. -/
theorem toShiftHom_homD (n : ℤ) (M N : RightModule.{w} C) (k : ℤ)
    (φ : HomogeneousMap M N (k + n)) :
    toShiftHom n
        ((rightModuleCategory.{w} C).d' (show (k + n) + 1 = (k + 1) + n by omega) φ) =
      (-1 : R) ^ n.natAbs • homD (toShiftHom n φ) := by
  have hkn : (-1 : R) ^ (k + n).natAbs = (-1 : R) ^ n.natAbs * (-1 : R) ^ k.natAbs := by
    rw [add_comm k n]; exact neg_one_pow_natAbs_add n k
  ext x i j e a
  rw [app_toShiftHom, app_dPrime, app_homD, smul_app, app_homD]
  simp only [app_toShiftHom, shift_d]
  rw [d_app φ (show i + (k + n) = i + k + n by omega)
      (show i + k + n + 1 = j + n by omega) (show i + (k + n) + 1 = j + n by omega),
    hkn, smul_sub, smul_smul, smul_smul, neg_one_pow_natAbs_mul_self n, one_smul]

/-- The identification is compatible with composition on the right. -/
theorem toShiftHom_homComp_right (n : ℤ) {M N P : RightModule.{w} C} {l m : ℤ}
    (ψ : HomogeneousMap N P (m + n)) (φ : HomogeneousMap M N l) :
    toShiftHom n (homComp (show (m + n) + l = (m + l) + n by omega) ψ φ) =
      homComp (show m + l = m + l by omega) (toShiftHom n ψ) φ := by
  ext x i j e a
  rw [app_toShiftHom, app_homComp, app_homComp, app_toShiftHom]

/-- The identification is compatible with composition on the left, up to the Koszul sign
`(-1)^{nm}` carried by the shift of the degree-`m` morphism. -/
theorem toShiftHom_homComp_left (n : ℤ) {M N P : RightModule.{w} C} {l m : ℤ}
    (ψ : HomogeneousMap N P m) (φ : HomogeneousMap M N (l + n)) :
    toShiftHom n (homComp (show m + (l + n) = (m + l) + n by omega) ψ φ) =
      (-1 : R) ^ (n * m).natAbs •
        homComp (show m + l = m + l by omega) (shiftMap ψ n) (toShiftHom n φ) := by
  ext x i j e a
  rw [app_toShiftHom, app_homComp, smul_app, app_homComp, app_shiftMap, app_toShiftHom,
    smul_smul, neg_one_pow_natAbs_mul_self (n * m), one_smul,
    app_app ψ φ (show i + (l + n) = i + l + n by omega)
      (show i + l + n + m = j + n by omega) (show i + (l + n) + m = j + n by omega)]

end RightModule

/-! ### Axiom (B) -/

/-- A shift on an ordinary category built from strict equalities of functors; the shift
functors are then the given ones by reflexivity. -/
@[instance_reducible]
def strictHasShift (D : Type*) [Category D] (F : ℤ → D ⥤ D) (h0 : F 0 = 𝟭 D)
    (ha : ∀ n m, F (n + m) = F n ⋙ F m) : HasShift D ℤ :=
  hasShiftMk D ℤ
    { F := F
      zero := eqToIso h0
      add := fun n m => eqToIso (ha n m)
      assoc_hom_app := by
        intro n m k X
        simp only [eqToIso.hom, eqToHom_app, eqToHom_map, eqToHom_trans]
      zero_add_hom_app := by
        intro n X
        simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_map, eqToHom_trans]
      add_zero_hom_app := by
        intro n X
        simp only [eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_trans] }

/-- **Axiom (B) for `Mod^dg(C)`.** The shift functors of the differential graded category of
right differential graded `C`-modules, the induced shifts on its category of complexes and on
its homotopy category, and the identification of `Hom(M, N)^{k + n}` with
`Hom(M, N⟦n⟧)^k`. -/
def rightModuleShiftAxiomB (C : DGCategory.{v, u} R) :
    ShiftAxiomB (rightModuleCategory.{w} C) where
  shiftFunctor n := rightModuleShiftFunctor.{w} C n
  compShift := strictHasShift _ (fun n => (rightModuleShiftFunctor.{w} C n).onComp)
    (rightModuleShift_onComp_zero C) (rightModuleShift_onComp_add C)
  kShift := strictHasShift _ (fun n => (rightModuleShiftFunctor.{w} C n).onK)
    (rightModuleShift_onK_zero C) (rightModuleShift_onK_add C)
  compShift_functor _ := rfl
  kShift_functor _ := rfl
  zero_obj M := RightModule.shift_zero M
  add_obj n m M := RightModule.shift_add M n m
  zero_map := by
    intro M N k φ
    exact RightModule.shiftMap_zero φ
  add_map := by
    intro n m M N k φ
    exact RightModule.shiftMap_add φ n m
  toShift n M N k := RightModule.toShiftEquiv n M N k
  toShift_d := by
    intro n M N k φ
    exact RightModule.toShiftHom_homD n M N k φ
  toShift_comp_right := by
    intro n M N P l m ψ φ
    exact RightModule.toShiftHom_homComp_right n ψ φ
  toShift_comp_left := by
    intro n M N P l m ψ φ
    exact RightModule.toShiftHom_homComp_left n ψ φ

end DGCategory
