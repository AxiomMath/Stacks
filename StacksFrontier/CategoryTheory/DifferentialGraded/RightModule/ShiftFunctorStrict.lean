module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.ShiftReassoc

/-!
# The shift of right differential graded modules is strictly coherent

`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.ShiftReassoc` proves that the shift
of a right differential graded module is strictly coherent on objects: `M⟦0⟧ = M` and
`M⟦n + m⟧ = (M⟦m⟧)⟦n⟧`. This file carries those equalities up to morphisms and to the induced
ordinary functors.

On a homogeneous morphism `φ` of degree `p` the shift by `n` multiplies by the Koszul sign
`(-1)^{np}`; since that sign is `1` at `n = 0` and multiplicative in `n`, the shift of morphisms
is strictly coherent as well, and the two comparisons are heterogeneous equalities over the two
comparisons of objects. The induced functors on the category of complexes and on the homotopy
category of `Mod^dg(C)` are then *equal* to the identity and to the composite respectively,
which is what lets the shift on those two ordinary categories be built from `eqToIso` rather
than from a genuine coherence datum.

## Main definitions

None; this file only proves lemmas.

## Main results

* `DGCategory.RightModule.shiftMap_zero` and `DGCategory.RightModule.shiftMap_add`: the shift of
  a homogeneous morphism is strictly coherent.
* `DGCategory.rightModuleShift_onComp_zero`, `DGCategory.rightModuleShift_onComp_add`,
  `DGCategory.rightModuleShift_onK_zero` and `DGCategory.rightModuleShift_onK_add`: the induced
  functors on `Comp(Mod^dg(C))` and on `K(Mod^dg(C))` are the identity and the composite.

## Implementation notes

The comparison of two homogeneous morphisms living over two different pairs of modules is
`DGCategory.RightModule.homogeneousMap_heq`, which substitutes the two equalities of modules and
then reduces to the ordinary extensionality `DGCategory.RightModule.hom_ext`. This is possible
only because the comparisons of objects are genuine equalities; were they mere isomorphisms the
shift on `Comp` and on `K` would have to be assembled from a `CategoryTheory.ShiftMkCore` with
non-trivial coherence, and `DGCategory.ShiftAxiomB`, which demands equalities, could not be
produced at all.
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe w v u r

variable {R : Type r} [CommRing R]

/-! ### Heterogeneous comparison of cocycles and homotopy classes -/

/-- Cocycles over equal pairs of objects agree as soon as their underlying morphisms do. -/
theorem cocycle_heq (A : DGCategory.{v, u} R) {x x' y y' : A.Obj} (hx : x = x') (hy : y = y')
    {f : A.Cocycle x y} {g : A.Cocycle x' y'} (h : HEq f.1 g.1) : HEq f g := by
  subst hx; subst hy
  exact heq_of_eq (Subtype.ext (eq_of_heq h))

/-- Homotopy classes over equal pairs of objects agree as soon as their representatives do. -/
theorem homotopyClass_heq (A : DGCategory.{v, u} R) {x x' y y' : A.Obj} (hx : x = x')
    (hy : y = y') {f : A.Cocycle x y} {g : A.Cocycle x' y'} (h : HEq f.1 g.1) :
    HEq (Quotient.mk (A.homotopySetoid x y) f) (Quotient.mk (A.homotopySetoid x' y') g) := by
  subst hx; subst hy
  exact heq_of_eq (congrArg (Quotient.mk _) (Subtype.ext (eq_of_heq h)))

namespace RightModule

variable {C : DGCategory.{v, u} R}

/-! ### Heterogeneous comparison of homogeneous morphisms -/

/-- The values of a homogeneous morphism at equal source and target degrees agree. -/
theorem app_heq {M N : RightModule.{w} C} {p : ℤ} (φ : HomogeneousMap M N p) {x : C.Obj}
    {i i' j j' : ℤ} (hi : i = i') (hj : j = j') {h : i + p = j} {h' : i' + p = j'}
    {a : M.obj x i} {a' : M.obj x i'} (ha : HEq a a') :
    HEq (app φ h a) (app φ h' a') := by
  subst hi; subst hj
  obtain rfl := eq_of_heq ha
  rfl

/-- Two homogeneous morphisms over equal pairs of modules agree as soon as their values do. -/
theorem homogeneousMap_heq {M₁ M₂ N₁ N₂ : RightModule.{w} C} {p : ℤ} (hM : M₁ = M₂)
    (hN : N₁ = N₂) {φ : HomogeneousMap M₁ N₁ p} {ψ : HomogeneousMap M₂ N₂ p}
    (h : ∀ (x : C.Obj) (i j : ℤ) (e : i + p = j) (a : M₁.obj x i) (b : M₂.obj x i),
      HEq a b → HEq (app φ e a) (app ψ e b)) : HEq φ ψ := by
  subst hM; subst hN
  exact heq_of_eq (hom_ext fun x i j e a => eq_of_heq (h x i j e a a HEq.rfl))

/-! ### The strict coherences of the shift of a homogeneous morphism -/

variable {M N : RightModule.{w} C} {p : ℤ}

/-- The shift of a homogeneous morphism by `0` is the morphism itself. -/
theorem shiftMap_zero (φ : HomogeneousMap M N p) : HEq (shiftMap φ 0) φ := by
  refine homogeneousMap_heq (shift_zero M) (shift_zero N) ?_
  intro x i j e a b hab
  change HEq ((-1 : R) ^ ((0 : ℤ) * p).natAbs •
    app φ (show i + 0 + p = j + 0 by omega) a) (app φ e b)
  rw [zero_mul, Int.natAbs_zero, pow_zero, one_smul]
  exact app_heq φ (add_zero i) (add_zero j) hab

/-- The shift of a homogeneous morphism by a sum is the composite of the two shifts: the Koszul
signs multiply exactly as the two shifts of the modules compose. -/
theorem shiftMap_add (φ : HomogeneousMap M N p) (n m : ℤ) :
    HEq (shiftMap φ (n + m)) (shiftMap (shiftMap φ m) n) := by
  have hs : (-1 : R) ^ ((n + m) * p).natAbs
      = (-1 : R) ^ (n * p).natAbs * (-1 : R) ^ (m * p).natAbs := by
    rw [add_mul]; exact neg_one_pow_natAbs_add _ _
  refine homogeneousMap_heq (shift_add M n m) (shift_add N n m) ?_
  intro x i j e a b hab
  change HEq ((-1 : R) ^ ((n + m) * p).natAbs •
      app φ (show i + (n + m) + p = j + (n + m) by omega) a)
    ((-1 : R) ^ (n * p).natAbs • ((-1 : R) ^ (m * p).natAbs •
      app φ (show i + n + m + p = j + n + m by omega) b))
  rw [hs, ← smul_smul]
  exact smul_heq N (show j + (n + m) = j + n + m by omega) _
    (smul_heq N (show j + (n + m) = j + n + m by omega) _
      (app_heq φ (show i + (n + m) = i + n + m by omega)
        (show j + (n + m) = j + n + m by omega) hab))

/-- `shiftMap_add` with the two shifts composed in the order used by the induced functors. -/
private theorem shiftMap_add_comm (φ : HomogeneousMap M N p) (n m : ℤ) :
    HEq (shiftMap φ (n + m)) (shiftMap (shiftMap φ n) m) := by
  rw [add_comm n m]
  exact shiftMap_add φ m n

end RightModule

/-! ### The induced functors on the category of complexes and the homotopy category -/

variable (C : DGCategory.{v, u} R)

/-- The composite of the two shifts of objects, in the order the composition of the induced
ordinary functors uses it. -/
theorem rightModuleShift_obj_add (n m : ℤ) (M : RightModule.{w} C) :
    RightModule.shift M (n + m) = RightModule.shift (RightModule.shift M n) m := by
  rw [add_comm n m]
  exact RightModule.shift_add M m n

/-- The shift by `0` induces the identity on the category of complexes. -/
theorem rightModuleShift_onComp_zero :
    (rightModuleShiftFunctor.{w} C 0).onComp = 𝟭 (rightModuleCategory.{w} C).Comp := by
  refine CategoryTheory.Functor.hext (fun M => RightModule.shift_zero M) ?_
  intro M N f
  exact cocycle_heq _ (RightModule.shift_zero M) (RightModule.shift_zero N)
    (RightModule.shiftMap_zero f.1)

/-- The shift by a sum induces the composite on the category of complexes. -/
theorem rightModuleShift_onComp_add (n m : ℤ) :
    (rightModuleShiftFunctor.{w} C (n + m)).onComp =
      (rightModuleShiftFunctor.{w} C n).onComp ⋙ (rightModuleShiftFunctor.{w} C m).onComp := by
  refine CategoryTheory.Functor.hext (fun M => rightModuleShift_obj_add C n m M) ?_
  intro M N f
  refine cocycle_heq _ (rightModuleShift_obj_add C n m M) (rightModuleShift_obj_add C n m N) ?_
  exact RightModule.shiftMap_add_comm f.1 n m

/-- The shift by `0` induces the identity on the homotopy category. -/
theorem rightModuleShift_onK_zero :
    (rightModuleShiftFunctor.{w} C 0).onK = 𝟭 (rightModuleCategory.{w} C).K := by
  refine CategoryTheory.Functor.hext (fun M => RightModule.shift_zero M) ?_
  intro M N f
  refine Quotient.inductionOn f (fun f => ?_)
  exact homotopyClass_heq _ (RightModule.shift_zero M) (RightModule.shift_zero N)
    (RightModule.shiftMap_zero f.1)

/-- The shift by a sum induces the composite on the homotopy category. -/
theorem rightModuleShift_onK_add (n m : ℤ) :
    (rightModuleShiftFunctor.{w} C (n + m)).onK =
      (rightModuleShiftFunctor.{w} C n).onK ⋙ (rightModuleShiftFunctor.{w} C m).onK := by
  refine CategoryTheory.Functor.hext (fun M => rightModuleShift_obj_add C n m M) ?_
  intro M N f
  refine Quotient.inductionOn f (fun f => ?_)
  refine homotopyClass_heq _ (rightModuleShift_obj_add C n m M)
    (rightModuleShift_obj_add C n m N) ?_
  exact RightModule.shiftMap_add_comm f.1 n m

end DGCategory
