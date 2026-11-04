module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedUnitAlgebra
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRestriction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRegularModuleUniversal

/-!
# The unit `(O, 0) ⟶ A` and homotopies of `(O, 0)`-modules

Let `O` be a sheaf of commutative rings on a site and let `A` be a sheaf of differential graded
`O`-algebras. The unit `r ↦ r · 1` is a unit-preserving homomorphism `(O, 0) ⟶ A` of sheaves of
differential graded `O`-algebras, along which `A` is a differential graded
`((O, 0), A)`-bimodule. A homotopy between the underlying morphisms of complexes of two
morphisms of right differential graded `(O, 0)`-modules is a homotopy of right differential
graded `(O, 0)`-modules, since `(O, 0)` acts by scalars.

## Main definitions

* `SheafOfModules.DifferentialGradedAlgebra.unitAlgebraHom`: the unit `(O, 0) ⟶ A`.
* `SheafOfModules.DifferentialGradedModule.unitHomotopyOfHomotopy`: a homotopy of underlying
  complexes as a homotopy of right differential graded `(O, 0)`-modules.

## Main results

* `SheafOfModules.DifferentialGradedAlgebra.unitAlgebraHom_preservesOne`: the unit preserves
  the unit.

## References

* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
* [Stacks Project, Tag 0FS0](https://stacks.math.columbia.edu/tag/0FS0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}

open unitDGAlgebra

namespace DifferentialGradedAlgebra

variable (A : DifferentialGradedAlgebra.{t, t} (toRingCat J Osharp))

/-- The unit `O ⟶ A^0` of a sheaf of differential graded algebras: the section `1` of `A` in
degree zero, as a morphism out of the structure sheaf. -/
noncomputable def unitSection : (unitComplex Osharp).X 0 ⟶ A.complex.X 0 :=
  (unitXIso (Osharp := Osharp) rfl).hom ≫ (A.complex.X 0).unitHomEquiv.symm A.one

/-- On sections over `U`, the unit `O ⟶ A^0` sends `x` to `x • 1`. -/
theorem unitSection_app (U : Cᵒᵖ) (x : ((unitComplex Osharp).X 0).val.obj U) :
    (unitSection A).val.app U x = toScalar rfl U x • A.one.eval U := rfl

/-- The component in degree `k` of the unit `(O, 0) ⟶ A`. -/
noncomputable def unitAlgebraHomF (k : ℤ) : (unitComplex Osharp).X k ⟶ A.complex.X k :=
  if hk : k = 0 then
    degCastHom (unitComplex Osharp).X hk ≫ unitSection A ≫ degCastHom A.complex.X hk.symm
  else 0

/-- In a degree `k` equal to zero, the component of the unit sends `x` to `x • 1`, transported
along `k = 0`. -/
theorem unitAlgebraHomF_app_of_eq {k : ℤ} (hk : k = 0) (U : Cᵒᵖ)
    (x : ((unitComplex Osharp).X k).val.obj U) :
    (unitAlgebraHomF A k).val.app U x =
      castHom A.complex.X hk.symm U (toScalar hk U x • A.one.eval U) := by
  subst hk
  rfl

/-- In degree zero, the component of the unit sends `x` to `x • 1`. -/
theorem unitAlgebraHomF_app_zero (U : Cᵒᵖ) (x : ((unitComplex Osharp).X 0).val.obj U) :
    (unitAlgebraHomF A 0).val.app U x = toScalar rfl U x • A.one.eval U :=
  unitAlgebraHomF_app_of_eq A rfl U x

/-- In a nonzero degree, the component of the unit is zero. -/
theorem unitAlgebraHomF_app_of_ne {k : ℤ} (hk : k ≠ 0) (U : Cᵒᵖ)
    (x : ((unitComplex Osharp).X k).val.obj U) :
    (unitAlgebraHomF A k).val.app U x = 0 := by
  simp [unitAlgebraHomF, hk]
  rfl

/-- The degree-zero component of the unit sends `1` to `1`. -/
theorem unitAlgebraHomF_app_one (U : Cᵒᵖ) :
    (unitAlgebraHomF A 0).val.app U ((unitDGAlgebra Osharp).one.eval U) = A.one.eval U := by
  rw [unitAlgebraHomF_app_zero, one_eval, toScalar_ofScalar, one_smul]

/-- The unit `(O, 0) ⟶ A` as a morphism of cochain complexes: `r ↦ r · 1` in degree zero. -/
noncomputable def unitAlgebraComplexHom : unitComplex Osharp ⟶ A.complex where
  f := unitAlgebraHomF A
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
      ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
    have hd : (unitComplex Osharp).d i (i + 1) = 0 := rfl
    change (A.complex.d i (i + 1)).val.app U ((unitAlgebraHomF A i).val.app U x) =
      (unitAlgebraHomF A (i + 1)).val.app U (((unitComplex Osharp).d i (i + 1)).val.app U x)
    rw [hd, show ((0 : (unitComplex Osharp).X i ⟶ _).val.app U) x = 0 from rfl, map_zero]
    by_cases hi : i = 0
    · subst hi
      rw [unitAlgebraHomF_app_zero, ((A.complex.d 0 (0 + 1)).val.app U).hom.map_smul]
      change toScalar rfl U x • (A.complex.d 0 1).val.app U (A.one.eval U) = 0
      rw [A.one_closed U, smul_zero]
    · rw [unitAlgebraHomF_app_of_ne A hi, map_zero]

/-- **The unit `(O, 0) ⟶ A` of a sheaf of differential graded `O`-algebras**: in degree zero it
is `r ↦ r · 1`. -/
noncomputable def unitAlgebraHom : unitDGAlgebra Osharp ⟶ A where
  toHomologicalComplex := unitAlgebraComplexHom A
  map_mul n m U x y := by
    change (unitAlgebraHomF A (n + m)).val.app U (mulApp n m U x y) =
      (A.mul n m).app U ((unitAlgebraHomF A n).val.app U x) ((unitAlgebraHomF A m).val.app U y)
    by_cases h : n = 0 ∧ m = 0
    · obtain ⟨rfl, rfl⟩ := h
      rw [mulApp_of ⟨rfl, rfl⟩, unitAlgebraHomF_app_zero, unitAlgebraHomF_app_zero,
        unitAlgebraHomF_app_of_eq A (add_zero 0)]
      change (toScalar (add_zero 0) U (ofScalar (add_zero 0) U
          (toScalar rfl U x * toScalar rfl U y))) • A.one.eval U =
        (A.mul 0 0).app U (toScalar rfl U x • A.one.eval U) (toScalar rfl U y • A.one.eval U)
      rw [toScalar_ofScalar, (A.mul 0 0).map_smul_left, (A.mul 0 0).map_smul_right,
        eq_of_heq (A.mul_one 0 U (A.one.eval U)), mul_smul]
    · rw [mulApp_of_not h, map_zero]
      by_cases hn : n = 0
      · rw [unitAlgebraHomF_app_of_ne A (fun hm => h ⟨hn, hm⟩), map_zero]
      · rw [unitAlgebraHomF_app_of_ne A hn, map_zero, AddMonoidHom.zero_apply]

/-- The component in degree `k` of the unit `(O, 0) ⟶ A` is `unitAlgebraHomF A k`. -/
@[simp]
theorem unitAlgebraHom_f (k : ℤ) :
    (unitAlgebraHom A).toHomologicalComplex.f k = unitAlgebraHomF A k := rfl

/-- The unit `(O, 0) ⟶ A` preserves the unit. -/
theorem unitAlgebraHom_preservesOne : (unitAlgebraHom A).PreservesOne := fun U =>
  unitAlgebraHomF_app_one A U

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

/-- Families of morphisms indexed by integers respect heterogeneous equality of their
arguments along an equality of indices. -/
theorem heq_app_of_eq {X Y : ℤ → SheafOfModules.{m} (toRingCat J Osharp)}
    (h : ∀ k, X k ⟶ Y k) {k k' : ℤ} (hk : k = k') (U : Cᵒᵖ) {x : (X k).val.obj U}
    {x' : (X k').val.obj U} (hx : HEq x x') : HEq ((h k).val.app U x) ((h k').val.app U x') := by
  subst hk
  cases hx
  rfl

/-- A homotopy between the underlying morphisms of complexes of two morphisms of right
differential graded `(O, 0)`-modules is a homotopy of right differential graded
`(O, 0)`-modules. -/
noncomputable def unitHomotopyOfHomotopy
    {M N : DifferentialGradedModule.{t, t, m} (unitDGAlgebra Osharp)} {f g : M ⟶ N}
    (h : _root_.Homotopy f.toHomologicalComplex g.toHomologicalComplex) : Homotopy f g where
  app n := h.hom n (n - 1)
  map_mul n i U x a := by
    rw [unitMul_eq, unitMul_eq]
    by_cases hi : i = 0
    · subst hi
      rw [dif_pos rfl, dif_pos rfl]
      refine (heq_app_of_eq (fun k => h.hom k (k - 1)) (add_zero n) U
        (heq_castHom M.complex.X _ U _)).trans ?_
      refine HEq.trans ?_ (heq_castHom N.complex.X _ U _).symm
      exact heq_of_eq (homSections_smul (h.hom n (n - 1)) U _ x)
    · rw [dif_neg hi, dif_neg hi, map_zero]
      have : ∀ (a b : ℤ) (e : a = b),
          HEq (0 : (N.complex.X a).val.obj U) (0 : (N.complex.X b).val.obj U) := by
        intro a b e; subst e; rfl
      exact this _ _ (by omega)
  comm n := by
    have hc := h.comm n
    rw [dNext_eq _ (ComplexShape.up_mk n (n + 1) rfl),
      prevD_eq _ (ComplexShape.up_mk (n - 1) n (by omega))] at hc
    have he : h.hom (n + 1) (n + 1 - 1) ≫
        eqToHom (congrArg N.complex.X (show (n + 1) - 1 = n by omega)) = h.hom (n + 1) n := by
      have : ∀ (j : ℤ) (hj : j = n), h.hom (n + 1) j ≫ eqToHom (congrArg N.complex.X hj) =
          h.hom (n + 1) n := by
        rintro j rfl
        simp
      exact this _ (by omega)
    rw [Category.assoc, he, hc]
    abel

end DifferentialGradedModule

end SheafOfModules
