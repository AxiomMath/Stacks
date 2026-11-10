module

public import Mathlib.Algebra.Homology.Single
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetRightAdjoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedAlgebras
public import StacksCore.Tactic.StacksAttribute

/-!
# The differential graded algebra `(O, 0)` and its modules

Let `(C, O)` be a ringed site. The structure sheaf `O`, placed in degree zero with zero
differential, is a sheaf of differential graded `O`-algebras `(O, 0)`. A right differential graded
`(O, 0)`-module is the same thing as a cochain complex of `O`-modules: the action of a local
section `r` of `O` in degree zero is forced to be scalar multiplication by `r`, and there is
nothing else to act. This is the identification `Mod(O, 0) = Comp(O)`.

## Main definitions

* `SheafOfModules.unitDGAlgebra Osharp` is `(O, 0)`: the complex `O[0]` concentrated in degree
  zero, with the multiplication of `O`.
* `SheafOfModules.unitDGAlgebra.toScalar` and `ofScalar` read a degree-zero local section of
  `(O, 0)` as a local section of `O` and back.
* `SheafOfModules.DifferentialGradedModule.ofComplex K` is a cochain complex `K` of `O`-modules,
  regarded as a right differential graded `(O, 0)`-module.
* `SheafOfModules.DifferentialGradedModule.homMk` is a morphism of cochain complexes, regarded as a
  morphism of right differential graded `(O, 0)`-modules, and `isoMk` the same for isomorphisms.
* `SheafOfModules.DifferentialGradedAlgebra.toUnitModule B` is the underlying complex of
  `O`-modules of a sheaf of differential graded `O`-algebras `B`, regarded as a right
  differential graded `(O, 0)`-module.

## Main results

* `SheafOfModules.DifferentialGradedModule.unitMul_eq`: **the action of `(O, 0)` on any right
  differential graded `(O, 0)`-module is scalar multiplication** in degree zero, and zero in every
  other degree.
* `SheafOfModules.DifferentialGradedModule.toCochainComplex_unit_full` and
  `SheafOfModules.DifferentialGradedModule.toCochainComplex_unit_faithful`: forgetting the action
  identifies `Mod(O, 0)` with a full subcategory of the cochain complexes.
* `SheafOfModules.DifferentialGradedModule.isoOfComplex`: every right differential graded
  `(O, 0)`-module is isomorphic to `ofComplex` of its underlying complex.

## References

* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
* [Stacks Project, Tag 0FRF](https://stacks.math.columbia.edu/tag/0FRF)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] (Osharp : Sheaf J CommRingCat.{t})

/-- The category of sheaves of `O`-modules has a zero object. -/
noncomputable instance unitDGAlgebra.hasZeroObject :
    HasZeroObject (SheafOfModules.{t} (toRingCat J Osharp)) :=
  hasZeroObject_of_hasTerminal_object

/-- The complex `O[0]`: the structure sheaf in degree zero and zero elsewhere. -/
noncomputable abbrev unitComplex : CochainComplex (SheafOfModules.{t} (toRingCat J Osharp)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (SheafOfModules.unit _)

namespace unitDGAlgebra

variable {Osharp}

/-- Equal morphisms of sheaves of modules act equally on local sections. -/
private theorem app_apply_congr {X Y : SheafOfModules.{t} (toRingCat J Osharp)}
    {f g : X ⟶ Y} (h : f = g) (U : Cᵒᵖ) (x : X.val.obj U) : f.val.app U x = g.val.app U x := by
  rw [h]

/-- The identification of the degree-`i` piece of `O[0]` with `O`, for `i = 0`. -/
noncomputable abbrev unitXIso {i : ℤ} (h : i = 0) :
    (unitComplex Osharp).X i ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (toRingCat J Osharp)) i h

/-- A degree-zero local section of `O[0]`, read as a local section of `O`. -/
noncomputable def toScalar {i : ℤ} (h : i = 0) (U : Cᵒᵖ) :
    ((unitComplex Osharp).X i).val.obj U →ₗ[(toRingCat J Osharp).obj.obj U]
      (toRingCat J Osharp).obj.obj U :=
  ((unitXIso h).hom.val.app U).hom

/-- A local section of `O`, read as a degree-zero local section of `O[0]`. -/
noncomputable def ofScalar {i : ℤ} (h : i = 0) (U : Cᵒᵖ) :
    (toRingCat J Osharp).obj.obj U →ₗ[(toRingCat J Osharp).obj.obj U]
      ((unitComplex Osharp).X i).val.obj U :=
  ((unitXIso h).inv.val.app U).hom

/-- Reading a local section of `O` into degree zero of `O[0]` and back is the identity. -/
@[simp] theorem toScalar_ofScalar {i : ℤ} (h : i = 0) (U : Cᵒᵖ)
    (r : (toRingCat J Osharp).obj.obj U) : toScalar h U (ofScalar h U r) = r :=
  app_apply_congr (unitXIso (Osharp := Osharp) h).inv_hom_id U r

/-- Reading a degree-zero local section of `O[0]` as a section of `O` and back is the identity. -/
@[simp] theorem ofScalar_toScalar {i : ℤ} (h : i = 0) (U : Cᵒᵖ)
    (x : ((unitComplex Osharp).X i).val.obj U) : ofScalar h U (toScalar h U x) = x :=
  app_apply_congr (unitXIso (Osharp := Osharp) h).hom_inv_id U x

/-- `toScalar` commutes with restriction of local sections. -/
theorem toScalar_naturality {i : ℤ} (h : i = 0) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((unitComplex Osharp).X i).val.obj U) :
    toScalar h V (Stacks.sectionRestrict ((unitComplex Osharp).X i).val f x) =
      (toRingCat J Osharp).obj.map f (toScalar h U x) :=
  PresheafOfModules.naturality_apply (unitXIso (Osharp := Osharp) h).hom.val f x

/-- `ofScalar` commutes with restriction of local sections. -/
theorem ofScalar_naturality {i : ℤ} (h : i = 0) {U V : Cᵒᵖ} (f : U ⟶ V)
    (r : (toRingCat J Osharp).obj.obj U) :
    Stacks.sectionRestrict ((unitComplex Osharp).X i).val f (ofScalar h U r) =
      ofScalar h V ((toRingCat J Osharp).obj.map f r) :=
  (PresheafOfModules.naturality_apply (unitXIso (Osharp := Osharp) h).inv.val f r).symm

/-- Reading a degree-zero local section of `O[0]` as a section of `O` and back into a possibly
different index `i' = 0` gives the same section, up to heterogeneous equality. -/
theorem ofScalar_toScalar_heq {i i' : ℤ} (h : i = 0) (h' : i' = 0) (U : Cᵒᵖ)
    (x : ((unitComplex Osharp).X i).val.obj U) : HEq (ofScalar h' U (toScalar h U x)) x := by
  subst h h'
  rw [ofScalar_toScalar]

/-- The zero local sections of `O[0]` in equal degrees are heterogeneously equal. -/
theorem heq_zero {i i' : ℤ} (h : i = i') (U : Cᵒᵖ) :
    HEq (0 : ((unitComplex Osharp).X i).val.obj U) (0 : ((unitComplex Osharp).X i').val.obj U) := by
  subst h
  rfl

/-- `toScalar` is injective. -/
theorem toScalar_injective {i : ℤ} (h : i = 0) (U : Cᵒᵖ) :
    Function.Injective (toScalar (Osharp := Osharp) h U) := fun x y hxy => by
  rw [← ofScalar_toScalar h U x, ← ofScalar_toScalar h U y, hxy]

/-- Heterogeneously equal degree-zero local sections of `O[0]` read as the same section of `O`. -/
theorem toScalar_congr {i i' : ℤ} (h : i = 0) (h' : i' = 0) (U : Cᵒᵖ)
    {x : ((unitComplex Osharp).X i).val.obj U} {x' : ((unitComplex Osharp).X i').val.obj U}
    (hx : HEq x x') : toScalar h U x = toScalar h' U x' := by
  subst h h'
  rw [eq_of_heq hx]

/-- A local section of `O` read into two indices `i = 0` and `i' = 0` of `O[0]` gives
heterogeneously equal sections. -/
theorem ofScalar_heq {i i' : ℤ} (h : i = 0) (h' : i' = 0) (U : Cᵒᵖ)
    (r : (toRingCat J Osharp).obj.obj U) : HEq (ofScalar h U r) (ofScalar h' U r) := by
  subst h h'
  rfl

/-- In a nonzero degree every local section of `O[0]` vanishes. -/
theorem eq_zero {i : ℤ} (h : i ≠ 0) (U : Cᵒᵖ) (x : ((unitComplex Osharp).X i).val.obj U) :
    x = 0 := by
  have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (toRingCat J Osharp)) i h
  have e : 𝟙 ((unitComplex Osharp).X i) = 0 := hz.eq_of_src _ _
  exact app_apply_congr e U x

/-- The multiplication of `O[0]`: multiplication of `O` in degree zero, and zero otherwise. -/
noncomputable def mulApp (n i : ℤ) (U : Cᵒᵖ) :
    ((unitComplex Osharp).X n).val.obj U →+ ((unitComplex Osharp).X i).val.obj U →+
      ((unitComplex Osharp).X (n + i)).val.obj U :=
  if h : n = 0 ∧ i = 0 then
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
        (fun y => ofScalar (by omega) U (toScalar h.1 U x * toScalar h.2 U y))
        (fun y y' => by rw [map_add, mul_add, map_add]))
      (fun x x' => by ext y; simp [map_add, add_mul])
  else 0

/-- In bidegree `(0, 0)`, `mulApp` is the multiplication of `O`. -/
theorem mulApp_of {n i : ℤ} (h : n = 0 ∧ i = 0) (U : Cᵒᵖ)
    (x : ((unitComplex Osharp).X n).val.obj U) (y : ((unitComplex Osharp).X i).val.obj U) :
    mulApp n i U x y = ofScalar (by omega) U (toScalar h.1 U x * toScalar h.2 U y) := by
  rw [mulApp, dite_eq_left h]
  rfl

/-- Outside bidegree `(0, 0)`, `mulApp` is zero. -/
theorem mulApp_of_not {n i : ℤ} (h : ¬ (n = 0 ∧ i = 0)) (U : Cᵒᵖ)
    (x : ((unitComplex Osharp).X n).val.obj U) (y : ((unitComplex Osharp).X i).val.obj U) :
    mulApp n i U x y = 0 := by
  rw [mulApp, dite_eq_right h]
  rfl

/-- In bidegree `(0, 0)`, the product under `mulApp` reads as the product of the two scalars. -/
theorem toScalar_mulApp {n i : ℤ} (h : n = 0 ∧ i = 0) (h' : n + i = 0) (U : Cᵒᵖ)
    (x : ((unitComplex Osharp).X n).val.obj U) (y : ((unitComplex Osharp).X i).val.obj U) :
    toScalar h' U (mulApp n i U x y) = toScalar h.1 U x * toScalar h.2 U y := by
  rw [mulApp_of h, toScalar_ofScalar]

end unitDGAlgebra

open unitDGAlgebra in
/-- **The sheaf of differential graded algebras `(O, 0)`**: the structure sheaf in degree zero,
zero in every other degree, with zero differential and the multiplication of `O`. A right
differential graded module over it is a cochain complex of `O`-modules. -/
noncomputable abbrev unitDGAlgebra : DifferentialGradedAlgebra.{t, t} (toRingCat J Osharp) where
  complex := unitComplex Osharp
  mul n i :=
    { app U := mulApp n i U
      map_smul_left U r x y := by
        by_cases h : n = 0 ∧ i = 0
        · rw [mulApp_of h, mulApp_of h, map_smul, smul_eq_mul, mul_assoc, ← smul_eq_mul,
            map_smul]
        · rw [mulApp_of_not h, mulApp_of_not h, smul_zero]
      map_smul_right U r x y := by
        by_cases h : n = 0 ∧ i = 0
        · rw [mulApp_of h, mulApp_of h, map_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul,
            map_smul]
        · rw [mulApp_of_not h, mulApp_of_not h, smul_zero]
      naturality {U V} f x y := by
        change Stacks.sectionRestrict ((unitComplex Osharp).X (n + i)).val f (mulApp n i U x y) =
          mulApp n i V (Stacks.sectionRestrict ((unitComplex Osharp).X n).val f x)
            (Stacks.sectionRestrict ((unitComplex Osharp).X i).val f y)
        by_cases h : n = 0 ∧ i = 0
        · rw [mulApp_of h, mulApp_of h, ofScalar_naturality, map_mul, toScalar_naturality,
            toScalar_naturality]
        · rw [mulApp_of_not h, mulApp_of_not h, map_zero] }
  one := PresheafOfModules.sectionsMk (fun U => ofScalar rfl U 1) (fun {U V} f => by
    change Stacks.sectionRestrict ((unitComplex Osharp).X 0).val f (ofScalar rfl U 1) = _
    rw [ofScalar_naturality, map_one])
  mul_assoc n i j U x y z := by
    change HEq (mulApp (n + i) j U (mulApp n i U x y) z)
      (mulApp n (i + j) U x (mulApp i j U y z))
    by_cases h : n = 0 ∧ i = 0 ∧ j = 0
    · rw [mulApp_of (n := n + i) (i := j) ⟨by omega, h.2.2⟩, mulApp_of ⟨h.1, h.2.1⟩,
        mulApp_of (n := n) (i := i + j) ⟨h.1, by omega⟩, mulApp_of ⟨h.2.1, h.2.2⟩,
        toScalar_ofScalar, toScalar_ofScalar, mul_assoc]
      exact ofScalar_heq _ _ U _
    · by_cases hni : n = 0 ∧ i = 0
      · have hj : j ≠ 0 := fun hj => h ⟨hni.1, hni.2, hj⟩
        rw [mulApp_of_not (fun h' => hj h'.2), mulApp_of_not (i := j) (fun h' => hj h'.2),
          map_zero]
        exact heq_zero (add_assoc n i j) U
      · rw [mulApp_of_not hni, map_zero, AddMonoidHom.zero_apply]
        by_cases hij : i = 0 ∧ j = 0
        · rw [mulApp_of_not (fun h' => hni ⟨h'.1, hij.1⟩)]
          exact heq_zero (add_assoc n i j) U
        · rw [mulApp_of_not hij, map_zero]
          exact heq_zero (add_assoc n i j) U
  one_mul n U x := by
    change HEq (mulApp 0 n U (ofScalar rfl U 1) x) x
    by_cases h : n = 0
    · rw [mulApp_of ⟨rfl, h⟩, toScalar_ofScalar, one_mul]
      exact ofScalar_toScalar_heq h _ U x
    · rw [mulApp_of_not (fun h' => h h'.2), eq_zero h U x]
      exact heq_zero (zero_add n) U
  mul_one n U x := by
    change HEq (mulApp n 0 U x (ofScalar rfl U 1)) x
    by_cases h : n = 0
    · rw [mulApp_of ⟨h, rfl⟩, toScalar_ofScalar, mul_one]
      exact ofScalar_toScalar_heq h _ U x
    · rw [mulApp_of_not (fun h' => h h'.1), eq_zero h U x]
      exact heq_zero (add_zero n) U
  leibniz n i U x y := by
    have hd : ∀ (a b : ℤ) (z : ((unitComplex Osharp).X a).val.obj U),
        ((unitComplex Osharp).d a b).val.app U z = 0 := fun _ _ _ => rfl
    rw [hd, hd, hd]
    change (0 : ((unitComplex Osharp).X (n + i + 1)).val.obj U) =
      gradedCast (fun q ↦ (((unitComplex Osharp).X q).val.obj U)) (add_right_comm n 1 i)
          (mulApp (n + 1) i U 0 y) +
        (Int.negOnePow n : ℤ) •
          gradedCast (fun q ↦ (((unitComplex Osharp).X q).val.obj U)) (add_assoc n i 1).symm
            (mulApp n (i + 1) U x 0)
    rw [map_zero, AddMonoidHom.zero_apply, map_zero, gradedCast_zero, gradedCast_zero, smul_zero,
      add_zero]

namespace unitDGAlgebra

variable {Osharp}

/-- The underlying complex of `(O, 0)` is `O[0]`. -/
@[simp] theorem complex_eq : (unitDGAlgebra Osharp).complex = unitComplex Osharp := rfl

/-- The unit of `(O, 0)` over `U` is the section `1` of `O`, in degree zero. -/
theorem one_eval (U : Cᵒᵖ) : (unitDGAlgebra Osharp).one.eval U = ofScalar rfl U 1 := rfl

/-- The multiplication of `(O, 0)` on local sections is `mulApp`. -/
theorem mul_app (n i : ℤ) (U : Cᵒᵖ) (x : ((unitComplex Osharp).X n).val.obj U)
    (y : ((unitComplex Osharp).X i).val.obj U) :
    ((unitDGAlgebra Osharp).mul n i).app U x y = mulApp n i U x y := rfl

/-- The degree-zero piece of `(O, 0)` is `O`. -/
noncomputable def pieceZeroIso :
    (unitDGAlgebra Osharp).complex.X 0 ≅ SheafOfModules.unit (toRingCat J Osharp) :=
  HomologicalComplex.singleObjXSelf _ 0 _

/-- Every piece of `(O, 0)` in a nonzero degree is zero. -/
theorem isZero_piece {i : ℤ} (h : i ≠ 0) : IsZero ((unitDGAlgebra Osharp).complex.X i) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 _ i h

/-- The differential of `(O, 0)` is zero. -/
theorem d_eq_zero (i j : ℤ) : (unitDGAlgebra Osharp).complex.d i j = 0 := rfl

/-- A degree-zero local section of `(O, 0)` is the scalar it reads as, times the unit. -/
theorem eq_smul_one {i : ℤ} (h : i = 0) (U : Cᵒᵖ) (y : ((unitComplex Osharp).X i).val.obj U) :
    HEq y (toScalar h U y • (unitDGAlgebra Osharp).one.eval U) := by
  subst h
  have e := (ofScalar (Osharp := Osharp) rfl U).map_smul (toScalar rfl U y) 1
  rw [smul_eq_mul, mul_one, ofScalar_toScalar] at e
  exact heq_of_eq e

end unitDGAlgebra

namespace DifferentialGradedModule

open unitDGAlgebra

variable {Osharp}

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Transport along an equality of degrees commutes with the differential of a complex. -/
theorem d_castHom {R : Sheaf J RingCat.{t}} (K : CochainComplex (SheafOfModules.{m} R) ℤ)
    {a b : ℤ} (h : a = b) (h' : a + 1 = b + 1) (U : Cᵒᵖ) (z : (K.X a).val.obj U) :
    (K.d b (b + 1)).val.app U (castHom K.X h U z) =
      castHom K.X h' U ((K.d a (a + 1)).val.app U z) := by
  subst h
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Scalar multiples of a local section transported along two equalities of degrees with the same
source are heterogeneously equal. -/
theorem smul_castHom_heq {R : Sheaf J RingCat.{t}} (X : ℤ → SheafOfModules.{m} R) {a b b' : ℤ}
    (h : a = b) (h' : a = b') (U : Cᵒᵖ) (c : R.obj.obj U) (z : (X a).val.obj U) :
    HEq (c • castHom X h U z) (c • castHom X h' U z) := by
  subst h h'
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Transport along an equality of degrees commutes with restriction. -/
theorem restrict_castHom {R : Sheaf J RingCat.{t}} (X : ℤ → SheafOfModules.{m} R) {a b : ℤ}
    (h : a = b) {U V : Cᵒᵖ} (f : U ⟶ V) (z : (X a).val.obj U) :
    Stacks.sectionRestrict (X b).val f (castHom X h U z) =
      castHom X h V (Stacks.sectionRestrict (X a).val f z) := by
  subst h
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] in
/-- Transport along an equality of degrees commutes with a morphism of complexes. -/
theorem f_castHom {R : Sheaf J RingCat.{t}} {K L : CochainComplex (SheafOfModules.{m} R) ℤ}
    (φ : K ⟶ L) {a b : ℤ} (h : a = b) (U : Cᵒᵖ) (z : (K.X a).val.obj U) :
    (φ.f b).val.app U (castHom K.X h U z) = castHom L.X h U ((φ.f a).val.app U z) := by
  subst h
  rfl

/-- **The action of `(O, 0)` on a right differential graded `(O, 0)`-module is scalar
multiplication** in degree zero and zero in every other degree. -/
theorem unitMul_eq (M : DifferentialGradedModule.{t, t, m} (unitDGAlgebra Osharp)) (n i : ℤ)
    (U : Cᵒᵖ) (x : (M.complex.X n).val.obj U) (y : ((unitComplex Osharp).X i).val.obj U) :
    (M.mul n i).app U x y =
      if h : i = 0 then castHom M.complex.X (show n = n + i by omega) U (toScalar h U y • x)
        else 0 := by
  by_cases h : i = 0
  · rw [dite_eq_left h]
    subst h
    have h1 : (M.mul n 0).app U x ((unitDGAlgebra Osharp).one.eval U) =
        castHom M.complex.X (show n = n + 0 by omega) U x :=
      eq_of_heq ((M.mul_one n U x).trans (heq_castHom _ _ U x).symm)
    calc (M.mul n 0).app U x y
        = (M.mul n 0).app U x (toScalar rfl U y • (unitDGAlgebra Osharp).one.eval U) :=
          congrArg _ (eq_of_heq (eq_smul_one rfl U y))
      _ = toScalar rfl U y • (M.mul n 0).app U x ((unitDGAlgebra Osharp).one.eval U) :=
          (M.mul n 0).map_smul_right U _ x _
      _ = _ := by rw [h1, castHom_smul]
  · rw [dite_eq_right h, unitDGAlgebra.eq_zero h U y]
    exact map_zero _

/-- **A morphism of cochain complexes is a morphism of right differential graded
`(O, 0)`-modules**: the action is scalar multiplication, which every morphism of complexes of
`O`-modules commutes with. -/
def homMk {M N : DifferentialGradedModule.{t, t, m} (unitDGAlgebra Osharp)}
    (φ : M.complex ⟶ N.complex) : M ⟶ N where
  toHomologicalComplex := φ
  map_mul n i U x y := by
    rw [unitMul_eq, unitMul_eq]
    by_cases h : i = 0
    · rw [dite_eq_left h, dite_eq_left h, f_castHom, map_smul]
    · rw [dite_eq_right h, dite_eq_right h, map_zero]

/-- The underlying morphism of complexes of `homMk φ` is `φ`. -/
@[simp] theorem homMk_toHomologicalComplex
    {M N : DifferentialGradedModule.{t, t, m} (unitDGAlgebra Osharp)}
    (φ : M.complex ⟶ N.complex) : (homMk φ).toHomologicalComplex = φ := rfl

/-- An isomorphism of cochain complexes is an isomorphism of right differential graded
`(O, 0)`-modules. -/
def isoMk {M N : DifferentialGradedModule.{t, t, m} (unitDGAlgebra Osharp)}
    (e : M.complex ≅ N.complex) : M ≅ N where
  hom := homMk e.hom
  inv := homMk e.inv
  hom_inv_id := Hom.ext fun n => congrArg (fun φ => HomologicalComplex.Hom.f φ n) e.hom_inv_id
  inv_hom_id := Hom.ext fun n => congrArg (fun φ => HomologicalComplex.Hom.f φ n) e.inv_hom_id

/-- The forgetful functor from right differential graded `(O, 0)`-modules to cochain complexes is
faithful. -/
instance toCochainComplex_unit_faithful :
    (toCochainComplex.{t, t, m} (unitDGAlgebra Osharp)).Faithful where
  map_injective {_ _} _ _ h := Hom.ext fun n => congrArg (fun φ => HomologicalComplex.Hom.f φ n) h

/-- The forgetful functor from right differential graded `(O, 0)`-modules to cochain complexes is
full. -/
instance toCochainComplex_unit_full : (toCochainComplex.{t, t, m} (unitDGAlgebra Osharp)).Full where
  map_surjective φ := ⟨homMk φ, rfl⟩

/-- The action of `(O, 0)` on a cochain complex of `O`-modules: scalar multiplication in degree
zero. -/
noncomputable def ofComplexMulApp (K : CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ)
    (n i : ℤ) (U : Cᵒᵖ) :
    (K.X n).val.obj U →+ ((unitComplex Osharp).X i).val.obj U →+ (K.X (n + i)).val.obj U :=
  if h : i = 0 then
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
        (fun y => castHom K.X (show n = n + i by omega) U (toScalar h U y • x))
        (fun y y' => by rw [map_add, add_smul, map_add]))
      (fun x x' => by ext y; simp [smul_add, map_add])
  else 0

/-- In degree zero, `ofComplexMulApp` is scalar multiplication by the section of `O`. -/
theorem ofComplexMulApp_of (K : CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ)
    {n i : ℤ} (h : i = 0) (U : Cᵒᵖ) (x : (K.X n).val.obj U)
    (y : ((unitComplex Osharp).X i).val.obj U) :
    ofComplexMulApp K n i U x y = castHom K.X (show n = n + i by omega) U (toScalar h U y • x) := by
  rw [ofComplexMulApp, dite_eq_left h]
  rfl

/-- In a nonzero degree, `ofComplexMulApp` is zero. -/
theorem ofComplexMulApp_of_ne (K : CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ)
    {n i : ℤ} (h : i ≠ 0) (U : Cᵒᵖ) (x : (K.X n).val.obj U)
    (y : ((unitComplex Osharp).X i).val.obj U) : ofComplexMulApp K n i U x y = 0 := by
  rw [ofComplexMulApp, dite_eq_right h]
  rfl

/-- `ofComplexMulApp` is `O`-linear in its first argument. -/
theorem ofComplexMulApp_smul_left
    (K : CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ) (n i : ℤ) (U : Cᵒᵖ)
    (r : (toRingCat J Osharp).obj.obj U) (x : (K.X n).val.obj U)
    (y : ((unitComplex Osharp).X i).val.obj U) :
    ofComplexMulApp K n i U (r • x) y = r • ofComplexMulApp K n i U x y := by
  by_cases h : i = 0
  · rw [ofComplexMulApp_of K h, ofComplexMulApp_of K h, smul_comm, castHom_smul]
  · rw [ofComplexMulApp_of_ne K h, ofComplexMulApp_of_ne K h, smul_zero]

/-- `ofComplexMulApp` is `O`-linear in its second argument. -/
theorem ofComplexMulApp_smul_right
    (K : CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ) (n i : ℤ) (U : Cᵒᵖ)
    (r : (toRingCat J Osharp).obj.obj U) (x : (K.X n).val.obj U)
    (y : ((unitComplex Osharp).X i).val.obj U) :
    ofComplexMulApp K n i U x (r • y) = r • ofComplexMulApp K n i U x y := by
  by_cases h : i = 0
  · rw [ofComplexMulApp_of K h, ofComplexMulApp_of K h, (toScalar h U).map_smul, smul_eq_mul,
      mul_smul, castHom_smul]
  · rw [ofComplexMulApp_of_ne K h, ofComplexMulApp_of_ne K h, smul_zero]

/-- `ofComplexMulApp` commutes with restriction of local sections. -/
theorem ofComplexMulApp_naturality
    (K : CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ) (n i : ℤ) {U V : Cᵒᵖ}
    (f : U ⟶ V) (x : (K.X n).val.obj U) (y : ((unitComplex Osharp).X i).val.obj U) :
    Stacks.sectionRestrict (K.X (n + i)).val f (ofComplexMulApp K n i U x y) =
      ofComplexMulApp K n i V (Stacks.sectionRestrict (K.X n).val f x)
        (Stacks.sectionRestrict ((unitComplex Osharp).X i).val f y) := by
  by_cases h : i = 0
  · rw [ofComplexMulApp_of K h, ofComplexMulApp_of K h, toScalar_naturality,
      ← Stacks.sectionRestrict_smul]
    exact restrict_castHom K.X _ f _
  · rw [ofComplexMulApp_of_ne K h, ofComplexMulApp_of_ne K h, map_zero]

/-- **A cochain complex of `O`-modules, regarded as a right differential graded
`(O, 0)`-module**: a local section `r` of `O` in degree zero acts by scalar multiplication. -/
noncomputable def ofComplex (K : CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ) :
    DifferentialGradedModule.{t, t, m} (unitDGAlgebra Osharp) where
  complex := K
  mul n i :=
    { app U := ofComplexMulApp K n i U
      map_smul_left U r x y := ofComplexMulApp_smul_left K n i U r x y
      map_smul_right U r x y := ofComplexMulApp_smul_right K n i U r x y
      naturality {U V} f x y := ofComplexMulApp_naturality K n i f x y }
  mul_assoc n i j U x y z := by
    change HEq (ofComplexMulApp K (n + i) j U (ofComplexMulApp K n i U x y) z)
      (ofComplexMulApp K n (i + j) U x (mulApp i j U y z))
    by_cases h : i = 0 ∧ j = 0
    · rw [ofComplexMulApp_of K h.2, ofComplexMulApp_of K h.1,
        ofComplexMulApp_of K (i := i + j) (by omega), toScalar_mulApp h (by omega), castHom_smul,
        castHom_smul, castHom_smul, smul_smul, mul_comm, Cofree.castHom_castHom,
        castHom_smul (h := show n = n + (i + j) by omega)]
      exact smul_castHom_heq K.X _ _ U _ x
    · have h0 : ∀ (a b : ℤ) (e : a = b), HEq (0 : (K.X a).val.obj U) (0 : (K.X b).val.obj U) := by
        rintro a b rfl
        rfl
      by_cases hi : i = 0
      · have hj : j ≠ 0 := fun hj => h ⟨hi, hj⟩
        rw [ofComplexMulApp_of_ne K hj, mulApp_of_not (fun h' => hj h'.2), map_zero]
        exact h0 _ _ (add_assoc n i j)
      · rw [ofComplexMulApp_of_ne K hi, map_zero, AddMonoidHom.zero_apply,
          mulApp_of_not (fun h' => hi h'.1), map_zero]
        exact h0 _ _ (add_assoc n i j)
  mul_one n U x := by
    change HEq (ofComplexMulApp K n 0 U x (ofScalar rfl U 1)) x
    rw [ofComplexMulApp_of K rfl, toScalar_ofScalar, one_smul]
    exact heq_castHom _ _ U x
  leibniz n i U x y := by
    have h2 : ((unitDGAlgebra Osharp).complex.d i (i + 1)).val.app U y = 0 := rfl
    rw [h2]
    change (K.d (n + i) (n + i + 1)).val.app U (ofComplexMulApp K n i U x y) =
      gradedCast (fun q ↦ ((K.X q).val.obj U)) (add_right_comm n 1 i)
          (ofComplexMulApp K (n + 1) i U ((K.d n (n + 1)).val.app U x) y) +
        (Int.negOnePow n : ℤ) • gradedCast (fun q ↦ ((K.X q).val.obj U)) (add_assoc n i 1).symm
          (ofComplexMulApp K n (i + 1) U x 0)
    rw [map_zero, gradedCast_zero, smul_zero, add_zero]
    by_cases h : i = 0
    · rw [ofComplexMulApp_of K h, ofComplexMulApp_of K h, d_castHom K _ (by omega), map_smul,
        ← castHom_apply, Cofree.castHom_castHom]
    · rw [ofComplexMulApp_of_ne K h, ofComplexMulApp_of_ne K h, map_zero, gradedCast_zero]

/-- The underlying complex of `ofComplex K` is `K`. -/
@[simp] theorem ofComplex_complex
    (K : CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ) :
    (ofComplex K).complex = K := rfl

/-- A morphism of cochain complexes, regarded as a morphism between the two right differential
graded `(O, 0)`-modules. -/
noncomputable def ofComplexMap {K L : CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ}
    (φ : K ⟶ L) : ofComplex K ⟶ ofComplex L :=
  homMk φ

/-- **Cochain complexes of `O`-modules, regarded as right differential graded
`(O, 0)`-modules.** -/
noncomputable def ofComplexFunctor :
    CochainComplex (SheafOfModules.{m} (toRingCat J Osharp)) ℤ ⥤
      DifferentialGradedModule.{t, t, m} (unitDGAlgebra Osharp) where
  obj := ofComplex
  map := ofComplexMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Every right differential graded `(O, 0)`-module is the module of its underlying complex. -/
noncomputable def isoOfComplex (M : DifferentialGradedModule.{t, t, m} (unitDGAlgebra Osharp)) :
    M ≅ ofComplex M.complex :=
  isoMk (Iso.refl _)

end DifferentialGradedModule

namespace DifferentialGradedAlgebra

variable {Osharp}

/-- **The underlying complex of `O`-modules of a sheaf of differential graded `O`-algebras**,
regarded as a right differential graded `(O, 0)`-module. Its flatness as a graded
`(O, 0)`-module and its K-flatness are flatness as a graded `O`-module and K-flatness as a
complex of `O`-modules. -/
noncomputable abbrev toUnitModule (B : DifferentialGradedAlgebra.{t, t} (toRingCat J Osharp)) :
    DifferentialGradedModule.{t, t, t} (unitDGAlgebra Osharp) :=
  DifferentialGradedModule.ofComplex B.complex

end DifferentialGradedAlgebra

end SheafOfModules

end
