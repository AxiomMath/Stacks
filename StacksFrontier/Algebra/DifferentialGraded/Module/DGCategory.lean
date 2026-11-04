module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.CochainComplex
public import StacksFrontier.Algebra.DifferentialGraded.Sign
public import StacksFrontier.Algebra.DGA.DGCategory

/-!
# The differential graded category of differential graded modules

For a differential graded algebra `(A, d)` over a commutative ring `R`, the right differential
graded `A`-modules are the objects of a differential graded category: a homogeneous morphism of
degree `n` from `L` to `M` is a right `A`-linear map raising degrees by `n`, the differential of
such a morphism is the graded commutator `d_M ∘ f - (-1)^n (f ∘ d_L)` with the differentials of
the two modules, and composition is composition of maps. The category of complexes and the
homotopy category of this differential graded category are the category and the homotopy
category of differential graded modules.

## Main definitions

* `DifferentialGradedModule.homogeneousMapSubmodule` and
  `DifferentialGradedModule.HomogeneousMap`: the `R`-module of homogeneous right `A`-linear maps
  of a fixed degree.
* `DifferentialGradedModule.homogeneousMapDifferential`,
  `DifferentialGradedModule.homogeneousMapComp` and
  `DifferentialGradedModule.homogeneousMapId`: the differential, composition and identities of
  homogeneous maps.
* `DifferentialGradedModule.dgCategory`: the resulting `DGCategory`.
* `DifferentialGradedModule.DGCategoryData`: a differential graded category together with the
  identification of its objects with differential graded modules and of its homogeneous
  morphisms with homogeneous maps, and the formulas these identifications satisfy.
* `DifferentialGradedModule.dgCategoryData`: the construction of that data.

## Main results

The formulas for the differential, the composition and the identity of the differential graded
category are `DifferentialGradedModule.dgCategory_d_val`,
`DifferentialGradedModule.dgCategory_comp_val` and
`DifferentialGradedModule.dgCategory_id_val`, and are also fields of `DGCategoryData`.

## Implementation notes

The model of a differential graded category is `DGCategory`. The construction is stated through
`DGCategoryData`, using an equivalence on objects and linear equivalences on homogeneous
morphisms, so that the canonical formulas for the differential, the identity and the composition
are part of the statement while no universe-dependent transport of morphisms is needed.
Right-linearity of a homogeneous map carries no sign; the sign appears only in the differential
of the Hom module, where it is `DifferentialGraded.gradedSign`. Both the `DGCategory` and the
data are implicitly reducible, so clients can synthesize the additive-group and module instances
on homogeneous morphisms directly.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

@[expose] public section

namespace DifferentialGradedModule

universe u v w

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

/-- A homogeneous right `A`-linear map of degree `n` between differential graded modules. -/
@[stacks 09LC "differential_graded_category_of_differential_graded_modules"]
public def homogeneousMapSubmodule (L M : DifferentialGradedModule.{u, v, w} A)
    (n : ℤ) : Submodule R (L.M →ₗ[R] M.M) where
  carrier := { f | (∀ i x, x ∈ L.grading i → f x ∈ M.grading (i + n)) ∧
    (∀ (a : A.A) (x : L.M), f (MulOpposite.op a • x) = MulOpposite.op a • f x) }
  zero_mem' := ⟨fun i _ _ => (M.grading (i + n)).zero_mem, fun _ _ => by simp⟩
  add_mem' {f g} hf hg :=
    ⟨fun i x hx => (M.grading (i + n)).add_mem (hf.1 i x hx) (hg.1 i x hx),
      fun a x => by simp [hf.2 a x, hg.2 a x, smul_add]⟩
  smul_mem' r f hf := ⟨fun i x hx => (M.grading (i + n)).smul_mem r (hf.1 i x hx), fun a x => by
    change r • f (MulOpposite.op a • x) = MulOpposite.op a • (r • f x)
    rw [hf.2 a x, smul_comm]⟩

/-- A linear map lies in `homogeneousMapSubmodule A L M n` if and only if it raises degrees by `n`
and is right `A`-linear. -/
@[simp] public theorem mem_homogeneousMapSubmodule
    {L M : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    {f : L.M →ₗ[R] M.M} :
    f ∈ homogeneousMapSubmodule A L M n ↔
      (∀ i x, x ∈ L.grading i → f x ∈ M.grading (i + n)) ∧
      (∀ (a : A.A) (x : L.M), f (MulOpposite.op a • x) = MulOpposite.op a • f x) :=
  Iff.rfl

/-- Degree-`n` homogeneous right `A`-linear maps. -/
public abbrev HomogeneousMap (L M : DifferentialGradedModule.{u, v, w} A) (n : ℤ) :=
  homogeneousMapSubmodule A L M n

/-- Data identifying a differential graded category with differential graded `A`-modules and
their homogeneous right-linear maps. -/
public structure DGCategoryData where
  category : DGCategory.{w, max (max u v) (w + 1), u} R
  objects : category.Obj ≃ DifferentialGradedModule.{u, v, w} A
  hom : ∀ (X Y : category.Obj) (n : ℤ),
    category.Hom X Y n ≃ₗ[R] HomogeneousMap A (objects X) (objects Y) n
  differential : ∀ (X Y : category.Obj) (n : ℤ) (f : category.Hom X Y n),
    ((hom X Y (n + 1)) (category.d f)).1 =
      (objects Y).d ∘ₗ ((hom X Y n) f).1 -
        ((-1 : R) ^ n.natAbs) • (((hom X Y n) f).1 ∘ₗ (objects X).d)
  composition : ∀ (X Y Z : category.Obj) (m n k : ℤ) (h : m + n = k)
      (g : category.Hom Y Z m) (f : category.Hom X Y n),
    ((hom X Z k) (category.comp h g f)).1 =
      ((hom Y Z m) g).1 ∘ₗ ((hom X Y n) f).1
  identity : ∀ X : category.Obj,
    ((hom X X 0) (category.id X)).1 = LinearMap.id

/-- The differential `d_M ∘ f - (-1)^n (f ∘ d_L)` of a homogeneous map `f` of degree `n`, a
homogeneous map of degree `n + 1`. -/
public def homogeneousMapDifferential {L M : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f : HomogeneousMap A L M n) : HomogeneousMap A L M (n + 1) :=
  ⟨M.d ∘ₗ f.1 - DifferentialGraded.gradedSign R n • (f.1 ∘ₗ L.d), fun i x hx => by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply]
      refine (M.grading (i + (n + 1))).sub_mem ?_ ((M.grading (i + (n + 1))).smul_mem _ ?_)
      · simpa only [add_assoc] using M.d_mem (i + n) (f.1 x) (f.2.1 i x hx)
      · change f.1 (L.d x) ∈ M.grading (i + (n + 1))
        simpa only [add_assoc, add_comm 1 n] using f.2.1 (i + 1) (L.d x) (L.d_mem i x hx),
    fun a x => by
      induction x using DirectSum.Decomposition.inductionOn L.grading with
      | zero => simp
      | @homogeneous i x =>
        change M.d (f.1 (MulOpposite.op a • x)) -
            DifferentialGraded.gradedSign R n • f.1 (L.d (MulOpposite.op a • x)) =
          MulOpposite.op a • (M.d (f.1 x) - DifferentialGraded.gradedSign R n • f.1 (L.d x))
        rw [f.2.2 a x, M.leibniz_apply (i + n) (f.1 x) (f.2.1 i x x.property) a,
          L.leibniz_apply i x x.property a, map_add, map_zsmul, f.2.2 (A.d a) x]
        simp only [← Int.cast_smul_eq_zsmul R, DifferentialGraded.intCast_negOnePow,
          DifferentialGraded.gradedSign_add i n, smul_add, smul_sub, smul_smul]
        rw [mul_comm (DifferentialGraded.gradedSign R i) (DifferentialGraded.gradedSign R n),
          f.2.2 a (L.d x), smul_comm (DifferentialGraded.gradedSign R n) (MulOpposite.op a)]
        abel
      | add x y hx hy => simp only [map_add, smul_add, hx, hy]⟩

/-- The composition of homogeneous maps of degrees `m` and `n`, a homogeneous map of degree
`k = m + n`. -/
public def homogeneousMapComp {L M N : DifferentialGradedModule.{u, v, w} A}
    {m n k : ℤ} (h : m + n = k)
    (g : HomogeneousMap A M N m) (f : HomogeneousMap A L M n) :
    HomogeneousMap A L N k :=
  ⟨g.1 ∘ₗ f.1, fun i x hx => by
      simpa only [LinearMap.comp_apply, ← h, add_assoc, add_left_comm, add_comm] using
        g.2.1 (i + n) (f.1 x) (f.2.1 i x hx),
    fun a x => by simp only [LinearMap.comp_apply, f.2.2 a, g.2.2 a]⟩

/-- The identity of a differential graded module, a homogeneous map of degree `0`. -/
public def homogeneousMapId (L : DifferentialGradedModule.{u, v, w} A) :
    HomogeneousMap A L L 0 :=
  ⟨LinearMap.id, fun _ _ hx => by simpa only [add_zero, LinearMap.id_apply] using hx,
    fun _ _ => rfl⟩

/-- The underlying linear map of `homogeneousMapDifferential A f` is
`d_M ∘ f - (-1)^n (f ∘ d_L)`. -/
@[simp] public theorem homogeneousMapDifferential_val {L M : DifferentialGradedModule.{u, v, w} A}
    {n : ℤ} (f : HomogeneousMap A L M n) :
    (homogeneousMapDifferential A f).1 =
      M.d ∘ₗ f.1 - DifferentialGraded.gradedSign R n • (f.1 ∘ₗ L.d) := rfl

/-- The underlying linear map of `homogeneousMapComp A h g f` is the composite `g ∘ f`. -/
@[simp] public theorem homogeneousMapComp_val {L M N : DifferentialGradedModule.{u, v, w} A}
    {m n k : ℤ} (h : m + n = k)
    (g : HomogeneousMap A M N m) (f : HomogeneousMap A L M n) :
    (homogeneousMapComp A h g f).1 = g.1 ∘ₗ f.1 := rfl

/-- The underlying linear map of `homogeneousMapId A L` is the identity. -/
@[simp] public theorem homogeneousMapId_val (L : DifferentialGradedModule.{u, v, w} A) :
    (homogeneousMapId A L).1 = LinearMap.id := rfl

/-- The differential graded category of right differential graded `A`-modules: its homogeneous
morphisms of degree `n` are the homogeneous right `A`-linear maps of degree `n`, with
differential `homogeneousMapDifferential`, composition `homogeneousMapComp` and identities
`homogeneousMapId`. -/
@[implicit_reducible] public def dgCategory : DGCategory.{w, max (max u v) (w + 1), u} R where
  Obj := DifferentialGradedModule.{u, v, w} A
  Hom L M n := HomogeneousMap A L M n
  addCommGroup L M n := inferInstance
  module L M n := inferInstance
  d := homogeneousMapDifferential A
  d_add := by
    intros
    ext
    simp [homogeneousMapDifferential, LinearMap.comp_apply, LinearMap.sub_apply, smul_add]
    abel
  d_smul := by
    intros
    ext
    simp only [homogeneousMapDifferential, SetLike.val_smul, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_smul, mul_comm, smul_sub]
  d_d := by
    intro L M n f
    ext x
    simp only [homogeneousMapDifferential, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, map_sub, map_smul, smul_sub, smul_smul, ZeroMemClass.coe_zero,
      LinearMap.zero_apply]
    have hdM := LinearMap.congr_fun M.d_comp_d (f.1 x)
    have hdL := LinearMap.congr_fun L.d_comp_d x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hdM hdL
    rw [hdM, hdL, map_zero, smul_zero, DifferentialGraded.gradedSign_succ]
    simp only [neg_smul]
    abel
  comp := homogeneousMapComp A
  comp_add_left := by
    intros
    ext
    simp [homogeneousMapComp, LinearMap.comp_apply]
  comp_add_right := by
    intros
    ext
    simp [homogeneousMapComp, LinearMap.comp_apply]
  comp_smul_left := by
    intros
    ext
    simp [homogeneousMapComp, LinearMap.comp_apply]
  comp_smul_right := by
    intros
    ext
    simp [homogeneousMapComp, LinearMap.comp_apply]
  leibniz := by
    intro L M N m n k h g f
    ext
    simp only [homogeneousMapDifferential, homogeneousMapComp, LinearMap.sub_apply,
      LinearMap.comp_apply, LinearMap.smul_apply, SetLike.mk_smul_mk, AddMemClass.mk_add_mk,
      LinearMap.add_apply, map_sub, map_smul, smul_sub, smul_smul]
    rw [← h, DifferentialGraded.gradedSign_add,
      show (-1 : R) ^ m.natAbs = DifferentialGraded.gradedSign R m from rfl]
    abel
  assoc := by
    intros
    rfl
  id := homogeneousMapId A
  id_comp := by
    intros
    rfl
  comp_id := by
    intros
    rfl
  d_id := by
    intros
    ext
    simp [homogeneousMapDifferential, homogeneousMapId, DifferentialGraded.gradedSign_zero]

/-- The differential of `dgCategory A` on underlying linear maps is
`d_M ∘ f - (-1)^n (f ∘ d_L)`. -/
@[simp] public theorem dgCategory_d_val {L M : DifferentialGradedModule.{u, v, w} A}
    {n : ℤ} (f : (dgCategory A).Hom L M n) :
    ((dgCategory A).d f).1 = M.d ∘ₗ f.1 - DifferentialGraded.gradedSign R n • (f.1 ∘ₗ L.d) := rfl

/-- Composition in `dgCategory A` is composition of underlying linear maps. -/
@[simp] public theorem dgCategory_comp_val {L M N : DifferentialGradedModule.{u, v, w} A}
    {m n k : ℤ} (h : m + n = k)
    (g : (dgCategory A).Hom M N m) (f : (dgCategory A).Hom L M n) :
    ((dgCategory A).comp h g f).1 = g.1 ∘ₗ f.1 := rfl

/-- The identity of `dgCategory A` is the identity linear map. -/
@[simp] public theorem dgCategory_id_val (L : DifferentialGradedModule.{u, v, w} A) :
    ((dgCategory A).id L).1 = LinearMap.id := rfl

/-- The differential graded category of right differential graded modules over `A`. -/
@[stacks 09LC "differential_graded_category_of_differential_graded_modules"]
public noncomputable def dgCategoryData :
    DGCategoryData A where
  category := dgCategory A
  objects := Equiv.refl _
  hom := fun _ _ _ => LinearEquiv.refl _ _
  differential := by intros; rfl
  composition := by intros; rfl
  identity := by intro X; rfl

attribute [implicit_reducible] dgCategoryData

/-- The differential of `(dgCategoryData A).category` on underlying linear maps is
`d_M ∘ f - (-1)^n (f ∘ d_L)`. -/
@[simp] public theorem dgCategoryData_d_val
    {L M : DifferentialGradedModule.{u, v, w} A} {n : ℤ}
    (f : (dgCategoryData A).category.Hom L M n) :
    ((dgCategoryData A).category.d f).1 =
      M.d ∘ₗ f.1 - DifferentialGraded.gradedSign R n • (f.1 ∘ₗ L.d) := rfl

/-- Composition in `(dgCategoryData A).category` is composition of underlying linear maps. -/
@[simp] public theorem dgCategoryData_comp_val
    {L M N : DifferentialGradedModule.{u, v, w} A}
    {m n k : ℤ} (h : m + n = k)
    (g : (dgCategoryData A).category.Hom M N m)
    (f : (dgCategoryData A).category.Hom L M n) :
    ((dgCategoryData A).category.comp h g f).1 = g.1 ∘ₗ f.1 := rfl

/-- The identity of `(dgCategoryData A).category` is the identity linear map. -/
@[simp] public theorem dgCategoryData_id_val
    (L : DifferentialGradedModule.{u, v, w} A) :
    ((dgCategoryData A).category.id L).1 = LinearMap.id := rfl

end DifferentialGradedModule
