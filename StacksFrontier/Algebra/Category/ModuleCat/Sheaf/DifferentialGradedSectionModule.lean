module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionAlgebra

/-!
# The differential graded modules of sections of a sheaf of differential graded modules

Let `(A, d)` be a sheaf of differential graded algebras on a site, let `M` be a right
differential graded `A`-module and let `U` be an object of the site. The sections of `M` over `U`
form a right differential graded module over the section algebra
`A(U) = SheafOfModules.DifferentialGradedAlgebra.sectionAlgebra A U`: the underlying group is the
direct sum `⨁ n, M^n(U)` of the sections of the homogeneous pieces, the right action of `A(U)` is
the right action of `A` read on sections, and the differential is the differential of `M` read on
sections. The assignment is functorial in `M`, and restriction along a morphism `V ⟶ U` of `Cᵒᵖ`
gives a homomorphism `M(V) ⟶ M(U)` of differential graded `A(V)`-modules, `M(U)` being read
through restriction of scalars along `A(V) ⟶ A(U)`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.sectionModule`: **the differential graded `A(U)`-module
  `M(U)` of sections of `M` over `U`.**
* `SheafOfModules.DifferentialGradedModule.sectionModuleFunctor`: the functor
  `M ↦ M(U)` from right differential graded `A`-modules to right differential graded
  `A(U)`-modules.
* `SheafOfModules.DifferentialGradedModule.sectionModuleRestriction`: the homomorphism
  `M(V) ⟶ M(U)` of differential graded `A(V)`-modules attached to a morphism `V ⟶ U` of `Cᵒᵖ`.

## Main results

* `SheafOfModules.DifferentialGradedModule.act_one` and
  `SheafOfModules.DifferentialGradedModule.act_mul`: the unit and associativity laws of the right
  action on the total sections, which the `HEq`-valued laws of a sheaf of differential graded
  modules give summand by summand.
* `SheafOfModules.DifferentialGradedModule.sectionModule_d_of` and
  `SheafOfModules.DifferentialGradedModule.sectionRModule_smul`: the differential and the action
  of the section module, computed on summands and on total sections respectively.

## Implementation notes

The right action of `A(U)` on `M(U)` is built as the additive map
`⨁ n, M^n(U) →+ (⨁ i, A^i(U) →+ ⨁ n, M^n(U))` obtained from the graded action of `A` by
`DirectSum.toAddMonoid` in each variable, and the module axioms are checked on summands by
`DirectSum.induction_on`. A right module is encoded as a left module over the opposite ring, so
the unit and associativity laws are the laws of the action with the two algebra arguments
exchanged; the degree bookkeeping is absorbed by `SheafOfModules.of_heq`.

The module universe of the sheaf of differential graded modules is taken equal to the module
universe of the sheaf of differential graded algebras: the sections of both have to land in the
universe of the coefficient ring of the section algebra, which the derived category of a
differential graded algebra in the ambient library requires to be the universe of the algebra.

## References

* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory DirectSum

universe t a v u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- An additive map between groups on which `ULift ℤ` acts through its integer value is linear
over `ULift ℤ`. -/
def uliftIntLinear {X Y : Type a} [AddCommGroup X] [AddCommGroup Y] (f : X →+ Y) :
    X →ₗ[ULift.{a, 0} ℤ] Y where
  toFun := f
  map_add' := map_add f
  map_smul' c x := map_zsmul f c.down x

/-- The map `uliftIntLinear f` is `f` on elements. -/
@[simp] theorem uliftIntLinear_apply {X Y : Type a} [AddCommGroup X] [AddCommGroup Y]
    (f : X →+ Y) (x : X) : uliftIntLinear f x = f x := rfl

variable (M : DifferentialGradedModule.{t, a, a} A) (U : Cᵒᵖ)

/-- The sections over `U` of the degree-`n` piece of a right differential graded module. -/
abbrev sectionsPiece (n : ℤ) : Type a := (M.complex.X n).val.obj U

/-- **The group of all local sections over `U`** of a right differential graded module: the
direct sum of the sections of its homogeneous pieces. -/
abbrev totalSections : Type a := DirectSum ℤ (M.sectionsPiece U)

/-! ### The right action of the section algebra -/

/-- The right action of the sections of `A` on a homogeneous section of `M`. -/
def actOn (n : ℤ) (x : M.sectionsPiece U n) :
    A.toGradedAlgebra.totalSections U →+ M.totalSections U :=
  DirectSum.toAddMonoid fun i ↦
    (DirectSum.of (M.sectionsPiece U) (n + i)).comp ((M.mul n i).app U x)

/-- A homogeneous section `x` of degree `n` acted on by a homogeneous section `y` of `A` of
degree `i` is the degree-`n + i` summand given by the right action of `A` on `x` and `y`. -/
@[simp] theorem actOn_of (n i : ℤ) (x : M.sectionsPiece U n)
    (y : A.toGradedAlgebra.sectionsPiece U i) :
    M.actOn U n x (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i y) =
      DirectSum.of (M.sectionsPiece U) (n + i) ((M.mul n i).app U x y) :=
  DirectSum.toAddMonoid_of
    (fun i ↦ (DirectSum.of (M.sectionsPiece U) (n + i)).comp ((M.mul n i).app U x)) i y

/-- The right action on a homogeneous section, as an additive map in that section. -/
def actOnHom (n : ℤ) :
    M.sectionsPiece U n →+ (A.toGradedAlgebra.totalSections U →+ M.totalSections U) :=
  AddMonoidHom.mk' (M.actOn U n) fun x x' ↦
    DirectSum.addHom_ext fun i y ↦ by
      rw [AddMonoidHom.add_apply, actOn_of, actOn_of, actOn_of,
        Stacks.BilinearMap.map_add_left (M.mul n i) U x x' y, map_add]

/-- The map `actOnHom U n` sends a homogeneous section `x` to `actOn U n x`. -/
@[simp] theorem actOnHom_apply (n : ℤ) (x : M.sectionsPiece U n) :
    M.actOnHom U n x = M.actOn U n x := rfl

/-- **The right action of the section algebra `A(U)` on the sections of `M` over `U`**, as an
additive map in each variable. -/
def act : M.totalSections U →+ (A.toGradedAlgebra.totalSections U →+ M.totalSections U) :=
  DirectSum.toAddMonoid (M.actOnHom U)

/-- On the degree-`n` summand, the right action is `actOn U n`. -/
@[simp] theorem act_of (n : ℤ) (x : M.sectionsPiece U n) :
    M.act U (DirectSum.of (M.sectionsPiece U) n x) = M.actOn U n x :=
  DirectSum.toAddMonoid_of (M.actOnHom U) n x

/-- The unit of `A(U)` acts as the identity: this is the unit law of the right action of `A`,
read on sections. -/
theorem act_one (x : M.totalSections U) : M.act U x 1 = x := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, AddMonoidHom.zero_apply]
  | of n p =>
      rw [act_of, ← DirectSum.of_zero_one (A.toGradedAlgebra.sectionsPiece U), actOn_of]
      exact of_heq (add_zero n) (M.mul_one n U p)
  | add x y hx hy => rw [map_add, AddMonoidHom.add_apply, hx, hy]

/-- Acting by a product is acting twice: this is the associativity law of the right action of
`A`, read on sections. The two algebra arguments appear in the order of the right action, which
is the reverse of their order in the opposite ring. -/
theorem act_mul (x : M.totalSections U) (b c : A.toGradedAlgebra.totalSections U) :
    M.act U x (b * c) = M.act U (M.act U x b) c := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  | of n p =>
      induction b using DirectSum.induction_on with
      | zero => simp only [zero_mul, map_zero, AddMonoidHom.zero_apply]
      | add b b' hb hb' =>
          simp only [add_mul, map_add, AddMonoidHom.add_apply, hb, hb']
      | of i y =>
          induction c using DirectSum.induction_on with
          | zero => simp only [mul_zero, map_zero]
          | add c c' hc hc' => simp only [mul_add, map_add, hc, hc']
          | of j z =>
              simp only [GradedAlgebra.of_mul_of_eq, act_of, actOn_of]
              exact (of_heq (add_assoc n i j) (M.mul_assoc n i j U p y z)).symm

/-- **The right action of `A(U)` on the sections of `M` over `U`.** A right module is a left
module over the opposite ring, so the unit and associativity laws are `act_one` and `act_mul`
with the two algebra arguments exchanged. -/
@[instance_reducible]
def sectionRModule :
    Module (MulOpposite (A.sectionAlgebra U).A) (M.totalSections U) where
  smul s x := M.act U x s.unop
  one_smul x := M.act_one U x
  mul_smul s s' x := M.act_mul U x s'.unop s.unop
  smul_zero s := map_zero (AddMonoidHom.flip (M.act U) s.unop)
  smul_add s x y := map_add (AddMonoidHom.flip (M.act U) s.unop) x y
  add_smul s s' x := map_add (M.act U x) s.unop s'.unop
  zero_smul x := map_zero (M.act U x)

attribute [local instance] sectionRModule

/-- The scalar `op s` acts on a section `x` as `act U x s`. -/
@[simp] theorem sectionRModule_smul (s : A.toGradedAlgebra.totalSections U)
    (x : M.totalSections U) :
    (MulOpposite.op s : (A.sectionAlgebra U).Aᵐᵒᵖ) • x = M.act U x s := rfl

/-! ### The differential on the sections -/

/-- The differential of `M` on the sections over `U` of the degree-`n` piece. -/
def sectionDApp (n : ℤ) : M.sectionsPiece U n →+ M.sectionsPiece U (n + 1) :=
  AddMonoidHom.mk' (fun x ↦ (M.complex.d n (n + 1)).val.app U x) fun x y ↦ map_add _ x y

/-- The map `sectionDApp U n` is the component over `U` of the differential `d^n` of `M`. -/
@[simp] theorem sectionDApp_apply (n : ℤ) (x : M.sectionsPiece U n) :
    M.sectionDApp U n x = (M.complex.d n (n + 1)).val.app U x := rfl

/-- The differential of the group of sections: on the degree-`n` summand it is the differential
of `M`, landing in the degree-`n + 1` summand. -/
def sectionD : M.totalSections U →+ M.totalSections U :=
  DirectSum.toAddMonoid fun n ↦
    (DirectSum.of (M.sectionsPiece U) (n + 1)).comp (M.sectionDApp U n)

/-- The differential sends a section of the degree-`n` summand to its image under the
differential of `M`, in the degree-`n + 1` summand. -/
@[simp] theorem sectionD_of (n : ℤ) (x : M.sectionsPiece U n) :
    M.sectionD U (DirectSum.of (M.sectionsPiece U) n x) =
      DirectSum.of (M.sectionsPiece U) (n + 1) (M.sectionDApp U n x) :=
  DirectSum.toAddMonoid_of
    (fun n ↦ (DirectSum.of (M.sectionsPiece U) (n + 1)).comp (M.sectionDApp U n)) n x

/-- The differential of the group of sections squares to zero. -/
theorem sectionD_sectionD (x : M.totalSections U) : M.sectionD U (M.sectionD U x) = 0 := by
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n y =>
      rw [sectionD_of, sectionD_of]
      have h : (M.complex.d n (n + 1) ≫ M.complex.d (n + 1) (n + 1 + 1)) = 0 :=
        M.complex.d_comp_d _ _ _
      have h₂ : M.sectionDApp U (n + 1) (M.sectionDApp U n y) = 0 := by
        change (M.complex.d (n + 1) (n + 1 + 1)).val.app U
          ((M.complex.d n (n + 1)).val.app U y) = 0
        rw [← comp_val_app_apply, h, zero_val_app_apply]
      rw [h₂, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/-! ### The differential graded module of sections -/

/-- **The differential graded `A(U)`-module of sections over `U` of a right differential graded
`A`-module.** Its underlying group is the direct sum of the sections of the homogeneous pieces,
its grading is by the summands of that direct sum, its right action is the right action of `A`
read on sections, and its differential is the differential of `M` read on sections. -/
def sectionModule : _root_.DifferentialGradedModule.{a, a, a} (A.sectionAlgebra U) where
  M := M.totalSections U
  rmodule := M.sectionRModule U
  isScalarTower := by
    refine IsScalarTower.mk fun r s x ↦ ?_
    change M.act U x (r • s).unop = r • M.act U x s.unop
    exact map_zsmul (M.act U x) r.down s.unop
  grading := Stacks.ExternalGrading.intSummand (M.sectionsPiece U)
  smul_mem := by
    rintro n i x y ⟨p, rfl⟩ ⟨q, rfl⟩
    change M.act U (DirectSum.of (M.sectionsPiece U) n p)
        (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i q) ∈
      Stacks.ExternalGrading.intSummand (M.sectionsPiece U) (n + i)
    rw [act_of, actOn_of]
    exact Stacks.ExternalGrading.of_mem_intSummand _ (n + i) _
  d := uliftIntLinear (M.sectionD U)
  d_comp_d := LinearMap.ext fun x ↦ M.sectionD_sectionD U x
  d_mem := by
    rintro n x ⟨p, rfl⟩
    change M.sectionD U (DirectSum.of (M.sectionsPiece U) n p) ∈
      Stacks.ExternalGrading.intSummand (M.sectionsPiece U) (n + 1)
    rw [sectionD_of]
    exact Stacks.ExternalGrading.of_mem_intSummand _ (n + 1) _
  leibniz := by
    rintro n i x y ⟨p, rfl⟩ ⟨q, rfl⟩
    change M.sectionD U (M.act U (DirectSum.of (M.sectionsPiece U) n p)
          (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i q)) =
        M.act U (M.sectionD U (DirectSum.of (M.sectionsPiece U) n p))
          (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i q) +
      (n.negOnePow : ℤ) • M.act U (DirectSum.of (M.sectionsPiece U) n p)
        (A.sectionD U (DirectSum.of (A.toGradedAlgebra.sectionsPiece U) i q))
    rw [A.sectionD_of U i q]
    simp only [act_of, actOn_of, sectionD_of, sectionDApp_apply]
    rw [M.leibniz n i U p q, map_add, of_gradedCast, map_zsmul, of_gradedCast]

/-- The underlying group of the section module is the group of total sections. -/
theorem sectionModule_M : (M.sectionModule U).M = M.totalSections U := rfl

/-- The differential of the section module sends a section of the degree-`n` summand to its
image under the differential of `M`, in the degree-`n + 1` summand. -/
theorem sectionModule_d_of (n : ℤ) (x : M.sectionsPiece U n) :
    (M.sectionModule U).d (DirectSum.of (M.sectionsPiece U) n x) =
      DirectSum.of (M.sectionsPiece U) (n + 1) (M.sectionDApp U n x) :=
  M.sectionD_of U n x

/-- The degree-`n` part of the section module is the degree-`n` summand of the total sections. -/
theorem sectionModule_grading (n : ℤ) :
    (M.sectionModule U).grading n = Stacks.ExternalGrading.intSummand (M.sectionsPiece U) n :=
  rfl

/-! ### Functoriality in the differential graded module -/

section Functoriality

variable {M N P : DifferentialGradedModule.{t, a, a} A}

/-- The map on sections of the degree-`n` piece induced by a homomorphism of right differential
graded modules. -/
def sectionMapApp (f : M ⟶ N) (U : Cᵒᵖ) (n : ℤ) :
    M.sectionsPiece U n →+ N.sectionsPiece U n :=
  AddMonoidHom.mk' (fun x ↦ (f.toHomologicalComplex.f n).val.app U x) fun x y ↦ map_add _ x y

/-- The map `sectionMapApp f U n` is the component over `U` of the degree-`n` part of `f`. -/
theorem sectionMapApp_apply (f : M ⟶ N) (U : Cᵒᵖ) (n : ℤ) (x : M.sectionsPiece U n) :
    sectionMapApp f U n x = (f.toHomologicalComplex.f n).val.app U x := rfl

/-- The map on total sections induced by a homomorphism of right differential graded modules. -/
def sectionMapAdd (f : M ⟶ N) (U : Cᵒᵖ) : M.totalSections U →+ N.totalSections U :=
  DirectSum.map (sectionMapApp f U)

/-- On the degree-`n` summand, the map on total sections induced by `f` is
`sectionMapApp f U n`. -/
@[simp] theorem sectionMapAdd_of (f : M ⟶ N) (U : Cᵒᵖ) (n : ℤ) (x : M.sectionsPiece U n) :
    sectionMapAdd f U (DirectSum.of (M.sectionsPiece U) n x) =
      DirectSum.of (N.sectionsPiece U) n (sectionMapApp f U n x) :=
  DirectSum.map_of (sectionMapApp f U) n x

/-- The map on total sections induced by `f` commutes with the right action of `A(U)`. -/
theorem sectionMapAdd_act (f : M ⟶ N) (U : Cᵒᵖ) (x : M.totalSections U)
    (s : A.toGradedAlgebra.totalSections U) :
    sectionMapAdd f U (M.act U x s) = N.act U (sectionMapAdd f U x) s := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  | of n p =>
      induction s using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | add s s' hs hs' => simp only [map_add, hs, hs']
      | of i q =>
          simp only [act_of, actOn_of, sectionMapAdd_of]
          exact congrArg (DirectSum.of (N.sectionsPiece U) (n + i)) (f.map_mul n i U p q)

/-- The map on total sections induced by `f` commutes with the differentials. -/
theorem sectionMapAdd_sectionD (f : M ⟶ N) (U : Cᵒᵖ) (x : M.totalSections U) :
    sectionMapAdd f U (M.sectionD U x) = N.sectionD U (sectionMapAdd f U x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n p =>
      simp only [sectionD_of, sectionMapAdd_of]
      refine congrArg (DirectSum.of (N.sectionsPiece U) (n + 1)) ?_
      change (f.toHomologicalComplex.f (n + 1)).val.app U
          ((M.complex.d n (n + 1)).val.app U p) =
        (N.complex.d n (n + 1)).val.app U ((f.toHomologicalComplex.f n).val.app U p)
      rw [← comp_val_app_apply, ← comp_val_app_apply,
        f.toHomologicalComplex.comm n (n + 1)]

/-- **The homomorphism of section modules induced by a homomorphism of right differential graded
`A`-modules.** -/
def sectionMap (f : M ⟶ N) (U : Cᵒᵖ) : M.sectionModule U ⟶ N.sectionModule U where
  toFun := uliftIntLinear (sectionMapAdd f U)
  map_smul x s := sectionMapAdd_act f U x s
  map_grading := by
    rintro n x ⟨p, rfl⟩
    change sectionMapAdd f U (DirectSum.of (M.sectionsPiece U) n p) ∈
      Stacks.ExternalGrading.intSummand (N.sectionsPiece U) n
    rw [sectionMapAdd_of]
    exact Stacks.ExternalGrading.of_mem_intSummand _ n _
  map_d := LinearMap.ext fun x ↦ sectionMapAdd_sectionD f U x

/-- The underlying map of `sectionMap f U` is the map on total sections induced by `f`. -/
@[simp] theorem sectionMap_toFun (f : M ⟶ N) (U : Cᵒᵖ) (x : M.totalSections U) :
    (sectionMap f U).toFun x = sectionMapAdd f U x := rfl

/-- **Taking sections over `U` is a functor** from right differential graded `A`-modules to
right differential graded `A(U)`-modules. -/
def sectionModuleFunctor (A : DifferentialGradedAlgebra.{t, a} R) (U : Cᵒᵖ) :
    DifferentialGradedModule.{t, a, a} A ⥤
      _root_.DifferentialGradedModule.{a, a, a} (A.sectionAlgebra U) where
  obj M := M.sectionModule U
  map f := sectionMap f U
  map_id M := by
    refine _root_.DifferentialGradedModule.Hom.ext (LinearMap.ext fun x ↦ ?_)
    change sectionMapAdd (𝟙 M) U x = x
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => rw [map_add, hx, hy]
    | of n p => rw [sectionMapAdd_of]; rfl
  map_comp f g := by
    refine _root_.DifferentialGradedModule.Hom.ext (LinearMap.ext fun x ↦ ?_)
    change sectionMapAdd (f ≫ g) U x = sectionMapAdd g U (sectionMapAdd f U x)
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | of n p => rw [sectionMapAdd_of, sectionMapAdd_of, sectionMapAdd_of]; rfl

/-- The section functor sends `M` to its section module `M(U)`. -/
@[simp] theorem sectionModuleFunctor_obj (U : Cᵒᵖ) (M : DifferentialGradedModule.{t, a, a} A) :
    (sectionModuleFunctor A U).obj M = M.sectionModule U := rfl

/-- The section functor sends `f` to the induced homomorphism `sectionMap f U`. -/
@[simp] theorem sectionModuleFunctor_map (U : Cᵒᵖ) (f : M ⟶ N) :
    (sectionModuleFunctor A U).map f = sectionMap f U := rfl

end Functoriality

/-! ### Restriction of sections along a morphism of the site -/

section Restriction

variable {U V : Cᵒᵖ}

/-- Restriction of sections of the degree-`n` piece of a right differential graded module. -/
def sectionRestrictApp (M : DifferentialGradedModule.{t, a, a} A) (a : V ⟶ U) (n : ℤ) :
    M.sectionsPiece V n →+ M.sectionsPiece U n :=
  AddMonoidHom.mk' (fun x ↦ (M.complex.X n).val.map a x) fun x y ↦ map_add _ x y

/-- The map `sectionRestrictApp a n` is the restriction map along `a` of the degree-`n` piece. -/
theorem sectionRestrictApp_apply (M : DifferentialGradedModule.{t, a, a} A) (a : V ⟶ U) (n : ℤ)
    (x : M.sectionsPiece V n) :
    M.sectionRestrictApp a n x = (M.complex.X n).val.map a x := rfl

/-- Restriction of the total sections along a morphism of `Cᵒᵖ`. -/
def sectionRestrictAdd (M : DifferentialGradedModule.{t, a, a} A) (a : V ⟶ U) :
    M.totalSections V →+ M.totalSections U :=
  DirectSum.map (M.sectionRestrictApp a)

/-- On the degree-`n` summand, restriction of total sections is `sectionRestrictApp a n`. -/
@[simp] theorem sectionRestrictAdd_of (M : DifferentialGradedModule.{t, a, a} A) (a : V ⟶ U)
    (n : ℤ) (x : M.sectionsPiece V n) :
    M.sectionRestrictAdd a (DirectSum.of (M.sectionsPiece V) n x) =
      DirectSum.of (M.sectionsPiece U) n (M.sectionRestrictApp a n x) :=
  DirectSum.map_of (M.sectionRestrictApp a) n x

/-- Restriction of sections is compatible with the right action: the right action of `A` is
natural in the object of the site, so restricting a product is the product of the
restrictions. -/
theorem sectionRestrictAdd_act (M : DifferentialGradedModule.{t, a, a} A) (a : V ⟶ U)
    (x : M.totalSections V) (s : A.toGradedAlgebra.totalSections V) :
    M.sectionRestrictAdd a (M.act V x s) =
      M.act U (M.sectionRestrictAdd a x) (A.sectionRestrictRing a s) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  | of n p =>
      induction s using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | add s s' hs hs' => simp only [map_add, hs, hs']
      | of i q =>
          simp only [act_of, actOn_of, sectionRestrictAdd_of,
            DifferentialGradedAlgebra.sectionRestrictRing_of]
          exact congrArg (DirectSum.of (M.sectionsPiece U) (n + i)) ((M.mul n i).naturality a p q)

/-- Restriction of sections commutes with the differential of `M`. -/
theorem sectionRestrictAdd_sectionD (M : DifferentialGradedModule.{t, a, a} A) (a : V ⟶ U)
    (x : M.totalSections V) :
    M.sectionRestrictAdd a (M.sectionD V x) = M.sectionD U (M.sectionRestrictAdd a x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n p =>
      simp only [sectionD_of, sectionRestrictAdd_of]
      exact congrArg (DirectSum.of (M.sectionsPiece U) (n + 1))
        (PresheafOfModules.naturality_apply (M.complex.d n (n + 1)).val a p).symm

/-- **Restriction of sections is natural in the differential graded module.** Restricting the
sections of `M` and then applying a homomorphism `f : M ⟶ N` is applying `f` and then
restricting: each side is, summandwise, the naturality square of the component of `f` in that
degree against the restriction maps of the two complexes. -/
theorem sectionRestrictAdd_sectionMapAdd {M N : DifferentialGradedModule.{t, a, a} A}
    (f : M ⟶ N) (a : V ⟶ U) (x : M.totalSections V) :
    N.sectionRestrictAdd a (sectionMapAdd f V x) =
      sectionMapAdd f U (M.sectionRestrictAdd a x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n p =>
      rw [sectionMapAdd_of, sectionRestrictAdd_of, sectionRestrictAdd_of, sectionMapAdd_of]
      simp only [sectionMapApp_apply, sectionRestrictApp_apply]
      exact congrArg (DirectSum.of (N.sectionsPiece U) n)
        (PresheafOfModules.naturality_apply (f.toHomologicalComplex.f n).val a p).symm

/-- **Restriction of sections, as a homomorphism of differential graded `A(V)`-modules**
`M(V) ⟶ M(U)`, the target being read through restriction of scalars along the restriction
homomorphism `A(V) ⟶ A(U)`. -/
def sectionModuleRestriction (M : DifferentialGradedModule.{t, a, a} A) (a : V ⟶ U) :
    M.sectionModule V ⟶
      _root_.DifferentialGradedModule.restrictScalars (A.sectionRestriction a)
        (M.sectionModule U) where
  toFun := uliftIntLinear (M.sectionRestrictAdd a)
  map_smul x s := M.sectionRestrictAdd_act a x s
  map_grading := by
    rintro n x ⟨p, rfl⟩
    change M.sectionRestrictAdd a (DirectSum.of (M.sectionsPiece V) n p) ∈
      Stacks.ExternalGrading.intSummand (M.sectionsPiece U) n
    rw [sectionRestrictAdd_of]
    exact Stacks.ExternalGrading.of_mem_intSummand _ n _
  map_d := LinearMap.ext fun x ↦ M.sectionRestrictAdd_sectionD a x

/-- The underlying map of `sectionModuleRestriction a` is restriction of total sections
along `a`. -/
@[simp] theorem sectionModuleRestriction_toFun (M : DifferentialGradedModule.{t, a, a} A)
    (a : V ⟶ U) (x : M.totalSections V) :
    (M.sectionModuleRestriction a).toFun x = M.sectionRestrictAdd a x := rfl

end Restriction

end DifferentialGradedModule

end SheafOfModules

end
