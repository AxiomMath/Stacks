module

public import Mathlib.Algebra.Module.GradedModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite
public import StacksCore.Tactic.StacksAttribute

/-!
# The total module of a graded module, over the ungraded realization of the algebra

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of graded `R`-algebras and let `M` be a
graded `A`-module. `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization` turns `A`
into an ungraded sheaf of rings `SheafOfModules.GradedAlgebra.ungradedSheaf`, the sheafification
of the objectwise direct sum `⨁ᵢ Aᵢ`. This file does the same for `M`: the *total module*
`⨁ₙ Mₙ`, as a sheaf of modules over that ungraded sheaf of rings.

## Main definitions

* `Stacks.GradedModule` is a right graded module over `Stacks.GradedAlgebra`: the presheaf-level,
  arbitrary-index form of `SheafOfModules.GradedModule`, exactly as `Stacks.GradedAlgebra` is the
  presheaf-level form of `SheafOfModules.GradedAlgebra`.
* `Stacks.GradedAlgebra.IsCommutative` says that homogeneous sections of the algebra commute.
* `Stacks.GradedModule.Total` is the module of sections of the total module over an object of the
  site, and `Stacks.GradedModule.incl` views a homogeneous section in it.
* `Stacks.GradedModule.gmodule` is the `DirectSum.Gmodule` structure the graded data induces on
  the homogeneous components over a fixed object of the site, and
  `Stacks.GradedModule.moduleTotal` the resulting module structure over
  `Stacks.GradedAlgebra.Total`.
* `Stacks.GradedModule.totalPresheafMod` is the total module as a presheaf of modules over the
  ungraded realization `Stacks.GradedAlgebra.totalPresheaf`.
* `Stacks.GradedModule.TotalDescData` and `Stacks.GradedModule.totalDesc` are the universal
  property of the total module: a morphism out of it is a family of additive maps on the
  homogeneous pieces, compatible with restriction and with the action.
* `SheafOfModules.GradedModule.toPresheafGradedModule` reads a graded module over a sheaf of
  graded algebras as one of these, and `SheafOfModules.GradedModule.ungradedSheaf` is the total
  module of a graded module over a sheaf of graded algebras, as a sheaf of modules over
  `SheafOfModules.GradedAlgebra.ungradedSheaf`, with sheafification unit
  `SheafOfModules.GradedModule.toUngradedSheaf`, degreewise inclusions
  `SheafOfModules.GradedModule.ungradedIncl` and lift
  `SheafOfModules.GradedModule.ungradedSheafLift`.

## Main results

* `Stacks.GradedModule.incl_smul_incl`: the action of the ungraded realization on the total module
  agrees with the graded action on homogeneous local sections.
* `Stacks.GradedModule.structureMap_smul`: the module structure of the total module over the base
  ring is the one induced along the structure map of the ungraded realization.
* `Stacks.GradedModule.totalDesc_incl` and `Stacks.GradedModule.totalMod_hom_ext`: the universal
  property, in its existence and its uniqueness half.
* `Stacks.GradedModule.generates_totalPresheafMod`: finite type passes from the graded module to
  the total module. If finitely many homogeneous sections generate every homogeneous section
  locally over the ungraded realization, then they generate the total module in the sense of
  `PresheafOfModules.Generates`; `Stacks.GradedModule.isFiniteType_totalPresheafMod` is the
  resulting statement about `PresheafOfModules.IsFiniteType`.
* `SheafOfModules.GradedModule.ungradedSheafHomEquiv`: the universal property at the sheaf
  level — morphisms of sheaves of modules out of the total module are the morphisms of
  presheaves of modules out of the presheaf total module — and
  `SheafOfModules.GradedModule.ungradedSheafHomEquiv_ungradedSheafLift`, which says that the lift
  restricts along the unit to the morphism it was built from.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite DirectSum

universe v u t w

namespace Stacks

/-! ### Reading a right action as a left one -/

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}} {ι : Type} [DecidableEq ι]

/-- The index action under which a right graded module is read as a left module over the ungraded
realization: the degree of `a • m` is the degree of `m` plus the degree of `a`. -/
@[reducible] def rightVAdd (ι : Type) [Add ι] : VAdd ι ι := ⟨fun i n => n + i⟩

attribute [local instance 100000] rightVAdd

section GradedCommutative

variable [AddCommMonoid ι] {P : ι → PresheafOfModules.{w} R}

/-- Commutativity of a graded algebra of presheaves of modules: the product of two homogeneous
local sections does not depend on the order of the factors. The two sides live in pieces of
propositionally equal degrees, so the equality is heterogeneous. Commutativity is strict, with no
Koszul sign. -/
class GradedAlgebra.IsCommutative (A : GradedAlgebra P) : Prop where
  /-- Homogeneous local sections commute. -/
  mul_comm (i j : ι) (X : Cᵒᵖ) (x : (P i).obj X) (y : (P j).obj X) :
    HEq ((A.mul i j).app X x y) ((A.mul j i).app X y x)

/-- The sections of a presheaf of modules over the ungraded realization, as a module over
`Stacks.GradedAlgebra.Total`. -/
noncomputable instance moduleTotalSections (A : GradedAlgebra P)
    (T : PresheafOfModules.{w} A.totalPresheaf) (X : Cᵒᵖ) :
    Module (A.Total X) (T.obj X : Type w) :=
  inferInstanceAs (Module (A.totalPresheaf.obj X) (T.obj X : Type w))

/-! ### Graded modules of presheaves of modules -/

/-- A right `ι`-graded module over a graded algebra of presheaves of modules: a family `Q` of
presheaves of modules with a restriction-compatible, `R`-bilinear action
`Q n × P i ⟶ Q (n + i)` which is associative and unital.

This is the presheaf-level, arbitrary-index form of `SheafOfModules.GradedModule`. The
associativity and unit laws are heterogeneous equalities because the two sides of each live in
pieces whose degrees are propositionally but not definitionally equal. -/
structure GradedModule (A : GradedAlgebra P) (Q : ι → PresheafOfModules.{w} R) where
  /-- Multiplication of a homogeneous module section by a homogeneous algebra section. -/
  smul (n i : ι) (X : Cᵒᵖ) : (Q n).obj X →+ (P i).obj X →+ (Q (n + i)).obj X
  /-- The action is linear over the base ring in the module variable. -/
  smul_smul_left (n i : ι) (X : Cᵒᵖ) (r : R.obj X) (x : (Q n).obj X) (y : (P i).obj X) :
    smul n i X (r • x) y = r • smul n i X x y
  /-- The action is linear over the base ring in the algebra variable. -/
  smul_smul_right (n i : ι) (X : Cᵒᵖ) (r : R.obj X) (x : (Q n).obj X) (y : (P i).obj X) :
    smul n i X x (r • y) = r • smul n i X x y
  /-- The action commutes with restriction. -/
  smul_naturality (n i : ι) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (Q n).obj X) (y : (P i).obj X) :
    sectionRestrict (Q (n + i)) f (smul n i X x y) =
      smul n i Y (sectionRestrict (Q n) f x) (sectionRestrict (P i) f y)
  /-- The action is associative. -/
  smul_mul (n i j : ι) (X : Cᵒᵖ) (x : (Q n).obj X) (y : (P i).obj X) (z : (P j).obj X) :
    HEq (smul (n + i) j X (smul n i X x y) z) (smul n (i + j) X x ((A.mul i j).app X y z))
  /-- The unit of the algebra acts as the identity. -/
  smul_one (n : ι) (X : Cᵒᵖ) (x : (Q n).obj X) : HEq (smul n 0 X x (A.one.eval X)) x

namespace GradedModule

variable {A : GradedAlgebra P} {Q : ι → PresheafOfModules.{w} R} (M : GradedModule A Q)

/-- The graded scalar multiplication of the homogeneous components over an object of the site,
with the algebra acting on the left through `Stacks.rightVAdd`. -/
@[instance_reducible]
def gsmul (X : Cᵒᵖ) :
    GradedMonoid.GSMul (fun i => ((P i).obj X : Type w)) (fun n => ((Q n).obj X : Type w)) :=
  ⟨fun {i n} y x => M.smul n i X x y⟩

omit [DecidableEq ι] in
/-- Transport of the action along an equality of algebra degrees. -/
theorem heq_smul_congr {n i j : ι} (e : i = j) (X : Cᵒᵖ) (x : (Q n).obj X) {y : (P i).obj X}
    {z : (P j).obj X} (h : HEq y z) : HEq (M.smul n i X x y) (M.smul n j X x z) := by
  subst e
  rw [eq_of_heq h]

/-- The `DirectSum.Gmodule` structure carried by the homogeneous components over a fixed object
of the site, for a commutative graded algebra. -/
@[instance_reducible]
def gmodule [A.IsCommutative] (X : Cᵒᵖ) :
    letI := A.gring X
    DirectSum.Gmodule (fun i => ((P i).obj X : Type w)) (fun n => ((Q n).obj X : Type w)) :=
  letI _gr := A.gring X
  letI _gs := M.gsmul X
  { _gs with
    one_smul := fun b => Sigma.ext (add_zero b.1) (M.smul_one b.1 X b.2)
    mul_smul := fun a a' b =>
      Sigma.ext (by
          change b.1 + (a.1 + a'.1) = b.1 + a'.1 + a.1
          rw [add_comm a.1 a'.1, add_assoc])
        (HEq.trans
          (M.heq_smul_congr (add_comm a.1 a'.1) X b.2
            (GradedAlgebra.IsCommutative.mul_comm a.1 a'.1 X a.2 a'.2))
          (M.smul_mul b.1 a'.1 a.1 X b.2 a'.2 a.2).symm)
    smul_add := fun {i j} a y z => map_add ((M.smul j i X).flip a) y z
    smul_zero := fun {i j} a => map_zero ((M.smul j i X).flip a)
    add_smul := fun {i j} a a' y => map_add (M.smul j i X y) a a'
    zero_smul := fun {i j} y => map_zero (M.smul j i X y) }

/-- The sections of the total module over an object of the site: the direct sum of the
homogeneous components, as a type synonym carrying the module structure over the ungraded
realization. -/
def Total (_M : GradedModule A Q) (X : Cᵒᵖ) : Type w := DirectSumType Q X

/-- The sections of the total module form an additive commutative group. -/
noncomputable instance (X : Cᵒᵖ) : AddCommGroup (M.Total X) :=
  inferInstanceAs (AddCommGroup (DirectSumType Q X))

/-- The sections of the total module form a module over the base ring. -/
noncomputable instance (X : Cᵒᵖ) : Module (R.obj X) (M.Total X) :=
  inferInstanceAs (Module (R.obj X) (DirectSumType Q X))

/-- The total module is a module over the ungraded realization of the algebra. -/
noncomputable instance moduleTotal [A.IsCommutative] (X : Cᵒᵖ) :
    Module (A.Total X) (M.Total X) :=
  letI _gr := A.gring X
  letI _gm := M.gmodule X
  inferInstanceAs (Module (DirectSum ι fun i => ((P i).obj X : Type w))
    (DirectSum ι fun n => ((Q n).obj X : Type w)))

/-! ### Homogeneous sections of the total module -/

/-- A homogeneous local section, viewed in the total module. -/
def incl {X : Cᵒᵖ} (n : ι) (x : (Q n).obj X) : M.Total X := DirectSum.of _ n x

/-- The zero homogeneous section is zero in the total module. -/
@[simp]
lemma incl_zero {X : Cᵒᵖ} (n : ι) : M.incl n (0 : (Q n).obj X) = 0 := map_zero _

/-- The inclusion of a homogeneous component into the total module is additive. -/
@[simp]
lemma incl_add {X : Cᵒᵖ} (n : ι) (x y : (Q n).obj X) :
    M.incl n (x + y) = M.incl n x + M.incl n y := map_add _ x y

/-- The inclusion of a homogeneous component into the total module is linear over the base
ring. -/
lemma incl_smul {X : Cᵒᵖ} (n : ι) (r : R.obj X) (x : (Q n).obj X) :
    M.incl n (r • x) = r • M.incl n x := DirectSum.of_smul _ _ _ _

/-- Every section of the total module is a finite sum of homogeneous ones. -/
lemma incl_induction {X : Cᵒᵖ} {motive : M.Total X → Prop} (m : M.Total X) (zero : motive 0)
    (incl : ∀ (n : ι) (x : (Q n).obj X), motive (M.incl n x))
    (add : ∀ m m', motive m → motive m' → motive (m + m')) : motive m :=
  DirectSum.induction_on (β := fun n => ((Q n).obj X : Type w)) m zero incl add

/-- Induction on a pair of sections, one of the ungraded realization and one of the total module,
reducing to homogeneous ones. -/
private theorem smul_induction {X : Cᵒᵖ} {motive : A.Total X → M.Total X → Prop}
    (a : A.Total X) (m : M.Total X) (zero_left : ∀ m, motive 0 m) (zero_right : ∀ a, motive a 0)
    (add_left : ∀ a a' m, motive a m → motive a' m → motive (a + a') m)
    (add_right : ∀ a m m', motive a m → motive a m' → motive a (m + m'))
    (incl : ∀ (i : ι) (y : (P i).obj X) (n : ι) (x : (Q n).obj X),
      motive (A.incl i y) (M.incl n x)) : motive a m := by
  induction a using A.incl_induction with
  | zero => exact zero_left m
  | incl i y =>
    induction m using M.incl_induction with
    | zero => exact zero_right _
    | incl n x => exact incl i y n x
    | add m m' hm hm' => exact add_right _ _ _ hm hm'
  | add a a' ha ha' => exact add_left _ _ _ ha ha'

variable [A.IsCommutative]

/-- The action of the ungraded realization on the total module agrees with the graded action on
homogeneous local sections. -/
lemma incl_smul_incl {X : Cᵒᵖ} (i n : ι) (y : (P i).obj X) (x : (Q n).obj X) :
    A.incl i y • M.incl n x = M.incl (n + i) (M.smul n i X x y) := by
  let _gr := A.gring X
  let _gm := M.gmodule (A := A) (Q := Q) X
  change (DirectSum.of (fun k => ((P k).obj X : Type w)) i y) •
      (DirectSum.of (fun k => ((Q k).obj X : Type w)) n x) = _
  rw [DirectSum.Gmodule.of_smul_of]
  rfl

/-- The two scalar actions on the total module are compatible: the base ring acts through the
ungraded realization. -/
lemma smul_smul_eq {X : Cᵒᵖ} (r : R.obj X) (a : A.Total X) (m : M.Total X) :
    (r • a) • m = r • (a • m) := by
  induction a, m using M.smul_induction with
  | incl i y n x =>
    rw [← A.incl_smul, M.incl_smul_incl, M.incl_smul_incl, M.smul_smul_right, M.incl_smul]
  | _ => simp [add_smul, *]

/-! ### The total module as a presheaf of modules over the ungraded realization -/

/-- Restriction of sections of the total module, as an additive map. -/
noncomputable def totalRestrict {X Y : Cᵒᵖ} (f : X ⟶ Y) : M.Total X →+ M.Total Y :=
  directSumRestrict Q f

omit [A.IsCommutative] in
/-- Restriction of a homogeneous section of the total module is the homogeneous section given by
its restriction. -/
@[simp]
lemma totalRestrict_incl {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ι) (x : (Q n).obj X) :
    M.totalRestrict f (M.incl n x) = M.incl n (sectionRestrict (Q n) f x) :=
  directSumRestrict_of Q f n x

omit [A.IsCommutative] in
/-- Restriction of sections of the total module is semilinear over the restriction of the base
ring. -/
lemma totalRestrict_smul_base {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (m : M.Total X) :
    M.totalRestrict f (r • m) = R.map f r • M.totalRestrict f m :=
  directSumRestrict_smul Q f r m

/-- Restriction of sections of the total module is semilinear over the restriction of the
ungraded realization. -/
lemma totalRestrict_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (a : A.Total X) (m : M.Total X) :
    M.totalRestrict f (a • m) = A.totalRestrict f a • M.totalRestrict f m := by
  induction a, m using M.smul_induction with
  | incl i y n x =>
    rw [M.incl_smul_incl, M.totalRestrict_incl, A.totalRestrict_incl, M.totalRestrict_incl,
      M.incl_smul_incl, M.smul_naturality]
  | _ => simp [add_smul, *]

/-- The total module `⨁ₙ Mₙ` of a graded module, as a presheaf of modules over the ungraded
realization of the algebra: over each object of the site its sections are the direct sum of the
homogeneous components, acted on by the ungraded realization through the graded action. -/
noncomputable def totalPresheafMod : PresheafOfModules.{w} A.totalPresheaf :=
  @PresheafOfModules.ofPresheaf C _ A.totalPresheaf (directSumAb Q)
    (fun X => inferInstanceAs (Module (A.Total X) (M.Total X)))
    (fun _ _ f a m => M.totalRestrict_smul f a m)

/-- The restriction maps of `totalPresheafMod` are given by `totalRestrict`. -/
lemma totalPresheafMod_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.Total X) :
    M.totalPresheafMod.map f m = M.totalRestrict f m := rfl

/-- Restriction of sections of `totalPresheafMod` is given by `totalRestrict`. -/
lemma sectionRestrict_totalPresheafMod {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.Total X) :
    sectionRestrict M.totalPresheafMod f m = M.totalRestrict f m := rfl

/-! ### The universal property -/

/-- The datum determining a morphism out of the total module: a family of additive maps on the
homogeneous pieces, compatible with restriction and with the action of the algebra. -/
structure TotalDescData (M : GradedModule A Q) (T : PresheafOfModules.{w} A.totalPresheaf) where
  /-- The map on the degree-`n` piece. -/
  app (n : ι) (X : Cᵒᵖ) : (Q n).obj X →+ (T.obj X : Type w)
  /-- Compatibility with restriction. -/
  naturality (n : ι) {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : (Q n).obj X) :
    sectionRestrict T f (app n X x) = app n Y (sectionRestrict (Q n) f x)
  /-- Compatibility with the action of the algebra. -/
  map_smul (n i : ι) (X : Cᵒᵖ) (x : (Q n).obj X) (y : (P i).obj X) :
    app (n + i) X (M.smul n i X x y) = A.incl i y • app n X x

variable {T : PresheafOfModules.{w} A.totalPresheaf}

/-- The additive map out of the sections of the total module assembled from a `TotalDescData`. -/
noncomputable def descAddHom (d : M.TotalDescData T) (X : Cᵒᵖ) :
    M.Total X →+ (T.obj X : Type w) :=
  DirectSum.toAddMonoid fun n => d.app n X

omit [A.IsCommutative] in
/-- On a homogeneous section of degree `n`, `descAddHom` is the degree-`n` map of the datum. -/
@[simp]
lemma descAddHom_incl (d : M.TotalDescData T) (X : Cᵒᵖ) (n : ι) (x : (Q n).obj X) :
    M.descAddHom d X (M.incl n x) = d.app n X x := by
  change DirectSum.toAddMonoid (fun k => d.app k X) (DirectSum.of _ n x) = _
  rw [DirectSum.toAddMonoid_of]

/-- The map `descAddHom` is linear over the ungraded realization of the algebra. -/
lemma descAddHom_smul (d : M.TotalDescData T) (X : Cᵒᵖ) (a : A.Total X) (m : M.Total X) :
    M.descAddHom d X (a • m) = a • M.descAddHom d X m := by
  induction a, m using M.smul_induction with
  | incl i y n x => rw [M.incl_smul_incl, M.descAddHom_incl, M.descAddHom_incl, d.map_smul]
  | _ => simp [add_smul, *]

omit [A.IsCommutative] in
/-- The maps `descAddHom` commute with restriction of sections. -/
lemma descAddHom_naturality (d : M.TotalDescData T) {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.Total X) :
    M.descAddHom d Y (M.totalRestrict f m) = sectionRestrict T f (M.descAddHom d X m) := by
  induction m using M.incl_induction with
  | zero => simp
  | incl n x => rw [M.totalRestrict_incl, M.descAddHom_incl, M.descAddHom_incl, d.naturality]
  | add m m' hm hm' => simp only [map_add, hm, hm']

/-- The morphism out of the total module determined by a family of additive maps on the
homogeneous pieces compatible with restriction and with the action. -/
noncomputable def totalDesc (d : M.TotalDescData T) : M.totalPresheafMod ⟶ T :=
  letI : ∀ X : Cᵒᵖ, Module (A.totalPresheaf.obj X) ((directSumAb Q).obj X) :=
    fun X => inferInstanceAs (Module (A.Total X) (M.Total X))
  { app := fun X => ModuleCat.ofHom
      { toFun := fun m => M.descAddHom d X m
        map_add' := fun m m' => map_add (M.descAddHom d X) m m'
        map_smul' := fun a m => M.descAddHom_smul d X a m }
    naturality := fun {X Y} f => by
      refine ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
      exact M.descAddHom_naturality d f m }

/-- On a homogeneous section of degree `n`, `totalDesc` is the degree-`n` map of the datum. -/
@[simp]
lemma totalDesc_incl (d : M.TotalDescData T) (X : Cᵒᵖ) (n : ι) (x : (Q n).obj X) :
    (M.totalDesc d).app X (M.incl n x) = d.app n X x :=
  M.descAddHom_incl d X n x

/-- A morphism out of the sections of the total module, as an additive map whose source type is
written as a direct sum. -/
noncomputable def homAddHom (h : M.totalPresheafMod ⟶ T) (X : Cᵒᵖ) :
    M.Total X →+ (T.obj X : Type w) :=
  AddMonoidHom.mk' (fun m => h.app X m) (fun m m' => map_add (h.app X).hom m m')

/-- Two morphisms out of the total module agreeing on homogeneous sections are equal. -/
lemma totalMod_hom_ext {h h' : M.totalPresheafMod ⟶ T}
    (hh : ∀ (n : ι) (X : Cᵒᵖ) (x : (Q n).obj X),
      (h.app X) (M.incl n x) = (h'.app X) (M.incl n x)) : h = h' := by
  refine PresheafOfModules.hom_ext fun X => ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  exact DFunLike.congr_fun (DirectSum.addHom_ext (f := M.homAddHom h X) (g := M.homAddHom h' X)
    fun n x => hh n X x) m

/-! ### Finite type -/

section FiniteType

variable (J : GrothendieckTopology C)

/-- Generation of a graded module by finitely many homogeneous local sections of degrees `d` over
an object `U` of the site: every *homogeneous* section over an object above `U` is locally a
combination of the restrictions of the family, with coefficients in the ungraded realization. -/
def GeneratesHomogeneous {U : C} {k : ℕ} (d : Fin k → ι) (s : ∀ a, (Q (d a)).obj (op U)) : Prop :=
  ∀ (n : ι) (V : C) (f : V ⟶ U) (x : (Q n).obj (op V)),
    ∃ S : Sieve V, S ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), S g →
      ∃ c : Fin k → A.Total (op W),
        ∑ a, c a • M.totalRestrict (g ≫ f).op (M.incl (d a) (s a)) =
          M.totalRestrict g.op (M.incl n x)

/-- Every section of the total module is locally a combination of a family of homogeneous sections
generating the homogeneous sections. -/
theorem exists_sieve_combination {U : C} {k : ℕ} {d : Fin k → ι} {s : ∀ a, (Q (d a)).obj (op U)}
    (hs : M.GeneratesHomogeneous J d s) (V : C) (f : V ⟶ U) (t : M.Total (op V)) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), S g →
      ∃ c : Fin k → A.Total (op W),
        ∑ a, c a • M.totalRestrict (g ≫ f).op (M.incl (d a) (s a)) =
          M.totalRestrict g.op t := by
  induction t using M.incl_induction with
  | zero => exact ⟨⊤, J.top_mem V, fun W _ _ => ⟨0, by simp⟩⟩
  | incl n x => exact hs n V f x
  | add t t' ht ht' =>
    obtain ⟨S, hS, hc⟩ := ht
    obtain ⟨S', hS', hc'⟩ := ht'
    refine ⟨S ⊓ S', J.intersection_covering hS hS', fun W g hg => ?_⟩
    obtain ⟨c, hcw⟩ := hc W g hg.1
    obtain ⟨c', hcw'⟩ := hc' W g hg.2
    exact ⟨c + c', by
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hcw, hcw', map_add]⟩

/-- A finite family of
homogeneous sections generating every homogeneous section locally generates the total module as a
presheaf of modules over the ungraded realization. -/
theorem generates_totalPresheafMod {U : C} {k : ℕ} (d : Fin k → ι)
    (s : ∀ a, (Q (d a)).obj (op U)) (hs : M.GeneratesHomogeneous J d s) :
    PresheafOfModules.Generates J M.totalPresheafMod (fun a => M.incl (d a) (s a)) :=
  fun V f t => M.exists_sieve_combination J hs V f t

/-- The total module of a graded module of finite type is of finite type. -/
theorem isFiniteType_totalPresheafMod
    (h : ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
      ∀ i, ∃ (k : ℕ) (d : Fin k → ι) (s : ∀ a, (Q (d a)).obj (op (U i))),
        M.GeneratesHomogeneous J d s) :
    PresheafOfModules.IsFiniteType J M.totalPresheafMod := by
  obtain ⟨I, U, hU, hgen⟩ := h
  refine ⟨I, U, hU, fun i => ?_⟩
  obtain ⟨k, d, s, hs⟩ := hgen i
  exact ⟨k, fun a => M.incl (d a) (s a), M.generates_totalPresheafMod J d s hs⟩

end FiniteType

end GradedModule

end GradedCommutative

/-! ### The structure map -/

section StructureMap

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddCommMonoid ι] {P : ι → PresheafOfModules.{w} R} {A : GradedAlgebra P}
  [A.IsCommutative] {Q : ι → PresheafOfModules.{w} R} (M : GradedModule A Q)

/-- The module structure of the total module over the base ring is the one induced along the
structure map of the ungraded realization. -/
lemma GradedModule.structureMap_smul {X : Cᵒᵖ} (r : R.obj X) (m : M.Total X) :
    A.structureMap X r • m = r • m := by
  change (r • (1 : A.Total X)) • m = r • m
  rw [M.smul_smul_eq, one_smul]

end StructureMap

end Stacks

namespace SheafOfModules

open CategoryTheory

universe v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- A graded module over a sheaf of graded algebras, read as a graded module of presheaves of
modules by forgetting the sheaf conditions on its pieces. -/
def GradedModule.toPresheafGradedModule {A : GradedAlgebra.{w, w} R}
    (M : GradedModule.{w, w, w} A) :
    Stacks.GradedModule A.toPresheafGradedAlgebra (fun n : ℤ => (M.piece n).val) where
  smul := M.smul
  smul_smul_left := M.smul_smul_left
  smul_smul_right := M.smul_smul_right
  smul_naturality := M.smul_naturality
  smul_mul := M.smul_mul
  smul_one := M.smul_one

/-- Commutativity of a sheaf of graded algebras: `Stacks.GradedAlgebra.IsCommutative` for the
graded algebra of presheaves of modules it determines. -/
abbrev GradedAlgebra.IsCommutative (A : GradedAlgebra.{w, w} R) : Prop :=
  A.toPresheafGradedAlgebra.IsCommutative

section Ungraded

variable [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {A : GradedAlgebra.{w, w} R} [A.IsCommutative] (M : GradedModule.{w, w, w} A)

/-- The total module `⨁ₙ Mₙ` of a graded module over a sheaf of graded algebras, as a sheaf of
modules over the ungraded realization `SheafOfModules.GradedAlgebra.ungradedSheaf`: the
sheafification of the presheaf of modules `Stacks.GradedModule.totalPresheafMod` along the
sheafification unit of the ungraded realization. -/
noncomputable def GradedModule.ungradedSheaf : SheafOfModules.{w} A.ungradedSheaf :=
  (PresheafOfModules.sheafification (A.toPresheafGradedAlgebra.toTotalSheaf J)).obj
    M.toPresheafGradedModule.totalPresheafMod

/-- The sheafification unit of the total module. -/
noncomputable def GradedModule.toUngradedSheaf :
    M.toPresheafGradedModule.totalPresheafMod ⟶
      (PresheafOfModules.restrictScalars (A.toPresheafGradedAlgebra.toTotalSheaf J)).obj
        ((SheafOfModules.forget A.ungradedSheaf).obj M.ungradedSheaf) :=
  (PresheafOfModules.sheafificationAdjunction
    (A.toPresheafGradedAlgebra.toTotalSheaf J)).unit.app _

/-- A homogeneous local section of a graded module, viewed in the total module. -/
noncomputable def GradedModule.ungradedIncl {X : Cᵒᵖ} (n : ℤ) (x : (M.piece n).val.obj X) :
    (M.ungradedSheaf.val.obj X : Type w) :=
  M.toUngradedSheaf.app X (M.toPresheafGradedModule.incl n x)

/-- Morphisms of sheaves of modules out of the total module are the morphisms of presheaves of
modules out of the presheaf total module, read through the sheafification unit of the ungraded
realization. -/
noncomputable def GradedModule.ungradedSheafHomEquiv (F : SheafOfModules.{w} A.ungradedSheaf) :
    (M.ungradedSheaf ⟶ F) ≃
      (M.toPresheafGradedModule.totalPresheafMod ⟶
        (PresheafOfModules.restrictScalars (A.toPresheafGradedAlgebra.toTotalSheaf J)).obj
          ((SheafOfModules.forget A.ungradedSheaf).obj F)) :=
  PresheafOfModules.sheafificationHomEquiv (A.toPresheafGradedAlgebra.toTotalSheaf J)

/-- The morphism of sheaves of modules out of the total module determined by a morphism of
presheaves of modules out of the presheaf total module. -/
noncomputable def GradedModule.ungradedSheafLift (F : SheafOfModules.{w} A.ungradedSheaf)
    (φ : M.toPresheafGradedModule.totalPresheafMod ⟶
      (PresheafOfModules.restrictScalars (A.toPresheafGradedAlgebra.toTotalSheaf J)).obj
        ((SheafOfModules.forget A.ungradedSheaf).obj F)) :
    M.ungradedSheaf ⟶ F :=
  (M.ungradedSheafHomEquiv F).symm φ

/-- The lift restricts along the sheafification unit to the given morphism. -/
theorem GradedModule.ungradedSheafHomEquiv_ungradedSheafLift
    (F : SheafOfModules.{w} A.ungradedSheaf)
    (φ : M.toPresheafGradedModule.totalPresheafMod ⟶
      (PresheafOfModules.restrictScalars (A.toPresheafGradedAlgebra.toTotalSheaf J)).obj
        ((SheafOfModules.forget A.ungradedSheaf).obj F)) :
    M.ungradedSheafHomEquiv F (M.ungradedSheafLift F φ) = φ :=
  (M.ungradedSheafHomEquiv F).apply_symm_apply φ

end Ungraded

end SheafOfModules
