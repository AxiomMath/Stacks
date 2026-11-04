module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization

/-!
# The ungraded realization of a graded module, as a sheaf of modules

`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/UngradedAlgebras.lean` turns a graded algebra of
presheaves of modules into the presheaf of rings `Stacks.GradedAlgebra.totalPresheaf` whose
sections are the direct sum of the homogeneous components, and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/UngradedRealization.lean` sheafifies that into
`Stacks.GradedAlgebra.totalSheaf`, the ungraded realization as a *sheaf of rings*. This file does
for a graded *module* what those two do for the algebra: the direct sum `⨁ₙ Mₙ` of the
homogeneous components of a graded module is a module over the ungraded realization of the
algebra, as a presheaf and then — by sheafification — as a sheaf.

What makes this a construction rather than a repackaging is that a graded module supplies only
the degreewise biadditive maps `Mₙ × Aᵢ ⟶ M_{n+i}`; there is no single action anywhere in the
data. The action of the ungraded realization is assembled from them by `DirectSum.toAddMonoid` in
both variables, and the module axioms are then proved by induction on homogeneous sections.

## Main definitions

* `Stacks.RightGradedModule` is a right graded module over `Stacks.GradedAlgebra`: the
  presheaf-level, arbitrary-index form of `SheafOfModules.GradedModule`.
* `Stacks.RightGradedModule.Total` is the direct sum of the homogeneous components over an object
  of the site, and `Stacks.RightGradedModule.incl` views a homogeneous section in it.
* `Stacks.RightGradedModule.act` is the action of the ungraded realization of the algebra on it,
  and `Stacks.RightGradedModule.moduleTotal` is the resulting module structure.
* `Stacks.RightGradedModule.totalPresheafModule` is **the ungraded realization of a graded module,
  as a presheaf of modules over `Stacks.GradedAlgebra.totalPresheaf`**.
* `SheafOfModules.GradedModule.ungradedSheafModule` is **the ungraded realization of a graded
  module over a sheaf of graded algebras, as a sheaf of modules over
  `SheafOfModules.GradedAlgebra.ungradedSheaf`**.

## Main results

* `Stacks.RightGradedModule.act_incl_incl`: the action is the graded action on homogeneous
  sections.
* `Stacks.RightGradedModule.act_one` and `Stacks.RightGradedModule.act_mul`: the two `MulAction`
  laws.
* `Stacks.RightGradedModule.act_structureMap`: **the structure map of the ungraded realization acts
  by the base-ring action**, so the realization is an extension of scalars of the direct sum and
  not a new module structure on it.
* `Stacks.RightGradedModule.totalRestrict_act`: restriction is semilinear over the restriction of
  the ungraded realization of the algebra.
* The two sheafification hypotheses this file adds beyond those of `UngradedRealization`,
  `HasWeakSheafify` and `WEqualsLocallyBijective` for `AddCommGrpCat.{u}`, hold on the site of
  opens of a topological space in `Type u` by Mathlib's instances, so nothing here is vacuous.

## Implementation notes

**Commutativity is needed, and is an explicit hypothesis.** A `Stacks.RightGradedModule` is a
*right* module — the action is `Mₙ × Aᵢ ⟶ M_{n+i}`, with the algebra on the right — while
`Module` in Mathlib is a left module. Reading the right action as a left one turns the law
`(a * b) • x = a • (b • x)` into `x · (a * b) = (x · b) · a`, and associativity of the right
action only gives `x · (a * b) = (x · a) · b`; the two agree exactly when `a` and `b` commute. So
`Stacks.RightGradedModule.moduleTotal` carries the graded commutativity hypothesis `hc` of
`Stacks.GradedAlgebra.mul_comm_total`, together with `hadd`, commutativity of the grading monoid.
This is not a restriction for the intended use: the ungraded realization is consumed as an
algebra sheaf on a scheme (`Stacks.RelativeSpec.gradedAlgebraSheaf`), which needs the very same
hypothesis.

**`hadd` rather than `[AddCommMonoid ι]`.** `Stacks.GradedAlgebra` is stated over
`[AddMonoid ι]`, so asking for `[AddCommMonoid ι]` here would put a second `AddMonoid ι` instance
beside the one the graded algebra carries. Commutativity of the index monoid is therefore the
explicit hypothesis `hadd : ∀ i j, i + j = j + i`, exactly as in
`StacksFrontier/AlgebraicGeometry/Constructions/GradedAlgebraToAlgebraSheaf.lean`; `ℕ` and `ℤ`, the
only intended indices, supply it by `add_comm`.

**Degrees do not need casting.** The right action lands in degree `n + i`, which is the degree the
inclusion into the direct sum is taken at, so `Stacks.RightGradedModule.act` is written without a
single transport. Heterogeneous equality enters only where the *source* data is heterogeneous —
`smul_mul` and `smul_one` — and is discharged by `Stacks.RightGradedModule.incl_eq_incl_of_heq` and
`Stacks.RightGradedModule.smul_congr`.

**Sheafification.** The sheaf-level realization is `PresheafOfModules.sheafification` along the
sheafification unit `Stacks.GradedAlgebra.toTotalSheaf`, which is locally bijective — those are
the instances `UngradedRealization` already proves. The hypotheses are therefore the ones that
file carries plus `HasWeakSheafify J AddCommGrpCat` and
`J.WEqualsLocallyBijective AddCommGrpCat`, which is what sheafifying the underlying abelian
presheaf needs.

**What is here and what is not.** This file builds the module structure. It does not identify the
underlying sheaf of modules with the sheaf coproduct `∐ₙ Mₙ`, and it says nothing about
quasi-coherence or coherence of the result, which are statements about a particular site and
particular pieces.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe v u t w m

namespace Stacks

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P : ι → PresheafOfModules.{w} R}

/-- A right graded module over a graded algebra of presheaves of modules: a family `Q` of
presheaves of modules together with a restriction-compatible biadditive action
`Q n × P i ⟶ Q (n + i)`, linear over the base ring in each variable, associative over the graded
multiplication and unital for the graded unit.

This is the presheaf-level, arbitrary-index form of `SheafOfModules.GradedModule`. The
associativity and unit laws are heterogeneous equalities because the two sides of each live in
pieces whose degrees are propositionally but not definitionally equal. -/
structure RightGradedModule (A : GradedAlgebra P) (Q : ι → PresheafOfModules.{m} R) where
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
    (Q (n + i)).map f (smul n i X x y) = smul n i Y ((Q n).map f x) ((P i).map f y)
  /-- The action is associative over the graded multiplication. -/
  smul_mul (n i j : ι) (X : Cᵒᵖ) (x : (Q n).obj X) (y : (P i).obj X) (z : (P j).obj X) :
    HEq (smul (n + i) j X (smul n i X x y) z) (smul n (i + j) X x ((A.mul i j).app X y z))
  /-- The graded unit acts as the identity. -/
  smul_one (n : ι) (X : Cᵒᵖ) (x : (Q n).obj X) : HEq (smul n 0 X x (A.one.eval X)) x

namespace RightGradedModule

variable {A : GradedAlgebra P} {Q : ι → PresheafOfModules.{m} R} (M : RightGradedModule A Q)

/-! ### The sections of the realization -/

/-- The sections of the ungraded realization of a graded module over an object of the site: the
direct sum of the homogeneous components. -/
def Total (_M : RightGradedModule A Q) (X : Cᵒᵖ) : Type m := DirectSumType Q X

/-- The additive group of sections of the ungraded realization of a graded module. -/
noncomputable instance (X : Cᵒᵖ) : AddCommGroup (M.Total X) :=
  inferInstanceAs (AddCommGroup (DirectSumType Q X))

/-- The module structure over the base ring on the sections of the ungraded realization of a
graded module. -/
noncomputable instance (X : Cᵒᵖ) : Module (R.obj X) (M.Total X) :=
  inferInstanceAs (Module (R.obj X) (DirectSumType Q X))

/-- A homogeneous local section of a graded module, viewed in the ungraded realization. -/
def incl {X : Cᵒᵖ} (n : ι) (x : (Q n).obj X) : M.Total X := DirectSum.of _ n x

/-- The zero homogeneous section is zero in the ungraded realization. -/
@[simp]
lemma incl_zero {X : Cᵒᵖ} (n : ι) : M.incl n (0 : (Q n).obj X) = 0 := map_zero _

/-- The inclusion of homogeneous sections into the ungraded realization is additive. -/
@[simp]
lemma incl_add {X : Cᵒᵖ} (n : ι) (x y : (Q n).obj X) :
    M.incl n (x + y) = M.incl n x + M.incl n y := map_add _ x y

/-- The inclusion of homogeneous sections into the ungraded realization is linear over the base
ring. -/
lemma incl_smul {X : Cᵒᵖ} (n : ι) (r : R.obj X) (x : (Q n).obj X) :
    M.incl n (r • x) = r • M.incl n x := DirectSum.of_smul _ _ _ _

/-- Every section of the ungraded realization is a finite sum of homogeneous ones. -/
lemma incl_induction {X : Cᵒᵖ} {motive : M.Total X → Prop} (x : M.Total X) (zero : motive 0)
    (incl : ∀ (n : ι) (y : (Q n).obj X), motive (M.incl n y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x :=
  DirectSum.induction_on (β := fun n => ((Q n).obj X : Type m)) x zero incl add

/-- Two homogeneous local sections of equal degree which are heterogeneously equal have the same
image in the ungraded realization. -/
lemma incl_eq_incl_of_heq {X : Cᵒᵖ} {n n' : ι} (h : n = n') {x : (Q n).obj X}
    {y : (Q n').obj X} (hxy : HEq x y) : M.incl n x = M.incl n' y := by
  subst h
  rw [eq_of_heq hxy]

omit [DecidableEq ι] in
/-- The graded action respects a heterogeneous equality of homogeneous algebra sections of equal
degree. -/
lemma smul_congr {X : Cᵒᵖ} {n : ι} (x : (Q n).obj X) {i j : ι} (h : i = j) {a : (P i).obj X}
    {b : (P j).obj X} (hab : HEq a b) :
    HEq (M.smul n i X x a) (M.smul n j X x b) := by
  subst h
  rw [eq_of_heq hab]

/-! ### The action of the ungraded realization of the algebra -/

/-- The action of the ungraded realization of the algebra on a *homogeneous* local section of the
module, as an additive map: the graded action, summed over the degrees of the algebra. -/
noncomputable def smulHom {X : Cᵒᵖ} {n : ι} (x : (Q n).obj X) : A.Total X →+ M.Total X :=
  DirectSum.toAddMonoid fun i =>
    (DirectSum.of (fun k => ((Q k).obj X : Type m)) (n + i)).comp (M.smul n i X x)

/-- The action of a homogeneous module section on a homogeneous algebra section is their graded
action. -/
@[simp]
lemma smulHom_incl {X : Cᵒᵖ} {n i : ι} (x : (Q n).obj X) (a : (P i).obj X) :
    M.smulHom x (A.incl i a) = M.incl (n + i) (M.smul n i X x a) :=
  DirectSum.toAddMonoid_of _ _ _

/-- **The action of the ungraded realization of the algebra on the ungraded realization of the
module**, as a biadditive map. The two direct sums are eliminated one after the other, so the
action is determined by its values on pairs of homogeneous sections. -/
noncomputable def act (X : Cᵒᵖ) : M.Total X →+ A.Total X →+ M.Total X :=
  DirectSum.toAddMonoid fun n =>
    AddMonoidHom.mk' (fun x : (Q n).obj X => M.smulHom x) fun x x' => by
      refine DirectSum.addHom_ext fun i a => ?_
      change M.smulHom (x + x') (A.incl i a) = (M.smulHom x + M.smulHom x') (A.incl i a)
      have h : M.smul n i X (x + x') a = M.smul n i X x a + M.smul n i X x' a := by
        rw [map_add, AddMonoidHom.add_apply]
      rw [AddMonoidHom.add_apply, M.smulHom_incl, M.smulHom_incl, M.smulHom_incl, h, M.incl_add]

/-- The action on a homogeneous module section is `Stacks.RightGradedModule.smulHom`. -/
@[simp]
lemma act_incl {X : Cᵒᵖ} {n : ι} (x : (Q n).obj X) : M.act X (M.incl n x) = M.smulHom x :=
  DirectSum.toAddMonoid_of _ _ _

/-- **The action is the graded action on homogeneous sections.** This is its defining property;
every identity below is this together with an induction on homogeneous sections. -/
lemma act_incl_incl {X : Cᵒᵖ} {n i : ι} (x : (Q n).obj X) (a : (P i).obj X) :
    M.act X (M.incl n x) (A.incl i a) = M.incl (n + i) (M.smul n i X x a) := by
  rw [M.act_incl, M.smulHom_incl]

/-- Acting by the graded unit on a homogeneous section does not change its image in the ungraded
realization. -/
private lemma incl_smul_one {X : Cᵒᵖ} (n : ι) (y : (Q n).obj X) :
    M.incl (n + 0) (M.smul n 0 X y (A.one.eval X)) = M.incl n y :=
  M.incl_eq_incl_of_heq (add_zero n) (M.smul_one n X y)

/-- The unit of the ungraded realization of the algebra acts as the identity. -/
lemma act_one {X : Cᵒᵖ} (x : M.Total X) : M.act X x 1 = x := by
  induction x using M.incl_induction with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | incl n y =>
    rw [A.one_eq_incl, M.act_incl_incl, M.incl_smul_one]
  | add x x' hx hx' => rw [map_add, AddMonoidHom.add_apply, hx, hx']

/-- **The action is associative**, read as a left action of the ungraded realization of the
algebra: `(a * b) · x = a · (b · x)` when the two sides are written with the right action
`x · a`. This is the one place where commutativity is used — the right action gives
`x · (a * b) = (x · a) · b`, and turning that into `(x · b) · a` is exactly `a * b = b * a`. -/
lemma act_mul (hadd : ∀ i j : ι, i + j = j + i)
    (hc : ∀ (i j : ι) (W : Cᵒᵖ) (x : (P i).obj W) (y : (P j).obj W),
      HEq ((A.mul i j).app W x y) ((A.mul j i).app W y x))
    {X : Cᵒᵖ} (x : M.Total X) (a b : A.Total X) :
    M.act X x (a * b) = M.act X (M.act X x b) a := by
  induction x using M.incl_induction with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | incl n y =>
    induction a using A.incl_induction with
    | zero => simp only [zero_mul, map_zero]
    | incl i u =>
      induction b using A.incl_induction with
      | zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
      | incl j v =>
        rw [A.incl_mul_incl, M.act_incl_incl, M.act_incl_incl, M.act_incl_incl]
        refine (M.incl_eq_incl_of_heq ?_ ?_).symm
        · rw [add_assoc, hadd j i]
        · exact (M.smul_mul n j i X y v u).trans
            (M.smul_congr y (hadd j i) (hc j i X v u))
      | add b b' hb hb' =>
        simp only [mul_add, map_add, AddMonoidHom.add_apply, hb, hb']
    | add a a' ha ha' =>
      simp only [add_mul, map_add, ha, ha']
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']

/-- **The ungraded realization of a graded module is a module over the ungraded realization of
the algebra**, over each object of the site. -/
@[instance_reducible]
noncomputable def moduleTotal (hadd : ∀ i j : ι, i + j = j + i)
    (hc : ∀ (i j : ι) (W : Cᵒᵖ) (x : (P i).obj W) (y : (P j).obj W),
      HEq ((A.mul i j).app W x y) ((A.mul j i).app W y x))
    (X : Cᵒᵖ) : Module (A.Total X) (M.Total X) where
  smul a x := M.act X x a
  one_smul x := M.act_one x
  mul_smul a b x := M.act_mul hadd hc x a b
  smul_zero a := congrArg (fun φ : A.Total X →+ M.Total X => φ a) (map_zero (M.act X))
  smul_add a x y := congrArg (fun φ : A.Total X →+ M.Total X => φ a) (map_add (M.act X) x y)
  add_smul a b x := map_add (M.act X x) a b
  zero_smul x := map_zero (M.act X x)

/-- **The structure map of the ungraded realization acts by the base-ring action.** The element
`r • 1` of the ungraded realization of the algebra acts on the realization of the module as `r`
acts on the direct sum, so restricting the scalars of the realization along
`Stacks.GradedAlgebra.structureHom` returns the module structure over the base ring that the
direct sum already carries. This is what identifies the underlying module of the realization
with the direct sum of the homogeneous pieces. -/
lemma act_structureMap {X : Cᵒᵖ} (r : R.obj X) (x : M.Total X) :
    M.act X x (A.structureMap X r) = r • x := by
  have h1 : A.structureMap X r = A.incl 0 (r • A.one.eval X) := by
    rw [A.incl_smul, ← A.one_eq_incl]
    rfl
  induction x using M.incl_induction with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply, smul_zero]
  | incl n y =>
    rw [h1, M.act_incl_incl, M.smul_smul_right, M.incl_smul, M.incl_smul_one]
  | add x x' hx hx' => rw [map_add, AddMonoidHom.add_apply, hx, hx', smul_add]

/-! ### The realization as a presheaf of modules -/

/-- Restriction of sections of the ungraded realization of a graded module. -/
noncomputable def totalRestrict {X Y : Cᵒᵖ} (f : X ⟶ Y) : M.Total X →+ M.Total Y :=
  directSumRestrict Q f

/-- Restriction in the ungraded realization restricts each homogeneous section in its degree. -/
@[simp]
lemma totalRestrict_incl {X Y : Cᵒᵖ} (f : X ⟶ Y) (n : ι) (x : (Q n).obj X) :
    M.totalRestrict f (M.incl n x) = M.incl n (sectionRestrict (Q n) f x) :=
  directSumRestrict_of Q f n x

/-- **Restriction is semilinear over restriction in the ungraded realization of the algebra.**
This is what makes the family of modules a presheaf of modules over
`Stacks.GradedAlgebra.totalPresheaf`. -/
lemma totalRestrict_act {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.Total X) (a : A.Total X) :
    M.totalRestrict f (M.act X x a) = M.act Y (M.totalRestrict f x) (A.totalRestrict f a) := by
  induction x using M.incl_induction with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | incl n y =>
    induction a using A.incl_induction with
    | zero => simp only [map_zero]
    | incl i u =>
      have h : sectionRestrict (Q (n + i)) f (M.smul n i X y u) =
          M.smul n i Y (sectionRestrict (Q n) f y) (sectionRestrict (P i) f u) :=
        M.smul_naturality n i f y u
      rw [M.act_incl_incl, M.totalRestrict_incl, M.totalRestrict_incl, A.totalRestrict_incl,
        M.act_incl_incl, h]
    | add a a' ha ha' => simp only [map_add, ha, ha']
  | add x x' hx hx' => simp only [map_add, AddMonoidHom.add_apply, hx, hx']

/-- **The ungraded realization of a graded module, as a presheaf of modules over the ungraded
realization of the algebra.** -/
noncomputable def totalPresheafModule (hadd : ∀ i j : ι, i + j = j + i)
    (hc : ∀ (i j : ι) (W : Cᵒᵖ) (x : (P i).obj W) (y : (P j).obj W),
      HEq ((A.mul i j).app W x y) ((A.mul j i).app W y x)) :
    PresheafOfModules.{m} A.totalPresheaf :=
  letI : ∀ X : Cᵒᵖ, Module (A.totalPresheaf.obj X) ((directSumAb Q).obj X) :=
    fun X => M.moduleTotal hadd hc X
  PresheafOfModules.ofPresheaf (R := A.totalPresheaf) (directSumAb Q)
    fun _ _ f a x => M.totalRestrict_act f x a

end RightGradedModule

end Stacks

namespace SheafOfModules

open CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Presheaf

variable {R : Sheaf J RingCat.{t}} {A : GradedAlgebra.{t, w} R}

/-- A graded module over a sheaf of graded algebras, read as a graded module of presheaves of
modules, so that the ungraded realization applies to it. The action and its laws are the same
data: only the sheaf conditions on the pieces are forgotten, and they play no part in the
realization. -/
def GradedModule.toPresheafRightGradedModule (F : GradedModule.{t, w, m} A) :
    Stacks.RightGradedModule A.toPresheafGradedAlgebra fun n : ℤ => (F.piece n).val where
  smul := F.smul
  smul_smul_left := F.smul_smul_left
  smul_smul_right := F.smul_smul_right
  smul_naturality := F.smul_naturality
  smul_mul := F.smul_mul
  smul_one := F.smul_one

end Presheaf

section Sheaf

variable {R : Sheaf J RingCat.{w}} [HasSheafify J RingCat.{w}]
  [J.WEqualsLocallyBijective RingCat.{w}] [HasWeakSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] {A : GradedAlgebra.{w, w} R}

/-- **The ungraded realization of a graded module over a sheaf of graded algebras, as a sheaf of
modules over `SheafOfModules.GradedAlgebra.ungradedSheaf`.**

The presheaf of modules `Stacks.RightGradedModule.totalPresheafModule` is sheafified along the
sheafification unit `Stacks.GradedAlgebra.toTotalSheaf`, which is locally bijective; that is what
`PresheafOfModules.sheafification` consumes, and the result is a sheaf of modules over the
ungraded realization of the algebra as a sheaf of rings.

The hypothesis `hc` is graded commutativity of the algebra, which is what reads the right action
of a `SheafOfModules.GradedModule` as a left module structure; see the implementation notes. It
is the same hypothesis `Stacks.RelativeSpec.gradedAlgebraSheaf` carries. -/
noncomputable def GradedModule.ungradedSheafModule (F : GradedModule.{w, w, m} A)
    (hc : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a)) :
    SheafOfModules.{m} A.ungradedSheaf :=
  (PresheafOfModules.sheafification (A.toPresheafGradedAlgebra.toTotalSheaf J)).obj
    (F.toPresheafRightGradedModule.totalPresheafModule (fun i j => add_comm i j) hc)

end Sheaf

end SheafOfModules

end
