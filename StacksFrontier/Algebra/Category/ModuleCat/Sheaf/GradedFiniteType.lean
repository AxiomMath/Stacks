module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Graded modules of finite type over a sheaf of graded algebras

Let `R` be a sheaf of rings on a site, let `A` be a sheaf of `ℤ`-graded `R`-algebras and let `M`
be a right graded `A`-module. A finite family of homogeneous local sections of `M` over an
object `U`, given together with their degrees, **generates** `M` over `U` when every homogeneous
section of `M` over an object above `U` is, locally, an `A`-linear combination of their
restrictions; and `M` is **of finite type** when the site has a covering family of objects on
each member of which some finite family of homogeneous sections generates `M`.

This is the graded analogue of `PresheafOfModules.Generates` and
`PresheafOfModules.IsFiniteType`, the sectionwise form of Stacks 03DL(5) for an ungraded sheaf
of modules, and it is the notion to which the hypothesis "`ℱ` is a quasi-coherent graded
`ℬ`-module of finite type" of [Stacks, Tag 0897] refers.

## Main definitions

* `SheafOfModules.GradedModule.smulSection M k x` is multiplication of a homogeneous section `x`
  of degree `d` by a homogeneous section of `A` of degree `k - d`, landing in degree `k`: the
  action of `M` with the degree bookkeeping `d + (k - d) = k` performed once and for all.
* `SheafOfModules.GradedModule.combinationSieve` is the sieve of arrows along which a given
  homogeneous section of `M` becomes an `A`-combination of a given family of homogeneous
  sections.
* `SheafOfModules.GradedModule.Generates M d s` says that the family `s` of homogeneous sections
  of degrees `d` generates `M` over `U`, i.e. that each of those sieves is covering.
* `SheafOfModules.GradedModule.IsFiniteType M` says that `M` is of finite type.

## Main results

* `SheafOfModules.GradedModule.smulSection_restrictₛₗ`, `smulSection_smul_left`,
  `smulSection_smul_right` and `smulSection_sum_left` are the sectionwise calculus of the action
  in the form the definitions below use it.
* `SheafOfModules.GradedModule.generates_iff_combinationSieve_mem`: generation is exactly the
  statement that every combination sieve is covering.
* `SheafOfModules.GradedModule.Generates.restrict`: a generating family stays generating after
  restriction to an object over `U`.
* `SheafOfModules.GradedModule.generates_of_degreeZero`: **generation in degree zero.** If the
  degree-zero piece of `M` is generated over `U` by finitely many sections `s` as a sheaf of
  `R`-modules, and every homogeneous section of `M` is locally a sum of products of sections of
  `M.piece 0` with homogeneous sections of `A`, then `s` generates `M` as a graded `A`-module
  over `U`. This is the criterion by which a graded module generated in degree zero inherits
  finite type from its degree-zero piece, and it is the sentence the proof of
  [Stacks, Tag 02O8] opens with.

## Implementation notes

The degree of a coefficient is written `k - d i` rather than quantified over with an equation
`d i + j i = k`, exactly as in the free graded module on a sheaf of graded sets, where the
degree-`n` piece of the presentation is a direct sum of the pieces `A^{n - deg s}`. One
consequence is that a statement about generators all of degree zero mentions `A.piece (k - 0)`
and not `A.piece k`: `k - 0 = k` is not a definitional equality of integers, and transporting
along it is `SheafOfModules.castHom`.

Generation is defined through `combinationSieve` rather than as a bare existential over covering
sieves, because the two coverings of `generates_of_degreeZero` have to be composed, and
composing them is `GrothendieckTopology.transitive` applied to an actual sieve. The bare
existential form, which is the one `PresheafOfModules.Generates` uses, is recovered by
`generates_iff_combinationSieve_mem`.

The first hypothesis of `generates_of_degreeZero`, `GeneratesDegreeZeroPiece`, is
`PresheafOfModules.Generates` of `StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite`
written out for the degree-zero piece, so a proof of the latter may be supplied for it directly.

The index type of the covering family in `IsFiniteType` lies in the universe of objects of the
site, which loses no generality: a covering family may always be reindexed by the set of objects
carrying generators. This matches `PresheafOfModules.IsFiniteType`.

## References

* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t a m v u

namespace SheafOfModules.GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : GradedAlgebra.{t, a} R}

/-! ### The action of a homogeneous section of the algebra, in a fixed total degree -/

/-- Multiplication of a homogeneous section `x` of degree `d` by a homogeneous section of `A` of
degree `k - d`, landing in degree `k`.

This is the action of `M` with the degree bookkeeping done once: the action itself lands in
degree `d + (k - d)`, and `SheafOfModules.castHom` transports it to degree `k`. -/
def smulSection (M : GradedModule.{t, a, m} A) (k : ℤ) {d : ℤ} {U : Cᵒᵖ}
    (x : (M.piece d).val.obj U) :
    (A.piece (k - d)).val.obj U →+ (M.piece k).val.obj U :=
  (castHom M.piece (show d + (k - d) = k by omega) U).comp (M.smul d (k - d) U x)

/-- The action in a fixed total degree, as an additive map in the module variable. -/
def smulSectionFlip (M : GradedModule.{t, a, m} A) (k : ℤ) {d : ℤ} {U : Cᵒᵖ}
    (y : (A.piece (k - d)).val.obj U) :
    (M.piece d).val.obj U →+ (M.piece k).val.obj U :=
  (castHom M.piece (show d + (k - d) = k by omega) U).comp ((M.smul d (k - d) U).flip y)

/-- `M.smulSection k x y` is the product `M.smul d (k - d) U x y`, transported from degree
`d + (k - d)` to degree `k` by `SheafOfModules.castHom`. -/
theorem smulSection_apply (M : GradedModule.{t, a, m} A) (k : ℤ) {d : ℤ} {U : Cᵒᵖ}
    (x : (M.piece d).val.obj U) (y : (A.piece (k - d)).val.obj U) :
    M.smulSection k x y =
      castHom M.piece (show d + (k - d) = k by omega) U (M.smul d (k - d) U x y) :=
  rfl

/-- `M.smulSectionFlip k y x` and `M.smulSection k x y` are the same section of degree `k`. -/
theorem smulSectionFlip_apply (M : GradedModule.{t, a, m} A) (k : ℤ) {d : ℤ} {U : Cᵒᵖ}
    (x : (M.piece d).val.obj U) (y : (A.piece (k - d)).val.obj U) :
    M.smulSectionFlip k y x = M.smulSection k x y :=
  rfl

/-- Restriction of a section of a presheaf of modules along two composable arrows. -/
theorem restrictₛₗ_restrictₛₗ (N : PresheafOfModules.{m} R.obj) {W V U : C} (g : V ⟶ U)
    (h : W ⟶ V) (y : N.obj (op U)) :
    N.restrictₛₗ h.op (N.restrictₛₗ g.op y) = N.restrictₛₗ (h ≫ g).op y :=
  (N.map_comp_apply g.op h.op y).symm

/-- The action in a fixed total degree commutes with restriction. -/
theorem smulSection_restrictₛₗ (M : GradedModule.{t, a, m} A) (k : ℤ) {d : ℤ} {U V : Cᵒᵖ}
    (f : U ⟶ V) (x : (M.piece d).val.obj U) (y : (A.piece (k - d)).val.obj U) :
    (M.piece k).val.restrictₛₗ f (M.smulSection k x y) =
      M.smulSection k ((M.piece d).val.restrictₛₗ f x)
        ((A.piece (k - d)).val.restrictₛₗ f y) :=
  (castHom_naturality M.piece _ f _).trans
    (congrArg (castHom M.piece (show d + (k - d) = k by omega) V)
      (M.smul_naturality d (k - d) f x y))

/-- The action in a fixed total degree is linear over the sheaf of rings in the module
variable. -/
theorem smulSection_smul_left (M : GradedModule.{t, a, m} A) (k : ℤ) {d : ℤ} {U : Cᵒᵖ}
    (r : R.obj.obj U) (x : (M.piece d).val.obj U) (y : (A.piece (k - d)).val.obj U) :
    M.smulSection k (r • x) y = r • M.smulSection k x y := by
  rw [smulSection_apply, smulSection_apply, M.smul_smul_left, castHom_smul]

/-- The action in a fixed total degree is linear over the sheaf of rings in the algebra
variable. -/
theorem smulSection_smul_right (M : GradedModule.{t, a, m} A) (k : ℤ) {d : ℤ} {U : Cᵒᵖ}
    (r : R.obj.obj U) (x : (M.piece d).val.obj U) (y : (A.piece (k - d)).val.obj U) :
    M.smulSection k x (r • y) = r • M.smulSection k x y := by
  rw [smulSection_apply, smulSection_apply, M.smul_smul_right, castHom_smul]

/-- The action in a fixed total degree is additive in the module variable. -/
theorem smulSection_sum_left (M : GradedModule.{t, a, m} A) (k : ℤ) {d : ℤ} {U : Cᵒᵖ}
    {ι : Type*} (s : Finset ι) (x : ι → (M.piece d).val.obj U)
    (y : (A.piece (k - d)).val.obj U) :
    M.smulSection k (∑ i ∈ s, x i) y = ∑ i ∈ s, M.smulSection k (x i) y :=
  map_sum (M.smulSectionFlip k y) x s

/-- The zero section acts as zero. -/
theorem smulSection_zero_left (M : GradedModule.{t, a, m} A) (k : ℤ) {d : ℤ} {U : Cᵒᵖ}
    (y : (A.piece (k - d)).val.obj U) :
    M.smulSection k (0 : (M.piece d).val.obj U) y = 0 :=
  map_zero (M.smulSectionFlip k y)

/-! ### Generation by a finite family of homogeneous sections -/

/-- The sieve of arrows `g : W ⟶ V` along which the homogeneous section `x` of degree `k`
restricts to an `A`-linear combination of the restrictions of the family `s` of homogeneous
sections of degrees `d`.

A combination restricts to a combination, which is what makes this a sieve. -/
def combinationSieve (M : GradedModule.{t, a, m} A) {U : C} {n : ℕ} (d : Fin n → ℤ)
    (s : ∀ i, (M.piece (d i)).val.obj (op U)) (k : ℤ) {V : C} (f : V ⟶ U)
    (x : (M.piece k).val.obj (op V)) : Sieve V where
  arrows W g := ∃ c : ∀ i, (A.piece (k - d i)).val.obj (op W),
    ∑ i, M.smulSection k ((M.piece (d i)).val.restrictₛₗ (g ≫ f).op (s i)) (c i) =
      (M.piece k).val.restrictₛₗ g.op x
  downward_closed := by
    rintro W W' g ⟨c, hc⟩ h
    refine ⟨fun i => (A.piece (k - d i)).val.restrictₛₗ h.op (c i), ?_⟩
    have hsum : ∑ i, (M.piece k).val.restrictₛₗ h.op
          (M.smulSection k ((M.piece (d i)).val.restrictₛₗ (g ≫ f).op (s i)) (c i)) =
        (M.piece k).val.restrictₛₗ h.op ((M.piece k).val.restrictₛₗ g.op x) := by
      rw [← map_sum, hc]
    rw [Category.assoc]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
      (hsum.trans (restrictₛₗ_restrictₛₗ (M.piece k).val g h x))
    rw [smulSection_restrictₛₗ, restrictₛₗ_restrictₛₗ]

/-- A finite family of homogeneous local sections of `M` over `U`, of degrees `d`,
**generates** `M` over `U` when every homogeneous section of `M` over an object above `U` is
locally an `A`-linear combination of the restrictions of the family.

This is the graded form of `PresheafOfModules.Generates`, the sectionwise meaning of generation
by global sections on a site. -/
def Generates (M : GradedModule.{t, a, m} A) {U : C} {n : ℕ} (d : Fin n → ℤ)
    (s : ∀ i, (M.piece (d i)).val.obj (op U)) : Prop :=
  ∀ (k : ℤ) (V : C) (f : V ⟶ U) (x : (M.piece k).val.obj (op V)),
    M.combinationSieve d s k f x ∈ J V

/-- Generation, in the form of an existential over covering sieves: every homogeneous section is
locally a combination of the family. This is the shape of `PresheafOfModules.Generates`. -/
theorem generates_iff_combinationSieve_mem (M : GradedModule.{t, a, m} A) {U : C} {n : ℕ}
    (d : Fin n → ℤ) (s : ∀ i, (M.piece (d i)).val.obj (op U)) :
    M.Generates d s ↔ ∀ (k : ℤ) (V : C) (f : V ⟶ U) (x : (M.piece k).val.obj (op V)),
      ∃ S : Sieve V, S ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), S g →
        ∃ c : ∀ i, (A.piece (k - d i)).val.obj (op W),
          ∑ i, M.smulSection k ((M.piece (d i)).val.restrictₛₗ (g ≫ f).op (s i)) (c i) =
            (M.piece k).val.restrictₛₗ g.op x := by
  refine ⟨fun h k V f x => ⟨_, h k V f x, fun _ _ hg => hg⟩, fun h k V f x => ?_⟩
  obtain ⟨S, hS, hcomb⟩ := h k V f x
  refine J.superset_covering ?_ hS
  intro W g hg
  exact hcomb W g hg

/-- A family generating `M` over `U` still generates `M` after restriction to an object over
`U`. -/
theorem Generates.restrict {M : GradedModule.{t, a, m} A} {U : C} {n : ℕ} {d : Fin n → ℤ}
    {s : ∀ i, (M.piece (d i)).val.obj (op U)} (hs : M.Generates d s) {U' : C} (p : U' ⟶ U) :
    M.Generates d (fun i => (M.piece (d i)).val.restrictₛₗ p.op (s i)) := by
  intro k V f x
  refine J.superset_covering ?_ (hs k V (f ≫ p) x)
  intro W g hg
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, Eq.trans (Finset.sum_congr rfl fun _ _ => ?_) hc⟩
  rw [restrictₛₗ_restrictₛₗ, Category.assoc]

/-! ### Finite type -/

/-- A right graded module over a sheaf of graded algebras is **of finite type** when the site
has a covering family of objects on each member of which the module is generated by finitely
many homogeneous sections.

This is the graded form of `PresheafOfModules.IsFiniteType`, and it is the hypothesis "finite
type graded `ℬ`-module" of [Stacks, Tag 0897]. -/
class IsFiniteType (M : GradedModule.{t, a, m} A) : Prop where
  /-- A covering family carrying finitely many homogeneous generators on each member. -/
  exists_generators : ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
    ∀ i, ∃ (n : ℕ) (d : Fin n → ℤ) (s : ∀ j, (M.piece (d j)).val.obj (op (U i))),
      M.Generates d s

/-! ### Generation in degree zero -/

section DegreeZero

variable (M : GradedModule.{t, a, m} A) {U : C} {n : ℕ}
  (s : Fin n → (M.piece 0).val.obj (op U))

/-- The hypothesis that the finite family `s` generates the degree-zero piece of `M` over `U` as
a sheaf of `R`-modules. This is `PresheafOfModules.Generates` written out; see the
implementation notes. -/
def GeneratesDegreeZeroPiece : Prop :=
  ∀ (V : C) (f : V ⟶ U) (y : (M.piece 0).val.obj (op V)),
    ∃ S : Sieve V, S ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), S g →
      ∃ c : Fin n → R.obj.obj (op W),
        ∑ i, c i • (M.piece 0).val.restrictₛₗ (g ≫ f).op (s i) =
          (M.piece 0).val.restrictₛₗ g.op y

/-- A single product of a section of `M.piece 0` with a homogeneous section of `A` is locally an
`A`-combination of a family generating the degree-zero piece: the coefficient of a generator is
multiplied by the homogeneous section. -/
theorem combinationSieve_mem_of_smulSection (hs : M.GeneratesDegreeZeroPiece s) (k : ℤ)
    {W : C} (f : W ⟶ U) (y : (M.piece 0).val.obj (op W))
    (b : (A.piece (k - 0)).val.obj (op W)) :
    M.combinationSieve (fun _ : Fin n => (0 : ℤ)) s k f (M.smulSection k y b) ∈ J W := by
  obtain ⟨S, hS, hcomb⟩ := hs W f y
  refine J.superset_covering ?_ hS
  intro W' h hh
  obtain ⟨c, hc⟩ := hcomb W' h hh
  refine ⟨fun i => c i • (A.piece (k - 0)).val.restrictₛₗ h.op b, ?_⟩
  rw [smulSection_restrictₛₗ, ← hc, smulSection_sum_left]
  exact Finset.sum_congr rfl fun i _ =>
    (smulSection_smul_right M k _ _ _).trans (smulSection_smul_left M k _ _ _).symm

/-- A finite sum of products of sections of `M.piece 0` with homogeneous sections of `A` is
locally an `A`-combination of a family generating the degree-zero piece. The summands are each
only locally such a combination, so the coverings of the summands are intersected. -/
theorem combinationSieve_mem_of_sum (hs : M.GeneratesDegreeZeroPiece s) (k : ℤ) {W : C}
    (f : W ⟶ U) :
    ∀ (q : ℕ) (y : Fin q → (M.piece 0).val.obj (op W))
      (b : Fin q → (A.piece (k - 0)).val.obj (op W)),
      M.combinationSieve (fun _ : Fin n => (0 : ℤ)) s k f
        (∑ j, M.smulSection k (y j) (b j)) ∈ J W := by
  intro q
  induction q with
  | zero =>
      intro y b
      refine J.superset_covering ?_ (J.top_mem W)
      intro W' h _
      refine ⟨fun _ => 0, ?_⟩
      rw [Fin.sum_univ_zero, map_zero]
      exact Finset.sum_eq_zero fun _ _ => map_zero _
  | succ q ih =>
      intro y b
      rw [Fin.sum_univ_succ]
      refine J.superset_covering ?_ (J.intersection_covering
        (combinationSieve_mem_of_smulSection M s hs k f (y 0) (b 0))
        (ih (fun j => y j.succ) fun j => b j.succ))
      intro W' h hh
      obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ := (Sieve.inter_apply h).1 hh
      refine ⟨fun i => c₁ i + c₂ i, ?_⟩
      rw [map_add, ← hc₁, ← hc₂, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => map_add _ _ _

/-- **Generation in degree zero.** Suppose the degree-zero piece of `M` is generated over `U` by
the finite family `s` as a sheaf of `R`-modules, and that every homogeneous section of `M` is
locally a sum of products of sections of `M.piece 0` with homogeneous sections of `A`. Then `s`
generates `M` as a graded `A`-module over `U`.

Both hypotheses are local, so the two coverings have to be composed: `hzero` produces a covering
of the given object, and on each of its members the finitely many sections of `M.piece 0`
appearing there are themselves only locally combinations of `s`. -/
theorem generates_of_degreeZero (hs : M.GeneratesDegreeZeroPiece s)
    (hzero : ∀ (k : ℤ) (V : C) (x : (M.piece k).val.obj (op V)),
      ∃ S : Sieve V, S ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), S g →
        ∃ (q : ℕ) (y : Fin q → (M.piece 0).val.obj (op W))
          (b : Fin q → (A.piece (k - 0)).val.obj (op W)),
          ∑ j, M.smulSection k (y j) (b j) = (M.piece k).val.restrictₛₗ g.op x) :
    M.Generates (fun _ : Fin n => (0 : ℤ)) s := by
  intro k V f x
  obtain ⟨S, hS, hcomb⟩ := hzero k V x
  refine J.transitive hS _ ?_
  intro W g hg
  obtain ⟨q, y, b, hyb⟩ := hcomb W g hg
  refine J.superset_covering ?_ (combinationSieve_mem_of_sum M s hs k (g ≫ f) q y b)
  intro W' h hh
  obtain ⟨c, hc⟩ := hh
  refine ⟨c, ?_⟩
  rw [Category.assoc, hc, hyb]
  exact restrictₛₗ_restrictₛₗ (M.piece k).val g h x

end DegreeZero

end SheafOfModules.GradedModule

end
