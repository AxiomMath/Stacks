module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.GradedAlgebra.Basic

@[expose] public section

/-!
# Differential graded algebras and modules, and property (P)

Let `R` be a commutative ring. A *differential graded `R`-algebra* `(A, d)` is a graded
`R`-algebra together with an `R`-linear differential of degree `+1` squaring to zero and
satisfying the graded Leibniz rule. A *right differential graded `A`-module* `(M, d_M)` is a
graded right `A`-module with an `R`-linear differential of degree `+1` squaring to zero and
satisfying the graded Leibniz rule for the right action.

This file sets up that vocabulary: the algebra and module data together with their defining
laws, graded and differential graded homomorphisms, isomorphisms, differential graded
submodules, direct sums, the free module `A` and its shifts `A[k]`, admissible monomorphisms
and epimorphisms and admissible short exact sequences, and finally *property (P)*: a
filtration `0 = F_{-1} P ⊆ F_0 P ⊆ F_1 P ⊆ ⋯` of a differential graded module by differential
graded submodules which is exhaustive, whose inclusions are admissible monomorphisms, and
whose graded pieces `F_{i+1} P / F_i P` are direct sums of shifts of `A`.

## Main definitions

* `Stacks.DifferentialGraded.DGAlgebra` and `Stacks.DifferentialGraded.DGAlgebra.IsLawful`: the
  data of a differential graded `R`-algebra and its defining laws.
* `Stacks.DifferentialGraded.DGModule` and `Stacks.DifferentialGraded.DGModule.IsLawful`: the data
  of a right differential graded `A`-module and its defining laws.
* `Stacks.DifferentialGraded.DGModule.GradedHom`, `Stacks.DifferentialGraded.DGModule.Hom`,
  `Stacks.DifferentialGraded.DGModule.Iso`: homomorphisms of graded modules, of differential
  graded modules, and isomorphisms.
* `Stacks.DifferentialGraded.DGModule.DGSubmodule`: a submodule stable under the action and the
  differential, with the differential graded module structure it inherits.
* `Stacks.DifferentialGraded.DGModule.directSum`: the direct sum of a family of differential graded
  modules, with its componentwise differential and grading.
* `Stacks.DifferentialGraded.DGModule.free`, `Stacks.DifferentialGraded.DGModule.shift`,
  `Stacks.DifferentialGraded.DGModule.shiftFree`: the algebra as a module over itself, the shift
  `M[k]`, and the shifts `A[k]` of the free module.
* `Stacks.DifferentialGraded.DGModule.IsAdmissibleMono`,
  `Stacks.DifferentialGraded.DGModule.IsAdmissibleEpi`,
  `Stacks.DifferentialGraded.DGModule.AdmissibleSES`: the maps and short exact sequences which are
  split after forgetting the differentials.
* `Stacks.DifferentialGraded.DGModule.PropertyPFiltration`: a filtration exhibiting property (P).

## Main results

* `Stacks.DifferentialGraded.DGModule.DGSubmodule.toDGModule`: a differential graded submodule is
  itself a differential graded module, and `Stacks.DifferentialGraded.DGModule.DGSubmodule.incl`
  realizes the inclusion as a homomorphism of differential graded modules.

## Implementation notes

The universe parameters of the filtration are independent of one another.

A right differential graded `A`-module is encoded as a left module over `Aᵐᵒᵖ`; the right
action `m · a` is `MulOpposite.op a • m`. Such a module is also an `R`-module, and its
differential is `R`-linear; the `R`-module structure and the compatibility of the `R`-action
with the `Aᵐᵒᵖ`-action (the `R`-action is restriction of scalars along
`r ↦ MulOpposite.op (algebraMap R A r)`) are part of the data.

Data is separated from laws. A `DGModule` carries the underlying data — carrier, `R`-module
and right `A`-action structures with their compatibility, grading by additive subgroups, and
an `R`-linear differential — while the defining axioms are recorded by the predicate
`DGModule.IsLawful`. This lets every construction (free module, shift, direct sum,
submodule) be a proof-free definition, with lawfulness proved separately where it is needed.

The filtration is indexed by `ℕ`; the stage `F_{-1} = 0` is encoded by the extra bottom data,
which requires the bottom quotient `F_0 / F_{-1} = F_0` to be a direct sum of shifts. All
gradedness and lawfulness conditions of property (P) are bundled into
`PropertyPFiltration`, so that an inhabitant of that structure *is* a filtration as in
property (P).

## References

* [The Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI)
* [The Stacks Project, Tag 09JJ](https://stacks.math.columbia.edu/tag/09JJ)
* [The Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT)
* [The Stacks Project, Tag 09KK](https://stacks.math.columbia.edu/tag/09KK)
-/

set_option backward.isDefEq.respectTransparency false

namespace Stacks.DifferentialGraded

universe u v w w₀ w₁ wq

open scoped DirectSum
open MulOpposite

/- ## Differential graded algebras -/

/-- A (right) differential graded algebra `(A, d)` over a commutative ring `R`:
a `ℤ`-graded `R`-algebra equipped with an `R`-linear differential `d` of degree `+1`.
The conditions that `d` raises degree by one, squares to zero, and satisfies the graded
Leibniz rule are recorded separately in `DGAlgebra.IsLawful`. -/
structure DGAlgebra (R : Type u) [CommRing R] where
  carrier : Type v
  [ring : Ring carrier]
  [algebra : Algebra R carrier]
  grading : ℤ → Submodule R carrier
  [gradedAlgebra : GradedAlgebra grading]
  d : carrier →ₗ[R] carrier

attribute [instance] DGAlgebra.ring DGAlgebra.algebra DGAlgebra.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- The defining laws of a differential graded algebra:
`d (A^n) ⊆ A^{n+1}`, `d ∘ d = 0`, and the graded Leibniz rule
`d (a b) = (d a) b + (-1)^n a (d b)` for homogeneous `a ∈ A^n`. -/
structure DGAlgebra.IsLawful (A : DGAlgebra R) : Prop where
  d_mem : ∀ (n : ℤ) (x : A.carrier), x ∈ A.grading n → A.d x ∈ A.grading (n + 1)
  d_comp_d : ∀ x, A.d (A.d x) = 0
  leibniz : ∀ (n m : ℤ) (a b : A.carrier), a ∈ A.grading n → b ∈ A.grading m →
    A.d (a * b) = A.d a * b + ((-1 : ℤ) ^ n.natAbs) • (a * A.d b)

/- ## Differential graded modules -/

/-- A (right) differential graded `A`-module `(M, d_M)` as *data*: a right `A`-module
(encoded as a module over `Aᵐᵒᵖ`) which is simultaneously an `R`-module, with the
`R`-action being the restriction of scalars along `r ↦ op (algebraMap R A r)`
(`smul_def`).  It carries a grading by additive subgroups `M^n := grading n` and an
`R`-linear differential `d_M` (so `d_M` is `R`-linear by construction, as required by
the data). Its remaining laws are in `DGModule.IsLawful`. -/
structure DGModule (A : DGAlgebra R) where
  carrier : Type w
  [addCommGroup : AddCommGroup carrier]
  [moduleA : Module (A.carrier)ᵐᵒᵖ carrier]
  [moduleR : Module R carrier]
  /-- The `R`-action is the restriction of scalars of the `Aᵐᵒᵖ`-action along the central
  ring map `r ↦ op (algebraMap R A r)`; this makes the inclusion `R → A` act centrally and
  forces `d_M` (being `R`-linear below) to be compatible with the structures. -/
  smul_def : ∀ (r : R) (x : carrier), r • x = (op (algebraMap R A.carrier r)) • x
  grading : ℤ → AddSubgroup carrier
  /-- The differential `d_M`, required to be `R`-linear. -/
  d : carrier →ₗ[R] carrier

attribute [instance] DGModule.addCommGroup DGModule.moduleA DGModule.moduleR

namespace DGModule

variable {A : DGAlgebra R}

/-- The differential of a DG module as an additive group homomorphism. -/
def dAddHom (M : DGModule A) : M.carrier →+ M.carrier := M.d.toAddMonoidHom

/-- The additive differential of a DG module applied to `x` is `d_M x`. -/
@[simp] lemma dAddHom_apply (M : DGModule A) (x : M.carrier) : M.dAddHom x = M.d x := rfl

/-- The defining laws of a differential graded `A`-module `M`:
* `M = ⨁_n M^n` (the grading is an internal direct sum),
* `M^n A^m ⊆ M^{n+m}`,
* `d_M (M^n) ⊆ M^{n+1}`,
* `d_M ∘ d_M = 0`,
* the graded Leibniz rule `d (m·a) = (d m)·a + (-1)^n m·(d a)` for `m ∈ M^n`.
(The `R`-linearity of `d_M` is already part of the data, since `M.d` is an `R`-linear
map; the compatibility of the `R`- and `A`-actions is recorded by `M.smul_def`.) -/
structure IsLawful (M : DGModule A) : Prop where
  isInternal : DirectSum.IsInternal M.grading
  grading_smul : ∀ (n m : ℤ) (x : M.carrier) (a : A.carrier),
    x ∈ M.grading n → a ∈ A.grading m → (op a) • x ∈ M.grading (n + m)
  d_mem : ∀ (n : ℤ) (x : M.carrier), x ∈ M.grading n → M.d x ∈ M.grading (n + 1)
  d_comp_d : ∀ x, M.d (M.d x) = 0
  leibniz : ∀ (n m : ℤ) (x : M.carrier) (a : A.carrier), x ∈ M.grading n → a ∈ A.grading m →
    M.d ((op a) • x) = (op a) • M.d x + ((-1 : ℤ) ^ n.natAbs) • (op (A.d a) • x)

/- ## Homomorphisms of differential graded modules -/

/-- A homomorphism of *graded* `A`-modules: an `Aᵐᵒᵖ`-linear map preserving the grading.
It is **not** required to commute with the differentials. -/
structure GradedHom (M N : DGModule A) where
  toFun : M.carrier →ₗ[(A.carrier)ᵐᵒᵖ] N.carrier
  map_grading : ∀ (n : ℤ) (x : M.carrier), x ∈ M.grading n → toFun x ∈ N.grading n

/-- A homomorphism of *differential* graded `A`-modules: a graded homomorphism that
additionally commutes with the differentials. -/
structure Hom (M N : DGModule A) extends GradedHom M N where
  commute_d : ∀ x, toFun (M.d x) = N.d (toFun x)

/-- The identity graded homomorphism. -/
def GradedHom.id (M : DGModule A) : GradedHom M M where
  toFun := LinearMap.id
  map_grading _ _ hx := hx

/-- The identity DG homomorphism. -/
def Hom.id (M : DGModule A) : Hom M M where
  toGradedHom := GradedHom.id M
  commute_d _ := rfl

/-- Composition of graded homomorphisms. -/
def GradedHom.comp {M N P : DGModule A} (g : GradedHom N P) (f : GradedHom M N) :
    GradedHom M P where
  toFun := g.toFun.comp f.toFun
  map_grading n x hx := g.map_grading n _ (f.map_grading n x hx)

/-- Composition of DG homomorphisms. -/
def Hom.comp {M N P : DGModule A} (g : Hom N P) (f : Hom M N) : Hom M P where
  toGradedHom := g.toGradedHom.comp f.toGradedHom
  commute_d x := (congrArg g.toFun (f.commute_d x)).trans (g.commute_d _)

/-- An isomorphism of differential graded `A`-modules: a DG homomorphism whose underlying
`Aᵐᵒᵖ`-linear map is bijective. -/
structure Iso (M N : DGModule A) extends Hom M N where
  invFun : N.carrier →ₗ[(A.carrier)ᵐᵒᵖ] M.carrier
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

/- ## Differential graded submodules -/

/-- A differential graded `A`-submodule of `M`: an `Aᵐᵒᵖ`-submodule which is stable under
the differential `d_M`.  (Gradedness of the submodule — that `K = ⨁_n (K ∩ M^n)` — is a
law recorded in `DGSubmodule.IsLawful`.)  It inherits the structure of a differential
graded `A`-module via `toDGModule`. -/
structure DGSubmodule (M : DGModule A) where
  toSubmodule : Submodule (A.carrier)ᵐᵒᵖ M.carrier
  /-- Stable under the differential. -/
  d_stable : ∀ x ∈ toSubmodule, M.d x ∈ toSubmodule

/-- A DG submodule is also an `R`-submodule: it is stable under the `R`-action, since the
`R`-action is restriction of scalars of the `Aᵐᵒᵖ`-action. -/
instance {M : DGModule A} (K : DGSubmodule M) : Module R K.toSubmodule :=
  Module.compHom K.toSubmodule (algebraMap R (A.carrier)ᵐᵒᵖ)

/-- The grading on a DG submodule `K ⊆ M`: the degree-`n` piece is `K ∩ M^n`, viewed as a
subgroup of the subtype `K`. -/
def DGSubmodule.grading {M : DGModule A} (K : DGSubmodule M) (n : ℤ) :
    AddSubgroup K.toSubmodule :=
  (M.grading n).comap (K.toSubmodule.toAddSubgroup.subtype)

/-- The differential inherited by a DG submodule `K ⊆ M` (the restriction of `d_M`), as an
`R`-linear map. -/
noncomputable def DGSubmodule.dHom {M : DGModule A} (K : DGSubmodule M) :
    K.toSubmodule →ₗ[R] K.toSubmodule where
  toFun := fun x => ⟨M.d x, K.d_stable x x.2⟩
  map_add' := by intro x y; apply Subtype.ext; simp
  map_smul' r x := by
    apply Subtype.ext
    change M.d ((algebraMap R (A.carrier)ᵐᵒᵖ r) • (x : M.carrier))
        = (algebraMap R (A.carrier)ᵐᵒᵖ r) • (M.d (x : M.carrier))
    have e (y : M.carrier) : (algebraMap R (A.carrier)ᵐᵒᵖ r) • y = r • y := (M.smul_def r y).symm
    rw [e, e, map_smul]

/-- The differential graded `A`-module structure carried by a DG submodule `K ⊆ M`. -/
noncomputable def DGSubmodule.toDGModule {M : DGModule A} (K : DGSubmodule M) : DGModule A where
  carrier := K.toSubmodule
  smul_def _ _ := rfl
  grading := K.grading
  d := K.dHom

/-- The gradedness law for a DG submodule `K ⊆ M`: every homogeneous component (with
respect to the internal grading of `M`) of an element of `K` again lies in `K`, so that
`K = ⨁_n (K ∩ M^n)`. -/
def DGSubmodule.IsLawful {M : DGModule A} (K : DGSubmodule M) : Prop :=
  DirectSum.IsInternal K.grading

/-- The inclusion `K ↪ M` of a DG submodule, as a homomorphism of differential graded
`A`-modules. -/
def DGSubmodule.incl {M : DGModule A} (K : DGSubmodule M) :
    Hom K.toDGModule M where
  toFun := K.toSubmodule.subtype
  map_grading _ _ hx := hx
  commute_d _ := rfl

/- ## Direct sums of differential graded modules -/

/-- The degree-`n` piece of the direct-sum grading: tuples that are homogeneous of degree
`n` in each component. -/
def directSumGrading {ι : Type*} (N : ι → DGModule A) (n : ℤ) :
    AddSubgroup (⨁ i, (N i).carrier) where
  carrier := { x | ∀ i, x i ∈ (N i).grading n }
  add_mem' := by intro a b ha hb i; simpa using add_mem (ha i) (hb i)
  zero_mem' := by intro i; simp
  neg_mem' := by
    intro a ha i
    have h : (-a) i = -(a i) := map_neg (DirectSum.component ℤ _ _ i) a
    rw [h]; exact neg_mem (ha i)

/-- The `R`-linear differential on the direct sum `⨁ i, N i`, acting componentwise. -/
noncomputable def directSumD {ι : Type*} [DecidableEq ι] (N : ι → DGModule A) :
    (⨁ i, (N i).carrier) →ₗ[R] (⨁ i, (N i).carrier) :=
  DirectSum.toModule R ι _ (fun i => (DirectSum.lof R ι _ i).comp ((N i).d))

/-- The direct sum `⨁ i, N i` of a family of differential graded `A`-modules, as a
differential graded `A`-module: the `R`-module structure, the right `A`-action, the
grading, and the (`R`-linear) differential are all defined componentwise. -/
noncomputable def directSum {ι : Type*} [DecidableEq ι] (N : ι → DGModule A) : DGModule A where
  carrier := ⨁ i, (N i).carrier
  moduleA := by
    classical
    exact inferInstance
  smul_def := by
    intro r x
    refine DirectSum.ext (fun i => ?_)
    rw [DirectSum.smul_apply, DirectSum.smul_apply, (N i).smul_def]
  grading := directSumGrading N
  d := directSumD N

/- ## Admissible short exact sequences -/

/-- `f : M → N` is an *admissible monomorphism* if it is injective and admits a graded
`A`-module retraction `π : N → M` with `π ∘ f = id`. -/
def IsAdmissibleMono {M N : DGModule A} (f : Hom M N) : Prop :=
  Function.Injective f.toFun ∧
    ∃ π : GradedHom N M, ∀ x, π.toFun (f.toFun x) = x

/-- `g : M → N` is an *admissible epimorphism* if it is surjective and admits a graded
`A`-module section `s : N → M` with `g ∘ s = id`. -/
def IsAdmissibleEpi {M N : DGModule A} (g : Hom M N) : Prop :=
  Function.Surjective g.toFun ∧
    ∃ s : GradedHom N M, ∀ y, g.toFun (s.toFun y) = y

/-- An *admissible short exact sequence* `0 → K → L → M → 0` in `Mod_(A,d)`: `f, g` are
DG homomorphisms forming a short exact sequence (`f` injective, `g` surjective,
`range f = ker g`) which is split as a sequence of graded `A`-modules (equivalently, `f`
is an admissible monomorphism and `g` is an admissible epimorphism). -/
structure AdmissibleSES {K L M : DGModule A} (f : Hom K L) (g : Hom L M) : Prop where
  injective : Function.Injective f.toFun
  surjective : Function.Surjective g.toFun
  exact : LinearMap.range f.toFun = LinearMap.ker g.toFun
  admissibleMono : IsAdmissibleMono f
  admissibleEpi : IsAdmissibleEpi g

/- ## Shifts `A[k]` -/

/-- The free right differential graded `A`-module `A` (the algebra acting on itself on the
right), as data. -/
noncomputable def free (A : DGAlgebra R) : DGModule A where
  carrier := A.carrier
  grading := fun n => (A.grading n).toAddSubgroup
  smul_def := by
    intro r x
    rw [MulOpposite.smul_eq_mul_unop]
    simp [Algebra.commutes, Algebra.smul_def]
  d := A.d

/-- The shift `M[k]` of a differential graded `A`-module `M`: the same underlying right
`A`-module, with grading `(M[k])^n = M^{n+k}` and differential `(-1)^k d_M`
(Stacks Tag 09KG). -/
noncomputable def shift (M : DGModule A) (k : ℤ) : DGModule A where
  carrier := M.carrier
  smul_def := M.smul_def
  grading := fun n => M.grading (n + k)
  d := ((-1 : ℤ) ^ k.natAbs) • M.d

/-- The shift `A[k]` of the free module. -/
noncomputable def shiftFree (A : DGAlgebra R) (k : ℤ) : DGModule A := (free A).shift k

/- ## Property (P) -/

/-- A *filtration as in property (P)* on a differential graded `A`-module `P` (Tag 09KK):
an increasing sequence of DG submodules
`0 = F_{-1} ⊆ F 0 ⊆ F 1 ⊆ ⋯ ⊆ P`
(the `F_{-1} = 0` stage is implicit, encoded by the bottom quotient `F 0 / F_{-1} = F 0`)
such that:
1. `P = ⋃_p F p` (every element of `P` lies in some `F p`);
2. each inclusion `F_{i-1} ↪ F_i` is an admissible monomorphism (for `i ≥ 0`, where the
   `i = 0` case is the inclusion `0 = F_{-1} ↪ F 0`, automatically admissible); and
3. each quotient `F_i / F_{i-1}` (for `i ≥ 0`) is isomorphic, as a DG `A`-module, to a
   direct sum of shifts `A[k]`.

All gradedness/lawfulness conditions are bundled here so that an inhabitant of this
structure *is* a filtration as in property (P): we record the data of the filtration `F`,
its monotonicity, the exhaustion property, lawfulness (gradedness) of every step `F i`,
for each `i` the admissible inclusion `F i ↪ F (i+1)` together with the corresponding
graded data, and the quotient data for *all* graded pieces including the bottom piece
`F 0 / F_{-1} = F 0`.

The module, the two families of cell indices, and the chosen quotient modules have
independent universes. Each direct sum of shifts has carrier universe equal to the maximum
of the algebra and its cell-index universe; the isomorphisms allow different carrier
universes on their two sides. In particular the cells may be indexed by homogeneous
elements of a module in an arbitrary universe, as in the resolution of Tag 09KP. -/
structure PropertyPFiltration (P : DGModule.{u, w, v} A) where
  /-- `F i` is the `i`-th step of the filtration, a DG submodule of `P` (`i ≥ 0`). -/
  F : ℕ → DGSubmodule P
  /-- Every step `F i` is a (graded) lawful DG submodule, i.e. `F i = ⨁_n (F i ∩ P^n)`. -/
  F_lawful : ∀ i, (F i).IsLawful
  /-- The filtration is increasing. -/
  mono : ∀ i, (F i).toSubmodule ≤ (F (i + 1)).toSubmodule
  /-- `P = ⋃_p F p`. -/
  exhaustive : ∀ x : P.carrier, ∃ p, x ∈ (F p).toSubmodule
  /-- For each `i`, the inclusion `F i ↪ F (i+1)`, as a DG homomorphism. -/
  inclHom : ∀ i, Hom (F i).toDGModule (F (i + 1)).toDGModule
  /-- The inclusion is compatible with the underlying inclusion of submodules. -/
  inclHom_apply : ∀ i (x : (F i).toDGModule.carrier),
    (F (i + 1)).toSubmodule.subtype ((inclHom i).toFun x) = (F i).toSubmodule.subtype x
  /-- Property (P)(2): each inclusion `F i ↪ F (i+1)` is an admissible monomorphism. -/
  admissible : ∀ i, IsAdmissibleMono (inclHom i)
  /-- Index set for the shifts appearing in the bottom graded piece `F 0 / F_{-1} = F 0`. -/
  bottomShiftIndex : Type w₀
  bottomShiftIndexDec : DecidableEq bottomShiftIndex
  /-- The shift amounts `k` for the bottom graded piece. -/
  bottomShiftAmount : bottomShiftIndex → ℤ
  /-- Property (P)(3) for the bottom piece: `F 0 / F_{-1} = F 0 ≅ ⨁ A[k]`. -/
  bottomIso :
    @Iso _ _ _ (F 0).toDGModule
      (@directSum _ _ _ bottomShiftIndex bottomShiftIndexDec
        (fun j => shiftFree A (bottomShiftAmount j)))
  /-- Index set for the shifts appearing in the `i`-th graded piece `F (i+1) / F i`. -/
  shiftIndex : ℕ → Type w₁
  shiftIndexDec : ∀ i, DecidableEq (shiftIndex i)
  /-- The shift amounts `k` for the `i`-th graded piece `F (i+1) / F i`. -/
  shiftAmount : ∀ i, shiftIndex i → ℤ
  /-- The quotient `F (i+1) / F i` (as a DG module), in an independent carrier universe. -/
  quotient : ℕ → DGModule.{u, wq, v} A
  /-- Property (P)(3): `F (i+1)/F i ≅ ⨁ A[k]`. -/
  quotientIso : ∀ i,
    @Iso _ _ _ (quotient i)
      (@directSum _ _ _ (shiftIndex i) (shiftIndexDec i)
        (fun j => shiftFree A (shiftAmount i j)))
  /-- The quotient is the cokernel of the admissible inclusion `F i ↪ F (i+1)`. -/
  isQuotient : ∀ i, ∃ q : Hom (F (i + 1)).toDGModule (quotient i),
    Function.Surjective q.toFun ∧
      LinearMap.ker q.toFun = LinearMap.range (inclHom i).toFun

end DGModule

end Stacks.DifferentialGraded

end
