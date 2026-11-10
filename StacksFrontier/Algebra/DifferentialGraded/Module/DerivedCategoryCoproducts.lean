module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclic
public import StacksCore.Tactic.StacksAttribute

/-! # Direct sums in the derived category of a differential graded algebra

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. The canonical functor
`Mod_{(A,d)} ⥤ D(A, d)` to the derived category — the quotient by homotopy followed by the
localization at the quasi-isomorphisms — carries a direct sum of differential graded modules to
a direct sum in `D(A, d)`.

## Main definitions

* `DifferentialGradedModule.directSumObj`: the direct sum `⨁ᵢ Nᵢ` of a family of differential
  graded modules, with underlying right module `⨁ᵢ (Nᵢ).M`.
* `DifferentialGradedModule.directSumInj`: its coprojections.
* `DifferentialGradedModule.directSumDesc`: the descent of a family of homomorphisms out of the
  summands.
* `DifferentialGradedModule.directSumMap`: the direct sum of a family of homomorphisms.

## Main results

* `DifferentialGradedModule.isColimit_directSumObj`: `⨁ᵢ Nᵢ` with its coprojections is a direct
  sum in `Mod_{(A,d)}`.
* `DifferentialGradedModule.directSumHomotopy`: a family of homotopies out of the summands
  assembles into a homotopy out of the direct sum, so the coprojections are jointly epimorphic
  in `K(A, d)` (`DifferentialGradedModule.directSum_homotopyCategory_hom_ext`).
* `DifferentialGradedModule.isQuasiIsomorphism_directSumMap`: a direct sum of
  quasi-isomorphisms is a quasi-isomorphism.
* `DifferentialGradedModule.leftOrthogonal_acyclic_directSumObj`: a direct sum of modules
  orthogonal on the left to the acyclic modules is itself orthogonal on the left to them.
* `DifferentialGradedModule.isColimit_q_mapCocone_directSumObj`: the image of such a direct sum
  is a direct sum in `D(A, d)`.
* `DifferentialGradedModule.derivedCategoryQ_preservesCoproducts`: **Stacks 09QI**, the
  direct-sum half — the canonical functor to the derived category preserves direct sums.

## Implementation notes

*Why the direct sum is rebuilt here.* `Mod_{(A,d)}` has arbitrary direct sums
(`DifferentialGradedModule.instHasCoproducts`, Tag 09JJ) but the object representing one is
`private`, so nothing can be proved about its elements. The argument below needs exactly that:
that a direct sum of quasi-isomorphisms is a quasi-isomorphism, which is a statement about
cocycles and boundaries of the direct sum. So the direct sum is built again, with its carrier
*literally* `⨁ᵢ (Nᵢ).M`, and its universal property is proved; being a colimit, it agrees with
the private one up to the unique isomorphism, and `preservesColimit_of_preserves_colimit_cocone`
only ever needs one colimit cocone per diagram.

*The shape of the proof.* The source's proof (Stacks 09QI) resolves the *target* by a module
with property (I) and appeals to Tag 09KY. Property (I) resolutions (Tag 09KU) are not available
in this development, so the dual route is taken, on the resolutions that are: every module
receives a quasi-isomorphism from one with property (P)
(`DifferentialGradedModule.exists_propertyP_resolution`, Tag 09KP), and such a module is
orthogonal on the *left* to the acyclic modules (Tag 09KM). For a left-orthogonal `P`,
`Hom_{K(A,d)}(P, Y) → Hom_{D(A,d)}(P, Y)` is bijective for *every* `Y`
(`CategoryTheory.ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated`), and a direct
sum of left-orthogonal modules is left-orthogonal; so the image of `⨁ᵢ Pᵢ` is a direct sum in
`D(A, d)`. Replacing an arbitrary family `Mᵢ` by property-(P) resolutions `Pᵢ → Mᵢ` is legitimate
because the induced map `⨁ᵢ Pᵢ → ⨁ᵢ Mᵢ` is again a quasi-isomorphism, hence an isomorphism in
`D(A, d)` — and that is the one step for which the concrete direct sum is needed.

*Universes.* The bundled encoding of Tag 09JJ is single-universe: `R`, the algebra and every
module live in one universe `u`. The index type of a direct sum is therefore taken in `Type u` as
well, that being where `⨁ᵢ (Nᵢ).M` is again a `Type u`. The Stacks source, and the tagged
statement, are polymorphic in the index universe; widening is a widening of Tag 09JJ, not of
this file.

## References

* [Stacks Project, Tag 09QI](https://stacks.math.columbia.edu/tag/09QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-! ### The direct sum of a family of differential graded modules -/

section DirectSum

variable {ι : Type u} (N : ι → DifferentialGradedModule A)

/-- The degree-`n` part of the direct sum `⨁ᵢ Nᵢ`: the elements all of whose components are
homogeneous of degree `n`. -/
def directSumGrading (n : ℤ) : Submodule R (⨁ i, (N i).M) where
  carrier := {x | ∀ i, x i ∈ (N i).grading n}
  add_mem' {x y} hx hy i := by
    simpa only [DirectSum.add_apply] using (((N i).grading n).add_mem (hx i) (hy i))
  zero_mem' i := by
    simpa only [DirectSum.zero_apply] using ((N i).grading n).zero_mem
  smul_mem' r x hx i := by
    simpa only [DirectSum.smul_apply] using ((N i).grading n).smul_mem r (hx i)

/-- Homogeneity in the direct sum is componentwise. -/
@[simp] theorem mem_directSumGrading {n : ℤ} {x : ⨁ i, (N i).M} :
    x ∈ directSumGrading N n ↔ ∀ i, x i ∈ (N i).grading n := Iff.rfl

/-- The `j`-th coprojection carries a homogeneous element of degree `n` to one. -/
theorem lof_mem_directSumGrading [DecidableEq ι] {n : ℤ} (j : ι) {y : (N j).M}
    (hy : y ∈ (N j).grading n) :
    DirectSum.lof R ι (fun i => (N i).M) j y ∈ directSumGrading N n := by
  intro i
  by_cases h : j = i
  · subst h
    simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_same] using hy
  · simpa only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)] using
      ((N i).grading n).zero_mem

/-- The `j`-th summand inclusion carries a homogeneous element of degree `n` to one. -/
theorem of_mem_directSumGrading [DecidableEq ι] {n : ℤ} (j : ι) {y : (N j).M}
    (hy : y ∈ (N j).grading n) :
    DirectSum.of (fun i => (N i).M) j y ∈ directSumGrading N n :=
  lof_mem_directSumGrading N j hy

/-- The `j`-th component map sends the degree-`n` part of the direct sum into the degree-`n`
part of `N j`. -/
theorem map_component_directSumGrading (j : ι) (n : ℤ) :
    Submodule.map (DirectSum.component R ι (fun i => (N i).M) j) (directSumGrading N n)
      ≤ (N j).grading n := by
  rintro _ ⟨x, hx, rfl⟩
  exact hx j

/-- The degree-`n` parts of the direct sum are independent. -/
theorem directSumGrading_iSupIndep : iSupIndep (directSumGrading N) := by
  rw [iSupIndep_def]
  intro n
  rw [Submodule.disjoint_def]
  intro x hxn hxsup
  apply DirectSum.ext
  intro j
  have hgj : iSupIndep (N j).grading :=
    (DirectSum.Decomposition.isInternal (N j).grading).submodule_iSupIndep
  rw [iSupIndep_def] at hgj
  have hd := hgj n
  rw [Submodule.disjoint_def] at hd
  have hproj : x j ∈ ⨆ m, ⨆ (_ : m ≠ n), (N j).grading m := by
    have h : x j ∈ Submodule.map (DirectSum.component R ι (fun i => (N i).M) j)
        (⨆ m, ⨆ (_ : m ≠ n), directSumGrading N m) := ⟨x, hxsup, rfl⟩
    rw [Submodule.map_iSup] at h
    refine (iSup_le (fun m => ?_) : _ ≤ ⨆ m, ⨆ (_ : m ≠ n), (N j).grading m) h
    rw [Submodule.map_iSup]
    exact iSup_le (fun hm => le_trans (map_component_directSumGrading N j m)
      (le_iSup₂ (f := fun m _ => (N j).grading m) m hm))
  simpa using hd (x j) (hxn j) hproj

/-- The degree-`n` parts of the direct sum span it. -/
theorem directSumGrading_iSup_eq_top : iSup (directSumGrading N) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro x _
  rw [← DirectSum.sum_support_of x]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  suffices key : ∀ y : (N j).M, y ∈ ⨆ n, (N j).grading n →
      DirectSum.of (fun i => (N i).M) j y ∈ iSup (directSumGrading N) by
    refine key (x j) ?_
    rw [(DirectSum.Decomposition.isInternal (N j).grading).submodule_iSup_eq_top]
    exact Submodule.mem_top
  intro y hy
  induction hy using Submodule.iSup_induction' with
  | mem n z hz =>
      exact Submodule.mem_iSup_of_mem n (lof_mem_directSumGrading N j hz)
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add a b _ _ iha ihb =>
      simpa only [map_add] using Submodule.add_mem _ iha ihb

/-- The degree-`n` parts of the direct sum form a direct-sum decomposition of it. -/
@[instance_reducible]
def directSumDecomposition : DirectSum.Decomposition (directSumGrading N) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (directSumGrading_iSupIndep N) (directSumGrading_iSup_eq_top N)).chooseDecomposition _

variable [DecidableEq ι]

/-- The componentwise differential of the direct sum. -/
def directSumD : (⨁ i, (N i).M) →ₗ[R] (⨁ i, (N i).M) :=
  DirectSum.toModule R ι (⨁ i, (N i).M)
    (fun i => (DirectSum.lof R ι (fun i => (N i).M) i).comp (N i).d)

/-- The differential of the direct sum acts componentwise. -/
@[simp] theorem directSumD_apply (x : ⨁ i, (N i).M) (j : ι) :
    directSumD N x j = (N j).d (x j) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, DirectSum.zero_apply]
  | of i a =>
      rw [show DirectSum.of (fun i => (N i).M) i a
            = DirectSum.lof R ι (fun i => (N i).M) i a from rfl, directSumD,
        DirectSum.toModule_lof (R := R) (M := fun i => (N i).M) (N := (⨁ i, (N i).M)) i a]
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of]
      by_cases h : i = j
      · subst h; simp
      · simp only [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), map_zero]
  | add x y hx hy => simp only [map_add, DirectSum.add_apply, hx, hy]

/-- The componentwise differential on the `i`-th summand. -/
theorem directSumD_of (i : ι) (y : (N i).M) :
    directSumD N (DirectSum.of (fun i => (N i).M) i y)
      = DirectSum.of (fun i => (N i).M) i ((N i).d y) := by
  apply DirectSum.ext
  intro j
  rw [directSumD_apply]
  by_cases h : j = i
  · subst h; simp
  · simp only [DirectSum.of_eq_of_ne _ _ _ h, map_zero]

/-- The direct sum `⨁ᵢ Nᵢ` of a family of differential graded modules: its carrier is the
direct sum `⨁ᵢ (Nᵢ).M` of the carriers, and its grading, right action and differential are all
componentwise. -/
@[implicit_reducible]
def directSumObj : DifferentialGradedModule A where
  M := ⨁ i, (N i).M
  grading := directSumGrading N
  decomposition := directSumDecomposition N
  smul_mem n m x a hx ha i := by
    simpa only [DirectSum.smul_apply] using (N i).smul_mem n m (x i) a (hx i) ha
  d := directSumD N
  d_comp_d := by
    apply LinearMap.ext
    intro x
    apply DirectSum.ext
    intro j
    simp only [LinearMap.comp_apply, directSumD_apply, DirectSum.zero_apply,
      LinearMap.zero_apply]
    exact LinearMap.congr_fun (N j).d_comp_d (x j)
  d_mem n x hx i := by
    simpa only [directSumD_apply] using (N i).d_mem n (x i) (hx i)
  leibniz n m x a hx ha := by
    apply DirectSum.ext
    intro j
    simp only [directSumD_apply, DirectSum.add_apply, DirectSum.smul_apply,
      DirectSum.apply_eq_component]
    exact (N j).leibniz n m (x j) a (hx j) ha

/-- Homogeneity in `⨁ᵢ Nᵢ` is componentwise. -/
@[simp] theorem mem_directSumObj_grading {n : ℤ} {x : ⨁ i, (N i).M} :
    x ∈ (directSumObj N).grading n ↔ ∀ i, x i ∈ (N i).grading n := Iff.rfl

/-! ### The coprojections and the universal property

Every companion fact about the direct sum is stated over the bare direct sum `⨁ᵢ (Nᵢ).M`, with
the differential written out as the `DirectSum.toModule` it is, and the structure fields of
`directSumObj` are then discharged by `exact`. The carrier of `directSumObj N` is that direct
sum only up to unfolding at default transparency, which is more than instance search performs,
so no instance on it synthesizes and no rewrite can be set up against it; `exact` does check
definitional equality at default transparency, which is why discharging the field works. -/

/-- The `j`-th coprojection intertwines the differential of `N j` with the componentwise
differential of the direct sum. This is the compatibility with the differentials of
`directSumInj`, stated at the honest type. -/
theorem lof_comp_directSumD (j : ι) :
    (DirectSum.lof R ι (fun i => (N i).M) j).comp (N j).d
      = (DirectSum.toModule R ι (⨁ i, (N i).M)
          (fun i => (DirectSum.lof R ι (fun i => (N i).M) i).comp (N i).d)).comp
        (DirectSum.lof R ι (fun i => (N i).M) j) :=
  LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply,
      DirectSum.toModule_lof (R := R) (M := fun i => (N i).M) (N := (⨁ i, (N i).M)) j x]

/-- The `j`-th coprojection `N j ⟶ ⨁ᵢ Nᵢ`. -/
def directSumInj (j : ι) : N j ⟶ directSumObj N where
  toFun := DirectSum.lof R ι (fun i => (N i).M) j
  map_smul x a :=
    map_smul (DirectSum.lof (MulOpposite A.A) ι (fun i => (N i).M) j) (MulOpposite.op a) x
  map_grading _ _ hx := lof_mem_directSumGrading N j hx
  map_d := lof_comp_directSumD N j

/-- The `j`-th coprojection is the `j`-th coprojection of the underlying direct sum. -/
@[simp] theorem directSumInj_toFun_apply (j : ι) (x : (N j).M) :
    (directSumInj N j).toFun x = DirectSum.lof R ι (fun i => (N i).M) j x := rfl

variable {T : DifferentialGradedModule A}

/-- The descent of a family of homomorphisms out of the summands, as a linear map at the honest
type. -/
abbrev directSumDescLinear (g : ∀ i, N i ⟶ T) : (⨁ i, (N i).M) →ₗ[R] T.M :=
  DirectSum.toModule R ι T.M (fun i => (g i).toFun)

/-- The descent reads off the `i`-th map on the `i`-th coprojection. -/
theorem directSumDescLinear_lof (g : ∀ i, N i ⟶ T) (i : ι) (y : (N i).M) :
    directSumDescLinear N g (DirectSum.lof R ι (fun i => (N i).M) i y) = (g i).toFun y :=
  DirectSum.toModule_lof (R := R) (φ := fun i => (g i).toFun) i y

/-- The descent reads off the `i`-th map on the `i`-th summand. -/
theorem directSumDescLinear_of (g : ∀ i, N i ⟶ T) (i : ι) (y : (N i).M) :
    directSumDescLinear N g (DirectSum.of (fun i => (N i).M) i y) = (g i).toFun y :=
  directSumDescLinear_lof N g i y

/-- The coprojections are `Aᵐᵒᵖ`-linear: a right multiple of the `i`-th coprojection of `y` is
the `i`-th coprojection of the right multiple of `y`. -/
theorem op_smul_of (i : ι) (y : (N i).M) (a : A.A) :
    MulOpposite.op a • DirectSum.of (fun i => (N i).M) i y
      = DirectSum.of (fun i => (N i).M) i (MulOpposite.op a • y) :=
  (map_smul (DirectSum.lof (MulOpposite A.A) ι (fun i => (N i).M) i) (MulOpposite.op a) y).symm

/-- The descent is compatible with the right `A`-action. -/
theorem directSumDescLinear_smul (g : ∀ i, N i ⟶ T) (x : ⨁ i, (N i).M)
    (a : A.A) :
    directSumDescLinear N g (MulOpposite.op a • x)
      = MulOpposite.op a • directSumDescLinear N g x := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y =>
      rw [op_smul_of N i y a, directSumDescLinear_of, directSumDescLinear_of]
      exact (g i).map_smul y a
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- The descent preserves the grading. -/
theorem directSumDescLinear_mem_grading (g : ∀ i, N i ⟶ T) (n : ℤ)
    (x : ⨁ i, (N i).M) (hx : x ∈ directSumGrading N n) :
    directSumDescLinear N g x ∈ T.grading n := by
  classical
  rw [← DirectSum.sum_support_of x, map_sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [directSumDescLinear_of]
  exact (g j).map_grading n (x j) (hx j)

/-- The descent commutes with the differentials. -/
theorem directSumDescLinear_comp_directSumD (g : ∀ i, N i ⟶ T) :
    (directSumDescLinear N g).comp
        (DirectSum.toModule R ι (⨁ i, (N i).M)
          (fun i => (DirectSum.lof R ι (fun i => (N i).M) i).comp (N i).d))
      = T.d.comp (directSumDescLinear N g) :=
  DirectSum.linearMap_ext R fun i => LinearMap.ext fun y => by
    simp only [LinearMap.comp_apply]
    rw [DirectSum.toModule_lof (R := R)
        (φ := fun i => (DirectSum.lof R ι (fun i => (N i).M) i).comp (N i).d) i y,
      LinearMap.comp_apply, directSumDescLinear_lof, directSumDescLinear_lof]
    exact LinearMap.congr_fun (g i).map_d y

/-- The descent `⨁ᵢ Nᵢ ⟶ T` of a family of homomorphisms `Nᵢ ⟶ T`. -/
def directSumDesc (g : ∀ i, N i ⟶ T) : directSumObj N ⟶ T where
  toFun := directSumDescLinear N g
  map_smul := directSumDescLinear_smul N g
  map_grading := directSumDescLinear_mem_grading N g
  map_d := directSumDescLinear_comp_directSumD N g

/-- The descent restricts on the `j`-th summand to the `j`-th given homomorphism. -/
@[simp] theorem directSumInj_comp_directSumDesc (g : ∀ i, N i ⟶ T) (j : ι) :
    directSumInj N j ≫ directSumDesc N g = g j := by
  refine Hom.ext (LinearMap.ext fun y => ?_)
  change directSumDescLinear N g (DirectSum.of (fun i => (N i).M) j y) = (g j).toFun y
  exact directSumDescLinear_of N g j y

/-- Two homomorphisms out of the direct sum agreeing on every summand are equal. -/
theorem directSum_hom_ext {f g : directSumObj N ⟶ T}
    (h : ∀ i, directSumInj N i ≫ f = directSumInj N i ≫ g) : f = g := by
  refine Hom.ext (DirectSum.linearMap_ext R fun i => ?_)
  exact congrArg Hom.toFun (h i)

/-- The direct sum `⨁ᵢ Nᵢ`, with its coprojections, is a direct sum in `Mod_{(A,d)}`. -/
def isColimit_directSumObj :
    IsColimit (Cofan.mk (directSumObj N) (directSumInj N)) :=
  Cofan.IsColimit.mk _ (fun s => directSumDesc N (fun i => s.inj i))
    (fun s j => directSumInj_comp_directSumDesc N _ j)
    (fun s m hm => directSum_hom_ext N (fun i => by
      rw [directSumInj_comp_directSumDesc]
      exact hm i))

/-! ### Homotopies out of a direct sum

A homotopy out of a direct sum is the same thing as a family of homotopies out of the summands:
the assembled map is produced by the universal property of the direct sum of right `A`-modules,
and the homotopy equation is checked on the coprojections, every element of a direct sum having
finite support. -/

section HomotopyAssembly

variable {T : DifferentialGradedModule A}

/-- The assembly of a family of maps out of the summands reads off the `i`-th map on the `i`-th
summand. Stated over `Aᵐᵒᵖ`, the ring over which a homotopy is linear. -/
theorem toModuleOp_of (k : ∀ i, (N i).M →ₗ[MulOpposite A.A] T.M) (i : ι) (y : (N i).M) :
    DirectSum.toModule (MulOpposite A.A) ι T.M k (DirectSum.of (fun i => (N i).M) i y)
      = k i y :=
  DirectSum.toModule_lof (R := MulOpposite A.A) (φ := k) i y

/-- The assembly of a family of degree `-1` maps out of the summands again lowers the grading
by one. -/
theorem toModuleOp_mem_grading (k : ∀ i, (N i).M →ₗ[MulOpposite A.A] T.M)
    (hk : ∀ (i : ι) (n : ℤ) (y : (N i).M), y ∈ (N i).grading n → k i y ∈ T.grading (n - 1))
    (n : ℤ) (x : ⨁ i, (N i).M) (hx : x ∈ directSumGrading N n) :
    DirectSum.toModule (MulOpposite A.A) ι T.M k x ∈ T.grading (n - 1) := by
  classical
  rw [← DirectSum.sum_support_of x, map_sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  rw [toModuleOp_of]
  exact hk j n (x j) (hx j)

/-- The homotopy equation for the assembled map, over the bare direct sum. -/
theorem toModuleOp_homotopy_eq {f g : directSumObj N ⟶ T}
    (h : ∀ i, Homotopy (directSumInj N i ≫ f) (directSumInj N i ≫ g)) (x : ⨁ i, (N i).M) :
    f.toFun x - g.toFun x
      = T.d (DirectSum.toModule (MulOpposite A.A) ι T.M (fun i => (h i).toLinearMap) x)
        + DirectSum.toModule (MulOpposite A.A) ι T.M (fun i => (h i).toLinearMap)
            (directSumD N x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y =>
      rw [directSumD_of, toModuleOp_of, toModuleOp_of]
      exact (h i).homotopy_eq y
  | add x y hx hy =>
      simp only [map_add]
      rw [show f.toFun x + f.toFun y - (g.toFun x + g.toFun y)
            = (f.toFun x - g.toFun x) + (f.toFun y - g.toFun y) from by abel, hx, hy]
      abel

/-- A family of homotopies out of the summands assembles into a homotopy out of the direct
sum. -/
def directSumHomotopy {f g : directSumObj N ⟶ T}
    (h : ∀ i, Homotopy (directSumInj N i ≫ f) (directSumInj N i ≫ g)) : Homotopy f g where
  toLinearMap := DirectSum.toModule (MulOpposite A.A) ι T.M (fun i => (h i).toLinearMap)
  map_grading := toModuleOp_mem_grading N _
    (fun i n y hy => (h i).map_grading n y hy) 
  homotopy_eq := toModuleOp_homotopy_eq N h

/-- The coprojections of the direct sum are jointly epimorphic in the homotopy category. -/
theorem directSum_homotopyCategory_hom_ext {Y : HomotopyCategory A}
    (f g : (toHomotopyCategory A).obj (directSumObj N) ⟶ Y)
    (hfg : ∀ i, (toHomotopyCategory A).map (directSumInj N i) ≫ f
      = (toHomotopyCategory A).map (directSumInj N i) ≫ g) : f = g := by
  have hf : (toHomotopyCategory A).map ((toHomotopyCategory A).preimage f) = f :=
    (toHomotopyCategory A).map_preimage f
  have hg : (toHomotopyCategory A).map ((toHomotopyCategory A).preimage g) = g :=
    (toHomotopyCategory A).map_preimage g
  set f' := (toHomotopyCategory A).preimage f with hf'
  set g' := (toHomotopyCategory A).preimage g with hg'
  have hcomp : ∀ i, Homotopic (directSumInj N i ≫ f') (directSumInj N i ≫ g') := by
    intro i
    refine (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) _ _).1 ?_
    rw [Functor.map_comp, Functor.map_comp, hf, hg]
    exact hfg i
  have : Homotopic f' g' := ⟨directSumHomotopy N (fun i => (hcomp i).some)⟩
  rw [← hf, ← hg]
  exact (CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) f' g').2 this

end HomotopyAssembly

/-! ### Direct sums of homomorphisms, and of quasi-isomorphisms -/

section QuasiIso

variable {N' : ι → DifferentialGradedModule A} (f : ∀ i, N i ⟶ N' i)

/-- The direct sum `⨁ᵢ fᵢ : ⨁ᵢ Nᵢ ⟶ ⨁ᵢ Nᵢ'` of a family of homomorphisms. -/
def directSumMap : directSumObj N ⟶ directSumObj N' :=
  directSumDesc N (fun i => f i ≫ directSumInj N' i)

/-- The direct sum of a family of homomorphisms is componentwise on the coprojections. -/
@[simp] theorem directSumInj_comp_directSumMap (i : ι) :
    directSumInj N i ≫ directSumMap N f = f i ≫ directSumInj N' i :=
  directSumInj_comp_directSumDesc N _ i

/-- The direct sum of a family of homomorphisms, as a linear map at the honest type. -/
abbrev directSumMapLinear : (⨁ i, (N i).M) →ₗ[R] (⨁ i, (N' i).M) :=
  DirectSum.toModule R ι (⨁ i, (N' i).M) (fun i => (f i ≫ directSumInj N' i).toFun)

/-- The underlying map of `⨁ᵢ fᵢ`, read at the honest type. -/
theorem directSumMap_toFun_apply (x : ⨁ i, (N i).M) :
    (directSumMap N f).toFun x = directSumMapLinear N f x := rfl

/-- `⨁ᵢ fᵢ` carries the `i`-th summand to the `i`-th summand by `fᵢ`. -/
theorem directSumMapLinear_of (i : ι) (y : (N i).M) :
    directSumMapLinear N f (DirectSum.of (fun i => (N i).M) i y)
      = DirectSum.of (fun i => (N' i).M) i ((f i).toFun y) :=
  DirectSum.toModule_lof (R := R) (φ := fun i => (f i ≫ directSumInj N' i).toFun) i y

/-- `⨁ᵢ fᵢ` acts componentwise. -/
theorem directSumMapLinear_apply (x : ⨁ i, (N i).M) (j : ι) :
    directSumMapLinear N f x j = (f j).toFun (x j) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y =>
      rw [directSumMapLinear_of]
      by_cases h : j = i
      · subst h; simp
      · simp only [DirectSum.of_eq_of_ne _ _ _ h, map_zero]
  | add a b ha hb =>
      rw [map_add]
      simp only [DirectSum.add_apply, ha, hb, map_add]

/-- If the differential of `x` is `y`, then it is so componentwise. -/
private theorem directSumD_component_eq {M : ι → DifferentialGradedModule A}
    {x y : ⨁ i, (M i).M} (h : directSumD M x = y) (i : ι) : (M i).d (x i) = y i := by
  rw [← h, directSumD_apply]

/-- Every homogeneous cocycle of `⨁ᵢ Nᵢ'` is, modulo a boundary, the image of a homogeneous
cocycle of `⨁ᵢ Nᵢ`: the components are handled one at a time and summed over the (finite)
support. -/
private theorem directSumMap_cocycle_aux (hf : ∀ i, IsQuasiIsomorphism (f i)) (n : ℤ)
    (y : ⨁ i, (N' i).M) (hy : y ∈ directSumGrading N' n) (hdy : directSumD N' y = 0) :
    ∃ x : ⨁ i, (N i).M, x ∈ directSumGrading N n ∧ directSumD N x = 0 ∧
      ∃ z : ⨁ i, (N' i).M, z ∈ directSumGrading N' (n - 1) ∧
        directSumD N' z = y - directSumMapLinear N f x := by
  classical
  have hdy' : ∀ i, (N' i).d (y i) = 0 := fun i => directSumD_component_eq hdy i
  rw [← DirectSum.sum_support_of y]
  refine Finset.sum_induction _ (fun w => ∃ x : ⨁ i, (N i).M, x ∈ directSumGrading N n ∧
    directSumD N x = 0 ∧ ∃ z : ⨁ i, (N' i).M, z ∈ directSumGrading N' (n - 1) ∧
      directSumD N' z = w - directSumMapLinear N f x) ?_ ?_ ?_
  · rintro a b ⟨xa, hxa, hdxa, za, hza, hzaeq⟩ ⟨xb, hxb, hdxb, zb, hzb, hzbeq⟩
    refine ⟨xa + xb, (directSumGrading N n).add_mem hxa hxb, ?_,
      za + zb, (directSumGrading N' (n - 1)).add_mem hza hzb, ?_⟩
    · rw [map_add, hdxa, hdxb, add_zero]
    · rw [map_add, hzaeq, hzbeq, map_add]
      abel
  · exact ⟨0, Submodule.zero_mem _, map_zero _, 0, Submodule.zero_mem _, by simp⟩
  · intro i _
    obtain ⟨xi, hxi, hdxi, zi, hzi, hzieq⟩ := (hf i n).1 (y i) (hy i) (hdy' i)
    refine ⟨DirectSum.of (fun i => (N i).M) i xi, of_mem_directSumGrading N i hxi, ?_,
      DirectSum.of (fun i => (N' i).M) i zi, of_mem_directSumGrading N' i hzi, ?_⟩
    · rw [directSumD_of, hdxi, map_zero]
    · rw [directSumD_of, hzieq, directSumMapLinear_of, ← map_sub]

/-- A homogeneous cocycle of `⨁ᵢ Nᵢ` whose image is a boundary is itself a boundary. -/
private theorem directSumMap_boundary_aux (hf : ∀ i, IsQuasiIsomorphism (f i)) (n : ℤ)
    (x : ⨁ i, (N i).M) (hx : x ∈ directSumGrading N n) (hdx : directSumD N x = 0)
    (hb : ∃ z : ⨁ i, (N' i).M, z ∈ directSumGrading N' (n - 1) ∧
      directSumD N' z = directSumMapLinear N f x) :
    ∃ w : ⨁ i, (N i).M, w ∈ directSumGrading N (n - 1) ∧ directSumD N w = x := by
  classical
  obtain ⟨z, hz, hzeq⟩ := hb
  have hdx' : ∀ i, (N i).d (x i) = 0 := fun i => directSumD_component_eq hdx i
  have hzeq' : ∀ i, (N' i).d (z i) = (f i).toFun (x i) := fun i => by
    rw [directSumD_component_eq hzeq i, directSumMapLinear_apply]
  rw [← DirectSum.sum_support_of x]
  refine Finset.sum_induction _ (fun v => ∃ w : ⨁ i, (N i).M,
    w ∈ directSumGrading N (n - 1) ∧ directSumD N w = v) ?_ ?_ ?_
  · rintro a b ⟨wa, hwa, hwaeq⟩ ⟨wb, hwb, hwbeq⟩
    exact ⟨wa + wb, (directSumGrading N (n - 1)).add_mem hwa hwb, by
      rw [map_add, hwaeq, hwbeq]⟩
  · exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  · intro i _
    obtain ⟨wi, hwi, hwieq⟩ := (hf i n).2 (x i) (hx i) (hdx' i) ⟨z i, hz i, hzeq' i⟩
    exact ⟨DirectSum.of (fun i => (N i).M) i wi, of_mem_directSumGrading N i hwi, by
      rw [directSumD_of, hwieq]⟩

/-- A direct sum of quasi-isomorphisms is a quasi-isomorphism, in the cycle-and-boundary
form. -/
theorem isQuasiIsomorphism_directSumMap (hf : ∀ i, IsQuasiIsomorphism (f i)) :
    IsQuasiIsomorphism (directSumMap N f) := by
  intro n
  refine ⟨fun y hy hdy => ?_, fun x hx hdx hb => ?_⟩
  · exact directSumMap_cocycle_aux N f hf n y hy hdy
  · exact directSumMap_boundary_aux N f hf n x hx hdx hb

/-- A direct sum of quasi-isomorphisms is a quasi-isomorphism of the underlying cochain
complexes. -/
theorem quasiIso_directSumMap (hf : ∀ i, IsQuasiIsomorphism (f i)) :
    QuasiIso ((forgetToCochainComplex A).map (directSumMap N f)) :=
  quasiIso_of_isQuasiIsomorphism _ (isQuasiIsomorphism_directSumMap N f hf)

end QuasiIso

/-! ### Direct sums of left-orthogonal modules -/

/-- A direct sum of differential graded modules orthogonal on the left to the acyclic modules is
itself orthogonal on the left to them. -/
theorem leftOrthogonal_acyclic_directSumObj
    (hN : ∀ i, (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (N i))) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (directSumObj N)) :=
  leftOrthogonal_acyclic_of_directSum (directSumInj N)
    (LinearEquiv.refl (MulOpposite A.A) (⨁ i, (N i).M))
    (fun _ _ => rfl) (fun _ _ hz j => hz j) hN

/-! ### Direct sums in the derived category -/

section Derived

/-- The localization at the quasi-isomorphisms is a localization at the multiplicative system
attached to the acyclic objects: the two classes of morphisms coincide (Tag 09KW). -/
theorem q_isLocalization_acyclic_trW (A : DifferentialGradedAlgebra R) :
    ((quasiIsomorphisms' A).Q).IsLocalization (acyclic' A).trW := by
  rw [acyclic_trW_eq_quasiIsomorphisms']
  infer_instance

/-- For a module orthogonal on the left to the acyclic modules, the localization functor is
bijective on homomorphisms out of its class in the homotopy category: homomorphisms in
`D(A, d)` out of such a module are computed in `K(A, d)`. -/
theorem map_q_bijective_of_leftOrthogonal {P : DifferentialGradedModule A}
    (hP : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P))
    (Y : HomotopyCategory A) :
    Function.Bijective (((quasiIsomorphisms' A).Q).map :
      ((toHomotopyCategory A).obj P ⟶ Y) → _) :=
  have := q_isLocalization_acyclic_trW A
  ObjectProperty.leftOrthogonal.map_bijective_of_isTriangulated hP
    ((quasiIsomorphisms' A).Q) Y

/-- The image of a direct sum of modules orthogonal on the left to the acyclic modules is a
direct sum in the derived category.

Both halves of the universal property are read off in `K(A, d)`: existence because the homotopy
quotient is full and `⨁ᵢ Nᵢ` is a direct sum of differential graded modules, uniqueness because
the coprojections are jointly epimorphic in `K(A, d)` and the localization is injective on
homomorphisms out of the left-orthogonal `⨁ᵢ Nᵢ`. -/
def isColimit_q_mapCocone_directSumObj
    (hN : ∀ i, (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj (N i))) :
    IsColimit ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).mapCocone
      (Cofan.mk (directSumObj N) (directSumInj N))) := by
  classical
  refine IsColimit.ofExistsUnique (fun s => ?_)
  let Y : DifferentialGradedModule A := (((quasiIsomorphisms' A).Q).objPreimage s.pt).as
  let e : ((quasiIsomorphisms' A).Q).obj ((toHomotopyCategory A).obj Y) ≅ s.pt :=
    ((quasiIsomorphisms' A).Q).objObjPreimageIso s.pt
  choose h hh using fun i =>
    (map_q_bijective_of_leftOrthogonal (hN i) ((toHomotopyCategory A).obj Y)).surjective
      (s.ι.app ⟨i⟩ ≫ e.inv)
  let k : ∀ i, N i ⟶ Y := fun i => (toHomotopyCategory A).preimage (h i)
  have hfac : ∀ i, (toHomotopyCategory A).map (directSumInj N i)
      ≫ (toHomotopyCategory A).map (directSumDesc N k) = h i := by
    intro i
    rw [← Functor.map_comp, directSumInj_comp_directSumDesc]
    exact (toHomotopyCategory A).map_preimage (h i)
  refine ⟨((quasiIsomorphisms' A).Q).map ((toHomotopyCategory A).map (directSumDesc N k))
    ≫ e.hom, ?_, ?_⟩
  · rintro ⟨i⟩
    simp only [Functor.mapCocone_ι_app, Functor.comp_map, Cofan.mk_ι_app]
    rw [← Category.assoc, ← Functor.map_comp, hfac i, hh i, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · intro m hm
    obtain ⟨m', hm'⟩ :=
      (map_q_bijective_of_leftOrthogonal (leftOrthogonal_acyclic_directSumObj N hN)
        ((toHomotopyCategory A).obj Y)).surjective (m ≫ e.inv)
    have hcomp : ∀ i, (toHomotopyCategory A).map (directSumInj N i) ≫ m'
        = (toHomotopyCategory A).map (directSumInj N i)
          ≫ (toHomotopyCategory A).map (directSumDesc N k) := by
      intro i
      refine (map_q_bijective_of_leftOrthogonal (hN i)
        ((toHomotopyCategory A).obj Y)).injective ?_
      have hmi := hm ⟨i⟩
      simp only [Functor.mapCocone_ι_app, Functor.comp_map, Cofan.mk_ι_app] at hmi
      rw [Functor.map_comp, hm', ← Category.assoc, hmi, hfac i, hh i]
    rw [← directSum_homotopyCategory_hom_ext N _ _ hcomp, hm', Category.assoc, Iso.inv_hom_id,
      Category.comp_id]

end Derived

end DirectSum

/-! ### Resolutions by left-orthogonal modules, in cycle-and-boundary form -/

/-! The property-(P) filtration produced by the unbundled development is bundled by
`DifferentialGradedModule.bundleFiltration`, which is public in
`StacksFrontier/Algebra/DifferentialGraded/Module/PropertyP.lean`. A verbatim private copy used to
sit here, because that declaration was private; it has been retired in favour of the original. -/

/-- **Stacks Tag 09KP** together with **Tag 09KM**, in the form the direct-sum argument needs:
every differential graded module receives a quasi-isomorphism — recorded in the
cycle-and-boundary form — from a module orthogonal on the left to the acyclic modules. -/
theorem exists_isQuasiIsomorphism_leftOrthogonal (A : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule A) :
    ∃ (P : DifferentialGradedModule A) (f : P ⟶ M), IsQuasiIsomorphism f ∧
      (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P) := by
  obtain ⟨P, hP, f, hf, ⟨F⟩⟩ := Stacks.DifferentialGraded.DGModule.exists_propertyP_resolution
    (Unbundled.algebra A) (Unbundled.algebra_isLawful A)
    (Unbundled.module M) (Unbundled.module_isLawful M)
  exact ⟨Unbundled.bundle hP,
    { toFun := Unbundled.restrictR (N := Unbundled.module M) f.toFun
      map_smul := fun x a => f.toFun.map_smul (MulOpposite.op a) x
      map_grading := f.map_grading
      map_d := LinearMap.ext f.commute_d }, hf,
    leftOrthogonal_acyclic_of_propertyP (bundleFiltration hP F)⟩

/-- A quasi-isomorphism becomes an isomorphism in the derived category. -/
theorem isIso_q_map_of_isQuasiIsomorphism {M M' : DifferentialGradedModule A} (g : M ⟶ M')
    (hg : IsQuasiIsomorphism g) :
    IsIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map g) :=
  Localization.inverts ((quasiIsomorphisms' A).Q) (quasiIsomorphisms' A) _
    ((quasiIsomorphisms_map_iff' A g).2 (quasiIso_of_isQuasiIsomorphism g hg))

/-- **Stacks Tag 09QI**, the direct-sum half: *"direct sums in `D(A, d)` are obtained by taking
direct sums of differential graded modules"*, in the form that the canonical functor
`Mod_{(A,d)} ⥤ D(A, d)` — the quotient by homotopy followed by the localization at the
quasi-isomorphisms — preserves direct sums. Preservation of colimits of discrete diagrams
records both that the image of a direct sum is a direct sum and that its coproduct injections
are the images of the canonical ones.

The family is replaced by a family of property-(P) resolutions `Pᵢ → Mᵢ`: the direct sum of
those resolutions is again a quasi-isomorphism, so the two diagrams have isomorphic images in
`D(A, d)`, and the image of `⨁ᵢ Pᵢ` is a direct sum because `⨁ᵢ Pᵢ` is orthogonal on the left
to the acyclic modules. -/
@[stacks 09QI "direct_sums"]
instance derivedCategoryQ_preservesCoproducts (A : DifferentialGradedAlgebra R) (ι : Type u) :
    PreservesColimitsOfShape (Discrete ι)
      (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q) := by
  classical
  have key : ∀ M : ι → DifferentialGradedModule A,
      PreservesColimit (Discrete.functor M)
        (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q) := by
    intro M
    choose P f hf hP using fun i => exists_isQuasiIsomorphism_leftOrthogonal A (M i)
    have hisof : ∀ i, IsIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (f i)) :=
      fun i => isIso_q_map_of_isQuasiIsomorphism (f i) (hf i)
    have hisou : IsIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map
        (directSumMap P f)) :=
      isIso_q_map_of_isQuasiIsomorphism _ (isQuasiIsomorphism_directSumMap P f hf)
    let β : Discrete.functor P ⋙ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q)
        ≅ Discrete.functor M ⋙ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q) :=
      Discrete.natIso (fun i =>
        asIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (f i.as)))
    refine preservesColimit_of_preserves_colimit_cocone (isColimit_directSumObj M) ?_
    refine (IsColimit.precomposeHomEquiv β _) ?_
    refine (isColimit_q_mapCocone_directSumObj P hP).ofIsoColimit
      (Cocone.ext (asIso ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map
        (directSumMap P f))) ?_)
    rintro ⟨i⟩
    have hstep : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (directSumInj P i)
          ≫ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (directSumMap P f)
        = (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (f i)
          ≫ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).map (directSumInj M i) := by
      rw [← Functor.map_comp, ← Functor.map_comp, directSumInj_comp_directSumMap]
    exact hstep
  refine ⟨fun {F} => ?_⟩
  have := key (F.obj ∘ Discrete.mk)
  exact preservesColimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := F)).symm

end DifferentialGradedModule

end
