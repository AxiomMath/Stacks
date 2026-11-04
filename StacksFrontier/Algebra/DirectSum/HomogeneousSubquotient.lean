module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule

/-!
# Gradings of a homogeneous submodule and of its quotient

Let `M` be a module over a commutative ring `S`, graded by a family `ℳ : ι → AddSubgroup M`
with a chosen decomposition, and let `p` be a submodule of `M` which is *homogeneous*: every
homogeneous component of an element of `p` again lies in `p`. Then both `p` and `M ⧸ p` inherit
gradings, by `ℳ i ∩ p` and by the image of `ℳ i` respectively, and the two inherited gradings
are again decompositions.

## Main definitions

* `Stacks.GradedModule.subGrade`: the degree-`i` piece `ℳ i ∩ p` of a submodule, as an additive
  subgroup of `p`.
* `Stacks.GradedModule.quotGrade`: the degree-`i` piece of `M ⧸ p`, the image of `ℳ i`.
* `Stacks.GradedModule.subGradeDecomposition` and
  `Stacks.GradedModule.quotGradeDecomposition`: the induced decompositions, for `p` homogeneous.

## Main results

* `Stacks.GradedModule.isInternal_subGrade` and `Stacks.GradedModule.isInternal_quotGrade`: the
  two induced gradings are internal direct sum decompositions.
* `Stacks.GradedModule.subGrade_gradedSMul` and `Stacks.GradedModule.quotGrade_gradedSMul`: both
  inherited gradings are compatible with the action of a graded ring.
-/

@[expose] public noncomputable section

open DirectSum

namespace Stacks.GradedModule

universe uι uS uM

variable {ι : Type uι} [DecidableEq ι]
variable {S : Type uS} {M : Type uM} [CommRing S] [AddCommGroup M] [Module S M]
variable (ℳ : ι → AddSubgroup M) [Decomposition ℳ] (p : Submodule S M)

/-! ### Degreewise behaviour of a grading-preserving map -/

/-- The degree-`i` component of a sum of homogeneous elements `m j ∈ 𝒩 j` over `s` is `m i` if
`i ∈ s` and `0` otherwise. -/
private theorem decompose_sum_apply {N : Type*} [AddCommGroup N] (𝒩 : ι → AddSubgroup N)
    [Decomposition 𝒩] (s : Finset ι) (m : ι → N) (hm : ∀ j, m j ∈ 𝒩 j) (i : ι) :
    (DirectSum.decompose 𝒩 (∑ j ∈ s, m j) i : N) = if i ∈ s then m i else 0 := by
  rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  split_ifs with hi
  · rw [Finset.sum_eq_single_of_mem i hi fun j _ hji =>
      DirectSum.decompose_of_mem_ne 𝒩 (hm j) hji]
    exact DirectSum.decompose_of_mem_same 𝒩 (hm i)
  · exact Finset.sum_eq_zero fun j hj =>
      DirectSum.decompose_of_mem_ne 𝒩 (hm j) (by rintro rfl; exact hi hj)

/-- A grading-preserving additive map commutes with taking homogeneous components: the
degree-`i` component of `f x` is `f` of the degree-`i` component of `x`. -/
public theorem decompose_apply_map {N : Type*} [AddCommGroup N] (𝒩 : ι → AddSubgroup N)
    [Decomposition 𝒩] (f : M →+ N) (hf : ∀ (i : ι) (m : M), m ∈ ℳ i → f m ∈ 𝒩 i) (x : M)
    (i : ι) :
    ((DirectSum.decompose 𝒩 (f x) i : N)) = f ((DirectSum.decompose ℳ x i : M)) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose ℳ x]
  rw [map_sum, decompose_sum_apply 𝒩 _ _ (fun j => hf j _ (DirectSum.decompose ℳ x j).2)]
  split_ifs with hi
  · rfl
  · rw [DFinsupp.notMem_support_iff.1 hi]
    simp

/-! ### The grading of a homogeneous submodule -/

/-- The degree-`i` piece of a submodule `p` of a graded module: the elements of `p` which are
homogeneous of degree `i`, as an additive subgroup of `p`. -/
public def subGrade (i : ι) : AddSubgroup p := (ℳ i).comap p.subtype.toAddMonoidHom

omit [DecidableEq ι] [Decomposition ℳ] in
/-- An element of `p` lies in the degree-`i` piece of `p` iff it lies in `ℳ i`. -/
@[simp] public theorem mem_subGrade {i : ι} {x : p} :
    x ∈ subGrade ℳ p i ↔ (x : M) ∈ ℳ i := Iff.rfl

/-- The degreewise inclusion of the pieces of a submodule into the pieces of the ambient
module. -/
public def subGradeIncl (i : ι) : subGrade ℳ p i →+ ℳ i where
  toFun x := ⟨((x : p) : M), x.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

omit [DecidableEq ι] [Decomposition ℳ] in
/-- The degreewise inclusion `subGradeIncl` does not change the underlying element of `M`. -/
@[simp] public theorem subGradeIncl_coe {i : ι} (x : subGrade ℳ p i) :
    ((subGradeIncl ℳ p i x : M)) = ((x : p) : M) := rfl

omit [DecidableEq ι] [Decomposition ℳ] in
/-- The degreewise inclusion `subGradeIncl` is injective. -/
public theorem subGradeIncl_injective (i : ι) :
    Function.Injective (subGradeIncl ℳ p i) :=
  fun _ _ h => Subtype.ext <| Subtype.ext (congrArg Subtype.val h :)

omit [Decomposition ℳ] in
/-- Recomposition of the pieces of a submodule is recomposition in the ambient module. -/
public theorem subtype_comp_coeAddMonoidHom_subGrade :
    p.subtype.toAddMonoidHom.comp (DirectSum.coeAddMonoidHom (subGrade ℳ p)) =
      (DirectSum.coeAddMonoidHom ℳ).comp (DirectSum.map (subGradeIncl ℳ p)) :=
  DirectSum.addHom_ext fun _ _ => by simp

/-- **The pieces of a homogeneous submodule decompose it.** -/
public theorem isInternal_subGrade (hp : SetLike.IsHomogeneous ℳ p) :
    DirectSum.IsInternal (subGrade ℳ p) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    have h : DirectSum.map (subGradeIncl ℳ p) z = 0 := (Decomposition.isInternal ℳ).1 <| by
      simpa [hz] using (DFunLike.congr_fun (subtype_comp_coeAddMonoidHom_subGrade ℳ p) z).symm
    exact DirectSum.ext fun i => subGradeIncl_injective ℳ p i (by simpa using congrArg (· i) h)
  · intro x
    refine ⟨∑ i ∈ (DirectSum.decompose ℳ (x : M)).support,
      DirectSum.of (fun i => subGrade ℳ p i) i
        ⟨⟨((DirectSum.decompose ℳ (x : M) i : M)), hp i x.2⟩,
          (DirectSum.decompose ℳ (x : M) i).2⟩, Subtype.ext ?_⟩
    simpa using DirectSum.sum_support_decompose ℳ (x : M)

/-- The grading a homogeneous submodule inherits from its ambient graded module. -/
@[instance_reducible]
public def subGradeDecomposition (hp : SetLike.IsHomogeneous ℳ p) :
    Decomposition (subGrade ℳ p) :=
  (isInternal_subGrade ℳ p hp).chooseDecomposition

section GradedSMul

variable {ιA : Type*} {σA : Type*} [AddMonoid ιA] [SetLike σA S] [AddSubmonoidClass σA S]
  (𝒮 : ιA → σA) [VAdd ιA ι] [SetLike.GradedSMul 𝒮 ℳ]

omit [DecidableEq ι] [Decomposition ℳ] [AddMonoid ιA] [AddSubmonoidClass σA S] in
/-- A homogeneous submodule inherits compatibility of its grading with a graded ring action. -/
public theorem subGrade_gradedSMul : SetLike.GradedSMul 𝒮 (subGrade ℳ p) where
  smul_mem _ _ _ _ ha hx := SetLike.GradedSMul.smul_mem (A := 𝒮) (B := ℳ) ha hx

end GradedSMul

/-! ### The grading of the quotient by a homogeneous submodule -/

/-- The degree-`i` piece of `M ⧸ p`: the image of the degree-`i` piece of `M`. -/
public def quotGrade (i : ι) : AddSubgroup (M ⧸ p) := (ℳ i).map p.mkQ.toAddMonoidHom

omit [DecidableEq ι] [Decomposition ℳ] in
/-- An element of `M ⧸ p` lies in the degree-`i` piece iff it is the class of an element of
`ℳ i`. -/
public theorem mem_quotGrade {i : ι} {y : M ⧸ p} :
    y ∈ quotGrade ℳ p i ↔ ∃ m ∈ ℳ i, p.mkQ m = y := by
  simp [quotGrade]

omit [DecidableEq ι] [Decomposition ℳ] in
/-- The class of an element of `ℳ i` lies in the degree-`i` piece of `M ⧸ p`. -/
public theorem mkQ_mem_quotGrade {i : ι} {m : M} (hm : m ∈ ℳ i) :
    p.mkQ m ∈ quotGrade ℳ p i := ⟨m, hm, rfl⟩

/-- **The images of the homogeneous pieces decompose the quotient by a homogeneous
submodule.** -/
public theorem isInternal_quotGrade (hp : SetLike.IsHomogeneous ℳ p) :
    DirectSum.IsInternal (quotGrade ℳ p) := by
  classical
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    choose m hm hmeq using fun i => (mem_quotGrade ℳ p).1 (z i).2
    have hmem : (∑ i ∈ z.support, m i) ∈ p := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum, ← hz,
        DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum]
      exact Finset.sum_congr rfl fun i _ => hmeq i
    refine DirectSum.ext fun i => ?_
    by_cases hi : i ∈ z.support
    · have hdec : (DirectSum.decompose ℳ (∑ j ∈ z.support, m j) i : M) = m i := by
        simpa [hi] using decompose_sum_apply ℳ z.support m hm i
      have := hp i hmem
      rw [hdec, ← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, hmeq] at this
      exact Subtype.ext (by simpa using this)
    · simpa using DFinsupp.notMem_support_iff.1 hi
  · intro y
    obtain ⟨x, rfl⟩ := p.mkQ_surjective y
    refine ⟨∑ i ∈ (DirectSum.decompose ℳ x).support,
      DirectSum.of (fun i => quotGrade ℳ p i) i
        ⟨p.mkQ ((DirectSum.decompose ℳ x i : M)),
          mkQ_mem_quotGrade ℳ p (DirectSum.decompose ℳ x i).2⟩, ?_⟩
    simp only [map_sum, DirectSum.coeAddMonoidHom_of]
    rw [← map_sum, DirectSum.sum_support_decompose ℳ x]

/-- The grading the quotient by a homogeneous submodule inherits. -/
@[instance_reducible]
public def quotGradeDecomposition (hp : SetLike.IsHomogeneous ℳ p) :
    Decomposition (quotGrade ℳ p) :=
  (isInternal_quotGrade ℳ p hp).chooseDecomposition

section GradedSMulQuot

variable {ιA : Type*} {σA : Type*} [AddMonoid ιA] [SetLike σA S] [AddSubmonoidClass σA S]
  (𝒮 : ιA → σA) [VAdd ιA ι] [SetLike.GradedSMul 𝒮 ℳ]

omit [DecidableEq ι] [Decomposition ℳ] [AddMonoid ιA] [AddSubmonoidClass σA S] in
/-- The quotient by a homogeneous submodule inherits compatibility of its grading with a graded
ring action. -/
public theorem quotGrade_gradedSMul : SetLike.GradedSMul 𝒮 (quotGrade ℳ p) where
  smul_mem {i j a y} ha hy := by
    obtain ⟨n, hn, rfl⟩ := (mem_quotGrade ℳ p).1 hy
    exact mkQ_mem_quotGrade ℳ p (SetLike.GradedSMul.smul_mem (A := 𝒮) (B := ℳ) ha hn)

end GradedSMulQuot

end Stacks.GradedModule

end
