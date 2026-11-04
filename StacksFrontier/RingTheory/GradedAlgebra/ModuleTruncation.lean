module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The truncation of a graded module above a degree

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring and `M = ⨁_{i ∈ ℤ} 𝒨 i` a `ℤ`-graded
`S`-module. For a cut `N₀ : ℤ` the *truncation of `M` above `N₀`* is

  `M_{≥ N₀} = ⨁_{i ≥ N₀} 𝒨 i ⊆ M`,

the elements all of whose homogeneous components in degrees `< N₀` vanish. It is an
`S`-*submodule*, not merely an additive subgroup, precisely because `𝒮` is nonnegatively graded:
a homogeneous scalar of degree `d ≥ 0` carries the degree-`i` summand into the degree-`d + i`
summand, and `i ≥ N₀` forces `d + i ≥ N₀`.

The pieces `𝒨 i` for `i ≥ N₀` grade `M_{≥ N₀}`, and the pieces for `i < N₀` are zero there, so
one single family — the elements of `M_{≥ N₀}` whose image in `M` is homogeneous of degree `i` —
serves for every degree without a case split: below the cut it is automatically trivial. That
family carries a `DirectSum.Decomposition` and, over `𝒮`, a `SetLike.GradedSMul`, so
`M_{≥ N₀}` is again a graded `S`-module, and the inclusion `M_{≥ N₀} ⊆ M` is a
degree-preserving `S`-linear map which is injective in every degree and surjective in every
degree `≥ N₀`.

That last pair of properties is what the truncation is for: it is the hypothesis of
`isIso_associatedModuleSheafMap_of_eventually_bijective` (in the namespace
`Stacks.AlgebraicGeometry.ProjStalkGlobalSections`), so the associated sheaf of `M_{≥ N₀}` on
`Proj(S)` is canonically isomorphic to that of `M`, while `M_{≥ N₀}` has lost the low-degree
generators that obstruct writing down a map out of `M`.

## Main definitions

* `Stacks.GradedModule.truncationAbove`: the submodule `M_{≥ N₀}`.
* `Stacks.GradedModule.truncationAboveGrading`: its grading, the degree-`i` piece being the
  elements of `M_{≥ N₀}` homogeneous of degree `i` in `M`.
* `Stacks.GradedModule.truncationAboveComponent`: the degree-`i` homogeneous component of an
  element of `M_{≥ N₀}`, read inside `M_{≥ N₀}`.

## Main results

* `Stacks.GradedModule.mem_truncationAbove_iff`: membership is the vanishing of all components
  in degrees `< N₀`.
* `Stacks.GradedModule.mem_truncationAbove_of_mem`: a homogeneous element of degree `≥ N₀`
  lies in the truncation.
* `Stacks.GradedModule.truncationAbove_eq_span`: the truncation is the `S`-span of the
  homogeneous elements of degree `≥ N₀`, which is the description `⨁_{i ≥ N₀} 𝒨 i`.
* `Stacks.GradedModule.truncationAboveGradingDecomposition`,
  `Stacks.GradedModule.truncationAboveGradingGradedSMul`: the truncation is again a graded
  `S`-module.
* `Stacks.GradedModule.truncationAbove_subtype_mem`: the inclusion into `M` is
  degree-preserving.
* `Stacks.GradedModule.eq_zero_of_truncationAbove_subtype_eq_zero`: it is injective.
* `Stacks.GradedModule.exists_mem_truncationAboveGrading`: it is surjective onto the degree-`j`
  piece of `M` for every `j ≥ N₀`.

## Implementation notes

The truncation is cut out by the vanishing of the low-degree components rather than defined as
`⨆_{i ≥ N₀} 𝒨 i`; the two agree by `truncationAbove_eq_span`, and the first description is the
one every proof below computes with. The same choice is made by
`Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsTruncation`, the truncation of
the graded module of twisted global sections, which is this construction's nearest neighbour in
the library but is not an instance of it.

That the truncation is closed under the action needs the elements of `𝒮` and of `M` decomposed
into homogeneous pieces, so it is proved for the underlying additive subgroup
`truncationAboveAddSubgroup`, where the double sum over the two supports can be formed, and the
submodule is then assembled from it. A `Finset` support only exists after `classical`, so no
statement below mentions one: the degree bound on the support is obtained inside each proof from
`eq_zero_of_mem_truncationAboveAddSubgroup_of_lt`, which is support-free.

The grading is a family of `AddSubgroup`s rather than of `Submodule`s because the grading of `M`
itself is only a family of additive subgroups: its `SetLike` carrier `τ` is arbitrary.

The decomposition is built from the single computation
`coe_decompose_coeAddMonoidHom_truncationAboveGrading`, which says that recomposing a family of
homogeneous elements of `M_{≥ N₀}` and then taking the degree-`j` component of the result in `M`
returns the degree-`j` member of the family. Both halves of the bijectivity of the recomposition
map follow from it, injectivity directly and surjectivity together with
`DirectSum.sum_support_decompose`.

The action of `ℕ`-degrees on `ℤ`-degrees that `SetLike.GradedSMul` needs is the scoped instance
`Stacks.GradedLocalization.instVAddNatInt`; open that namespace to use
`truncationAboveGradingGradedSMul`.

## References

* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
-/

@[expose] public noncomputable section

open DirectSum

namespace Stacks.GradedModule

open Stacks.GradedLocalization

universe u v w t

variable {S : Type u} {M : Type v} {σ : Type w} {τ : Type t}
  [CommRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [AddCommGroup M] [Module S M] [SetLike τ M] [AddSubgroupClass τ M]
  (𝒨 : ℤ → τ) [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨] (N₀ : ℤ)

/-! ### The truncation as a submodule -/

/-- The elements of `M` all of whose homogeneous components in degrees `< N₀` vanish, as an
additive subgroup. It is in fact an `S`-submodule, `truncationAbove`. -/
@[ega "II 8.2.1" "partial"]
def truncationAboveAddSubgroup : AddSubgroup M where
  carrier := {x : M | ∀ i : ℤ, i < N₀ → (decompose 𝒨 x i : M) = 0}
  add_mem' hx hy i hi := by
    simp only [decompose_add, DirectSum.add_apply, AddMemClass.coe_add, hx i hi, hy i hi,
      add_zero]
  zero_mem' i _ := by simp
  neg_mem' {x} hx i hi := by
    have h : decompose 𝒨 (-x) = 0 - decompose 𝒨 x := by
      rw [zero_sub]; exact map_neg (decomposeAddEquiv 𝒨) x
    rw [h, DirectSum.sub_apply]
    simp [hx i hi]

/-- An element lies in `truncationAboveAddSubgroup 𝒨 N₀` exactly when all its components in
degrees `< N₀` vanish. -/
theorem mem_truncationAboveAddSubgroup_iff (x : M) :
    x ∈ truncationAboveAddSubgroup 𝒨 N₀ ↔ ∀ i : ℤ, i < N₀ → (decompose 𝒨 x i : M) = 0 :=
  Iff.rfl

/-- A homogeneous element of degree `≥ N₀` has no components below `N₀`. -/
theorem mem_truncationAboveAddSubgroup_of_mem {j : ℤ} (hj : N₀ ≤ j) {x : M} (hx : x ∈ 𝒨 j) :
    x ∈ truncationAboveAddSubgroup 𝒨 N₀ :=
  fun _ hi => decompose_of_mem_ne 𝒨 hx (by omega)

/-- The homogeneous components of an element of the truncation below the cut vanish, read in the
summand rather than in `M`. This is the support-free form of the bound on the support of the
decomposition. -/
theorem eq_zero_of_mem_truncationAboveAddSubgroup_of_lt {x : M}
    (hx : x ∈ truncationAboveAddSubgroup 𝒨 N₀) {j : ℤ} (hj : j < N₀) :
    decompose 𝒨 x j = 0 :=
  ZeroMemClass.coe_eq_zero.mp (hx j hj)

/-- A nonzero component of an element of the truncation has degree `≥ N₀`. -/
private theorem le_of_decompose_ne_zero_of_mem_truncationAboveAddSubgroup {x : M}
    (hx : x ∈ truncationAboveAddSubgroup 𝒨 N₀) {j : ℤ} (hj : decompose 𝒨 x j ≠ 0) : N₀ ≤ j := by
  by_contra h
  exact hj (eq_zero_of_mem_truncationAboveAddSubgroup_of_lt 𝒨 N₀ hx (by omega))

include 𝒮 in
/-- **The truncation is closed under the action of `S`**: a homogeneous scalar has nonnegative
degree, so it cannot move a homogeneous component of degree `≥ N₀` below `N₀`. -/
theorem smul_mem_truncationAboveAddSubgroup (c : S) {x : M}
    (hx : x ∈ truncationAboveAddSubgroup 𝒨 N₀) :
    c • x ∈ truncationAboveAddSubgroup 𝒨 N₀ := by
  classical
  have key : c • x = ∑ d ∈ (decompose 𝒮 c).support, ∑ j ∈ (decompose 𝒨 x).support,
      (decompose 𝒮 c d : S) • (decompose 𝒨 x j : M) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose 𝒮 c, ← DirectSum.sum_support_decompose 𝒨 x]
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun _ _ => Finset.smul_sum
  rw [key]
  refine sum_mem fun d _ => sum_mem fun j hj => ?_
  refine mem_truncationAboveAddSubgroup_of_mem 𝒨 N₀ ?_
    (SetLike.GradedSMul.smul_mem (decompose 𝒮 c d).2 (decompose 𝒨 x j).2)
  have hj' := le_of_decompose_ne_zero_of_mem_truncationAboveAddSubgroup 𝒨 N₀ hx
    (DFinsupp.mem_support_iff.mp hj)
  have hvadd : (d +ᵥ j : ℤ) = (d : ℤ) + j := rfl
  omega

include 𝒮 in
/-- **The truncation `M_{≥ N₀} = ⨁_{i ≥ N₀} 𝒨 i` of a graded module above a degree**, as an
`S`-submodule of `M`: the elements all of whose homogeneous components in degrees `< N₀`
vanish. -/
@[ega "II 8.12.9" "special case"]
def truncationAbove : Submodule S M where
  carrier := truncationAboveAddSubgroup 𝒨 N₀
  add_mem' := (truncationAboveAddSubgroup 𝒨 N₀).add_mem
  zero_mem' := (truncationAboveAddSubgroup 𝒨 N₀).zero_mem
  smul_mem' c _ hx := smul_mem_truncationAboveAddSubgroup 𝒮 𝒨 N₀ c hx

/-- The additive subgroup underlying `truncationAbove 𝒮 𝒨 N₀` is
`truncationAboveAddSubgroup 𝒨 N₀`. -/
@[simp]
theorem toAddSubgroup_truncationAbove :
    (truncationAbove 𝒮 𝒨 N₀).toAddSubgroup = truncationAboveAddSubgroup 𝒨 N₀ := rfl

/-- An element lies in the truncation exactly when all its components in degrees `< N₀`
vanish. -/
theorem mem_truncationAbove_iff (x : M) :
    x ∈ truncationAbove 𝒮 𝒨 N₀ ↔ ∀ i : ℤ, i < N₀ → (decompose 𝒨 x i : M) = 0 :=
  Iff.rfl

/-- A homogeneous element of degree `≥ N₀` lies in the truncation. -/
theorem mem_truncationAbove_of_mem {j : ℤ} (hj : N₀ ≤ j) {x : M} (hx : x ∈ 𝒨 j) :
    x ∈ truncationAbove 𝒮 𝒨 N₀ :=
  mem_truncationAboveAddSubgroup_of_mem 𝒨 N₀ hj hx

/-- **The truncation is the `S`-span of the homogeneous elements of degree `≥ N₀`**, which is
the description `⨁_{i ≥ N₀} 𝒨 i` of it. -/
theorem truncationAbove_eq_span :
    truncationAbove 𝒮 𝒨 N₀ = Submodule.span S (⋃ j ∈ Set.Ici N₀, (𝒨 j : Set M)) := by
  classical
  refine le_antisymm (fun x hx => ?_) (Submodule.span_le.mpr fun z hz => ?_)
  · rw [← DirectSum.sum_support_decompose 𝒨 x]
    refine Submodule.sum_mem _ fun j hj => Submodule.subset_span ?_
    exact Set.mem_biUnion (Set.mem_Ici.mpr
      (le_of_decompose_ne_zero_of_mem_truncationAboveAddSubgroup 𝒨 N₀ hx
        (DFinsupp.mem_support_iff.mp hj))) (decompose 𝒨 x j).2
  · obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.mp hz
    exact mem_truncationAbove_of_mem 𝒮 𝒨 N₀ (Set.mem_Ici.mp hj) hzj

/-! ### The grading of the truncation -/

/-- The degree-`i` piece of the truncation: the elements of `M_{≥ N₀}` that are homogeneous of
degree `i` in `M`. For `i < N₀` it is trivial, by `truncationAboveGrading_eq_bot`. -/
def truncationAboveGrading (i : ℤ) : AddSubgroup (truncationAbove 𝒮 𝒨 N₀) where
  carrier := {x | (x : M) ∈ 𝒨 i}
  add_mem' hx hy := add_mem hx hy
  zero_mem' := zero_mem (𝒨 i)
  neg_mem' hx := neg_mem hx

/-- An element of the truncation lies in its degree-`i` piece exactly when its image in `M` is
homogeneous of degree `i`. -/
theorem mem_truncationAboveGrading_iff (i : ℤ) (x : truncationAbove 𝒮 𝒨 N₀) :
    x ∈ truncationAboveGrading 𝒮 𝒨 N₀ i ↔ (x : M) ∈ 𝒨 i :=
  Iff.rfl

/-- Below the cut the grading of the truncation is trivial: an element of the truncation which
is homogeneous of degree `< N₀` is its own vanishing component. -/
theorem truncationAboveGrading_eq_bot {i : ℤ} (hi : i < N₀) :
    truncationAboveGrading 𝒮 𝒨 N₀ i = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  refine AddSubgroup.mem_bot.mpr (Subtype.ext ?_)
  rw [← decompose_of_mem_same 𝒨 hx]
  exact (mem_truncationAbove_iff 𝒮 𝒨 N₀ _).mp x.2 i hi

/-- The inclusion of the truncation into `M` is degree-preserving. -/
theorem truncationAbove_subtype_mem (i : ℤ) (x : truncationAbove 𝒮 𝒨 N₀)
    (hx : x ∈ truncationAboveGrading 𝒮 𝒨 N₀ i) :
    (truncationAbove 𝒮 𝒨 N₀).subtype x ∈ 𝒨 i :=
  hx

/-- The inclusion of the truncation into `M` is injective, in particular on each homogeneous
piece. -/
theorem eq_zero_of_truncationAbove_subtype_eq_zero {x : truncationAbove 𝒮 𝒨 N₀}
    (hx : (truncationAbove 𝒮 𝒨 N₀).subtype x = 0) : x = 0 :=
  Subtype.ext hx

/-- **The inclusion of the truncation into `M` is surjective in every degree `≥ N₀`**: a
homogeneous element of degree `j ≥ N₀` already lies in the truncation. -/
theorem exists_mem_truncationAboveGrading {j : ℤ} (hj : N₀ ≤ j) {m : M} (hm : m ∈ 𝒨 j) :
    ∃ x : truncationAbove 𝒮 𝒨 N₀, x ∈ truncationAboveGrading 𝒮 𝒨 N₀ j ∧
      (truncationAbove 𝒮 𝒨 N₀).subtype x = m :=
  ⟨⟨m, mem_truncationAbove_of_mem 𝒮 𝒨 N₀ hj hm⟩, hm, rfl⟩

/-- The homogeneous components of an element of the truncation again lie in the truncation:
above the cut because they are homogeneous of degree `≥ N₀`, below it because they vanish. -/
theorem decompose_coe_mem_truncationAbove (x : truncationAbove 𝒮 𝒨 N₀) (i : ℤ) :
    (decompose 𝒨 (x : M) i : M) ∈ truncationAbove 𝒮 𝒨 N₀ := by
  rcases lt_or_ge i N₀ with hi | hi
  · rw [(mem_truncationAbove_iff 𝒮 𝒨 N₀ _).mp x.2 i hi]
    exact zero_mem _
  · exact mem_truncationAbove_of_mem 𝒮 𝒨 N₀ hi (decompose 𝒨 (x : M) i).2

/-- The degree-`i` homogeneous component of an element of the truncation, read as an element of
the truncation's degree-`i` piece. -/
def truncationAboveComponent (x : truncationAbove 𝒮 𝒨 N₀) (i : ℤ) :
    truncationAboveGrading 𝒮 𝒨 N₀ i :=
  ⟨⟨(decompose 𝒨 (x : M) i : M), decompose_coe_mem_truncationAbove 𝒮 𝒨 N₀ x i⟩,
    (decompose 𝒨 (x : M) i).2⟩

/-- The image in `M` of `truncationAboveComponent 𝒮 𝒨 N₀ x i` is the degree-`i` component of
`x` in `M`. -/
@[simp]
theorem coe_truncationAboveComponent (x : truncationAbove 𝒮 𝒨 N₀) (i : ℤ) :
    ((truncationAboveComponent 𝒮 𝒨 N₀ x i : truncationAbove 𝒮 𝒨 N₀) : M) =
      (decompose 𝒨 (x : M) i : M) := rfl

/-- **Recomposing and then decomposing returns the family one started with.** The degree-`j`
component in `M` of the sum of a family of homogeneous elements of the truncation is the
degree-`j` member of that family. -/
theorem coe_decompose_coeAddMonoidHom_truncationAboveGrading
    (a : ⨁ i, truncationAboveGrading 𝒮 𝒨 N₀ i) (j : ℤ) :
    (decompose 𝒨
        ((DirectSum.coeAddMonoidHom (truncationAboveGrading 𝒮 𝒨 N₀) a :
          truncationAbove 𝒮 𝒨 N₀) : M) j : M) =
      ((a j : truncationAbove 𝒮 𝒨 N₀) : M) := by
  classical
  induction a using DirectSum.induction_on with
  | zero => simp
  | of i x =>
    rw [DirectSum.coeAddMonoidHom_of]
    rcases eq_or_ne i j with rfl | hij
    · rw [decompose_of_mem_same 𝒨 x.2, DirectSum.of_eq_same]
    · rw [decompose_of_mem_ne 𝒨 x.2 hij, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij)]
      simp
  | add a b ha hb =>
    rw [map_add, Submodule.coe_add, decompose_add, DirectSum.add_apply, AddMemClass.coe_add, ha,
      hb, DirectSum.add_apply, AddMemClass.coe_add, Submodule.coe_add]

/-- **The truncation of a graded module is again a graded module**: the family of its
homogeneous pieces decomposes it. -/
@[ega "II 8.2.1" "Grading of M^{≥}"]
instance truncationAboveGradingDecomposition :
    DirectSum.Decomposition (truncationAboveGrading 𝒮 𝒨 N₀) := by
  classical
  refine DirectSum.IsInternal.chooseDecomposition _ ⟨fun a b hab => ?_, fun x => ?_⟩
  · refine DFinsupp.ext fun j => Subtype.ext (Subtype.ext ?_)
    rw [← coe_decompose_coeAddMonoidHom_truncationAboveGrading 𝒮 𝒨 N₀ a j, hab,
      coe_decompose_coeAddMonoidHom_truncationAboveGrading 𝒮 𝒨 N₀ b j]
  · refine ⟨∑ i ∈ (decompose 𝒨 (x : M)).support,
      DirectSum.of _ i (truncationAboveComponent 𝒮 𝒨 N₀ x i), Subtype.ext ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    rw [Submodule.coe_sum]
    simpa only [coe_truncationAboveComponent] using DirectSum.sum_support_decompose 𝒨 (x : M)

/-- **A nonnegatively graded ring acts on the truncation**: the action on `M` preserves the
truncation and the degree bookkeeping is the one it has on `M`. -/
instance truncationAboveGradingGradedSMul :
    SetLike.GradedSMul 𝒮 (truncationAboveGrading 𝒮 𝒨 N₀) where
  smul_mem _ _ _ _ ha hb :=
    SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒨) ha
      ((mem_truncationAboveGrading_iff 𝒮 𝒨 N₀ _ _).mp hb)

end Stacks.GradedModule

end
