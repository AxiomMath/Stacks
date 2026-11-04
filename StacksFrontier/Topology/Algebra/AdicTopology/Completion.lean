module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.UniformSpace.CompleteSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedComplete.NakayamaModule
public import StacksFrontier.Homology.DerivedComplete.PrincipalHenselianPair
public import StacksFrontier.RingTheory.Henselian.AbsolutelyIntegrallyClosed
public import StacksFrontier.RingTheory.Henselian.Pair
public import StacksFrontier.RingTheory.Idempotents.Lifting
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible

/-!
# Completion of a submodule-quotient pair

For a submodule `N` of a topological module `M`, completion carries the inclusion and the
quotient projection to maps of completions.  This file records that the completed inclusion is
injective with closed range equal to the closure of `N`, that the completed pair is exact, and
that for a countably generated topology the completed projection is a surjective open map.
It closes with the Henselian-pair property of a weakly admissible ring, the description of the
closure of a submodule as the intersection of its sums with a fundamental system of open
submodules, and the separatedness and completeness of the quotient by a closed submodule.

## References

* [Stacks Project, Tag 0ARZ](https://stacks.math.columbia.edu/tag/0ARZ)
* [Stacks Project, Tag 0AS0](https://stacks.math.columbia.edu/tag/0AS0)
* [Stacks Project, Tag 0AMS](https://stacks.math.columbia.edu/tag/0AMS)
* [Stacks Project, Tag 0AMT](https://stacks.math.columbia.edu/tag/0AMT)
* [Stacks Project, Tag 0DCZ](https://stacks.math.columbia.edu/tag/0DCZ)
-/

@[expose] public section

namespace TopologicalRing

section

/-!
# Completion of a submodule

Let `N` be a submodule of a linearly topologized module `M`.  Completion
preserves exactness at the first two terms of the sequence from `N` to `M` and
then to `M ⧸ N`.  Moreover, the completed submodule has image equal to the
closure of the image of `N` in the completion of `M`.

## Main definitions

* `TopologicalCompletion` is completion for the canonical uniformity of a
  topological additive commutative group.
* `completionSubtype` is the map on completions induced by the inclusion of a
  submodule.
* `completionQuotient` is the map on completions induced by the quotient map.

## Main results

* `completionSubtype_injective` states exactness at the completed submodule.
* `exact_completionSubtype_completionQuotient` states exactness at the
  completed ambient module.
* `range_completionSubtype_eq_closure` identifies the image of the completed
  submodule with the closure of the original submodule's image.

## Implementation notes

The completion is Mathlib's uniform-space completion, formed with the canonical
right uniformity of the topological additive group. Thus the assertion that
`N^wedge` is the closure is expressed as an equality of subsets of `M^wedge`,
using the canonical map on completions.  The two exactness assertions in part
(1) and the closure assertion in part (2) are stated separately.

## References

* [Stacks Project, Tag 0ARZ](https://stacks.math.columbia.edu/tag/0ARZ)
-/


open Set Topology UniformSpace

universe u v

variable {R : Type u} {M : Type v}
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [IsLinearTopology R M]

/-- The completion of a topological additive commutative group with respect to
its canonical uniformity. -/
public abbrev TopologicalCompletion (A : Type*) [AddCommGroup A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] :=
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  Completion A

/-- The map between completions induced by the inclusion of a submodule. -/
public noncomputable def completionSubtype (N : Submodule R M) :
    TopologicalCompletion N → TopologicalCompletion M := by
  letI : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  exact Completion.map N.subtype

/-- The map between completions induced by the quotient map by a submodule. -/
public noncomputable def completionQuotient (N : Submodule R M) :
    TopologicalCompletion M → TopologicalCompletion (M ⧸ N) := by
  letI : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  letI : UniformSpace (M ⧸ N) := IsTopologicalAddGroup.rightUniformSpace (M ⧸ N)
  exact Completion.map N.mkQ

omit [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R M] in
private lemma isUniformInducing_subtype (N : Submodule R M) :
    @IsUniformInducing N M (IsTopologicalAddGroup.rightUniformSpace N)
      (IsTopologicalAddGroup.rightUniformSpace M) N.subtype := by
  let : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  have heq : IsTopologicalAddGroup.rightUniformSpace N =
      UniformSpace.comap N.subtype (IsTopologicalAddGroup.rightUniformSpace M) := by
    let : UniformSpace N := UniformSpace.comap N.subtype
      (IsTopologicalAddGroup.rightUniformSpace M)
    let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
    let : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
    let : IsUniformAddGroup N := AddSubgroup.isUniformAddGroup N.toAddSubgroup
    exact IsUniformAddGroup.rightUniformSpace_eq
  rw [isUniformInducing_iff_uniformSpace]
  exact heq.symm

omit [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R M] in
private lemma isUniformInducing_completionSubtype (N : Submodule R M) :
    @IsUniformInducing (TopologicalCompletion N) (TopologicalCompletion M)
      (by infer_instance) (by infer_instance) (completionSubtype N) := by
  let : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  exact Completion.isUniformInducing_extension
    ((Completion.isUniformInducing_coe M).comp (isUniformInducing_subtype N))

omit [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R M] in
/-- **Stacks Project, Tag 0ARZ, part (1).** The map from the completion of a
submodule to the completion of the ambient linearly topologized module is
injective. -/
@[stacks 0ARZ "part (1), injectivity"]
public lemma completionSubtype_injective (N : Submodule R M) :
    Function.Injective (completionSubtype N) :=
  (isUniformInducing_completionSubtype N).injective

/-- The completed inclusion sends the image of `n` to the image of `n`. -/
private lemma completionSubtype_coe {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (N : Submodule R M) (n : N) :
    completionSubtype N (n : TopologicalCompletion N) = (n.1 : TopologicalCompletion M) := by
  let : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  exact Completion.map_coe (isUniformInducing_subtype N).uniformContinuous n

/-- The completed quotient map sends the image of `m` to the image of its class. -/
private lemma completionQuotient_coe {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] (N : Submodule R M) (m : M) :
    completionQuotient N (m : TopologicalCompletion M) =
      ((N.mkQ m : M ⧸ N) : TopologicalCompletion (M ⧸ N)) := by
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  let : UniformSpace (M ⧸ N) := IsTopologicalAddGroup.rightUniformSpace (M ⧸ N)
  have : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup (M ⧸ N) := isUniformAddGroup_of_addCommGroup
  exact Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous N.continuous_mkQ) m

omit [TopologicalSpace R] [IsTopologicalRing R] in
private lemma kernel_completionQuotient_subset_closure (N : Submodule R M) :
    {x | completionQuotient N x = (0 : M ⧸ N)} ⊆
      closure (range fun n : N ↦ (n.1 : TopologicalCompletion M)) := by
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  let : UniformSpace (M ⧸ N) :=
    IsTopologicalAddGroup.rightUniformSpace (M ⧸ N)
  have : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup (M ⧸ N) := isUniformAddGroup_of_addCommGroup
  intro x hx
  rw [mem_closure_iff_nhds_zero]
  intro U hU
  obtain ⟨V, hV, hVV⟩ := exists_nhds_half_neg hU
  have hVM : {m : M | (m : TopologicalCompletion M) ∈ V} ∈ 𝓝 (0 : M) :=
    (Completion.continuous_coe M).continuousAt.preimage_mem_nhds
      (by simpa only [Completion.coe_zero] using hV)
  obtain ⟨P, hPopen, hPsub⟩ :=
    (IsLinearTopology.hasBasis_open_submodule R).mem_iff.mp hVM
  have hQopen : IsOpen (N.mkQ '' (P : Set M)) :=
    QuotientAddGroup.isOpenMap_coe (P : Set M) hPopen
  obtain ⟨W, hWopen, hWpre⟩ :=
    (Completion.isUniformInducing_coe (M ⧸ N)).isInducing.isOpen_iff.mp hQopen
  have hWzero : (0 : TopologicalCompletion (M ⧸ N)) ∈ W := by
    have h0 : (0 : M ⧸ N) ∈ N.mkQ '' (P : Set M) :=
      ⟨0, P.zero_mem, by simp⟩
    rw [← hWpre] at h0
    simpa only [Set.mem_preimage, Completion.coe_zero] using h0
  have hnear : {y : TopologicalCompletion M | y - x ∈ V} ∈ 𝓝 x := by
    have h : ContinuousAt (fun y : TopologicalCompletion M => y - x) x := by fun_prop
    exact h.preimage_mem_nhds (by simpa using hV)
  have hmap : (completionQuotient N) ⁻¹' W ∈ 𝓝 x := by
    have hWnhds : W ∈ 𝓝 (completionQuotient N x) := by
      rw [hx]
      exact hWopen.mem_nhds hWzero
    exact (Completion.continuous_map (f := N.mkQ)).continuousAt.preimage_mem_nhds hWnhds
  obtain ⟨g, hgnear, hgmap⟩ :=
    (Completion.denseRange_coe (α := M)).mem_nhds (Filter.inter_mem hnear hmap)
  have hgQ : N.mkQ g ∈ N.mkQ '' (P : Set M) := by
    have hgw : ((N.mkQ g : M ⧸ N) : TopologicalCompletion (M ⧸ N)) ∈ W := by
      rwa [mem_preimage, completionQuotient_coe] at hgmap
    change N.mkQ g ∈ (Completion.coe' : M ⧸ N → Completion (M ⧸ N)) ⁻¹' W at hgw
    rwa [hWpre] at hgw
  obtain ⟨p, hpP, hgp⟩ := hgQ
  have hgn : g - p ∈ N := by
    apply (Submodule.Quotient.mk_eq_zero N).mp
    have : N.mkQ (g - p) = 0 := by rw [map_sub, hgp, sub_self]
    simpa using this
  refine ⟨((g - p : M) : TopologicalCompletion M),
    ⟨⟨g - p, hgn⟩, rfl⟩, ?_⟩
  have := hVV ((g : TopologicalCompletion M) - x) hgnear
    (p : TopologicalCompletion M) (hPsub hpP)
  rw [Completion.coe_sub]
  convert this using 1
  abel

omit [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R M] in
private lemma isClosed_range_completionSubtype (N : Submodule R M) :
    IsClosed (range (completionSubtype N)) :=
  (isUniformInducing_completionSubtype N).isComplete_range.isClosed

/-- The image of the completed submodule is the closure of the image of the submodule. -/
private lemma range_completionSubtype_eq_closure_aux {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] (N : Submodule R M) :
    range (completionSubtype N) =
      closure (range fun x : N ↦ (x.1 : TopologicalCompletion M)) := by
  let : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  refine Subset.antisymm ?_ (closure_minimal ?_ (isClosed_range_completionSubtype N))
  · rintro _ ⟨x, rfl⟩
    refine Completion.induction_on x (isClosed_closure.preimage Completion.continuous_map) ?_
    intro x
    rw [completionSubtype_coe]
    exact subset_closure ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, completionSubtype_coe N x⟩

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- **Stacks Project, Tag 0ARZ, part (1).** The image of the completed
submodule is the kernel of the map from the completed module to the completion
of its quotient. -/
@[stacks 0ARZ "part (1), exactness"]
public lemma exact_completionSubtype_completionQuotient (N : Submodule R M) :
    range (completionSubtype N) =
      {x | completionQuotient N x = (0 : M ⧸ N)} := by
  let : UniformSpace N := IsTopologicalAddGroup.rightUniformSpace N
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  let : UniformSpace (M ⧸ N) :=
    IsTopologicalAddGroup.rightUniformSpace (M ⧸ N)
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    refine Completion.induction_on z ?_ ?_
    · show IsClosed ((completionQuotient N ∘ completionSubtype N) ⁻¹'
        {(0 : TopologicalCompletion (M ⧸ N))})
      exact isClosed_singleton.preimage
        (Completion.continuous_map.comp Completion.continuous_map)
    · intro n
      show completionQuotient N (completionSubtype N
        (n : TopologicalCompletion N)) = (0 : TopologicalCompletion (M ⧸ N))
      rw [completionSubtype_coe, completionQuotient_coe,
        Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr n.2, Completion.coe_zero]
  · intro x hx
    rw [range_completionSubtype_eq_closure_aux]
    exact kernel_completionQuotient_subset_closure N hx

omit [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R M] in
/-- **Stacks Project, Tag 0ARZ, part (2).** In the completion of a linearly
topologized module, the image of the completion of a submodule is precisely the
closure of the image of that submodule. -/
@[stacks 0ARZ "part (2)"]
public lemma range_completionSubtype_eq_closure (N : Submodule R M) :
    range (completionSubtype N) =
      closure (range fun x : N ↦ (x.1 : TopologicalCompletion M)) :=
  range_completionSubtype_eq_closure_aux N

end

section

open Filter Topology UniformSpace

universe u v

variable {R : Type u} {M : Type v}
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [IsLinearTopology R M]

private lemma topologicalCompletion_firstCountable
    {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (hM : (nhds (0 : M)).IsCountablyGenerated) :
    FirstCountableTopology (TopologicalRing.TopologicalCompletion M) := by
  have : IsCountablyGenerated (nhds (0 : M)) := hM
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  have : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  have : IsCountablyGenerated (uniformity M) :=
    IsUniformAddGroup.uniformity_countably_generated
  have : IsCountablyGenerated (uniformity (CauchyFilter M)) := by
    obtain ⟨s, hs⟩ := (uniformity M).exists_antitone_basis
    exact (CauchyFilter.basis_uniformity hs.toHasBasis).isCountablyGenerated
  have : IsCountablyGenerated (uniformity (TopologicalRing.TopologicalCompletion M)) := by
    show IsCountablyGenerated ((uniformity (CauchyFilter M)).map
      (Prod.map SeparationQuotient.mk SeparationQuotient.mk))
    infer_instance
  exact UniformSpace.firstCountableTopology _

omit [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R M] in
private lemma completionQuotient_surjective_and_open
    (N : Submodule R M) (hM : (nhds (0 : M)).IsCountablyGenerated) :
    Function.Surjective (TopologicalRing.completionQuotient N) ∧
      IsOpenMap (TopologicalRing.completionQuotient N) := by
  let : UniformSpace M := IsTopologicalAddGroup.rightUniformSpace M
  let : UniformSpace (M ⧸ N) :=
    IsTopologicalAddGroup.rightUniformSpace (M ⧸ N)
  have : IsUniformAddGroup M := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup (M ⧸ N) := isUniformAddGroup_of_addCommGroup
  let A := TopologicalRing.TopologicalCompletion M
  let B := TopologicalRing.TopologicalCompletion (M ⧸ N)
  let q₀ : M →+ M ⧸ N := N.mkQ.toAddMonoidHom
  have hq₀cont : Continuous q₀ := N.continuous_mkQ
  let f : A →+ B := q₀.completion hq₀cont
  have hfcont : Continuous f :=
    AddMonoidHom.continuous_completion q₀ hq₀cont
  have hf_coe (m : M) : f (m : A) = (N.mkQ m : B) :=
    AddMonoidHom.completion_coe q₀ hq₀cont m
  have hf (x : A) : f x = TopologicalRing.completionQuotient N x := by
    refine Completion.induction_on x ?_ ?_
    · exact isClosed_eq hfcont Completion.continuous_map
    · intro m
      rw [hf_coe, completionQuotient_coe]
  let K : AddSubgroup A := f.ker
  have hKclosed : IsClosed (K : Set A) := by
    show IsClosed (f ⁻¹' ({0} : Set B))
    exact isClosed_singleton.preimage hfcont
  have : IsClosed (K : Set A) := hKclosed
  let Q := A ⧸ K
  let q : A →+ Q := QuotientAddGroup.mk' K
  let u : M →+ Q := q.comp (Completion.toCompl (α := M))
  have hN : N.toAddSubgroup ≤ u.ker := by
    intro m hm
    rw [AddMonoidHom.mem_ker]
    dsimp [u]
    show (Completion.toCompl (α := M) m : A ⧸ K) = 0
    rw [QuotientAddGroup.eq_zero_iff]
    show f (m : A) = 0
    rw [hf_coe]
    show (N.mkQ m : B) = 0
    rw [← Completion.coe_zero]
    congr 1
    exact (Submodule.Quotient.mk_eq_zero N).2 hm
  let g : M ⧸ N →+ Q := QuotientAddGroup.lift N.toAddSubgroup u hN
  have hgcont : Continuous g := by
    apply (N.isQuotientMap_mkQ).continuous_iff.mpr
    show Continuous u
    dsimp [u]
    exact (QuotientAddGroup.continuous_mk.comp Completion.continuous_toCompl)
  have : FirstCountableTopology A := topologicalCompletion_firstCountable hM
  have : FirstCountableTopology Q := QuotientAddGroup.instFirstCountableTopology K
  let : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
  have : IsUniformAddGroup Q := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace Q := QuotientAddGroup.completeSpace_right A K
  let c : Q →+ B := QuotientAddGroup.lift K f le_rfl
  have hccont : Continuous c := (QuotientAddGroup.isQuotientMap_mk K).continuous_iff.mpr hfcont
  let b : B →+ Q := g.extension hgcont
  have hbcont : Continuous b := AddMonoidHom.continuous_extension g hgcont
  have hcb : ∀ y : B, c (b y) = y := by
    intro y
    refine Completion.induction_on y ?_ ?_
    · exact isClosed_eq (hccont.comp hbcont) continuous_id
    · intro z
      obtain ⟨m, rfl⟩ := N.mkQ_surjective z
      rw [AddMonoidHom.extension_coe]
      calc
        c (g (N.mkQ m)) = c (u m) := congrArg c
          (QuotientAddGroup.lift_mk N.toAddSubgroup hN m)
        _ = c (q (m : A)) := rfl
        _ = f (m : A) := QuotientAddGroup.lift_mk K le_rfl (m : A)
        _ = (N.mkQ m : B) := hf_coe m
  have hbq : ∀ x : A, b (c (q x)) = q x := by
    intro x
    refine Completion.induction_on x ?_ ?_
    · exact isClosed_eq ((hbcont.comp hccont).comp QuotientAddGroup.continuous_mk)
        QuotientAddGroup.continuous_mk
    · intro m
      calc
        b (c (q (m : A))) = b (f (m : A)) := congrArg b
          (QuotientAddGroup.lift_mk K le_rfl (m : A))
        _ = b (N.mkQ m : B) := congrArg b (hf_coe m)
        _ = g (N.mkQ m) := AddMonoidHom.extension_coe g hgcont (N.mkQ m)
        _ = u m := QuotientAddGroup.lift_mk N.toAddSubgroup hN m
        _ = q (Completion.toCompl (α := M) m) := rfl
  have heq : TopologicalRing.completionQuotient N = c ∘ (QuotientAddGroup.mk' K) := by
    funext x
    rw [← hf x]
    exact QuotientAddGroup.lift_mk K le_rfl x
  constructor
  · intro y
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (b y)
    refine ⟨x, ?_⟩
    rw [heq]
    exact (congrArg c (show q x = b y from hx)).trans (hcb y)
  · rw [heq]
    refine (IsOpenMap.of_inverse hbcont hcb fun y ↦ ?_).comp QuotientAddGroup.isOpenMap_coe
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact hbq x

add_to_stacks 0AS0 "part (1), injectivity"
  TopologicalRing.completionSubtype_injective

add_to_stacks 0AS0 "part (1), exactness at the middle term"
  TopologicalRing.exact_completionSubtype_completionQuotient

add_to_stacks 0AS0 "part (2)"
  TopologicalRing.range_completionSubtype_eq_closure

omit [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R M] in
/-- **Stacks Project, Tag 0AS0, part (1).** For a linearly topologized module
with a countable fundamental system of neighborhoods of zero, the canonical
map from its completion to the completion of a quotient is surjective. -/
@[stacks 0AS0 "part (1), surjectivity"]
public lemma completionQuotient_surjective_of_isCountablyGenerated
    (N : Submodule R M) (hM : (nhds (0 : M)).IsCountablyGenerated) :
    Function.Surjective (TopologicalRing.completionQuotient N) :=
  (completionQuotient_surjective_and_open N hM).1

omit [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R M] in
/-- **Stacks Project, Tag 0AS0, part (3).** For a linearly topologized module
with a countable fundamental system of neighborhoods of zero, the canonical
map from its completion to the completion of a quotient is open. -/
@[stacks 0AS0 "part (3)"]
public lemma completionQuotient_isOpenMap_of_isCountablyGenerated
    (N : Submodule R M) (hM : (nhds (0 : M)).IsCountablyGenerated) :
    IsOpenMap (TopologicalRing.completionQuotient N) :=
  (completionQuotient_surjective_and_open N hM).2

end

section

open scoped Topology

private lemma recurrence_bijective (A : Type*) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A]
    [@CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A)] [T2Space A]
    {f : A} (hf : IsTopologicallyNilpotent f) :
    Function.Bijective (fun a : ℕ → A ↦ fun n ↦ a n - f • a (n + 1)) := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let : NonarchimedeanAddGroup A := {
    toIsTopologicalAddGroup := inferInstance
    is_nonarchimedean U hU := by
      rcases IsLinearTopology.hasBasis_open_ideal.mem_iff.mp hU with ⟨J, hJ, hJU⟩
      exact ⟨⟨J.toAddSubgroup, hJ⟩, hJU⟩
  }
  constructor
  · intro a b hab
    funext n
    have hrec : ∀ k, a n - b n = f ^ k * (a (n + k) - b (n + k)) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [ih, pow_succ, Nat.add_succ, mul_assoc]
          congr 1
          have h := congrFun hab (n + k)
          simp only [smul_eq_mul] at h
          linear_combination h
    have ht : Filter.Tendsto (fun k ↦ f ^ k * (a (n + k) - b (n + k)))
        Filter.atTop (𝓝 0) :=
      IsLinearTopology.tendsto_mul_zero_of_left _ _ hf
    have ht' : Filter.Tendsto (fun _ : ℕ ↦ a n - b n) Filter.atTop (𝓝 0) :=
      ht.congr' (Filter.Eventually.of_forall fun k ↦ (hrec k).symm)
    exact sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds ht')
  · intro b
    let a : ℕ → A := fun n ↦ ∑' k : ℕ, f ^ k * b (n + k)
    have hs : ∀ n, Summable (fun k : ℕ ↦ f ^ k * b (n + k)) := by
      intro n
      apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      rw [Nat.cofinite_eq_atTop]
      exact IsLinearTopology.tendsto_mul_zero_of_left _ _ hf
    refine ⟨a, funext fun n ↦ ?_⟩
    show a n - f * a (n + 1) = b n
    dsimp only [a]
    have htail := (hs n).sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
      one_mul] at htail
    rw [← htail, ← (hs (n + 1)).tsum_mul_left f]
    apply sub_eq_iff_eq_add.mpr
    congr 1
    apply tsum_congr
    intro k
    rw [pow_succ', show n + (k + 1) = n + 1 + k by omega]
    ring

/-- **Stacks Project, Tag 0DCZ.** A weak ideal of definition in a weakly
admissible topological ring forms a henselian pair with the ring. -/
@[stacks 0DCZ, ega "0 7.1.10"]
theorem henselianPair_of_isWeaklyAdmissible
    (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    HenselianPair A I := by
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  let : CompleteSpace A := hA.2.1
  let : T2Space A := hA.2.2
  apply PrincipalHenselianPair.henselianPair_of_isDerivedCompleteModule A I
  rw [bijective_recurrence_iff_isDerivedCompleteModule]
  intro f hf
  exact recurrence_bijective A (hI.2 f hf)

end

end TopologicalRing

end

@[expose] public section

namespace TopologicalRing

section ClosureOfSubmodule

universe u v

open Filter Topology

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [IsLinearTopology R M]

omit [IsLinearTopology R M] in
/-- The sum of a submodule with an open submodule of a topological module is open. -/
public lemma isOpen_sup_of_isOpen_right {N L : Submodule R M} (hL : IsOpen (L : Set M)) :
    IsOpen ((N ⊔ L : Submodule R M) : Set M) :=
  AddSubgroup.isOpen_mono
    (show L.toAddSubgroup ≤ (N ⊔ L : Submodule R M).toAddSubgroup from
      fun _ hx ↦ Submodule.mem_sup_right hx) hL

/-- A point of a linearly topologized module lies in the closure of a submodule `N` exactly
when it lies in `N ⊔ L` for every open submodule `L`. -/
public theorem mem_closure_iff_forall_sup_isOpen (N : Submodule R M) (x : M) :
    x ∈ closure (N : Set M) ↔ ∀ L : Submodule R M, IsOpen (L : Set M) → x ∈ N ⊔ L := by
  refine ⟨fun hx L hL ↦ ?_, fun h ↦ ?_⟩
  · refine closure_minimal (show (N : Set M) ⊆ ((N ⊔ L : Submodule R M) : Set M) from
      fun _ hy ↦ Submodule.mem_sup_left hy) ?_ hx
    exact (N ⊔ L : Submodule R M).toAddSubgroup.isClosed_of_isOpen
      (isOpen_sup_of_isOpen_right hL)
  · refine mem_closure_iff_nhds.mpr fun t ht ↦ ?_
    obtain ⟨L, hL, hLt⟩ :=
      ((IsLinearTopology.hasBasis_open_submodule R).nhds_of_zero' x).mem_iff.mp ht
    obtain ⟨j, hj, l, hl, hsum⟩ := Submodule.mem_sup.mp (h L hL)
    refine ⟨j, hLt ⟨-l, L.neg_mem hl, ?_⟩, hj⟩
    simpa only [vadd_eq_add, sub_eq_add_neg] using (show x + -l = j by rw [← hsum]; abel)

/-- **Stacks Project, Tag 0AMS.** Let `M` be a linearly topologized `R`-module and let
`L i`, `i : ι`, be a fundamental system of open submodules of `M`. The closure of a submodule
`N ⊆ M` is the intersection of the submodules `N + L i`. -/
@[stacks 0AMS]
public theorem closure_eq_iInter_sup_of_hasBasis {ι : Sort*} (L : ι → Submodule R M)
    (hopen : ∀ i, IsOpen ((L i : Set M)))
    (hbasis : (𝓝 (0 : M)).HasBasis (fun _ : ι ↦ True) fun i ↦ ((L i : Set M)))
    (N : Submodule R M) :
    closure (N : Set M) = ⋂ i, ((N ⊔ L i : Submodule R M) : Set M) := by
  ext x
  simp only [Set.mem_iInter, SetLike.mem_coe, mem_closure_iff_forall_sup_isOpen]
  refine ⟨fun h i ↦ h (L i) (hopen i), fun h K hK ↦ ?_⟩
  obtain ⟨i, -, hiK⟩ := hbasis.mem_iff.mp (hK.mem_nhds K.zero_mem)
  exact sup_le_sup_left (show L i ≤ K from fun _ hy ↦ hiK hy) N (h i)

/-- **Stacks Project, Tag 0AMS**, as an equality of submodules: the topological closure of a
submodule `N` is the infimum of the submodules `N + L i` over a fundamental system `L i` of open
submodules. -/
@[stacks 0AMS "the same identity read as an equality of submodules"]
public theorem topologicalClosure_eq_iInf_sup_of_hasBasis [ContinuousConstSMul R M]
    {ι : Sort*} (L : ι → Submodule R M)
    (hopen : ∀ i, IsOpen ((L i : Set M)))
    (hbasis : (𝓝 (0 : M)).HasBasis (fun _ : ι ↦ True) fun i ↦ ((L i : Set M)))
    (N : Submodule R M) :
    N.topologicalClosure = ⨅ i, (N ⊔ L i : Submodule R M) := by
  refine SetLike.coe_injective ?_
  rw [Submodule.topologicalClosure_coe,
    closure_eq_iInter_sup_of_hasBasis L hopen hbasis N, Submodule.coe_iInf]

end ClosureOfSubmodule

section

universe u v

/-- **Stacks Project, Tag 0AMT.** The quotient of a linearly topologized module by a closed
submodule is separated; this is the Hausdorff half of the completeness of `M ⧸ N`. -/
@[stacks 0AMT "the quotient is separated"]
public lemma t2Space_quotient_of_isClosed {R : Type u} {M : Type v}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [IsLinearTopology R M] (N : Submodule R M) (hN : IsClosed (N : Set M)) :
    T2Space (M ⧸ N) := by
  have : IsClosed (N : Set M) := hN
  infer_instance

/-- **Stacks Project, Tag 0AMT.** The quotient of a complete, linearly topologized module with a
countable fundamental system of neighbourhoods of zero by a submodule is itself complete for the
canonical uniformity of a topological additive group. -/
@[stacks 0AMT "the quotient is complete"]
public lemma completeSpace_quotient_of_isCountablyGenerated {R : Type u} {M : Type v}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [IsLinearTopology R M] (N : Submodule R M)
    (hM : @CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M))
    (hcount : (nhds (0 : M)).IsCountablyGenerated) :
    @CompleteSpace (M ⧸ N) (IsTopologicalAddGroup.rightUniformSpace (M ⧸ N)) := by
  have : Filter.IsCountablyGenerated (nhds (0 : M)) := hcount
  have : FirstCountableTopology M := by
    refine ⟨fun a => ?_⟩
    rw [← nhds_translation_add_neg a]
    infer_instance
  have : @CompleteSpace M (IsTopologicalAddGroup.rightUniformSpace M) := hM
  exact QuotientAddGroup.completeSpace_right' M N.toAddSubgroup

/-! The third assertion of Tag 0AMT, that `M → M ⧸ N` is open, holds for the quotient topology
on any topological module and is `Submodule.isOpenMap_mkQ`. -/
add_to_stacks 0AMT "the map to the quotient is open" Submodule.isOpenMap_mkQ

end

end TopologicalRing

end
