module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.SetTheory.ZFC.PSet
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Refining partitions by good stratifications

A partition of a topological space $X$ is a decomposition $X = \coprod_{i \in I} X_i$ into
pairwise disjoint locally closed subsets. It is a good stratification if for all $i, j$,
$X_i \cap \overline{X_j} \neq \emptyset$ implies $X_i \subseteq \overline{X_j}$. We show that
every finite partition of a Noetherian topological space is refined by a finite good
stratification.

## Main definitions

* `TopPartitionOpenCover`: A partition of a topological space into pairwise disjoint locally
  closed subsets.
* `TopPartitionOpenCover.IsFinite`: The partition has a finite index type.
* `TopPartitionOpenCover.Refines`: Every part of one partition is contained in a part of another.
* `TopPartitionOpenCover.IsGood`: The partition is a good stratification.

## Main results

* `main_theorem09Y5`: Every finite partition of a Noetherian topological space is refined by a
  finite good stratification.

## References

* [Stacks Project, Section 5.28][stacks-project]
-/

@[expose] public section

universe u v w

/-- A *partition* of a topological space `X`: an indexed family of pairwise disjoint locally closed
subsets whose union covers `X`. The index type `ι` is part of the data. -/
structure TopPartitionOpenCover (X : Type u) [TopologicalSpace X] where
  /-- The index type of the partition. -/
  ι : Type v
  /-- The parts of the partition, indexed by `ι`. -/
  parts : ι → Set X
  /-- Each part is locally closed in `X`. -/
  locallyClosed : ∀ i, IsLocallyClosed (parts i)
  /-- The parts are pairwise disjoint. -/
  pairwiseDisjoint : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (parts i) (parts j)
  /-- The parts cover `X`. -/
  covers : ⋃ i, parts i = Set.univ

namespace TopPartitionOpenCover

variable {X : Type u} [TopologicalSpace X]

/-- A partition is *finite* if its index type is finite. -/
abbrev IsFinite (P : TopPartitionOpenCover.{u, v} X) : Prop :=
  Finite P.ι

/-- A partition `P'` *refines* a partition `P` if every part of `P'` is contained in some part of
`P`. -/
def Refines (P' : TopPartitionOpenCover.{u, v} X)
    (P : TopPartitionOpenCover.{u, w} X) : Prop :=
  ∀ j, ∃ i, P'.parts j ⊆ P.parts i

/-- A *good stratification* of `X` is a partition such that for all indices `i, j`, if the `i`-th
part meets the closure of the `j`-th part, then the `i`-th part is contained in the closure of the
`j`-th part. -/
def IsGood (P : TopPartitionOpenCover.{u, v} X) : Prop :=
  ∀ i j, (P.parts i ∩ closure (P.parts j)).Nonempty →
    P.parts i ⊆ closure (P.parts j)

end TopPartitionOpenCover

/-- Transport a partition along a homeomorphism by taking images of its parts. -/
private def mapHomeomorph {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] (e : Y ≃ₜ Z)
    (R : TopPartitionOpenCover.{u, v} Y) : TopPartitionOpenCover.{u, v} Z where
  ι := R.ι
  parts i := e '' R.parts i
  locallyClosed i := (R.locallyClosed i).image e.isInducing
    (by rw [Homeomorph.range_coe]; exact isOpen_univ.isLocallyClosed)
  pairwiseDisjoint i j hij := Set.disjoint_image_of_injective e.injective (R.pairwiseDisjoint hij)
  covers := by rw [← Set.image_iUnion, R.covers, Set.image_univ, Homeomorph.range_coe]

/-- Transporting a good stratification along a homeomorphism gives a good stratification. -/
private theorem isGood_mapHomeomorph {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
    (e : Y ≃ₜ Z) {R : TopPartitionOpenCover.{u, v} Y} (h : R.IsGood) :
    (mapHomeomorph e R).IsGood := by
  rintro i j ⟨_, ⟨a, ha, rfl⟩, hx⟩
  change e a ∈ closure (e '' R.parts j) at hx
  rw [← e.image_closure] at hx
  rw [show closure ((mapHomeomorph e R).parts j) = e '' closure (R.parts j) from
    (e.image_closure _).symm]
  exact Set.image_mono (h i j ⟨a, ha, e.injective.mem_set_image.mp hx⟩)

/-- If `R'` refines the transport of `Q` along `e`, then `R'` transported back along `e.symm`
refines `Q`. -/
private theorem refines_symm_mapHomeomorph {Y Z : Type u} [TopologicalSpace Y]
    [TopologicalSpace Z] (e : Y ≃ₜ Z) {R' : TopPartitionOpenCover.{u, u} Z}
    {Q : TopPartitionOpenCover.{u, u} Y} (h : R'.Refines (mapHomeomorph e Q)) :
    (mapHomeomorph e.symm R').Refines Q := fun j => by
  obtain ⟨k, hk⟩ := h j
  exact ⟨k, (Set.image_mono hk).trans (e.symm_image_image _).subset⟩

/-- If a nonempty Noetherian space is the union of finitely many locally closed sets, then one of
them contains a nonempty open subset. -/
lemma exists_nonempty_open_subset_part {X : Type u}
    [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    {ι : Type u} [Finite ι] (parts : ι → Set X)
    (hlc : ∀ i, IsLocallyClosed (parts i))
    (hcov : ⋃ i, parts i = Set.univ)
    (hne : Nonempty X) :
    ∃ (i : ι) (U : Set X),
      IsOpen U ∧ U.Nonempty ∧ U ⊆ parts i := by
  obtain ⟨x⟩ := hne
  set C := irreducibleComponent x
  have hCirr : IsIrreducible C := isIrreducible_irreducibleComponent
  have hCclosed : IsClosed C := isClosed_irreducibleComponent
  have hCne : C.Nonempty := ⟨x, mem_irreducibleComponent⟩
  have hCcov : C ⊆ ⋃ i, parts i := hcov ▸ Set.subset_univ C
  cases nonempty_fintype ι
  have hCcov_cl : C ⊆ ⋃ i, closure (C ∩ parts i) := by
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hCcov hy)
    exact Set.mem_iUnion.mpr ⟨i, subset_closure ⟨hy, hi⟩⟩
  have hcov_finset : C ⊆ ⋃₀ ↑(Finset.univ.image (fun i => closure (C ∩ parts i))) := by
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hCcov_cl hy)
    exact Set.mem_sUnion.mpr ⟨_, Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _,
        rfl⟩), hi⟩
  obtain ⟨w, hw, hCw⟩ := isIrreducible_iff_sUnion_isClosed.mp hCirr _ (fun w hw => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact isClosed_closure) hcov_finset
  obtain ⟨i₀, _, rfl⟩ := Finset.mem_image.mp hw
  have hcl_eq : closure (C ∩ parts i₀) = C :=
    le_antisymm (hCclosed.closure_subset_iff.mpr Set.inter_subset_left) hCw
  obtain ⟨V, F, hV, hF, hparts_eq⟩ := hlc i₀
  have hCF : C ⊆ F := by
    calc C = closure (C ∩ parts i₀) := hcl_eq.symm
      _ ⊆ closure F := closure_mono (fun y ⟨_, h⟩ => (hparts_eq ▸ h).2)
      _ = F := hF.closure_eq
  have hCV_sub : C ∩ V ⊆ parts i₀ := fun y ⟨hyC, hyV⟩ => hparts_eq ▸ ⟨hyV, hCF hyC⟩
  have hcl_CV : closure (C ∩ V) = C := by
    apply le_antisymm (hCclosed.closure_subset_iff.mpr Set.inter_subset_left)
    calc C = closure (C ∩ parts i₀) := hcl_eq.symm
      _ ⊆ closure (C ∩ V) := closure_mono (fun y ⟨hyC, hyP⟩ => ⟨hyC, (hparts_eq ▸ hyP).1⟩)
  have hCV_ne : (C ∩ V).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, closure_empty] at hcl_CV
    exact hCne.ne_empty hcl_CV.symm
  have hCirr_sUnion := isIrreducible_iff_sUnion_isClosed.mp hCirr
  have hfin_comp := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have hfin_diff := hfin_comp.subset (Set.sdiff_subset (s := irreducibleComponents X) (t := {C}))
  have hothers_closed : IsClosed (⋃₀ (irreducibleComponents X \ {C})) := by
    have := hfin_diff.to_subtype
    rw [Set.sUnion_eq_iUnion]
    exact isClosed_iUnion_of_finite fun ⟨s, hs⟩ =>
      ((irreducibleComponents_eq_maximals_closed X ▸ ((Set.mem_sdiff _).mp hs).1)).1.1
  set W := (⋃₀ (irreducibleComponents X \ {C}))ᶜ
  have hW_open : IsOpen W := hothers_closed.isOpen_compl
  have hW_sub_C : W ⊆ C := by
    intro y hy
    have hy_comp : y ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]
      exact Set.mem_univ y
    obtain ⟨D, hD, hyD⟩ := Set.mem_sUnion.mp hy_comp
    have hD_eq_C : D = C := by
      by_contra hne_DC
      have : D ∈ irreducibleComponents X \ {C} :=
        Set.mem_sdiff_of_mem hD (Set.mem_singleton_iff.not.mpr hne_DC)
      exact hy (Set.mem_sUnion.mpr ⟨D, this, hyD⟩)
    exact hD_eq_C ▸ hyD
  have hCW_ne : (C ∩ W).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hC_sub_others : C ⊆ ⋃₀ (irreducibleComponents X \ {C}) := by
      intro y hy
      by_contra hy_not
      exact (h ▸ (⟨hy, hy_not⟩ : y ∈ C ∩ W) : y ∈ (∅ : Set X))
    set S := hfin_diff.toFinset
    have hcov_S : C ⊆ ⋃₀ ↑S := Set.Finite.coe_toFinset hfin_diff ▸ hC_sub_others
    obtain ⟨D, hD, hCD⟩ := hCirr_sUnion S (fun z hz => by
      rw [Set.Finite.mem_toFinset] at hz
      exact ((irreducibleComponents_eq_maximals_closed X ▸ ((Set.mem_sdiff _).mp hz).1)).1.1) hcov_S
    rw [Set.Finite.mem_toFinset] at hD
    have hD_ne_C : D ≠ C := fun heq => ((Set.mem_sdiff _).mp hD).2 (Set.mem_singleton_iff.mpr heq)
    have hD_irr : IsIrreducible D := ((Set.mem_sdiff _).mp hD).1 |>.1
    have hC_max : Maximal IsIrreducible C := irreducibleComponent_mem_irreducibleComponents x
    exact hD_ne_C (le_antisymm hCD (hC_max.2 hD_irr hCD)).symm
  have hWV_ne : (C ∩ (W ∩ V)).Nonempty := hCirr.2 W V hW_open hV hCW_ne hCV_ne
  exact ⟨i₀, W ∩ V, hW_open.inter hV, hWV_ne.mono Set.inter_subset_right,
    fun y ⟨hyW, hyV⟩ => hCV_sub ⟨hW_sub_C hyW, hyV⟩⟩

/-- Given a finite partition of `X` into pairwise disjoint locally closed sets and a subset `U`,
there is a finite partition of `Uᶜ` each of whose parts lies in a part of the given partition and
is either contained in or disjoint from `closure U`. -/
lemma split_partition_on_complement {X : Type u}
    [TopologicalSpace X]
    {ι : Type u} [Finite ι] (parts : ι → Set X)
    (hlc : ∀ i, IsLocallyClosed (parts i))
    (hpd : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (parts i) (parts j))
    (hcov : ⋃ i, parts i = Set.univ)
    (U : Set X) :
    ∃ (Q : TopPartitionOpenCover.{u, u} ↥Uᶜ),
      Q.IsFinite ∧
      (∀ j, ∃ i, (Subtype.val '' Q.parts j) ⊆ parts i) ∧
      (∀ j, (Subtype.val '' Q.parts j) ⊆ closure U ∨
        Disjoint (Subtype.val '' Q.parts j) (closure U)) := by
  let qparts : ι × Bool → Set ↥Uᶜ := fun ⟨i, b⟩ =>
    match b with
    | true => {x : ↥Uᶜ | x.val ∈ parts i ∧ x.val ∈ closure U}
    | false => {x : ↥Uᶜ | x.val ∈ parts i ∧ x.val ∉ closure U}
  have hlc_q : ∀ ib, IsLocallyClosed (qparts ib) := by
    intro ⟨i, b⟩
    have h1 : IsLocallyClosed (Subtype.val ⁻¹' (parts i) : Set ↥Uᶜ) :=
      (hlc i).preimage continuous_subtype_val
    cases b
    · have h2 : IsLocallyClosed ((Subtype.val ⁻¹' (closure U))ᶜ : Set ↥Uᶜ) :=
        (isClosed_closure.preimage continuous_subtype_val).isOpen_compl.isLocallyClosed
      exact h1.inter h2
    · have h2 : IsLocallyClosed (Subtype.val ⁻¹' (closure U) : Set ↥Uᶜ) :=
        isClosed_closure.isLocallyClosed.preimage continuous_subtype_val
      exact h1.inter h2
  have hpd_q : ∀ ⦃ib jb : ι × Bool⦄, ib ≠ jb → Disjoint (qparts ib) (qparts jb) := by
    intro ⟨i, b⟩ ⟨j, c⟩ hne
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    have hij : b = c → i ≠ j := fun hbc h => hne (Prod.ext h hbc)
    cases b <;> cases c <;> simp only [qparts, Set.mem_ofPred_eq] at hxi hxj
    · exact Set.disjoint_left.mp (hpd (hij rfl)) hxi.1 hxj.1
    · exact hxi.2 hxj.2
    · exact hxj.2 hxi.2
    · exact Set.disjoint_left.mp (hpd (hij rfl)) hxi.1 hxj.1
  have hcov_q : ⋃ ib, qparts ib = Set.univ := by
    ext ⟨x, hx⟩
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, qparts]
    have hx_cov : x ∈ ⋃ i, parts i := hcov ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx_cov
    by_cases hcl : x ∈ closure U
    · exact ⟨⟨i, true⟩, hi, hcl⟩
    · exact ⟨⟨i, false⟩, hi, hcl⟩
  let Q : TopPartitionOpenCover.{u, u} ↥Uᶜ := ⟨ι × Bool, qparts, hlc_q, hpd_q, hcov_q⟩
  refine ⟨Q, Finite.instProd, ?_, ?_⟩
  · intro ⟨i, b⟩
    refine ⟨i, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    cases b <;> simp only [Q, qparts, Set.mem_ofPred_eq] at hy <;> exact hy.1
  · intro ⟨i, b⟩
    cases b with
    | true =>
      left
      rintro _ ⟨y, hy, rfl⟩
      simp only [Q, qparts, Set.mem_ofPred_eq] at hy
      exact hy.2
    | false =>
      right
      rw [Set.disjoint_left]
      rintro _ ⟨y, hy, rfl⟩ hx2
      simp only [Q, qparts, Set.mem_ofPred_eq] at hy
      exact hy.2 hx2

/-- Let `U` be an open subset of `X` contained in a part of a finite partition of `X`, and let `Q`
be a finite good stratification of `Uᶜ` whose parts lie in parts of the partition and are each
contained in or disjoint from `closure U`. Then `U` together with the parts of `Q` is a finite good
stratification of `X` refining the partition. -/
lemma combine_open_and_complement_stratification
    {X : Type u} [TopologicalSpace X]
    {ι : Type u} [Finite ι] (parts : ι → Set X)
    (hlc : ∀ i, IsLocallyClosed (parts i))
    (hpd : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (parts i) (parts j))
    (hcov : ⋃ i, parts i = Set.univ)
    (U : Set X) (hUopen : IsOpen U)
    (i₀ : ι)
    (hU_sub : U ⊆ parts i₀)
    (Q : TopPartitionOpenCover.{u, u} ↥Uᶜ)
    (hQfin : Q.IsFinite) (hQgood : Q.IsGood)
    (hQref : ∀ j, ∃ i,
      (Subtype.val '' Q.parts j) ⊆ parts i)
    (hQsplit : ∀ j,
      (Subtype.val '' Q.parts j) ⊆ closure U ∨
      Disjoint (Subtype.val '' Q.parts j) (closure U)) :
    ∃ P' : TopPartitionOpenCover.{u, u} X,
      P'.IsFinite ∧ P'.IsGood ∧ P'.Refines
        (TopPartitionOpenCover.mk ι parts hlc hpd hcov) := by
  have hclosed_Uc : IsClosed (Uᶜ : Set X) := hUopen.isClosed_compl
  have hemb : Topology.IsClosedEmbedding (Subtype.val : ↥Uᶜ → X) :=
    hclosed_Uc.isClosedEmbedding_subtypeVal
  let newParts : Option Q.ι → Set X := fun o =>
    match o with
    | none => U
    | some j => Subtype.val '' Q.parts j
  have hlc_new : ∀ o, IsLocallyClosed (newParts o) := fun
    | none => hUopen.isLocallyClosed
    | some j => (Q.locallyClosed j).image hemb.isInducing hemb.isClosed_range.isLocallyClosed
  have hpd_new : ∀ ⦃o₁ o₂ : Option Q.ι⦄, o₁ ≠ o₂ → Disjoint (newParts o₁) (newParts o₂) := by
    intro o₁ o₂ hne
    match o₁, o₂ with
    | none, none => exact (hne rfl).elim
    | none, some j =>
      apply Set.disjoint_left.mpr
      intro x hxU hxj
      obtain ⟨⟨y, hy⟩, _, rfl⟩ := hxj
      exact hy hxU
    | some j, none =>
      apply Set.disjoint_right.mpr
      intro x hxU hxj
      obtain ⟨⟨y, hy⟩, _, rfl⟩ := hxj
      exact hy hxU
    | some j, some k =>
      have hjk : j ≠ k := fun h => hne (congrArg some h)
      exact Set.disjoint_image_of_injective Subtype.val_injective (Q.pairwiseDisjoint hjk)
  have hcov_new : ⋃ o, newParts o = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hx : x ∈ U
    · exact ⟨none, hx⟩
    · have hxUc : x ∈ Uᶜ := hx
      have hx_mem : (⟨x, hxUc⟩ : ↥Uᶜ) ∈ ⋃ j, Q.parts j := Q.covers ▸ Set.mem_univ _
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx_mem
      exact ⟨some j, ⟨⟨x, hxUc⟩, hj, rfl⟩⟩
  let P' : TopPartitionOpenCover.{u, u} X :=
    ⟨Option Q.ι, newParts, hlc_new, hpd_new, hcov_new⟩
  refine ⟨P', ?_, ?_, ?_⟩
  · have : Finite Q.ι := hQfin
    infer_instance
  · intro o₁ o₂ hne
    match o₁, o₂ with
    | none, none =>
      exact fun _ hx => subset_closure hx
    | none, some j =>
      obtain ⟨x, hxU, hxcl⟩ := hne
      exact (hclosed_Uc.closure_subset_iff.mpr (Subtype.coe_image_subset _ (Q.parts j))
        hxcl hxU).elim
    | some j, none =>
      rcases hQsplit j with h | h
      · exact h
      · obtain ⟨z, hzj, hzcl⟩ := hne
        exact (Set.disjoint_left.mp h hzj hzcl).elim
    | some j, some k =>
      obtain ⟨_, ⟨p, hpj, rfl⟩, hpcl⟩ := hne
      rw [hemb.closure_image_eq] at hpcl ⊢
      exact Set.image_mono (hQgood j k ⟨p, hpj, Subtype.val_injective.mem_set_image.mp hpcl⟩)
  · intro o
    match o with
    | none => exact ⟨i₀, hU_sub⟩
    | some j => exact hQref j

/-- Let `F` be a closed subset of a Noetherian space and `U` a nonempty open subset of `F`.
If every finite partition of every closed subset strictly smaller than `F` is refined by a finite
good stratification, then so is every finite partition of the complement of `U` in `F`. -/
lemma subspace_good_strat_from_smaller_closed
    {X : Type u} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X]
    (F : TopologicalSpace.Closeds X)
    (U : Set ↥F.carrier) (hUopen : IsOpen U)
    (hUne : U.Nonempty)
    (Q : TopPartitionOpenCover.{u, u} ↥Uᶜ) (hQfin : Q.IsFinite)
    (ih : ∀ G < F,
      ∀ (R : TopPartitionOpenCover.{u, u} ↥G.carrier),
        R.IsFinite →
        ∃ R' : TopPartitionOpenCover.{u, u} ↥G.carrier,
          R'.IsFinite ∧ R'.IsGood ∧ R'.Refines R) :
    ∃ Q' : TopPartitionOpenCover.{u, u} ↥Uᶜ,
      Q'.IsFinite ∧ Q'.IsGood ∧ Q'.Refines Q := by
  have hFclosed : IsClosed F.carrier := F.isClosed'
  have hUcClosed : IsClosed (Uᶜ : Set ↥F.carrier) := hUopen.isClosed_compl
  have himg_closed : IsClosed (Subtype.val '' (Uᶜ : Set ↥F.carrier)) :=
    hFclosed.isClosedMap_subtype_val _ hUcClosed
  let G : TopologicalSpace.Closeds X := ⟨Subtype.val '' (Uᶜ : Set ↥F.carrier), himg_closed⟩
  have hG_le : G ≤ F := fun x hx => by obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx; exact hy
  have hG_lt : G < F := by
    refine lt_of_le_of_ne hG_le ?_
    intro heq
    obtain ⟨⟨x, hxF⟩, hxU⟩ := hUne
    have hxG : x ∈ G.carrier := (heq ▸ le_refl _ : F.carrier ⊆ G.carrier) hxF
    obtain ⟨⟨y, hyF⟩, hyUc, hyx⟩ := hxG
    have heq' : (⟨x, hxF⟩ : ↥F.carrier) = ⟨y, hyF⟩ := Subtype.ext hyx.symm
    rw [heq'] at hxU
    exact hyUc hxU
  have hemb : Topology.IsEmbedding (fun (p : ↥(Uᶜ : Set ↥F.carrier)) => (p.val.val : X)) :=
    Topology.IsEmbedding.comp Topology.IsEmbedding.subtypeVal Topology.IsEmbedding.subtypeVal
  have hrange : Set.range (fun (p : ↥(Uᶜ : Set ↥F.carrier)) => (p.val.val : X)) = G.carrier := by
    ext x
    simp only [Set.mem_range, G, Set.mem_image]
    constructor
    · rintro ⟨⟨⟨y, hyF⟩, hyUc⟩, rfl⟩; exact ⟨⟨y, hyF⟩, hyUc, rfl⟩
    · rintro ⟨⟨y, hyF⟩, hyUc, rfl⟩; exact ⟨⟨⟨y, hyF⟩, hyUc⟩, rfl⟩
  let e : ↥(Uᶜ : Set ↥F.carrier) ≃ₜ ↥G.carrier :=
    (hemb.toHomeomorph).trans (Homeomorph.setCongr hrange)
  obtain ⟨R', hR'fin, hR'good, hR'ref⟩ := ih G hG_lt (mapHomeomorph e Q) hQfin
  exact ⟨mapHomeomorph e.symm R', hR'fin, isGood_mapHomeomorph e.symm hR'good,
    refines_symm_mapHomeomorph e hR'ref⟩

/-- For every closed subset `F` of a Noetherian space, every finite partition of `F` is refined by
a finite good stratification. -/
lemma good_stratification_induction {X : Type u}
    [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X]
    (F : TopologicalSpace.Closeds X)
    (Q : TopPartitionOpenCover.{u, u} ↥F.carrier)
    (hQfin : Q.IsFinite) :
    ∃ Q' : TopPartitionOpenCover.{u, u} ↥F.carrier,
      Q'.IsFinite ∧ Q'.IsGood ∧ Q'.Refines Q := by
  apply (TopologicalSpace.instWellFoundedLTClosedsOfNoetherianSpace (α := X)).wf.induction
    (C := fun F => ∀ (Q : TopPartitionOpenCover.{u, u} ↥F.carrier),
      Q.IsFinite →
      ∃ Q' : TopPartitionOpenCover.{u, u} ↥F.carrier,
        Q'.IsFinite ∧ Q'.IsGood ∧ Q'.Refines Q)
    F _ Q hQfin
  intro F ih Q hQfin
  by_cases hF : Nonempty ↥F.carrier
  · have hNoeth : TopologicalSpace.NoetherianSpace ↥F.carrier :=
      TopologicalSpace.NoetherianSpace.set F.carrier
    have hfin : Finite Q.ι := hQfin
    obtain ⟨i₀, U, hUopen, hUne, hU_sub⟩ :=
      exists_nonempty_open_subset_part Q.parts
        Q.locallyClosed Q.covers hF
    obtain ⟨Qsplit, hQsfin, hQsref, hQssplit⟩ :=
      split_partition_on_complement Q.parts Q.locallyClosed Q.pairwiseDisjoint Q.covers U
    obtain ⟨Qgood, hQgfin, hQggood, hQgref⟩ :=
      subspace_good_strat_from_smaller_closed F U hUopen
        hUne Qsplit hQsfin ih
    have hQgref' : ∀ j, ∃ i,
        (Subtype.val '' Qgood.parts j) ⊆ Q.parts i := by
      intro j
      obtain ⟨k, hk⟩ := hQgref j
      obtain ⟨i, hi⟩ := hQsref k
      exact ⟨i, (Set.image_mono hk).trans hi⟩
    have hQgsplit : ∀ j,
        (Subtype.val '' Qgood.parts j) ⊆ closure U ∨
        Disjoint (Subtype.val '' Qgood.parts j)
          (closure U) := by
      intro j
      obtain ⟨k, hk⟩ := hQgref j
      exact (hQssplit k).imp (fun h => (Set.image_mono hk).trans h)
        (fun h => h.mono_left (Set.image_mono hk))
    exact combine_open_and_complement_stratification
      Q.parts Q.locallyClosed Q.pairwiseDisjoint Q.covers
      U hUopen i₀ hU_sub Qgood hQgfin hQggood
      hQgref' hQgsplit
  · refine ⟨Q, hQfin, ?_, fun j => ⟨j, le_rfl⟩⟩
    rintro i j ⟨x, -⟩
    exact (hF ⟨x⟩).elim

/-- Let `X` be a Noetherian topological space. Any finite partition of `X` can be refined by a
finite good stratification of `X`. -/
@[stacks 09Y5]
theorem main_theorem09Y5 (X : Type u) [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X]
    (P : TopPartitionOpenCover.{u, v} X) (hP : P.IsFinite) :
    ∃ P' : TopPartitionOpenCover.{u, u} X,
      P'.IsFinite ∧ P'.IsGood ∧ P'.Refines P := by
  have : Finite P.ι := hP
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin P.ι
  let ι' : Type u := ULift.{u} (Fin n)
  let re : ι' ≃ P.ι := Equiv.ulift.trans e.symm
  let Pu : TopPartitionOpenCover.{u, u} X := {
    ι := ι'
    parts := fun i => P.parts (re i)
    locallyClosed := fun i => P.locallyClosed (re i)
    pairwiseDisjoint := by
      intro i j hij
      exact P.pairwiseDisjoint
        (fun h => hij (re.injective h))
    covers := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      have hx := (P.covers ▸ Set.mem_univ x :
        x ∈ ⋃ i, P.parts i)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨re.symm i, by simp [hi]⟩
  }
  have hPufin : Pu.IsFinite := Finite.of_equiv _ re.symm
  let F : TopologicalSpace.Closeds X := ⊤
  have hFcarr : F.carrier = Set.univ :=
    TopologicalSpace.Closeds.coe_top
  let Q : TopPartitionOpenCover.{u, u} ↥F.carrier := {
    ι := ι'
    parts := fun i => Subtype.val ⁻¹' (Pu.parts i)
    locallyClosed := fun i =>
      (Pu.locallyClosed i).preimage continuous_subtype_val
    pairwiseDisjoint := fun {i j} hij =>
      (Pu.pairwiseDisjoint hij).preimage _
    covers := by
      ext ⟨x, hx⟩
      simp only [Set.mem_iUnion, Set.mem_preimage,
        Set.mem_univ, iff_true]
      exact Set.mem_iUnion.mp
        (Pu.covers ▸ Set.mem_univ x)
  }
  have hQfin : Q.IsFinite := hPufin
  obtain ⟨Q', hQ'fin, hQ'good, hQ'ref⟩ :=
    good_stratification_induction F Q hQfin
  let e' : ↥F.carrier ≃ₜ X := (Homeomorph.setCongr hFcarr).trans (Homeomorph.Set.univ X)
  have he_val : ∀ (a : ↥F.carrier), (e' a : X) = a.val := fun a => by
    simp [e', Homeomorph.setCongr, Homeomorph.Set.univ, Homeomorph.trans_apply,
          Set.equivOfEq, Equiv.Set.univ, Equiv.subtypeEquivProp]
  refine ⟨mapHomeomorph e' Q', hQ'fin, isGood_mapHomeomorph e' hQ'good, ?_⟩
  · intro j
    obtain ⟨k, hk⟩ := hQ'ref j
    refine ⟨re k, ?_⟩
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    have haQ : a ∈ Q.parts k := hk ha
    simp only [Q, Set.mem_preimage] at haQ
    rw [he_val]
    exact haQ

