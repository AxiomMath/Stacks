module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.NoetherianStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.PartitionPieceComparison
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ConstructibleReduction
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedComparison
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedIrreducible
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen
public import StacksFrontier.Topology.Irreducible.LocallyClosedCoverParts
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smooth irreducible stratifications with a closed filtration

A scheme `X` of finite type over a perfect field `k` has, refining any given constructible
stratification, a constructible stratification whose strata are irreducible and smooth over `k`
and are the successive differences of a decreasing chain of closed subsets
`X = Y 0 ⊇ Y 1 ⊇ ⋯ ⊇ Y n = ∅`. The `t`-th stratum is then open in `Y t`, with closed complement
`Y (t + 1)`.

## Main definitions

* `AlgebraicGeometry.ConstructibleStratification.ClosedFiltration`: a closed filtration of `X`
  whose successive differences are the reduced strata of a given stratification of `X`.
* `AlgebraicGeometry.ConstructibleStratification.ClosedFiltration.stage`, `.stageInclusion`,
  `.stageSucc`, `.stageOpen`, `.stageOpenObj` and `.stageOpenInclusion`: the members of the
  filtration as reduced closed subschemes of `X`, the closed immersion of each member into the
  previous one, and the open complement of each member in the previous one.
* `AlgebraicGeometry.ConstructibleStratification.ClosedFiltration.toStageStratification` and
  `.toStageFiltration`: the stratification by the open stages of the filtration, with the same
  filtration.

## Main results

* `AlgebraicGeometry.exists_closed_filtration_of_noetherianSpace`: a closed filtration of a
  Noetherian space whose successive differences satisfy a given property.
* `AlgebraicGeometry.exists_isOpen_isIrreducible_inter_subset`: an irreducible relatively open part
  of a closed set inside one member of a locally closed cover.
* `AlgebraicGeometry.exists_isOpen_inter_smooth_reducedInducedInclusion`: a relatively open part
  of a locally closed set whose reduced induced scheme is smooth over a perfect field.
* `ConstructibleStratification.exists_refines_irreducibleSpace_smooth_closedFiltration` (in the
  `AlgebraicGeometry` namespace): the refinement by irreducible strata smooth over `k`, with a
  closed filtration.
* `AlgebraicGeometry.ConstructibleStratification.ClosedFiltration.exists_pieceIso_stageOpenObj` and
  `.exists_pieceIso_sheafPullback`: the `i`-th stratum is the open complement of the
  `(i + 1)`-th member in the `i`-th, compatibly with the immersions into `X` and with inverse
  image of sheaves.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
* [Stacks Project, Tag 020I](https://stacks.math.columbia.edu/tag/020I)
* [Stacks Project, Tag 03UZ](https://stacks.math.columbia.edu/tag/03UZ)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry

section Filtration

variable {α : Type*} [TopologicalSpace α]

/-- The Noetherian induction producing a closed filtration, relative to a closed set. -/
private theorem exists_closed_filtration_aux [NoetherianSpace α] (P : Set α → Prop)
    (hP : ∀ Z : Set α, IsClosed Z → Z.Nonempty →
      ∃ V : Set α, IsOpen V ∧ (V ∩ Z).Nonempty ∧ P (V ∩ Z))
    (Z : Closeds α) :
    ∃ (n : ℕ) (Y : ℕ → Set α), Y 0 = Z ∧ (∀ t, n ≤ t → Y t = ∅) ∧ (∀ t, IsClosed (Y t)) ∧
      (∀ t, Y (t + 1) ⊆ Y t) ∧ ∀ t < n, (Y t \ Y (t + 1)).Nonempty ∧ P (Y t \ Y (t + 1)) := by
  apply wellFounded_lt.induction Z
  clear Z
  intro Z H
  rcases Set.eq_empty_or_nonempty (Z : Set α) with hempty | hne
  · exact ⟨0, fun _ ↦ Z, rfl, fun _ _ ↦ hempty, fun _ ↦ Z.isClosed, fun _ ↦ subset_rfl,
      fun t ht ↦ by omega⟩
  obtain ⟨V, hV, hVne, hVP⟩ := hP Z Z.isClosed hne
  let Z' : Closeds α := ⟨(Z : Set α) \ V, Z.isClosed.sdiff hV⟩
  have hZ'lt : Z' < Z := by
    refine lt_of_le_of_ne (fun x hx ↦ hx.1) fun hcontra ↦ ?_
    obtain ⟨x, hxV, hxZ⟩ := hVne
    exact (hcontra ▸ hxZ : x ∈ (Z' : Set α)).2 hxV
  obtain ⟨m, Y', hY'0, hY'e, hY'c, hY'd, hY'P⟩ := H Z' hZ'lt
  have hdiff : (Z : Set α) \ Y' 0 = V ∩ Z := by
    rw [hY'0, show ((Z' : Set α)) = (Z : Set α) \ V from rfl, Set.sdiff_sdiff_right_self,
      Set.inter_comm]
  refine ⟨m + 1, fun t ↦ Nat.casesOn t (Z : Set α) Y', rfl, ?_, ?_, ?_, ?_⟩
  · rintro (_ | t) ht
    · omega
    · exact hY'e t (Nat.le_of_succ_le_succ ht)
  · rintro (_ | t)
    · exact Z.isClosed
    · exact hY'c t
  · rintro (_ | t)
    · exact fun x hx ↦ (hY'0 ▸ hx : x ∈ (Z' : Set α)).1
    · exact hY'd t
  · rintro (_ | t) ht
    · exact ⟨hdiff ▸ hVne, hdiff ▸ hVP⟩
    · exact hY'P t (Nat.lt_of_succ_lt_succ ht)

/-- Let `P` be a property of subsets of a Noetherian space such that every nonempty closed set `Z`
contains a nonempty relatively open part `V ∩ Z` satisfying `P`. Then there is a finite decreasing
chain of closed sets `univ = Y 0 ⊇ Y 1 ⊇ ⋯ ⊇ Y n = ∅` whose successive differences
`Y t \ Y (t + 1)`, each open in `Y t`, are nonempty and satisfy `P`. -/
public theorem exists_closed_filtration_of_noetherianSpace [NoetherianSpace α]
    (P : Set α → Prop)
    (hP : ∀ Z : Set α, IsClosed Z → Z.Nonempty →
      ∃ V : Set α, IsOpen V ∧ (V ∩ Z).Nonempty ∧ P (V ∩ Z)) :
    ∃ (n : ℕ) (Y : ℕ → Set α), Y 0 = Set.univ ∧ (∀ t, n ≤ t → Y t = ∅) ∧
      (∀ t, IsClosed (Y t)) ∧ (∀ t, Y (t + 1) ⊆ Y t) ∧
      ∀ t < n, (Y t \ Y (t + 1)).Nonempty ∧ P (Y t \ Y (t + 1)) :=
  exists_closed_filtration_aux P hP ⊤

end Filtration

section Irreducible

variable {α : Type*} [TopologicalSpace α]

/-- A nonempty relatively open part of an irreducible set is irreducible. -/
public theorem _root_.IsIrreducible.open_inter {L V : Set α} (hL : IsIrreducible L) (hV : IsOpen V)
    (hne : (V ∩ L).Nonempty) : IsIrreducible (V ∩ L) := by
  have : IrreducibleSpace L := Subtype.irreducibleSpace hL
  have h : IsPreirreducible ((Subtype.val : L → α) ⁻¹' V) :=
    (IrreducibleSpace.isIrreducible_univ L).2.open_subset
      (hV.preimage continuous_subtype_val) (Set.subset_univ _)
  have himg := h.image _ continuous_subtype_val.continuousOn
  rw [Subtype.image_preimage_coe, Set.inter_comm] at himg
  exact ⟨hne, himg⟩

/-- In a Noetherian quasi-sober space covered by locally closed sets `S i`, every nonempty closed
set `Z` has a nonempty relatively open part `V ∩ Z` which is irreducible and contained in some
`S i`. -/
public theorem exists_isOpen_isIrreducible_inter_subset [NoetherianSpace α] [QuasiSober α]
    {κ : Type*} (S : κ → Set α) (hS : ∀ i, IsLocallyClosed (S i)) (hcov : ⋃ i, S i = Set.univ)
    {Z : Set α} (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ V : Set α, IsOpen V ∧ IsIrreducible (V ∩ Z) ∧ ∃ i, V ∩ Z ⊆ S i := by
  have : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have : Finite (irreducibleComponents Z) :=
    (NoetherianSpace.finite_irreducibleComponents (α := Z)).to_subtype
  obtain ⟨W, hWo, hWirr, -, -, hWS⟩ :=
    Stacks.Topology.Irreducible.exists_isIrreducible_opens_of_isLocallyClosed_cover
      (fun i ↦ (Subtype.val : Z → α) ⁻¹' S i)
      (fun i ↦ (hS i).preimage continuous_subtype_val)
      (by rw [← Set.preimage_iUnion, hcov, Set.preimage_univ])
  obtain ⟨z, hz⟩ := hne
  obtain ⟨c, hc, -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({⟨z, hz⟩} : Set Z) isIrreducible_singleton
  obtain ⟨V, hV, hVW⟩ := isOpen_induced_iff.mp (hWo ⟨c, hc⟩)
  have himg : V ∩ Z = Subtype.val '' W ⟨c, hc⟩ := by
    rw [← hVW, Subtype.image_preimage_coe, Set.inter_comm]
  obtain ⟨i, hi⟩ := hWS ⟨c, hc⟩
  refine ⟨V, hV, himg ▸ (hWirr ⟨c, hc⟩).image _ continuous_subtype_val.continuousOn, i, ?_⟩
  rw [himg]
  exact Set.image_subset_iff.mpr hi

end Irreducible

section Partition

variable {α : Type*} {Y : ℕ → Set α} {n : ℕ}

/-- The successive differences of a decreasing chain of sets are pairwise disjoint. -/
public theorem disjoint_sdiff_succ_of_succ_subset (hY : ∀ j, Y (j + 1) ⊆ Y j) {i j : ℕ}
    (hij : i ≠ j) : Disjoint (Y i \ Y (i + 1)) (Y j \ Y (j + 1)) := by
  wlog h : i < j generalizing i j
  · exact (this hij.symm (by omega)).symm
  exact Set.disjoint_left.mpr fun x hx hx' ↦ hx.2 (antitone_nat_of_succ_le hY h hx'.1)

/-- A decreasing chain of sets from `univ` to `∅` in `n` steps is covered by its first `n`
successive differences. -/
public theorem iUnion_sdiff_succ_eq_univ (hY0 : Y 0 = Set.univ) (hYn : Y n = ∅) :
    ⋃ i : Fin n, Y i \ Y (i + 1) = Set.univ := by
  classical
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have hex : ∃ m, x ∉ Y m := ⟨n, hYn ▸ Set.notMem_empty x⟩
  obtain ⟨m, hm, hmin, hmn⟩ : ∃ m, x ∉ Y m ∧ (∀ m' < m, x ∈ Y m') ∧ m ≤ n :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m' h ↦ not_not.mp (Nat.find_min hex h),
      Nat.find_min' hex (hYn ▸ Set.notMem_empty x)⟩
  rcases m with _ | i
  · exact absurd (hY0 ▸ Set.mem_univ x) hm
  · exact Set.mem_iUnion.mpr ⟨⟨i, hmn⟩, hmin i (Nat.lt_succ_self i), hm⟩

end Partition

section Smooth

open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A morphism into a reduced scheme which is surjective and whose composite with an immersion is
an immersion is an isomorphism. -/
private theorem isIso_of_comp_isImmersion_of_range_eq_univ {X Y Z : Scheme.{u}} (g : X ⟶ Y)
    (h : Y ⟶ Z) [IsImmersion (g ≫ h)] [IsReduced Y] [IsImmersion h]
    (hsurj : Set.range g = Set.univ) : IsIso g := by
  have : IsImmersion g := IsImmersion.of_comp g h
  have : Surjective g := ⟨Set.range_eq_univ.mp hsurj⟩
  have : IsClosedImmersion g := .of_isPreimmersion _ (by rw [hsurj]; exact isClosed_univ)
  exact isIso_of_isClosedImmersion_of_surjective g

/-- Let `X` be locally of finite type over a perfect field `k` and `L` a nonempty locally closed
subset of `X`. Then some nonempty relatively open part `V ∩ L` of `L`, with its reduced induced
scheme structure, is smooth over `k`. -/
@[ega "IV 17.15.12" "special case"]
public theorem exists_isOpen_inter_smooth_reducedInducedInclusion [PerfectField k]
    [LocallyOfFiniteType f] (L : Set X) (hL : IsLocallyClosed L) (hne : L.Nonempty) :
    ∃ V : Set X, IsOpen V ∧ (V ∩ L).Nonempty ∧
      ∀ h : IsLocallyClosed (V ∩ L), Smooth (reducedInducedInclusion (V ∩ L) h ≫ f) := by
  let ι := reducedInducedInclusion L hL
  have : IsImmersion ι := isImmersion_reducedInducedInclusion L hL
  obtain ⟨U, hUd, hUs⟩ := (geometricallyReduced_iff_exists_dense_open_smooth (ι ≫ f)).mp
    (geometricallyReduced_of_isReduced (ι ≫ f))
  have : Nonempty (reducedInducedScheme L hL) := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, -⟩ := (range_inclusion L hL).ge hx
    exact ⟨y⟩
  obtain ⟨V, hV, hVU⟩ := (isEmbedding_reducedInducedInclusion L hL).isInducing.isOpen_iff.mp U.2
  have hVU' : ι ⁻¹' V = (U : Set (reducedInducedScheme L hL)) := hVU
  have himg : V ∩ L = ι '' (U : Set (reducedInducedScheme L hL)) := by
    rw [← hVU', Set.image_preimage_eq_inter_range, range_inclusion]
  refine ⟨V, hV, himg ▸ hUd.nonempty.image _, fun h ↦ ?_⟩
  have hrange : Set.range (U.ι ≫ ι) = V ∩ L := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι, himg]
  let g := reducedInducedLift (V ∩ L) h (U.ι ≫ ι) hrange.le
  have hg : g ≫ reducedInducedInclusion (V ∩ L) h = U.ι ≫ ι :=
    reducedInducedLift_inclusion _ _ _ _
  have : IsImmersion (g ≫ reducedInducedInclusion (V ∩ L) h) := by
    rw [hg]
    infer_instance
  have hsurj : Set.range g = Set.univ := by
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hx⟩ := hrange.ge ((range_inclusion (V ∩ L) h).le ⟨y, rfl⟩)
    refine ⟨x, (isEmbedding_reducedInducedInclusion (V ∩ L) h).injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg, hx]
  have := isIso_of_comp_isImmersion_of_range_eq_univ g (reducedInducedInclusion (V ∩ L) h) hsurj
  have hfac : reducedInducedInclusion (V ∩ L) h ≫ f = inv g ≫ (U.ι ≫ ι ≫ f) := by
    rw [← Category.assoc U.ι, ← hg]
    simp
  rw [hfac]
  infer_instance

/-- Let `X` be locally of finite type over a perfect field `k`, with Noetherian underlying space,
and covered by locally closed sets `S i`. Every nonempty closed `Z ⊆ X` has a nonempty relatively
open part `V ∩ Z` which is irreducible, lies in some `S i`, and whose reduced induced scheme is
smooth over `k`. -/
public theorem exists_isOpen_inter_isIrreducible_smooth [PerfectField k] [LocallyOfFiniteType f]
    [NoetherianSpace X] {κ : Type*} (S : κ → Set X) (hS : ∀ i, IsLocallyClosed (S i))
    (hcov : ⋃ i, S i = Set.univ) {Z : Set X} (hZ : IsClosed Z) (hne : Z.Nonempty) :
    ∃ V : Set X, IsOpen V ∧ IsIrreducible (V ∩ Z) ∧ (∃ i, V ∩ Z ⊆ S i) ∧
      ∀ h : IsLocallyClosed (V ∩ Z), Smooth (reducedInducedInclusion (V ∩ Z) h ≫ f) := by
  obtain ⟨V₁, hV₁, hirr, i, hi⟩ := exists_isOpen_isIrreducible_inter_subset S hS hcov hZ hne
  obtain ⟨V₂, hV₂, hne₂, hsm⟩ := exists_isOpen_inter_smooth_reducedInducedInclusion f (V₁ ∩ Z)
    (hV₁.isLocallyClosed.inter hZ.isLocallyClosed) hirr.nonempty
  have e : V₂ ∩ V₁ ∩ Z = V₂ ∩ (V₁ ∩ Z) := Set.inter_assoc _ _ _
  refine ⟨V₂ ∩ V₁, hV₂.inter hV₁, e ▸ hirr.open_inter hV₂ hne₂,
    ⟨i, e ▸ Set.inter_subset_right.trans hi⟩, ?_⟩
  rwa [e]

end Smooth

namespace ConstructibleStratification

variable {B : BigEtaleSite.{u}} {X : B.Scheme}

/-- A closed filtration of `X` whose successive differences are the strata of a constructible
stratification `s` of the whole of `X`: a decreasing chain of closed sets
`univ = Y 0 ⊇ Y 1 ⊇ ⋯ ⊇ Y s.n = ∅` such that the `i`-th stratum is `Y i \ Y (i + 1)`, and the
strata are reduced. -/
public structure ClosedFiltration (s : ConstructibleStratification B X ⊤) where
  /-- The closed sets of the filtration. -/
  Y : ℕ → Set X.obj
  /-- The filtration starts with the whole space. -/
  zero : Y 0 = Set.univ
  /-- The filtration ends with the empty set after `s.n` steps. -/
  eq_empty : ∀ j, s.n ≤ j → Y j = ∅
  /-- Each member of the filtration is closed. -/
  isClosed : ∀ j, IsClosed (Y j)
  /-- The filtration is decreasing. -/
  succ_subset : ∀ j, Y (j + 1) ⊆ Y j
  /-- The `i`-th stratum is the `i`-th successive difference. -/
  range_eq : ∀ i : Fin s.n,
    Set.range (B.inclusion.map (s.inclusion i)).base = Y i \ Y (i + 1)
  /-- The strata are reduced. -/
  isReduced : ∀ i : Fin s.n, IsReduced (B.inclusion.obj (s.piece i))

open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed in
/-- Let `X` be an object of a big étale site which is locally of finite type over a perfect field
`k`, with Noetherian underlying space. Every constructible stratification `t` of `X` is refined by
a constructible stratification `s` whose strata are irreducible and smooth over `k`, and whose
strata are the successive differences of a closed filtration of `X`. -/
public theorem exists_refines_irreducibleSpace_smooth_closedFiltration (B : BigEtaleSite.{u})
    (X : B.Scheme) {k : Type u} [Field k] [PerfectField k] (f : X.obj ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [NoetherianSpace X.obj] (t : ConstructibleStratification B X ⊤) :
    ∃ s : ConstructibleStratification B X ⊤, s.Refines t ∧
      (∀ i, IrreducibleSpace (s.piece i).obj) ∧
      (∀ i, Smooth (B.inclusion.map (s.inclusion i) ≫ f)) ∧ Nonempty s.ClosedFiltration := by
  let S : Fin t.n → Set X.obj := fun j ↦ Set.range (B.inclusion.map (t.inclusion j)).base
  have hS : ∀ j, IsLocallyClosed (S j) := fun j ↦
    have := t.isImmersion j
    (B.inclusion.map (t.inclusion j)).isLocallyClosed_range
  have hcov : ⋃ j, S j = Set.univ := by
    rw [← t.covers, TopologicalSpace.Opens.coe_top]
  let P : Set X.obj → Prop := fun L ↦ IsIrreducible L ∧ (∃ j, L ⊆ S j) ∧
    ∀ h : IsLocallyClosed L, Smooth (reducedInducedInclusion L h ≫ f)
  obtain ⟨n, Y, hY0, hYe, hYc, hYd, hYP⟩ := exists_closed_filtration_of_noetherianSpace P
    fun Z hZ hne ↦ by
      obtain ⟨V, hV, hirr, hsub, hsm⟩ :=
        exists_isOpen_inter_isIrreducible_smooth f S hS hcov hZ hne
      exact ⟨V, hV, hirr.nonempty, hirr, hsub, hsm⟩
  let A : Fin n → Set X.obj := fun i ↦ Y i \ Y (i + 1)
  have hlc : ∀ i, IsLocallyClosed (A i) := fun i ↦
    (hYc i).isLocallyClosed.inter (hYc (i + 1)).isOpen_compl.isLocallyClosed
  have hnoeth : NoetherianSpace (⊤ : X.obj.Opens).toScheme :=
    (⊤ : X.obj.Opens).isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  let s := ofPartition B X ⊤ A hlc (fun _ _ _ ↦ trivial)
    (fun i ↦ isConstructible_of_isLocallyClosed ((hlc i).preimage (Scheme.Hom.continuous _)))
    (fun i j hij ↦ disjoint_sdiff_succ_of_succ_subset hYd (fun h ↦ hij (Fin.ext h)))
    (by rw [TopologicalSpace.Opens.coe_top, iUnion_sdiff_succ_eq_univ hY0 (hYe n le_rfl)])
  have hrange : ∀ i, Set.range (B.inclusion.map (s.inclusion i)).base = A i :=
    range_inclusion_ofPartition B X ⊤ A hlc _ _ _ _
  refine ⟨s, fun i ↦ ?_, fun i ↦ irreducibleSpace_reducedInducedScheme (A i) (hlc i)
    (hYP i i.2).2.1, fun i ↦ ?_, ⟨⟨Y, hY0, hYe, hYc, hYd, hrange, fun i ↦
      inferInstanceAs (IsReduced (reducedInducedScheme (A i) (hlc i)))⟩⟩⟩
  · obtain ⟨j, hj⟩ := (hYP i i.2).2.2.1
    have := t.isImmersion j
    have : IsReduced (B.inclusion.obj (s.piece i)) :=
      inferInstanceAs (IsReduced (reducedInducedScheme (A i) (hlc i)))
    obtain ⟨g, hg⟩ := Scheme.exists_comp_eq_of_isImmersion_of_isReduced
      (B.inclusion.map (t.inclusion j)) (B.inclusion.map (s.inclusion i)) ((hrange i).le.trans hj)
    have : IsImmersion (g ≫ B.inclusion.map (t.inclusion j)) := by
      rw [hg]
      exact s.isImmersion i
    refine ⟨j, ObjectProperty.homMk g, IsImmersion.of_comp g (B.inclusion.map (t.inclusion j)),
      ?_⟩
    ext1
    exact hg
  · change Smooth (B.inclusion.map (partitionInclusion B X (A i) (hlc i)) ≫ f)
    rw [map_partitionInclusion]
    exact (hYP i i.2).2.2.2 _

namespace ClosedFiltration

open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

variable {s : ConstructibleStratification B X ⊤} (Φ : s.ClosedFiltration)

/-- The `j`-th member of the filtration, as a reduced closed subscheme of `X` in the big étale
site. -/
public def stage (j : ℕ) : B.Scheme :=
  partitionPiece B X (Φ.Y j) (Φ.isClosed j).isLocallyClosed

/-- The closed immersion of the `j`-th member of the filtration into `X`. -/
public def stageInclusion (j : ℕ) : Φ.stage j ⟶ X :=
  partitionInclusion B X (Φ.Y j) (Φ.isClosed j).isLocallyClosed

/-- The closed immersion of the `j`-th member of the filtration is the inclusion of the reduced
induced scheme on `Y j`. -/
public theorem map_stageInclusion (j : ℕ) :
    B.inclusion.map (Φ.stageInclusion j) =
      reducedInducedInclusion (Φ.Y j) (Φ.isClosed j).isLocallyClosed :=
  map_partitionInclusion B X _ _

/-- The image of the `j`-th member of the filtration in `X` is `Y j`. -/
public theorem range_stageInclusion (j : ℕ) :
    Set.range (B.inclusion.map (Φ.stageInclusion j)).base = Φ.Y j :=
  range_partitionInclusion B X _ _

/-- The members of the filtration are reduced. -/
public instance isReduced_stage (j : ℕ) : IsReduced (B.inclusion.obj (Φ.stage j)) :=
  inferInstanceAs (IsReduced (reducedInducedScheme (Φ.Y j) (Φ.isClosed j).isLocallyClosed))

/-- The inclusion of a member of the filtration into `X` is a closed immersion. -/
public instance isClosedImmersion_stageInclusion (j : ℕ) :
    IsClosedImmersion (B.inclusion.map (Φ.stageInclusion j)) := by
  have : IsImmersion (B.inclusion.map (Φ.stageInclusion j)) := by
    rw [map_stageInclusion]
    exact isImmersion_reducedInducedInclusion _ _
  exact .of_isPreimmersion _ (by rw [range_stageInclusion]; exact Φ.isClosed j)

/-- The closed immersion of the `(j + 1)`-th member of the filtration into the `j`-th. -/
public def stageSucc (j : ℕ) : Φ.stage (j + 1) ⟶ Φ.stage j :=
  partitionComparison B X (Φ.Y (j + 1)) (Φ.Y j) (Φ.isClosed (j + 1)).isLocallyClosed
    (Φ.isClosed j).isLocallyClosed (Φ.succ_subset j)

/-- The inclusion of the `(j + 1)`-th member into the `j`-th, followed by the inclusion of the
`j`-th member into `X`, is the inclusion of the `(j + 1)`-th member into `X`. -/
@[reassoc (attr := simp)]
public theorem stageSucc_stageInclusion (j : ℕ) :
    Φ.stageSucc j ≫ Φ.stageInclusion j = Φ.stageInclusion (j + 1) :=
  partitionComparison_inclusion B X _ _ _ _ _

/-- The image of the `(j + 1)`-th member in the `j`-th is the preimage of `Y (j + 1)`. -/
public theorem range_stageSucc (j : ℕ) :
    Set.range (B.inclusion.map (Φ.stageSucc j)).base =
      (B.inclusion.map (Φ.stageInclusion j)).base ⁻¹' Φ.Y (j + 1) :=
  range_partitionComparison B X _ _ _ _ _

/-- The inclusion of the `(j + 1)`-th member into the `j`-th is a closed immersion. -/
public instance isClosedImmersion_stageSucc (j : ℕ) :
    IsClosedImmersion (B.inclusion.map (Φ.stageSucc j)) := by
  have : IsImmersion (B.inclusion.map (Φ.stageSucc j)) :=
    isImmersion_partitionComparison B X _ _ _ _ _
  exact .of_isPreimmersion _ (by
    rw [range_stageSucc]
    exact (Φ.isClosed (j + 1)).preimage (Scheme.Hom.continuous _))

/-- The open complement in the `j`-th member of the filtration of the `(j + 1)`-th. -/
public def stageOpen (j : ℕ) : (B.inclusion.obj (Φ.stage j)).Opens :=
  ⟨(Set.range (B.inclusion.map (Φ.stageSucc j)).base)ᶜ,
    (IsClosedImmersion.isClosedEmbedding
      (B.inclusion.map (Φ.stageSucc j))).isClosed_range.isOpen_compl⟩

/-- The image of the open complement `stageOpen j` is the complement of the image of the
`(j + 1)`-th member. -/
public theorem range_stageOpen_ι (j : ℕ) :
    Set.range (Φ.stageOpen j).ι.base = (Set.range (B.inclusion.map (Φ.stageSucc j)).base)ᶜ :=
  (Φ.stageOpen j).range_ι

/-- The `i`-th stratum is isomorphic to the open subscheme of the `i`-th member of the filtration
complementary to the `(i + 1)`-th member, compatibly with the immersions into `X`. -/
public theorem exists_pieceIso (i : Fin s.n) :
    ∃ e : B.inclusion.obj (s.piece i) ≅ (Φ.stageOpen i).toScheme,
      e.hom ≫ (Φ.stageOpen i).ι ≫ B.inclusion.map (Φ.stageInclusion i) =
        B.inclusion.map (s.inclusion i) := by
  have := Φ.isReduced i
  have := s.isImmersion i
  let ιP := B.inclusion.map (s.inclusion i)
  let ιY := B.inclusion.map (Φ.stageInclusion i)
  have hP : Set.range ιP.base ⊆ Φ.Y i := (Φ.range_eq i).trans_subset Set.sdiff_subset
  let ℓ : B.inclusion.obj (s.piece i) ⟶ B.inclusion.obj (Φ.stage i) :=
    reducedInducedLift (Φ.Y i) (Φ.isClosed i).isLocallyClosed ιP hP
  have hℓ : ℓ ≫ ιY = ιP :=
    (congrArg (ℓ ≫ ·) (Φ.map_stageInclusion i)).trans (reducedInducedLift_inclusion _ _ _ _)
  have hsub : Set.range ℓ.base ⊆ Set.range (Φ.stageOpen i).ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [range_stageOpen_ι, range_stageSucc]
    intro h
    have hy : ιP.base y ∈ Φ.Y i \ Φ.Y (i + 1) := (Φ.range_eq i).le ⟨y, rfl⟩
    exact hy.2 (by rwa [← hℓ, Scheme.Hom.comp_apply])
  let g := IsOpenImmersion.lift (Φ.stageOpen i).ι ℓ hsub
  have hg : g ≫ (Φ.stageOpen i).ι = ℓ := IsOpenImmersion.lift_fac _ _ _
  have hgι : g ≫ (Φ.stageOpen i).ι ≫ ιY = ιP := by rw [reassoc_of% hg, hℓ]
  have : IsImmersion (g ≫ (Φ.stageOpen i).ι ≫ ιY) := by
    rw [hgι]
    infer_instance
  have hsurj : Set.range g.base = Set.univ := by
    refine Set.eq_univ_of_forall fun u ↦ ?_
    have hu : ιY.base ((Φ.stageOpen i).ι.base u) ∈ Φ.Y i \ Φ.Y (i + 1) :=
      ⟨(range_stageInclusion Φ i).le ⟨_, rfl⟩, fun h ↦
        (range_stageOpen_ι Φ i).le ⟨u, rfl⟩ ((range_stageSucc Φ i).ge h)⟩
    obtain ⟨y, hy⟩ := (Φ.range_eq i).ge hu
    refine ⟨y, (Φ.stageOpen i).ι.isEmbedding.injective (ιY.isEmbedding.injective ?_)⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hgι, hy]
  have := isIso_of_comp_isImmersion_of_range_eq_univ g ((Φ.stageOpen i).ι ≫ ιY) hsurj
  exact ⟨asIso g, hgι⟩

/-- The open complement in the `j`-th member of the filtration of the `(j + 1)`-th, as an object
of the big étale site. -/
public def stageOpenObj (j : ℕ) : B.Scheme :=
  ⟨(Φ.stageOpen j).toScheme,
    (Scheme.size_le_of_isOpenImmersion (Φ.stageOpen j).ι).trans_lt (Φ.stage j).property⟩

/-- The open immersion of the open complement into the `j`-th member of the filtration. -/
public def stageOpenInclusion (j : ℕ) : Φ.stageOpenObj j ⟶ Φ.stage j :=
  B.inclusion.preimage (Φ.stageOpen j).ι

/-- The image of `stageOpenInclusion j` under the inclusion of the big étale site is the open
immersion of `stageOpen j`. -/
public theorem map_stageOpenInclusion (j : ℕ) :
    B.inclusion.map (Φ.stageOpenInclusion j) = (Φ.stageOpen j).ι :=
  B.inclusion.map_preimage _

/-- The inclusion of the open complement into the `j`-th member is an open immersion. -/
public instance isOpenImmersion_stageOpenInclusion (j : ℕ) :
    IsOpenImmersion (B.inclusion.map (Φ.stageOpenInclusion j)) := by
  rw [map_stageOpenInclusion]
  exact inferInstanceAs (IsOpenImmersion (Scheme.Opens.ι (Φ.stageOpen j)))

/-- In the big étale site, the `i`-th stratum is isomorphic to the open complement of the
`(i + 1)`-th member of the filtration in the `i`-th, compatibly with the inclusions into `X`. -/
public theorem exists_pieceIso_stageOpenObj (i : Fin s.n) :
    ∃ e : s.piece i ≅ Φ.stageOpenObj i,
      e.hom ≫ Φ.stageOpenInclusion i ≫ Φ.stageInclusion i = s.inclusion i := by
  obtain ⟨e, he⟩ := Φ.exists_pieceIso i
  let e' : B.inclusion.obj (s.piece i) ≅ B.inclusion.obj (Φ.stageOpenObj i) := e
  refine ⟨B.inclusion.preimageIso e', B.inclusion.map_injective ?_⟩
  simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage,
    map_stageOpenInclusion]
  exact he

/-- The composite of the open immersion of the open complement and the closed immersion of the
member of the filtration has image the successive difference `Y j \ Y (j + 1)`. -/
public theorem range_stageOpenInclusion_stageInclusion (j : ℕ) :
    Set.range (B.inclusion.map (Φ.stageOpenInclusion j ≫ Φ.stageInclusion j)).base =
      Φ.Y j \ Φ.Y (j + 1) := by
  have h1 : Set.range (B.inclusion.map (Φ.stageOpenInclusion j)).base =
      Set.range (Φ.stageOpen j).ι.base :=
    congrArg (fun m : B.inclusion.obj (Φ.stageOpenObj j) ⟶ B.inclusion.obj (Φ.stage j) ↦
      Set.range m.base) (Φ.map_stageOpenInclusion j)
  rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, h1,
    range_stageOpen_ι, range_stageSucc, Set.image_compl_preimage, range_stageInclusion]

/-- The stratification by the open complements of the filtration: its `i`-th stratum is the open
complement `stageOpenObj i` of the `(i + 1)`-th member of the filtration in the `i`-th, with
inclusion into `X` the open immersion followed by the closed immersion. -/
public def toStageStratification : ConstructibleStratification B X ⊤ where
  n := s.n
  piece i := Φ.stageOpenObj i
  inclusion i := Φ.stageOpenInclusion i ≫ Φ.stageInclusion i
  isImmersion i := by
    rw [Functor.map_comp]
    infer_instance
  contained _ _ _ := trivial
  constructible i := by
    rw [range_stageOpenInclusion_stageInclusion, ← Φ.range_eq i]
    exact s.constructible i
  pairwise_disjoint i j hij := by
    rw [range_stageOpenInclusion_stageInclusion, range_stageOpenInclusion_stageInclusion,
      ← Φ.range_eq i, ← Φ.range_eq j]
    exact s.pairwise_disjoint i j hij
  covers := by
    rw [s.covers]
    exact Set.iUnion_congr fun i ↦ by
      rw [range_stageOpenInclusion_stageInclusion, ← Φ.range_eq i]

/-- The stratification by open complements has as many strata as `s`. -/
@[simp]
public theorem toStageStratification_n : Φ.toStageStratification.n = s.n := rfl

/-- The `i`-th stratum of the stratification by open complements is `stageOpenObj i`. -/
public theorem toStageStratification_piece (i : Fin s.n) :
    Φ.toStageStratification.piece i = Φ.stageOpenObj i := rfl

/-- The inclusion of the `i`-th stratum of the stratification by open complements. -/
public theorem toStageStratification_inclusion (i : Fin s.n) :
    Φ.toStageStratification.inclusion i = Φ.stageOpenInclusion i ≫ Φ.stageInclusion i := rfl

/-- The closed filtration `Φ`, as a closed filtration of the stratification by open complements. -/
public def toStageFiltration : Φ.toStageStratification.ClosedFiltration where
  Y := Φ.Y
  zero := Φ.zero
  eq_empty := Φ.eq_empty
  isClosed := Φ.isClosed
  succ_subset := Φ.succ_subset
  range_eq i := Φ.range_stageOpenInclusion_stageInclusion i
  isReduced i := inferInstanceAs (IsReduced (Φ.stageOpen i).toScheme)

/-- Along the isomorphism of `exists_pieceIso_stageOpenObj`, the inverse image of a sheaf `F` on
`X` to the `i`-th stratum is the inverse image of its restriction to the `i`-th member of the
filtration, restricted to the open complement of the `(i + 1)`-th member. -/
public theorem exists_pieceIso_sheafPullback {D : Type*} [Category D]
    [∀ (S T : B.Scheme) (g : T ⟶ S),
      ((smallEtaleBaseChange B g).sheafPushforwardContinuous D
        (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) D) (i : Fin s.n) :
    ∃ e : s.piece i ≅ Φ.stageOpenObj i,
      e.hom ≫ Φ.stageOpenInclusion i ≫ Φ.stageInclusion i = s.inclusion i ∧
        Nonempty (smallEtalePullObj B (s.inclusion i) F ≅
          smallEtalePullObj B e.hom
            (smallEtalePullObj B (Φ.stageOpenInclusion i)
              (smallEtalePullObj B (Φ.stageInclusion i) F))) := by
  obtain ⟨e, he⟩ := Φ.exists_pieceIso_stageOpenObj i
  refine ⟨e, he, ⟨?_⟩⟩
  rw [← he]
  exact ((smallEtaleSheafPullbackCompIso B _ _ _ e.hom
      (Φ.stageOpenInclusion i ≫ Φ.stageInclusion i) D).app F).symm ≪≫
    ((smallEtaleBaseChange B e.hom).sheafPullback D _ _).mapIso
      ((smallEtaleSheafPullbackCompIso B _ _ _ (Φ.stageOpenInclusion i)
        (Φ.stageInclusion i) D).app F).symm

end ClosedFiltration

end ConstructibleStratification

end AlgebraicGeometry

end
