module

public import StacksFrontier.Topology.Compactification.OnePoint
import StacksCore.Tactic.EgaSgaAttribute

/-!
# qc coverings of Hausdorff and locally quasi-compact spaces

A family `{f i : X i → Y}ᵢ` of continuous maps with common target is a *qc covering* when every
point of `Y` has a neighbourhood covered by the images of finitely many quasi-compact subsets of
the `X i`. This file defines qc coverings and proves the three axioms exhibiting them as a
pretopology on the category `LC` of Hausdorff locally quasi-compact spaces: an isomorphism is a
covering, coverings are closed under composition, and coverings are stable under base change along
the topological fibre product.

Here *quasi-compact* means `IsCompact`, with no separation axiom attached, and *locally
quasi-compact* means that every point has a quasi-compact neighbourhood, which is
`WeaklyLocallyCompactSpace` in Mathlib.

## Main definitions

* `IsQcCovering`: the predicate on a family of maps with common target.
* `FiberProd`: the topological fibre product `X' ×_Y Xi`, as the subspace of `X' × Xi` on which
  the two maps to `Y` agree.
* `FiberProd.prX'`: the projection of the fibre product to `X'`.

## Main results

* `qcCovering_refine_compact`: a quasi-compact subset of the target of a qc covering is contained
  in the union of the images of finitely many quasi-compact subsets of the members.
* `fiberProd_slice_isCompact`: the fibre product of two quasi-compact subsets over a Hausdorff
  base is quasi-compact.
* `isQcCovering_of_homeomorph`: a homeomorphism gives a qc covering by the singleton family.
* `isQcCovering_comp`: qc coverings of the members of a qc covering compose to a qc covering.
* `isQcCovering_base_change`: the projections `X' ×_Y X i → X'` of a qc covering `{X i → Y}` along
  a map `h : X' → Y` form a qc covering of `X'`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-- A family `{f i : X i → Y}ᵢ` of continuous maps with common target `Y` is a *qc covering* when
for every `y : Y` there is a finite set `s` of indices and quasi-compact sets `E i ⊆ X i` whose
images' union is a neighbourhood of `y`. This is the definition of Stacks 09X0. -/
def IsQcCovering {ι : Type*} {X : ι → Type*} {Y : Type*}
    [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y]
    (f : ∀ i, X i → Y) : Prop :=
  ∀ y : Y, ∃ (s : Finset ι) (E : ∀ i, Set (X i)),
    (∀ i ∈ s, IsCompact (E i)) ∧
    (⋃ i ∈ s, f i '' (E i)) ∈ nhds y

/-- The topological fibre product `X' ×_Y Xi` of `h : X' → Y` and `fi : Xi → Y`, realized as the
subspace `{(x', x) | h x' = fi x}` of `X' × Xi`. -/
@[ega "I 3.4.2"]
def FiberProd {X' Xi Y : Type*} [TopologicalSpace X'] [TopologicalSpace Xi] [TopologicalSpace Y]
    (h : X' → Y) (fi : Xi → Y) : Type _ :=
  {p : X' × Xi // h p.1 = fi p.2}

/-- The subspace topology on the topological fibre product `X' ×_Y Xi`. -/
instance {X' Xi Y : Type*} [TopologicalSpace X'] [TopologicalSpace Xi] [TopologicalSpace Y]
    (h : X' → Y) (fi : Xi → Y) : TopologicalSpace (FiberProd h fi) :=
  inferInstanceAs (TopologicalSpace {p : X' × Xi // h p.1 = fi p.2})

/-- The projection `pr_{X'} : X' ×_Y Xi → X'` of the fibre product. -/
def FiberProd.prX' {X' Xi Y : Type*} [TopologicalSpace X'] [TopologicalSpace Xi] [TopologicalSpace
    Y]
    (h : X' → Y) (fi : Xi → Y) : FiberProd h fi → X' := fun p => p.val.1

/-- If `{g j : Z j → Xi}ⱼ` is a qc covering of `Xi` and `E ⊆ Xi` is quasi-compact, then `E` is
contained in a finite union of images `g j '' (F j)` of quasi-compact sets `F j ⊆ Z j`. -/
theorem qcCovering_refine_compact {Xi : Type*} {J : Type*} {Z : J → Type*}
    [TopologicalSpace Xi] [∀ j, TopologicalSpace (Z j)]
    (g : ∀ j, Z j → Xi)
    (hcov : IsQcCovering g) {E : Set Xi} (hE : IsCompact E) :
    ∃ (t : Finset J) (F : ∀ j, Set (Z j)),
      (∀ j ∈ t, IsCompact (F j)) ∧ E ⊆ ⋃ j ∈ t, g j '' (F j) := by
  classical
  choose tx Fx hFxc hUnhd using hcov
  obtain ⟨pts, hpts⟩ := hE.elim_nhds_subcover (fun x => ⋃ j ∈ tx x, g j '' (Fx x j))
    (fun x _ => hUnhd x)
  refine ⟨pts.biUnion tx, fun j => ⋃ x ∈ pts.filter (fun x => j ∈ tx x), Fx x j, ?_, ?_⟩
  · intro j hj
    apply Set.Finite.isCompact_biUnion (Finset.finite_toSet _)
    intro x hx
    rw [Finset.coe_filter, Set.mem_ofPred_eq] at hx
    exact hFxc x j hx.2
  · refine hpts.2.trans ?_
    intro z hz
    simp only [Set.mem_iUnion] at hz ⊢
    obtain ⟨x, hx, j, hj, w, hw, rfl⟩ := hz
    refine ⟨j, Finset.mem_biUnion.mpr ⟨x, hx, hj⟩, w, ?_, rfl⟩
    simp only [Set.mem_iUnion]
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hj⟩, hw⟩

/-- If `F ⊆ X'` and `E ⊆ Xi` are quasi-compact and `Y` is Hausdorff, then the slice
`{p ∈ X' ×_Y Xi | pr_{X'} p ∈ F ∧ pr_{Xi} p ∈ E}` of the fibre product is quasi-compact. -/
theorem fiberProd_slice_isCompact {X' Xi Y : Type*}
    [TopologicalSpace X'] [TopologicalSpace Xi] [TopologicalSpace Y] [T2Space Y]
    (h : X' → Y) (hh : Continuous h) (fi : Xi → Y) (hfi : Continuous fi)
    {F : Set X'} (hF : IsCompact F) {E : Set Xi} (hE : IsCompact E) :
    IsCompact {p : FiberProd h fi | p.val.1 ∈ F ∧ p.val.2 ∈ E} := by
  have hind : Topology.IsInducing (Subtype.val : FiberProd h fi → X' × Xi) :=
    Topology.IsInducing.subtypeVal
  have hclosed : IsClosed {q : X' × Xi | h q.1 = fi q.2} :=
    isClosed_eq (hh.comp continuous_fst) (hfi.comp continuous_snd)
  have hKcompact : IsCompact ((F ×ˢ E) ∩ {q : X' × Xi | h q.1 = fi q.2}) :=
    (hF.prod hE).inter_right hclosed
  apply hind.isCompact_iff.mpr
  convert hKcompact using 1
  ext q
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod]
  constructor
  · rintro ⟨p, ⟨hpF, hpE⟩, rfl⟩
    exact ⟨⟨hpF, hpE⟩, p.2⟩
  · rintro ⟨⟨hF', hE'⟩, hq⟩
    exact ⟨⟨q, hq⟩, ⟨hF', hE'⟩, rfl⟩

/-- **Stacks 09X1** (1). If `X' → X` is an isomorphism in `LC`, that is, a homeomorphism of
Hausdorff locally quasi-compact spaces, then the singleton family `{X' → X}` is a qc covering. -/
@[stacks 09X1 "(1)"]
theorem isQcCovering_of_homeomorph {X' X : Type*}
    [TopologicalSpace X'] [T2Space X'] [WeaklyLocallyCompactSpace X']
    [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X]
    (e : X' ≃ₜ X) :
    IsQcCovering (X := fun _ : Unit => X') (fun _ => (e : X' → X)) := by
  intro x
  obtain ⟨K, hK, hKnhd⟩ := exists_compact_mem_nhds (e.symm x)
  refine ⟨{()}, fun _ => K, ?_, ?_⟩
  · intro i _; exact hK
  · have he : e '' K ∈ nhds x := by
      have hmap := e.map_nhds_eq (e.symm x)
      rw [Homeomorph.apply_symm_apply] at hmap
      rw [← hmap]
      exact Filter.image_mem_map hKnhd
    simpa only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, Set.iUnion_const] using he

set_option linter.unusedVariables false in
/-- **Stacks 09X1** (2). If `f` is a qc covering of `Y` and each `g i` is a qc covering of `X i`,
then the family of composites `(i, j) ↦ f i ∘ g i j` is a qc covering of `Y`. -/
@[stacks 09X1 "(2)"]
theorem isQcCovering_comp {ι : Type*} {X : ι → Type*} {Y : Type*}
    {J : ι → Type*} {Z : ∀ i, J i → Type*}
    [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y]
    [∀ i, T2Space (X i)] [∀ i, WeaklyLocallyCompactSpace (X i)]
    [T2Space Y] [WeaklyLocallyCompactSpace Y]
    [∀ i j, TopologicalSpace (Z i j)]
    [∀ i j, T2Space (Z i j)] [∀ i j, WeaklyLocallyCompactSpace (Z i j)]
    (f : ∀ i, X i → Y) (hf : ∀ i, Continuous (f i))
    (g : ∀ i (j : J i), Z i j → X i)
    (hcov : IsQcCovering f)
    (hcov' : ∀ i, IsQcCovering (g i)) :
    IsQcCovering (X := fun p : Σ i, J i => Z p.1 p.2)
      (fun p => f p.1 ∘ g p.1 p.2) := by
  intro y
  obtain ⟨s, E, hEc, hEnhd⟩ := hcov y
  choose! t F htc hsub using fun i (hi : i ∈ s) =>
    qcCovering_refine_compact (g i) (hcov' i) (hEc i hi)
  refine ⟨s.sigma t, fun p => F p.1 p.2, ?_, ?_⟩
  · intro p hp
    rw [Finset.mem_sigma] at hp
    exact htc p.1 hp.1 p.2 hp.2
  · refine Filter.mem_of_superset hEnhd ?_
    intro z hz
    simp only [Set.mem_iUnion] at hz ⊢
    obtain ⟨i, hi, e, he, rfl⟩ := hz
    have hmem : e ∈ ⋃ j ∈ t i, g i j '' (F i j) := hsub i hi he
    simp only [Set.mem_iUnion] at hmem
    obtain ⟨j, hj, w, hw, rfl⟩ := hmem
    exact ⟨⟨i, j⟩, Finset.mem_sigma.mpr ⟨hi, hj⟩, w, hw, rfl⟩

/-- **Stacks 09X1** (3). If `f` is a qc covering of `Y` and `h : X' → Y` is a morphism of `LC`,
then the family of projections `pr_{X'} : X' ×_Y X i → X'` is a qc covering of `X'`. -/
@[stacks 09X1 "(3)"]
theorem isQcCovering_base_change {ι : Type*} {X : ι → Type*} {Y X' : Type*}
    [∀ i, TopologicalSpace (X i)] [TopologicalSpace Y] [TopologicalSpace X']
    [∀ i, T2Space (X i)] [∀ i, WeaklyLocallyCompactSpace (X i)]
    [T2Space Y] [WeaklyLocallyCompactSpace Y]
    [T2Space X'] [WeaklyLocallyCompactSpace X']
    (f : ∀ i, X i → Y) (hf : ∀ i, Continuous (f i))
    (h : X' → Y) (hh : Continuous h)
    (hcov : IsQcCovering f) :
    IsQcCovering (X := fun i => FiberProd h (f i))
      (fun i => FiberProd.prX' h (f i)) := by
  intro x'
  obtain ⟨s, E, hEc, hEnhd⟩ := hcov (h x')
  have hn : h ⁻¹' (⋃ i ∈ s, f i '' (E i)) ∈ nhds x' :=
    hh.continuousAt.preimage_mem_nhds hEnhd
  obtain ⟨F, hFnhd, hFsub, hFc⟩ := local_compact_nhds hn
  refine ⟨s, fun i => {p : FiberProd h (f i) | p.val.1 ∈ F ∧ p.val.2 ∈ E i}, ?_, ?_⟩
  · intro i hi
    exact fiberProd_slice_isCompact h hh (f i) (hf i) hFc (hEc i hi)
  · refine Filter.mem_of_superset hFnhd ?_
    intro a ha
    have haN : h a ∈ ⋃ i ∈ s, f i '' (E i) := hFsub ha
    simp only [Set.mem_iUnion] at haN
    obtain ⟨i, hi, e, he, hea⟩ := haN
    simp only [Set.mem_iUnion]
    refine ⟨i, hi, ?_⟩
    refine ⟨⟨(a, e), ?_⟩, ?_, ?_⟩
    · simp only; rw [hea]
    · exact ⟨ha, he⟩
    · rfl
