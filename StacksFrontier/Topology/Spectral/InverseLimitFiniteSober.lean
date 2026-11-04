module

public import Mathlib.Topology.Spectral.Basic

/-!
# Inverse limits of finite sober spaces

Let `I` be a directed set and let `X : I → Type*` be an inverse system of topological spaces with
transition maps `f h : X j → X i` for `h : i ≤ j`. Its inverse limit `inverseLimit f` is the
subspace of `∀ i, X i` consisting of the compatible families.

The main result says that if every `X i` is finite and sober (`T0Space` together with
`QuasiSober`, which is the Stacks project's notion of a sober space), then `inverseLimit f` is a
spectral space. Following the source, quasi-compactness of the basic opens comes from the
profinite topology: this is isolated as `isCompact_of_forall_finset_exists_mem`, which says that a
subset of a product of finite spaces that is closed under approximation on finite sets of
coordinates is quasi-compact.

Note that functoriality of the transition maps (`f le_rfl = id` and
`f h₁ ∘ f h₂ = f (h₁.trans h₂)`) is never needed: only the compatibility condition built into
`inverseLimit` is used.

## Main results

* `isCompact_of_forall_finset_exists_mem`: quasi-compactness in a product of finite spaces of any
  subset that is closed in the profinite topology.
* `isTopologicalBasis_inverseLimitProj`: the sets `p i ⁻¹' U` for `U ⊆ X i` open form a basis of
  the inverse limit.
* `spectralSpace_inverseLimit` (Stacks 09XV): the inverse limit of a directed inverse system of
  finite sober topological spaces is a spectral topological space.
-/

@[expose] public section

universe u v

open Filter Set Topology TopologicalSpace

/-- Let `X` be a family of finite topological spaces. A subset `s` of the product `∀ i, X i` that
is closed under approximation on finite sets of coordinates -- that is, `x ∈ s` as soon as every
finite set of coordinates of `x` is realised by some element of `s` -- is quasi-compact.

Equivalently, `s` is closed in the *profinite* topology, i.e. the product of the discrete
topologies, which is compact by Tychonoff; the given topologies are coarser, so `s` stays
quasi-compact for them. -/
theorem isCompact_of_forall_finset_exists_mem {I : Type u} {X : I → Type v}
    [∀ i, TopologicalSpace (X i)] [∀ i, Finite (X i)] {s : Set (∀ i, X i)}
    (hs : ∀ x : ∀ i, X i, (∀ t : Finset I, ∃ y ∈ s, ∀ i ∈ t, y i = x i) → x ∈ s) :
    IsCompact s := by
  rw [isCompact_iff_ultrafilter_le_nhds]
  intro F hF
  choose a ha using fun i => (Ultrafilter.map (Function.eval i) F).eq_pure_of_finite
  have key : ∀ i, Function.eval i ⁻¹' {a i} ∈ (F : Filter (∀ i, X i)) := fun i =>
    Ultrafilter.mem_map.mp (by rw [ha i]; exact Ultrafilter.mem_pure.mpr rfl)
  refine ⟨a, hs a fun t => ?_, ?_⟩
  · have h1 : s ∩ ⋂ i ∈ t, Function.eval i ⁻¹' {a i} ∈ (F : Filter (∀ i, X i)) :=
      Filter.inter_mem (Filter.le_principal_iff.mp hF) ((biInter_finset_mem t).mpr fun i _ => key i)
    obtain ⟨y, hy, hy'⟩ := Filter.nonempty_of_mem h1
    exact ⟨y, hy, fun i hi => by simpa using mem_iInter₂.mp hy' i hi⟩
  · rw [nhds_pi]
    refine Filter.le_pi.2 fun i => ?_
    have h2 : Filter.map (Function.eval i) (F : Filter (∀ i, X i)) = pure (a i) := by
      rw [← Ultrafilter.coe_map, ha i]; rfl
    rw [Filter.Tendsto, h2]
    exact pure_le_nhds _

variable {I : Type u} [Preorder I] {X : I → Type v} (f : ∀ ⦃i j : I⦄, i ≤ j → X j → X i)

/-- The inverse limit of the inverse system `X` with transition maps `f`, as the subset of the
product `∀ i, X i` cut out by the compatibility conditions `f h (x j) = x i` for `h : i ≤ j`. -/
def inverseLimit : Set (∀ i, X i) :=
  {x | ∀ ⦃i j : I⦄ (h : i ≤ j), f h (x j) = x i}

/-- The projection `p i` from the inverse limit to the `i`-th space of the system. -/
def inverseLimitProj (i : I) (x : inverseLimit f) : X i := (x : ∀ i, X i) i

/-- The projections of the inverse limit are compatible with the transition maps:
`f h ∘ p j = p i` for `h : i ≤ j`. -/
theorem inverseLimitProj_comp {i j : I} (h : i ≤ j) (x : inverseLimit f) :
    f h (inverseLimitProj f j x) = inverseLimitProj f i x := x.2 h

variable [∀ i, TopologicalSpace (X i)]

/-- The projections of the inverse limit are continuous. -/
theorem continuous_inverseLimitProj (i : I) : Continuous (inverseLimitProj f i) :=
  (continuous_apply i).comp continuous_subtype_val

/-- **Stacks 09XV**, first step. Over a directed index set the preimages `p i ⁻¹' U` of the opens
`U` of the spaces of the system form a basis for the topology of the inverse limit: a basic open of
the product topology involves only finitely many coordinates, and these can be pushed to a single
index by directedness. -/
theorem isTopologicalBasis_inverseLimitProj [Nonempty I] [IsDirectedOrder I]
    (hf : ∀ ⦃i j : I⦄ (h : i ≤ j), Continuous (f h)) :
    IsTopologicalBasis (Set.range fun p : (i : I) × Opens (X i) =>
      inverseLimitProj f p.1 ⁻¹' p.2) := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨⟨i, U⟩, rfl⟩
    exact U.2.preimage (continuous_inverseLimitProj f i)
  · intro x W hxW hW
    obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.mp hW
    obtain ⟨t, u, hu, hsub⟩ := isOpen_pi_iff.mp hW' _ hxW
    obtain ⟨M, hM⟩ := t.exists_le
    set U : Opens (X M) := ⟨⋂ i : (t : Set I), f (hM i.1 i.2) ⁻¹' u i.1,
      isOpen_iInter_of_finite fun i => (hu i.1 i.2).1.preimage (hf _)⟩
    refine ⟨inverseLimitProj f M ⁻¹' U, ⟨⟨M, U⟩, rfl⟩, ?_, ?_⟩
    · refine mem_iInter.mpr fun i => ?_
      rw [mem_preimage, inverseLimitProj_comp f]
      exact (hu i.1 i.2).2
    · intro y hy
      refine hsub fun i hi => ?_
      have h3 := mem_iInter.mp hy ⟨i, hi⟩
      rw [mem_preimage, inverseLimitProj_comp f] at h3
      exact h3

/-- **Stacks 09XV**, second step. In an inverse limit of finite spaces the intersection of two
preimages `p i ⁻¹' U` and `p j ⁻¹' V` is quasi-compact, for arbitrary subsets `U ⊆ X i` and
`V ⊆ X j`. Taking `i = j` and `U = V` this also gives quasi-compactness of `p i ⁻¹' U` itself. -/
theorem isCompact_inverseLimitProj_preimage_inter [∀ i, Finite (X i)]
    (i j : I) (U : Set (X i)) (V : Set (X j)) :
    IsCompact (inverseLimitProj f i ⁻¹' U ∩ inverseLimitProj f j ⁻¹' V) := by
  classical
  have h : IsCompact (inverseLimit f ∩ {x : ∀ i, X i | x i ∈ U ∧ x j ∈ V}) := by
    refine isCompact_of_forall_finset_exists_mem fun x hx => ⟨fun {p q} h => ?_, ?_, ?_⟩
    · obtain ⟨y, ⟨hy, -⟩, hxy⟩ := hx {p, q}
      rw [← hxy p (by simp), ← hxy q (by simp)]
      exact hy h
    · obtain ⟨y, ⟨-, hyU, -⟩, hxy⟩ := hx {i}
      rw [← hxy i (by simp)]; exact hyU
    · obtain ⟨y, ⟨-, -, hyV⟩, hxy⟩ := hx {j}
      rw [← hxy j (by simp)]; exact hyV
  have h2 := (IsInducing.subtypeVal (t := inverseLimit f)).isCompact_preimage' h
    (inter_subset_left.trans_eq Subtype.range_val.symm)
  convert h2 using 1
  ext x
  simp [inverseLimitProj]

/-- **Stacks 09XV**, third step. The inverse limit of a directed inverse system of sober spaces is
sober: an irreducible closed `Z` has irreducible image in each `X i`, hence a generic point `ξ i`
there, and the `ξ i` are compatible by uniqueness of generic points, so they assemble to a generic
point of `Z`. -/
theorem quasiSober_inverseLimit [Nonempty I] [IsDirectedOrder I] [∀ i, T0Space (X i)]
    [∀ i, QuasiSober (X i)] (hf : ∀ ⦃i j : I⦄ (h : i ≤ j), Continuous (f h)) :
    QuasiSober (inverseLimit f) := by
  have hbasis := isTopologicalBasis_inverseLimitProj f hf
  refine ⟨fun {Z} hZ hZcl => ?_⟩
  have hgen : ∀ i, ∃ ξ : X i, IsGenericPoint ξ (closure (inverseLimitProj f i '' Z)) := fun i =>
    QuasiSober.sober ((hZ.image _ (continuous_inverseLimitProj f i).continuousOn).closure)
      isClosed_closure
  choose ξ hξ using hgen
  have himg : ∀ ⦃i j : I⦄ (h : i ≤ j), f h '' (inverseLimitProj f j '' Z)
      = inverseLimitProj f i '' Z := by
    intro i j h
    rw [← image_comp]
    exact image_congr fun z _ => inverseLimitProj_comp f h z
  have hmem : ∀ i, ξ i ∈ closure (inverseLimitProj f i '' Z) := fun i =>
    (hξ i) ▸ subset_closure rfl
  have hcomp : ∀ ⦃i j : I⦄ (h : i ≤ j), f h (ξ j) = ξ i := by
    intro i j h
    have := (hξ j).image (hf h)
    rw [closure_image_closure (hf h), himg h] at this
    exact this.eq (hξ i)
  refine ⟨⟨ξ, fun _ _ h => hcomp h⟩, Set.Subset.antisymm ?_ ?_⟩
  · refine hZcl.closure_subset_iff.mpr (singleton_subset_iff.mpr ?_)
    rw [← hZcl.closure_eq, hbasis.mem_closure_iff]
    rintro o ⟨⟨i, U⟩, rfl⟩ hξo
    obtain ⟨w, hwU, z, hzZ, rfl⟩ := mem_closure_iff.mp (hmem i) U U.2 hξo
    exact ⟨z, hwU, hzZ⟩
  · intro z hz
    rw [hbasis.mem_closure_iff]
    rintro o ⟨⟨i, U⟩, rfl⟩ hzo
    refine ⟨⟨ξ, fun _ _ h => hcomp h⟩, ?_, rfl⟩
    have hz' : inverseLimitProj f i z ∈ closure ({ξ i} : Set (X i)) := by
      rw [hξ i]; exact subset_closure ⟨z, hz, rfl⟩
    obtain ⟨w, hwU, rfl⟩ := mem_closure_iff.mp hz' U U.2 hzo
    exact hwU

/-- **Stacks 09XV**. The inverse limit of a directed inverse system of finite sober topological
spaces is a spectral topological space. Here a sober space in the sense of the Stacks project is a
space that is both `T0Space` and `QuasiSober`. -/
@[stacks 09XV]
theorem spectralSpace_inverseLimit [Nonempty I] [IsDirectedOrder I] [∀ i, Finite (X i)]
    [∀ i, T0Space (X i)] [∀ i, QuasiSober (X i)]
    (hf : ∀ ⦃i j : I⦄ (h : i ≤ j), Continuous (f h)) :
    SpectralSpace (inverseLimit f) := by
  have hbasis := isTopologicalBasis_inverseLimitProj f hf
  have hc : ∀ p q : (i : I) × Opens (X i),
      IsCompact ((inverseLimitProj f p.1 ⁻¹' p.2) ∩ (inverseLimitProj f q.1 ⁻¹' q.2)) :=
    fun p q => isCompact_inverseLimitProj_preimage_inter f p.1 q.1 _ _
  have : CompactSpace (inverseLimit f) := by
    refine isCompact_univ_iff.mp ?_
    simpa using isCompact_inverseLimitProj_preimage_inter f (Classical.arbitrary I)
      (Classical.arbitrary I) univ univ
  have : QuasiSober (inverseLimit f) := quasiSober_inverseLimit f hf
  have : PrespectralSpace (inverseLimit f) :=
    .of_isTopologicalBasis' hbasis fun p => by simpa using hc p p
  have : QuasiSeparatedSpace (inverseLimit f) := .of_isTopologicalBasis hbasis hc
  constructor
