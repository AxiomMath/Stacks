module

public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute

/-!
# A sober space with a subspace that is not quasi-sober (Stacks 0B35)

Fix an infinite set `Z` and a point `z : Z`, and give `Z` the topology whose closed
sets are `Z` itself together with all finite subsets of `Z \ {z}`; this is
`Stacks.Examples.SoberSubspace.cofiniteAway`. It is *not* Mathlib's `CofiniteTopology`: the point
  `z`
is distinguished, and `Z` is the only closed set containing it.

The irreducible closed subsets are therefore `Set.univ`, whose unique generic point is
`z`, and the singletons `{x}` with `x ≠ z`. So `Z` is sober in the sense of the Stacks
Project: every irreducible closed subset has a *unique* generic point. We record this as
`Stacks.Examples.SoberSubspace.unique_genericPoint_cofiniteAway`, and factor it through Mathlib's
  split of
sobriety into `QuasiSober` (existence) and `T0Space` (uniqueness).

The subspace `{x : Z // x ≠ z}` carries the cofinite topology of an infinite set: its
closed sets are the whole subspace and the finite sets. Hence it is irreducible while all
of its singletons are closed, so no point is generic for it and it is not quasi-sober
(`Stacks.Examples.SoberSubspace.not_quasiSober_subtype_ne`). Sobriety therefore does not pass to
  arbitrary
subspaces — contrast Stacks 0B31, which passes to *locally closed* ones.
-/

@[expose] public section

namespace Stacks.Examples.SoberSubspace

/-- In a quasi-sober Kolmogorov space, every irreducible closed subset has a *unique*
generic point. This is the Stacks Project's reading of "sober", split by Mathlib into
existence (`QuasiSober`) and uniqueness (`T0Space`). -/
@[ega "0 2.1.3" "special case"]
theorem existsUnique_isGenericPoint_iff (X : Type*) [TopologicalSpace X] :
    (∀ {S : Set X}, IsIrreducible S → IsClosed S → ∃! x, IsGenericPoint x S) ↔
      QuasiSober X ∧ T0Space X := by
  refine ⟨fun h => ⟨⟨fun {_} irr cl => (h irr cl).exists⟩, ?_⟩, fun ⟨hQS, hT0⟩ => ?_⟩
  · rw [t0Space_iff_inseparable]
    intro x y hxy
    have hcl : closure ({x} : Set X) = closure {y} := inseparable_iff_closure_eq.mp hxy
    obtain ⟨_, _, hz⟩ := h isIrreducible_singleton.closure isClosed_closure
    rw [hz x isGenericPoint_closure, hz y hcl.symm]
  · intro h_irred h_closed
    obtain ⟨x, hx⟩ := hQS.sober h_irred h_closed
    exact ⟨x, hx, fun y hy => (t0Space_iff_inseparable X).mp hT0 y x
      (inseparable_iff_closure_eq.mpr (by rw [hx, hy]))⟩

/-- The topology on `Z` of Stacks 0B35: the closed sets are `Z` itself together with all
finite subsets of `Z \ {z}`. -/
@[implicit_reducible]
def cofiniteAway (Z : Type*) (z : Z) : TopologicalSpace Z :=
  TopologicalSpace.ofClosed
    {S : Set Z | S = Set.univ ∨ (S.Finite ∧ z ∉ S)}
    (Or.inr ⟨Set.finite_empty, by simp⟩)
    (by
      intro A hA
      by_cases hAll : ∀ S ∈ A, S = Set.univ
      · left
        ext x
        simp only [Set.mem_sInter, Set.mem_univ, iff_true]
        intro S hS
        rw [hAll S hS]
        trivial
      · rw [not_forall] at hAll
        obtain ⟨S₀, hS₀⟩ := hAll
        rw [Classical.not_imp] at hS₀
        obtain ⟨hS₀A, hS₀ne⟩ := hS₀
        rcases hA hS₀A with hu | ⟨hfin, hnz⟩
        · exact absurd hu hS₀ne
        · exact Or.inr ⟨hfin.subset (Set.sInter_subset_of_mem hS₀A),
            fun hmem => hnz (Set.mem_sInter.mp hmem S₀ hS₀A)⟩)
    (by
      intro A hA B hB
      rcases hA with rfl | ⟨hAfin, hAnz⟩
      · exact Or.inl (Set.univ_union B)
      rcases hB with rfl | ⟨hBfin, hBnz⟩
      · exact Or.inl (Set.union_univ A)
      · exact Or.inr ⟨hAfin.union hBfin, fun h => h.elim hAnz hBnz⟩)

/-- The open sets of `cofiniteAway Z z` are the complements of its closed sets. -/
theorem isOpen_cofiniteAway_iff (Z : Type*) (z : Z) (S : Set Z) :
    @IsOpen Z (cofiniteAway Z z) S ↔ Sᶜ ∈ {T : Set Z | T = Set.univ ∨ (T.Finite ∧ z ∉ T)} :=
  Iff.rfl

/-- The closed sets of `cofiniteAway Z z` are `Set.univ` and the finite sets avoiding `z`. -/
theorem isClosed_cofiniteAway_iff (Z : Type*) (z : Z) (S : Set Z) :
    @IsClosed Z (cofiniteAway Z z) S ↔ S = Set.univ ∨ (S.Finite ∧ z ∉ S) := by
  refine ⟨fun h => ?_, fun h => @IsClosed.mk Z (cofiniteAway Z z) S ?_⟩
  · have : Sᶜᶜ ∈ {T : Set Z | T = Set.univ ∨ (T.Finite ∧ z ∉ T)} := h.isOpen_compl
    rwa [compl_compl] at this
  · rwa [isOpen_cofiniteAway_iff, compl_compl]

/-- Every finite set avoiding `z` is closed in `cofiniteAway Z z`. -/
private lemma isClosed_of_finite_of_notMem (Z : Type*) (z : Z) {S : Set Z} (hS : S.Finite)
    (hz : z ∉ S) : @IsClosed Z (cofiniteAway Z z) S :=
  (isClosed_cofiniteAway_iff Z z S).mpr (Or.inr ⟨hS, hz⟩)

/-- Every singleton `{x}` with `x ≠ z` is closed in `cofiniteAway Z z`. -/
private lemma isClosed_singleton_of_ne (Z : Type*) (z : Z) {x : Z} (hx : x ≠ z) :
    @IsClosed Z (cofiniteAway Z z) {x} :=
  isClosed_of_finite_of_notMem Z z (Set.finite_singleton x) fun h => hx h.symm

/-- `cofiniteAway Z z` is Kolmogorov: distinct points are separated by the complement of a
singleton. -/
theorem t0Space_cofiniteAway (Z : Type*) [Infinite Z] (z : Z) :
    letI : TopologicalSpace Z := cofiniteAway Z z
    T0Space Z := by
  let : TopologicalSpace Z := cofiniteAway Z z
  refine ⟨fun x y h => ?_⟩
  by_contra hxy
  by_cases hy : y = z
  · have hcl : IsClosed ({x} : Set Z) := isClosed_singleton_of_ne Z z (hy ▸ hxy)
    exact (h.mem_open_iff hcl.isOpen_compl).mpr
      (fun hh => hxy (Set.mem_singleton_iff.mp hh).symm) rfl
  · exact (h.mem_open_iff (isClosed_singleton_of_ne Z z hy).isOpen_compl).mp hxy rfl

/-- `cofiniteAway Z z` is quasi-sober: `Set.univ` has generic point `z`, and an irreducible
finite closed set avoiding `z` is a singleton. -/
theorem quasiSober_cofiniteAway (Z : Type*) [Infinite Z] (z : Z) :
    letI : TopologicalSpace Z := cofiniteAway Z z
    QuasiSober Z := by
  let : TopologicalSpace Z := cofiniteAway Z z
  refine ⟨fun {S} hirr hcl => ?_⟩
  rw [isClosed_cofiniteAway_iff] at hcl
  rcases hcl with rfl | ⟨hfin, hnz⟩
  · -- The closure of `{z}` is closed and contains `z`, so it must be `Set.univ`.
    refine ⟨z, ?_⟩
    rw [isGenericPoint_def]
    exact ((isClosed_cofiniteAway_iff Z z _).mp isClosed_closure).resolve_right
      fun ⟨_, hnz⟩ => hnz (subset_closure rfl)
  · -- An irreducible finite set not containing `z` must be a singleton.
    obtain ⟨x, hx⟩ := hirr.nonempty
    have hxz : x ≠ z := fun h => hnz (h ▸ hx)
    have hcl_x : IsClosed ({x} : Set Z) := isClosed_singleton_of_ne Z z hxz
    have hcl_d : IsClosed (S \ {x}) :=
      isClosed_of_finite_of_notMem Z z (hfin.subset Set.sdiff_subset) fun h => hnz h.1
    have hsub : S ⊆ {x} ∪ (S \ {x}) := fun s hs =>
      (Classical.em (s = x)).imp id fun hsx => ⟨hs, hsx⟩
    rcases isPreirreducible_iff_isClosed_union_isClosed.mp hirr.2 _ _ hcl_x hcl_d hsub with h | h
    · exact ⟨x, (Set.Subset.antisymm h (Set.singleton_subset_iff.mpr hx)) ▸ hcl_x.closure_eq⟩
    · exact absurd rfl (h hx).2

/-- **Stacks 0B35.** The space `Z` with the topology `cofiniteAway Z z` is sober: every
irreducible closed subset has a unique generic point. -/
@[stacks 0B35]
theorem unique_genericPoint_cofiniteAway (Z : Type*) [Infinite Z] (z : Z) :
    letI : TopologicalSpace Z := cofiniteAway Z z
    ∀ {S : Set Z}, IsIrreducible S → IsClosed S → ∃! x, IsGenericPoint x S := by
  let : TopologicalSpace Z := cofiniteAway Z z
  have : QuasiSober Z := quasiSober_cofiniteAway Z z
  have : T0Space Z := t0Space_cofiniteAway Z z
  exact fun _ => (existsUnique_isGenericPoint_iff Z).mpr ⟨inferInstance, inferInstance⟩

/-- **Stacks 0B35.** The subspace `Z \ {z}` of the sober space `cofiniteAway Z z` is not
quasi-sober: it is irreducible, yet all of its singletons are closed. -/
@[stacks 0B35]
theorem not_quasiSober_subtype_ne (Z : Type*) [Infinite Z] (z : Z) :
    letI : TopologicalSpace Z := cofiniteAway Z z
    ¬ QuasiSober ({x : Z // x ≠ z}) := by
  let : TopologicalSpace Z := cofiniteAway Z z
  let : TopologicalSpace {x : Z // x ≠ z} :=
    @instTopologicalSpaceSubtype Z (fun x => x ≠ z) (cofiniteAway Z z)
  have : Infinite {x : Z // x ≠ z} :=
    (Set.Finite.infinite_compl (Set.finite_singleton z)).to_subtype
  -- Closed sets of the subspace are either `Set.univ` or finite.
  have hclassify : ∀ A : Set {x : Z // x ≠ z}, IsClosed A → A = Set.univ ∨ A.Finite := by
    intro A hA
    rw [isClosed_induced_iff] at hA
    obtain ⟨C, hC, hAC⟩ := hA
    rw [isClosed_cofiniteAway_iff] at hC
    rcases hC with rfl | ⟨hfin, _⟩
    · exact Or.inl (by rw [← hAC, Set.preimage_univ])
    · exact Or.inr (hAC ▸ hfin.preimage Subtype.val_injective.injOn)
  -- The whole subspace is irreducible.
  have hirr : IsIrreducible (Set.univ : Set {x : Z // x ≠ z}) := by
    refine ⟨Set.univ_nonempty, ?_⟩
    rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro A B hA hB hsub
    rcases hclassify A hA with rfl | hAfin
    · exact Or.inl subset_rfl
    rcases hclassify B hB with rfl | hBfin
    · exact Or.inr subset_rfl
    exact (Set.infinite_univ ((hAfin.union hBfin).subset fun x _ => hsub (Set.mem_univ x))).elim
  -- Singletons in the subspace are closed.
  have hcl_sing : ∀ p : {x : Z // x ≠ z}, IsClosed ({p} : Set {x : Z // x ≠ z}) := fun p => by
    have h2 : IsClosed (Subtype.val ⁻¹' ({p.val} : Set Z) : Set {y : Z // y ≠ z}) :=
      (isClosed_singleton_of_ne Z z p.property).preimage continuous_subtype_val
    have h3 : (Subtype.val ⁻¹' ({p.val} : Set Z) : Set {y : Z // y ≠ z}) = {p} := by
      ext y
      simp [Subtype.ext_iff]
    rwa [h3] at h2
  intro hQS
  obtain ⟨p, hp⟩ := hQS.sober hirr isClosed_univ
  obtain ⟨q, hq⟩ := exists_ne (α := {x : Z // x ≠ z}) p
  have hpu : ({p} : Set {x : Z // x ≠ z}) = Set.univ := by
    rw [← (hcl_sing p).closure_eq]
    exact hp
  exact hq (by simpa using (hpu ▸ Set.mem_univ q : q ∈ ({p} : Set _)))

end Stacks.Examples.SoberSubspace
