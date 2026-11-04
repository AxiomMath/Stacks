module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Spectral.Prespectral
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Consequences of a basis of quasi-compact opens

Assume a topological space `X` has a basis of quasi-compact opens (H1) and the intersection of two
quasi-compact opens is quasi-compact (H2). Then `X` is locally quasi-compact, every quasi-compact
open is retrocompact, and every quasi-compact open has a cofinal system of finite open coverings by
quasi-compact opens with quasi-compact pairwise intersections.

## Main results

* The hypotheses (H1) and (H2) are Mathlib's `PrespectralSpace` and `QuasiSeparatedSpace`.
* `HasCofinalCompactRefinements`: the conclusion (C3), that an open has a cofinal system of finite
  coverings by quasi-compact opens with quasi-compact pairwise intersections.
* `locallyCompactSpace_of_hasBasisOfCompactOpens` (C1),
  `isRetrocompact_of_isCompact_isOpen` (C2),
  `hasCofinalCompactRefinements_of_isCompact_isOpen` (C3): the three conclusions.
* `locallyCompactSpace_and_isRetrocompact_and_hasCofinalCompactRefinements` (Stacks 0069): the
  three conclusions together.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- Conclusion (C3) of Stacks 0069: `U` has a cofinal system of finite open coverings by
quasi-compact opens whose pairwise intersections are also quasi-compact. -/
def HasCofinalCompactRefinements (U : Set X) : Prop :=
  ∀ {K : Type*} (V : K → Set X), (∀ k, IsOpen (V k)) → U ⊆ ⋃ k, V k →
    ∃ (ι : Type) (J : Finset ι) (W : ι → Set X),
      (∀ j ∈ J, IsOpen (W j)) ∧
      (∀ j ∈ J, IsCompact (W j)) ∧
      U = ⋃ j ∈ J, W j ∧
      (∀ j ∈ J, ∀ j' ∈ J, IsCompact (W j ∩ W j')) ∧
      (∀ j ∈ J, ∃ k, W j ⊆ V k)

/-- **Stacks 0069**, conclusion (C1). A space with a basis of quasi-compact opens is locally
quasi-compact. -/
theorem locallyCompactSpace_of_hasBasisOfCompactOpens
    (h1 : PrespectralSpace X) :
    LocallyCompactSpace X := by
  refine ⟨fun x n hn => ?_⟩
  obtain ⟨t, ht, hxt, hts⟩ := h1.isTopologicalBasis.mem_nhds_iff.mp hn
  exact ⟨t, h1.isTopologicalBasis.mem_nhds ht hxt, hts, ht.2⟩

/-- **Stacks 0069**, conclusion (C2). If the intersection of two quasi-compact opens of `X` is
quasi-compact, then every quasi-compact open subset of `X` is retrocompact. -/
@[ega "0 9.1.6" "partial", sga "3 VIB 3.7" "partial"]
theorem isRetrocompact_of_isCompact_isOpen
    (h2 : QuasiSeparatedSpace X)
    {U : Set X} (hUopen : IsOpen U) (hUcomp : IsCompact U) :
    IsRetrocompact U :=
  fun _ hVcomp hVopen => h2.inter_isCompact _ _ hUopen hUcomp hVopen hVcomp

/-- **Stacks 0069**, conclusion (C3). Under (H1) and (H2), every quasi-compact open admits a
cofinal system of finite open coverings by quasi-compact opens with quasi-compact pairwise
intersections. -/
theorem hasCofinalCompactRefinements_of_isCompact_isOpen
    (h1 : PrespectralSpace X) (h2 : QuasiSeparatedSpace X)
    {U : Set X} (hUopen : IsOpen U) (hUcomp : IsCompact U) :
    HasCofinalCompactRefinements U := by
  classical
  have hB := h1.isTopologicalBasis
  intro K V hVopen hUcov
  -- Refine the cover by intersecting with `U` so basis elements stay inside `U`.
  let V' : K → Set X := fun k => V k ∩ U
  have hV'open : ∀ k, IsOpen (V' k) := fun k => (hVopen k).inter hUopen
  have hUcov' : U ⊆ ⋃ k, V' k := fun x hx => by
    obtain ⟨k, hkx⟩ := Set.mem_iUnion.mp (hUcov hx)
    exact Set.mem_iUnion.mpr ⟨k, hkx, hx⟩
  -- For each `x ∈ U`, pick a basis element `b x ⊆ V (k x) ∩ U` containing `x`.
  have hsel : ∀ x : X, x ∈ U →
      ∃ (b : Set X) (k : K), (IsOpen b ∧ IsCompact b) ∧ x ∈ b ∧ b ⊆ V' k := fun x hx => by
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hUcov' hx)
    obtain ⟨b, hbB, hxb, hb_sub⟩ := hB.exists_subset_of_mem_open hk (hV'open k)
    exact ⟨b, k, hbB, hxb, hb_sub⟩
  choose! b k hbB hxb hbV' using hsel
  -- Index the family by points of `U` and extract a finite subcover.
  let b' : U → Set X := fun x => b x.1
  have hb'open : ∀ x : U, IsOpen (b' x) := fun x => hB.isOpen (hbB x.1 x.2)
  have hb'comp : ∀ x : U, IsCompact (b' x) := fun x => (hbB x.1 x.2).2
  obtain ⟨F, hF⟩ := hUcomp.elim_finite_subcover b' hb'open
    fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxb x hx⟩
  let e : Fin F.card ≃ {x // x ∈ F} := F.equivFin.symm
  -- The point of `U` indexed by `i`, so that the two components of a member of `F` never
  -- have to be reached through a chain of projections.
  let p : Fin F.card → U := fun i => (e i).1
  let W : Fin F.card → Set X := fun i => b' (p i)
  refine ⟨Fin F.card, Finset.univ, W, fun i _ => hb'open (p i),
    fun i _ => hb'comp (p i), ?_,
    fun i _ i' _ => h2.inter_isCompact _ _ (hb'open (p i)) (hb'comp (p i))
      (hb'open (p i')) (hb'comp (p i')),
    fun i _ => ⟨k (p i).1 (p i).2, (hbV' (p i).1 (p i).2).trans Set.inter_subset_left⟩⟩
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨j, hjF, hxj⟩ : ∃ j ∈ F, x ∈ b' j := by
      simpa [Set.mem_iUnion, exists_prop] using hF hx
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨j, hjF⟩,
      Set.mem_iUnion.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    simpa [W, p, e.apply_symm_apply] using hxj
  · simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact ((hbV' (p i).1 (p i).2).trans Set.inter_subset_right) hxi

/-- **Stacks 0069.** Under hypotheses (H1) and (H2), `X` is locally quasi-compact, every
quasi-compact open of `X` is retrocompact, and every quasi-compact open of `X` has a cofinal system
of finite open coverings by quasi-compact opens with quasi-compact pairwise intersections. -/
@[stacks 0069, ega "0 9.1.6" "second conjunct"]
theorem locallyCompactSpace_and_isRetrocompact_and_hasCofinalCompactRefinements
    (h1 : PrespectralSpace X) (h2 : QuasiSeparatedSpace X) :
    LocallyCompactSpace X ∧
    (∀ {U : Set X}, IsOpen U → IsCompact U → IsRetrocompact U) ∧
    (∀ {U : Set X}, IsOpen U → IsCompact U → HasCofinalCompactRefinements U) :=
  ⟨locallyCompactSpace_of_hasBasisOfCompactOpens h1, isRetrocompact_of_isCompact_isOpen h2,
    hasCofinalCompactRefinements_of_isCompact_isOpen h1 h2⟩
