module

public import StacksFrontier.Topology.Spectral.InverseLimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descent of constructible subsets along an inverse limit of spectral spaces

Let `D` be a cofiltered diagram of spectral spaces with spectral transition maps and let
`E ⊆ D.invLimit` be a constructible subset of its inverse limit. Then there are an object
`i : J` and a constructible subset `E_i ⊆ D.F.obj i` with `D.projFun i ⁻¹' E_i = E`, and
`E_i` may be chosen open (resp. closed) when `E` is open (resp. closed).

## Main results

* `descend_isCompact_isOpen`: a quasi-compact open subset of the inverse limit is the
  preimage of a quasi-compact open subset of some factor.
* `descend_isConstructible`: a constructible subset of the inverse limit is the preimage of a
  constructible subset of some factor.
* `descend_isConstructible_isOpen`: the open refinement.
* `descend_isConstructible_isClosed`: the closed refinement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe v u

variable {J : Type v} [SmallCategory J] [IsCofiltered J] (D : SpectralDiagram.{v, u} J)

attribute [local instance] SpectralDiagram.isSpectralSpace
attribute [local instance] spectralDiagram_invLimit_spectralSpace

/-! ### Quasi-compact open descent -/

/-- A quasi-compact open subset of the inverse limit is the preimage of a quasi-compact open
subset of one of the factors. -/
theorem descend_isCompact_isOpen
    {E : Set D.invLimit} (hEopen : IsOpen E) (hEcomp : IsCompact E) :
    ∃ (i : J) (U : Set (D.F.obj i)), IsOpen U ∧ IsCompact U ∧ D.projFun i ⁻¹' U = E := by
  classical
  obtain ⟨i, V, hVopen, hEeq⟩ :=
    TopCat.exists_isOpen_eq_preimage_of_isCompact_of_isOpen (Limits.limit.isLimit D.F) hEcomp
      hEopen
  have hpi : D.projFun i = ConcreteCategory.hom ((Limits.limit.cone D.F).π.app i) := rfl
  have : PrespectralSpace (D.F.obj i) := inferInstance
  have hb : IsTopologicalBasis { W : Set (D.F.obj i) | IsOpen W ∧ IsCompact W } :=
    PrespectralSpace.isTopologicalBasis
  obtain ⟨β, b, hVeq, hb_sub⟩ := hb.open_eq_iUnion hVopen
  have hbOpen : ∀ k, IsOpen (b k) := fun k => (hb_sub k).1
  have hbCompact : ∀ k, IsCompact (b k) := fun k => (hb_sub k).2
  have hE_eq_proj : E = D.projFun i ⁻¹' V := by
    rw [hEeq, hpi]
  have hEeq' : E = ⋃ k, D.projFun i ⁻¹' b k := by
    rw [hE_eq_proj, hVeq, Set.preimage_iUnion]
  have hcover : E ⊆ ⋃ k, D.projFun i ⁻¹' b k := hEeq'.le
  have hOpen_pre : ∀ k, IsOpen (D.projFun i ⁻¹' b k) :=
    fun k => (hbOpen k).preimage (D.projFun_continuous i)
  obtain ⟨t, hts⟩ := hEcomp.elim_finite_subcover (fun k => D.projFun i ⁻¹' b k) hOpen_pre hcover
  refine ⟨i, ⋃ k ∈ t, b k, ?_, ?_, ?_⟩
  · exact isOpen_biUnion fun k _ => hbOpen k
  · exact t.isCompact_biUnion fun k _ => hbCompact k
  · apply Set.Subset.antisymm
    · intro x hx
      rcases Set.mem_preimage.mp hx with hxpre
      rcases Set.mem_iUnion₂.mp hxpre with ⟨k, _, hxk⟩
      have hbV : b k ⊆ V := by
        rw [hVeq]; exact Set.subset_iUnion b k
      have : D.projFun i x ∈ V := hbV hxk
      rw [hE_eq_proj]
      exact this
    · intro x hxE
      rcases Set.mem_iUnion₂.mp (hts hxE) with ⟨k, hk, hxk⟩
      refine Set.mem_preimage.mpr ?_
      refine Set.mem_iUnion₂.mpr ⟨k, hk, ?_⟩
      exact hxk

/-! ### Pulling back a constructible to a common factor under cofiltering -/

/-- If a constructible subset `E_i ⊆ D.F.obj i` descends through `projFun i`, then pulling it
back along a transition map `D.F.map a : k ⟶ i` gives a constructible subset of `D.F.obj k`
whose preimage in the limit is the same. -/
private lemma pullback_descent {i k : J} (a : k ⟶ i)
    {E_i : Set (D.F.obj i)} (hE_i : IsConstructible E_i)
    {E : Set D.invLimit} (hEeq : D.projFun i ⁻¹' E_i = E) :
    ∃ E_k : Set (D.F.obj k), IsConstructible E_k ∧ D.projFun k ⁻¹' E_k = E := by
  refine ⟨D.F.map a ⁻¹' E_i, ?_, ?_⟩
  · refine hE_i.preimage (D.F.map a).hom.continuous ?_
    intro s hs_open hs_retro
    have hs_comp : IsCompact s := hs_retro.isCompact
    have hpre_comp : IsCompact (D.F.map a ⁻¹' s) :=
      (D.isSpectralMap a).isCompact_preimage_of_isOpen hs_open hs_comp
    have hpre_open : IsOpen (D.F.map a ⁻¹' s) :=
      hs_open.preimage (D.F.map a).hom.continuous
    exact hpre_comp.isRetrocompact hpre_open
  · rw [← hEeq, ← Set.preimage_comp]
    congr 1
    funext x
    exact (D.projFun_comp a x).symm

/-! ### Constructible subsets of the inverse limit descend -/

/-- For a cofiltered diagram `D` of spectral spaces with spectral transition maps, every
constructible subset `E` of the inverse limit `D.invLimit` is the preimage under some projection
`D.projFun i` of a constructible subset of `D.F.obj i`. -/
@[stacks 0A2Y, ega "IV 8.3.11" "partial"]
theorem descend_isConstructible
    {E : Set D.invLimit} (hE : IsConstructible E) :
    ∃ (i : J) (E_i : Set (D.F.obj i)), IsConstructible E_i ∧ D.projFun i ⁻¹' E_i = E := by
  classical
  induction hE using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen hUcomp =>
    have hUc : IsCompact U := hUcomp.isCompact
    obtain ⟨i, V, hVopen, hVcomp, hVpre⟩ := descend_isCompact_isOpen D hUopen hUc
    exact ⟨i, V, hVcomp.isConstructible hVopen, hVpre⟩
  | union s _ t _ hs ht =>
    obtain ⟨is_, Es, hEs, hEseq⟩ := hs
    obtain ⟨it, Et, hEt, hEteq⟩ := ht
    obtain ⟨k, hk⟩ : ∃ k : J,
        ∀ {X : J}, X ∈ ({is_, it} : Finset J) → Nonempty (k ⟶ X) :=
      IsCofiltered.inf_objs_exists ({is_, it} : Finset J)
    obtain ⟨a⟩ : Nonempty (k ⟶ is_) := hk (by simp)
    obtain ⟨b⟩ : Nonempty (k ⟶ it) := hk (by simp)
    obtain ⟨Es', hEs'_constr, hEs'_pre⟩ := pullback_descent D a hEs hEseq
    obtain ⟨Et', hEt'_constr, hEt'_pre⟩ := pullback_descent D b hEt hEteq
    refine ⟨k, Es' ∪ Et', hEs'_constr.union hEt'_constr, ?_⟩
    rw [Set.preimage_union, hEs'_pre, hEt'_pre]
  | compl s _ hs =>
    obtain ⟨i, E_i, hE_i, hEipre⟩ := hs
    refine ⟨i, E_iᶜ, hE_i.compl, ?_⟩
    rw [Set.preimage_compl, hEipre]

/-! ### Open and closed refinements -/

/-- A constructible open subset of the inverse limit of a cofiltered diagram of spectral
spaces is quasi-compact. -/
private lemma isCompact_of_isConstructible_of_isOpen
    {E : Set D.invLimit} (hE : IsConstructible E) (hEopen : IsOpen E) : IsCompact E := by
  classical
  have : QuasiSeparatedSpace D.invLimit := inferInstance
  have : CompactSpace D.invLimit := inferInstance
  have : PrespectralSpace D.invLimit := inferInstance
  rw [← QuasiSeparatedSpace.isRetrocompact_iff_isCompact hEopen]
  set ι : Type _ := { W : Set D.invLimit // IsOpen W ∧ IsCompact W } with hι_def
  set b : ι → Set D.invLimit := fun W => W.val with hb_def
  have : Nonempty ι := ⟨⟨∅, isOpen_empty, isCompact_empty⟩⟩
  have hbasis : IsTopologicalBasis (Set.range b) := by
    convert PrespectralSpace.isTopologicalBasis (X := D.invLimit) using 1
    exact Set.ext fun W => ⟨fun ⟨⟨_, hW'⟩, rfl⟩ => hW', fun hW => ⟨⟨W, hW⟩, rfl⟩⟩
  have hb_compact : ∀ i : ι, IsCompact (b i) := fun i => i.property.2
  have hb_open : ∀ i : ι, IsOpen (b i) := fun i => i.property.1
  refine IsConstructible.induction_of_isTopologicalBasis (X := D.invLimit)
    (P := fun s _ => IsRetrocompact s) b hbasis hb_compact ?_ ?_ E hE
  · intro i s _ K hKcomp hKopen
    have hbiK_comp : IsCompact (b i ∩ K) :=
      (hb_compact i).inter_of_isOpen hKcomp (hb_open i) hKopen
    have hrewrite : (b i \ ⋃ j ∈ s, b j) ∩ K = (b i ∩ K) \ ⋃ j ∈ s, b j := by
      rw [Set.sdiff_eq, Set.sdiff_eq, Set.inter_right_comm]
    rw [hrewrite]
    exact hbiK_comp.diff (isOpen_biUnion fun j _ => hb_open j)
  · intro s _ t _ hs' ht'
    exact hs'.union ht'

/-- If the constructible subset of the inverse limit is moreover open, the constructible subset it
descends from on the factor can be chosen open. -/
@[stacks 0A2Y "open refinement", ega "IV 8.3.12" "open case", ega "IV 8.3.11" "partial"]
theorem descend_isConstructible_isOpen
    {E : Set D.invLimit} (hE : IsConstructible E) (hEopen : IsOpen E) :
    ∃ (i : J) (E_i : Set (D.F.obj i)),
      IsConstructible E_i ∧ IsOpen E_i ∧ D.projFun i ⁻¹' E_i = E := by
  have hEcomp : IsCompact E := isCompact_of_isConstructible_of_isOpen D hE hEopen
  obtain ⟨i, V, hVopen, hVcomp, hVpre⟩ := descend_isCompact_isOpen D hEopen hEcomp
  exact ⟨i, V, hVcomp.isConstructible hVopen, hVopen, hVpre⟩

/-- If the constructible subset of the inverse limit is moreover closed, the constructible subset
it descends from on the factor can be chosen closed. -/
@[stacks 0A2Y "closed refinement", ega "IV 8.3.12" "resp. closed case", ega "IV 8.3.11" "partial"]
theorem descend_isConstructible_isClosed
    {E : Set D.invLimit} (hE : IsConstructible E) (hEcl : IsClosed E) :
    ∃ (i : J) (E_i : Set (D.F.obj i)),
      IsConstructible E_i ∧ IsClosed E_i ∧ D.projFun i ⁻¹' E_i = E := by
  obtain ⟨i, V, hVconstr, hVopen, hVpre⟩ :=
    descend_isConstructible_isOpen D hE.compl hEcl.isOpen_compl
  refine ⟨i, Vᶜ, hVconstr.compl, hVopen.isClosed_compl, ?_⟩
  rw [Set.preimage_compl, hVpre, compl_compl]

