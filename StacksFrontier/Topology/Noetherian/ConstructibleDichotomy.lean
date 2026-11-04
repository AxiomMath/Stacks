module

public import Mathlib.Topology.Constructible
public import StacksCore.Topology.Noetherian.Retrocompact
public import StacksFrontier.Topology.Constructible.InConstructible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Recognizing constructible sets by a dichotomy on irreducible closed subsets

In a Noetherian topological space a subset `E` is constructible exactly when, on each irreducible
closed `Z`, the intersection `E ∩ Z` either contains a nonempty open of `Z` or is not dense in `Z`.

## Main definitions

* `ContainsNonemptyOpenOf`, `IsDenseIn`: the two alternatives of the dichotomy.

## Main results

* `IsLocallyClosed.isConstructibleSet`: a locally closed subset of a Noetherian space is
  constructible.
* `constructible_iff_dichotomy_irreducible_closed`: the characterization.
-/

@[expose] public section

variable {X : Type*} [TopologicalSpace X]

/-- The intersection `E ∩ Z` *contains a nonempty open of `Z`* (in the subspace topology on `Z`)
if there exists an open subset `U ⊆ X` such that `U ∩ Z` is nonempty and contained in `E ∩ Z`. -/
def ContainsNonemptyOpenOf (E Z : Set X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ (U ∩ Z).Nonempty ∧ U ∩ Z ⊆ E ∩ Z

/-- The intersection `E ∩ Z` is *dense in `Z`* if `Z ⊆ closure (E ∩ Z)`. -/
def IsDenseIn (E Z : Set X) : Prop :=
  Z ⊆ closure (E ∩ Z)

/-- The empty set is constructible. -/
lemma isConstructibleSet_empty : IsConstructibleSet (∅ : Set X) := by
  refine ⟨0, fun _ : Fin 0 => ∅, fun _ : Fin 0 => ∅, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

/-- In a Noetherian space, a locally closed subset is constructible. -/
@[ega "0 9.1.5" "special case",
  ega "0 9.1.7" "sufficiency",
  ega "0 9.2.1" "partial",
  ega "IV 1.8.1" "special case",
  ega "IV 1.9.5" "(v), special case",
  ega "IV 10.1.1" "special case"]
lemma IsLocallyClosed.isConstructibleSet [TopologicalSpace.NoetherianSpace X]
    {L : Set X} (hL : IsLocallyClosed L) : IsConstructibleSet L := by
  obtain ⟨U, F, hU, hF, hLeq⟩ := hL
  refine ⟨1, fun _ => U, fun _ => Fᶜ, fun _ => hU,
    fun _ => noetherianSpace_isRetrocompact X _, fun _ => hF.isOpen_compl,
    fun _ => noetherianSpace_isRetrocompact X _, ?_⟩
  simpa [Set.iUnion_const, compl_compl] using hLeq

/-- An irreducible subset contained in a finite union of closed sets is contained in one of
them. -/
@[ega "0 2.1.7" "more general"]
lemma isIrreducible_subset_of_subset_iUnion_isClosed
    {Z : Set X} (hZ : IsIrreducible Z) {n : ℕ} (F : Fin n → Set X)
    (hF : ∀ i, IsClosed (F i)) (h : Z ⊆ ⋃ i, F i) : ∃ i, Z ⊆ F i := by
  induction n with
  | zero =>
    simp only [Set.iUnion_of_empty, Set.subset_empty_iff] at h
    exact absurd h hZ.nonempty.ne_empty
  | succ m ih =>
    set G : Set X := ⋃ i : Fin m, F i.succ
    have hG_closed : IsClosed G := isClosed_iUnion_of_finite (fun i => hF i.succ)
    have h_decomp : (⋃ i : Fin (m + 1), F i) = F 0 ∪ G := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union, G]
      refine ⟨fun ⟨i, hi⟩ => ?_, ?_⟩
      · induction i using Fin.cases with
        | zero => exact Or.inl hi
        | succ j => exact Or.inr ⟨j, hi⟩
      · rintro (h0 | ⟨j, hj⟩)
        · exact ⟨0, h0⟩
        · exact ⟨j.succ, hj⟩
    rw [h_decomp] at h
    have hbin : Z ⊆ F 0 ∨ Z ⊆ G := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hns, hnt⟩ := hcon
      rw [Set.not_subset] at hns hnt
      obtain ⟨x, hxZ, hxs⟩ := hns
      obtain ⟨y, hyZ, hyt⟩ := hnt
      obtain ⟨z, hzZ, hzsc, hztc⟩ :=
        hZ.isPreirreducible (F 0)ᶜ Gᶜ (hF 0).isOpen_compl hG_closed.isOpen_compl
          ⟨x, hxZ, hxs⟩ ⟨y, hyZ, hyt⟩
      exact (h hzZ).elim hzsc hztc
    rcases hbin with h1 | h2
    · exact ⟨0, h1⟩
    · obtain ⟨j, hj⟩ := ih (fun i => F i.succ) (fun i => hF i.succ) h2
      exact ⟨j.succ, hj⟩

/-- In a Noetherian space, if `E` is constructible and `Z` is irreducible, then `E ∩ Z` either
contains a nonempty open of `Z` or is not dense in `Z`. -/
@[ega "0 9.2.2" "necessity", sga "1 IV 6.1" "necessity"]
lemma containsNonemptyOpenOf_or_not_isDenseIn [TopologicalSpace.NoetherianSpace X]
    {E : Set X} (hE : IsConstructibleSet E)
    (Z : Set X) (hZ_irr : IsIrreducible Z) :
    ContainsNonemptyOpenOf E Z ∨ ¬ IsDenseIn E Z := by
  obtain ⟨n, U, V, hU_open, _, hV_open, _, hE_eq⟩ := hE
  by_cases hdense : IsDenseIn E Z
  · refine Or.inl ?_
    have hZ_sub_clU : Z ⊆ ⋃ i, closure (U i ∩ (V i)ᶜ ∩ Z) := by
      rwa [IsDenseIn, hE_eq, Set.iUnion_inter, closure_iUnion_of_finite] at hdense
    obtain ⟨i₀, hi₀⟩ :=
      isIrreducible_subset_of_subset_iUnion_isClosed hZ_irr
        (fun i => closure (U i ∩ (V i)ᶜ ∩ Z)) (fun _ => isClosed_closure) hZ_sub_clU
    have hZ_sub_VC : Z ⊆ (V i₀)ᶜ := hi₀.trans <| by
      have h2 := closure_mono (s := U i₀ ∩ (V i₀)ᶜ ∩ Z) (fun _ ⟨⟨_, hxV⟩, _⟩ => hxV)
      rwa [(hV_open i₀).isClosed_compl.closure_eq] at h2
    have hUZ_ne : (U i₀ ∩ Z).Nonempty := by
      obtain ⟨z, hz⟩ := hZ_irr.nonempty
      obtain ⟨w, ⟨hwU, _⟩, hwZ⟩ := closure_nonempty_iff.mp ⟨z, hi₀ hz⟩
      exact ⟨w, hwU, hwZ⟩
    refine ⟨U i₀, hU_open i₀, hUZ_ne, fun x ⟨hxU, hxZ⟩ => ⟨?_, hxZ⟩⟩
    rw [hE_eq]
    exact Set.mem_iUnion.mpr ⟨i₀, hxU, hZ_sub_VC hxZ⟩
  · exact Or.inr hdense

/-- A closed nonempty subset that is not irreducible decomposes as a binary union of two proper
closed subsets. -/
lemma exists_binary_reducible_decomposition
    (F : Set X) (hF : IsClosed F) (hne : F.Nonempty) (hni : ¬ IsIrreducible F) :
    ∃ F₁ F₂ : Set X, IsClosed F₁ ∧ IsClosed F₂ ∧ F₁ ⊂ F ∧ F₂ ⊂ F ∧ F = F₁ ∪ F₂ := by
  have hnp : ¬ IsPreirreducible F := fun hp => hni ⟨hne, hp⟩
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hnp
  push Not at hnp
  obtain ⟨C₁, C₂, hC₁, hC₂, hsub, hn₁, hn₂⟩ := hnp
  refine ⟨F ∩ C₁, F ∩ C₂, hF.inter hC₁, hF.inter hC₂,
    ⟨Set.inter_subset_left, fun h => hn₁ fun x hx => (h hx).2⟩,
    ⟨Set.inter_subset_left, fun h => hn₂ fun x hx => (h hx).2⟩, ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_inter_iff]
  refine ⟨fun hxF => (hsub hxF).imp (⟨hxF, ·⟩) (⟨hxF, ·⟩), ?_⟩
  rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

/-- Let `F` be a closed subset of a Noetherian space such that `E ∩ F'` is constructible for every
closed `F' ⊂ F`. If `U ∩ F ⊆ E ∩ F` for an open `U` meeting `F`, then `E ∩ F` is constructible. -/
lemma isConstructibleSet_inter_of_containsNonemptyOpen
    [TopologicalSpace.NoetherianSpace X] (E F : Set X)
    (hF : IsClosed F)
    (IH : ∀ F' : Set X, IsClosed F' → F' ⊂ F → IsConstructibleSet (E ∩ F'))
    (U : Set X) (hU : IsOpen U) (hne : (U ∩ F).Nonempty) (hsub : U ∩ F ⊆ E ∩ F) :
    IsConstructibleSet (E ∩ F) := by
  have hdecomp : E ∩ F = (U ∩ F) ∪ (E ∩ (F \ U)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff, Set.subset_def] at hsub ⊢
    grind
  have hUF : IsConstructibleSet (U ∩ F) :=
    IsLocallyClosed.isConstructibleSet (hU.isLocallyClosed.inter hF.isLocallyClosed)
  have hFU_ssub : F \ U ⊂ F := by
    refine ⟨Set.sdiff_subset, fun hsubset => ?_⟩
    obtain ⟨x, hxU, hxF⟩ := hne
    exact (hsubset hxF).2 hxU
  rw [hdecomp]
  exact hUF.union (IH (F \ U) (hF.sdiff hU) hFU_ssub)

/-- Let `F` be a closed subset of a Noetherian space such that `E ∩ F'` is constructible for every
closed `F' ⊂ F`. If `E ∩ F` is not dense in `F`, then `E ∩ F` is constructible. -/
lemma isConstructibleSet_inter_of_not_isDenseIn
    [TopologicalSpace.NoetherianSpace X] (E F : Set X)
    (hF : IsClosed F)
    (IH : ∀ F' : Set X, IsClosed F' → F' ⊂ F → IsConstructibleSet (E ∩ F'))
    (hnd : ¬ IsDenseIn E F) :
    IsConstructibleSet (E ∩ F) := by
  obtain ⟨x, hxF, hxC⟩ := Set.not_subset.mp hnd
  set G := closure (E ∩ F) ∩ F
  have hG_ssub : G ⊂ F := ⟨Set.inter_subset_right, fun h => hxC (h hxF).1⟩
  have hEF_eq : E ∩ F = E ∩ G :=
    Set.eq_of_subset_of_subset
      (fun _ ⟨hyE, hyF⟩ => ⟨hyE, subset_closure ⟨hyE, hyF⟩, hyF⟩)
      (fun _ ⟨hyE, _, hyF⟩ => ⟨hyE, hyF⟩)
  rw [hEF_eq]
  exact IH G (isClosed_closure.inter hF) hG_ssub

/-- In a Noetherian space, if `E` satisfies the dichotomy on every irreducible closed subset, then
`E ∩ F` is constructible for every closed `F`. -/
@[ega "0 9.2.3" "partial", ega "0 9.3.2" "special case", sga "1 IV 6.1" "sufficiency"]
lemma constructibleSet_inter_of_dichotomy [TopologicalSpace.NoetherianSpace X]
    (E : Set X)
    (h : ∀ Z : Set X, IsIrreducible Z → IsClosed Z →
         ContainsNonemptyOpenOf E Z ∨ ¬ IsDenseIn E Z)
    (F : Set X) (hF : IsClosed F) :
    IsConstructibleSet (E ∩ F) := by
  suffices H : ∀ C : TopologicalSpace.Closeds X, IsConstructibleSet (E ∩ C.carrier) from
    H ⟨F, hF⟩
  intro C
  induction C using WellFoundedLT.induction with
  | _ C ih =>
    set F' := C.carrier
    have hF'cl : IsClosed F' := C.isClosed'
    have IH : ∀ G : Set X, IsClosed G → G ⊂ F' → IsConstructibleSet (E ∩ G) :=
      fun G hG hGlt => ih ⟨G, hG⟩ hGlt
    by_cases hne : F'.Nonempty
    · by_cases hirr : IsIrreducible F'
      · rcases h F' hirr hF'cl with ⟨U, hU, hUne, hUsub⟩ | hB
        · exact isConstructibleSet_inter_of_containsNonemptyOpen E F' hF'cl IH U hU hUne hUsub
        · exact isConstructibleSet_inter_of_not_isDenseIn E F' hF'cl IH hB
      · obtain ⟨F₁, F₂, hF₁, hF₂, hlt₁, hlt₂, hunion⟩ :=
          exists_binary_reducible_decomposition F' hF'cl hne hirr
        rw [show E ∩ F' = (E ∩ F₁) ∪ (E ∩ F₂) by
          rw [hunion, Set.inter_union_distrib_left]]
        exact (IH F₁ hF₁ hlt₁).union (IH F₂ hF₂ hlt₂)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.inter_empty]
      exact isConstructibleSet_empty

/-- Let `X` be a Noetherian topological space and let `E ⊆ X`. Then `E` is
constructible if and only if for every irreducible closed `Z ⊆ X` the intersection `E ∩ Z` either
contains a nonempty open of `Z` or fails to be dense in `Z`. -/
@[stacks 053Z,
  ega "0 9.2.3",
  sga "1 IV 6.1",
  ega "0 9.2.2" "necessity",
  ega "0 9.3.2" "special case",
  ega "IV 9.2.5" "more general"]
theorem constructible_iff_dichotomy_irreducible_closed
    [TopologicalSpace.NoetherianSpace X] (E : Set X) :
    IsConstructibleSet E ↔
      ∀ Z : Set X, IsIrreducible Z → IsClosed Z →
        ContainsNonemptyOpenOf E Z ∨ ¬ IsDenseIn E Z := by
  refine ⟨fun hE Z hZ_irr _ => containsNonemptyOpenOf_or_not_isDenseIn hE Z hZ_irr, fun h => ?_⟩
  simpa using constructibleSet_inter_of_dichotomy E h Set.univ isClosed_univ

open Topology TopologicalSpace in
/-- A function on a Noetherian sober space that is constant on a nonempty open subset of the
closure of each point has constructible level sets. -/
@[ega "0 9.2.3" "partial", ega "0 9.3.2" "sufficiency direction", sga "1 IV 6.1" "special case"]
lemma isConstructible_of_constant_near_genericPoints {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] [QuasiSober T] {A : Type*} (g : T → A)
    (h : ∀ y : T, ∃ V : Opens (closure ({y} : Set T)), Nonempty V ∧ ∃ a, ∀ z : V, g z.1.1 = a)
    (a : A) : IsConstructible {y | g y = a} := by
  have H : IsConstructibleSet {y | g y = a} := by
    refine (constructible_iff_dichotomy_irreducible_closed _).2 fun Z hZ hcZ ↦ ?_
    obtain ⟨V, hV, b, hb⟩ := h hZ.genericPoint
    have e := hZ.closure_genericPoint hcZ
    obtain ⟨U, hU, he⟩ := isOpen_induced_iff.mp V.isOpen
    obtain ⟨z⟩ := hV
    have hzZ : z.1.1 ∈ Z := by simpa only [e] using z.1.2
    have hzU : z.1.1 ∈ U := (Set.ext_iff.mp he z.1).mpr z.2
    have hUb : ∀ x ∈ U ∩ Z, g x = b := fun x hx ↦
      hb ⟨⟨x, by simpa only [e] using hx.2⟩, (Set.ext_iff.mp he _).mp hx.1⟩
    by_cases hab : b = a
    · exact Or.inl ⟨U, hU, ⟨_, hzU, hzZ⟩, fun x hx ↦ ⟨(hUb x hx).trans hab, hx.2⟩⟩
    · refine Or.inr fun hd ↦ ?_
      obtain ⟨x, hxU, hx⟩ := mem_closure_iff.mp (hd hzZ) U hU hzU
      exact hab ((hUb x ⟨hxU, hx.2⟩).symm.trans hx.1)
  obtain ⟨n, U, V, hU, hUr, hV, hVr, e⟩ := H
  rw [e]
  exact IsConstructible.iUnion fun i ↦ ((hUr i).isConstructible (hU i)).inter
    ((hVr i).isConstructible (hV i)).compl
