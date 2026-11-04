module

public import StacksFrontier.AlgebraicGeometry.Stacks.C1575Private.ChowGerbeIsomFlatCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparationLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition

/-!
# The induction on the number of opens (proof of Stacks 0CQ7)

This file carries the proof of [Stacks, Tag 0CQ7] from the situation labelled (b) there to a
section cover, in the relative form of
`AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos.StageData`.

* **Stage (d).** If `V' ⊆ W_k` for every `k`, the pairs `(x_0, x_k)` are handled one at a time:
  each application of Stacks 0CQ6 to an `Isom` space (after a finite surjective cover) makes
  `x_0` and `x_k` Zariski locally isomorphic over `V'`, and this survives the later covers; with
  all pairs handled, stage (e) gives a section cover.
* **Stage (b).** By induction on the number `n` of opens. Put `V'₀ = V' ∩ W_0 ∩ ⋯ ∩ W_{n-1}`, which
  is stage (d), and for each `i` let `Y_i ⊆ Y'` be the reduced closed subspace on the complement
  of `W_i`. Pulled back to `Y_i`, the opens other than `W_i` still cover, so the induction
  hypothesis applies. Every point of `V'` is either in all `W_i` or in some `Y_i`, so the finite
  union of the section covers reaches the image of `V'`. This replaces the source's
  `Y ⨿ ∐ Y_i ⟶ Y`: the modifications here carry the disjoint union in the section cover.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos.StageData.sectionCover_of_le`
* `AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos.StageData.sectionCover`

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.PresheafOfCategories

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos

open ChowGerbeMerge ChowGerbeSectionCover

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
  {W V : Subfunctor Y} {n : ℕ}

/-! ### Reindexing the opens and shrinking `V'` -/

/-- Reindex the opens along `σ`, keeping the first `m` of them as the covering ones. -/
def StageData.reindex (D : StageData hY f W V n) (σ : ℕ → ℕ) (m : ℕ)
    (h : Set.range (Space.pointsMap B S hS (W.preimage D.p).toFunctor (W.preimage D.p).ι) ⊆
      ⋃ j : Fin m, Set.range (Space.pointsMap B S hS (D.Wi (σ j)).1.toFunctor (D.Wi (σ j)).1.ι)) :
    StageData hY f W V m :=
  { D with
    Wi := fun j => D.Wi (σ j)
    hWiqc := fun _ => D.hWiqc _
    hcov := h
    x := fun j => D.x (σ j)
    hx := fun _ => D.hx _ }

/-- Replace `V'` by a smaller quasi-compact open. -/
def StageData.restrictV (D : StageData hY f W V n) (V'' : Space.OpenSubspaces B S hS D.Y'.1)
    (hqc : Space.IsQuasiCompactSpace B S hS V''.1.toFunctor) (hle : V''.1 ≤ D.V'.1) :
    StageData hY f W V n :=
  { D with
    V' := V''
    hV'qc := hqc
    hV'V := hle.trans D.hV'V
    hV'W := hle.trans D.hV'W }

/-! ### Stage (d) -/

/-- **Stage (d) of the proof of Stacks 0CQ7 gives a section cover.** If `V' ⊆ W_k` for every `k`,
the pairs `(x_0, x_k)` for `k < n` are made Zariski locally isomorphic over `V'` one at a time,
each by a finite surjective cover (`StageData.exists_pullback_locIso`); the isomorphisms already
found survive (`StageData.locIso_pullback`) and the image of `V'` does not shrink; then stage (e)
gives the section cover. -/
theorem StageData.sectionCover_of_le (hf : IsSeparated B S hS f)
    (hW : Space.IsOpenSubspace B S hS W) (hV : Space.IsOpenSubspace B S hS V)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    (D : StageData hY f W V n) (hVW : ∀ k, D.V'.1 ≤ (D.Wi k).1) :
    SectionCover hY f W D.image := by
  have key : ∀ m, ∃ (D' : StageData hY f W V n) (hVW' : ∀ k, D'.V'.1 ≤ (D'.Wi k).1),
      D.image ⊆ D'.image ∧ ∀ k < m, D'.LocIso hVW' k := by
    intro m
    induction m with
    | zero => exact ⟨D, hVW, le_rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ m ih =>
      obtain ⟨D', hVW', hsub, hloc⟩ := ih
      obtain ⟨Y'', hY'', g, hg, hgs, hnew⟩ := D'.exists_pullback_locIso hV hG hVW' m
      refine ⟨D'.pullback hY'' g hg, D'.pullback_le hY'' g hg hVW',
        hsub.trans (D'.image_subset_pullback hY'' g hg hgs), fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact D'.locIso_pullback hY'' g hg hVW' (hloc k hk)
      · exact hnew
  obtain ⟨D', hVW', hsub, hloc⟩ := key n
  exact (D'.sectionCover_of_locallyIso hf hW hVW' hloc).mono hsub

/-! ### The intersection of `V'` with the first opens -/

/-- `V' ∩ W_0 ∩ ⋯ ∩ W_{j-1}`. -/
def StageData.infOpen (D : StageData hY f W V n) : ℕ → Subfunctor D.Y'.1
  | 0 => D.V'.1
  | j + 1 => D.infOpen j ⊓ (D.Wi j).1

/-- Each `D.infOpen j` is an open subspace of `D.Y'`. -/
theorem StageData.isOpenSubspace_infOpen (D : StageData hY f W V n) :
    ∀ j, Space.IsOpenSubspace B S hS (D.infOpen j)
  | 0 => D.V'.2
  | j + 1 => Space.isOpenSubspace_inf B S hS D.Y'.2 _ _ (D.isOpenSubspace_infOpen j) (D.Wi j).2

/-- Each `D.infOpen j` is quasi-compact. -/
theorem StageData.isQuasiCompactSpace_infOpen (D : StageData hY f W V n) :
    ∀ j, Space.IsQuasiCompactSpace B S hS (D.infOpen j).toFunctor
  | 0 => D.hV'qc
  | j + 1 => isQuasiCompactSpace_inf D.Y'.2 D.qs (D.isOpenSubspace_infOpen j)
      (D.isQuasiCompactSpace_infOpen j) (D.hWiqc j)

/-- Each `D.infOpen j` is contained in `V'`. -/
theorem StageData.infOpen_le (D : StageData hY f W V n) : ∀ j, D.infOpen j ≤ D.V'.1
  | 0 => le_rfl
  | j + 1 => inf_le_left.trans (D.infOpen_le j)

/-- For `k < j`, `D.infOpen j` is contained in `W_k`. -/
theorem StageData.infOpen_le_Wi (D : StageData hY f W V n) :
    ∀ j, ∀ k < j, D.infOpen j ≤ (D.Wi k).1
  | 0, k, hk => absurd hk (Nat.not_lt_zero k)
  | j + 1, k, hk => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact inf_le_left.trans (D.infOpen_le_Wi j k hk)
    · exact inf_le_right

/-- A point of `V'` lying in `W_k` for every `k < j` lies in `D.infOpen j`. -/
theorem StageData.mem_infOpen (D : StageData hY f W V n) :
    ∀ j, ∀ t ∈ Space.subspacePointSet B S hS D.Y'.1 D.V'.1,
      (∀ k < j, t ∈ Space.subspacePointSet B S hS D.Y'.1 (D.Wi k).1) →
        t ∈ Space.subspacePointSet B S hS D.Y'.1 (D.infOpen j)
  | 0, _, ht, _ => ht
  | j + 1, t, ht, hk => by
    show t ∈ Space.subspacePointSet B S hS D.Y'.1 (D.infOpen j ⊓ (D.Wi j).1)
    rw [Space.subspacePointSet_inf]
    exact ⟨D.mem_infOpen j t ht fun k hk' => hk k (Nat.lt_succ_of_lt hk'),
      hk j (Nat.lt_succ_self j)⟩

/-! ### Stage (b) -/

/-- The reindexing that skips the `i`-th open. -/
def skipIdx (i : ℕ) (j : ℕ) : ℕ := if j < i then j else j + 1

/-- **Stage (b) of the proof of Stacks 0CQ7 gives a section cover**, by induction on the number of
opens (see the module documentation). -/
theorem StageData.sectionCover (hf : IsSeparated B S hS f)
    (hW : Space.IsOpenSubspace B S hS W) (hV : Space.IsOpenSubspace B S hS V)
    (hG : IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst)
    (D : StageData hY f W V n) : SectionCover hY f W D.image := by
  classical
  induction n with
  | zero => exact D.sectionCover_zero hW
  | succ m ih =>
  -- the piece over `V' ∩ W_0 ∩ ⋯ ∩ W_m`
  let Dc := D.reindex (clampIdx m) (m + 1) (fun y hy => by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (D.hcov hy)
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    rw [clampIdx_of_lt j.2]
    exact hj)
  let D₀ := Dc.restrictV ⟨D.infOpen (m + 1), D.isOpenSubspace_infOpen (m + 1)⟩
    (D.isQuasiCompactSpace_infOpen (m + 1)) (D.infOpen_le (m + 1))
  have h₀ : SectionCover hY f W D₀.image :=
    D₀.sectionCover_of_le hf hW hV hG fun k =>
      D.infOpen_le_Wi (m + 1) (clampIdx m k) (clampIdx_lt m k)
  -- the pieces over the closed complements of the `W_i`
  have hclosed : ∀ i, _root_.IsClosed
      (Set.range (Space.pointsMap B S hS (D.Wi i).1.toFunctor (D.Wi i).1.ι))ᶜ := fun i =>
    (Space.isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (D.Wi i).2.2).isClosed_compl
  let C : ℕ → Subfunctor D.Y'.1 := fun i =>
    Space.reducedClosedSubspace B S hS D.Y'.1 D.Y'.2 _ (hclosed i)
  have hC : ∀ i, Space.IsClosedSubspace B S hS (C i) := fun i =>
    Space.isClosedSubspace_reducedClosedSubspace' B S hS D.Y'.2 _ (hclosed i)
  have hCpts : ∀ i, Set.range (Space.pointsMap B S hS (C i).toFunctor (C i).ι) =
      (Set.range (Space.pointsMap B S hS (D.Wi i).1.toFunctor (D.Wi i).1.ι))ᶜ := fun i =>
    Space.range_pointsMap_ι_reducedClosedSubspace B S hS D.Y'.1 D.Y'.2 _ (hclosed i)
  have hCp : ∀ i, Space.IsProper B S hS (C i).ι := fun i =>
    Space.isProper_of_isClosedImmersion B S hS (hC i).1 D.Y'.2 (C i).ι (hC i).2
  let Di : ℕ → StageData hY f W V (m + 1) := fun i => D.pullback (hC i).1 (C i).ι (hCp i)
  have hi : ∀ i < m + 1, SectionCover hY f W (Di i).image := by
    intro i hi
    refine ih ((Di i).reindex (skipIdx i) m fun y hy => ?_)
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 ((Di i).hcov hy)
    have hk' : Space.pointsMap B S hS _ (C i).ι y ∈
        Set.range (Space.pointsMap B S hS (D.Wi k).1.toFunctor (D.Wi k).1.ι) := by
      change y ∈ Set.range (Space.pointsMap B S hS ((D.Wi k).1.preimage (C i).ι).toFunctor
        ((D.Wi k).1.preimage (C i).ι).ι) at hk
      rwa [Space.range_pointsMap_preimage_ι] at hk
    have hki : (k : ℕ) ≠ i := by
      rintro hki
      have hyC : Space.pointsMap B S hS _ (C i).ι y ∈
          Set.range (Space.pointsMap B S hS (C i).toFunctor (C i).ι) := ⟨y, rfl⟩
      rw [hCpts i] at hyC
      exact hyC (hki ▸ hk')
    have hj : (if (k : ℕ) < i then (k : ℕ) else (k : ℕ) - 1) < m := by
      have := k.2
      split_ifs <;> omega
    refine Set.mem_iUnion.2 ⟨⟨_, hj⟩, ?_⟩
    have hs : skipIdx i (if (k : ℕ) < i then (k : ℕ) else (k : ℕ) - 1) = k := by
      unfold skipIdx
      split_ifs <;> omega
    show y ∈ Set.range (Space.pointsMap B S hS ((Di i).Wi (skipIdx i _)).1.toFunctor
      ((Di i).Wi (skipIdx i _)).1.ι)
    rw [hs]
    exact hk
  -- the finite union
  let A : Option (ULift.{u} (Fin (m + 1))) → Set (Space.points B S hS Y)
    | none => D₀.image
    | some i => (Di i.down).image
  have hA : ∀ k, SectionCover hY f W (A k)
    | none => h₀
    | some i => hi i.down i.down.2
  refine (SectionCover.iUnion hW A hA).mono ?_
  rintro _ ⟨v, rfl⟩
  set t := Space.pointsMap B S hS _ D.V'.1.ι v with ht
  by_cases hall : ∀ k < m + 1, t ∈ Space.subspacePointSet B S hS D.Y'.1 (D.Wi k).1
  · obtain ⟨v₀, hv₀⟩ := D.mem_infOpen (m + 1) t ⟨v, rfl⟩ hall
    refine Set.mem_iUnion.2 ⟨none, v₀, ?_⟩
    show Space.pointsMap B S hS _ ((D.infOpen (m + 1)).ι ≫ D.p) v₀ = _
    rw [Space.pointsMap_comp_apply, hv₀, ← Space.pointsMap_comp_apply]
  · push Not at hall
    obtain ⟨i, hi, hti⟩ := hall
    have htC : t ∈ Set.range (Space.pointsMap B S hS (C i).toFunctor (C i).ι) := by
      rw [hCpts i]
      exact hti
    obtain ⟨s, hs⟩ := htC
    have hs' : s ∈ Set.range (Space.pointsMap B S hS (D.V'.1.preimage (C i).ι).toFunctor
        (D.V'.1.preimage (C i).ι).ι) := by
      rw [Space.range_pointsMap_preimage_ι]
      exact ⟨v, (hs.trans ht).symm⟩
    obtain ⟨s', rfl⟩ := hs'
    refine Set.mem_iUnion.2 ⟨some ⟨⟨i, hi⟩⟩, s', ?_⟩
    show Space.pointsMap B S hS _ ((D.V'.1.preimage (C i).ι).ι ≫ (C i).ι ≫ D.p) s' = _
    rw [Space.pointsMap_comp_apply, Space.pointsMap_comp_apply, hs, ht,
      ← Space.pointsMap_comp_apply]

end AlgebraicGeometry.Stack.AlgebraicStacks.ChowGerbeLocalIsos

end
