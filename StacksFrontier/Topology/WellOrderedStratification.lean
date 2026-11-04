module

public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.Topology.Basic

/-!
# Well-ordered stratifications by successively removing open pieces

Let `X` be a topological space and let `f` assign to every closed subset `T ⊆ X` a subset
`f T ⊆ T` which is open in `T` and nonempty when `T` is. Removing `f T` from `T` again gives a
closed set. Iterating transfinitely, starting from `X` and intersecting at limit stages, produces a
strictly decreasing sequence of closed sets, which reaches `∅` because `X` has only a set of
subsets. This is the construction in the proof of **Stacks 06RF**.

## Main results

* `TopologicalSpace.exists_wellOrdered_stratification`: there are a well-ordered index set `I`
  and nonempty closed sets `Tᵢ` with `Tᵢ = X \ ⋃_{j < i} f Tⱼ` and `⋃ᵢ f Tᵢ = X`.
* `TopologicalSpace.stratification_unique`: any two such families for the same `f` are
  order-isomorphic, with the same closed sets.
* `TopologicalSpace.stratificationIndex`, `TopologicalSpace.stratificationSeq`: the stratification
  as a definite object, indexed by the ordinals below the least `α` with `T_α = ∅`
  (`TopologicalSpace.isWellOrderedStratification_stratificationIndex`).

## References

* [Stacks Project, Tag 06RF](https://stacks.math.columbia.edu/tag/06RF)
-/

@[expose] public section

universe v

namespace TopologicalSpace

variable {X : Type v} [TopologicalSpace X]

/-- The transfinite sequence of closed sets `T_α = X \ ⋃_{β < α} f T_β`. -/
private noncomputable def stratSeq (f : Set X → Set X) : Ordinal.{v} → Set X :=
  Ordinal.lt_wf.fix fun α rec => Set.univ \ ⋃ (β : Ordinal.{v}) (h : β < α), f (rec β h)

omit [TopologicalSpace X] in
private lemma stratSeq_eq (f : Set X → Set X) (α : Ordinal.{v}) :
    stratSeq f α = Set.univ \ ⋃ (β : Ordinal.{v}) (_ : β < α), f (stratSeq f β) :=
  Ordinal.lt_wf.fix_eq _ α

omit [TopologicalSpace X] in
private lemma stratSeq_antitone (f : Set X → Set X) {α β : Ordinal.{v}} (h : β ≤ α) :
    stratSeq f α ⊆ stratSeq f β := by
  rw [stratSeq_eq f α, stratSeq_eq f β]
  refine Set.diff_subset_diff_right (Set.iUnion₂_subset fun γ hγ => ?_)
  exact Set.subset_iUnion₂_of_subset γ (lt_of_lt_of_le hγ h) le_rfl

omit [TopologicalSpace X] in
private lemma disjoint_stratSeq (f : Set X → Set X) (hsub : ∀ T, f T ⊆ T)
    {α β : Ordinal.{v}} (h : β < α) : Disjoint (f (stratSeq f α)) (f (stratSeq f β)) := by
  rw [Set.disjoint_left]
  intro x hxα hxβ
  have hx := hsub _ hxα
  rw [stratSeq_eq f α] at hx
  exact hx.2 (Set.mem_iUnion₂.2 ⟨β, h, hxβ⟩)

variable (f : Set X → Set X) (hsub : ∀ T, f T ⊆ T)
  (hopen : ∀ T, IsClosed T → ∃ O, IsOpen O ∧ f T = T ∩ O)
  (hne : ∀ T, IsClosed T → T.Nonempty → (f T).Nonempty)

include hsub hopen in
private lemma isClosed_stratSeq (α : Ordinal.{v}) : IsClosed (stratSeq f α) := by
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    choose O hO hfO using fun (β : Ordinal.{v}) (h : β < α) => hopen _ (ih β h)
    rw [stratSeq_eq f α, ← Set.compl_eq_univ_sdiff, isClosed_compl_iff]
    have hlow : ∀ β < α, ∀ x, x ∉ stratSeq f β →
        x ∈ ⋃ (γ : Ordinal.{v}) (_ : γ < α), f (stratSeq f γ) := by
      intro β h x hx
      rw [stratSeq_eq f β] at hx
      simp only [Set.mem_diff, Set.mem_univ, true_and, not_not] at hx
      obtain ⟨γ, hγ, hxγ⟩ := Set.mem_iUnion₂.1 hx
      exact Set.mem_iUnion₂.2 ⟨γ, hγ.trans h, hxγ⟩
    have heq : (⋃ (β : Ordinal.{v}) (_ : β < α), f (stratSeq f β)) =
        ⋃ (β : Ordinal.{v}) (h : β < α), ((stratSeq f β)ᶜ ∪ O β h) := by
      apply le_antisymm
      · refine Set.iUnion₂_subset fun β h => ?_
        rw [hfO β h]
        exact Set.subset_iUnion₂_of_subset β h
          (Set.inter_subset_right.trans Set.subset_union_right)
      · refine Set.iUnion₂_subset fun β h => Set.union_subset ?_ ?_
        · exact fun x hx => hlow β h x hx
        · intro x hx
          by_cases hxT : x ∈ stratSeq f β
          · exact Set.mem_iUnion₂.2 ⟨β, h, by rw [hfO β h]; exact ⟨hxT, hx⟩⟩
          · exact hlow β h x hxT
    rw [heq]
    exact isOpen_iUnion fun β => isOpen_iUnion fun h => ((ih β h).isOpen_compl).union (hO β h)

include hsub hopen hne in
private lemma exists_stratSeq_eq_empty : ∃ α : Ordinal.{v}, stratSeq f α = ∅ := by
  by_contra hall
  push Not at hall
  have key : ∀ α β : Ordinal.{v}, β < α → f (stratSeq f α) ≠ f (stratSeq f β) := by
    intro α β hlt h
    have hd := disjoint_stratSeq f hsub hlt
    rw [h, disjoint_self, Set.bot_eq_empty] at hd
    exact (hne _ (isClosed_stratSeq f hsub hopen β) (hall β)).ne_empty hd
  have hinj : Function.Injective fun α : Ordinal.{v} => f (stratSeq f α) := fun α β h =>
    (lt_trichotomy α β).elim (fun hlt => (key β α hlt h.symm).elim)
      fun h' => h'.elim id fun hlt => (key α β hlt h).elim
  exact not_injective_of_ordinal _ hinj

omit [TopologicalSpace X] in
/-- The stratification indexed by the ordinals below the first `α₀` with `T_{α₀} = ∅`. -/
private lemma stratSeq_Iio_stratification (α₀ : Ordinal.{v})
    (hα₀ : stratSeq f α₀ = ∅) (hmin : ∀ β < α₀, (stratSeq f β).Nonempty) :
    (∀ i : Set.Iio α₀, stratSeq f i =
      Set.univ \ ⋃ (j : Set.Iio α₀) (_ : j < i), f (stratSeq f j)) ∧
      (∀ i : Set.Iio α₀, (stratSeq f i).Nonempty) ∧
      (⋃ i : Set.Iio α₀, f (stratSeq f i)) = Set.univ := by
  have hreindex : ∀ β ≤ α₀, (⋃ (j : Set.Iio α₀) (_ : j.1 < β), f (stratSeq f j.1)) =
      ⋃ (γ : Ordinal.{v}) (_ : γ < β), f (stratSeq f γ) := fun β hβ => by
    ext x
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨fun ⟨j, hj, hx⟩ => ⟨j.1, hj, hx⟩, fun ⟨γ, hγ, hx⟩ => ⟨⟨γ, hγ.trans_le hβ⟩, hγ, hx⟩⟩
  refine ⟨fun i => ?_, fun i => hmin i.1 i.2, ?_⟩
  · show stratSeq f i.1 = Set.univ \ ⋃ (j : Set.Iio α₀) (_ : j.1 < i.1), f (stratSeq f j.1)
    rw [stratSeq_eq f i.1, hreindex i.1 i.2.le]
  · have h := stratSeq_eq f α₀
    rw [hα₀, ← hreindex α₀ le_rfl] at h
    refine Set.eq_univ_of_univ_subset ((Set.diff_eq_empty.1 h.symm).trans ?_)
    exact Set.iUnion₂_subset fun j _ => Set.subset_iUnion_of_subset j subset_rfl

include hsub hopen hne in
/-- **The well-ordered stratification.** If `f` assigns to every closed `T ⊆ X` a subset
`f T ⊆ T`, open in `T` and nonempty when `T` is, then there are a well-ordered index set `I` and
nonempty closed sets `Tᵢ` with `Tᵢ = X \ ⋃_{j < i} f Tⱼ` for every `i` and `⋃ᵢ f Tᵢ = X`. -/
theorem exists_wellOrdered_stratification :
    ∃ (I : Type (v + 1)) (_ : LinearOrder I) (_ : WellFoundedLT I) (T : I → Set X),
      (∀ i, T i = Set.univ \ ⋃ (j : I) (_ : j < i), f (T j)) ∧ (∀ i, IsClosed (T i)) ∧
        (∀ i, (T i).Nonempty) ∧ (⋃ i, f (T i)) = Set.univ := by
  obtain ⟨α, hα⟩ := exists_stratSeq_eq_empty f hsub hopen hne
  let α₀ := Ordinal.lt_wf.min {α | stratSeq f α = ∅} ⟨α, hα⟩
  have hα₀ : stratSeq f α₀ = ∅ := Ordinal.lt_wf.min_mem {α | stratSeq f α = ∅} ⟨α, hα⟩
  have hmin : ∀ β < α₀, (stratSeq f β).Nonempty := fun β hβ =>
    Set.nonempty_iff_ne_empty.2 fun h =>
      Ordinal.lt_wf.not_lt_min {α | stratSeq f α = ∅} h hβ
  obtain ⟨h1, h2, h3⟩ := stratSeq_Iio_stratification f α₀ hα₀ hmin
  exact ⟨Set.Iio α₀, inferInstance, inferInstance, fun i => stratSeq f i.1, h1,
    fun i => isClosed_stratSeq f hsub hopen i.1, h2, h3⟩

omit [TopologicalSpace X] in
/-- An initial segment between two well-ordered stratifications for the same `f` matches their
sets and is surjective, hence an order isomorphism. -/
private lemma exists_orderIso_of_initialSeg (f : Set X → Set X) (hsub : ∀ T, f T ⊆ T)
    {I : Type*} [LinearOrder I] [WellFoundedLT I] (T : I → Set X)
    (hT : ∀ i, T i = Set.univ \ ⋃ (j : I) (_ : j < i), f (T j))
    (hTcov : (⋃ i, f (T i)) = Set.univ)
    {I' : Type*} [LinearOrder I'] [WellFoundedLT I'] (T' : I' → Set X)
    (hT' : ∀ i, T' i = Set.univ \ ⋃ (j : I') (_ : j < i), f (T' j))
    (hT'ne : ∀ i, (f (T' i)).Nonempty)
    (g : @InitialSeg I I' (· < ·) (· < ·)) :
    ∃ e : I ≃o I', ∀ i, T' (e i) = T i := by
  have hg : ∀ i, T' (g i) = T i := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      rw [hT' (g i), hT i]
      congr 1
      ext x
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨j', hj', hx⟩
        obtain ⟨j, rfl⟩ := g.mem_range_of_rel hj'
        have hji : j < i := g.map_rel_iff.1 hj'
        exact ⟨j, hji, by rwa [← ih j hji]⟩
      · rintro ⟨j, hj, hx⟩
        exact ⟨g j, g.map_rel_iff.2 hj, by rwa [ih j hj]⟩
  have hsurj : Function.Surjective g := by
    by_contra hns
    have hne : (Set.range g)ᶜ.Nonempty := Set.nonempty_compl.2 (mt Set.range_eq_univ.1 hns)
    let m := wellFounded_lt.min _ hne
    have hm : m ∉ Set.range g := wellFounded_lt.min_mem _ hne
    have hlt : ∀ j : I, g j < m := by
      intro j
      rcases lt_trichotomy (g j) m with h | h | h
      · exact h
      · exact absurd ⟨j, h⟩ hm
      · exact absurd (g.mem_range_of_rel h) hm
    have hempty : T' m = ∅ := by
      rw [hT' m]
      apply Set.diff_eq_empty.2
      intro x _
      have hx : x ∈ ⋃ i, f (T i) := hTcov ▸ Set.mem_univ x
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      exact Set.mem_iUnion₂.2 ⟨g j, hlt j, by rwa [hg j]⟩
    exact (hT'ne m).ne_empty (Set.subset_eq_empty (hsub _) hempty)
  exact ⟨OrderIso.ofRelIsoLT (RelIso.ofSurjective g.toRelEmbedding hsurj), hg⟩

omit [TopologicalSpace X] in
/-- **The well-ordered stratification is canonical.** Two well-ordered families of nonempty sets
`Tᵢ = X \ ⋃_{j < i} f Tⱼ` whose pieces `f Tᵢ` cover `X` are isomorphic: there is an order
isomorphism of the index sets matching the sets. -/
theorem stratification_unique (f : Set X → Set X) (hsub : ∀ T, f T ⊆ T)
    {I : Type*} [LinearOrder I] [WellFoundedLT I] (T : I → Set X)
    (hT : ∀ i, T i = Set.univ \ ⋃ (j : I) (_ : j < i), f (T j)) (hTne : ∀ i, (f (T i)).Nonempty)
    (hTcov : (⋃ i, f (T i)) = Set.univ)
    {I' : Type*} [LinearOrder I'] [WellFoundedLT I'] (T' : I' → Set X)
    (hT' : ∀ i, T' i = Set.univ \ ⋃ (j : I') (_ : j < i), f (T' j))
    (hT'ne : ∀ i, (f (T' i)).Nonempty) (hT'cov : (⋃ i, f (T' i)) = Set.univ) :
    ∃ e : I ≃o I', ∀ i, T' (e i) = T i := by
  rcases InitialSeg.total (α := I) (β := I') (· < ·) (· < ·) with g | g
  · exact exists_orderIso_of_initialSeg f hsub T hT hTcov T' hT' hT'ne g
  · obtain ⟨e, he⟩ := exists_orderIso_of_initialSeg f hsub T' hT' hT'cov T hT hTne g
    exact ⟨e.symm, fun i => by rw [← he (e.symm i), OrderIso.apply_symm_apply]⟩

/-! ### The canonical stratification as a definite object

The transfinite sequence `T_α` is a definite function of `f`, and so is the least ordinal at which
it becomes empty; the well-ordered index set of the stratification is the set of ordinals below it.
By `stratification_unique` every other stratification for the same `f` is order-isomorphic to this
one, with the same sets. -/

omit [TopologicalSpace X] in
/-- **The canonical sequence of closed sets** `T_α = X \ ⋃_{β < α} f T_β`, indexed by all ordinals
of the universe of `X`. -/
noncomputable def stratificationSeq (f : Set X → Set X) : Ordinal.{v} → Set X :=
  Ordinal.lt_wf.fix fun α rec => Set.univ \ ⋃ (β : Ordinal.{v}) (h : β < α), f (rec β h)

omit [TopologicalSpace X] in
/-- The canonical sequence is the sequence of the construction above. -/
private lemma stratificationSeq_eq_stratSeq (f : Set X → Set X) :
    stratificationSeq f = stratSeq f :=
  rfl

omit [TopologicalSpace X] in
/-- The defining recursion of `stratificationSeq`. -/
theorem stratificationSeq_eq (f : Set X → Set X) (α : Ordinal.{v}) :
    stratificationSeq f α = Set.univ \ ⋃ (β : Ordinal.{v}) (_ : β < α), f (stratificationSeq f β) :=
  Ordinal.lt_wf.fix_eq _ α

omit [TopologicalSpace X] in
/-- **The length of the canonical stratification**: the least ordinal `α` with `T_α = ∅`. -/
noncomputable def stratificationLength (f : Set X → Set X) : Ordinal.{v} :=
  sInf {α | stratificationSeq f α = ∅}

omit [TopologicalSpace X] in
/-- **The index set of the canonical stratification**: the ordinals below its length, well-ordered
by the order of ordinals. -/
def stratificationIndex (f : Set X → Set X) : Set Ordinal.{v} :=
  Set.Iio (stratificationLength f)

omit [TopologicalSpace X] in
/-- The closed sets `T_α` indexed by the canonical index set are nonempty. -/
theorem stratificationSeq_nonempty (f : Set X → Set X) {α : Ordinal.{v}}
    (hα : α ∈ stratificationIndex f) :
    (stratificationSeq f α).Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun h =>
    (csInf_le' (s := {α : Ordinal.{v} | stratificationSeq f α = ∅}) h).not_gt hα

include hsub hopen in
/-- The sets `T_α` are closed. -/
theorem isClosed_stratificationSeq (α : Ordinal.{v}) : IsClosed (stratificationSeq f α) := by
  rw [stratificationSeq_eq_stratSeq]
  exact isClosed_stratSeq f hsub hopen α

include hsub hopen hne in
/-- The canonical sequence reaches `∅` at its length. -/
theorem stratificationSeq_stratificationLength :
    stratificationSeq f (stratificationLength f) = ∅ :=
  csInf_mem (s := {α | stratificationSeq f α = ∅}) (by
    rw [stratificationSeq_eq_stratSeq]
    exact exists_stratSeq_eq_empty f hsub hopen hne)

include hsub hopen hne in
/-- **The canonical well-ordered stratification.** Indexed by `stratificationIndex f`, the closed
sets `T_α` satisfy `T_α = X \ ⋃_{β < α} f T_β`, are nonempty, and the pieces `f T_α` cover `X`; so
this is the stratification of `exists_wellOrdered_stratification`, made definite. -/
theorem isWellOrderedStratification_stratificationIndex :
    (∀ i : stratificationIndex f, stratificationSeq f i =
      Set.univ \ ⋃ (j : stratificationIndex f) (_ : j < i), f (stratificationSeq f j)) ∧
      (∀ i : stratificationIndex f, IsClosed (stratificationSeq f i)) ∧
      (∀ i : stratificationIndex f, (stratificationSeq f i).Nonempty) ∧
      (⋃ i : stratificationIndex f, f (stratificationSeq f i)) = Set.univ := by
  obtain ⟨h1, h2, h3⟩ := stratSeq_Iio_stratification f (stratificationLength f)
    (stratificationSeq_stratificationLength f hsub hopen hne) fun β hβ =>
    stratificationSeq_nonempty f hβ
  exact ⟨h1, fun i => isClosed_stratificationSeq f hsub hopen i.1, h2, h3⟩

end TopologicalSpace

end
