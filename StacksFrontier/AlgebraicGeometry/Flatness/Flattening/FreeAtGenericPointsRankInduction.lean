module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsChartIsoLocus
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeAtGenericPointsLocality
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ImmersionLocalRepresentatives

/-!
# The induction on the maximal rank for the generic-rank functors

In Situation 05MP the functors `H_p` of Stacks 05MR are represented by immersions into the base.
This file carries out the last paragraphs of the source's proof of Stacks 05UC. Around every
point `s` of the base there is a chart whose number of generators is the rank `p(s)` at `s`; over
the chart's base `H_{p(s)}` is represented by a closed immersion (Theorem 05PF), `H_q` is empty for
`q > p(s)`, and on the complement of the closed stratum the rank drops, so that `H_q` for
`q < p(s)` is represented there by induction on the maximal rank. The local representatives are
glued along the charts (Stacks 02W5, 02W8, 02YM). Quasi-compactness over affine opens is carried
along the induction when the module is of finite presentation: the complement of a closed
immersion of finite presentation into an affine scheme is quasi-compact.

## Main results

* `AlgebraicGeometry.FreeAtGenericPointsSituation.exists_representsOn_of_rankBound`: over an open
  where the ranks are bounded, every `H_p` is represented by an immersion.
* `AlgebraicGeometry.FreeAtGenericPointsSituation.exists_representsOn_top`: every `H_p` is
  represented by an immersion into the base.

Both take as inputs the existence of a rank at every point and the existence of charts adapted to
a given rank.

## References

* [Stacks Project, Tag 05UC](https://stacks.math.columbia.edu/tag/05UC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace FreeAtGenericPointsSituation

open Stacks.Flatness

variable (D : FreeAtGenericPointsSituation.{u})

/-- The generic-point condition of rank `p`, as a property of morphisms into the base. -/
def condProp (p : ℕ) : ∀ T : Scheme.{u}, (T ⟶ D.S) → Prop :=
  fun _ a ↦ D.Condition p (Over.mk a)

/-- The generic-point condition of rank `p` is stable under precomposition. -/
theorem condProp_comp (p : ℕ) {T T' : Scheme.{u}} (g : T' ⟶ T) (a : T ⟶ D.S)
    (h : D.condProp p T a) : D.condProp p T' (g ≫ a) :=
  D.condition_of_hom p (Over.homMk g rfl : Over.mk (g ≫ a) ⟶ Over.mk a) h

/-- The generic-point condition of rank `p` holds for a morphism if it holds on each member of an
open cover of its source. -/
theorem condProp_sheaf (p : ℕ) {T : Scheme.{u}} (a : T ⟶ D.S) {K : Type u} (O : K → T.Opens)
    (hO : ∀ t, ∃ k, t ∈ O k) (h : ∀ k, D.condProp p _ ((O k).ι ≫ a)) : D.condProp p T a :=
  D.condition_of_openCover p a O hO h

/-- The generic-point conditions of two ranks cannot both hold over a nonempty scheme. -/
theorem eq_of_condition_of_condition {T : Over D.S} {p q : ℕ} (hp : D.Condition p T)
    (hq : D.Condition q T) (t : T.left) : p = q := by
  obtain ⟨ξ, hξ⟩ := D.exists_isGenericPoint_fiber_baseChangeMap T t
  exact freeAtPointOfRank_unique _ (hp t ξ hξ) (hq t ξ hξ)

/-- The rank of the situation at a point of the base: the generic-point condition over the
residue field. -/
abbrev RankAt (q : ℕ) (s : D.S) : Prop :=
  D.Condition q (Over.mk (D.S.fromSpecResidueField s))

/-- The ranks at the points of an open are at most `n`. -/
def RankBound (W : D.S.Opens) (n : ℕ) : Prop :=
  ∀ s ∈ W, ∀ q, D.RankAt q s → q ≤ n

variable {D}

namespace Chart

variable (c : D.Chart)

/-- A morphism with image in the chart's base factors through it. -/
theorem exists_lift {T : Scheme.{u}} (a : T ⟶ D.S) (ha : Set.range a.base ⊆ c.V) :
    ∃ a' : T ⟶ c.V.toScheme, a' ≫ c.V.ι = a :=
  ⟨IsOpenImmersion.lift c.V.ι a (by rwa [Scheme.Opens.range_ι]),
    IsOpenImmersion.lift_fac _ _ _⟩

/-- The residue field map at a point of the chart's base factors through the chart, and the
rank condition at that point transfers along the factorization. -/
private theorem exists_lift_residueField {s : D.S} (hs : s ∈ c.V) {q : ℕ} (hq : D.RankAt q s) :
    ∃ a' : Spec (D.S.residueField s) ⟶ c.V.toScheme,
      a' ≫ c.V.ι = D.S.fromSpecResidueField s ∧ D.Condition q (Over.mk (a' ≫ c.V.ι)) := by
  obtain ⟨a', ha'⟩ := c.exists_lift (D.S.fromSpecResidueField s) (by
    rw [Scheme.range_fromSpecResidueField]; simpa using hs)
  exact ⟨a', ha', by rw [ha']; exact hq⟩

/-- A compact open of the base pulls back to a compact open of the chart's base. -/
private theorem isCompact_preimage_ι {U : D.S.Opens} (hU : (U : Set D.S) ⊆ c.V)
    (hUaff : IsAffineOpen U) :
    IsCompact ((c.V.ι ⁻¹ᵁ U : c.V.toScheme.Opens) : Set c.V.toScheme) := by
  refine (c.V.ι.isOpenEmbedding.isInducing.isCompact_preimage_iff ?_).mpr hUaff.isCompact
  rw [Scheme.Opens.range_ι]; exact hU

/-- The ranks at the points of the chart's base are at most the chart's number of generators. -/
theorem rankBound : D.RankBound c.V c.n := by
  intro s hs q hq
  by_contra hlt
  obtain ⟨a', -, h⟩ := c.exists_lift_residueField hs hq
  have := c.isEmpty_of_condition a' (not_le.mp hlt) h
  exact this.false (IsLocalRing.closedPoint (D.S.residueField s))

end Chart

/-- The empty scheme represents a property which holds only over the empty scheme. -/
theorem representsOn_empty {S : Scheme.{u}} (P : ∀ T : Scheme.{u}, (T ⟶ S) → Prop)
    (V : S.Opens)
    (h : ∀ (T : Scheme.{u}) (a : T ⟶ S), Set.range a.base ⊆ V → (P T a ↔ IsEmpty T)) :
    RepresentsOn P V (Scheme.emptyTo S) := by
  refine ⟨inferInstance, ?_, fun T a ha ↦ ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact (IsEmpty.false x).elim
  · rw [h T a ha]
    constructor
    · intro hT
      exact ⟨isInitialOfIsEmpty.to _, isInitialOfIsEmpty.hom_ext _ _⟩
    · rintro ⟨b, -⟩
      exact ⟨fun t ↦ (IsEmpty.false (b.base t)).elim⟩

/-- The morphism from the empty scheme is quasi-compact over every open. -/
theorem qcOn_empty {S : Scheme.{u}} (V : S.Opens) : QCOn V (Scheme.emptyTo S) := by
  intro U _ _
  rw [Set.eq_empty_of_isEmpty ((Scheme.emptyTo S).base ⁻¹' (U : Set S))]
  exact isCompact_empty

variable (D)

/-- **The step of the induction on the maximal rank.** On a chart whose number of generators is
at most `n`, every generic-rank functor is represented over the chart's base by an immersion,
granted the statement for all bounds below `n` over all opens. -/
theorem exists_representsOn_chart (n : ℕ)
    (IH : ∀ m < n, ∀ W : D.S.Opens, D.RankBound W m → ∀ p : ℕ,
      ∃ (Z : Scheme.{u}) (i : Z ⟶ D.S), RepresentsOn (D.condProp p) W i ∧
        (D.F.IsFinitePresentation → QCOn W i))
    (c : D.Chart) (hn : c.n ≤ n) (p : ℕ) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ D.S), RepresentsOn (D.condProp p) c.V i ∧
      (D.F.IsFinitePresentation → QCOn c.V i) := by
  obtain ⟨Zc, ic, hic, hfp, hrep⟩ := c.exists_closedImmersion
  rcases lt_trichotomy p c.n with hlt | heq | hgt
  · -- below the chart's rank: recurse on the complement of the closed stratum
    let O : c.V.toScheme.Opens :=
      ⟨(Set.range ic.base)ᶜ, ic.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    let W' : D.S.Opens := c.V.ι ''ᵁ O
    have hW'V : W' ≤ c.V := by
      rintro _ ⟨v, -, rfl⟩
      exact v.2
    have hmemW' : ∀ v : c.V.toScheme, c.V.ι v ∈ W' ↔ v ∉ Set.range ic.base := by
      intro v
      constructor
      · rintro ⟨w, hw, hwv⟩
        rwa [c.V.ι.isOpenEmbedding.injective hwv] at hw
      · intro hv
        exact ⟨v, hv, rfl⟩
    have hbound : D.RankBound W' (c.n - 1) := by
      intro s hs q hq
      have hsV := hW'V hs
      have hle := c.rankBound s hsV q hq
      have hne : q ≠ c.n := by
        rintro rfl
        obtain ⟨a', ha', h⟩ := c.exists_lift_residueField hsV hq
        obtain ⟨b, hb⟩ := (hrep _ a').mp h
        let pt := IsLocalRing.closedPoint (D.S.residueField s)
        have hpt : c.V.ι (a' pt) = s := by
          show (a' ≫ c.V.ι).base pt = s
          rw [ha']; exact Scheme.fromSpecResidueField_apply _ _
        obtain ⟨v, hv, hvs⟩ := hs
        have : v = a' pt := c.V.ι.isOpenEmbedding.injective (hvs.trans hpt.symm)
        apply hv
        rw [this, ← hb]
        exact ⟨b pt, rfl⟩
      omega
    obtain ⟨Z', i', hrep', hqc'⟩ := IH (c.n - 1) (by omega) W' hbound p
    refine ⟨Z', i', hrep'.of_le hW'V fun T a ha hP ↦ ?_, fun hF ↦ ?_⟩
    · rintro _ ⟨t, rfl⟩
      obtain ⟨a', rfl⟩ := c.exists_lift a ha
      show c.V.ι (a' t) ∈ W'
      rw [hmemW']
      rintro ⟨w, hw⟩
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := a') (g := ic) t w hw.symm
      have h1 : D.Condition p (Over.mk (pullback.fst a' ic ≫ a' ≫ c.V.ι)) :=
        D.condProp_comp p (pullback.fst a' ic) _ hP
      have h2 : D.Condition c.n (Over.mk (pullback.fst a' ic ≫ a' ≫ c.V.ι)) := by
        rw [← Category.assoc]
        exact (hrep _ _).mpr ⟨pullback.snd a' ic, pullback.condition.symm⟩
      exact absurd (D.eq_of_condition_of_condition h1 h2 z) hlt.ne
    · have hlfp : LocallyOfFinitePresentation ic := hfp hF
      have hO : IsCompact (O : Set c.V.toScheme) := isCompact_compl_range_of_isClosedImmersion ic
      intro U hU hUaff
      have hUW' : IsCompact ((U ⊓ W' : D.S.Opens) : Set D.S) := by
        have hint := QuasiSeparatedSpace.inter_isCompact _ _ (c.V.ι ⁻¹ᵁ U).isOpen
          (c.isCompact_preimage_ι hU hUaff) O.isOpen hO
        have himg := hint.image c.V.ι.base.hom.continuous
        have heq : ((U ⊓ W' : D.S.Opens) : Set D.S) =
            c.V.ι.base '' (((c.V.ι ⁻¹ᵁ U : c.V.toScheme.Opens) : Set c.V.toScheme) ∩ O) := by
          apply Set.Subset.antisymm
          · rintro s ⟨hsU, hsW⟩
            obtain ⟨v, hv, rfl⟩ := hsW
            exact ⟨v, ⟨hsU, hv⟩, rfl⟩
          · rintro _ ⟨v, ⟨hvU, hv⟩, rfl⟩
            exact ⟨hvU, v, hv, rfl⟩
        rw [heq]; exact himg
      obtain ⟨t, ht, htU⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
        ⟨hUW', (U ⊓ W').isOpen⟩
      have hpre : i'.base ⁻¹' (U : Set D.S) = i'.base ⁻¹' ((U ⊓ W' : D.S.Opens) : Set D.S) := by
        ext z
        simp only [Set.mem_preimage, TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff,
          SetLike.mem_coe, iff_self_and]
        exact fun _ ↦ hrep'.2.1 ⟨z, rfl⟩
      rw [hpre, htU, Set.preimage_iUnion₂]
      refine ht.isCompact_biUnion fun A hA ↦ ?_
      have hAle : (A : D.S.Opens) ≤ U ⊓ W' := by
        intro x hx
        have : x ∈ ((U ⊓ W' : D.S.Opens) : Set D.S) := by
          rw [htU]; exact Set.mem_biUnion hA hx
        exact this
      exact hqc' hF A (hAle.trans inf_le_right) A.2
  · -- at the chart's rank: the closed stratum of Theorem 05PF
    subst heq
    refine ⟨Zc, ic ≫ c.V.ι, ⟨inferInstance, ?_, fun T a ha ↦ ?_⟩, fun _ ↦ ?_⟩
    · rintro _ ⟨z, rfl⟩
      exact (ic z).2
    · obtain ⟨a', rfl⟩ := c.exists_lift a ha
      show D.Condition c.n (Over.mk (a' ≫ c.V.ι)) ↔ _
      rw [hrep]
      constructor
      · rintro ⟨b, hb⟩; exact ⟨b, by rw [← hb, Category.assoc]⟩
      · rintro ⟨b, hb⟩
        exact ⟨b, (cancel_mono c.V.ι).mp (by rw [Category.assoc, hb])⟩
    · intro U hU hUaff
      exact QuasiCompact.isCompact_preimage (f := ic) _ (c.V.ι ⁻¹ᵁ U).isOpen
        (c.isCompact_preimage_ι hU hUaff)
  · -- above the chart's rank: empty
    refine ⟨∅, Scheme.emptyTo D.S, representsOn_empty _ _ fun T a ha ↦ ?_, fun _ ↦ qcOn_empty _⟩
    constructor
    · intro h
      obtain ⟨a', rfl⟩ := c.exists_lift a ha
      exact c.isEmpty_of_condition a' hgt h
    · intro hT t
      exact (hT.false t).elim

/-- Local representatives of a generic-rank functor over an open cover glue, together with
quasi-compactness. -/
private theorem exists_representsOn_of_cover_qc (p : ℕ) (W : D.S.Opens) {J : Type u}
    (V : J → D.S.Opens) (hV : ∀ j, V j ≤ W) (hcov : ∀ s ∈ W, ∃ j, s ∈ V j) (Z : J → Scheme.{u})
    (i : ∀ j, Z j ⟶ D.S) (hrep : ∀ j, RepresentsOn (D.condProp p) (V j) (i j))
    (hqc : ∀ j, D.F.IsFinitePresentation → QCOn (V j) (i j)) :
    ∃ (Z₀ : Scheme.{u}) (i₀ : Z₀ ⟶ D.S), RepresentsOn (D.condProp p) W i₀ ∧
      (D.F.IsFinitePresentation → QCOn W i₀) := by
  obtain ⟨Z₀, i₀, h₀⟩ := exists_representsOn_of_cover (D.condProp p) (D.condProp_comp p)
    (D.condProp_sheaf p) W V hV hcov Z i hrep
  exact ⟨Z₀, i₀, h₀, fun hF ↦ qcOn_of_cover (D.condProp_comp p) W h₀ V hV hcov Z i hrep
    fun j ↦ hqc j hF⟩

/-- **The induction on the maximal rank.** Over an open where the ranks are bounded by `n`, every
generic-rank functor is represented by an immersion, quasi-compact over that open when the
module is of finite presentation. The two inputs are the existence of a rank at every point and
the existence of charts. -/
theorem exists_representsOn_of_rankBound
    (hexists : ∀ s : D.S, ∃ q, D.RankAt q s)
    (hchart : ∀ (s : D.S) (W : D.S.Opens), s ∈ W → ∀ q, D.RankAt q s →
      ∃ c : D.Chart, s ∈ c.V ∧ c.V ≤ W ∧ c.n = q) :
    ∀ n : ℕ, ∀ W : D.S.Opens, D.RankBound W n → ∀ p : ℕ,
      ∃ (Z : Scheme.{u}) (i : Z ⟶ D.S), RepresentsOn (D.condProp p) W i ∧
        (D.F.IsFinitePresentation → QCOn W i) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro W hW p
  have hc : ∀ s : W, ∃ c : D.Chart, s.1 ∈ c.V ∧ c.V ≤ W ∧ c.n ≤ n := by
    intro s
    obtain ⟨q, hq⟩ := hexists s.1
    obtain ⟨c, hsc, hcW, hcq⟩ := hchart s.1 W s.2 q hq
    exact ⟨c, hsc, hcW, hcq ▸ hW s.1 s.2 q hq⟩
  choose c hsc hcW hcn using hc
  have hloc := fun s ↦ D.exists_representsOn_chart n IH (c s) (hcn s) p
  choose Z i hrep hqc using hloc
  exact D.exists_representsOn_of_cover_qc p W (fun s ↦ (c s).V) hcW
    (fun s hs ↦ ⟨⟨s, hs⟩, hsc ⟨s, hs⟩⟩) Z i hrep hqc

/-- **Every generic-rank functor is represented by an immersion into the base**, quasi-compact
when the module is of finite presentation. -/
theorem exists_representsOn_top
    (hexists : ∀ s : D.S, ∃ q, D.RankAt q s)
    (hchart : ∀ (s : D.S) (W : D.S.Opens), s ∈ W → ∀ q, D.RankAt q s →
      ∃ c : D.Chart, s ∈ c.V ∧ c.V ≤ W ∧ c.n = q) (p : ℕ) :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ D.S), RepresentsOn (D.condProp p) ⊤ i ∧
      (D.F.IsFinitePresentation → QCOn ⊤ i) := by
  have hc : ∀ s : D.S, ∃ c : D.Chart, s ∈ c.V := by
    intro s
    obtain ⟨q, hq⟩ := hexists s
    obtain ⟨c, hsc, -, -⟩ := hchart s ⊤ trivial q hq
    exact ⟨c, hsc⟩
  choose c hsc using hc
  have hloc := fun s ↦ D.exists_representsOn_of_rankBound hexists hchart (c s).n (c s).V
    (c s).rankBound p
  choose Z i hrep hqc using hloc
  exact D.exists_representsOn_of_cover_qc p ⊤ (fun s ↦ (c s).V) (fun _ ↦ le_top)
    (fun s _ ↦ ⟨s, hsc s⟩) Z i hrep hqc

end FreeAtGenericPointsSituation

end AlgebraicGeometry

end
