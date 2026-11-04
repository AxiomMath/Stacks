module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NumericalType.TopologicalGenus
public import Mathlib.Tactic.Linarith
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ModelNumericalType
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormulaModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreFiltration
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ComponentStepEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.RationalPointSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberGeometricallyConnected
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFibreRadicalComponents
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricComponents
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibreSum
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GeometricGenusReduction
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Intersection
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierPullbackCorollaries
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.Immersions
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic

/-!
# The genus of the reduced special fibre

In the situation of [Stacks, Tag 0C61] let `X` be a regular proper model of a smooth projective
curve over the fraction field of a discrete valuation ring with residue field `k`, and suppose the
special fibre `X_k` has a `k`-rational point which is a smooth point of `X_k ⟶ Spec(k)`.
[Stacks, Tag 0CEA] bounds the genus of the reduction of the special fibre from below:

`dim_k H¹((X_k)_red, 𝒪) ≥ g_top + g_geom(X_k/k)`,

where `g_top` is the topological genus ([Stacks, Tag 0C79]) of the numerical type associated to
`X` ([Stacks, Tag 0CA5]) and `g_geom` is the geometric genus of [Stacks, Section 0CE0].

## Main results

* `AlgebraicGeometry.NumericalType.topologicalGenus_add_sum_le` — the combinatorial core: an
  integer-valued function on sets of components with the recursion of an Euler characteristic
  bounds the topological genus.
* `Stacks.Models.RegularProperModelSituation.specialFiberDivisorEulerChar_indicator_insert` —
  adding a component `C_W` to a sum `D` of other components changes `χ(𝒪_D)` by
  `χ(𝒪_{C_W}) - (C_W · D)`.
* `Stacks.Models.RegularProperModelSituation.specialFiberDivisorEulerChar_one` —
  `χ((X_k)_red, 𝒪) = 1 - dim_k H¹((X_k)_red, 𝒪)` when `X_k` has a `k`-rational point.
* `RegularProperModelSituation.topologicalGenus_add_geometricGenus_le_finrank_reduction` —
  **[Stacks, Tag 0CEA]**.

## The argument

The source proves `dim_k H¹(D, 𝒪_D) ≥ g_top(D) + g_geom(D/k)` for connected reduced divisors
`D ⊆ (X_k)_red` through the rational point by induction on the number of components, removing a
component farthest from the point. Here the induction runs in the other direction and is carried
by the Euler characteristic alone. Starting from the component `C_{i₀}` through the rational point,
components meeting the current sum are added one at a time — possible by the connectedness of the
intersection graph, part (3) of [Stacks, Tag 0C66] — and the quantity
`1 - χ(𝒪_D) - g_top(D) - Σ_{Cᵢ ⊆ D} g_geom(Cᵢ/k)` never decreases:

* adding `C_W` to `D` changes `χ(𝒪_D)` by `χ(𝒪_{C_W}) - Σ_{Cⱼ ⊆ D} aⱼ` with `aⱼ = (C_W · Cⱼ)`
  ([Stacks, Tag 0CA2]), and `g_top` by `t - 1`, where `t ≥ 1` is the number of `Cⱼ ⊆ D` meeting
  `C_W`;
* `[κ_W : k]` divides each `aⱼ` ([Stacks, Tag 0C6P]), so `Σ aⱼ ≥ [κ_W : k] + t - 1`;
* `χ(𝒪_{C_W}) = [κ_W : k](1 - g_W)` and `g_geom(C_W/k) ≤ [κ_W : k]_s g_W ≤ [κ_W : k] g_W`
  ([Stacks, Tag 0CE5]).

At the start `[κ_{i₀} : k] = 1` because `C_{i₀}` has a `k`-rational point. When every component has
been added `D = Σ Cᵢ = (X_k)_red`, its cohomology vanishes above degree one, and
`H⁰((X_k)_red, 𝒪) ≠ 0`, so `1 - χ ≤ dim_k H¹`; finally `g_geom(X_k/k) = Σ g_geom(Cᵢ/k)`
([Stacks, Tag 0CE1]). In this form the source's identity `H⁰(D, 𝒪_D) = k` for every intermediate
`D` is not needed, and the smoothness of the rational point is not used: only its rationality,
through `[κ_{i₀} : k] = 1`.

## References

* [Stacks Project, Tag 0CEA](https://stacks.math.columbia.edu/tag/0CEA)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C79](https://stacks.math.columbia.edu/tag/0C79)
* [Stacks Project, Tag 0CA5](https://stacks.math.columbia.edu/tag/0CA5)
* [Stacks Project, Section 0CE0](https://stacks.math.columbia.edu/tag/0CE0)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

variable (T : NumericalType)

/-- The number of pairs `i < j` of components in `s` whose intersection number is positive. -/
def edgeCountOn (s : Finset (Fin T.componentCount)) : ℕ :=
  ((s ×ˢ s).filter fun p => p.1 < p.2 ∧ 0 < T.intersection p.1 p.2).card

/-- On all components, `edgeCountOn` is the edge count of the intersection graph. -/
theorem edgeCountOn_univ : T.edgeCountOn Finset.univ = edgeCount T := by
  rw [edgeCountOn, edgeCount, Finset.univ_product_univ]

/-- A single component spans no edge. -/
theorem edgeCountOn_singleton (i : Fin T.componentCount) : T.edgeCountOn {i} = 0 := by
  rw [edgeCountOn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  simp only [Finset.singleton_product_singleton, Finset.mem_singleton] at hp
  subst hp
  simp

/-- The edges of `insert W s` incident to `W ∉ s` correspond to the components of `s` meeting
`W`. -/
private theorem card_filter_incident_insert (s : Finset (Fin T.componentCount))
    {W : Fin T.componentCount} (hW : W ∉ s) :
    ((((insert W s) ×ˢ (insert W s)).filter fun p => p.1 < p.2 ∧ 0 < T.intersection p.1 p.2).filter
      fun p => p.1 = W ∨ p.2 = W).card = (s.filter fun j => 0 < T.intersection W j).card := by
  classical
  refine Finset.card_bij (fun p _ => if p.1 = W then p.2 else p.1) ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert] at hp
    obtain ⟨⟨⟨hi, hj⟩, hlt, hpos⟩, hW'⟩ := hp
    simp only [Finset.mem_filter]
    by_cases hiW : i = W
    · subst hiW
      simp only [ite_true]
      exact ⟨hj.resolve_left hlt.ne', hpos⟩
    · simp only [hiW, ite_false]
      obtain rfl := hW'.resolve_left hiW
      exact ⟨hi.resolve_left hiW, by rwa [T.intersection_symm]⟩
  · have hrec : ∀ p ∈ ((insert W s ×ˢ insert W s).filter
          fun p => p.1 < p.2 ∧ 0 < T.intersection p.1 p.2).filter fun p => p.1 = W ∨ p.2 = W,
        p = if W < (if p.1 = W then p.2 else p.1) then (W, if p.1 = W then p.2 else p.1)
          else ((if p.1 = W then p.2 else p.1), W) := by
      rintro ⟨i, j⟩ hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert] at hp
      obtain ⟨⟨-, hlt, -⟩, hW'⟩ := hp
      by_cases hiW : i = W
      · subst hiW
        simp [hlt]
      · obtain rfl := hW'.resolve_left hiW
        simp [hiW, not_lt.mpr hlt.le]
    intro p hp p' hp' heq
    rw [hrec p hp, hrec p' hp', heq]
  · intro j hj
    simp only [Finset.mem_filter] at hj
    rcases lt_trichotomy W j with h | h | h
    · exact ⟨(W, j), by simp [hj.1, h, hj.2], by simp⟩
    · exact absurd (h ▸ hj.1) hW
    · exact ⟨(j, W), by simp [hj.1, h, T.intersection_symm j W, hj.2], by simp [h.ne]⟩

/-- Adding a component `W` to `s` adds one edge for each component of `s` meeting `W`. -/
theorem edgeCountOn_insert (s : Finset (Fin T.componentCount)) {W : Fin T.componentCount}
    (hW : W ∉ s) :
    T.edgeCountOn (insert W s) =
      T.edgeCountOn s + (s.filter fun j => 0 < T.intersection W j).card := by
  classical
  let A := (s ×ˢ s).filter fun p => p.1 < p.2 ∧ 0 < T.intersection p.1 p.2
  let B := (((insert W s) ×ˢ (insert W s)).filter
    fun p => p.1 < p.2 ∧ 0 < T.intersection p.1 p.2).filter fun p => p.1 = W ∨ p.2 = W
  have hsplit : ((insert W s) ×ˢ (insert W s)).filter
      (fun p => p.1 < p.2 ∧ 0 < T.intersection p.1 p.2) = A ∪ B := by
    ext ⟨i, j⟩
    simp only [A, B, Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_union]
    tauto
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hA hB
    simp only [A, B, Finset.mem_filter, Finset.mem_product] at hA hB
    rcases hB.2 with h | h
    · exact hW (h ▸ hA.1.1)
    · exact hW (h ▸ hA.1.2)
  rw [edgeCountOn, hsplit, Finset.card_union_of_disjoint hdisj,
    T.card_filter_incident_insert s hW]
  rfl

/-- A component of the intersection graph meets some component outside every proper nonempty
set of components. -/
private theorem exists_intersection_ne_zero_of_ne_univ {s : Finset (Fin T.componentCount)}
    {j₀ : Fin T.componentCount} (hj₀ : j₀ ∈ s) (hne : s ≠ Finset.univ) :
    ∃ i ∈ s, ∃ j ∉ s, T.intersection i j ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact T.connected ⟨(s : Set (Fin T.componentCount)), ⟨j₀, hj₀⟩,
    fun h => hne (Finset.coe_eq_univ.mp h), hcon⟩

/-- For `W ∉ s`, the intersection numbers of `W` with `s` sum to at least `w_W` times the number
of components of `s` meeting `W`. -/
private theorem card_filter_mul_weight_le_sum_intersection (s : Finset (Fin T.componentCount))
    {W : Fin T.componentCount} (hW : W ∉ s) :
    ((s.filter fun j => 0 < T.intersection W j).card : ℤ) * T.weight W ≤
      ∑ j ∈ s, T.intersection W j := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not s
    (fun j => 0 < T.intersection W j) (fun j => T.intersection W j)
  have h1 : ((s.filter fun j => 0 < T.intersection W j).card : ℤ) * T.weight W ≤
      ∑ j ∈ s.filter (fun j => 0 < T.intersection W j), T.intersection W j := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun j hj => ?_
    obtain ⟨d, hd⟩ := T.weight_dvd_intersection W j
    have hpos := (Finset.mem_filter.mp hj).2
    have hw := T.weight_pos W
    rw [hd] at hpos ⊢
    have : 0 < d := pos_of_mul_pos_right hpos hw.le
    nlinarith
  have h2 : 0 ≤ ∑ j ∈ s.filter (fun j => ¬ 0 < T.intersection W j), T.intersection W j :=
    Finset.sum_nonneg fun j hj =>
      T.intersection_nonneg W j (fun h => hW (h ▸ (Finset.mem_filter.mp hj).1))
  linarith

/-- A property of finite sets that holds for `s₀`, and that every proper subset satisfying it
passes on to some one-element extension, holds for `univ`. -/
private theorem _root_.Finset.univ_of_exists_insert {α : Type*} [Fintype α] [DecidableEq α]
    {P : Finset α → Prop} {s₀ : Finset α} (h₀ : P s₀)
    (hgrow : ∀ s, P s → s ≠ Finset.univ → ∃ W ∉ s, P (insert W s)) : P Finset.univ := by
  suffices ∀ k : ℕ, ∀ s, P s → (Finset.univ \ s).card = k → P Finset.univ from this _ s₀ h₀ rfl
  intro k
  induction k with
  | zero =>
    intro s hs hk
    rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset, Finset.univ_subset_iff] at hk
    exact hk ▸ hs
  | succ k ih =>
    intro s hs hk
    have hne : s ≠ Finset.univ := by
      rintro rfl
      simp at hk
    obtain ⟨W, hW, hP⟩ := hgrow s hs hne
    refine ih _ hP ?_
    rw [Finset.sdiff_insert, Finset.card_erase_of_mem (by simp [hW]), hk]
    simp

/-- **The cycle-rank inequality behind [Stacks, Tag 0CEA].** Let `χ` assign an integer to every
set of components, satisfying the recursion `χ(s + W) = χ(s) - Σ_{j ∈ s} a_{Wj} + c_W` of an
Euler characteristic, and let `g'_i ≤ w_i - c_i`. If some component `j₀` has weight one and
`χ({j₀}) = c_{j₀}`, then `g_top + Σ g'_i ≤ 1 - χ(all components)`. -/
theorem topologicalGenus_add_sum_le (χ : Finset (Fin T.componentCount) → ℤ)
    (c gg : Fin T.componentCount → ℤ) (j₀ : Fin T.componentCount) (hw₀ : T.weight j₀ = 1)
    (hbase : χ {j₀} = c j₀)
    (hstep : ∀ s W, W ∉ s → χ (insert W s) = χ s - ∑ j ∈ s, T.intersection W j + c W)
    (hgg : ∀ i, gg i ≤ T.weight i - c i) :
    T.topologicalGenus + ∑ i, gg i ≤ 1 - χ Finset.univ := by
  classical
  let P : Finset (Fin T.componentCount) → Prop := fun s =>
    j₀ ∈ s ∧ 1 - (s.card : ℤ) + T.edgeCountOn s + ∑ i ∈ s, gg i ≤ 1 - χ s
  have hP0 : P {j₀} := by
    refine ⟨Finset.mem_singleton_self _, ?_⟩
    rw [Finset.card_singleton, edgeCountOn_singleton, Finset.sum_singleton, hbase]
    push_cast
    linarith [hgg j₀]
  have hgrow : ∀ s, P s → s ≠ Finset.univ → ∃ W ∉ s, P (insert W s) := by
    intro s ⟨hj₀, hs⟩ hne
    obtain ⟨i, hi, W, hW, hiW⟩ := T.exists_intersection_ne_zero_of_ne_univ hj₀ hne
    refine ⟨W, hW, Finset.mem_insert_of_mem hj₀, ?_⟩
    let t := (s.filter fun j => 0 < T.intersection W j).card
    have ht : (1 : ℤ) ≤ t := by
      norm_cast
      refine Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
      rw [T.intersection_symm]
      exact (T.intersection_nonneg i W fun h => hW (h ▸ hi)).lt_of_ne' hiW
    have hsum := T.card_filter_mul_weight_le_sum_intersection s hW
    rw [Finset.card_insert_of_notMem hW, edgeCountOn_insert T s hW,
      Finset.sum_insert hW, hstep s W hW]
    have hw := T.weight_pos W
    have hg := hgg W
    have hmul : 0 ≤ ((t : ℤ) - 1) * (T.weight W - 1) :=
      mul_nonneg (by linarith) (by linarith)
    push_cast
    nlinarith
  obtain ⟨-, h⟩ := Finset.univ_of_exists_insert (P := P) hP0 hgrow
  rwa [Finset.card_univ, Fintype.card_fin, edgeCountOn_univ] at h

end AlgebraicGeometry.NumericalType

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.isIso_residueFieldMap_of_isClosedImmersion
  Stacks.Models.RegularProperModelSituation.connectedSpace_specialFiber

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- A closed immersion whose kernel is `I` factors through `I.subschemeι` by an isomorphism. -/
private theorem exists_isIso_comp_subschemeι_eq {X Y : Scheme.{u}} (j : Y ⟶ X)
    [IsClosedImmersion j] (I : X.IdealSheafData) (h : j.ker = I) :
    ∃ φ : Y ⟶ I.subscheme, IsIso φ ∧ φ ≫ I.subschemeι = j := by
  have hker : I.subschemeι.ker = j.ker := by rw [Scheme.IdealSheafData.ker_subschemeι, h]
  exact ⟨_, IsClosedImmersion.isIso_lift _ _ hker, IsClosedImmersion.lift_fac _ _ hker.le⟩

/-- The kernel of the closed immersion `(X_k)_red ⟶ X` is the sum of the components. -/
theorem ker_reductionι_specialFiberι :
    (S.specialFiber.reductionι ≫ S.specialFiberι).ker = ∏ Z, S.specialFiberComponentIdeal Z := by
  rw [← S.radical_specialFiberIdeal_eq_prod, ker_eq_vanishingIdeal_of_reduced_closed_immersion,
    ← Scheme.IdealSheafData.vanishingIdeal_support]
  congr 1
  refine SetLike.coe_injective ?_
  rw [Scheme.Hom.support_ker, S.coe_support_specialFiberIdeal, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, S.specialFiber.range_reductionι, Set.image_univ]
  exact S.specialFiberι.isClosedEmbedding.isClosed_range.closure_eq

/-- The sum of the components of the special fibre is a reduced subscheme. -/
private theorem isReduced_prod_specialFiberComponentIdeal :
    IsReduced (∏ Z, S.specialFiberComponentIdeal Z).subscheme := by
  have hrad : IsReduced S.specialFiberIdeal.radical.subscheme :=
    Scheme.IdealSheafData.vanishingIdeal_support (I := S.specialFiberIdeal) ▸
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal S.specialFiberIdeal.support
  rwa [S.radical_specialFiberIdeal_eq_prod] at hrad

/-- **`H^n((X_k)_red, 𝒪)` is the cohomology of the sum of the components.** -/
theorem finrank_cohomologyOverField_reduction_specialFiber
    (h : S.specialFiberIdeal ≤ ∏ Z, S.specialFiberComponentIdeal Z) (n : ℕ) :
    Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) n) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.fibreSubschemeι _ h ≫ S.specialFiberToSpec)
        (SheafOfModules.unit
          (∏ Z, S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf) n) := by
  set D := ∏ Z, S.specialFiberComponentIdeal Z
  set j := S.specialFiber.reductionι ≫ S.specialFiberι
  obtain ⟨φ, _, hφ⟩ := exists_isIso_comp_subschemeι_eq j D S.ker_reductionι_specialFiberι
  have hcomp : φ ≫ S.fibreSubschemeι _ h = S.specialFiber.reductionι := by
    rw [← cancel_mono S.specialFiberι, Category.assoc,
      fibreSubschemeι_comp, hφ]
  rw [← hcomp, Category.assoc, finrank_cohomologyOverField_unit_pushforward]

/-- The indicator `c_t` of a set `t` of components, so that `Σ_Z (c_t)_Z C_Z = Σ_{Z ∈ t} C_Z`. -/
theorem indicator_le_specialFiberMultiplicity [DecidableEq (irreducibleComponents S.specialFiber)]
    (t : Finset (irreducibleComponents S.specialFiber)) :
    (fun Z => if Z ∈ t then 1 else 0) ≤ S.specialFiberMultiplicity := fun Z => by
  dsimp only
  split_ifs
  · exact S.specialFiberMultiplicity_pos Z
  · exact Nat.zero_le _

/-- **Adding a component to a reduced sum of components** (Tag 0CA2): for `W ∉ t`,
`χ(𝒪_{D + C_W}) = χ(𝒪_D) - Σ_{Z ∈ t} (C_W · C_Z) + χ(𝒪_{C_W})` with `D = Σ_{Z ∈ t} C_Z`. -/
theorem specialFiberDivisorEulerChar_indicator_insert
    [DecidableEq (irreducibleComponents S.specialFiber)]
    (t : Finset (irreducibleComponents S.specialFiber)) {W : irreducibleComponents S.specialFiber}
    (hW : W ∉ t) :
    S.specialFiberDivisorEulerChar (fun Z => if Z ∈ insert W t then 1 else 0) =
      S.specialFiberDivisorEulerChar (fun Z => if Z ∈ t then 1 else 0) -
        ∑ Z ∈ t, S.specialFiberIntersectionMatrix W Z +
        eulerCharacteristic S.k (S.specialFiberComponentToSpec W)
          (SheafOfModules.unit (S.specialFiberComponentIdeal W).subscheme.ringCatSheaf) := by
  have hc : (fun Z => if Z ∈ insert W t then 1 else 0) =
      (fun Z => if Z ∈ t then 1 else 0) + Pi.single W 1 := by
    funext Z
    by_cases hZ : Z = W <;> simp [hZ, hW]
  rw [hc, S.specialFiberDivisorEulerChar_add_single _ W
    (hc ▸ S.indicator_le_specialFiberMultiplicity _)]
  congr 2
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ t)]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.sum_eq_zero (s := Finset.univ.filter (· ∉ t)) (fun Y hY => by
    simp [(Finset.mem_filter.mp hY).2]), add_zero]
  exact Finset.sum_congr rfl fun Y hY => by simp [hY]

/-- `χ(𝒪_{C_W})` is the Euler characteristic of the one-component sum `C_W`. -/
theorem specialFiberDivisorEulerChar_indicator_singleton
    [DecidableEq (irreducibleComponents S.specialFiber)]
    (W : irreducibleComponents S.specialFiber) :
    S.specialFiberDivisorEulerChar (fun Z => if Z ∈ ({W} : Finset _) then 1 else 0) =
      eulerCharacteristic S.k (S.specialFiberComponentToSpec W)
        (SheafOfModules.unit (S.specialFiberComponentIdeal W).subscheme.ringCatSheaf) := by
  have h := S.specialFiberDivisorEulerChar_indicator_insert ∅ (Finset.notMem_empty W)
  simp only [Finset.sum_empty, sub_zero, Finset.notMem_empty, ite_false] at h
  rw [show (fun _ : irreducibleComponents S.specialFiber => (0 : ℕ)) = 0 from rfl,
    S.specialFiberDivisorEulerChar_zero, zero_add] at h
  simpa using h

/-- The component `C_Z ⊆ X` and the reduced closed subscheme of `X_k` supported on `Z` have the
same geometric genus over `k`: they are isomorphic over `X_k`. -/
theorem geometricGenus_specialFiberComponentToSpec (Z : irreducibleComponents S.specialFiber) :
    geometricGenus S.k (S.specialFiberComponentToSpec Z) =
      geometricGenus S.k ((irreducibleComponentIdeal Z).subschemeι ≫ S.specialFiberToSpec) := by
  have hker : (S.specialFiberComponentι Z).ker = irreducibleComponentIdeal Z := by
    rw [ker_eq_vanishingIdeal_of_reduced_closed_immersion]
    congr 1
    refine SetLike.coe_injective ?_
    rw [Scheme.Hom.support_ker, range_specialFiberComponentι]
    exact (isClosed_of_mem_irreducibleComponents _ Z.2).closure_eq
  obtain ⟨ψ, _, hψ⟩ := exists_isIso_comp_subschemeι_eq (S.specialFiberComponentι Z)
    (irreducibleComponentIdeal Z) hker
  have h : S.specialFiberComponentToSpec Z =
      ψ ≫ (irreducibleComponentIdeal Z).subschemeι ≫ S.specialFiberToSpec := by
    rw [← Category.assoc, hψ]
    rfl
  simp only [h]
  exact geometricGenus_eq_of_surjective_isClosedImmersion _ ψ

/-- **`g_geom(X_k/k) = Σ_Z g_geom(C_Z/k)`**, the sum over the irreducible components of the
special fibre (Tag 0CE1). -/
theorem geometricGenus_specialFiberToSpec_eq_sum :
    geometricGenus S.k S.specialFiberToSpec =
      ∑ Z, geometricGenus S.k (S.specialFiberComponentToSpec Z) := by
  rw [geometricGenus_eq_sum_all_components]
  exact Finset.sum_congr rfl fun Z _ => (S.geometricGenus_specialFiberComponentToSpec Z).symm

/-- **A component through a `k`-rational point has weight one**: its field of global functions is
`k` (Tag 0CE8 (2)). -/
theorem specialFiberComponentWeight_eq_one_of_isRationalPoint
    (Z : irreducibleComponents S.specialFiber) (x : S.specialFiber)
    (hx : IsRationalPoint S.specialFiberToSpec x) (hxZ : x ∈ Z.1) :
    S.specialFiberComponentWeight Z = 1 := by
  have hiso := S.isIso_globalSections_specialFiberComponent_of_isRationalPoint Z x hx hxZ
  let : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  have hbij : Function.Bijective
      (algebraMap S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)) :=
    ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop)
  rw [specialFiberComponentWeight,
    ← (AlgEquiv.ofBijective (Algebra.ofId _ _) hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-- **`χ((X_k)_red, 𝒪) = 1 - dim_k H¹((X_k)_red, 𝒪)`** when `X_k` has a `k`-rational point, for
the reduced special fibre `(X_k)_red = Σ Cᵢ` seen in `X_k`: its cohomology vanishes above degree
one, and `H⁰((X_k)_red, 𝒪) = k`, the reduced special fibre being connected and having a
`k`-rational point. -/
theorem eulerCharacteristic_pushforward_prod_specialFiberComponentIdeal (x : S.specialFiber)
    (hx : IsRationalPoint S.specialFiberToSpec x) (E : S.X.IdealSheafData)
    (h : S.specialFiberIdeal ≤ E) (hE : E = ∏ Z, S.specialFiberComponentIdeal Z) :
    eulerCharacteristic S.k S.specialFiberToSpec
        ((Scheme.Modules.pushforward (S.fibreSubschemeι _ h)).obj
          (SheafOfModules.unit E.subscheme.ringCatSheaf)) =
      1 - (Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) : ℤ) := by
  subst hE
  set ι := S.fibreSubschemeι _ h
  have hcoh :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k (ι ≫ S.specialFiberToSpec)
  rw [eulerCharacteristic_pushforward_of_isClosedImmersion S.k ι S.specialFiberToSpec _ hcoh
    inferInstance, S.finrank_cohomologyOverField_reduction_specialFiber h 1,
    ← (structureSheafCohomologyIsoCohomologyOverField S.k _ 1).toLinearEquiv.finrank_eq,
    ← genus_eq_finrank_structureSheafCohomology]
  have hdim : topologicalKrullDim (∏ Z, S.specialFiberComponentIdeal Z).subscheme ≤ 1 := by
    have h' := ι.isClosedEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    rwa [S.topologicalKrullDim_specialFiber ⟨x⟩] at h'
  have hsurj : Function.Surjective ι := by
    intro w
    have hmem : S.specialFiberι w ∈
        Set.range (∏ Z, S.specialFiberComponentIdeal Z).subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι, ← S.radical_specialFiberIdeal_eq_prod,
        Scheme.IdealSheafData.support_radical, S.coe_support_specialFiberIdeal]
      exact ⟨w, rfl⟩
    obtain ⟨y, hy⟩ := hmem
    refine ⟨y, S.specialFiberι.isClosedEmbedding.injective ?_⟩
    rw [← hy, ← Scheme.Hom.comp_apply, fibreSubschemeι_comp]
  have := S.isReduced_prod_specialFiberComponentIdeal
  have : ConnectedSpace (∏ Z, S.specialFiberComponentIdeal Z).subscheme :=
    (ι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective hsurj).symm.surjective.connectedSpace
      (ι.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective hsurj).symm.continuous
  obtain ⟨y, rfl⟩ := hsurj x
  have : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (ι ≫ S.specialFiberToSpec).appTop) :=
    isIso_globalSections_of_isField_of_isRationalPoint _
      (isField_globalSections_of_connectedSpace S.k (ι ≫ S.specialFiberToSpec)) y
      (isRationalPoint_comp ι S.specialFiberToSpec y hx)
  exact (one_sub_genus_eq_eulerCharacteristic_unit S.k _ hdim
    (finrank_globalSections_eq_one_of_isIso S.k _)).symm

/-- **`χ((X_k)_red, 𝒪) = 1 - dim_k H¹((X_k)_red, 𝒪)`** for the divisor `Σ_Z C_Z` of all the
components, when `X_k` has a `k`-rational point. -/
theorem specialFiberDivisorEulerChar_one (x : S.specialFiber)
    (hx : IsRationalPoint S.specialFiberToSpec x) :
    S.specialFiberDivisorEulerChar (fun _ => 1) =
      1 - (Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) : ℤ) := by
  have h1 : (fun _ => 1) ≤ S.specialFiberMultiplicity := fun Z => S.specialFiberMultiplicity_pos Z
  rw [specialFiberDivisorEulerChar, dite_eq_left (S.specialFiberIdeal_le_prod_of_le _ h1)]
  exact S.eulerCharacteristic_pushforward_prod_specialFiberComponentIdeal x hx _ _
    (Finset.prod_congr rfl fun Z _ => pow_one _)

/-- **`g_geom(C_Z/k) ≤ [κ_Z : k]_s · g_Z`** for a component `C_Z` of the special fibre, with
`κ_Z = Γ(C_Z, 𝒪)` and `g_Z` the genus of `C_Z` over `κ_Z` (Tag 0CE5; a component of dimension zero
has geometric genus zero). -/
theorem geometricGenus_specialFiberComponent_le_finSepDegree_mul_genus
    (Z : irreducibleComponents S.specialFiber) :
    letI : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
      (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
    letI : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
    geometricGenus S.k (S.specialFiberComponentToSpec Z) ≤
      Field.finSepDegree S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) *
        S.specialFiberComponentGenus Z := by
  rcases (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z).lt_or_eq
    with hlt | heq
  · rw [geometricGenus_eq_zero_of_dim_lt_one _ hlt]
    exact Nat.zero_le _
  have : IsCurve S.k (S.specialFiberComponentToSpec Z) :=
    { toIsVariety := { }
      topologicalKrullDim_eq_one := heq }
  exact geometricGenus_le_finSepDegree_mul_genus_toSpecΓ_of_isCurve S.k
    (S.specialFiberComponentToSpec Z)

/-- **`g_geom(C_Z/k) ≤ [κ_Z : k] · g_Z`**, inequality (0CEC) of the source, for a component `C_Z`
of the special fibre. -/
theorem geometricGenus_specialFiberComponent_le_weight_mul_genus
    (Z : irreducibleComponents S.specialFiber) :
    geometricGenus S.k (S.specialFiberComponentToSpec Z) ≤
      S.specialFiberComponentWeight Z * S.specialFiberComponentGenus Z := by
  let : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
  let : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  have : FiniteDimensional S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    (S.isField_and_finite_globalSections_specialFiberComponent Z).2
  exact (S.geometricGenus_specialFiberComponent_le_finSepDegree_mul_genus Z).trans
    (Nat.mul_le_mul_right _ (Field.finSepDegree_le_finrank _ _))

/-- **`g_geom(C_Z/k) ≤ [κ_Z : k] - χ(C_Z, 𝒪)`** for a component `C_Z` of the special fibre: this
is (0CEC), since `χ(C_Z, 𝒪) = [κ_Z : k](1 - g_Z)`. -/
theorem geometricGenus_specialFiberComponent_le (Z : irreducibleComponents S.specialFiber) :
    (geometricGenus S.k (S.specialFiberComponentToSpec Z) : ℤ) ≤
      S.specialFiberComponentWeight Z - eulerCharacteristic S.k (S.specialFiberComponentToSpec Z)
        (SheafOfModules.unit (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf) := by
  rw [S.eulerCharacteristic_specialFiberComponent_eq Z]
  have h : (geometricGenus S.k (S.specialFiberComponentToSpec Z) : ℤ) ≤
      (S.specialFiberComponentWeight Z : ℤ) * S.specialFiberComponentGenus Z :=
    mod_cast S.geometricGenus_specialFiberComponent_le_weight_mul_genus Z
  linarith

/-- **Stacks Project, Tag 0CEA.** In the situation of [Stacks, Tag 0C61] suppose the special
fibre `X_k` has a `k`-rational point `x` which is a smooth point of `X_k ⟶ Spec(k)`. Then

`dim_k H¹((X_k)_red, 𝒪_{(X_k)_red}) ≥ g_top + g_geom(X_k/k)`,

where `g_top` is the topological genus ([Stacks, Tag 0C79]) of the numerical type associated to
`X` ([Stacks, Tag 0CA5]), for any enumeration `e` of the irreducible components of `X_k`, and
`g_geom(X_k/k)` is the geometric genus of [Stacks, Section 0CE0]. The cohomology of the reduction
`(X_k)_red` is taken over `k` through `(X_k)_red ⟶ X_k ⟶ Spec(k)`.

Only the rationality of `x` is used; see the module documentation. -/
@[stacks 0CEA "dim_k H^1((X_k)_red, O) >= g_top + g_geom(X_k/k) when X_k has a k-rational smooth \
point, g_top the topological genus of the numerical type associated to X"]
theorem topologicalGenus_add_geometricGenus_le_finrank_reduction
    (x : S.specialFiber) (hx : IsRationalPoint S.specialFiberToSpec x)
    (_hsm : InfinitesimalLifting.SmoothAt S.specialFiberToSpec x)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber) :
    (S.associatedNumericalType n e).topologicalGenus +
        (geometricGenus S.k S.specialFiberToSpec : ℤ) ≤
      Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1) := by
  classical
  obtain ⟨Z₀, hZ₀⟩ := S.exists_mem_specialFiberComponent x
  let T := S.associatedNumericalType n e
  let e' : Fin T.componentCount ≃ irreducibleComponents S.specialFiber := e
  have hw : ∀ i, T.weight i = (S.specialFiberComponentWeight (e' i) : ℤ) := fun _ => rfl
  have hint : ∀ i j, T.intersection i j = S.specialFiberIntersectionMatrix (e' i) (e' j) :=
    S.associatedNumericalType_intersection n e
  have hcomb := T.topologicalGenus_add_sum_le
    (fun s => S.specialFiberDivisorEulerChar fun Z => if Z ∈ s.map e'.toEmbedding then 1 else 0)
    (fun i => eulerCharacteristic S.k (S.specialFiberComponentToSpec (e' i))
      (SheafOfModules.unit (S.specialFiberComponentIdeal (e' i)).subscheme.ringCatSheaf))
    (fun i => (geometricGenus S.k (S.specialFiberComponentToSpec (e' i)) : ℤ))
    (e'.symm Z₀)
    (by
      rw [hw, Equiv.apply_symm_apply,
        S.specialFiberComponentWeight_eq_one_of_isRationalPoint Z₀ x hx hZ₀, Nat.cast_one])
    (by
      simp only [Finset.map_singleton, Equiv.coe_toEmbedding]
      exact S.specialFiberDivisorEulerChar_indicator_singleton _)
    (by
      intro s W hW
      simp only [Finset.map_insert, Equiv.coe_toEmbedding]
      rw [S.specialFiberDivisorEulerChar_indicator_insert _ (by simpa using hW), Finset.sum_map]
      simp only [hint, Equiv.coe_toEmbedding])
    (fun i => S.geometricGenus_specialFiberComponent_le (e' i))
  have huniv : (fun Z => if Z ∈ (Finset.univ : Finset (Fin T.componentCount)).map e'.toEmbedding
      then 1 else 0) = fun _ => 1 := by
    funext Z
    simp
  have hsum : ∑ i : Fin T.componentCount,
      (geometricGenus S.k (S.specialFiberComponentToSpec (e' i)) : ℤ) =
      (geometricGenus S.k S.specialFiberToSpec : ℤ) := by
    rw [S.geometricGenus_specialFiberToSpec_eq_sum, Nat.cast_sum]
    exact Fintype.sum_equiv e' _ _ fun _ => rfl
  simpa only [huniv, hsum, S.specialFiberDivisorEulerChar_one x hx, sub_sub_cancel] using hcomb

end Stacks.Models.RegularProperModelSituation
