module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreGenusBound
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ComponentRationalIntersectionPoint
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SmoothOfGenusEquality
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.FlatAtDivisor
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The equality case of the genus bound for the reduced special fibre

In the situation of [Stacks, Tag 0C61] let `x` be a `k`-rational point of the special fibre `X_k`
at which `X_k ⟶ Spec(k)` is smooth. [Stacks, Tag 0CEA] gives
`dim_k H¹((X_k)_red, 𝒪) ≥ g_top + g_geom(X_k/k)`, and [Stacks, Tag 0CEE] describes the components
of `X_k` when equality holds: the component through `x` is a smooth projective geometrically
irreducible curve over `k`, and every other component `C` is smooth over `κ = H⁰(C, 𝒪_C)`, finite
over `k`, with a `κ`-rational point.

The source also asserts that every such `κ` is separable over `k`. That is false in general, and
`RegularProperModelSituation.smooth_of_topologicalGenus_add_geometricGenus_eq_finrank_reduction`
proves the tag with separability required only of components of positive genus, where the
source's argument proves it; its docstring describes a model with an exceptional curve `ℙ¹_κ`,
`κ/k` purely inseparable, for which equality holds. That model is built in
`StacksFrontier/AlgebraicGeometry/Curves/Models/InseparableModel/`, and
`Stacks.Models.RegularProperModelSituation.smooth_and_not_forall_isSeparable_of_genus_equality`
pairs the corrected statement with the refutation of the separability clause.

## Main results

* `AlgebraicGeometry.NumericalType.le_genusDefect_univ` — the combinatorial core: in the
  induction of [Stacks, Tag 0CEA] the total defect bounds the defect of each component and the
  slack of a step adding any component other than the starting one.
* `AlgebraicGeometry.NumericalType.intersection_eq_weight_of_addSlack_nonpos` — a step with no
  slack adds a component `C` meeting the previous ones with `(C · C_j) = [κ_C : k]`.
* `AlgebraicGeometry.eq_of_mem_irreducibleComponents_of_isDomain_stalk` — a point with a domain as
  local ring lies on a unique irreducible component.
* `Stacks.Models.RegularProperModelSituation.topologicalKrullDim_specialFiberComponent_eq_one` —
  every component of `X_k` is a curve.
* `RegularProperModelSituation.geometricGenus_eq_and_exists_componentIntersection_eq_weight`
  — equality in [Stacks, Tag 0CEA] forces equality at every step.
* `RegularProperModelSituation.smooth_of_topologicalGenus_add_geometricGenus_eq_finrank_reduction`
  — **[Stacks, Tag 0CEE]**, in corrected form: the separability clause
  of part (2) is asserted for the components of positive genus.

## References

* [Stacks Project, Tag 0CEE](https://stacks.math.columbia.edu/tag/0CEE)
* [Stacks Project, Tag 0CEA](https://stacks.math.columbia.edu/tag/0CEA)
* [Stacks Project, Tag 0CE4](https://stacks.math.columbia.edu/tag/0CE4)
* [Stacks Project, Tag 0CDW](https://stacks.math.columbia.edu/tag/0CDW)
-/

@[expose] public section

namespace AlgebraicGeometry.NumericalType

variable (T : NumericalType)

/-- The slack of adding the component `W` to the set `s` in the induction of [Stacks, Tag 0CEA]:
`Σ_{j ∈ s} a_{Wj} - t - (w_W - 1)`, with `t` the number of `j ∈ s` meeting `W`. -/
def addSlack (W : Fin T.componentCount) (s : Finset (Fin T.componentCount)) : ℤ :=
  ∑ j ∈ s, T.intersection W j - ((s.filter fun j => 0 < T.intersection W j).card : ℤ) -
    (T.weight W - 1)

/-- Every positive intersection number `a_{Wj}` with `W ∉ s`, `j ∈ s` exceeds the slack by at
least `a_{Wj} - w_W`: the entries of the row of `W` are multiples of `w_W`. -/
theorem intersection_sub_weight_le_addSlack (s : Finset (Fin T.componentCount))
    {W : Fin T.componentCount} (hW : W ∉ s) {j : Fin T.componentCount} (hj : j ∈ s)
    (hpos : 0 < T.intersection W j) :
    T.intersection W j - T.weight W ≤ T.addSlack W s := by
  classical
  set P := s.filter fun j => 0 < T.intersection W j
  have hw := T.weight_pos W
  have hge : ∀ i ∈ P, T.weight W ≤ T.intersection W i := fun i hi =>
    Int.le_of_dvd (Finset.mem_filter.mp hi).2 (T.weight_dvd_intersection W i)
  have hjP : j ∈ P := Finset.mem_filter.mpr ⟨hj, hpos⟩
  have hP1 : 1 ≤ P.card := Finset.card_pos.mpr ⟨j, hjP⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not s
    (fun j => 0 < T.intersection W j) (fun j => T.intersection W j)
  have h2 : 0 ≤ ∑ j ∈ s.filter (fun j => ¬ 0 < T.intersection W j), T.intersection W j :=
    Finset.sum_nonneg fun i hi =>
      T.intersection_nonneg W i (fun h => hW (h ▸ (Finset.mem_filter.mp hi).1))
  have hP : ∑ i ∈ P, T.intersection W i =
      T.intersection W j + ∑ i ∈ P.erase j, T.intersection W i :=
    (Finset.add_sum_erase P _ hjP).symm
  have h3 : ((P.erase j).card : ℤ) * T.weight W ≤ ∑ i ∈ P.erase j, T.intersection W i := by
    rw [show ((P.erase j).card : ℤ) * T.weight W = ∑ i ∈ P.erase j, T.weight W by
      rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_le_sum fun i hi => hge i (Finset.mem_of_mem_erase hi)
  have hcard : ((P.erase j).card : ℤ) = (P.card : ℤ) - 1 := by
    rw [Finset.card_erase_of_mem hjP]
    omega
  have hmul : 0 ≤ ((P.card : ℤ) - 1) * (T.weight W - 1) := mul_nonneg (by omega) (by omega)
  unfold addSlack
  rw [hcard] at h3
  change T.intersection W j - T.weight W ≤
    ∑ j ∈ s, T.intersection W j - (P.card : ℤ) - (T.weight W - 1)
  nlinarith

/-- **Equality in the slack of [Stacks, Tag 0CEA].** If `W ∉ s` meets `s` and the slack of adding
`W` to `s` is not positive, then every `j ∈ s` meeting `W` has `a_{Wj} = w_W`. -/
theorem intersection_eq_weight_of_addSlack_nonpos (s : Finset (Fin T.componentCount))
    {W : Fin T.componentCount} (hW : W ∉ s) (h : T.addSlack W s ≤ 0)
    {j : Fin T.componentCount} (hj : j ∈ s) (hpos : 0 < T.intersection W j) :
    T.intersection W j = T.weight W := by
  have h1 := T.intersection_sub_weight_le_addSlack s hW hj hpos
  have h2 := Int.le_of_dvd hpos (T.weight_dvd_intersection W j)
  omega

/-- The defect `(1 - χ(s)) - g_top(s) - Σ_{i ∈ s} g'_i` of a set of components in the induction
of [Stacks, Tag 0CEA]. -/
def genusDefect (χ : Finset (Fin T.componentCount) → ℤ) (gg : Fin T.componentCount → ℤ)
    (s : Finset (Fin T.componentCount)) : ℤ :=
  (1 - χ s) - (1 - (s.card : ℤ) + T.edgeCountOn s + ∑ i ∈ s, gg i)

/-- How the defect changes when a component is added. -/
theorem genusDefect_insert (χ : Finset (Fin T.componentCount) → ℤ)
    (c gg : Fin T.componentCount → ℤ)
    (hstep : ∀ s W, W ∉ s → χ (insert W s) = χ s - ∑ j ∈ s, T.intersection W j + c W)
    (s : Finset (Fin T.componentCount)) {W : Fin T.componentCount} (hW : W ∉ s) :
    T.genusDefect χ gg (insert W s) =
      T.genusDefect χ gg s + T.addSlack W s + (T.weight W - c W - gg W) := by
  unfold genusDefect addSlack
  rw [Finset.card_insert_of_notMem hW, edgeCountOn_insert T s hW, Finset.sum_insert hW,
    hstep s W hW]
  push_cast
  ring

/-- The slack of adding a component which meets the set is nonnegative. -/
theorem addSlack_nonneg (s : Finset (Fin T.componentCount)) {W : Fin T.componentCount}
    (hW : W ∉ s) {j : Fin T.componentCount} (hj : j ∈ s) (hpos : 0 < T.intersection W j) :
    0 ≤ T.addSlack W s := by
  have h1 := T.intersection_sub_weight_le_addSlack s hW hj hpos
  have h2 := Int.le_of_dvd hpos (T.weight_dvd_intersection W j)
  omega

/-- A set of components which is neither empty nor everything meets its complement. -/
theorem exists_intersection_pos_of_ne_univ (s : Finset (Fin T.componentCount))
    {j₀ : Fin T.componentCount} (hj₀ : j₀ ∈ s) (hne : s ≠ Finset.univ) :
    ∃ i ∈ s, ∃ W ∉ s, 0 < T.intersection W i := by
  have hcon : ∃ i ∈ s, ∃ j ∉ s, T.intersection i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact T.connected ⟨(s : Set (Fin T.componentCount)), ⟨j₀, hj₀⟩,
      fun h => hne (Finset.coe_eq_univ.mp h), fun i hi j hj => hcon i hi j hj⟩
  obtain ⟨i, hi, W, hW, hiW⟩ := hcon
  refine ⟨i, hi, W, hW, ?_⟩
  have hne' : W ≠ i := fun h => hW (h ▸ hi)
  rw [T.intersection_symm]
  exact lt_of_le_of_ne (T.intersection_nonneg i W (fun h => hne' h.symm)) (Ne.symm hiW)

/-- Adding a component which meets the set does not decrease the defect. -/
private theorem genusDefect_le_genusDefect_insert (χ : Finset (Fin T.componentCount) → ℤ)
    (c gg : Fin T.componentCount → ℤ)
    (hstep : ∀ s W, W ∉ s → χ (insert W s) = χ s - ∑ j ∈ s, T.intersection W j + c W)
    (hgg : ∀ i, gg i ≤ T.weight i - c i) (s : Finset (Fin T.componentCount))
    {W : Fin T.componentCount} (hW : W ∉ s) {j : Fin T.componentCount} (hj : j ∈ s)
    (hpos : 0 < T.intersection W j) :
    T.genusDefect χ gg s ≤ T.genusDefect χ gg (insert W s) := by
  rw [T.genusDefect_insert χ c gg hstep s hW]
  linarith [T.addSlack_nonneg s hW hj hpos, hgg W]

variable (χ : Finset (Fin T.componentCount) → ℤ) (c gg : Fin T.componentCount → ℤ)
  (hstep : ∀ s W, W ∉ s → χ (insert W s) = χ s - ∑ j ∈ s, T.intersection W j + c W)
  (hgg : ∀ i, gg i ≤ T.weight i - c i)

include hstep hgg in
/-- The defect of all the components bounds the defect of any set containing a given
component. -/
theorem genusDefect_le_genusDefect_univ (j₀ : Fin T.componentCount) :
    ∀ s : Finset (Fin T.componentCount), j₀ ∈ s →
      T.genusDefect χ gg s ≤ T.genusDefect χ gg Finset.univ := by
  classical
  have key : ∀ k : ℕ, ∀ s : Finset (Fin T.componentCount), j₀ ∈ s →
      (Finset.univ \ s).card = k → T.genusDefect χ gg s ≤ T.genusDefect χ gg Finset.univ := by
    intro k
    induction k with
    | zero =>
      intro s _ hk
      have : s = Finset.univ := by
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hk
        exact Finset.eq_univ_of_forall fun x => hk (Finset.mem_univ x)
      rw [this]
    | succ k ih =>
      intro s hj₀ hk
      have hne : s ≠ Finset.univ := by
        rintro rfl
        simp at hk
      obtain ⟨i, hi, W, hW, hpos⟩ := T.exists_intersection_pos_of_ne_univ s hj₀ hne
      have hcard : (Finset.univ \ insert W s).card = k := by
        have : Finset.univ \ insert W s = (Finset.univ \ s).erase W := by
          ext x
          simp [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        rw [this, Finset.card_erase_of_mem (by simp [hW]), hk]
        simp
      exact (T.genusDefect_le_genusDefect_insert χ c gg hstep hgg s hW hi hpos).trans
        (ih (insert W s) (Finset.mem_insert_of_mem hj₀) hcard)
  exact fun s hs => key _ s hs rfl

include hstep hgg in
/-- **The defect controls every step of the induction of [Stacks, Tag 0CEA].** Let `χ`, `c`,
`g'` be as in `AlgebraicGeometry.NumericalType.topologicalGenus_add_sum_le`, and let
`Δ = (1 - χ(all)) - g_top - Σ g'_i` be the defect of that inequality. Then
`w_i - c_i - g'_i ≤ Δ` for every component `i`, and every component `i ≠ j₀` can be added, in
some order of the induction, to a set `s ∌ i` it meets with slack at most `Δ`. -/
theorem le_genusDefect_univ (j₀ : Fin T.componentCount) (hw₀ : T.weight j₀ = 1)
    (hbase : χ {j₀} = c j₀) :
    (∀ i, T.weight i - c i - gg i ≤ T.genusDefect χ gg Finset.univ) ∧
      ∀ i, i ≠ j₀ → ∃ s : Finset (Fin T.componentCount), i ∉ s ∧
        (∃ j ∈ s, 0 < T.intersection i j) ∧ T.addSlack i s ≤ T.genusDefect χ gg Finset.univ := by
  classical
  have hD₀ : T.genusDefect χ gg {j₀} = T.weight j₀ - c j₀ - gg j₀ := by
    unfold genusDefect
    rw [Finset.card_singleton, edgeCountOn_singleton, Finset.sum_singleton, hbase, hw₀]
    push_cast
    ring
  have hmono := T.genusDefect_le_genusDefect_univ χ c gg hstep hgg j₀
  -- for `i ≠ j₀`, a maximal set through `j₀` avoiding `i` with nonnegative defect
  have hstepI : ∀ i, i ≠ j₀ → ∃ s : Finset (Fin T.componentCount), j₀ ∈ s ∧ i ∉ s ∧
      0 ≤ T.genusDefect χ gg s ∧ ∃ j ∈ s, 0 < T.intersection i j := by
    intro i hi
    let F := (Finset.univ : Finset (Finset (Fin T.componentCount))).filter
      fun s => j₀ ∈ s ∧ i ∉ s ∧ 0 ≤ T.genusDefect χ gg s
    have hF : ({j₀} : Finset _) ∈ F := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton_self _,
        by simpa using hi, ?_⟩
      rw [hD₀]
      linarith [hgg j₀]
    obtain ⟨s, hsF, hsmax⟩ := F.exists_max_image Finset.card ⟨_, hF⟩
    obtain ⟨-, hj₀s, his, hDs⟩ := Finset.mem_filter.mp hsF
    refine ⟨s, hj₀s, his, hDs, ?_⟩
    have hne : s ≠ Finset.univ := fun h => his (h ▸ Finset.mem_univ i)
    obtain ⟨a, ha, W, hW, hpos⟩ := T.exists_intersection_pos_of_ne_univ s hj₀s hne
    by_cases hWi : W = i
    · subst hWi
      exact ⟨a, ha, hpos⟩
    · exfalso
      have hins : insert W s ∈ F := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_of_mem hj₀s, ?_, ?_⟩
        · simp only [Finset.mem_insert, not_or]
          exact ⟨Ne.symm hWi, his⟩
        · exact hDs.trans (T.genusDefect_le_genusDefect_insert χ c gg hstep hgg s hW ha hpos)
      have := hsmax _ hins
      rw [Finset.card_insert_of_notMem hW] at this
      omega
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · by_cases hi : i = j₀
    · subst hi
      rw [← hD₀]
      exact hmono _ (Finset.mem_singleton_self _)
    · obtain ⟨s, hj₀s, his, hDs, j, hj, hpos⟩ := hstepI i hi
      have h1 := hmono (insert i s) (Finset.mem_insert_of_mem hj₀s)
      rw [T.genusDefect_insert χ c gg hstep s his] at h1
      linarith [T.addSlack_nonneg s his hj hpos]
  · obtain ⟨s, hj₀s, his, hDs, j, hj, hpos⟩ := hstepI i hi
    refine ⟨s, his, ⟨j, hj, hpos⟩, ?_⟩
    have h1 := hmono (insert i s) (Finset.mem_insert_of_mem hj₀s)
    rw [T.genusDefect_insert χ c gg hstep s his] at h1
    linarith [hgg i]

/-- The defect of all the components is the defect of the inequality of [Stacks, Tag 0CEA]. -/
theorem genusDefect_univ :
    T.genusDefect χ gg Finset.univ = (1 - χ Finset.univ) - (T.topologicalGenus + ∑ i, gg i) := by
  unfold genusDefect topologicalGenus
  rw [Finset.card_univ, Fintype.card_fin, edgeCountOn_univ]

end AlgebraicGeometry.NumericalType

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A point whose local ring is a domain lies on only one irreducible component.** The generic
points of the components through `x` are generizations of `x`, hence images of points of
`Spec 𝒪_{X,x}`, all of which are specializations of the image of its generic point; a generic
point of an irreducible component has no proper generization. -/
theorem eq_of_mem_irreducibleComponents_of_isDomain_stalk {Y : Scheme.{u}} (x : Y)
    [IsDomain (Y.presheaf.stalk x)] {Z₁ Z₂ : irreducibleComponents Y} (h₁ : x ∈ Z₁.1)
    (h₂ : x ∈ Z₂.1) : Z₁ = Z₂ := by
  set η := Y.fromSpecStalk x (genericPoint (Spec (Y.presheaf.stalk x)))
  have key : ∀ Z : irreducibleComponents Y, x ∈ Z.1 → closure ({η} : Set Y) = Z.1 := by
    intro Z hx
    have hZc : IsClosed Z.1 := isClosed_of_mem_irreducibleComponents _ Z.2
    have hgen := Z.2.1.isGenericPoint_genericPoint_closure
    rw [hZc.closure_eq] at hgen
    have hsp : Z.2.1.genericPoint ⤳ x := hgen.specializes hx
    obtain ⟨q, hq⟩ : Z.2.1.genericPoint ∈ Set.range (Y.fromSpecStalk x) := by
      rwa [Scheme.range_fromSpecStalk]
    have hηξ : η ⤳ Z.2.1.genericPoint := by
      rw [← hq]
      exact (genericPoint_specializes q).map (Y.fromSpecStalk x).continuous
    have hsub : Z.1 ⊆ closure ({η} : Set Y) := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hηξ))
        isClosed_closure
    exact le_antisymm (Z.2.2 isIrreducible_singleton.closure hsub) hsub
  exact Subtype.ext ((key Z₁ h₁).symm.trans (key Z₂ h₂))

end AlgebraicGeometry

attribute [local instance] Stacks.Models.RegularProperModelSituation.connectedSpace_specialFiber

namespace Stacks.Models.RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **Every irreducible component of the special fibre is a curve.** A component of dimension zero
would be a single point not lying on any other component, hence open and closed in the connected
special fibre, which is one-dimensional. -/
@[sga "2 XIII 2.2" "special case"]
theorem topologicalKrullDim_specialFiberComponent_eq_one
    (Z : irreducibleComponents S.specialFiber) :
    topologicalKrullDim (S.specialFiberComponentIdeal Z).subscheme = 1 := by
  set C := (S.specialFiberComponentIdeal Z).subscheme
  refine le_antisymm (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z) ?_
  by_contra hlt
  push Not at hlt
  have hle0 : topologicalKrullDim C ≤ 0 := by
    refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun a b hab => ?_
    by_contra hba
    exact absurd (Order.one_le_krullDim_iff.mpr ⟨a, b, lt_of_le_not_ge hab hba⟩) (not_le.mpr hlt)
  have hsub : ∀ a b : C, a = b := by
    have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hle0
    have hgen : ∀ a : C, IsGenericPoint a Set.univ := fun a =>
      Set.eq_univ_of_univ_subset <| hmax ⟨closure {a}, isIrreducible_singleton.closure,
        isClosed_closure⟩ (b := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ C, isClosed_univ⟩)
        fun y _ => Set.mem_univ y
    exact fun a b => (hgen a).eq (hgen b)
  have hZsub : (Z.1 : Set S.specialFiber).Subsingleton := by
    rw [← S.range_specialFiberComponentι Z]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [hsub a b]
  have hcompl : (Z.1 : Set S.specialFiber)ᶜ = ⋃ W ∈ Finset.univ.erase Z, (W.1 : Set _) := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Finset.mem_erase, Finset.mem_univ, and_true,
      exists_prop]
    constructor
    · intro hy
      obtain ⟨W, hW⟩ := S.exists_mem_specialFiberComponent y
      exact ⟨W, fun h => hy (h ▸ hW), hW⟩
    · rintro ⟨W, hWZ, hyW⟩ hyZ
      have hZW : (Z.1 : Set S.specialFiber) ⊆ W.1 := fun z hz => (hZsub hz hyZ) ▸ hyW
      exact hWZ (Subtype.ext (le_antisymm (Z.2.2 W.2.1 hZW) hZW))
  have hopen : IsOpen (Z.1 : Set S.specialFiber) := by
    rw [← isClosed_compl_iff, hcompl]
    exact isClosed_biUnion_finset fun W _ => isClosed_of_mem_irreducibleComponents _ W.2
  have huniv := (isClopen_iff.mp ⟨isClosed_of_mem_irreducibleComponents _ Z.2, hopen⟩).resolve_left
    Z.2.1.nonempty.ne_empty
  have hsubX : ∀ a b : S.specialFiber, a = b := fun a b =>
    hZsub (huniv ▸ Set.mem_univ a) (huniv ▸ Set.mem_univ b)
  have hX : topologicalKrullDim S.specialFiber ≤ 0 := by
    refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun A B _ => ?_
    intro y _
    obtain ⟨a, ha⟩ := A.2.nonempty
    exact hsubX a y ▸ ha
  obtain ⟨w, -⟩ := Z.2.1.nonempty
  rw [S.topologicalKrullDim_specialFiber ⟨w⟩] at hX
  exact absurd hX (by decide)

/-- Each irreducible component of the special fibre is a curve over the residue field. -/
theorem isCurve_specialFiberComponentToSpec (Z : irreducibleComponents S.specialFiber) :
    IsCurve S.k (S.specialFiberComponentToSpec Z) :=
  { toIsVariety := { }
    topologicalKrullDim_eq_one := S.topologicalKrullDim_specialFiberComponent_eq_one Z }

/-- **The component through a smooth rational point is smooth there.** If `x` is a `k`-rational
point of `X_k` at which `X_k ⟶ Spec(k)` is smooth and `C_Z` is a component through `x`, then the
point `y` of `C_Z` over `x` is `k`-rational and `C_Z ⟶ Spec(k)` is smooth at `y`: the local ring
of `X_k` at `x` is regular, hence a domain, so the ideal of `C_Z` in it, a minimal prime, is zero
and the two local rings agree. -/
theorem exists_isRationalPoint_smoothAt_specialFiberComponentToSpec (x : S.specialFiber)
    (hx : IsRationalPoint S.specialFiberToSpec x)
    (hsm : InfinitesimalLifting.SmoothAt S.specialFiberToSpec x)
    (Z : irreducibleComponents S.specialFiber) (hxZ : x ∈ Z.1) :
    ∃ y : (S.specialFiberComponentIdeal Z).subscheme, S.specialFiberComponentι Z y = x ∧
      IsRationalPoint (S.specialFiberComponentToSpec Z) y ∧
      InfinitesimalLifting.SmoothAt (S.specialFiberComponentToSpec Z) y := by
  have hreg := isRegularLocalRing_stalk_of_smoothAt_of_isRationalPoint _ x hx hsm
  have : IsDomain (S.specialFiber.presheaf.stalk x) := IsRegularLocalRing.isDomain _
  obtain ⟨y, rfl⟩ : x ∈ Set.range (S.specialFiberComponentι Z).base := by
    rwa [S.range_specialFiberComponentι Z]
  have hy : IsRationalPoint (S.specialFiberComponentToSpec Z) y :=
    isRationalPoint_comp (S.specialFiberComponentι Z) S.specialFiberToSpec y hx
  refine ⟨y, rfl, hy, ?_⟩
  have hker : (S.specialFiberComponentι Z).ker = irreducibleComponentIdeal Z := by
    rw [ker_eq_vanishingIdeal_of_reduced_closed_immersion]
    congr 1
    refine SetLike.coe_injective ?_
    rw [Scheme.Hom.support_ker, S.range_specialFiberComponentι]
    exact (isClosed_of_mem_irreducibleComponents _ Z.2).closure_eq
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.specialFiber.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (S.specialFiberComponentι Z y)) isOpen_univ
  have hstalk := stalk_ker_eq_of_affine_target (S.specialFiberComponentι Z) y U hU hxU
  have hmin := stalk_vanishingIdeal_mem_minimalPrimes (S.specialFiberComponentι Z y) Z hxZ
  rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hmin
  rw [hker] at hstalk
  have hinj : Function.Injective ((S.specialFiberComponentι Z).stalkMap y).hom := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ RingHom.ker ((S.specialFiberComponentι Z).stalkMap y).hom := ha
    rw [← hstalk, hmin] at this
    exact (Submodule.mem_bot _).mp this
  have hregy : IsRegularLocalRing
      ((S.specialFiberComponentIdeal Z).subscheme.presheaf.stalk y) :=
    IsRegularLocalRing.of_ringEquiv
      (RingEquiv.ofBijective _ ⟨hinj, (S.specialFiberComponentι Z).stalkMap_surjective y⟩)
  exact (smoothAt_iff_isRegularLocalRing_stalk _ y
    (isSeparableExtension_residueField_of_isRationalPoint _ y hy)).mpr hregy

/-- The genus over `k` of a component of the special fibre is `[κ_Z : k] · g_Z`. -/
theorem genus_specialFiberComponentToSpec (Z : irreducibleComponents S.specialFiber) :
    genus (S.specialFiberComponentToSpec Z) =
      S.specialFiberComponentWeight Z * S.specialFiberComponentGenus Z := by
  let := (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
  exact genus_eq_finrank_globalSections_mul_genus_toSpecΓ S.k (S.specialFiberComponentToSpec Z)
    (S.isField_and_finite_globalSections_specialFiberComponent Z).1

/-- **Equality in [Stacks, Tag 0CEA] forces equality at every step.** If
`dim_k H¹((X_k)_red, 𝒪) = g_top + g_geom(X_k/k)` at a `k`-rational point `x` of `X_k`, then every
component has `g_geom(C_Z/k) = [κ_Z : k] · g_Z`, and every component not through `x` meets some
other component `C_W` with `(C_Z · C_W) = [κ_Z : k]`. -/
theorem geometricGenus_eq_and_exists_componentIntersection_eq_weight
    (x : S.specialFiber) (hx : IsRationalPoint S.specialFiberToSpec x)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (heq : (S.associatedNumericalType n e).topologicalGenus +
        (geometricGenus S.k S.specialFiberToSpec : ℤ) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1))
    (Z₀ : irreducibleComponents S.specialFiber) (hZ₀ : x ∈ Z₀.1) :
    (∀ Z, geometricGenus S.k (S.specialFiberComponentToSpec Z) =
      S.specialFiberComponentWeight Z * S.specialFiberComponentGenus Z) ∧
    ∀ Z, Z ≠ Z₀ → ∃ W, Z ≠ W ∧
      S.specialFiberIntersectionMatrix Z W = S.specialFiberComponentWeight Z := by
  classical
  let T := S.associatedNumericalType n e
  let e' : Fin T.componentCount ≃ irreducibleComponents S.specialFiber := e
  have hw : ∀ i, T.weight i = (S.specialFiberComponentWeight (e' i) : ℤ) := fun _ => rfl
  have hint : ∀ i j, T.intersection i j = S.specialFiberIntersectionMatrix (e' i) (e' j) :=
    S.associatedNumericalType_intersection n e
  let χ : Finset (Fin T.componentCount) → ℤ :=
    fun s => S.specialFiberDivisorEulerChar fun Z => if Z ∈ s.map e'.toEmbedding then 1 else 0
  let c : Fin T.componentCount → ℤ := fun i =>
    eulerCharacteristic S.k (S.specialFiberComponentToSpec (e' i))
      (SheafOfModules.unit (S.specialFiberComponentIdeal (e' i)).subscheme.ringCatSheaf)
  let gg : Fin T.componentCount → ℤ :=
    fun i => (geometricGenus S.k (S.specialFiberComponentToSpec (e' i)) : ℤ)
  have hstep : ∀ s W, W ∉ s → χ (insert W s) = χ s - ∑ j ∈ s, T.intersection W j + c W := by
    intro s W hW
    simp only [χ, c, Finset.map_insert, Equiv.coe_toEmbedding]
    rw [S.specialFiberDivisorEulerChar_indicator_insert _ (by simpa using hW), Finset.sum_map]
    simp only [hint, Equiv.coe_toEmbedding]
  have hgg : ∀ i, gg i ≤ T.weight i - c i := fun i => by
    rw [hw]
    exact S.geometricGenus_specialFiberComponent_le (e' i)
  have hw₀ : T.weight (e'.symm Z₀) = 1 := by
    rw [hw, Equiv.apply_symm_apply,
      S.specialFiberComponentWeight_eq_one_of_isRationalPoint Z₀ x hx hZ₀, Nat.cast_one]
  have hbase : χ {e'.symm Z₀} = c (e'.symm Z₀) := by
    simp only [χ, c, Finset.map_singleton, Equiv.coe_toEmbedding]
    exact S.specialFiberDivisorEulerChar_indicator_singleton _
  obtain ⟨hcomp, hslack⟩ := T.le_genusDefect_univ χ c gg hstep hgg (e'.symm Z₀) hw₀ hbase
  have huniv : (fun Z => if Z ∈ (Finset.univ : Finset (Fin T.componentCount)).map e'.toEmbedding
      then 1 else 0) = fun _ => 1 := by
    funext Z
    simp
  have hsum : ∑ i : Fin T.componentCount, gg i =
      (geometricGenus S.k S.specialFiberToSpec : ℤ) := by
    simp only [gg]
    rw [S.geometricGenus_specialFiberToSpec_eq_sum, Nat.cast_sum]
    exact Fintype.sum_equiv e' _ _ fun _ => rfl
  have hΔ : T.genusDefect χ gg Finset.univ = 0 := by
    rw [T.genusDefect_univ, hsum]
    simp only [χ, huniv, S.specialFiberDivisorEulerChar_one x hx]
    rw [heq]
    ring
  refine ⟨fun Z => ?_, fun Z hZ => ?_⟩
  · obtain ⟨i, rfl⟩ := e'.surjective Z
    have h1 := hcomp i
    have h2 := hgg i
    rw [hΔ] at h1
    simp only [gg, c, hw] at h1 h2
    rw [S.eulerCharacteristic_specialFiberComponent_eq (e' i)] at h1 h2
    have : (geometricGenus S.k (S.specialFiberComponentToSpec (e' i)) : ℤ) =
        (S.specialFiberComponentWeight (e' i) : ℤ) * S.specialFiberComponentGenus (e' i) := by
      linarith
    exact_mod_cast this
  · have hi : e'.symm Z ≠ e'.symm Z₀ := fun h => hZ (e'.symm.injective h)
    obtain ⟨s, his, ⟨j, hj, hpos⟩, hsl⟩ := hslack _ hi
    rw [hΔ] at hsl
    have hij := T.intersection_eq_weight_of_addSlack_nonpos s his hsl hj hpos
    refine ⟨e' j, fun h => his (by rwa [h, Equiv.symm_apply_apply]), ?_⟩
    rwa [hint, hw, Equiv.apply_symm_apply] at hij

/-- **Stacks Project, Tag 0CEE**, in corrected form, with the
separability clause of part (2) asserted for the components of positive genus. In the
situation of [Stacks, Tag 0C61] let `x` be a `k`-rational point of `X_k` at which `X_k ⟶ Spec(k)`
is smooth, and suppose equality holds in [Stacks, Tag 0CEA]:
`dim_k H¹((X_k)_red, 𝒪) = g_top + g_geom(X_k/k)`. Then

1. `x` lies on a unique irreducible component of `X_k`, and that component is a smooth,
   H-projective, geometrically irreducible curve over `k`;
2. every other irreducible component `C` has `κ = H⁰(C, 𝒪_C)` finite over `k`, has a `κ`-rational
   point and is smooth over `κ`; and `κ/k` is separable as soon as `H¹(C, 𝒪_C) ≠ 0`.

**The correction.** The source asserts in (2) that `κ/k` is always separable. That is false: let
`R = 𝔽_p(t)[[π]]`, so `k = 𝔽_p(t)`, let `C = ℙ¹_K`, and let `X` be the blow-up of `ℙ¹_R` at the
closed point `c ∈ ℙ¹_k` with residue field `κ = k(t^{1/p})`, purely inseparable of degree `p` over
`k`. Then `X` is a regular proper model of `C`, `X_k = C₁ + E` is reduced with `C₁ ≅ ℙ¹_k` the
strict transform and `E ≅ ℙ¹_κ` the exceptional curve, the two meeting transversally in one
`κ`-point, so `(C₁ · E) = p`. A `k`-point of `C₁` away from `c` is a smooth rational point of
`X_k`. Here `dim_k H¹(X_k, 𝒪) = 0` (because `χ(X_k, 𝒪) = χ(ℙ¹_K, 𝒪) = 1` and `H⁰(X_k, 𝒪) = k`),
`g_top = 1 - 2 + 1 = 0` and `g_geom(X_k/k) = 0 + 0`, so equality holds; but `H⁰(E, 𝒪_E) = κ` is not
separable over `k`. The source's step "equality in `[κ_i : k] g_i ≥ [κ_i : k]_s g_i ≥ g_geom`
implies `κ_i/k` separable" needs `g_i > 0`; every other assertion of the tag survives.

**The proof.** Equality in the induction of [Stacks, Tag 0CEA] forces equality at each step
(`geometricGenus_eq_and_exists_componentIntersection_eq_weight`): `g_geom(C_Z/k) = [κ_Z : k] g_Z`
for every component, and each component `C_Z` not through `x` meets some `C_W` with
`(C_Z · C_W) = [κ_Z : k]`, which makes `C_Z ∩ C_W` a `κ_Z`-rational point at which `C_Z` is
smooth over `κ_Z`. A smooth rational point makes a curve geometrically integral over its field of
constants ([Stacks, Tag 0CDW]), and a geometrically integral curve whose geometric genus is its
genus is smooth, because its normalization over `k̄` does not change the genus and is therefore
an isomorphism ([Stacks, Tag 0CE4]). Projectivity of the integral proper curve through `x` is
[Stacks, Tag 0A25] for integral curves together with [Stacks, Tag 0BCL]. -/
@[stacks 0CEE "(1) in full, and (2) with kappa/k separable when H^1(C, O_C) is nonzero \
(the corrected form)"]
theorem smooth_of_topologicalGenus_add_geometricGenus_eq_finrank_reduction
    (x : S.specialFiber) (hx : IsRationalPoint S.specialFiberToSpec x)
    (hsm : InfinitesimalLifting.SmoothAt S.specialFiberToSpec x)
    (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber)
    (heq : (S.associatedNumericalType n e).topologicalGenus +
        (geometricGenus S.k S.specialFiberToSpec : ℤ) =
      Module.finrank S.k (cohomologyOverField S.k
        (S.specialFiber.reductionι ≫ S.specialFiberToSpec)
        (SheafOfModules.unit S.specialFiber.reduction.ringCatSheaf) 1)) :
    (∃! Z : irreducibleComponents S.specialFiber, x ∈ Z.1) ∧
    (∀ Z : irreducibleComponents S.specialFiber, x ∈ Z.1 →
      Smooth (S.specialFiberComponentToSpec Z) ∧
        Stacks.HProjective.IsHProjective (S.specialFiberComponentToSpec Z) ∧
        GeometricallyIrreducible (S.specialFiberComponentToSpec Z) ∧
        IsCurve S.k (S.specialFiberComponentToSpec Z)) ∧
    (∀ Z : irreducibleComponents S.specialFiber, x ∉ Z.1 →
      letI : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
        (S.isField_and_finite_globalSections_specialFiberComponent Z).1.toField
      letI : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of S.k)).inv ≫ (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
      FiniteDimensional S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) ∧
        (genus (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ ≠ 0 →
          Algebra.IsSeparable S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤)) ∧
        (∃ c : (S.specialFiberComponentIdeal Z).subscheme,
          IsRationalPoint (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ c) ∧
        Smooth (S.specialFiberComponentIdeal Z).subscheme.toSpecΓ) := by
  have hreg := isRegularLocalRing_stalk_of_smoothAt_of_isRationalPoint _ x hx hsm
  have : IsDomain (S.specialFiber.presheaf.stalk x) := IsRegularLocalRing.isDomain _
  obtain ⟨Z₀, hZ₀⟩ := S.exists_mem_specialFiberComponent x
  have huniq : ∀ Z : irreducibleComponents S.specialFiber, x ∈ Z.1 → Z = Z₀ := fun Z hZ =>
    eq_of_mem_irreducibleComponents_of_isDomain_stalk x hZ hZ₀
  obtain ⟨hgeom, hmeet⟩ :=
    S.geometricGenus_eq_and_exists_componentIntersection_eq_weight x hx n e heq Z₀ hZ₀
  refine ⟨⟨Z₀, hZ₀, huniq⟩, fun Z hZ => ?_, fun Z hZ => ?_⟩
  · -- part (1)
    obtain rfl := huniq Z hZ
    set f := S.specialFiberComponentToSpec Z
    have hcurve : IsCurve S.k f := S.isCurve_specialFiberComponentToSpec Z
    have hdim : topologicalKrullDim (S.specialFiberComponentIdeal Z).subscheme = 1 :=
      S.topologicalKrullDim_specialFiberComponent_eq_one Z
    obtain ⟨y, -, hy, hsmy⟩ :=
      S.exists_isRationalPoint_smoothAt_specialFiberComponentToSpec x hx hsm Z hZ
    have hgi : GeometricallyIntegral f :=
      geometricallyIntegral_of_isVariety_of_smoothAt_rationalPoint f
        (ptOfIsRationalPoint f y hy) (ptOfIsRationalPoint_comp f y hy)
        (by rwa [ptOfIsRationalPoint_apply])
    have : IsIntegral (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap S.k (AlgebraicClosure S.k))))) :=
      pullback_of_geometrically hgi.geometrically_isIntegral (AlgebraicClosure S.k) _
    have hgf : geometricGenus S.k f = genus f := by
      rw [hgeom Z, S.genus_specialFiberComponentToSpec Z]
    have hsmooth : Smooth f := by
      refine smooth_of_geometricGenus_pullback_eq_genus S.k (AlgebraicClosure S.k)
        (algebraMap S.k (AlgebraicClosure S.k)) f hdim ?_
      rw [← geometricGenus_eq_geometricGenus_pullback_snd S.k f hdim.le,
        genus_pullback_snd_eq, hgf]
    refine ⟨hsmooth, ?_, inferInstance, hcurve⟩
    exact (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper (f := f)).mpr
      ⟨Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral f hdim, inferInstance⟩
  · -- part (2)
    have hne : Z ≠ Z₀ := fun h => hZ (h ▸ hZ₀)
    obtain ⟨W, hZW, hZWw⟩ := hmeet Z hne
    obtain ⟨c, hc, hsmc⟩ :=
      S.exists_isRationalPoint_smoothAt_toSpecΓ_of_componentIntersection_eq_weight hZW hZWw
    have : IsCurve S.k (S.specialFiberComponentToSpec Z) :=
      S.isCurve_specialFiberComponentToSpec Z
    obtain ⟨hsmooth, hsep⟩ := smooth_toSpecΓ_and_isSeparable_of_geometricGenus_eq S.k
      (S.specialFiberComponentToSpec Z) c hc hsmc (hgeom Z)
    exact ⟨(S.isField_and_finite_globalSections_specialFiberComponent Z).2, hsep, ⟨c, hc⟩,
      hsmooth⟩

end Stacks.Models.RegularProperModelSituation
