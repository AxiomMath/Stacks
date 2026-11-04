/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealOfDefinitionCounterexample
public import StacksFrontier.AlgebraicGeometry.FormalScheme.IdealSheafMinimalOpens
public import StacksFrontier.AlgebraicGeometry.FormalScheme.TwistedDoubleFormalScheme

/-!
# A fundamental system of ideals of definition on the twisted double

The twisted double `D` of `Y = Spf R⟦X⟧` over the bouquet ring `R`
(`AlgebraicGeometry.TwistedDouble.D`) is not quasi-separated, so the existence theorem of Stacks
0AJF does not apply to it. It nevertheless has a fundamental system of ideals of definition over
its affine formal opens: every point of `D` has a smallest open neighbourhood, which lies in one
of the two charts `U b ≅ Spf R⟦X⟧`, and the closed subschemes `Spec (R⟦X⟧/(X)^(l+1))` of the charts
cut out, over these smallest neighbourhoods, ideals of definition forming a basis of zero.

## Main definitions

* `AlgebraicGeometry.TwistedDouble.o`: the closed point of the `b`-th copy of `Y`.
* `AlgebraicGeometry.TwistedDouble.minOpen`, `AlgebraicGeometry.TwistedDouble.minIndex`: the
  smallest open neighbourhoods of the points of `D`, the charts `U b` and the points `η n`.
* `AlgebraicGeometry.TwistedDouble.chartIdeal`: over an open `V` of `D`, the sum of the kernel
  ideals of `Spec (R⟦X⟧/(X)^(l+1))` in those charts which contain `V`.

## Main results

* `AlgebraicGeometry.TwistedDouble.U_le_of_o_mem`: the smallest neighbourhood of `o b` is `U b`.
* `AlgebraicGeometry.TwistedDouble.η_le_of_mem`: the smallest neighbourhood of a point of `η n`
  is `η n`, a single point (`AlgebraicGeometry.TwistedDouble.mem_η_iff_eq`).
* `AlgebraicGeometry.TwistedDouble.minOpen_minIndex_le`: every point has a smallest open
  neighbourhood.
* `AlgebraicGeometry.LocallyTopologicallyRingedSpace`
  `.IsFundamentalSystemOfIdealsOfDefinitionOn.mono`: a fundamental system over a class of opens
  is one over any subclass.
* `AlgebraicGeometry.TwistedDouble.exists_isFundamentalSystemOfIdealsOfDefinitionOn`: the twisted
  double has a fundamental system of ideals of definition over its affine formal opens.

## Implementation notes

The fundamental system is built with
`LocallyTopologicallyRingedSpace.IdealSheaf.ofMinimalOpens`, from the ideals `chartIdeal l` over
the smallest neighbourhoods. Over a smallest neighbourhood lying in both charts (a point `η n`)
the two kernels are summed, which keeps the ideals compatible with restriction.

## References

* [Stacks Project, Tag 0AIW](https://stacks.math.columbia.edu/tag/0AIW)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace

/-- A fundamental system of ideals of definition over a class `𝒜` of opens is one over every
subclass `𝒜'`: both conditions are asked of each open of the class. -/
theorem IsFundamentalSystemOfIdealsOfDefinitionOn.mono {X : LTRS.{u}} {𝒮 : Set (IdealSheaf X)}
    {𝒜 𝒜' : Opens X → Prop} (h : IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 𝒜)
    (h𝒜 : ∀ U, 𝒜' U → 𝒜 U) : IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 𝒜' :=
  ⟨fun I hI U hU => h.1 I hI U (h𝒜 U hU), fun U hU => h.2 U (h𝒜 U hU)⟩

end AlgebraicGeometry.LocallyTopologicallyRingedSpace

namespace AlgebraicGeometry.TwistedDouble

open LocallyTopologicallyRingedSpace PowerSeriesFormalSpectrum IsLocalRing

open PowerSeries (X C)

/-! ### The smallest open neighbourhoods -/

/-- The points of `Y` are those of `Spec R`: `pointsEquiv` followed by its inverse is the
identity of `Y`. -/
theorem symm_pointsEquiv (x : Y) : pointsEquiv.symm (pointsEquiv x) = x :=
  pointsEquiv.symm_apply_apply x

/-- A point of `Y` corresponds to the point `p` of `Spec R` exactly when it is the point attached
to `p`. -/
theorem pointsEquiv_eq_iff (x : Y) (p : PrimeSpectrum BouquetRing.R) :
    pointsEquiv x = p ↔ x = pointsEquiv.symm p :=
  pointsEquiv.eq_symm_apply.symm

/-- Every point of `Y` specializes to the closed point of `Spec R`: the points of `Y` are those of
`Spec R`, a local ring. -/
theorem specializes_closedPoint (x : Y) : x ⤳ pointsEquiv.symm (closedPoint BouquetRing.R) := by
  have := (IsLocalRing.specializes_closedPoint (pointsEquiv x)).map pointsEquiv.symm.continuous
  rwa [symm_pointsEquiv] at this

/-- An open of `Y` containing the closed point is all of `Y`. -/
theorem eq_top_of_closedPoint_mem {V : Opens Y}
    (hV : pointsEquiv.symm (closedPoint BouquetRing.R) ∈ V) : V = ⊤ :=
  eq_top_iff.mpr fun x _ => (specializes_closedPoint x).mem_open V.2 hV

/-- The closed point of the `b`-th copy of `Y` in the twisted double. -/
noncomputable def o (b : Bool) : D :=
  (h b).toHom.base (pointsEquiv.symm (closedPoint BouquetRing.R))

/-- The closed point `o b` lies in the `b`-th copy `U b`. -/
theorem o_mem_U (b : Bool) : o b ∈ U b :=
  (mem_U_iff b _).mpr ⟨_, rfl⟩

/-- **The smallest neighbourhood of `o b` is `U b`.** An open of `D` containing `o b` pulls back
to an open of the `b`-th copy containing its closed point, which is the whole copy. -/
theorem U_le_of_o_mem {b : Bool} {V : Opens D} (hV : o b ∈ V) : U b ≤ V := by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_U_iff b z).mp hz
  have htop := eq_top_of_closedPoint_mem (V := (Opens.map (h b).toHom.base).obj V) hV
  have hx : x ∈ (Opens.map (h b).toHom.base).obj V := htop ▸ trivial
  exact hx

/-- The open `pt n` of `Y` is the single point attached to `q n`. -/
theorem mem_pt_iff_eq (n : ℕ) (x : Y) : x ∈ pt n ↔ x = pointsEquiv.symm (BouquetRing.q n) :=
  (mem_pt_iff n x).trans (pointsEquiv_eq_iff x _)

/-- The open `η n` of `D` is a single point. -/
theorem mem_η_iff_eq (n : ℕ) (z : D) :
    z ∈ η n ↔ z = (h false).toHom.base (pointsEquiv.symm (BouquetRing.q n)) := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact congrArg _ ((mem_pt_iff_eq n x).mp hx)
  · rintro rfl
    exact ⟨_, (mem_pt_iff_eq n _).mpr rfl, rfl⟩

/-- The open `η n` is quasi-compact, being a single point. -/
theorem isCompact_η (n : ℕ) : IsCompact (η n : Set D) := by
  have hs : (η n : Set D).Subsingleton := fun z hz z' hz' =>
    ((mem_η_iff_eq n z).mp hz).trans ((mem_η_iff_eq n z').mp hz').symm
  exact hs.finite.isCompact

/-- **The smallest neighbourhood of a point of `η n` is `η n`**, which is a single point. -/
theorem η_le_of_mem {n : ℕ} {z : D} {V : Opens D} (hz : z ∈ η n) (hzV : z ∈ V) : η n ≤ V := by
  intro z' hz'
  rw [(mem_η_iff_eq n z').mp hz', ← (mem_η_iff_eq n z).mp hz]
  exact hzV

/-- A point of the `b`-th copy of `Y` lying in no `η n` is the closed point `o b`. -/
theorem eq_o_of_forall_notMem_η {b : Bool} {x : Y} (hx : ∀ n, (h b).toHom.base x ∉ η n) :
    (h b).toHom.base x = o b := by
  rcases BouquetRing.eq_closedPoint_or_exists_eq_q (pointsEquiv x) with hc | ⟨n, hn⟩
  · exact congrArg _ ((pointsEquiv_eq_iff x _).mp hc)
  · exact ((hx n) ((h_base_mem_η_iff b n x).mpr ((mem_pt_iff n x).mpr hn))).elim

/-- The smallest open neighbourhoods of the points of `D`: the copy `U b` for the closed point
`o b`, and the point `η n` itself. -/
noncomputable def minOpen : Bool ⊕ ℕ → Opens D
  | .inl b => U b
  | .inr n => η n

open Classical in
/-- The index of the smallest open neighbourhood of a point of `D`: `η n` for a point of `η n`,
and otherwise the copy `U b` containing it. -/
noncomputable def minIndex (z : D) : Bool ⊕ ℕ :=
  if hz : ∃ n, z ∈ η n then .inr hz.choose else if z ∈ U true then .inl true else .inl false

/-- Every point of `D` lies in its smallest neighbourhood. -/
theorem mem_minOpen_minIndex (z : D) : z ∈ minOpen (minIndex z) := by
  unfold minIndex
  split_ifs with hz ht
  · exact hz.choose_spec
  · exact ht
  · obtain ⟨b, x, rfl⟩ := exists_h_base_eq z
    cases b
    · exact (mem_U_iff false _).mpr ⟨x, rfl⟩
    · exact (ht ((mem_U_iff true _).mpr ⟨x, rfl⟩)).elim

/-- A point of `U b` lying in no `η n` has smallest neighbourhood `U b`. -/
theorem U_le_of_mem {b : Bool} {z : D} (hzU : z ∈ U b) (hη : ¬ ∃ n, z ∈ η n) {V : Opens D}
    (hz : z ∈ V) : U b ≤ V := by
  obtain ⟨x, rfl⟩ := (mem_U_iff b z).mp hzU
  rw [eq_o_of_forall_notMem_η fun n hn => hη ⟨n, hn⟩] at hz
  exact U_le_of_o_mem hz

/-- **Every point of `D` has a smallest open neighbourhood**, `minOpen (minIndex z)`. -/
theorem minOpen_minIndex_le (z : D) (V : Opens D) (hz : z ∈ V) : minOpen (minIndex z) ≤ V := by
  have hmem := mem_minOpen_minIndex z
  unfold minIndex at hmem ⊢
  split_ifs at hmem ⊢ with h₀ h₁
  · exact η_le_of_mem hmem hz
  · exact U_le_of_mem hmem h₀ hz
  · exact U_le_of_mem hmem h₀ hz

/-- Every smallest neighbourhood is quasi-compact. -/
theorem isCompact_minOpen (i : Bool ⊕ ℕ) : IsCompact (minOpen i : Set D) := by
  cases i with
  | inl b => exact isCompact_U b
  | inr n => exact isCompact_η n

/-- Every smallest neighbourhood lies in one of the charts. -/
theorem exists_minOpen_le_U (i : Bool ⊕ ℕ) : ∃ b, minOpen i ≤ U b := by
  cases i with
  | inl b => exact ⟨b, le_rfl⟩
  | inr n => exact ⟨false, η_le_U false n⟩

/-! ### The ideals over the smallest neighbourhoods -/

/-- The ideal of definition `(X)^(l+1)` of `R⟦X⟧`. -/
noncomputable def powXIdeal (l : ℕ) : IdealsOfDefinition A.α :=
  ⟨Ideal.span {X} ^ (l + 1), isIdealOfDefinition_span_X_pow BouquetRing.R l⟩

/-- Over an open `V` of `D`, the kernel ideal of the closed subscheme `Spec (R⟦X⟧/(X)^(l+1))` of
the `b`-th chart when `V` lies in that chart, and `⊥` otherwise. -/
noncomputable def chartKer (b : Bool) (l : ℕ) (V : Opens D) : Ideal (D.presheaf.obj (op V)).α :=
  ⨆ (_ : V ≤ U b),
    (IdealSheaf.ker (spfChartPoint (isPreAdmissible BouquetRing.R) (e b) (powXIdeal l))).ideal V

/-- Over an open `V` of `D`, the sum of the kernel ideals of `Spec (R⟦X⟧/(X)^(l+1))` in the
charts containing `V`. -/
noncomputable def chartIdeal (l : ℕ) (V : Opens D) : Ideal (D.presheaf.obj (op V)).α :=
  chartKer false l V ⊔ chartKer true l V

/-- Over an open in the `b`-th chart, `chartKer b l` is the kernel ideal of the chart. -/
theorem chartKer_of_le {b : Bool} (l : ℕ) {V : Opens D} (hV : V ≤ U b) :
    chartKer b l V = (IdealSheaf.ker
      (spfChartPoint (isPreAdmissible BouquetRing.R) (e b) (powXIdeal l))).ideal V :=
  iSup_pos hV

/-- Over an open not in the `b`-th chart, `chartKer b l` is zero. -/
theorem chartKer_of_not_le {b : Bool} (l : ℕ) {V : Opens D} (hV : ¬ V ≤ U b) :
    chartKer b l V = ⊥ :=
  iSup_neg hV

/-- Restriction carries `chartKer b l` over an open into `chartKer b l` over a smaller one. -/
theorem chartKer_map_le (b : Bool) (l : ℕ) {V V' : Opens D} (hle : V' ≤ V) :
    Ideal.map (D.presheaf.map (homOfLE hle).op).1 (chartKer b l V) ≤ chartKer b l V' := by
  rw [chartKer, Ideal.map_iSup]
  refine iSup_le fun hV => le_iSup_of_le (hle.trans hV) ?_
  exact Ideal.map_le_iff_le_comap.mpr fun s hs => IdealSheaf.map_mem _ hle hs

/-- Restriction carries `chartIdeal l` over an open into `chartIdeal l` over a smaller one. -/
theorem chartIdeal_map_le (l : ℕ) {V V' : Opens D} (hle : V' ≤ V) :
    Ideal.map (D.presheaf.map (homOfLE hle).op).1 (chartIdeal l V) ≤ chartIdeal l V' := by
  rw [chartIdeal, Ideal.map_sup]
  exact sup_le_sup (chartKer_map_le false l hle) (chartKer_map_le true l hle)

/-- The ideals `chartKer b l` decrease in `l`. -/
theorem chartKer_anti (b : Bool) {l l' : ℕ} (hl : l ≤ l') (V : Opens D) :
    chartKer b l' V ≤ chartKer b l V :=
  iSup_mono fun _ => ker_spfChartPoint_le _ _ (Ideal.pow_le_pow_right (by omega)) V

/-- The ideals `chartIdeal l` decrease in `l`. -/
theorem chartIdeal_anti {l l' : ℕ} (hl : l ≤ l') (V : Opens D) :
    chartIdeal l' V ≤ chartIdeal l V :=
  sup_le_sup (chartKer_anti false hl V) (chartKer_anti true hl V)

/-- Over a quasi-compact open in the `b`-th chart, `chartKer b l` is an ideal of definition. -/
theorem isIdealOfDefinition_chartKer {b : Bool} (l : ℕ) {V : Opens D} (hV : V ≤ U b)
    (hc : IsCompact (V : Set D)) : TopologicalRing.IsIdealOfDefinition (chartKer b l V) := by
  rw [chartKer_of_le l hV]
  exact isIdealOfDefinition_ker_spfChartPoint _ _ _ hV hc

/-- Over a quasi-compact open lying in one of the charts, `chartIdeal l` is an ideal of
definition: it is a sum of one or two ideals of definition. -/
theorem isIdealOfDefinition_chartIdeal (l : ℕ) {V : Opens D} {b : Bool} (hV : V ≤ U b)
    (hc : IsCompact (V : Set D)) : TopologicalRing.IsIdealOfDefinition (chartIdeal l V) := by
  by_cases hf : V ≤ U false <;> by_cases ht : V ≤ U true
  · exact TopologicalRing.isIdealOfDefinition_sup (isIdealOfDefinition_chartKer l hf hc)
      (isIdealOfDefinition_chartKer l ht hc)
  · rw [chartIdeal, chartKer_of_not_le l ht, sup_bot_eq]
    exact isIdealOfDefinition_chartKer l hf hc
  · rw [chartIdeal, chartKer_of_not_le l hf, bot_sup_eq]
    exact isIdealOfDefinition_chartKer l ht hc
  · cases b
    · exact (hf hV).elim
    · exact (ht hV).elim

/-- Every neighbourhood of zero in the sections over `V` contains `chartKer b l` over `V` for all
large `l`. -/
theorem exists_forall_chartKer_subset (b : Bool) {V : Opens D}
    {N : Set (D.presheaf.obj (op V)).α} (hN : N ∈ nhds (0 : (D.presheaf.obj (op V)).α)) :
    ∃ k, ∀ l, k ≤ l → (chartKer b l V : Set (D.presheaf.obj (op V)).α) ⊆ N := by
  by_cases hV : V ≤ U b
  · obtain ⟨J, hJ⟩ := exists_ker_spfChartPoint_subset (isPreAdmissible BouquetRing.R) (e b) hV hN
    obtain ⟨k, hk⟩ := (isAdic_iff.mp (isAdic_span_X BouquetRing.R)).2 _
      (J.2.1.mem_nhds J.1.zero_mem)
    refine ⟨k, fun l hl s hs => hJ s ?_⟩
    rw [chartKer_of_le l hV] at hs
    exact ker_spfChartPoint_le _ _ ((Ideal.pow_le_pow_right (by omega)).trans hk) V hs
  · refine ⟨0, fun l _ s hs => ?_⟩
    rw [chartKer_of_not_le l hV] at hs
    rw [(Submodule.mem_bot _).mp hs]
    exact mem_of_mem_nhds hN

/-- Every neighbourhood of zero in the sections over `V` contains `chartIdeal l` over `V` for
some `l`: halve the neighbourhood and take `l` large for both charts. -/
theorem exists_chartIdeal_subset {V : Opens D} {N : Set (D.presheaf.obj (op V)).α}
    (hN : N ∈ nhds (0 : (D.presheaf.obj (op V)).α)) :
    ∃ l, (chartIdeal l V : Set (D.presheaf.obj (op V)).α) ⊆ N := by
  obtain ⟨N₁, hN₁, hN₁N⟩ := exists_nhds_zero_half hN
  obtain ⟨k, hk⟩ := exists_forall_chartKer_subset false hN₁
  obtain ⟨k', hk'⟩ := exists_forall_chartKer_subset true hN₁
  refine ⟨max k k', fun s hs => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hs
  exact hN₁N y (hk _ (le_max_left k k') hy) z (hk' _ (le_max_right k k') hz)

/-! ### The fundamental system -/

/-- The ideal sheaves of the fundamental system: the sections over an open `V` are those whose
restriction to the smallest neighbourhood of every point of `V` lies in `chartIdeal l` there. -/
noncomputable def idealSheaf (l : ℕ) : IdealSheaf D :=
  IdealSheaf.ofMinimalOpens minOpen minIndex minOpen_minIndex_le fun i => chartIdeal l (minOpen i)

/-- **The ideal sheaves `idealSheaf l` form a fundamental system of ideals of definition over the
quasi-compact opens of the twisted double.** -/
theorem isFundamentalSystemOfIdealsOfDefinitionOn_isCompact :
    IsFundamentalSystemOfIdealsOfDefinitionOn (Set.range idealSheaf)
      fun V => IsCompact (V : Set D) :=
  IdealSheaf.isFundamentalSystemOfIdealsOfDefinitionOn_ofMinimalOpens minOpen minIndex
    minOpen_minIndex_le mem_minOpen_minIndex (fun l i => chartIdeal l (minOpen i))
    (fun l _ _ h => chartIdeal_map_le l h) (fun _ _ _ hl => chartIdeal_anti hl _)
    (fun l i => by
      obtain ⟨b, hb⟩ := exists_minOpen_le_U i
      exact isIdealOfDefinition_chartIdeal l hb (isCompact_minOpen i))
    fun _ _ hN => exists_chartIdeal_subset hN

/-- **The twisted double has a fundamental system of ideals of definition** over its affine
formal opens, although it is not quasi-separated. -/
theorem exists_isFundamentalSystemOfIdealsOfDefinitionOn :
    ∃ 𝒮 : Set (IdealSheaf D),
      IsFundamentalSystemOfIdealsOfDefinitionOn 𝒮 (IsAffineFormalOpen D) :=
  ⟨_, isFundamentalSystemOfIdealsOfDefinitionOn_isCompact.mono
    fun _ hV => isCompact_of_isAffineFormalOpen hV⟩

end AlgebraicGeometry.TwistedDouble

end
