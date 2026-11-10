module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.InfiniteProduct

/-!
# A finite-type morphism with finite fibres which is not quasi-separated

Let `A = ∏ n : ℕ, 𝔽₂` and `S = Spec A`. Every element of `A` is idempotent, so every prime of
`A` is maximal with residue field `𝔽₂`, and `S` is quasi-compact and totally disconnected. The
coordinate projections `A ⟶ 𝔽₂` give open points of `S`, and since `S` is quasi-compact not all
of its points can be open; fix a closed point `p` of `S` which is not open. Gluing two copies
of `S` along `S \ {p}` gives a scheme `Y` — namely `S` with `p` doubled — and the canonical
morphism `f : Y ⟶ S` is quasi-compact, locally of finite type and has finite fibres, but is not
quasi-separated: the inverse image of any open neighbourhood of `p` fails to be affine. Since
`p` is the generic point of an irreducible component of `S`, this shows that conditions (3) and
(4) of Stacks Tag 02NW genuinely need quasi-separatedness.

## Main definitions

* `AlgebraicGeometry.DoubledPoint` records a two-chart gluing of the spectrum of `∏ n : ℕ, 𝔽₂`
  away from a closed, non-open point, together with the canonical morphism back to it.
* `AlgebraicGeometry.doubledPointPuncture`, `AlgebraicGeometry.doubledPointPreGlueData`,
  `AlgebraicGeometry.doubledPointGlueData`, `AlgebraicGeometry.doubledPointChart` and
  `AlgebraicGeometry.doubledPointProjection` are the gluing datum, its two charts and the
  canonical morphism back to the spectrum.
* `AlgebraicGeometry.doubledPoint` constructs such data.

## Main results

* `AlgebraicGeometry.coordinatePoint_injective`: distinct coordinate projections give distinct
  points of the spectrum of a product of copies of a field.
* `AlgebraicGeometry.doubledPoint_genericPoint`: the doubled point is the generic point of an
  irreducible component.
* `AlgebraicGeometry.doubledPoint_quasiCompact`,
  `AlgebraicGeometry.doubledPoint_locallyOfFiniteType` and
  `AlgebraicGeometry.doubledPoint_finiteFibres`: the positive properties of the morphism.
* `AlgebraicGeometry.doubledPoint_noAffinePreimage`,
  `AlgebraicGeometry.doubledPoint_notQuasiSeparated`,
  `AlgebraicGeometry.doubledPoint_noAffineOpenContainingFibre` and
  `AlgebraicGeometry.doubledPoint_noFiniteRestriction`: the failure of quasi-separatedness and
  of conditions (3) and (4) of Stacks Tag 02NW.

## References

* [Stacks Project, Tag 02NW](https://stacks.math.columbia.edu/tag/02NW)
* [Stacks Project, Tag 02Z8](https://stacks.math.columbia.edu/tag/02Z8)
* [Stacks Project, Tag 03HY](https://stacks.math.columbia.edu/tag/03HY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology
open AlgebraicGeometry.Space.InfiniteProduct

namespace AlgebraicGeometry

add_to_stacks 03HY "quasi-compactness of the affine spectrum" PrimeSpectrum.compactSpace
add_to_stacks 03HY "idempotence of the product ring"
  AlgebraicGeometry.Space.InfiniteProduct.pow_card_eq_self
add_to_stacks 03HY "closed points of the spectrum"
  AlgebraicGeometry.Space.InfiniteProduct.isClosed_singleton
add_to_stacks 03HY "residue fields"
  AlgebraicGeometry.Space.InfiniteProduct.nonempty_algEquiv_residueField
add_to_stacks 03HY "open coordinate points"
  AlgebraicGeometry.Space.InfiniteProduct.isOpen_singleton_iff_coordinate
add_to_stacks 03HY "existence of a non-open point"
  AlgebraicGeometry.Space.InfiniteProduct.not_discreteTopology
add_to_stacks 03HY "total disconnectedness"
  AlgebraicGeometry.Space.InfiniteProduct.instTotallyDisconnectedSpace

/-- Distinct coordinate projections induce distinct points of the spectrum of a countable product
of copies of a field. -/
@[stacks 03HY "distinctness of coordinate points"]
theorem coordinatePoint_injective (k : Type*) [Field k] :
    Function.Injective fun n : ℕ ↦ (coordinate k n).base (default : base k) := by
  intro n m h
  by_contra hnm
  let a : productRing k := fun i ↦ if i = n then 1 else 0
  change PrimeSpectrum.comap (Pi.evalRingHom (fun _ : ℕ ↦ k) n) (default : base k) =
    PrimeSpectrum.comap (Pi.evalRingHom (fun _ : ℕ ↦ k) m) (default : base k) at h
  have hp := congrArg (fun x : PrimeSpectrum (productRing k) ↦ a ∈ x.asIdeal) h
  change (a ∈ Ideal.comap (Pi.evalRingHom (fun _ : ℕ ↦ k) n) (default : base k).asIdeal) =
    (a ∈ Ideal.comap (Pi.evalRingHom (fun _ : ℕ ↦ k) m) (default : base k).asIdeal) at hp
  rw [Ideal.mem_comap, Ideal.mem_comap] at hp
  simp [a, Ne.symm hnm] at hp

section Gluing

variable (p : space (ZMod 2))

/-- The complement of a closed point of the spectrum of `∏ n : ℕ, 𝔽₂`, as an open subscheme. -/
@[implicit_reducible]
noncomputable def doubledPointPuncture : (space (ZMod 2)).Opens :=
  ⟨{p}ᶜ, (isClosed_singleton (ZMod 2) p).isOpen_compl⟩

/-- The gluing datum for two copies of the spectrum of `∏ n : ℕ, 𝔽₂`, identified away from a
point. -/
@[implicit_reducible]
noncomputable def doubledPointPreGlueData : CategoryTheory.GlueData' Scheme where
  J := Fin 2
  U _ := space (ZMod 2)
  V _ _ _ := (doubledPointPuncture p).toScheme
  f _ _ _ := (doubledPointPuncture p).ι
  f_mono := by intros; infer_instance
  f_hasPullback := by intros; infer_instance
  t _ _ _ := 𝟙 _
  t' i j l hij hil hjl := by
    exfalso
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all
  t_fac i j l hij hil hjl := by
    exfalso
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all
  t_inv := by intros; simp
  cocycle i j l hij hil hjl := by
    exfalso
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all

/-- The gluing datum of schemes obtained from `doubledPointPreGlueData`. -/
@[implicit_reducible]
noncomputable def doubledPointGlueData : Scheme.GlueData where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (doubledPointPreGlueData p)
  f_open i j := by
    dsimp [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
      doubledPointPreGlueData]
    split_ifs <;> infer_instance

/-- The `i`-th chart of the glued scheme. -/
@[implicit_reducible]
noncomputable def doubledPointChart (i : Fin 2) :
    space (ZMod 2) ⟶ (doubledPointGlueData p).glued :=
  (doubledPointGlueData p).ι i

/-- The canonical morphism from the glued scheme back to the spectrum, the identity on each
chart. -/
@[implicit_reducible]
noncomputable def doubledPointProjection :
    (doubledPointGlueData p).glued ⟶ space (ZMod 2) := by
  classical
  have hJ : Fintype (doubledPointGlueData p).toGlueData.J := by
    change Fintype (Fin 2); infer_instance
  have hJd : DecidableEq (doubledPointGlueData p).toGlueData.J := by
    change DecidableEq (Fin 2); infer_instance
  have hcompat : ∀ a : (doubledPointGlueData p).toGlueData.J ×
      (doubledPointGlueData p).toGlueData.J,
      (doubledPointGlueData p).toGlueData.diagram.fst a ≫ (fun _ ↦ 𝟙 _) _ =
        (doubledPointGlueData p).toGlueData.diagram.snd a ≫ (fun _ ↦ 𝟙 _) _ := by
    rintro ⟨i, j⟩
    change Fin 2 at i
    change Fin 2 at j
    change (doubledPointGlueData p).f i j ≫ 𝟙 (space (ZMod 2)) =
      (doubledPointGlueData p).t i j ≫ (doubledPointGlueData p).f j i ≫ 𝟙 (space (ZMod 2))
    fin_cases i <;> fin_cases j <;>
      simp [doubledPointGlueData, doubledPointPreGlueData,
        CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
  exact CategoryTheory.Limits.Multicoequalizer.desc (doubledPointGlueData p).toGlueData.diagram
    (space (ZMod 2)) (fun _ ↦ 𝟙 _) hcompat

/-- Each chart followed by the canonical projection is the identity of the spectrum. -/
theorem doubledPointChart_comp_projection (i : Fin 2) :
    doubledPointChart p i ≫ doubledPointProjection p = 𝟙 (space (ZMod 2)) := by
  have hJ : Fintype (doubledPointGlueData p).toGlueData.J := by
    change Fintype (Fin 2); infer_instance
  have hJd : DecidableEq (doubledPointGlueData p).toGlueData.J := by
    change DecidableEq (Fin 2); infer_instance
  change CategoryTheory.Limits.Multicoequalizer.π
      (doubledPointGlueData p).toGlueData.diagram i ≫
    CategoryTheory.Limits.Multicoequalizer.desc (doubledPointGlueData p).toGlueData.diagram
      (space (ZMod 2)) (fun _ ↦ 𝟙 (space (ZMod 2))) _ = 𝟙 (space (ZMod 2))
  exact CategoryTheory.Limits.Multicoequalizer.π_desc
    (doubledPointGlueData p).toGlueData.diagram (space (ZMod 2))
    (fun _ ↦ 𝟙 (space (ZMod 2))) _ i

/-- For distinct indices `i ≠ j`, the image of the overlap inclusion `f i j` is the complement of
the doubled point. -/
theorem doubledPointOverlapRange (i j : (doubledPointGlueData p).toGlueData.J)
    (hij : i ≠ j) :
    Set.range ((doubledPointGlueData p).f i j).base =
      (doubledPointPuncture p : Set (space (ZMod 2))) := by
  rw [← Scheme.Hom.coe_opensRange]
  simp only [doubledPointGlueData, doubledPointPreGlueData,
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
  split_ifs with h
  · exact absurd h hij
  · rw [Scheme.Hom.opensRange_comp_of_isIso]
    exact congrArg (fun U : Scheme.Opens (space (ZMod 2)) ↦ (U : Set (space (ZMod 2))))
      (Scheme.Opens.opensRange_ι _)

end Gluing

/-- Data exhibiting the doubling of a closed, non-open point of the spectrum of `∏ n : ℕ, 𝔽₂`.
The images of the two charts intersect exactly away from the selected point. -/
structure DoubledPoint where
  /-- The point that is doubled. -/
  point : space (ZMod 2)
  /-- The doubled point is closed. -/
  closed_point : IsClosed ({point} : Set (space (ZMod 2)))
  /-- The doubled point is not open. -/
  not_open_point : ¬ IsOpen ({point} : Set (space (ZMod 2)))
  /-- The scheme obtained by gluing the two charts. -/
  source : Scheme
  /-- The canonical morphism to the original affine scheme. -/
  projection : source ⟶ space (ZMod 2)
  /-- The two copies of the affine spectrum inside the gluing. -/
  chart : Fin 2 → (space (ZMod 2) ⟶ source)
  /-- Each chart is an open immersion. -/
  chart_open : ∀ i, IsOpenImmersion (chart i)
  /-- The two charts cover the glued scheme. -/
  chart_cover : Set.range (chart 0).base ∪ Set.range (chart 1).base = Set.univ
  /-- The canonical morphism restricts to the identity on each chart. -/
  chart_projection : ∀ i, chart i ≫ projection = 𝟙 (space (ZMod 2))
  /-- The two charts overlap exactly away from the doubled point. -/
  chart_overlap : (chart 0).base ⁻¹' Set.range (chart 1).base =
    ({point}ᶜ : Set (space (ZMod 2)))

/-- The spectrum of `∏ n : ℕ, 𝔽₂` with a closed, non-open point doubled, together with its
canonical projection and chart identifications. -/
@[stacks 03HY "the doubled-point construction"]
noncomputable def doubledPoint : DoubledPoint := by
  let hex := exists_noncoordinate_point (ZMod 2)
  let p := Classical.choose hex
  have hp := Classical.choose_spec hex
  have hpOpen : ¬ IsOpen ({p} : Set (space (ZMod 2))) := by
    intro h
    obtain ⟨n, hn⟩ := (isOpen_singleton_iff_coordinate (ZMod 2) p).mp h
    exact hp n hn
  have hJ : Fintype (doubledPointGlueData p).toGlueData.J := by
    change Fintype (Fin 2); infer_instance
  have hJd : DecidableEq (doubledPointGlueData p).toGlueData.J := by
    change DecidableEq (Fin 2); infer_instance
  let i0 : (doubledPointGlueData p).toGlueData.J := (0 : Fin 2)
  let i1 : (doubledPointGlueData p).toGlueData.J := (1 : Fin 2)
  have h01 : i0 ≠ i1 := fun h ↦ absurd (show (0 : Fin 2) = 1 from h) (by decide)
  have h10 : i1 ≠ i0 := fun h ↦ absurd (show (1 : Fin 2) = 0 from h) (by decide)
  refine ⟨p, isClosed_singleton (ZMod 2) p, hpOpen, (doubledPointGlueData p).glued,
    doubledPointProjection p, doubledPointChart p,
    fun i ↦ (doubledPointGlueData p).ι_isOpenImmersion i, ?_,
    doubledPointChart_comp_projection p, ?_⟩
  · ext y
    refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
    obtain ⟨i, z, hz⟩ := (doubledPointGlueData p).ι_jointly_surjective y
    change Fin 2 at i
    fin_cases i
    · exact Set.mem_union_left _ ⟨z, hz⟩
    · exact Set.mem_union_right _ ⟨z, hz⟩
  · ext z
    change ((doubledPointChart p 0).base z ∈ Set.range (doubledPointChart p 1).base) ↔
      z ∈ ({p}ᶜ : Set (space (ZMod 2)))
    constructor
    · rintro ⟨w, hw⟩
      have hw' : (doubledPointGlueData p).ι i0 z = (doubledPointGlueData p).ι i1 w := hw.symm
      obtain ⟨v, hv0, -⟩ := ((doubledPointGlueData p).ι_eq_iff _ _ _ _).mp hw'
      have hzrange : z ∈ Set.range ((doubledPointGlueData p).f i0 i1).base := ⟨v, hv0⟩
      rwa [doubledPointOverlapRange p i0 i1 h01] at hzrange
    · intro hz
      obtain ⟨v₀, hv₀⟩ : z ∈ Set.range ((doubledPointGlueData p).f i1 i0).base := by
        rwa [doubledPointOverlapRange p i1 i0 h10]
      have hcompat : (doubledPointGlueData p).t i1 i0 ≫ (doubledPointGlueData p).f i0 i1 =
          (doubledPointGlueData p).f i1 i0 := by
        simp [doubledPointGlueData, doubledPointPreGlueData,
          CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', i0, i1]
      refine ⟨z, ((doubledPointGlueData p).ι_eq_iff _ _ _ _).mpr ⟨v₀, hv₀, ?_⟩⟩
      rwa [hcompat]

private theorem doubledPoint_projection_chart (i : Fin 2) (z : space (ZMod 2)) :
    doubledPoint.projection.base ((doubledPoint.chart i).base z) = z := by
  simpa [Scheme.Hom.comp_base, TopCat.coe_comp] using
    congrArg (fun f : space (ZMod 2) ⟶ space (ZMod 2) ↦ f.base z)
      (doubledPoint.chart_projection i)

private theorem doubledPoint_eq_of_chart_eq {i j : Fin 2} {z w : space (ZMod 2)}
    (h : (doubledPoint.chart i).base z = (doubledPoint.chart j).base w) : z = w := by
  rw [← doubledPoint_projection_chart i z, ← doubledPoint_projection_chart j w, h]

private theorem doubledPoint_mem_chartRange_iff (z : space (ZMod 2)) :
    (doubledPoint.chart 0).base z ∈ Set.range (doubledPoint.chart 1).base ↔
      z ∈ ({doubledPoint.point}ᶜ : Set (space (ZMod 2))) :=
  Set.ext_iff.mp doubledPoint.chart_overlap z

/-- Every point of the glued scheme lies in the image of one of the two charts. -/
private theorem doubledPoint_mem_chart_range_union (x : doubledPoint.source) :
    x ∈ Set.range (doubledPoint.chart 0).base ∪ Set.range (doubledPoint.chart 1).base :=
  Set.eq_univ_iff_forall.mp doubledPoint.chart_cover x

/-- The doubled point is the generic point of an irreducible component of the spectrum. -/
@[stacks 03HY "generic point of an irreducible component"]
theorem doubledPoint_genericPoint :
    doubledPoint.point ∈ genericPoints (space (ZMod 2)) := by
  change closure {doubledPoint.point} ∈ irreducibleComponents (space (ZMod 2))
  rw [doubledPoint.closed_point.closure_eq]
  refine ⟨isIrreducible_singleton, fun t ht hst y hy ↦ ?_⟩
  have hpt : doubledPoint.point ∈ t := hst (Set.mem_singleton _)
  exact (IsPreconnected.subsingleton ht.2.isPreconnected hpt hy).symm

/-- The canonical projection is quasi-compact. -/
@[stacks 03HY "quasi-compactness"]
theorem doubledPoint_quasiCompact : QuasiCompact doubledPoint.projection := by
  have : CompactSpace (space (ZMod 2)) := PrimeSpectrum.compactSpace
  have : CompactSpace doubledPoint.source := isCompact_univ_iff.mp <| by
    rw [← doubledPoint.chart_cover]
    exact (isCompact_range (doubledPoint.chart 0).continuous).union
      (isCompact_range (doubledPoint.chart 1).continuous)
  infer_instance

/-- The canonical projection is locally of finite type. -/
@[stacks 03HY "finite type"]
theorem doubledPoint_locallyOfFiniteType : LocallyOfFiniteType doubledPoint.projection := by
  let C : doubledPoint.source.OpenCover :=
    Scheme.Cover.mkOfCovers (Fin 2) (fun _ ↦ space (ZMod 2)) doubledPoint.chart
      (fun x ↦ by
        rcases doubledPoint_mem_chart_range_union x with ⟨z, hz⟩ | ⟨z, hz⟩
        · exact ⟨0, z, hz⟩
        · exact ⟨1, z, hz⟩)
      doubledPoint.chart_open
  have : IsZariskiLocalAtSource (@LocallyOfFiniteType) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) C]
  intro i
  change LocallyOfFiniteType (doubledPoint.chart i ≫ doubledPoint.projection)
  rw [doubledPoint.chart_projection i]
  infer_instance

/-- Every fibre of the canonical projection is finite. -/
@[stacks 03HY "finite fibres"]
theorem doubledPoint_finiteFibres (y : space (ZMod 2)) :
    (doubledPoint.projection ⁻¹' {y}).Finite := by
  classical
  let S : Set doubledPoint.source :=
    {(doubledPoint.chart 0).base y, (doubledPoint.chart 1).base y}
  refine (show S.Finite by simp [S]).subset fun x hx ↦ ?_
  rcases doubledPoint_mem_chart_range_union x with ⟨z, rfl⟩ | ⟨z, rfl⟩ <;>
    obtain rfl := (doubledPoint_projection_chart _ z).symm.trans hx <;> simp [S]

/-- The complement of a closed, non-open point of the spectrum of `∏ n : ℕ, 𝔽₂` is not
compact. -/
private theorem doubledPoint_puncture_not_isCompact (p : space (ZMod 2))
    (hclosed : IsClosed ({p} : Set (space (ZMod 2))))
    (hp : ¬ IsOpen ({p} : Set (space (ZMod 2)))) :
    ¬ IsCompact ({p}ᶜ : Set (space (ZMod 2))) := by
  intro hcompact
  let C : Set (Set (space (ZMod 2))) :=
    {s | IsClopen s ∧ s ⊆ ({p}ᶜ : Set (space (ZMod 2)))}
  have hcover : ({p}ᶜ : Set (space (ZMod 2))) ⊆ ⋃ s : C, (s : Set (space (ZMod 2))) := by
    intro q hq
    obtain ⟨s, hs, hqs, hsp⟩ :=
      (isTopologicalBasis_isClopen (ZMod 2)).exists_subset_of_mem_open hq hclosed.isOpen_compl
    exact Set.mem_iUnion.mpr ⟨⟨s, hs, hsp⟩, hqs⟩
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover (fun s : C ↦ s.1)
    (fun s ↦ s.2.1.isOpen) hcover
  have hFclosed : IsClosed (⋃ s ∈ t, (s.1 : Set (space (ZMod 2)))) :=
    isClosed_biUnion_finset fun s _ ↦ s.2.1.isClosed
  have hFsub : (⋃ s ∈ t, (s.1 : Set (space (ZMod 2)))) ⊆ ({p}ᶜ : Set (space (ZMod 2))) := by
    intro q hq
    obtain ⟨s, -, hqs⟩ := Set.mem_iUnion₂.mp hq
    exact s.2.2 hqs
  have hcompl : (⋃ s ∈ t, (s.1 : Set (space (ZMod 2))))ᶜ = ({p} : Set (space (ZMod 2))) := by
    ext q
    constructor
    · intro hq
      by_contra hqp
      exact hq (ht (by simpa using hqp))
    · rintro rfl hqF
      exact hFsub hqF rfl
  exact hp (hcompl ▸ hFclosed.isOpen_compl)

/-- The intersection of the images of a set under the two charts is the image under the first
chart of that set with the doubled point removed. -/
private theorem doubledPoint_image_chart_inter (s : Set (space (ZMod 2))) :
    (doubledPoint.chart 0).base '' s ∩ (doubledPoint.chart 1).base '' s =
      (doubledPoint.chart 0).base '' (s ∩ ({doubledPoint.point}ᶜ)) := by
  ext y
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, ⟨w, -, hwz⟩⟩
    exact ⟨z, ⟨hz, (doubledPoint_mem_chartRange_iff z).mp ⟨w, hwz⟩⟩, rfl⟩
  · rintro ⟨z, ⟨hz, hzp⟩, rfl⟩
    refine ⟨⟨z, hz, rfl⟩, z, hz, ?_⟩
    obtain ⟨w, hw⟩ := (doubledPoint_mem_chartRange_iff z).mpr hzp
    rwa [doubledPoint_eq_of_chart_eq hw] at hw

/-- The inverse image of every open neighbourhood of the doubled point is non-affine. -/
@[stacks 03HY "failure of conditions (3) and (4) of Tag 02NW"]
theorem doubledPoint_noAffinePreimage (U : (space (ZMod 2)).Opens)
    (hU : doubledPoint.point ∈ U) :
    ¬ IsAffine ((doubledPoint.projection ⁻¹ᵁ U).toScheme) := by
  intro hAffine
  classical
  obtain ⟨Vset, hVclopen, hpV, hVU⟩ :=
    (isTopologicalBasis_isClopen (ZMod 2)).exists_subset_of_mem_open hU U.2
  have hWaff : IsAffineOpen (doubledPoint.projection ⁻¹ᵁ U) := hAffine
  have hsub (i : Fin 2) : (doubledPoint.chart i).base '' Vset ⊆
      ((doubledPoint.projection ⁻¹ᵁ U : doubledPoint.source.Opens) :
        Set doubledPoint.source) := by
    rintro _ ⟨z, hz, rfl⟩
    change doubledPoint.projection.base ((doubledPoint.chart i).base z) ∈ U
    rw [doubledPoint_projection_chart]
    exact hVU hz
  have hopen (i : Fin 2) : IsOpen ((doubledPoint.chart i).base '' Vset) := by
    have : IsOpenImmersion (doubledPoint.chart i) := doubledPoint.chart_open i
    exact (doubledPoint.chart i).isOpenEmbedding.isOpenMap _ hVclopen.2
  have hcompact (i : Fin 2) : IsCompact ((doubledPoint.chart i).base '' Vset) :=
    hVclopen.1.isCompact.image (doubledPoint.chart i).continuous
  have hinter := hWaff.isQuasiSeparated _ _ (hsub 0) (hopen 0) (hcompact 0)
    (hsub 1) (hopen 1) (hcompact 1)
  rw [doubledPoint_image_chart_inter] at hinter
  have h0 : IsOpenImmersion (doubledPoint.chart 0) := doubledPoint.chart_open 0
  have hpunct : IsCompact (Vset ∩ ({doubledPoint.point}ᶜ : Set (space (ZMod 2)))) :=
    (doubledPoint.chart 0).isOpenEmbedding.isEmbedding.isCompact_iff.mpr hinter
  have hcompl : IsCompact (Vsetᶜ : Set (space (ZMod 2))) := hVclopen.2.isClosed_compl.isCompact
  have hall : ({doubledPoint.point}ᶜ : Set (space (ZMod 2))) =
      (Vset ∩ ({doubledPoint.point}ᶜ : Set (space (ZMod 2)))) ∪ Vsetᶜ := by
    ext x
    by_cases hx : x = doubledPoint.point <;> by_cases hxV : x ∈ Vset <;> simp_all
  exact doubledPoint_puncture_not_isCompact doubledPoint.point doubledPoint.closed_point
    doubledPoint.not_open_point (hall ▸ hpunct.union hcompl)

/-- The canonical projection is not quasi-separated. -/
@[stacks 03HY "failure of quasi-separatedness"]
theorem doubledPoint_notQuasiSeparated : ¬ QuasiSeparated doubledPoint.projection := by
  intro hqs
  have hsource : QuasiSeparatedSpace doubledPoint.source :=
    quasiSeparatedSpace_of_quasiSeparated doubledPoint.projection
  have h0 : IsOpenImmersion (doubledPoint.chart 0) := doubledPoint.chart_open 0
  have h1 : IsOpenImmersion (doubledPoint.chart 1) := doubledPoint.chart_open 1
  let U0 : doubledPoint.source.affineOpens :=
    ⟨(doubledPoint.chart 0).opensRange, isAffineOpen_opensRange (doubledPoint.chart 0)⟩
  let U1 : doubledPoint.source.affineOpens :=
    ⟨(doubledPoint.chart 1).opensRange, isAffineOpen_opensRange (doubledPoint.chart 1)⟩
  have hcompact' : IsCompact (Set.range (doubledPoint.chart 0).base ∩
      Set.range (doubledPoint.chart 1).base) := by
    simpa [U0, U1] using (quasiSeparatedSpace_iff_forall_affineOpens.mp hsource) U0 U1
  have himage : (doubledPoint.chart 0).base ''
      ({doubledPoint.point}ᶜ : Set (space (ZMod 2))) =
      Set.range (doubledPoint.chart 0).base ∩ Set.range (doubledPoint.chart 1).base := by
    rw [← doubledPoint.chart_overlap, Set.image_preimage_eq_inter_range]
    exact Set.inter_comm _ _
  exact doubledPoint_puncture_not_isCompact doubledPoint.point doubledPoint.closed_point
    doubledPoint.not_open_point
    ((doubledPoint.chart 0).isOpenEmbedding.isEmbedding.isCompact_iff.mpr (himage ▸ hcompact'))

/-- There is no affine open neighbourhood `V` of the doubled point together with an affine open
`U` over `V` containing the whole fibre over the doubled point such that the restriction
`U ⟶ V` of the canonical projection is finite. -/
@[stacks 03HY "failure of condition (3) of Tag 02NW"]
theorem doubledPoint_noAffineOpenContainingFibre :
    ¬ ∃ (V : (space (ZMod 2)).affineOpens) (U : doubledPoint.source.affineOpens)
      (hUV : U.1 ≤ doubledPoint.projection ⁻¹ᵁ V.1),
        doubledPoint.point ∈ V.1 ∧
        doubledPoint.projection ⁻¹' {doubledPoint.point} ⊆ U.1 ∧
        IsFinite (doubledPoint.projection.resLE V.1 U.1 hUV) := by
  rintro ⟨V, U, hUV, hpV, hfibre, hfinite⟩
  classical
  let N : (space (ZMod 2)).Opens :=
    ((doubledPoint.chart 0 ⁻¹ᵁ U.1) ⊓ (doubledPoint.chart 1 ⁻¹ᵁ U.1)) ⊓ V.1
  have hmemFibre (i : Fin 2) :
      (doubledPoint.chart i).base doubledPoint.point ∈ U.1 := by
    refine hfibre ?_
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact doubledPoint_projection_chart i doubledPoint.point
  have hNp : doubledPoint.point ∈ N := ⟨⟨hmemFibre 0, hmemFibre 1⟩, hpV⟩
  obtain ⟨-, ⟨W, hWaff, rfl⟩, hpW, hWN⟩ :=
    (space (ZMod 2)).isBasis_affineOpens.exists_subset_of_mem_open hNp N.2
  have hWV : W ≤ V.1 := hWN.trans inf_le_right
  have hWchart (i : Fin 2) : W ≤ doubledPoint.chart i ⁻¹ᵁ U.1 := by
    intro z hz
    have hzN := hWN hz
    fin_cases i
    · exact hzN.1.1
    · exact hzN.1.2
  have hpreimage_le : doubledPoint.projection ⁻¹ᵁ W ≤ U.1 := by
    intro y hy
    rcases doubledPoint_mem_chart_range_union y with ⟨z, rfl⟩ | ⟨z, rfl⟩ <;>
      exact hWchart _ (by simpa [Set.mem_preimage, doubledPoint_projection_chart] using hy)
  let Wv : V.1.toScheme.Opens := V.1.ι ⁻¹ᵁ W
  have hWimage : V.1.ι ''ᵁ Wv = W := by
    dsimp only [Wv]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    simp [hWV]
  have hWvAffine : IsAffineOpen Wv := by
    refine V.1.ι.isAffineOpen_iff_of_isOpenImmersion.mp ?_
    rwa [hWimage]
  have hQaff : IsAffineOpen (doubledPoint.projection.resLE V.1 U.1 hUV ⁻¹ᵁ Wv) :=
    hWvAffine.preimage _
  have hQimage : U.1.ι ''ᵁ (doubledPoint.projection.resLE V.1 U.1 hUV ⁻¹ᵁ Wv) =
      doubledPoint.projection ⁻¹ᵁ W := by
    rw [Scheme.Hom.resLE_preimage, hWimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hpreimage_le
  have hWpreAffine : IsAffineOpen (doubledPoint.projection ⁻¹ᵁ W) := by
    rw [← hQimage]
    exact U.1.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hQaff
  exact doubledPoint_noAffinePreimage W hpW hWpreAffine

/-- There is no affine open neighbourhood of the doubled point above which the canonical
projection is finite. -/
@[stacks 03HY "failure of condition (4) of Tag 02NW"]
theorem doubledPoint_noFiniteRestriction :
    ¬ ∃ V : (space (ZMod 2)).affineOpens, doubledPoint.point ∈ V.1 ∧
      IsFinite (doubledPoint.projection ∣_ V.1) := by
  rintro ⟨V, hp, hfinite⟩
  have hpre : IsAffineOpen ((doubledPoint.projection ∣_ V.1) ⁻¹ᵁ
      (⊤ : V.1.toScheme.Opens)) :=
    (isAffineOpen_top V.1.toScheme).preimage (doubledPoint.projection ∣_ V.1)
  have : IsAffine (⊤ : ((doubledPoint.projection ⁻¹ᵁ V.1).toScheme).Opens) := hpre
  exact doubledPoint_noAffinePreimage V.1 hp (IsAffine.of_isIso (Scheme.topIso _).inv)

end AlgebraicGeometry

end
