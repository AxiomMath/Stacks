module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Characterization
public import StacksFrontier.AlgebraicGeometry.Topologies.FpqcCounterexample.DoubledOriginSource

/-!
# A flat surjection which is not an fpqc covering

The singleton family consisting of the morphism of
`AlgebraicGeometry.DoubledOriginSource` is not an fpqc covering, even though it is flat and
surjective and every point of the target has a neighbourhood which is the image of a
quasi-compact open of the source.

What fails is the condition that *every* affine open of the target be covered by the images of
quasi-compact opens: the second chart is an affine open, and no quasi-compact open of the source
has image exactly the second chart. Indeed such an open would meet the first summand in a
quasi-compact open, hence in finitely many of the basic opens `D(tᵢ)`, so some coordinate `tⱼ`
would be invertible on all of it; the point of the second chart where `tⱼ = 1` and the other
coordinates in that finite set vanish is then in the image, and it can come neither from the
first summand (its two chart images differ there) nor from the local scheme (whose image consists
of generalisations of the origin, and `tⱼ - 1` does not vanish at the origin).

The pointwise condition holds for a trivial reason: the source is quasi-compact, so the whole
source is a quasi-compact open whose image is everything.

## Main results

* `AlgebraicGeometry.DoubledOriginSource.map_image_ne_range_secondChart`: no quasi-compact open
  of the source has image the second chart.
* `AlgebraicGeometry.DoubledOriginSource.exists_isCompact_opens_image_mem_nhds`: the pointwise
  quasi-compact-neighbourhood condition.
* `AlgebraicGeometry.DoubledOriginSource.singleton_map_notMem_fpqcPrecoverage`: the singleton
  family is not an fpqc covering.

## Implementation notes

Quasi-compactness of an open is compactness of its underlying set, an image is a neighbourhood
when it lies in the neighbourhood filter, and being an fpqc covering is membership of the
presieve in `AlgebraicGeometry.Scheme.fpqcPrecoverage`. The second chart is presented as the
range of its canonical open immersion.

`range_glueData_overlap`, `chart_range_eq` and `overlap_range_eq` restate for the present use
the three facts about images of a gluing datum that
`StacksFrontier/AlgebraicGeometry/Scheme/Separation/DoubledOrigin.lean` proves privately.

## References

* [Stacks Project, Tag 0H7E](https://stacks.math.columbia.edu/tag/0H7E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The two chart images of a doubled-origin scheme meet in the image of the punctured affine
space. -/
private lemma chart_ranges_intersection {k : Type u} [Field k]
    (D : DoubledOriginData k) :
    Set.range (D.chart 0).base ∩ Set.range (D.chart 1).base =
      Set.range ((puncturedInfiniteAffineSpace k).ι ≫ D.chart 0).base := by
  rw [chart_range_eq D 0, chart_range_eq D 1,
    ← range_glueData_overlap D.glueData (D.indexEquiv 0) (D.indexEquiv 1),
    ← overlap_range_eq D]

/-- The two chart inclusions of a doubled-origin scheme agree away from the origin. -/
private theorem charts_agree_at_punctured {k : Type u} [Field k]
    (D : DoubledOriginData k) (x : infiniteAffineSpace k)
    (hx : x ∈ puncturedInfiniteAffineSpace k) :
    D.chart 0 x = D.chart 1 x := by
  let i := D.indexEquiv 0
  let j := D.indexEquiv 1
  let z : (puncturedInfiniteAffineSpace k).toScheme := ⟨x, hx⟩
  let e01 := D.overlapIso 0 1
  let e10 := D.overlapIso 1 0
  let x0 := (D.chartIso 0).inv.base x
  let x1 := (D.chartIso 1).inv.base x
  have hswap : (doubledOriginOverlapSwap k 0 1).base z = z := by
    classical
    unfold doubledOriginOverlapSwap
    have hne : (0 : Fin 2) ≠ 1 := by decide
    simp only [dite_eq_right hne]
    have hV : doubledOriginOverlap k 0 1 = doubledOriginOverlap k 1 0 := by
      simp [doubledOriginOverlap]
    cases hV
    rfl
  have htrans := congrArg (fun f => f.base z) (D.transition 0 1)
  have htrans' : (D.glueData.t i j).base (e01.hom.base z) = e10.hom.base z := by
    have ht : e10.inv ((D.glueData.t i j) (e01.hom z)) = z := by
      change e10.inv ((D.glueData.t i j) (e01.hom z)) =
        (doubledOriginOverlapSwap k 0 1) z at htrans
      rwa [hswap] at htrans
    calc
      (D.glueData.t i j) (e01.hom z) =
          e10.hom (e10.inv ((D.glueData.t i j) (e01.hom z))) := by simp
      _ = e10.hom z := congrArg e10.hom ht
  have hf : ∀ (a b : Fin 2) (w : doubledOriginOverlap k a b) (y : infiniteAffineSpace k),
      (doubledOriginOverlapι k a b).base w = y →
      (D.glueData.f (D.indexEquiv a) (D.indexEquiv b)).base ((D.overlapIso a b).hom.base w) =
        (D.chartIso a).inv.base y := by
    intro a b w y hy
    apply (D.chartIso a).hom.isOpenEmbedding.injective
    simpa [← hy] using congrArg (fun f => f.base w) (D.overlap_f a b)
  have hfirst' := hf 0 1 z x rfl
  have hsecond' := hf 1 0 z x rfl
  apply (D.glueData.ι_eq_iff i j x0 x1).2
  change ∃ w : (D.glueData.V (i, j)).carrier,
      (D.glueData.f i j) w = x0 ∧
        (D.glueData.t i j ≫ D.glueData.f j i) w = x1
  refine ⟨e01.hom.base z, hfirst', ?_⟩
  rw [Scheme.Hom.comp_apply, htrans', hsecond']

namespace DoubledOriginSource

/-- The basic open of the `i`-th coordinate in infinite-dimensional affine space. -/
private def coordinateBasicOpen {k : Type u} [Field k] (i : ℕ) :
    (infiniteAffineSpace k).Opens :=
  (infiniteAffineSpace k).basicOpen
    ((Scheme.ΓSpecIso (.of (MvPolynomial ℕ k))).inv (MvPolynomial.X i))

/-- The first chart of the target is an open immersion. -/
private instance (S : DoubledOriginSource.{u}) : IsOpenImmersion S.firstChart :=
  inferInstanceAs (IsOpenImmersion (S.gluing.chart 0))

/-- The second chart of the target is an open immersion. -/
private instance (S : DoubledOriginSource.{u}) : IsOpenImmersion S.secondChart :=
  inferInstanceAs (IsOpenImmersion (S.gluing.chart 1))

/-- Every point of the source comes from the affine summand or from the local scheme. -/
private lemma eq_inl_or_eq_inr (S : DoubledOriginSource.{u}) (y : S.source) :
    (∃ x, (coprod.inl : S.affine ⟶ S.source) x = y) ∨
      ∃ b, (coprod.inr : Spec (.of (S.affine.presheaf.stalk S.origin)) ⟶ S.source) b = y := by
  let e := coprodMk S.affine (Spec (.of (S.affine.presheaf.stalk S.origin)))
  have h := e.apply_symm_apply y
  cases hsum : e.symm y with
  | inl x =>
      rw [hsum] at h
      exact .inl ⟨x, by simpa [e] using h⟩
  | inr b =>
      rw [hsum] at h
      exact .inr ⟨b, by simpa [e] using h⟩

/-- On the affine summand, the canonical map is the first chart. -/
private lemma map_inl_apply (S : DoubledOriginSource.{u}) (x : S.affine) :
    S.map ((coprod.inl : S.affine ⟶ S.source) x) = S.firstChart x := by
  have hcomp : (coprod.inl : S.affine ⟶ S.source) ≫ S.map = S.firstChart := by
    rw [DoubledOriginSource.map, coprod.inl_desc]
  simpa [Scheme.Hom.comp_apply] using congrArg (fun f => f x) hcomp

/-- On the local scheme, the canonical map is the second chart after the canonical map to the
affine space. -/
private lemma map_inr_apply (S : DoubledOriginSource.{u})
    (b : Spec (.of (S.affine.presheaf.stalk S.origin))) :
    S.map ((coprod.inr : Spec (.of (S.affine.presheaf.stalk S.origin)) ⟶ S.source) b) =
      S.secondChart ((S.affine.fromSpecStalk S.origin) b) := by
  have hcomp : (coprod.inr : Spec (.of (S.affine.presheaf.stalk S.origin)) ⟶ S.source) ≫ S.map =
      S.affine.fromSpecStalk S.origin ≫ S.secondChart := by
    rw [DoubledOriginSource.map, coprod.inr_desc]
  simpa [Scheme.Hom.comp_apply] using congrArg (fun f => f b) hcomp

private lemma mem_coordinateBasicOpen_iff {k : Type u} [Field k] (p : infiniteAffineSpace k)
    (i : ℕ) : p ∈ coordinateBasicOpen (k := k) i ↔ MvPolynomial.X i ∉ p.asIdeal := by
  change p ∈ (infiniteAffineSpace k).basicOpen
    ((Scheme.ΓSpecIso (.of (MvPolynomial ℕ k))).inv (MvPolynomial.X i)) ↔ _
  rw [basicOpen_eq_of_affine]
  exact PrimeSpectrum.mem_basicOpen _ _

/-- A point of the affine space whose two chart images meet lies in the punctured affine
space. -/
private lemma mem_punctured_of_firstChart_mem_range_secondChart (S : DoubledOriginSource.{u})
    (x : S.affine) (hx : S.firstChart.base x ∈ Set.range S.secondChart.base) :
    x ∈ puncturedInfiniteAffineSpace S.k := by
  have hmem : S.firstChart.base x ∈
      Set.range S.firstChart.base ∩ Set.range S.secondChart.base :=
    ⟨⟨x, rfl⟩, hx⟩
  have hmem' : S.firstChart.base x ∈
      Set.range (S.gluing.chart 0).base ∩ Set.range (S.gluing.chart 1).base := by
    simpa [DoubledOriginSource.firstChart, DoubledOriginSource.secondChart] using hmem
  rw [chart_ranges_intersection S.gluing] at hmem'
  obtain ⟨z, hz⟩ := hmem'
  have hz' : (puncturedInfiniteAffineSpace S.k).ι z = x := by
    apply S.firstChart.isOpenEmbedding.injective
    change ((puncturedInfiniteAffineSpace S.k).ι ≫ S.firstChart) z =
      S.firstChart x at hz
    simpa [Scheme.Hom.comp_apply] using hz
  rw [← hz']
  exact z.2

private lemma exists_mem_coordinateBasicOpen (S : DoubledOriginSource.{u}) (x : S.affine)
    (hx : S.firstChart.base x ∈ Set.range S.secondChart.base) :
    ∃ i, x ∈ coordinateBasicOpen (k := S.k) i := by
  have hp := mem_punctured_of_firstChart_mem_range_secondChart S x hx
  change x ∈ ⨆ i, coordinateBasicOpen (k := S.k) i at hp
  exact TopologicalSpace.Opens.mem_iSup.mp hp

private lemma inl_mem_range_coordinateBasicOpen_iff (S : DoubledOriginSource.{u}) (i : ℕ)
    (x : S.affine) :
    (coprod.inl : S.affine ⟶ S.source).base x ∈
        Set.range (((coordinateBasicOpen (k := S.k) i).ι ≫
          (coprod.inl : S.affine ⟶ S.source)).base) ↔
      x ∈ coordinateBasicOpen (k := S.k) i := by
  constructor
  · rintro ⟨w, hw⟩
    have hwcoord : ((coordinateBasicOpen (k := S.k) i).ι).base w = x := by
      apply (coprod.inl : S.affine ⟶ S.source).isOpenEmbedding.injective
      simpa [Scheme.Hom.comp_apply] using hw
    rw [← hwcoord]
    exact w.2
  · intro hx
    obtain ⟨w, hw⟩ : x ∈ Set.range ((coordinateBasicOpen (k := S.k) i).ι).base := by
      rw [Scheme.Opens.range_ι]
      exact hx
    exact ⟨w, by rw [Scheme.Hom.comp_apply, hw]⟩

/-- A point of the affine space whose second-chart image comes from the local scheme is a
generalisation of the origin, so `tⱼ - 1` does not vanish at it. -/
private lemma X_sub_one_notMem_of_map_inr_eq (S : DoubledOriginSource.{u})
    (b : Spec (.of (S.affine.presheaf.stalk S.origin))) (p : S.affine)
    (h : S.map.base ((coprod.inr : Spec (.of (S.affine.presheaf.stalk S.origin)) ⟶ S.source) b) =
      S.secondChart.base p) (j : ℕ) :
    MvPolynomial.X j - 1 ∉ p.asIdeal := by
  intro hmem
  have hb : (S.affine.fromSpecStalk S.origin) b = p := by
    apply S.secondChart.isOpenEmbedding.injective
    exact (map_inr_apply S b).symm.trans h
  have hspec : p ⤳ S.origin := by
    have hrange : (S.affine.fromSpecStalk S.origin).base b ∈
        Set.range (S.affine.fromSpecStalk S.origin).base := ⟨b, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hrange
    have hspec' : (S.affine.fromSpecStalk S.origin).base b ⤳ S.origin := hrange
    rwa [hb] at hspec'
  have hle : p.asIdeal ≤ S.origin.asIdeal :=
    (PrimeSpectrum.asIdeal_le_asIdeal p S.origin).mpr
      ((PrimeSpectrum.le_iff_specializes p S.origin).mpr hspec)
  have hnotOrigin : MvPolynomial.X j - 1 ∉ S.origin.asIdeal := by
    change MvPolynomial.X j - 1 ∉
      (PrimeSpectrum.comap (MvPolynomial.eval 0) (⊤ : PrimeSpectrum S.k)).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    simp
  exact hnotOrigin (hle hmem)

/-- No quasi-compact open of the source maps onto the second affine chart of the
infinite-dimensional doubled-origin scheme. -/
@[stacks 0H7E "no_quasicompact_open"]
public theorem map_image_ne_range_secondChart (S : DoubledOriginSource)
    (W : S.source.Opens) (hW : IsCompact (W : Set S.source)) :
    S.map.base '' (W : Set S.source) ≠ Set.range S.secondChart.base := by
  classical
  intro hEq
  let first : S.affine ⟶ S.source := coprod.inl
  let second : Spec (.of (S.affine.presheaf.stalk S.origin)) ⟶ S.source := coprod.inr
  let B : Option ℕ → Set S.source := fun
    | none => Set.range second.base
    | some i => Set.range (((coordinateBasicOpen (k := S.k) i).ι ≫ first).base)
  have hBopen : ∀ a, IsOpen (B a) := by
    rintro (_ | _) <;> exact AlgebraicGeometry.IsOpenImmersion.isOpen_range _
  have hBcover : (W : Set S.source) ⊆ ⋃ a, B a := by
    intro y hy
    obtain ⟨x, rfl⟩ | ⟨b, rfl⟩ := eq_inl_or_eq_inr S y
    · obtain ⟨i, hi⟩ := exists_mem_coordinateBasicOpen S x (by
        rw [← hEq]
        exact ⟨_, hy, map_inl_apply S x⟩)
      exact Set.mem_iUnion.mpr ⟨some i, (inl_mem_range_coordinateBasicOpen_iff S i x).2 hi⟩
    · exact Set.mem_iUnion.mpr ⟨none, ⟨b, rfl⟩⟩
  obtain ⟨s, hs⟩ := hW.elim_finite_subcover B hBopen hBcover
  let t : Finset ℕ := s.image (fun a => a.getD 0)
  obtain ⟨j, -, hj⟩ := Set.infinite_univ.exists_notMem_finset t
  let ev : MvPolynomial ℕ S.k →+* S.k :=
    MvPolynomial.eval₂Hom (RingHom.id S.k) (fun i => if i ∈ t then 0 else 1)
  let p : S.affine := ⟨RingHom.ker ev, RingHom.ker_isPrime ev⟩
  have hpXj : MvPolynomial.X j ∉ p.asIdeal := fun hm => by
    simpa [ev, hj] using (RingHom.mem_ker.mp hm : ev (MvPolynomial.X j) = 0)
  have hpPunctured : p ∈ puncturedInfiniteAffineSpace S.k := by
    rw [puncturedInfiniteAffineSpace]
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, (mem_coordinateBasicOpen_iff p j).2 hpXj⟩
  obtain ⟨y, hyW, hyq⟩ : S.secondChart.base p ∈ S.map.base '' (W : Set S.source) :=
    hEq ▸ ⟨p, rfl⟩
  obtain ⟨x, rfl⟩ | ⟨b, rfl⟩ := eq_inl_or_eq_inr S y
  · have hxp : x = p := S.firstChart.isOpenEmbedding.injective <|
      (map_inl_apply S x).symm.trans <|
        hyq.trans (charts_agree_at_punctured S.gluing p hpPunctured).symm
    obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.mp (hs hyW)
    cases a with
    | none =>
        obtain ⟨b, hb⟩ := hya
        exact AlgebraicGeometry.inl_ne_inr S.affine
          (Spec (.of (S.affine.presheaf.stalk S.origin))) x b hb.symm
    | some i =>
        have hiT : i ∈ t := Finset.mem_image.mpr ⟨some i, ha, rfl⟩
        apply (mem_coordinateBasicOpen_iff p i).1 (by
          rw [← hxp]
          exact (inl_mem_range_coordinateBasicOpen_iff S i x).1 hya)
        change MvPolynomial.X i ∈ RingHom.ker ev
        exact RingHom.mem_ker.mpr (by simp [ev, hiT])
  · refine X_sub_one_notMem_of_map_inr_eq S b p hyq j ?_
    change MvPolynomial.X j - 1 ∈ RingHom.ker ev
    exact RingHom.mem_ker.mpr (by simp [ev, hj])

/-- Every point of the doubled-origin scheme has a neighbourhood that is the image of a
quasi-compact open of the source of the canonical map. -/
@[stacks 0H7E "pointwise_condition"]
public theorem exists_isCompact_opens_image_mem_nhds
    (S : DoubledOriginSource.{u}) (x : S.target) :
    ∃ V : S.source.Opens,
      IsCompact (V : Set S.source) ∧ S.map '' (V : Set S.source) ∈ nhds x := by
  have : CompactSpace S.source := (coprodMk S.affine
    (Spec (.of (S.affine.presheaf.stalk S.origin)))).compactSpace
  exact ⟨⊤, by simpa using (isCompact_univ : IsCompact (Set.univ : Set S.source)),
    by simp [Set.image_univ_of_surjective (surjective_map S).surj]⟩

/-- The map from the affine chart and the local scheme at the origin to the infinite-dimensional
doubled-origin scheme does not form an fpqc covering. -/
@[stacks 0H7E "not_fpqc"]
public theorem singleton_map_notMem_fpqcPrecoverage (S : DoubledOriginSource.{u}) :
    Presieve.singleton S.map ∉ Scheme.fpqcPrecoverage S.target := by
  intro hcover
  rw [← Presieve.ofArrows_pUnit.{u}] at hcover
  obtain ⟨V, hV, _, hU⟩ :=
    ((mem_fpqcPrecoverage_iff_affine_finite_support.{u, u}
      (T := S.target) (X := fun _ : PUnit.{u + 1} => S.source)
      (f := fun _ : PUnit.{u + 1} => S.map)).mp hcover).2
      S.secondChart.opensRange
        (@isAffineOpen_opensRange _ _ inferInstance S.secondChart inferInstance)
  exact (map_image_ne_range_secondChart S (V PUnit.unit) (hV PUnit.unit))
    (by simpa [Set.iUnion, iSup_unique] using hU)

end DoubledOriginSource

end AlgebraicGeometry

end
