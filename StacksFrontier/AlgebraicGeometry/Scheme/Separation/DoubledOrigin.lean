module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Scheme.Separation.PuncturedAffineSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Infinite-dimensional affine space with a doubled origin

Over a field `k`, glue two copies of `Spec k[X₀, X₁, …]` along the complement of the origin, by
the identity. The resulting scheme is the standard example of a scheme whose structure morphism
to `Spec k` is **not** quasi-separated: the two charts are affine opens, but their intersection
inside the glued scheme is the punctured affine space, which is not quasi-compact.

The argument is the valuative one. Quasi-separatedness of a morphism `f` means that the diagonal
`Δ : X ⟶ X ×_S X` is quasi-compact. The two charts give an affine open of `X ×_S X`, namely the
intersection of the inverse images of the two chart ranges under the two projections; its inverse
image under `Δ` is exactly the intersection of the two chart ranges in `X`, which is the
punctured affine space embedded through the first chart. So quasi-separatedness would force the
punctured affine space to be quasi-compact, contradicting
`AlgebraicGeometry.puncturedSpectrum_not_isCompact`.

## Main definitions

* `AlgebraicGeometry.infiniteAffineSpace`: countably infinite-dimensional affine space.
* `AlgebraicGeometry.puncturedInfiniteAffineSpace`: the union of the basic opens of the
  coordinates, that is, the complement of the origin.
* `AlgebraicGeometry.doubledOriginGlueData`: the gluing data of the two charts.
* `AlgebraicGeometry.DoubledOriginData`: gluing data together with identifications exhibiting it
  as two copies of infinite-dimensional affine space glued by the identity off the origin.
* `AlgebraicGeometry.structureMorphism`: the morphism to `Spec k`, with its chart restrictions.

## Main results

* `AlgebraicGeometry.diagonal_preimage_mixedCharts`: the inverse image under the relative diagonal
  of the mixed product of the two charts is the punctured affine space inside the first chart.
* `AlgebraicGeometry.structureMorphism_not_quasiSeparated`: the structure morphism is not
  quasi-separated.

That the two charts are affine opens is `AlgebraicGeometry.isAffineOpen_opensRange` applied to the
chart inclusions, whose common source is a spectrum.

## Implementation notes

The results are stated for an arbitrary `DoubledOriginData`, so that they apply to the canonical
construction without depending on how the gluing was built; the fields of that structure identify
both charts and their overlaps with the prescribed affine space and punctured affine space, and
say that the maps from the overlap are the canonical inclusions and that the transition map is the
identity. Only the gluing assertions need a field; the base ring may be any commutative ring
except where the punctured space itself is used.

The two charts are indexed by `Fin 2`, while the underlying `Scheme.GlueData` indexes them by
`ULift (Fin 2)` for universe reasons; `DoubledOriginData.indexEquiv` mediates. The self-overlaps
are the whole affine space and the distinct overlaps are the punctured space, which is what
`doubledOriginOverlap` records.

`structureMorphism` is packaged with its restriction equations, so that the morphism and its
defining property are available together rather than as separate declarations that a caller must
match up.

## References

* [Stacks Project, Tag 01KL](https://stacks.math.columbia.edu/tag/01KL)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

add_to_stacks 01KL "affine_open_charts" AlgebraicGeometry.isAffineOpen_opensRange

namespace AlgebraicGeometry

universe u

/-- Countably infinite-dimensional affine space over `k`. -/
public abbrev infiniteAffineSpace (k : Type u) [CommRing k] : Scheme.{u} :=
  Spec (.of (MvPolynomial ℕ k))

/-- The complement of the origin in countably infinite-dimensional affine
space, written as the union of the basic opens defined by its coordinates. -/
public def puncturedInfiniteAffineSpace (k : Type u) [CommRing k] :
    (infiniteAffineSpace k).Opens :=
  ⨆ i : ℕ, (infiniteAffineSpace k).basicOpen
    ((Scheme.ΓSpecIso (.of (MvPolynomial ℕ k))).inv (MvPolynomial.X i))

/-- The standard overlap of charts `i` and `j`: the whole affine space for a
self-overlap, and the punctured affine space for two distinct charts. -/
public def doubledOriginOverlap (k : Type u) [CommRing k] (i j : Fin 2) : Scheme.{u} :=
  if i = j then infiniteAffineSpace k else (puncturedInfiniteAffineSpace k).toScheme

/-- The canonical inclusion of a standard overlap into either affine chart. -/
public def doubledOriginOverlapι (k : Type u) [CommRing k] (i j : Fin 2) :
    doubledOriginOverlap k i j ⟶ infiniteAffineSpace k := by
  classical
  by_cases h : i = j
  · simpa [doubledOriginOverlap, h] using 𝟙 (infiniteAffineSpace k)
  · simpa [doubledOriginOverlap, h] using (puncturedInfiniteAffineSpace k).ι

/-- Swapping the two chart indices does not change their standard overlap. -/
public def doubledOriginOverlapSwap (k : Type u) [CommRing k] (i j : Fin 2) :
    doubledOriginOverlap k i j ⟶ doubledOriginOverlap k j i := by
  classical
  by_cases h : i = j
  · subst j
    exact 𝟙 _
  · have h' : j ≠ i := Ne.symm h
    exact eqToHom (by simp [doubledOriginOverlap, h, h'])

/-- The gluing data of two copies of infinite-dimensional affine space, glued by the identity
along the complement of the origin. The cocycle conditions are vacuous because no three distinct
indices exist in `Fin 2`. -/
@[ega "IV 1.6.4" "special case", sga "3 VIB 5.6.4" "partial"]
public noncomputable def doubledOriginGlueData (k : Type u) [CommRing k] :
    Scheme.GlueData.{u} := by
  let D : CategoryTheory.GlueData' Scheme.{u} :=
    { J := ULift.{u} (Fin 2)
      U := fun _ ↦ infiniteAffineSpace k
      V := fun _ _ _ ↦ (puncturedInfiniteAffineSpace k).toScheme
      f := fun _ _ _ ↦ (puncturedInfiniteAffineSpace k).ι
      t := fun _ _ _ ↦ 𝟙 _
      t_inv := by simp
      t' := by
        rintro ⟨i⟩ ⟨j⟩ ⟨l⟩ hij hil hjl
        exact False.elim (by fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all)
      t_fac := by
        rintro ⟨i⟩ ⟨j⟩ ⟨l⟩ hij hil hjl
        exact False.elim (by fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all)
      cocycle := by
        rintro ⟨i⟩ ⟨j⟩ ⟨l⟩ hij hil hjl
        exact False.elim (by fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all) }
  exact
    { toGlueData := CategoryTheory.GlueData.ofGlueData' D
      f_open := by
        intro i j
        dsimp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
        split_ifs
        · infer_instance
        · dsimp [D]
          infer_instance }

/-- Gluing data together with identifications exhibiting it as two copies of
infinite-dimensional affine space glued by the identity off the origin. -/
public structure DoubledOriginData (k : Type u) [CommRing k] where
  /-- The underlying scheme gluing data. -/
  glueData : Scheme.GlueData.{u}
  /-- Identification of the two indices with the charts of the gluing data. -/
  indexEquiv : Fin 2 ≃ glueData.J
  /-- Identification of every chart with infinite-dimensional affine space. -/
  chartIso : ∀ i, glueData.U (indexEquiv i) ≅ infiniteAffineSpace k
  /-- Identification of every overlap with its standard model. -/
  overlapIso : ∀ i j, doubledOriginOverlap k i j ≅ glueData.V (indexEquiv i, indexEquiv j)
  /-- Under the identifications, each overlap map is the canonical inclusion. -/
  overlap_f : ∀ i j,
    (overlapIso i j).hom ≫ glueData.f (indexEquiv i) (indexEquiv j) ≫
      (chartIso i).hom = doubledOriginOverlapι k i j
  /-- Under the identifications, transition maps are the identity. -/
  transition : ∀ i j,
    (overlapIso i j).hom ≫ glueData.t (indexEquiv i) (indexEquiv j) ≫
      (overlapIso j i).inv = doubledOriginOverlapSwap k i j

namespace DoubledOriginData

/-- The scheme obtained by gluing the two affine charts. -/
public abbrev scheme {k : Type u} [CommRing k] (D : DoubledOriginData k) : Scheme.{u} :=
  D.glueData.glued

/-- The canonical open immersion of a chart into the doubled-origin scheme. -/
public def chart {k : Type u} [CommRing k] (D : DoubledOriginData k) (i : Fin 2) :
    infiniteAffineSpace k ⟶ D.scheme :=
  (D.chartIso i).inv ≫ D.glueData.ι (D.indexEquiv i)

/-- Each chart inclusion is an open immersion. -/
public instance {k : Type u} [CommRing k] (D : DoubledOriginData k) (i : Fin 2) :
    IsOpenImmersion (D.chart i) := by
  dsimp [chart]
  infer_instance

end DoubledOriginData

open DoubledOriginData

/-- The structure morphism of infinite-dimensional affine space with doubled
origin, restricting on both charts to the canonical affine-space morphism. -/
@[stacks 01KL "structure_morphism"]
public noncomputable def structureMorphism {k : Type u} [CommRing k]
    (D : DoubledOriginData k) :
    { f : D.scheme ⟶ Spec (.of k) //
      ∀ i : Fin 2,
        D.chart i ≫ f = Spec.map (CommRingCat.ofHom (MvPolynomial.C :
          k →+* MvPolynomial ℕ k)) } := by
  classical
  let c : infiniteAffineSpace k ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial ℕ k))
  let chartMap : ∀ i : D.glueData.J, D.glueData.U i ⟶ Spec (.of k) := fun i =>
    eqToHom (congrArg D.glueData.U (D.indexEquiv.apply_symm_apply i).symm) ≫
      (D.chartIso (D.indexEquiv.symm i)).hom ≫ c
  have standard_compatible : ∀ a b : Fin 2,
      D.glueData.f (D.indexEquiv a) (D.indexEquiv b) ≫ (D.chartIso a).hom ≫ c =
        D.glueData.t (D.indexEquiv a) (D.indexEquiv b) ≫
          D.glueData.f (D.indexEquiv b) (D.indexEquiv a) ≫ (D.chartIso b).hom ≫ c := by
    intro a b
    refine (cancel_epi (D.overlapIso a b).hom).mp ?_
    calc
      (D.overlapIso a b).hom ≫ D.glueData.f (D.indexEquiv a) (D.indexEquiv b) ≫
          (D.chartIso a).hom ≫ c = doubledOriginOverlapι k a b ≫ c := by
            simpa only [Category.assoc] using congrArg (fun g => g ≫ c) (D.overlap_f a b)
      _ = doubledOriginOverlapSwap k a b ≫ doubledOriginOverlapι k b a ≫ c := by
            classical fin_cases a <;> fin_cases b <;> rfl
      _ = (D.overlapIso a b).hom ≫ D.glueData.t (D.indexEquiv a) (D.indexEquiv b) ≫
          D.glueData.f (D.indexEquiv b) (D.indexEquiv a) ≫ (D.chartIso b).hom ≫ c := by
            calc
              _ = ((D.overlapIso a b).hom ≫ D.glueData.t (D.indexEquiv a)
                    (D.indexEquiv b) ≫ (D.overlapIso b a).inv) ≫
                    ((D.overlapIso b a).hom ≫ D.glueData.f (D.indexEquiv b)
                      (D.indexEquiv a) ≫ (D.chartIso b).hom) ≫ c := by
                      rw [D.transition a b, D.overlap_f b a]
              _ = _ := by simp [Category.assoc]
  have chartIso_transport : ∀ {a b : Fin 2} (h : a = b),
      eqToHom (congrArg (fun x => D.glueData.U (D.indexEquiv x)) h) ≫
        (D.chartIso b).hom = (D.chartIso a).hom := by
    rintro a _ rfl
    simp
  have chartMap_index : ∀ a : Fin 2,
      chartMap (D.indexEquiv a) = (D.chartIso a).hom ≫ c := by
    intro a
    dsimp [chartMap]
    have h : a = D.indexEquiv.symm (D.indexEquiv a) := (D.indexEquiv.symm_apply_apply a).symm
    have hcast : (D.indexEquiv.apply_symm_apply (D.indexEquiv a)).symm =
        congrArg D.indexEquiv h := Subsingleton.elim _ _
    rw [hcast]
    simpa [Category.assoc] using congrArg (fun g => g ≫ c) (chartIso_transport h)
  have chartMap_compatible : ∀ i j,
      D.glueData.f i j ≫ chartMap i = D.glueData.t i j ≫ D.glueData.f j i ≫ chartMap j := by
    intro i j
    obtain ⟨a, rfl⟩ := D.indexEquiv.surjective i
    obtain ⟨b, rfl⟩ := D.indexEquiv.surjective j
    rw [chartMap_index a, chartMap_index b]
    exact standard_compatible a b
  let maps : ∀ i : (MultispanShape.prod D.glueData.J).R,
      D.glueData.toGlueData.diagram.right i ⟶ Spec (.of k) := fun i => by
    simpa only [CategoryTheory.GlueData.diagram_right] using chartMap i
  let gluedMap : multicoequalizer D.glueData.toGlueData.diagram ⟶ Spec (.of k) :=
    Multicoequalizer.desc D.glueData.toGlueData.diagram _ maps (by
    intro p
    rcases p with ⟨i, j⟩
    change D.glueData.f i j ≫ maps i = (D.glueData.t i j ≫ D.glueData.f j i) ≫ maps j
    simpa [maps, CategoryTheory.GlueData.diagram] using chartMap_compatible i j)
  refine ⟨gluedMap, ?_⟩
  intro i
  dsimp only [DoubledOriginData.chart]
  dsimp [AlgebraicGeometry.Scheme.GlueData.ι, CategoryTheory.GlueData.ι]
  let idx : (MultispanShape.prod D.glueData.J).R := D.indexEquiv i
  calc
    (D.chartIso i).inv ≫ Multicoequalizer.π D.glueData.toGlueData.diagram idx ≫
        gluedMap = (D.chartIso i).inv ≫ maps idx := by
          simpa only [Category.assoc, D.glueData.toGlueData.diagram_right] using
            congrArg (fun g => (D.chartIso i).inv ≫ g)
              (Multicoequalizer.π_desc D.glueData.toGlueData.diagram _ maps _ idx)
    _ = c := by
      rw [show maps idx = chartMap (D.indexEquiv i) by simp [maps, idx], chartMap_index]
      simp

/-- Precomposing with an isomorphism does not change the image on underlying spaces. -/
private theorem range_comp_base_of_isIso {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (g : Y ⟶ Z) :
    Set.range (e ≫ g).base = Set.range g.base :=
  (show Function.Surjective e.base from by
    rw [← TopCat.epi_iff_surjective]
    infer_instance).range_comp g.base

/-- In a scheme gluing datum, the image of an overlap map followed by a chart inclusion is the
intersection of the two chart images: the overlap is the pullback of the two inclusions. -/
lemma range_glueData_overlap (G : Scheme.GlueData) (i j : G.J) :
    Set.range ((G.f i j ≫ G.ι i).base) =
      Set.range (G.ι i).base ∩ Set.range (G.ι j).base := by
  let e := (G.vPullbackConeIsLimit i j).conePointUniqueUpToIso
    (limit.isLimit (cospan (G.ι i) (G.ι j)))
  have he : e.hom ≫ pullback.fst (G.ι i) (G.ι j) = G.f i j :=
    (G.vPullbackConeIsLimit i j).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (cospan (G.ι i) (G.ι j))) WalkingCospan.left
  have hassoc : e.hom ≫ (pullback.fst (G.ι i) (G.ι j) ≫ G.ι i) =
      G.f i j ≫ G.ι i := by
    rw [← Category.assoc, he]
    rfl
  calc
    Set.range ((G.f i j ≫ G.ι i).base) =
        Set.range ((e.hom ≫ (pullback.fst (G.ι i) (G.ι j) ≫ G.ι i)).base) :=
      congrArg (fun m : (G.vPullbackCone i j).pt ⟶ G.glued => Set.range m.base) hassoc.symm
    _ = Set.range ((pullback.fst (G.ι i) (G.ι j) ≫ G.ι i).base) :=
      range_comp_base_of_isIso e.hom _
    _ = Set.range (G.ι i).base ∩ Set.range (G.ι j).base :=
      AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left
        (G.ι i) (G.ι j)

/-- The image of a chart is the image of the corresponding canonical open immersion of the
gluing datum. -/
lemma chart_range_eq {k : Type u} [CommRing k] (D : DoubledOriginData k)
    (i : Fin 2) :
    Set.range (D.chart i).base = Set.range (D.glueData.ι (D.indexEquiv i)).base := by
  exact range_comp_base_of_isIso (D.chartIso i).inv _

/-- The two charts cover the doubled-origin scheme: every point of the glued scheme lies in
the image of one of the canonical open immersions of the gluing datum, and
`AlgebraicGeometry.DoubledOriginData.indexEquiv` identifies the index set of those with
`Fin 2`. -/
lemma iUnion_chart_range_eq_univ {k : Type u} [CommRing k] (D : DoubledOriginData k) :
    ⋃ i : Fin 2, Set.range (D.chart i).base = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨j, y, rfl⟩ := D.glueData.ι_jointly_surjective x
  refine Set.mem_iUnion.2 ⟨D.indexEquiv.symm j, ?_⟩
  rw [chart_range_eq D (D.indexEquiv.symm j), Equiv.apply_symm_apply]
  exact ⟨y, rfl⟩

/-- The doubled-origin scheme is quasi-compact (Stacks Tag 01KL): it is the union of the images
of its two charts, each of which is the image of a compact space — an affine scheme — under a
continuous map. -/
public instance compactSpace_scheme {k : Type u} [CommRing k] (D : DoubledOriginData k) :
    CompactSpace D.scheme := by
  refine ⟨?_⟩
  rw [← iUnion_chart_range_eq_univ D]
  exact isCompact_iUnion fun i ↦ isCompact_range (D.chart i).base.hom.continuous

/-- The punctured affine space, embedded through the first chart, has the same image as the
overlap map of the two distinct charts. -/
lemma overlap_range_eq {k : Type u} [CommRing k] (D : DoubledOriginData k) :
    Set.range ((puncturedInfiniteAffineSpace k).ι ≫ D.chart 0).base =
      Set.range ((D.glueData.f (D.indexEquiv 0) (D.indexEquiv 1) ≫
        D.glueData.ι (D.indexEquiv 0)).base) := by
  let e := D.overlapIso 0 1
  have hmap : e.hom ≫ D.glueData.f (D.indexEquiv 0) (D.indexEquiv 1) ≫
        D.glueData.ι (D.indexEquiv 0) =
        (puncturedInfiniteAffineSpace k).ι ≫ D.chart 0 := by
    have h01 : doubledOriginOverlapι k 0 1 =
        (puncturedInfiniteAffineSpace k).ι := by
      classical
      unfold doubledOriginOverlapι
      split_ifs with h
      · exact False.elim (by norm_num at h)
      · rfl
    rw [← h01]
    dsimp [DoubledOriginData.chart]
    calc
      e.hom ≫ D.glueData.f (D.indexEquiv 0) (D.indexEquiv 1) ≫
          D.glueData.ι (D.indexEquiv 0) =
        (e.hom ≫ D.glueData.f (D.indexEquiv 0) (D.indexEquiv 1) ≫
          (D.chartIso 0).hom) ≫ (D.chartIso 0).inv ≫
            D.glueData.ι (D.indexEquiv 0) := by simp [Category.assoc]
      _ = doubledOriginOverlapι k 0 1 ≫ (D.chartIso 0).inv ≫
          D.glueData.ι (D.indexEquiv 0) := by rw [D.overlap_f]
  rw [← hmap]
  exact range_comp_base_of_isIso e.hom _

/-- The diagonal inverse image of the product of the two affine charts is the punctured
affine space, embedded in the doubled-origin scheme through its first chart. -/
@[stacks 01KL "diagonal_inverse_image"]
public theorem diagonal_preimage_mixedCharts {k : Type u} [CommRing k]
    (D : DoubledOriginData k) {S : Scheme.{u}} (f : D.scheme ⟶ S) :
    (pullback.diagonal f) ⁻¹'
        ((pullback.fst f f) ⁻¹' Set.range (D.chart 0) ∩
          (pullback.snd f f) ⁻¹' Set.range (D.chart 1)) =
      Set.range ((puncturedInfiniteAffineSpace k).ι ≫ D.chart 0) := by
  have hdiag :
      (pullback.diagonal f) ⁻¹'
          ((pullback.fst f f) ⁻¹' Set.range (D.chart 0) ∩
            (pullback.snd f f) ⁻¹' Set.range (D.chart 1)) =
        Set.range (D.chart 0).base ∩ Set.range (D.chart 1).base := by
    have hfst : (fun x => (pullback.fst f f) ((pullback.diagonal f) x)) = id := by
      funext x
      rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
      rfl
    have hsnd : (fun x => (pullback.snd f f) ((pullback.diagonal f) x)) = id := by
      funext x
      rw [← Scheme.Hom.comp_apply, pullback.diagonal_snd]
      rfl
    simp only [Set.preimage_inter, Set.preimage_preimage, hfst, hsnd, Set.preimage_id]
  rw [hdiag, chart_range_eq D 0, chart_range_eq D 1,
    ← range_glueData_overlap D.glueData (D.indexEquiv 0) (D.indexEquiv 1)]
  exact (overlap_range_eq D).symm

/-- The image of the punctured-space inclusion is the complement of the origin. -/
private theorem punctured_eq_complement_origin (k : Type u) [Field k] :
    Set.range ((puncturedInfiniteAffineSpace k).ι) =
      {p : PrimeSpectrum (MvPolynomial ℕ k) |
        p.asIdeal ≠ Ideal.span (Set.range (MvPolynomial.X : ℕ → MvPolynomial ℕ k))} := by
  classical
  let m : Ideal (MvPolynomial ℕ k) :=
    Ideal.span (Set.range (MvPolynomial.X : ℕ → MvPolynomial ℕ k))
  have hm : m.IsMaximal := isMaximal_span_range_X k
  rw [Scheme.Opens.range_ι]
  ext p
  show p ∈ puncturedInfiniteAffineSpace k ↔ _
  simp only [puncturedInfiniteAffineSpace, infiniteAffineSpace, Opens.mem_iSup]
  constructor
  · rintro ⟨i, hi⟩ heq
    apply (PrimeSpectrum.mem_basicOpen _ _).mp ?_
      (heq.symm ▸ Ideal.subset_span (Set.mem_range_self i))
    rwa [← basicOpen_eq_of_affine (R := CommRingCat.of (MvPolynomial ℕ k))
      (MvPolynomial.X i)]
  · intro hp
    by_contra h
    have hall : ∀ i : ℕ, MvPolynomial.X i ∈ p.asIdeal := by
      intro i
      by_contra hnot
      exact h ⟨i, by
        have hmem : p ∈ PrimeSpectrum.basicOpen (MvPolynomial.X i) :=
          (PrimeSpectrum.mem_basicOpen _ _).mpr hnot
        exact (basicOpen_eq_of_affine (R := CommRingCat.of (MvPolynomial ℕ k))
          (MvPolynomial.X i)).symm ▸ hmem⟩
    exact hp (hm.eq_of_le p.isPrime.ne_top
      (Ideal.span_le.2 (Set.range_subset_iff.mpr hall))).symm

/-- The punctured affine space, embedded through a chart, is not quasi-compact. -/
private theorem punctured_chart_range_not_compact (k : Type u) [Field k]
    (D : DoubledOriginData k) :
    ¬ IsCompact (Set.range ((puncturedInfiniteAffineSpace k).ι ≫ D.chart 0)) := by
  classical
  intro hcompact
  have hsource : IsCompact (Set.univ : Set ↑(puncturedInfiniteAffineSpace k).toScheme) :=
    ((puncturedInfiniteAffineSpace k).ι ≫ D.chart 0).isOpenEmbedding.isEmbedding.isCompact_iff
      |>.2 (by simpa only [Set.image_univ] using hcompact)
  have hrange : IsCompact (Set.range ((puncturedInfiniteAffineSpace k).ι)) := by
    simpa only [Set.image_univ] using
      (puncturedInfiniteAffineSpace k).ι.isOpenEmbedding.isEmbedding.isCompact_iff.1 hsource
  change @IsCompact (↑(infiniteAffineSpace k)) PrimeSpectrum.zariskiTopology
    (Set.range ((puncturedInfiniteAffineSpace k).ι)) at hrange
  rw [punctured_eq_complement_origin] at hrange
  exact puncturedSpectrum_not_isCompact k hrange

/-- The structure morphism of a doubled-origin infinite-dimensional affine
space over a field is not quasi-separated. -/
@[stacks 01KL "not_quasi_separated"]
public theorem structureMorphism_not_quasiSeparated {k : Type u} [Field k]
    (D : DoubledOriginData k) :
    ¬ QuasiSeparated (structureMorphism D).1 := by
  classical
  let f := (structureMorphism D).1
  have hcompact : IsCompact
      ((pullback.fst f f) ⁻¹' Set.range (D.chart 0) ∩
        (pullback.snd f f) ⁻¹' Set.range (D.chart 1)) := by
    simpa using
      (AlgebraicGeometry.isAffineOpen_opensRange (D.chart 0)).isCompact_pullback_inf
        (AlgebraicGeometry.isAffineOpen_opensRange (D.chart 1)).isCompact
        (isAffineOpen_top _) (by simp) (by simp)
  have hopen : IsOpen
      ((pullback.fst f f) ⁻¹' Set.range (D.chart 0) ∩
        (pullback.snd f f) ⁻¹' Set.range (D.chart 1)) :=
    ((D.chart 0).isOpenEmbedding.isOpen_range.preimage
      (pullback.fst f f).continuous).inter
      ((D.chart 1).isOpenEmbedding.isOpen_range.preimage (pullback.snd f f).continuous)
  intro hqs
  have : QuasiSeparated f := hqs
  have : QuasiCompact (pullback.diagonal f) := hqs.quasiCompact_diagonal
  have hpre := QuasiCompact.isCompact_preimage (f := pullback.diagonal f)
    _ hopen hcompact
  rw [diagonal_preimage_mixedCharts D f] at hpre
  exact punctured_chart_range_not_compact k D hpre

/-- The doubled-origin scheme over a field is not a quasi-separated topological space. Its
structure morphism goes to an affine scheme, which is quasi-separated, so quasi-separatedness
of that morphism and of the source agree; the morphism is not quasi-separated by
`AlgebraicGeometry.structureMorphism_not_quasiSeparated` (Stacks Tag 01KL). -/
public theorem not_quasiSeparatedSpace_scheme {k : Type u} [Field k]
    (D : DoubledOriginData k) : ¬ QuasiSeparatedSpace D.scheme := fun h ↦
  structureMorphism_not_quasiSeparated D
    ((quasiSeparated_iff_quasiSeparatedSpace (structureMorphism D).1).2 h)

end AlgebraicGeometry

end

end
