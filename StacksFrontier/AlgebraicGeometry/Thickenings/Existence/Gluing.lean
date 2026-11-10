module

public import StacksFrontier.AlgebraicGeometry.Thickenings.Existence.Transitions

/-!
# Existence of the universal first-order thickening: gluing

This file glues the thickenings of the charts of an affine open cover into a universal
first-order thickening of a formally unramified morphism `h : Z ⟶ X`.

## Main definitions

* `Stacks.Thickenings.universalFirstOrderThickening` is the chosen universal first-order
  thickening of a formally unramified morphism.

## Main results

* `Stacks.Thickenings.nonempty_universalFirstOrderThickening`: a formally unramified morphism
  admits a universal first-order thickening. This is Tag 04F3.
* `Stacks.Thickenings.universalFirstOrderThickening_isUniversal`,
  `Stacks.Thickenings.isFirstOrderThickening_universalFirstOrderThickening_inclusion`,
  `Stacks.Thickenings.universalFirstOrderThickening_inclusion_comp_toBase` and
  `Stacks.Thickenings.universalFirstOrderThickening_existsUnique_lift` pin the chosen
  thickening down: they say that it is a first-order thickening, that it is a thickening over
  `X`, and that it has the universal lifting property.

## References

* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- `sourceOverlapIso` is compatible with the maps to `Z`. -/
private lemma sourceOverlapIso_hom_fac {Z : Scheme.{u}} (𝒰 : Z.OpenCover) (i j : 𝒰.I₀) :
    (sourceOverlapIso 𝒰 i j).hom ≫ (sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j =
      (sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (sourceOverlap_range 𝒰 i j)

/-- The gluing data assembled from the chosen thickenings of the charts, their double overlap
thickenings, and the canonical transition isomorphisms. The cocycle condition holds because
all the schemes involved are universal first-order thickenings of the corresponding overlaps,
hence determined up to unique isomorphism. -/
private noncomputable def thickeningGlueData {Z X : Scheme.{u}} (𝒰 : Z.OpenCover)
    (h : Z ⟶ X) (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h))
    (_hA : ∀ i, FormallyUnramified (A i).toBase) : Scheme.GlueData := by
  classical
  refine {
    J := 𝒰.I₀
    U := fun i => (A i).ambient
    V := fun ij => (overlapRestriction 𝒰 h A ij.1 ij.2).ambient
    f := fun i j => overlapRestrictionMap 𝒰 h A i j
    f_id := fun i => isIso_of_isOpenImmersion_of_opensRange_eq_top _
      (overlapRestrictionMap_self_opensRange 𝒰 h A i)
    t := fun i j => (overlapTransition 𝒰 h A i j).hom
    f_open := fun i j => isOpenImmersion_overlapRestrictionMap 𝒰 h A i j
    t_id := fun i => by simp [overlapTransition]
    t' := fun i j k => (tripleIsoPullback 𝒰 h A i j k).inv ≫
      (tripleTransition 𝒰 h A i j k).hom ≫
      (tripleIsoPullback 𝒰 h A j i k).hom ≫
      (pullbackSymmetry (overlapRestrictionMap 𝒰 h A j i)
        (overlapRestrictionMap 𝒰 h A j k)).hom
    t_fac := by
      intro i j k
      let H := tripleRestriction 𝒰 h A i j k
      let f := overlapRestrictionMap 𝒰 h A j i
      let e := tripleIsoPullback 𝒰 h A i j k
      let a := (sourceTripleIso 𝒰 i j k).hom ≫ (sourceTriple 𝒰 j i k).ι
      let p₁ := (tripleTransition 𝒰 h A i j k).hom ≫
        tripleToOverlapLeft 𝒰 h A j i k ≫ f
      let p₂ := tripleToOverlapLeft 𝒰 h A i j k ≫
        (overlapTransition 𝒰 h A i j).hom ≫ f
      have hsource :
          (𝒰.X i).homOfLE (sourceTriple_le_sourceOverlap 𝒰 i j k) ≫
            (sourceOverlapIso 𝒰 i j).hom ≫ (sourceOverlap 𝒰 j i).ι = a := by
        apply (cancel_mono (𝒰.f j)).mp
        simp only [a, Category.assoc, sourceOverlapIso_hom_fac, sourceTripleIso_hom_fac,
          Scheme.homOfLE_ι_assoc]
      have hinc₁ : H.inclusion ≫ p₁ = a ≫ (A j).inclusion := by
        simp only [p₁, H, f, a, tripleTransition_inclusion_assoc,
          reassoc_of% (tripleToOverlapLeft_inclusion 𝒰 h A j i k),
          overlapRestriction_inclusion_comp_map, Scheme.homOfLE_ι_assoc, Category.assoc]
      have hinc₂ : H.inclusion ≫ p₂ = a ≫ (A j).inclusion := by
        simp only [p₂, H, f, reassoc_of% (tripleToOverlapLeft_inclusion 𝒰 h A i j k),
          overlapTransition_inclusion_assoc, overlapRestriction_inclusion_comp_map,
          reassoc_of% hsource]
      have hbase₁ : p₁ ≫ (A j).toBase = H.toBase := by
        dsimp [p₁, H, f]
        simp [Category.assoc, tripleToOverlapLeft_toBase,
          overlapRestrictionMap_comp_toBase, tripleTransition_toBase]
      have hbase₂ : p₂ ≫ (A j).toBase = H.toBase := by
        dsimp [p₂, H, f]
        simp [Category.assoc, tripleToOverlapLeft_toBase,
          overlapRestrictionMap_comp_toBase, overlapTransition_toBase]
      have hab : H.inclusion ≫ H.toBase = a ≫ (𝒰.f j ≫ h) := by
        rw [H.isUniversal.inclusion_toBase]
        dsimp [a]
        simpa only [Category.assoc] using
          congrArg (fun g => g ≫ h) (sourceTripleIso_hom_fac 𝒰 i j k).symm
      obtain ⟨_, _, hu⟩ := (A j).isUniversal.existsUnique_lift H.inclusion
        H.isUniversal.isFirstOrderThickening a H.toBase hab
      have hp₁ := hu p₁ ⟨hinc₁, hbase₁⟩
      have hp₂ := hu p₂ ⟨hinc₂, hbase₂⟩
      have hp : p₁ = p₂ := hp₁.trans hp₂.symm
      apply (cancel_mono f).mp
      calc
        _ = e.inv ≫ p₁ := by
          simp only [p₁, e, Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
            reassoc_of% (tripleIsoPullback_fst 𝒰 h A j i k)]
        _ = e.inv ≫ p₂ := by rw [hp]
        _ = _ := by
          simp only [p₂, ← reassoc_of% (tripleIsoPullback_fst 𝒰 h A i j k), e,
            Iso.inv_hom_id_assoc, Category.assoc]
    cocycle := by
      intro i j k
      let H := tripleRestriction 𝒰 h A i j k
      let e := tripleIsoPullback 𝒰 h A i j k
      let c :=
        (tripleIsoPullback 𝒰 h A i j k).inv ≫
          (tripleTransition 𝒰 h A i j k).hom ≫
          (tripleIsoPullback 𝒰 h A j i k).hom ≫
          (pullbackSymmetry (overlapRestrictionMap 𝒰 h A j i)
            (overlapRestrictionMap 𝒰 h A j k)).hom ≫
          (tripleIsoPullback 𝒰 h A j k i).inv ≫
          (tripleTransition 𝒰 h A j k i).hom ≫
          (tripleIsoPullback 𝒰 h A k j i).hom ≫
          (pullbackSymmetry (overlapRestrictionMap 𝒰 h A k j)
            (overlapRestrictionMap 𝒰 h A k i)).hom ≫
          (tripleIsoPullback 𝒰 h A k i j).inv ≫
          (tripleTransition 𝒰 h A k i j).hom ≫
          (tripleIsoPullback 𝒰 h A i k j).hom ≫
          (pullbackSymmetry (overlapRestrictionMap 𝒰 h A i k)
            (overlapRestrictionMap 𝒰 h A i j)).hom
      have hc : e.hom ≫ c ≫ e.inv = 𝟙 H.ambient := by
        have hce : e.hom ≫ c ≫ e.inv = tripleCycle 𝒰 h A i j k := by
          dsimp [c, e, tripleCycle]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
        obtain ⟨f, hf, hu⟩ := H.isUniversal.existsUnique_lift H.inclusion
          H.isUniversal.isFirstOrderThickening (𝟙 _) H.toBase H.isUniversal.inclusion_toBase
        rw [hce]
        exact (hu _ ⟨(inclusion_tripleCycle 𝒰 h A i j k).trans (Category.id_comp _).symm,
          tripleCycle_toBase 𝒰 h A i j k⟩).trans (hu (𝟙 _) ⟨by simp, by simp⟩).symm
      change c = 𝟙 _
      calc
        c = (e.inv ≫ e.hom) ≫ c ≫ (e.inv ≫ e.hom) := by simp
        _ = e.inv ≫ (e.hom ≫ c ≫ e.inv) ≫ e.hom := by simp [Category.assoc]
        _ = e.inv ≫ 𝟙 _ ≫ e.hom := by rw [hc]
        _ = 𝟙 _ := by simp }

/-- The fibre product of two charts factors through both descriptions of their overlap. -/
private lemma exists_factorization_sourceOverlap {Z : Scheme.{u}} (𝒰 : Z.OpenCover)
    (i j : 𝒰.I₀) : ∃ l : pullback (𝒰.f i) (𝒰.f j) ⟶ (sourceOverlap 𝒰 i j).toScheme,
      l ≫ (sourceOverlap 𝒰 i j).ι = pullback.fst (𝒰.f i) (𝒰.f j) ∧
      l ≫ (sourceOverlapIso 𝒰 i j).hom ≫ (sourceOverlap 𝒰 j i).ι =
        pullback.snd (𝒰.f i) (𝒰.f j) := by
  have hr : Set.range (pullback.fst (𝒰.f i) (𝒰.f j)).base ⊆
      Set.range (sourceOverlap 𝒰 i j).ι.base := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨pullback.fst (𝒰.f i) (𝒰.f j) x, ?_⟩, rfl⟩
    exact ⟨pullback.snd (𝒰.f i) (𝒰.f j) x,
      (congrArg (fun f => (f : _ ⟶ Z) x) pullback.condition).symm⟩
  let l := IsOpenImmersion.lift (sourceOverlap 𝒰 i j).ι
    (pullback.fst (𝒰.f i) (𝒰.f j)) hr
  have hl : l ≫ (sourceOverlap 𝒰 i j).ι = pullback.fst (𝒰.f i) (𝒰.f j) :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨l, hl, ?_⟩
  apply (cancel_mono (𝒰.f j)).mp
  rw [Category.assoc, Category.assoc, sourceOverlapIso_hom_fac, ← Category.assoc, hl]
  exact pullback.condition

/-- The inclusions of the charts into their thickenings agree on the fibre products of the
charts, so they glue. -/
private lemma gluedInclusion_compatible {Z X : Scheme.{u}} (𝒰 : Z.OpenCover)
    (h : Z ⟶ X) (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h))
    (hA : ∀ i, FormallyUnramified (A i).toBase) (i j : 𝒰.I₀) :
    pullback.fst (𝒰.f i) (𝒰.f j) ≫ (A i).inclusion ≫
      (thickeningGlueData 𝒰 h A hA).ι i =
    pullback.snd (𝒰.f i) (𝒰.f j) ≫ (A j).inclusion ≫
      (thickeningGlueData 𝒰 h A hA).ι j := by
  let D := thickeningGlueData 𝒰 h A hA
  obtain ⟨l, hl, hl'⟩ := exists_factorization_sourceOverlap 𝒰 i j
  rw [← hl, ← hl']
  simp only [Category.assoc]
  have hg := D.glue_condition i j
  change (overlapTransition 𝒰 h A i j).hom ≫
    overlapRestrictionMap 𝒰 h A j i ≫ D.ι j =
    overlapRestrictionMap 𝒰 h A i j ≫ D.ι i at hg
  calc
    _ = l ≫ (overlapRestriction 𝒰 h A i j).inclusion ≫
        overlapRestrictionMap 𝒰 h A i j ≫ D.ι i :=
      congrArg (l ≫ ·) (overlapRestriction_inclusion_comp_map_assoc 𝒰 h A i j (D.ι i)).symm
    _ = l ≫ (overlapRestriction 𝒰 h A i j).inclusion ≫
        (overlapTransition 𝒰 h A i j).hom ≫ overlapRestrictionMap 𝒰 h A j i ≫ D.ι j := by
      rw [hg]
    _ = _ := by
      rw [overlapTransition_inclusion_assoc]
      exact congrArg (l ≫ (sourceOverlapIso 𝒰 i j).hom ≫ ·)
        (overlapRestriction_inclusion_comp_map_assoc 𝒰 h A j i (D.ι j))

/-- The inclusion of `Z` into the glued scheme. -/
private noncomputable def gluedInclusion {Z X : Scheme.{u}} (𝒰 : Z.OpenCover)
    (h : Z ⟶ X) (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h))
    (hA : ∀ i, FormallyUnramified (A i).toBase) :
    Z ⟶ (thickeningGlueData 𝒰 h A hA).glued :=
  𝒰.glueMorphisms (fun i => (A i).inclusion ≫ (thickeningGlueData 𝒰 h A hA).ι i)
    (gluedInclusion_compatible 𝒰 h A hA)

/-- `gluedInclusion` restricts to the inclusion of each chart into its thickening. -/
private lemma gluedInclusion_fac {Z X : Scheme.{u}} (𝒰 : Z.OpenCover)
    (h : Z ⟶ X) (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h))
    (hA : ∀ i, FormallyUnramified (A i).toBase) (i : 𝒰.I₀) :
    𝒰.f i ≫ gluedInclusion 𝒰 h A hA =
      (A i).inclusion ≫ (thickeningGlueData 𝒰 h A hA).ι i :=
  𝒰.ι_glueMorphisms _ _ i

/-- The structure morphism of the glued scheme to `X`. -/
private noncomputable def gluedToBase {Z X : Scheme.{u}} (𝒰 : Z.OpenCover)
    (h : Z ⟶ X) (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h))
    (hA : ∀ i, FormallyUnramified (A i).toBase) :
    (thickeningGlueData 𝒰 h A hA).glued ⟶ X := by
  apply Multicoequalizer.desc _ _ (fun i => (A i).toBase)
  rintro ⟨i, j⟩
  change 𝒰.I₀ at i j
  change overlapRestrictionMap 𝒰 h A i j ≫ (A i).toBase =
    ((overlapTransition 𝒰 h A i j).hom ≫
      overlapRestrictionMap 𝒰 h A j i) ≫ (A j).toBase
  simp only [Category.assoc, overlapRestrictionMap_comp_toBase,
    overlapTransition_toBase]

/-- `gluedToBase` restricts to the structure morphism of each chart's thickening. -/
private lemma gluedToBase_fac {Z X : Scheme.{u}} (𝒰 : Z.OpenCover)
    (h : Z ⟶ X) (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h))
    (hA : ∀ i, FormallyUnramified (A i).toBase) (i : 𝒰.I₀) :
    (thickeningGlueData 𝒰 h A hA).ι i ≫ gluedToBase 𝒰 h A hA = (A i).toBase := by
  dsimp only [gluedToBase]
  exact Multicoequalizer.π_desc
    (thickeningGlueData 𝒰 h A hA).toGlueData.diagram X (fun i => (A i).toBase) _ i

/-- Each chart's thickening is the fibre product of the chart and the glued scheme over `Z`. -/
private lemma gluedInclusion_isPullback {Z X : Scheme.{u}} (𝒰 : Z.OpenCover)
    (h : Z ⟶ X) (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h))
    (hA : ∀ i, FormallyUnramified (A i).toBase) (i : 𝒰.I₀) :
    IsPullback (A i).inclusion (𝒰.f i) ((thickeningGlueData 𝒰 h A hA).ι i)
      (gluedInclusion 𝒰 h A hA) := by
  let D := thickeningGlueData 𝒰 h A hA
  let g := gluedInclusion 𝒰 h A hA
  change IsPullback (A i).inclusion (𝒰.f i) (D.ι i) g
  refine @IsOpenImmersion.isPullback _ _ _ _ (A i).inclusion (𝒰.f i) (D.ι i) g
    inferInstance (D.ι_isOpenImmersion i) (gluedInclusion_fac 𝒰 h A hA i) ?_
  ext z
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨j, t, ht⟩ := 𝒰.exists_eq z
    have he : D.ι j ((A j).inclusion t) = D.ι i y := by
      calc
        _ = g (𝒰.f j t) := (congrArg (fun f => (f : _ ⟶ D.glued) t)
          (gluedInclusion_fac 𝒰 h A hA j)).symm
        _ = _ := by rw [ht]; exact hy.symm
    obtain ⟨w, hw, _⟩ := (D.ι_eq_iff j i _ _).mp he
    change D.f j i w = (A j).inclusion t at hw
    have hm : (A j).inclusion t ∈
        thickeningOpenImage (A j).inclusion (A j).isUniversal.isFirstOrderThickening.isThickening
          (sourceOverlap 𝒰 j i) := by
      rw [← hw]
      exact w.property
    have hm' : t ∈ sourceOverlap 𝒰 j i := by
      rw [← preimage_thickeningOpenImage (A j).inclusion
        (A j).isUniversal.isFirstOrderThickening.isThickening (sourceOverlap 𝒰 j i)]
      exact hm
    obtain ⟨x, hx⟩ := hm'
    exact ⟨x, hx.trans ht⟩
  · rintro ⟨t, rfl⟩
    exact ⟨(A i).inclusion t,
      (congrArg (fun f => (f : _ ⟶ D.glued) t) (gluedInclusion_fac 𝒰 h A hA i)).symm⟩

/-- Being a first-order thickening is local on the target: if it holds after base change to each
chart of an open cover of the ambient scheme, it holds. -/
private lemma isFirstOrderThickening_of_openCover {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (𝒱 : Y.OpenCover) (W : 𝒱.I₀ → Scheme.{u}) (v : ∀ i, W i ⟶ Z)
    (q : ∀ i, W i ⟶ 𝒱.X i)
    (hpb : ∀ i, IsPullback (q i) (v i) (𝒱.f i) g)
    (hq : ∀ i, IsFirstOrderThickening (q i)) :
    IsFirstOrderThickening g := by
  have hc : IsClosedImmersion g := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) 𝒱
    intro i
    have : IsClosedImmersion (q i) := (hq i).1
    change IsClosedImmersion (pullback.snd g (𝒱.f i))
    rw [← (hpb i).flip.isoPullback_inv_snd]
    infer_instance
  have := hc
  refine ⟨hc, ?_⟩
  let V : (Σ i, (𝒱.X i).affineOpens) → Y.affineOpens := fun a =>
    ⟨𝒱.f a.1 ''ᵁ a.2, a.2.2.image_of_isOpenImmersion (𝒱.f a.1)⟩
  have hV : ⨆ a, (V a : Y.Opens) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i, x, hx⟩ := 𝒱.exists_eq y
    let U : (𝒱.X i).affineOpens :=
      ⟨(𝒱.X i).affineCover.f ((𝒱.X i).affineCover.idx x) |>.opensRange,
        isAffineOpen_opensRange _⟩
    have hxU : x ∈ U.1 := (𝒱.X i).affineCover.covers x
    exact (TopologicalSpace.Opens.mem_iSup).mpr ⟨⟨i, U⟩, ⟨x, hxU, hx⟩⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V hV
  rintro ⟨i, U⟩
  have he := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g (q i) (v i)
    (𝒱.f i) (hpb i) U
  have hs : ((q i).ker.ideal U) ^ 2 = ⊥ := by
    simpa using congrArg (fun J : Scheme.IdealSheafData (𝒱.X i) => J.ideal U) (hq i).2
  rw [he] at hs
  have hh := congrArg (Ideal.map ((𝒱.f i).appIso U).inv.hom) hs
  change (g.ker.ideal (V ⟨i, U⟩)) ^ 2 = ⊥
  simpa only [Ideal.map_pow, Ideal.map_comap_of_surjective _
    (ConcreteCategory.bijective_of_isIso ((𝒱.f i).appIso U).inv).2, Ideal.map_bot] using hh

/-- The base change of a first-order thickening along an open immersion is a first-order
thickening. -/
private lemma isFirstOrderThickening_pullbackFst {T T' V : Scheme.{u}} (j : T ⟶ T')
    (hj : IsFirstOrderThickening j) (v : V ⟶ T') [IsOpenImmersion v] :
    IsFirstOrderThickening (pullback.fst v j) := by
  have : IsClosedImmersion j := hj.1
  refine ⟨inferInstance, ?_⟩
  rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  exact comap_sq_eq_bot_of_isOpenImmersion j.ker v hj.2

/-- The unique lifting property against a first-order thickening `j` may be checked on an open
cover of the ambient scheme of `j`, provided the target's structure morphism is formally
unramified: the local lifts then glue and the glued lift is unique. -/
private lemma existsUnique_lift_of_openCover {T T' Y X : Scheme.{u}}
    (j : T ⟶ T') (hj : IsFirstOrderThickening j)
    (p : Y ⟶ X) [FormallyUnramified p] (a : T ⟶ Y) (b : T' ⟶ X)
    (𝒱 : T'.OpenCover)
    (hl : ∀ i, ∃ f : 𝒱.X i ⟶ Y,
      pullback.fst (𝒱.f i) j ≫ f = pullback.snd (𝒱.f i) j ≫ a ∧
      f ≫ p = 𝒱.f i ≫ b) :
    ∃! f : T' ⟶ Y, j ≫ f = a ∧ f ≫ p = b := by
  classical
  choose f hf hb using hl
  have compat (i k : 𝒱.I₀) : pullback.fst (𝒱.f i) (𝒱.f k) ≫ f i =
      pullback.snd (𝒱.f i) (𝒱.f k) ≫ f k := by
    let v := pullback.fst (𝒱.f i) (𝒱.f k) ≫ 𝒱.f i
    let q := pullback.fst v j
    let r := pullback.snd v j
    have hq := isFirstOrderThickening_pullbackFst j hj v
    have : IsClosedImmersion q := hq.1
    have key (c : 𝒱.I₀) (π : pullback (𝒱.f i) (𝒱.f k) ⟶ 𝒱.X c) (hπ : π ≫ 𝒱.f c = v) :
        q ≫ π ≫ f c = r ≫ a := by
      let α := pullback.lift (q ≫ π) r
        (by rw [Category.assoc, hπ]; exact pullback.condition)
      calc
        _ = α ≫ pullback.fst (𝒱.f c) j ≫ f c := (pullback.lift_fst_assoc _ _ _ _).symm
        _ = r ≫ a := by rw [hf c, ← Category.assoc, pullback.lift_snd]
    have h₁ := key i (pullback.fst _ _) rfl
    have h₂ := key k (pullback.snd _ _) pullback.condition.symm
    apply FormallyUnramified.hom_ext q ⟨2, by simpa using hq.2⟩ p
    · exact h₁.trans h₂.symm
    · simp only [Category.assoc, hb, pullback.condition_assoc]
  let F := 𝒱.glueMorphisms f compat
  have hF : j ≫ F = a := by
    apply Scheme.Cover.hom_ext (𝒱.pullback₁ j)
    intro i
    change 𝒱.I₀ at i
    change pullback.fst j (𝒱.f i) ≫ j ≫ F = pullback.fst j (𝒱.f i) ≫ a
    rw [pullback.condition_assoc]
    change pullback.snd j (𝒱.f i) ≫ 𝒱.f i ≫ 𝒱.glueMorphisms f compat = _
    rw [𝒱.ι_glueMorphisms]
    have hi := congrArg (fun g => (pullbackSymmetry j (𝒱.f i)).hom ≫ g) (hf i)
    simpa only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
      pullbackSymmetry_hom_comp_snd_assoc] using hi
  have hB : F ≫ p = b := by
    apply 𝒱.hom_ext
    intro i
    change 𝒱.f i ≫ 𝒱.glueMorphisms f compat ≫ p = _
    rw [𝒱.ι_glueMorphisms_assoc]
    exact hb i
  refine ⟨F, ⟨hF, hB⟩, ?_⟩
  intro G hG
  have : IsClosedImmersion j := hj.1
  apply FormallyUnramified.hom_ext j ⟨2, by simpa using hj.2⟩ p
  · exact hG.1.trans hF.symm
  · exact hG.2.trans hB.symm

/-- The structure morphism of the glued thickening is formally unramified over `X`. Formal
unramifiedness is Zariski-local at the source, and on the chart `D.ι i` the structure morphism
is the structure morphism of the `i`-th chart thickening, which is formally unramified by
hypothesis. -/
private lemma formallyUnramified_gluedToBase {Z X : Scheme.{u}} (𝒰 : Z.OpenCover)
    (h : Z ⟶ X) (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h))
    (hA : ∀ i, FormallyUnramified (A i).toBase) :
    FormallyUnramified (gluedToBase 𝒰 h A hA) := by
  classical
  let D := thickeningGlueData 𝒰 h A hA
  let p := gluedToBase 𝒰 h A hA
  let : IsZariskiLocalAtSource (@FormallyUnramified : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FormallyUnramified)
  apply IsZariskiLocalAtSource.of_openCover (P := @FormallyUnramified) D.openCover
  intro i
  change 𝒰.I₀ at i
  change FormallyUnramified (D.ι i ≫ p)
  change FormallyUnramified
    ((thickeningGlueData 𝒰 h A hA).ι i ≫ gluedToBase 𝒰 h A hA)
  rw [gluedToBase_fac]
  exact hA i

/-- The glued scheme is a universal first-order thickening of `Z` over `X`. This is the final
step of the proof of Tag 04F3: being a first-order thickening is local on the target, and the
unique lifting property follows by covering any test thickening by the preimages of the
charts. -/
private lemma isUniversalFirstOrderThickening_gluedInclusion {Z X : Scheme.{u}} (𝒰 : Z.OpenCover)
    (h : Z ⟶ X) (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h))
    (hA : ∀ i, FormallyUnramified (A i).toBase) :
    IsUniversalFirstOrderThickening h (gluedInclusion 𝒰 h A hA)
      (gluedToBase 𝒰 h A hA) := by
  classical
  let D := thickeningGlueData 𝒰 h A hA
  let g := gluedInclusion 𝒰 h A hA
  let p := gluedToBase 𝒰 h A hA
  have hp : FormallyUnramified p := formallyUnramified_gluedToBase 𝒰 h A hA
  refine ⟨isFirstOrderThickening_of_openCover g D.openCover 𝒰.X 𝒰.f
    (fun i => (A i).inclusion) (gluedInclusion_isPullback 𝒰 h A hA)
    (fun i => (A i).isUniversal.isFirstOrderThickening), ?_, ?_⟩
  · apply 𝒰.hom_ext
    intro i
    change 𝒰.f i ≫ g ≫ p = _
    rw [← Category.assoc, gluedInclusion_fac]
    exact (congrArg (fun f => (A i).inclusion ≫ f)
      (gluedToBase_fac 𝒰 h A hA i)).trans (A i).isUniversal.inclusion_toBase
  · intro T T' j hj a b hab
    let W (i : 𝒰.I₀) := thickeningOpenImage j hj.isThickening (a ⁻¹ᵁ (𝒰.f i).opensRange)
    have hW (i : 𝒰.I₀) : j ⁻¹ᵁ W i = a ⁻¹ᵁ (𝒰.f i).opensRange :=
      preimage_thickeningOpenImage j hj.isThickening _
    let 𝒱 : T'.OpenCover := Scheme.Cover.mkOfCovers 𝒰.I₀
      (fun i => (W i).toScheme) (fun i => (W i).ι) (by
        intro t'
        obtain ⟨t, ht⟩ := hj.isThickening.2 t'
        obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (a t)
        refine ⟨i, ⟨t', ?_⟩, rfl⟩
        rw [← ht]
        change t ∈ j ⁻¹ᵁ W i
        rw [hW]
        exact ⟨x, hx⟩)
    apply existsUnique_lift_of_openCover j hj p (a ≫ g) b 𝒱
    intro i
    change 𝒰.I₀ at i
    have : IsOpenImmersion (𝒱.f i) := by
      change IsOpenImmersion (W i).ι
      infer_instance
    let q := pullback.fst (𝒱.f i) j
    let r := pullback.snd (𝒱.f i) j
    have hr : Set.range (r ≫ a).base ⊆ Set.range (𝒰.f i).base := by
      rintro _ ⟨t, rfl⟩
      have hm : j (r t) ∈ W i := by
        have he := congrArg (fun f => (f : _ ⟶ T') t)
          (pullback.condition (f := 𝒱.f i) (g := j))
        change (𝒱.f i) (q t) = j (r t) at he
        rw [← he]
        exact (q t).property
      change r t ∈ j ⁻¹ᵁ W i at hm
      rwa [hW] at hm
    let ai := IsOpenImmersion.lift (𝒰.f i) (r ≫ a) hr
    have hai : ai ≫ 𝒰.f i = r ≫ a := IsOpenImmersion.lift_fac _ _ _
    have hc : q ≫ (𝒱.f i ≫ b) = ai ≫ (𝒰.f i ≫ h) := by
      rw [← Category.assoc, pullback.condition, Category.assoc, hab,
        ← Category.assoc, ← hai]
      simp only [Category.assoc]
    obtain ⟨f, hf, _⟩ := (A i).isUniversal.existsUnique_lift q
      (isFirstOrderThickening_pullbackFst j hj (𝒱.f i)) ai (𝒱.f i ≫ b) hc
    refine ⟨f ≫ D.ι i, ?_, ?_⟩
    · change q ≫ (f ≫ D.ι i) = r ≫ a ≫ g
      calc
        q ≫ (f ≫ D.ι i) = (q ≫ f) ≫ D.ι i := (Category.assoc _ _ _).symm
        _ = (ai ≫ (A i).inclusion) ≫ D.ι i := eq_whisker hf.1 _
        _ = ai ≫ (𝒰.f i ≫ g) := (Category.assoc _ _ _).trans
          (congrArg (fun f => ai ≫ f) (gluedInclusion_fac 𝒰 h A hA i).symm)
        _ = r ≫ a ≫ g := by rw [← Category.assoc, hai]; simp only [Category.assoc]
    · have hfac : D.ι i ≫ p = (A i).toBase := gluedToBase_fac 𝒰 h A hA i
      calc
        (f ≫ D.ι i) ≫ p = f ≫ (D.ι i ≫ p) := Category.assoc _ _ _
        _ = f ≫ (A i).toBase := congrArg (fun z => f ≫ z) hfac
        _ = 𝒱.f i ≫ b := hf.2

/-- **Stacks Project, Tag 04F3.** A formally unramified morphism of schemes admits a universal
first-order thickening. It is constructed by gluing the thickenings of the charts of an affine
open cover of `Z` subordinate to an affine open cover of `X`; the affine charts come from the
algebraic universal first-order thickening
(`Algebra.FormallyUnramified.universalFirstOrderThickening`, Tag 04EB). -/
@[stacks 04F3]
theorem nonempty_universalFirstOrderThickening {Z X : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] : Nonempty (UniversalFirstOrderThickening h) :=
  let 𝒰 := affineSourceCover h
  let A := affineChartThickening h
  let hA := formallyUnramified_affineChartThickening_toBase h
  ⟨{ ambient := (thickeningGlueData 𝒰 h A hA).glued
     inclusion := gluedInclusion 𝒰 h A hA
     toBase := gluedToBase 𝒰 h A hA
     isUniversal := isUniversalFirstOrderThickening_gluedInclusion 𝒰 h A hA }⟩

/-- A formally unramified morphism admits a universal first-order thickening, as an instance. -/
instance instNonemptyUniversalFirstOrderThickening {Z X : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] : Nonempty (UniversalFirstOrderThickening h) :=
  nonempty_universalFirstOrderThickening h

/-- The universal first-order thickening constructed by
`Stacks.Thickenings.nonempty_universalFirstOrderThickening` has formally unramified structure
morphism. The construction glues the thickenings of the charts of an affine open cover, and
formal unramifiedness is Zariski-local at the source, so it is inherited from the charts.

This is the information the gluing construction produces but the bare existence statement
discards. Together with
`Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso` it gives Tag 04F6 for *every*
universal first-order thickening, not only for the glued one. -/
theorem exists_universalFirstOrderThickening_formallyUnramified_toBase {Z X : Scheme.{u}}
    (h : Z ⟶ X) [FormallyUnramified h] :
    ∃ t : UniversalFirstOrderThickening h, FormallyUnramified t.toBase :=
  let 𝒰 := affineSourceCover h
  let A := affineChartThickening h
  let hA := formallyUnramified_affineChartThickening_toBase h
  ⟨{ ambient := (thickeningGlueData 𝒰 h A hA).glued
     inclusion := gluedInclusion 𝒰 h A hA
     toBase := gluedToBase 𝒰 h A hA
     isUniversal := isUniversalFirstOrderThickening_gluedInclusion 𝒰 h A hA },
    formallyUnramified_gluedToBase 𝒰 h A hA⟩

/-- **Stacks Project, Tag 04F3.** *The* universal first-order thickening of a formally
unramified morphism `h : Z ⟶ X`, chosen by
`Stacks.Thickenings.nonempty_universalFirstOrderThickening`.

The universal property is part of the data, as the field
`Stacks.Thickenings.UniversalFirstOrderThickening.isUniversal`; it is spelled out in
`Stacks.Thickenings.universalFirstOrderThickening_isUniversal` and its consequences below.
Nothing beyond that property should be used: by
`Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso` the choice is unique up to
unique isomorphism, which is why the ambient scheme is left opaque here rather than exposed as
the glued scheme. -/
@[stacks 04F3]
noncomputable def universalFirstOrderThickening {Z X : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] : UniversalFirstOrderThickening h :=
  (nonempty_universalFirstOrderThickening h).some

/-- The chosen thickening of `h` has the first-order and universal mapping properties: this is
what pins `Stacks.Thickenings.universalFirstOrderThickening` down, since by
`Stacks.Thickenings.UniversalFirstOrderThickening.canonicalIso` any two objects with these
properties are canonically isomorphic. -/
theorem universalFirstOrderThickening_isUniversal {Z X : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] :
    IsUniversalFirstOrderThickening h (universalFirstOrderThickening h).inclusion
      (universalFirstOrderThickening h).toBase :=
  (universalFirstOrderThickening h).isUniversal

/-- The inclusion of `Z` into its universal first-order thickening is a closed immersion with
square-zero defining ideal sheaf. -/
theorem isFirstOrderThickening_universalFirstOrderThickening_inclusion {Z X : Scheme.{u}}
    (h : Z ⟶ X) [FormallyUnramified h] :
    IsFirstOrderThickening (universalFirstOrderThickening h).inclusion :=
  (universalFirstOrderThickening h).isUniversal.isFirstOrderThickening

/-- The universal first-order thickening of `h : Z ⟶ X` is a thickening *over* `X`: its
structure morphism restricts to `h` on `Z`. -/
theorem universalFirstOrderThickening_inclusion_comp_toBase {Z X : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] :
    (universalFirstOrderThickening h).inclusion ≫ (universalFirstOrderThickening h).toBase = h :=
  (universalFirstOrderThickening h).isUniversal.inclusion_toBase

/-- The universal property of `Stacks.Thickenings.universalFirstOrderThickening`, spelled out:
every morphism `a : T ⟶ Z` out of the closed subscheme of a first-order thickening
`j : T ⟶ T'`, together with a morphism `b : T' ⟶ X` making the square commute, extends
uniquely over `X` to the ambient scheme of the universal thickening. -/
theorem universalFirstOrderThickening_existsUnique_lift {Z X : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] {T T' : Scheme.{u}} (j : T ⟶ T') (hj : IsFirstOrderThickening j)
    (a : T ⟶ Z) (b : T' ⟶ X) (hab : j ≫ b = a ≫ h) :
    ∃! a' : T' ⟶ (universalFirstOrderThickening h).ambient,
      (j ≫ a' = a ≫ (universalFirstOrderThickening h).inclusion) ∧
        (a' ≫ (universalFirstOrderThickening h).toBase = b) :=
  (universalFirstOrderThickening h).isUniversal.existsUnique_lift j hj a b hab

end Stacks.Thickenings

end
