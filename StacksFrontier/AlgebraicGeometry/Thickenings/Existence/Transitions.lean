module

public import StacksFrontier.AlgebraicGeometry.Thickenings.Existence.Overlaps

/-!
# Existence of the universal first-order thickening: transition isomorphisms

This file constructs the transition isomorphisms between the thickenings of the double and
triple overlaps of an open cover, and proves the compatibilities of them with the inclusions and
the structure morphisms that the gluing data needs.

## References

* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- The inclusion of a triple overlap thickening into the double overlap thickening given by its
second index. -/
noncomputable def tripleToOverlapLeft {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).ambient ⟶
      (overlapRestriction 𝒰 h A i j).ambient := by
  let e := thickeningHomeomorph (A i).inclusion
    (A i).isUniversal.isFirstOrderThickening.isThickening
  have hle : thickeningOpenImage (A i).inclusion
      (A i).isUniversal.isFirstOrderThickening.isThickening (sourceTriple 𝒰 i j k) ≤
      thickeningOpenImage (A i).inclusion
        (A i).isUniversal.isFirstOrderThickening.isThickening (sourceOverlap 𝒰 i j) := by
    apply SetLike.coe_subset_coe.mpr
    change e '' (sourceOverlap 𝒰 i j ⊓ sourceOverlap 𝒰 i k) ⊆
      e '' sourceOverlap 𝒰 i j
    exact Set.image_mono inf_le_left
  exact (A i).ambient.homOfLE hle

/-- `tripleToOverlapLeft` is compatible with the maps to the chart's thickening. -/
private lemma tripleToOverlapLeft_fac {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    tripleToOverlapLeft 𝒰 h A i j k ≫
        overlapRestrictionMap 𝒰 h A i j =
      tripleRestrictionMap 𝒰 h A i j k := by
  dsimp [tripleToOverlapLeft, overlapRestrictionMap,
    tripleRestrictionMap]
  exact Scheme.homOfLE_ι (A i).ambient _

/-- `tripleToOverlapLeft` is a morphism over the base. -/
lemma tripleToOverlapLeft_toBase {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    tripleToOverlapLeft 𝒰 h A i j k ≫
        (overlapRestriction 𝒰 h A i j).toBase =
      (tripleRestriction 𝒰 h A i j k).toBase := by
  calc
    tripleToOverlapLeft 𝒰 h A i j k ≫
        (overlapRestriction 𝒰 h A i j).toBase =
        tripleToOverlapLeft 𝒰 h A i j k ≫
          overlapRestrictionMap 𝒰 h A i j ≫ (A i).toBase := by rfl
    _ = tripleRestrictionMap 𝒰 h A i j k ≫ (A i).toBase := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ (A i).toBase)
          (tripleToOverlapLeft_fac 𝒰 h A i j k)
    _ = (tripleRestriction 𝒰 h A i j k).toBase := by rfl

/-- The inclusion of a triple overlap thickening into the double overlap thickening given by its
third index. -/
private noncomputable def tripleToOverlapRight {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).ambient ⟶
      (overlapRestriction 𝒰 h A i k).ambient := by
  let e := thickeningHomeomorph (A i).inclusion
    (A i).isUniversal.isFirstOrderThickening.isThickening
  have hle : thickeningOpenImage (A i).inclusion
      (A i).isUniversal.isFirstOrderThickening.isThickening (sourceTriple 𝒰 i j k) ≤
      thickeningOpenImage (A i).inclusion
        (A i).isUniversal.isFirstOrderThickening.isThickening (sourceOverlap 𝒰 i k) := by
    apply SetLike.coe_subset_coe.mpr
    change e '' (sourceOverlap 𝒰 i j ⊓ sourceOverlap 𝒰 i k) ⊆
      e '' sourceOverlap 𝒰 i k
    exact Set.image_mono inf_le_right
  exact (A i).ambient.homOfLE hle

/-- `tripleToOverlapRight` is compatible with the maps to the chart's thickening. -/
private lemma tripleToOverlapRight_fac {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    tripleToOverlapRight 𝒰 h A i j k ≫
        overlapRestrictionMap 𝒰 h A i k =
      tripleRestrictionMap 𝒰 h A i j k := by
  dsimp [tripleToOverlapRight, overlapRestrictionMap,
    tripleRestrictionMap]
  exact Scheme.homOfLE_ι (A i).ambient _

/-- A triple overlap thickening has the same image as the fibre product of the two double overlap
thickenings. -/
lemma tripleRestrictionMap_range_eq {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    Set.range (tripleRestrictionMap 𝒰 h A i j k).base =
      Set.range (pullback.fst (overlapRestrictionMap 𝒰 h A i j)
        (overlapRestrictionMap 𝒰 h A i k) ≫
          overlapRestrictionMap 𝒰 h A i j).base := by
  let f₁ := overlapRestrictionMap 𝒰 h A i j
  let f₂ := overlapRestrictionMap 𝒰 h A i k
  have : IsOpenImmersion f₁ := isOpenImmersion_overlapRestrictionMap 𝒰 h A i j
  have : IsOpenImmersion f₂ := isOpenImmersion_overlapRestrictionMap 𝒰 h A i k
  have : IsOpenImmersion (pullback.fst f₁ f₂) := inferInstance
  have : IsOpenImmersion (pullback.fst f₁ f₂ ≫ f₁) := inferInstance
  have hrangeO : (tripleRestrictionMap 𝒰 h A i j k).opensRange =
      (pullback.fst f₁ f₂ ≫ f₁).opensRange := by
    calc
      (tripleRestrictionMap 𝒰 h A i j k).opensRange =
          f₁.opensRange ⊓ f₂.opensRange := tripleRestrictionMap_opensRange 𝒰 h A i j k
      _ = (pullback.fst f₁ f₂ ≫ f₁).opensRange := by
        rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_pullbackFst,
          f₁.image_preimage_eq_opensRange_inf]
  simpa only [Scheme.Hom.coe_opensRange] using
    congrArg (fun V : (A i).ambient.Opens => (V : Set (A i).ambient)) hrangeO

/-- A triple overlap thickening is the fibre product of the two double overlap thickenings. This
is the identification required to state the cocycle condition of the gluing data. -/
noncomputable def tripleIsoPullback {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).ambient ≅
      pullback (overlapRestrictionMap 𝒰 h A i j)
        (overlapRestrictionMap 𝒰 h A i k) :=
  IsOpenImmersion.isoOfRangeEq (tripleRestrictionMap 𝒰 h A i j k)
    (pullback.fst (overlapRestrictionMap 𝒰 h A i j)
      (overlapRestrictionMap 𝒰 h A i k) ≫
        overlapRestrictionMap 𝒰 h A i j)
    (tripleRestrictionMap_range_eq 𝒰 h A i j k)

/-- `tripleIsoPullback` is compatible with the first projection. -/
lemma tripleIsoPullback_fst {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleIsoPullback 𝒰 h A i j k).hom ≫
        pullback.fst (overlapRestrictionMap 𝒰 h A i j)
          (overlapRestrictionMap 𝒰 h A i k) =
      tripleToOverlapLeft 𝒰 h A i j k := by
  apply (cancel_mono (overlapRestrictionMap 𝒰 h A i j)).mp
  calc
    ((tripleIsoPullback 𝒰 h A i j k).hom ≫
        pullback.fst (overlapRestrictionMap 𝒰 h A i j)
          (overlapRestrictionMap 𝒰 h A i k)) ≫
        overlapRestrictionMap 𝒰 h A i j =
        tripleRestrictionMap 𝒰 h A i j k := by
          rw [Category.assoc]
          change (IsOpenImmersion.isoOfRangeEq
            (tripleRestrictionMap 𝒰 h A i j k)
            (pullback.fst (overlapRestrictionMap 𝒰 h A i j)
              (overlapRestrictionMap 𝒰 h A i k) ≫
                overlapRestrictionMap 𝒰 h A i j)
            (tripleRestrictionMap_range_eq 𝒰 h A i j k)).hom ≫ _ = _
          exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    _ = tripleToOverlapLeft 𝒰 h A i j k ≫
          overlapRestrictionMap 𝒰 h A i j := by
          rw [tripleToOverlapLeft_fac]

/-- `tripleIsoPullback` is compatible with the second projection. -/
private lemma tripleIsoPullback_snd {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleIsoPullback 𝒰 h A i j k).hom ≫
        pullback.snd (overlapRestrictionMap 𝒰 h A i j)
          (overlapRestrictionMap 𝒰 h A i k) =
      tripleToOverlapRight 𝒰 h A i j k := by
  let e := (tripleIsoPullback 𝒰 h A i j k).hom
  let f₁ := overlapRestrictionMap 𝒰 h A i j
  let f₂ := overlapRestrictionMap 𝒰 h A i k
  have hfst : e ≫ pullback.fst f₁ f₂ = tripleToOverlapLeft 𝒰 h A i j k := by
    simpa [e, f₁, f₂] using tripleIsoPullback_fst 𝒰 h A i j k
  have hcondition : e ≫ (pullback.fst f₁ f₂ ≫ f₁) =
      e ≫ (pullback.snd f₁ f₂ ≫ f₂) :=
    congrArg (fun f => e ≫ f) (pullback.condition (f := f₁) (g := f₂))
  have : IsOpenImmersion f₂ := isOpenImmersion_overlapRestrictionMap 𝒰 h A i k
  apply (cancel_mono (overlapRestrictionMap 𝒰 h A i k)).mp
  calc
    (e ≫ pullback.snd f₁ f₂) ≫ f₂ = (e ≫ pullback.fst f₁ f₂) ≫ f₁ := by
      simpa only [Category.assoc] using hcondition.symm
    _ = tripleToOverlapLeft 𝒰 h A i j k ≫ f₁ :=
      congrArg (fun f => f ≫ f₁) hfst
    _ = tripleRestrictionMap 𝒰 h A i j k :=
      tripleToOverlapLeft_fac 𝒰 h A i j k
    _ = tripleToOverlapRight 𝒰 h A i j k ≫ f₂ :=
      (tripleToOverlapRight_fac 𝒰 h A i j k).symm

/-- The inverse of `tripleIsoPullback` composed with the open immersion into the chart's
thickening is the first projection of the fibre product. -/
private lemma tripleIsoPullback_inv_comp_tripleRestrictionMap
    {Z X : Scheme.{u}} (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleIsoPullback 𝒰 h A i j k).inv ≫
        tripleRestrictionMap 𝒰 h A i j k =
      pullback.fst (overlapRestrictionMap 𝒰 h A i j)
        (overlapRestrictionMap 𝒰 h A i k) ≫
          overlapRestrictionMap 𝒰 h A i j := by
  apply (cancel_epi (tripleIsoPullback 𝒰 h A i j k).hom).mp
  calc
    (tripleIsoPullback 𝒰 h A i j k).hom ≫
        (tripleIsoPullback 𝒰 h A i j k).inv ≫
          tripleRestrictionMap 𝒰 h A i j k =
      tripleRestrictionMap 𝒰 h A i j k := by simp
    _ = tripleToOverlapLeft 𝒰 h A i j k ≫
          overlapRestrictionMap 𝒰 h A i j :=
      (tripleToOverlapLeft_fac 𝒰 h A i j k).symm
    _ = (tripleIsoPullback 𝒰 h A i j k).hom ≫
          pullback.fst (overlapRestrictionMap 𝒰 h A i j)
            (overlapRestrictionMap 𝒰 h A i k) ≫
          overlapRestrictionMap 𝒰 h A i j :=
      (congrArg (fun f => f ≫ overlapRestrictionMap 𝒰 h A i j)
        (tripleIsoPullback_fst 𝒰 h A i j k)).symm

/-- Congruence for a composite of three morphisms in its middle factor. -/
lemma comp_congr_middle {A B C D : Scheme.{u}} (a : A ⟶ B)
    {f g : B ⟶ C} (h : f = g) (b : C ⟶ D) :
    a ≫ f ≫ b = a ≫ g ≫ b := by rw [h]

/-- Swapping the last two indices of a triple overlap thickening is compatible with the maps to the
chart's thickening. -/
private lemma tripleIsoPullback_swap_comp_map {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleIsoPullback 𝒰 h A i j k).hom ≫
        (pullbackSymmetry (overlapRestrictionMap 𝒰 h A i j)
          (overlapRestrictionMap 𝒰 h A i k)).hom ≫
        (tripleIsoPullback 𝒰 h A i k j).inv ≫ tripleRestrictionMap 𝒰 h A i k j =
      tripleRestrictionMap 𝒰 h A i j k := by
  let e := tripleIsoPullback 𝒰 h A i j k
  let e' := tripleIsoPullback 𝒰 h A i k j
  let s := pullbackSymmetry (overlapRestrictionMap 𝒰 h A i j)
    (overlapRestrictionMap 𝒰 h A i k)
  calc
    e.hom ≫ s.hom ≫ e'.inv ≫
        tripleRestrictionMap 𝒰 h A i k j =
      e.hom ≫ s.hom ≫
        pullback.fst (overlapRestrictionMap 𝒰 h A i k)
          (overlapRestrictionMap 𝒰 h A i j) ≫
        overlapRestrictionMap 𝒰 h A i k := by
          rw [tripleIsoPullback_inv_comp_tripleRestrictionMap]
    _ = e.hom ≫ pullback.snd (overlapRestrictionMap 𝒰 h A i j)
          (overlapRestrictionMap 𝒰 h A i k) ≫
            overlapRestrictionMap 𝒰 h A i k := by
          have hs : s.hom ≫ pullback.fst
              (overlapRestrictionMap 𝒰 h A i k)
              (overlapRestrictionMap 𝒰 h A i j) =
              pullback.snd (overlapRestrictionMap 𝒰 h A i j)
                (overlapRestrictionMap 𝒰 h A i k) := by
            simp [s]
          exact comp_congr_middle e.hom hs (overlapRestrictionMap 𝒰 h A i k)
    _ = tripleToOverlapRight 𝒰 h A i j k ≫
          overlapRestrictionMap 𝒰 h A i k :=
          eq_whisker
            (tripleIsoPullback_snd 𝒰 h A i j k)
            (overlapRestrictionMap 𝒰 h A i k)
    _ = tripleRestrictionMap 𝒰 h A i j k :=
          tripleToOverlapRight_fac 𝒰 h A i j k

/-- Swapping the last two indices of a triple overlap thickening is a morphism over the base. -/
private lemma tripleIsoPullback_swap_toBase {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h))
    (i j k : 𝒰.I₀) :
    (tripleIsoPullback 𝒰 h A i j k).hom ≫
        (pullbackSymmetry (overlapRestrictionMap 𝒰 h A i j)
          (overlapRestrictionMap 𝒰 h A i k)).hom ≫
        (tripleIsoPullback 𝒰 h A i k j).inv ≫
        (tripleRestriction 𝒰 h A i k j).toBase =
      (tripleRestriction 𝒰 h A i j k).toBase := by
  let e := tripleIsoPullback 𝒰 h A i j k
  let e' := tripleIsoPullback 𝒰 h A i k j
  let s := pullbackSymmetry (overlapRestrictionMap 𝒰 h A i j)
    (overlapRestrictionMap 𝒰 h A i k)
  have hmap := tripleIsoPullback_swap_comp_map 𝒰 h A i j k
  calc
    e.hom ≫ s.hom ≫ e'.inv ≫
        (tripleRestriction 𝒰 h A i k j).toBase =
      e.hom ≫ s.hom ≫ e'.inv ≫
        tripleRestrictionMap 𝒰 h A i k j ≫ (A i).toBase := by rfl
    _ = tripleRestrictionMap 𝒰 h A i j k ≫ (A i).toBase :=
      congrArg (fun f => f ≫ (A i).toBase) hmap
    _ = (tripleRestriction 𝒰 h A i j k).toBase := by rfl

/-- The inclusion of a double overlap into its thickening, followed by the open immersion into
the chart's thickening. -/
@[reassoc]
lemma overlapRestriction_inclusion_comp_map {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j : 𝒰.I₀) :
    (overlapRestriction 𝒰 h A i j).inclusion ≫
        overlapRestrictionMap 𝒰 h A i j =
      (sourceOverlap 𝒰 i j).ι ≫ (A i).inclusion := by
  dsimp [overlapRestriction, overlapRestrictionMap]
  exact Scheme.Hom.resLE_comp_ι (A i).inclusion
    (U := thickeningOpenImage (A i).inclusion (A i).isUniversal.isFirstOrderThickening.isThickening
      (sourceOverlap 𝒰 i j))
    (V := sourceOverlap 𝒰 i j) (by
      rw [preimage_thickeningOpenImage])

/-- The inclusion of a triple overlap into its thickening, followed by the open immersion into
the chart's thickening. -/
private lemma tripleRestriction_inclusion_comp_map {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).inclusion ≫
        tripleRestrictionMap 𝒰 h A i j k =
      (sourceTriple 𝒰 i j k).ι ≫ (A i).inclusion := by
  dsimp [tripleRestriction, tripleRestrictionMap,
    restrictUniversalThickening]
  exact Scheme.Hom.resLE_comp_ι (A i).inclusion
    (U := thickeningOpenImage (A i).inclusion
      (A i).isUniversal.isFirstOrderThickening.isThickening (sourceTriple 𝒰 i j k))
    (V := sourceTriple 𝒰 i j k) (by rw [preimage_thickeningOpenImage])

/-- `tripleToOverlapLeft` is compatible with the inclusions of the overlaps. -/
lemma tripleToOverlapLeft_inclusion {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).inclusion ≫
        tripleToOverlapLeft 𝒰 h A i j k =
      (𝒰.X i).homOfLE (sourceTriple_le_sourceOverlap 𝒰 i j k) ≫
        (overlapRestriction 𝒰 h A i j).inclusion := by
  have : IsClosedImmersion (A i).inclusion :=
    (A i).isUniversal.isFirstOrderThickening.1
  apply (cancel_mono (overlapRestrictionMap 𝒰 h A i j)).mp
  calc
    (tripleRestriction 𝒰 h A i j k).inclusion ≫
        tripleToOverlapLeft 𝒰 h A i j k ≫
          overlapRestrictionMap 𝒰 h A i j =
      (tripleRestriction 𝒰 h A i j k).inclusion ≫
        tripleRestrictionMap 𝒰 h A i j k := by
          rw [tripleToOverlapLeft_fac]
    _ = (sourceTriple 𝒰 i j k).ι ≫ (A i).inclusion :=
      tripleRestriction_inclusion_comp_map 𝒰 h A i j k
    _ = (𝒰.X i).homOfLE (sourceTriple_le_sourceOverlap 𝒰 i j k) ≫
        (sourceOverlap 𝒰 i j).ι ≫ (A i).inclusion := by
          simpa only [Category.assoc] using congrArg
            (fun g => g ≫ (A i).inclusion)
            (Scheme.homOfLE_ι (𝒰.X i)
              (sourceTriple_le_sourceOverlap 𝒰 i j k)).symm
    _ = (𝒰.X i).homOfLE (sourceTriple_le_sourceOverlap 𝒰 i j k) ≫
        (overlapRestriction 𝒰 h A i j).inclusion ≫
          overlapRestrictionMap 𝒰 h A i j := by
          rw [overlapRestriction_inclusion_comp_map]

/-- The structure morphism of a double overlap thickening is that of the chart's thickening. -/
lemma overlapRestrictionMap_comp_toBase {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j : 𝒰.I₀) :
    overlapRestrictionMap 𝒰 h A i j ≫ (A i).toBase =
      (overlapRestriction 𝒰 h A i j).toBase := by
  rfl

/-- The transition isomorphism of the gluing data: the canonical identification of the two double
overlap thickenings attached to a pair of charts. -/
noncomputable def overlapTransition {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j : 𝒰.I₀) :
    (overlapRestriction 𝒰 h A i j).ambient ≅
      (overlapRestriction 𝒰 h A j i).ambient := by
  classical
  by_cases hij : i = j
  · subst j
    exact Iso.refl _
  · let e := sourceOverlapIso 𝒰 i j
    have heqZ : e.hom ≫ ((sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j) =
        (sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i :=
      IsOpenImmersion.isoOfRangeEq_hom_fac
        ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i)
        ((sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j) (sourceOverlap_range 𝒰 i j)
    have heq : e.hom ≫ ((sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j ≫ h) =
        (sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i ≫ h := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ h) heqZ
    have hright := isUniversalFirstOrderThickening_comp_iso e
      ((sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j ≫ h)
      (overlapRestriction 𝒰 h A j i).inclusion
      (overlapRestriction 𝒰 h A j i).toBase
      (overlapRestriction 𝒰 h A j i).isUniversal
    have hright' : IsUniversalFirstOrderThickening
        ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i ≫ h)
        (e.hom ≫ (overlapRestriction 𝒰 h A j i).inclusion)
        ((overlapRestriction 𝒰 h A j i).toBase) :=
      heq ▸ hright
    exact isoOfIsUniversal
      ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i ≫ h)
      (overlapRestriction 𝒰 h A i j).inclusion
      (overlapRestriction 𝒰 h A i j).toBase
      (e.hom ≫ (overlapRestriction 𝒰 h A j i).inclusion)
      (overlapRestriction 𝒰 h A j i).toBase
      (overlapRestriction 𝒰 h A i j).isUniversal hright'

/-- `overlapTransition` is compatible with the inclusions of the overlaps and with the base. -/
private lemma overlapTransition_inclusion_and_toBase {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j : 𝒰.I₀) :
    (overlapRestriction 𝒰 h A i j).inclusion ≫
        (overlapTransition 𝒰 h A i j).hom =
      (sourceOverlapIso 𝒰 i j).hom ≫
        (overlapRestriction 𝒰 h A j i).inclusion ∧
    (overlapTransition 𝒰 h A i j).hom ≫
        (overlapRestriction 𝒰 h A j i).toBase =
      (overlapRestriction 𝒰 h A i j).toBase := by
  classical
  by_cases hij : i = j
  · subst j
    constructor <;> simp [overlapTransition, sourceOverlapIso_self]
  · let e := sourceOverlapIso 𝒰 i j
    have heqZ : e.hom ≫ ((sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j) =
        (sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i :=
      IsOpenImmersion.isoOfRangeEq_hom_fac
        ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i)
        ((sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j) (sourceOverlap_range 𝒰 i j)
    have heq : e.hom ≫ ((sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j ≫ h) =
        (sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i ≫ h := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ h) heqZ
    let Hleft := overlapRestriction 𝒰 h A i j
    let Hright := overlapRestriction 𝒰 h A j i
    have hright := isUniversalFirstOrderThickening_comp_iso e
      ((sourceOverlap 𝒰 j i).ι ≫ 𝒰.f j ≫ h) Hright.inclusion Hright.toBase
      Hright.isUniversal
    have hright' : IsUniversalFirstOrderThickening
        ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i ≫ h)
        (e.hom ≫ Hright.inclusion) Hright.toBase :=
      heq ▸ hright
    have hf := isoOfIsUniversal_hom_fac
      ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i ≫ h)
      Hleft.inclusion Hleft.toBase (e.hom ≫ Hright.inclusion) Hright.toBase
      Hleft.isUniversal hright'
    have hb := isoOfIsUniversal_hom_toBase
      ((sourceOverlap 𝒰 i j).ι ≫ 𝒰.f i ≫ h)
      Hleft.inclusion Hleft.toBase (e.hom ≫ Hright.inclusion) Hright.toBase
      Hleft.isUniversal hright'
    exact ⟨by simpa [overlapTransition, hij, e, Hleft, Hright, hright, hright'] using hf,
      by simpa [overlapTransition, hij, e, Hleft, Hright, hright, hright'] using hb⟩

/-- `overlapTransition` is compatible with the inclusions of the overlaps. -/
@[reassoc]
lemma overlapTransition_inclusion {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j : 𝒰.I₀) :
    (overlapRestriction 𝒰 h A i j).inclusion ≫
        (overlapTransition 𝒰 h A i j).hom =
      (sourceOverlapIso 𝒰 i j).hom ≫
        (overlapRestriction 𝒰 h A j i).inclusion :=
  (overlapTransition_inclusion_and_toBase 𝒰 h A i j).1

/-- `overlapTransition` is a morphism over the base. -/
lemma overlapTransition_toBase {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j : 𝒰.I₀) :
    (overlapTransition 𝒰 h A i j).hom ≫
        (overlapRestriction 𝒰 h A j i).toBase =
      (overlapRestriction 𝒰 h A i j).toBase :=
  (overlapTransition_inclusion_and_toBase 𝒰 h A i j).2

/-- The overlap of a chart with itself is everything. -/
private lemma sourceOverlap_self {Z : Scheme.{u}} (𝒰 : Z.OpenCover) (i : 𝒰.I₀) :
    sourceOverlap 𝒰 i i = ⊤ := by
  ext z
  simp [sourceOverlap]

/-- The thickening of the overlap of a chart with itself is all of the chart's thickening. -/
lemma overlapRestrictionMap_self_opensRange {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i : 𝒰.I₀) :
    (overlapRestrictionMap 𝒰 h A i i).opensRange = ⊤ := by
  have : IsOpenImmersion (overlapRestrictionMap 𝒰 h A i i) :=
    isOpenImmersion_overlapRestrictionMap 𝒰 h A i i
  change Scheme.Hom.opensRange
      ((thickeningOpenImage (A i).inclusion
        (A i).isUniversal.isFirstOrderThickening.isThickening (sourceOverlap 𝒰 i i)).ι) = ⊤
  rw [Scheme.Opens.opensRange_ι]
  rw [sourceOverlap_self]
  apply SetLike.coe_injective
  change (thickeningHomeomorph (A i).inclusion
      (A i).isUniversal.isFirstOrderThickening.isThickening) '' (Set.univ : Set (𝒰.X i)) = Set.univ
  exact Set.image_univ_of_surjective
    (thickeningHomeomorph (A i).inclusion
      (A i).isUniversal.isFirstOrderThickening.isThickening).surjective

/-- `tripleTransition` is compatible with the inclusions of the triple overlaps and with the
base. -/
private lemma tripleTransition_inclusion_and_toBase {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).inclusion ≫
        (tripleTransition 𝒰 h A i j k).hom =
      (sourceTripleIso 𝒰 i j k).hom ≫
        (tripleRestriction 𝒰 h A j i k).inclusion ∧
    (tripleTransition 𝒰 h A i j k).hom ≫
        (tripleRestriction 𝒰 h A j i k).toBase =
      (tripleRestriction 𝒰 h A i j k).toBase := by
  let e := sourceTripleIso 𝒰 i j k
  have heqZ : e.hom ≫ ((sourceTriple 𝒰 j i k).ι ≫ 𝒰.f j) =
      (sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i :=
    sourceTripleIso_hom_fac 𝒰 i j k
  have heq : e.hom ≫ ((sourceTriple 𝒰 j i k).ι ≫ 𝒰.f j ≫ h) =
      (sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i ≫ h := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ h) heqZ
  let Hleft := tripleRestriction 𝒰 h A i j k
  let Hright := tripleRestriction 𝒰 h A j i k
  have hright := isUniversalFirstOrderThickening_comp_iso e
    ((sourceTriple 𝒰 j i k).ι ≫ 𝒰.f j ≫ h) Hright.inclusion Hright.toBase
    Hright.isUniversal
  have hright' : IsUniversalFirstOrderThickening
      ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i ≫ h)
      (e.hom ≫ Hright.inclusion) Hright.toBase :=
    heq ▸ hright
  have hf := isoOfIsUniversal_hom_fac
    ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i ≫ h)
    Hleft.inclusion Hleft.toBase (e.hom ≫ Hright.inclusion) Hright.toBase
    Hleft.isUniversal hright'
  have hb := isoOfIsUniversal_hom_toBase
    ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i ≫ h)
    Hleft.inclusion Hleft.toBase (e.hom ≫ Hright.inclusion) Hright.toBase
    Hleft.isUniversal hright'
  exact ⟨by simpa [tripleTransition, e, Hleft, Hright, hright, hright'] using hf,
    by simpa [tripleTransition, e, Hleft, Hright, hright, hright'] using hb⟩

/-- `tripleTransition` is compatible with the inclusions of the triple overlaps. -/
@[reassoc]
lemma tripleTransition_inclusion {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).inclusion ≫
        (tripleTransition 𝒰 h A i j k).hom =
      (sourceTripleIso 𝒰 i j k).hom ≫
        (tripleRestriction 𝒰 h A j i k).inclusion :=
  (tripleTransition_inclusion_and_toBase 𝒰 h A i j k).1

/-- `tripleTransition` is a morphism over the base. -/
lemma tripleTransition_toBase {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleTransition 𝒰 h A i j k).hom ≫
        (tripleRestriction 𝒰 h A j i k).toBase =
      (tripleRestriction 𝒰 h A i j k).toBase :=
  (tripleTransition_inclusion_and_toBase 𝒰 h A i j k).2

/-- Swapping the last two indices of a triple overlap thickening is compatible with the
inclusions. -/
@[reassoc]
private lemma tripleIsoPullback_swap_inclusion {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).inclusion ≫
      (tripleIsoPullback 𝒰 h A i j k).hom ≫
      (pullbackSymmetry (overlapRestrictionMap 𝒰 h A i j)
        (overlapRestrictionMap 𝒰 h A i k)).hom ≫
      (tripleIsoPullback 𝒰 h A i k j).inv =
    (𝒰.X i).homOfLE (sourceTriple_swap 𝒰 i j k).le ≫
      (tripleRestriction 𝒰 h A i k j).inclusion := by
  apply (cancel_mono (tripleRestrictionMap 𝒰 h A i k j)).mp
  simp only [Category.assoc]
  rw [tripleIsoPullback_swap_comp_map, tripleRestriction_inclusion_comp_map,
    tripleRestriction_inclusion_comp_map]
  simp [← Category.assoc, Scheme.homOfLE_ι]

/-- The loop of triple transitions `ijk → jki → kij → ijk` around a triple overlap thickening. -/
noncomputable def tripleCycle {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).ambient ⟶ (tripleRestriction 𝒰 h A i j k).ambient :=
  (tripleTransition 𝒰 h A i j k).hom ≫
    ((tripleIsoPullback 𝒰 h A j i k).hom ≫
      (pullbackSymmetry (overlapRestrictionMap 𝒰 h A j i)
        (overlapRestrictionMap 𝒰 h A j k)).hom ≫
      (tripleIsoPullback 𝒰 h A j k i).inv) ≫
    (tripleTransition 𝒰 h A j k i).hom ≫
    ((tripleIsoPullback 𝒰 h A k j i).hom ≫
      (pullbackSymmetry (overlapRestrictionMap 𝒰 h A k j)
        (overlapRestrictionMap 𝒰 h A k i)).hom ≫
      (tripleIsoPullback 𝒰 h A k i j).inv) ≫
    (tripleTransition 𝒰 h A k i j).hom ≫
    ((tripleIsoPullback 𝒰 h A i k j).hom ≫
      (pullbackSymmetry (overlapRestrictionMap 𝒰 h A i k)
        (overlapRestrictionMap 𝒰 h A i j)).hom ≫
      (tripleIsoPullback 𝒰 h A i j k).inv)

/-- `tripleCycle` is compatible with the inclusion of the triple overlap. -/
lemma inclusion_tripleCycle {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    (tripleRestriction 𝒰 h A i j k).inclusion ≫ tripleCycle 𝒰 h A i j k =
      (tripleRestriction 𝒰 h A i j k).inclusion := by
  let r :=
    (sourceTripleIso 𝒰 i j k).hom ≫
    (𝒰.X j).homOfLE (sourceTriple_swap 𝒰 j i k).le ≫
    (sourceTripleIso 𝒰 j k i).hom ≫
    (𝒰.X k).homOfLE (sourceTriple_swap 𝒰 k j i).le ≫
    (sourceTripleIso 𝒰 k i j).hom ≫
    (𝒰.X i).homOfLE (sourceTriple_swap 𝒰 i k j).le
  have hr : r = 𝟙 _ := by
    apply (cancel_mono ((sourceTriple 𝒰 i j k).ι ≫ 𝒰.f i)).mp
    dsimp [r]
    simp only [Category.assoc, Scheme.homOfLE_ι_assoc,
      sourceTripleIso_hom_fac, Category.id_comp]
  have hi : (tripleRestriction 𝒰 h A i j k).inclusion ≫ tripleCycle 𝒰 h A i j k =
      r ≫ (tripleRestriction 𝒰 h A i j k).inclusion := by
    dsimp [tripleCycle, r]
    simp only [Category.assoc]
    simp only [tripleTransition_inclusion_assoc,
      tripleIsoPullback_swap_inclusion_assoc,
      tripleIsoPullback_swap_inclusion]
  simpa [hr] using hi

/-- `tripleCycle` is a morphism over the base. -/
lemma tripleCycle_toBase {Z X : Scheme.{u}}
    (𝒰 : Z.OpenCover) (h : Z ⟶ X)
    (A : ∀ i, UniversalFirstOrderThickening (𝒰.f i ≫ h)) (i j k : 𝒰.I₀) :
    tripleCycle 𝒰 h A i j k ≫ (tripleRestriction 𝒰 h A i j k).toBase =
      (tripleRestriction 𝒰 h A i j k).toBase := by
  simp only [tripleCycle, Category.assoc]
  rw [tripleIsoPullback_swap_toBase 𝒰 h A i k j, tripleTransition_toBase 𝒰 h A k i j,
    tripleIsoPullback_swap_toBase 𝒰 h A k j i, tripleTransition_toBase 𝒰 h A j k i,
    tripleIsoPullback_swap_toBase 𝒰 h A j i k, tripleTransition_toBase 𝒰 h A i j k]

end Stacks.Thickenings

end
