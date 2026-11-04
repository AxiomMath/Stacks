module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing
public import StacksCore.Tactic.StacksAttribute

/-!
# Gluing locally ringed spaces

A family of locally ringed spaces, with open overlap spaces and transition isomorphisms between
them, glues to a locally ringed space. The canonical maps from the pieces are open immersions,
they cover the glued space, and they identify each prescribed overlap with the intersection of
the two corresponding charts. Morphisms out of the gluing are compatible families of morphisms
on the pieces.

This file records the description of a morphism *into* a gluing in terms of its pullbacks to the
canonical open cover: those pullbacks cover the source, the inverse image of a prescribed overlap
is exactly the intersection of two of them, and the local morphisms they carry are related on
intersections by the prescribed transition map.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.GlueData.range_overlap`: a prescribed overlap, viewed
  inside one chart, is exactly the part of that chart lying over the other chart.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.t_f_eq_restrictOverlapIso_comp`: the transition
  map is the restriction of `φ j⁻¹ ∘ φ i` to the overlap, with the inverse of `φ j` made
  explicit as the unique splitting of `φ j` over the intersection of the two charts.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.homOutEquiv`: morphisms out of the gluing are
  exactly the compatible families of morphisms on the pieces.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_pullbackCharts_jointlySurjective`: the
  pullbacks of the canonical charts cover the source of a morphism into the gluing.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_pullbackCharts_preimage_overlap`: the
  inverse image of an overlap is the intersection of two inverse-image charts.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_pullbackCharts_transition`: the transition
  compatibility of the induced local morphisms.
* `AlgebraicGeometry.LocallyRingedSpace.GlueData.range_pullback_fst_of_right`: the range of the
  first projection of a pullback along an open immersion is the inverse image of that
  immersion's range.

The glued space itself, its canonical maps and their joint surjectivity are already available:
they are `CategoryTheory.GlueData.glued`, `CategoryTheory.GlueData.ι` and
`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective`.

## References

* [Stacks Project, Tag 01JB](https://stacks.math.columbia.edu/tag/01JB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

add_to_stacks 01JB CategoryTheory.GlueData.glued
add_to_stacks 01JB CategoryTheory.GlueData.ι
add_to_stacks 01JB CategoryTheory.GlueData.glue_condition
add_to_stacks 01JB LocallyRingedSpace.GlueData.ι_isOpenImmersion
add_to_stacks 01JB LocallyRingedSpace.GlueData.ι_jointly_surjective
add_to_stacks 01JB LocallyRingedSpace.GlueData.vPullbackConeIsLimit
add_to_stacks 01JB LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right

namespace AlgebraicGeometry.LocallyRingedSpace.GlueData

section Helpers

/-- The source of the first projection of a pullback along an open immersion has, as its image in
the base space, exactly the inverse image of the open immersion's image. -/
lemma range_pullback_fst_of_right
    {X Y S : LocallyRingedSpace.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [LocallyRingedSpace.IsOpenImmersion g] :
    Set.range (pullback.fst f g).base = f.base ⁻¹' Set.range g.base := by
  let F := LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace
  have h := PreservesPullback.iso_hom_fst F f g
  let G := PresheafedSpace.forget CommRingCat
  have h' := PreservesPullback.iso_hom_fst G (F.map f) (F.map g)
  show Set.range (F.map (pullback.fst f g)).base =
    (F.map f).base ⁻¹' Set.range (F.map g).base
  have hsurj {A B : TopCat.{u}} (p : A ⟶ B) [Epi p] : Function.Surjective p :=
    (TopCat.epi_iff_surjective p).mp inferInstance
  rw [← h, PresheafedSpace.comp_base, TopCat.coe_comp, (hsurj _).range_comp]
  show Set.range (G.map (pullback.fst (F.map f) (F.map g))) =
    G.map (F.map f) ⁻¹' Set.range (G.map (F.map g))
  rw [← h', TopCat.coe_comp, (hsurj _).range_comp, TopCat.pullback_fst_range]
  ext x
  constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, hy.symm⟩

end Helpers

/-- The prescribed overlap `V i j`, viewed inside the chart `U i` through `D.f i j`, is exactly
the part of that chart lying over the chart `U j`: `φ i '' U i j = U i ∩ U j` in the glued
space, stated as an equality of subsets of `U i`. -/
@[stacks 01JB "part (2): the overlap is the intersection of two charts"]
lemma range_overlap (D : LocallyRingedSpace.GlueData.{u}) (i j : D.J) :
    Set.range (D.f i j).base = (D.ι i).base ⁻¹' Set.range (D.ι j).base := by
  let e := (D.vPullbackConeIsLimit i j).conePointUniqueUpToIso
    (limit.isLimit (cospan (D.ι i) (D.ι j)))
  have he : e.hom ≫ pullback.fst (D.ι i) (D.ι j) = D.f i j :=
    (D.vPullbackConeIsLimit i j).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (cospan (D.ι i) (D.ι j))) WalkingCospan.left
  have hsurj : Function.Surjective e.hom.base := fun z ↦ ⟨e.inv.base z, by simp⟩
  rw [← range_pullback_fst_of_right, ← he, LocallyRingedSpace.comp_base]
  exact hsurj.range_comp (pullback.fst (D.ι i) (D.ι j)).base

/-- The restriction isomorphism `U i j ≅ U i ∩ U j` carried by `φ i`: the prescribed overlap is
identified, through the chart `φ i`, with the intersection of the two charts inside the glued
space. -/
noncomputable def restrictOverlapIso (D : LocallyRingedSpace.GlueData.{u}) (i j : D.J) :
    D.V (i, j) ≅ pullback (D.ι i) (D.ι j) :=
  (D.vPullbackConeIsLimit i j).conePointUniqueUpToIso
    (limit.isLimit (cospan (D.ι i) (D.ι j)))

/-- The restriction isomorphism is `φ i` restricted to the overlap: composing it with the
inclusion of `U i ∩ U j` into the chart `U i` recovers `D.f i j`. -/
@[simp]
lemma restrictOverlapIso_hom_fst (D : LocallyRingedSpace.GlueData.{u}) (i j : D.J) :
    (D.restrictOverlapIso i j).hom ≫ pullback.fst (D.ι i) (D.ι j) = D.f i j :=
  (D.vPullbackConeIsLimit i j).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (cospan (D.ι i) (D.ι j))) WalkingCospan.left

/-- Composing the restriction isomorphism with the inclusion of `U i ∩ U j` into the chart `U j`
gives the transition map followed by `D.f j i`. -/
@[simp]
lemma restrictOverlapIso_hom_snd (D : LocallyRingedSpace.GlueData.{u}) (i j : D.J) :
    (D.restrictOverlapIso i j).hom ≫ pullback.snd (D.ι i) (D.ι j) = D.t i j ≫ D.f j i :=
  (D.vPullbackConeIsLimit i j).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (cospan (D.ι i) (D.ι j))) WalkingCospan.right

/-- The transition map is `φ j⁻¹ ∘ φ i` on the overlap: for any morphism `s : U i ∩ U j ⟶ U j`
with `s ≫ φ j` the inclusion of `U i ∩ U j` (the restriction of `φ j⁻¹` to `U i ∩ U j`), the
map `φ i j`, read in the chart `U j`, is `s` composed with the restriction isomorphism. -/
@[stacks 01JB "part (3): the transition map is the restriction of φ j⁻¹ ∘ φ i"]
theorem t_f_eq_restrictOverlapIso_comp (D : LocallyRingedSpace.GlueData.{u}) (i j : D.J)
    (s : pullback (D.ι i) (D.ι j) ⟶ D.U j)
    (hs : s ≫ D.ι j = pullback.fst (D.ι i) (D.ι j) ≫ D.ι i) :
    D.t i j ≫ D.f j i = (D.restrictOverlapIso i j).hom ≫ s := by
  have hsnd : s = pullback.snd (D.ι i) (D.ι j) := by
    rw [← cancel_mono (D.ι j), hs, pullback.condition]
  rw [hsnd, restrictOverlapIso_hom_snd]

/-- The mapping property for morphisms *out of* a gluing: a morphism `D.glued ⟶ Y` is the same
thing as a family of morphisms `D.U i ⟶ Y` agreeing on the prescribed overlaps, the agreement
being read through the transition maps. The bijection sends a morphism to the family of its
restrictions `D.ι i ≫ h`. -/
@[stacks 01JB "the mapping property for morphisms out of the glueing"]
noncomputable def homOutEquiv
    (D : LocallyRingedSpace.GlueData.{u}) (Y : LocallyRingedSpace.{u}) :
    (D.glued ⟶ Y) ≃
      { f : ∀ i, D.U i ⟶ Y //
          ∀ i j, D.f i j ≫ f i = D.t i j ≫ D.f j i ≫ f j } where
  toFun h := ⟨fun i ↦ D.ι i ≫ h, fun i j ↦ by
    calc
      D.f i j ≫ D.ι i ≫ h = (D.f i j ≫ D.ι i) ≫ h := by rw [← Category.assoc]
      _ = (D.t i j ≫ D.f j i ≫ D.ι j) ≫ h := by rw [D.glue_condition]
      _ = D.t i j ≫ D.f j i ≫ D.ι j ≫ h := by simp only [Category.assoc]⟩
  invFun F := Multicoequalizer.desc _ _ F.1 (by
    rintro ⟨i, j⟩
    change D.f i j ≫ F.1 i = (D.t i j ≫ D.f j i) ≫ F.1 j
    rw [Category.assoc]
    exact F.2 i j)
  left_inv h := by
    apply Multicoequalizer.hom_ext
    intro i
    exact Multicoequalizer.π_desc _ _ _ _ i
  right_inv F := by
    apply Subtype.ext
    funext i
    exact Multicoequalizer.π_desc D.diagram Y F.1 _ i

/-- The pullbacks of the canonical charts along a morphism into the glued space jointly cover its
source. -/
@[stacks 01JB "canonical inverse-image cover"]
theorem hom_pullbackCharts_jointlySurjective (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (g : Y ⟶ D.glued) (y : Y) :
    ∃ (i : D.J) (x : pullback (C := LocallyRingedSpace) g (D.ι i)),
      (pullback.fst g (D.ι i)).base x = y := by
  obtain ⟨i, x, hx⟩ := D.ι_jointly_surjective (g.base y)
  exact ⟨i, (Set.ext_iff.mp (range_pullback_fst_of_right g (D.ι i)) y).2 ⟨x, hx⟩⟩

/-- On the inverse-image chart indexed by `i`, the inverse image of `V i j` is exactly its
intersection with the chart indexed by `j`. -/
@[stacks 01JB "inverse images of overlaps"]
theorem hom_pullbackCharts_preimage_overlap (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (g : Y ⟶ D.glued) (i j : D.J) :
    (pullback.snd g (D.ι i)).base ⁻¹' Set.range (D.f i j).base =
      Set.range
        (pullback.fst (pullback.fst g (D.ι i))
          (pullback.fst g (D.ι j))).base := by
  rw [range_overlap, range_pullback_fst_of_right, range_pullback_fst_of_right]
  show (fun x ↦ (D.ι i).base ((pullback.snd g (D.ι i)).base x)) ⁻¹'
      Set.range (D.ι j).base =
    (fun x ↦ g.base ((pullback.fst g (D.ι i)).base x)) ⁻¹'
      Set.range (D.ι j).base
  congr 1
  funext x
  exact (ConcreteCategory.congr_hom (congrArg (fun q ↦ q.base)
    (pullback.condition (f := g) (g := D.ι i))) x).symm

/-- The local morphisms on the inverse-image charts are related on intersections by the
prescribed transition map. -/
@[stacks 01JB "transition compatibility for morphisms into the gluing"]
theorem hom_pullbackCharts_transition (D : LocallyRingedSpace.GlueData.{u})
    {Y : LocallyRingedSpace.{u}} (g : Y ⟶ D.glued) (i j : D.J) :
    ∃! k : pullback (pullback.fst g (D.ι i)) (pullback.fst g (D.ι j)) ⟶ D.V (i, j),
      k ≫ D.f i j =
          pullback.fst (pullback.fst g (D.ι i)) (pullback.fst g (D.ι j)) ≫
            pullback.snd g (D.ι i) ∧
        k ≫ D.t i j ≫ D.f j i =
          pullback.snd (pullback.fst g (D.ι i)) (pullback.fst g (D.ι j)) ≫
            pullback.snd g (D.ι j) := by
  let P := pullback (pullback.fst g (D.ι i)) (pullback.fst g (D.ι j))
  let a : P ⟶ D.U i := pullback.fst _ _ ≫ pullback.snd g (D.ι i)
  let b : P ⟶ D.U j := pullback.snd _ _ ≫ pullback.snd g (D.ι j)
  have hab : a ≫ D.ι i = b ≫ D.ι j := by
    dsimp [a, b]
    simp only [Category.assoc]
    rw [← pullback.condition, ← pullback.condition]
    rw [← Category.assoc, pullback.condition]
    simp only [Category.assoc]
  let s : PullbackCone (D.ι i) (D.ι j) := PullbackCone.mk a b hab
  let k := (D.vPullbackConeIsLimit i j).lift s
  refine ⟨k, ⟨(D.vPullbackConeIsLimit i j).fac s WalkingCospan.left,
    (D.vPullbackConeIsLimit i j).fac s WalkingCospan.right⟩, ?_⟩
  · intro l hl
    apply PullbackCone.IsLimit.hom_ext (D.vPullbackConeIsLimit i j)
    · exact hl.1.trans ((D.vPullbackConeIsLimit i j).fac s WalkingCospan.left).symm
    · exact hl.2.trans ((D.vPullbackConeIsLimit i j).fac s WalkingCospan.right).symm

end AlgebraicGeometry.LocallyRingedSpace.GlueData

end
