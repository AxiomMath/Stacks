module

public import StacksFrontier.AlgebraicGeometry.Spaces.Category

/-!
# Base change of an étale chart presentation along a morphism of the base

Let `U` be a presheaf on the big fppf site of `S` with a morphism `π : U ⟶ h_T` to a represented
presheaf, and let `j : T' ⟶ T` be a morphism of the site.  The base change `U' = U ×_T T'` is the
presheaf `pullback π (yoneda.map j)`.  For a morphism `v : h_V ⟶ U` out of a represented presheaf
the base change `V ×_U U'` is represented by the fibre product `V ×_T T'` formed in the site, and
this file records the cartesian square that says so.  For an étale chart `w : h_W ⟶ U` with
kernel pair `s, t : R ⟶ W` the base changes `W' = W ×_T T'` and `R' = R ×_T T'` give again a
chart with its kernel pair.

## Main definitions

* `AlgebraicGeometry.Space.levelChartBase`: the morphism `V ⟶ T` underlying `v ≫ π`.
* `AlgebraicGeometry.Space.levelChart`: the object `V ×_T T'` of the site.
* `AlgebraicGeometry.Space.levelChartMap`: its morphism to `U ×_T T'`.
* `AlgebraicGeometry.Space.levelKernelMap`: the morphism `R ×_T T' ⟶ W ×_T T'` induced by a
  morphism `R ⟶ W` over `U`.

## Main results

* `AlgebraicGeometry.Space.isPullback_levelChart`: the square exhibiting `h_{V ×_T T'}` as
  `h_V ×_U (U ×_T T')`.
* `AlgebraicGeometry.Space.isPullback_levelKernel`: the base changes of the kernel pair of a chart
  form the kernel pair of the base-changed chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS} (π : U ⟶ yoneda.obj T)

/-- The morphism of the site underlying `v ≫ π`. -/
def levelChartBase {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ U) : V ⟶ T :=
  yoneda.preimage (v ≫ π)

/-- The image of `levelChartBase π v` under the Yoneda embedding is `v ≫ π`. -/
@[simp]
theorem yoneda_map_levelChartBase {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ U) :
    yoneda.map (levelChartBase π v) = v ≫ π :=
  yoneda.map_preimage _

/-- The base change `V ×_T T'` of a chart along `j : T' ⟶ T`, as an object of the site. -/
abbrev levelChart {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ U) {T' : BigFppfOver B S hS}
    (j : T' ⟶ T) : BigFppfOver B S hS :=
  pullback (levelChartBase π v) j

/-- The morphism `h_{V ×_T T'} ⟶ U ×_T T'`. -/
def levelChartMap {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ U) {T' : BigFppfOver B S hS}
    (j : T' ⟶ T) : yoneda.obj (levelChart π v j) ⟶ pullback π (yoneda.map j) :=
  pullback.lift (yoneda.map (pullback.fst _ _) ≫ v) (yoneda.map (pullback.snd _ _)) (by
    rw [Category.assoc, ← yoneda_map_levelChartBase π v, ← yoneda.map_comp, ← yoneda.map_comp,
      pullback.condition])

/-- The first component of `levelChartMap π v j` is the projection to `V` followed by `v`. -/
@[reassoc (attr := simp)]
theorem levelChartMap_fst {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ U)
    {T' : BigFppfOver B S hS} (j : T' ⟶ T) :
    levelChartMap π v j ≫ pullback.fst π (yoneda.map j) = yoneda.map (pullback.fst _ _) ≫ v :=
  pullback.lift_fst _ _ _

/-- The second component of `levelChartMap π v j` is the projection `V ×_T T' ⟶ T'`. -/
@[reassoc (attr := simp)]
theorem levelChartMap_snd {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ U)
    {T' : BigFppfOver B S hS} (j : T' ⟶ T) :
    levelChartMap π v j ≫ pullback.snd π (yoneda.map j) = yoneda.map (pullback.snd _ _) :=
  pullback.lift_snd _ _ _

/-- **The base change of a chart is represented by the fibre product in the site.** -/
theorem isPullback_levelChart {V : BigFppfOver B S hS} (v : yoneda.obj V ⟶ U)
    {T' : BigFppfOver B S hS} (j : T' ⟶ T) :
    IsPullback (yoneda.map (pullback.fst (levelChartBase π v) j)) (levelChartMap π v j) v
      (pullback.fst π (yoneda.map j)) := by
  have hout := (IsPullback.of_hasPullback (levelChartBase π v) j).map yoneda
  refine IsPullback.of_bot (v₂₁ := pullback.snd π (yoneda.map j)) (v₂₂ := π)
    (h₃₁ := yoneda.map j) ?_ (levelChartMap_fst π v j).symm (IsPullback.of_hasPullback _ _)
  rw [levelChartMap_snd, ← yoneda_map_levelChartBase π v]
  exact hout

section KernelPair

variable {W R : BigFppfOver B S hS} (w : yoneda.obj W ⟶ U) {s t : R ⟶ W}
  (hR : IsPullback (yoneda.map s) (yoneda.map t) w w)

/-- The morphism to `T` underlying `yoneda.map s ≫ w ≫ π` is `s ≫ levelChartBase π w`. -/
theorem levelChartBase_comp (s : R ⟶ W) :
    levelChartBase π (yoneda.map s ≫ w) = s ≫ levelChartBase π w :=
  yoneda.map_injective (by simp)

/-- The morphism `R ×_T T' ⟶ W ×_T T'` induced by a morphism `a : R ⟶ W` with
`yoneda.map a ≫ w = yoneda.map s ≫ w`, where `R` lies over `T` through `s`. -/
def levelKernelMap (a : R ⟶ W) (ha : yoneda.map a ≫ w = yoneda.map s ≫ w)
    {T' : BigFppfOver B S hS} (j : T' ⟶ T) :
    levelChart π (yoneda.map s ≫ w) j ⟶ levelChart π w j :=
  pullback.map _ _ _ _ a (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, ← levelChartBase_comp, ← ha, levelChartBase_comp])
    (by simp)

/-- The first component of `levelKernelMap π w a ha j` is the projection to `R` followed by `a`. -/
@[reassoc (attr := simp)]
theorem levelKernelMap_fst (a : R ⟶ W) (ha : yoneda.map a ≫ w = yoneda.map s ≫ w)
    {T' : BigFppfOver B S hS} (j : T' ⟶ T) :
    levelKernelMap π w a ha j ≫ pullback.fst _ _ = pullback.fst _ _ ≫ a :=
  pullback.lift_fst _ _ _

/-- The morphism `levelKernelMap π w a ha j` commutes with the projections to `T'`. -/
@[reassoc (attr := simp)]
theorem levelKernelMap_snd (a : R ⟶ W) (ha : yoneda.map a ≫ w = yoneda.map s ≫ w)
    {T' : BigFppfOver B S hS} (j : T' ⟶ T) :
    levelKernelMap π w a ha j ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [levelKernelMap, pullback.lift_snd, Category.comp_id]

/-- The morphism `levelKernelMap π w a ha j` is compatible with the morphisms to `U ×_T T'`. -/
theorem levelKernelMap_levelChartMap (a : R ⟶ W) (ha : yoneda.map a ≫ w = yoneda.map s ≫ w)
    {T' : BigFppfOver B S hS} (j : T' ⟶ T) :
    yoneda.map (levelKernelMap π w a ha j) ≫ levelChartMap π w j =
      levelChartMap π (yoneda.map s ≫ w) j := by
  apply pullback.hom_ext
  · simp only [Category.assoc, levelChartMap_fst, ← yoneda.map_comp_assoc, levelKernelMap_fst]
    simp [ha]
  · simp only [Category.assoc, levelChartMap_snd, ← yoneda.map_comp, levelKernelMap_snd]

/-- `R ×_T T'` is the base change of `W ×_T T'` along a morphism `a : R ⟶ W` over `U`. -/
theorem isPullback_levelKernelMap (a : R ⟶ W) (ha : yoneda.map a ≫ w = yoneda.map s ≫ w)
    {T' : BigFppfOver B S hS} (j : T' ⟶ T) :
    IsPullback (pullback.fst (levelChartBase π (yoneda.map s ≫ w)) j)
      (levelKernelMap π w a ha j) a (pullback.fst (levelChartBase π w) j) := by
  have hout := IsPullback.of_hasPullback (levelChartBase π (yoneda.map s ≫ w)) j
  have hright := (IsPullback.of_hasPullback (levelChartBase π w) j).flip
  have he : levelChartBase π (yoneda.map s ≫ w) = a ≫ levelChartBase π w := by
    rw [← ha, levelChartBase_comp]
  have hout' : IsPullback (levelKernelMap π w a ha j ≫ pullback.snd _ _)
      (pullback.fst (levelChartBase π (yoneda.map s ≫ w)) j) j (a ≫ levelChartBase π w) := by
    rw [levelKernelMap_snd, ← he]
    exact hout.flip
  exact (IsPullback.of_right hout' (levelKernelMap_fst π w a ha j) hright).flip

include hR in
/-- **The base change of the kernel pair of a chart is the kernel pair of the base-changed
chart.** -/
theorem isPullback_levelKernel {T' : BigFppfOver B S hS} (j : T' ⟶ T) :
    IsPullback (yoneda.map (levelKernelMap π w s rfl j))
      (yoneda.map (levelKernelMap π w t hR.w.symm j)) (levelChartMap π w j)
      (levelChartMap π w j) := by
  have hA := (isPullback_levelKernelMap π w t hR.w.symm j).map yoneda
  have hout : IsPullback (yoneda.map (pullback.fst (levelChartBase π (yoneda.map s ≫ w)) j) ≫
        yoneda.map s)
      (yoneda.map (levelKernelMap π w t hR.w.symm j)) w
      (yoneda.map (pullback.fst (levelChartBase π w) j) ≫ w) :=
    hA.paste_horiz hR
  refine IsPullback.of_right ?_ ?_ (isPullback_levelChart π w j)
  · rw [← yoneda.map_comp, levelKernelMap_fst, yoneda.map_comp, levelChartMap_fst]
    exact hout
  · rw [levelKernelMap_levelChartMap, levelKernelMap_levelChartMap]

end KernelPair

end AlgebraicGeometry.Space

end
