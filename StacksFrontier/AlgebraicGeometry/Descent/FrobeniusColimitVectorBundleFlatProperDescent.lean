module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleFlatDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectColimitPresentation
public import
  StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleGroupoidCoreInclusion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.BigHOverProperQcqs

/-!
# Condition (2) of Stacks 0EX9 for the stack of Stacks Tag 0EXE

For a morphism `f : X ⟶ Y` of `(Sch/S)_h` with `Y` affine and `f` surjective, flat, proper and of
finite presentation, the category fibred in groupoids of finite locally free
`colim_F 𝒪`-modules of Stacks Tag 0EXE has effective descent along `{f}`
(`isAffineFlatProperFinitePresentationDescent_frobeniusVectorBundleGroupoidFibration`).

This is the proof of the source.  `Y`, `X`, `X ×_Y X` and `X ×_Y X ×_Y X` are quasi-compact and
quasi-separated (`AlgebraicGeometry.BigHOver.compactSpace_chosenPullback` and its companions), so
by Stacks Tag 0EXB the fibres over them are `colim_F Vect`
(`AlgebraicGeometry.isColimitPresentation_frobeniusColimitVectPseudococone`); finite locally free
`𝒪`-modules have effective descent along `{f}` by Stacks Tags 023T and 05B2
(`AlgebraicGeometry.isStackFor_bigHVectPseudofunctor_singleton_of_isProper`); and "this will imply
the same for the colimits" is
`CategoryTheory.Pseudofunctor.StageColimitData.isStackFor_singleton`, applied to the stage data
`AlgebraicGeometry.bigHStageColimitData` — the Frobenius pullback as an endo-transformation of
`U ↦ Vect(U)`, the stage-`n` extensions of scalars as strong transformations to the pseudofunctor
of Stacks Tag 0EXE, and the comparisons `F^* ⋙ S_{n + 1} ≅ S_n` of Stacks Tag 0EXB, whose
compatibility with pullbacks is `AlgebraicGeometry.frobeniusStageFunctorPullbackIso_compat`.
The passage to the maximal subgroupoids and to the Grothendieck construction is
`isAffineFlatProperFinitePresentationDescent_frobeniusVectorBundleGroupoidFibration_of`.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- The compatibility of the stage bridge with the comparison of consecutive stages, in the form
of inverses. -/
lemma frobeniusStageFunctorPullbackIso_compat_inv {X Y : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    (f : X ⟶ Y) (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (n : ℕ)
    (E : Y.Vect) :
    (frobeniusStageFunctor X p hX (n + 1)).map ((frobeniusVectPullbackIso f p hX hY).inv.app E) ≫
        (frobeniusStageFunctorPullbackIso p f hX hY (n + 1)).inv.app
          ((frobeniusPullback Y p hY).obj E) ≫
        (frobeniusColimitVectorBundlesPullback p f hX hY).map
          ((frobeniusStageFunctorIso Y p hY n).hom.app E) =
      (frobeniusStageFunctorIso X p hX n).hom.app ((Scheme.Vect.pullback f).obj E) ≫
        (frobeniusStageFunctorPullbackIso p f hX hY n).inv.app E := by
  rw [← cancel_mono ((frobeniusStageFunctorPullbackIso p f hX hY n).hom.app E)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [frobeniusStageFunctorPullbackIso_compat]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact (Category.comp_id _).symm

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

include hpS in
/-- **The stage data of Stacks Tag 0EXB on the big h site**: the Frobenius pullback on
`U ↦ Vect(U)`, the stage-`n` extensions of scalars to the pseudofunctor of Stacks Tag 0EXE, and the
comparisons `F^* ⋙ S_{n + 1} ≅ S_n`. -/
def bigHStageColimitData : (bigHVectPseudofunctor B S hS).StageColimitData
    (frobeniusVectorBundlePseudofunctor B S hS p hpS) where
  Φ := bigHFrobeniusVectTrans B S hS p hpS
  σ n := bigHStageTrans B S hS p hpS n
  μ n U := frobeniusStageFunctorIso ((BigHOver.toScheme B S hS).obj U) p
    (isInCharacteristic_bigHOver B S hS p hpS U) n
  pullIso_μ n {X Y} h M := frobeniusStageFunctorPullbackIso_compat_inv p
    ((BigHOver.toScheme B S hS).map h) (isInCharacteristic_bigHOver B S hS p hpS Y)
    (isInCharacteristic_bigHOver B S hS p hpS X) n M

include hpS in
/-- At an object of the big h site, the pseudo-cocone of the stage data is the pseudo-cocone of
Stacks Tag 0EXB. -/
lemma bigHStageColimitData_pc (U : BigHOver B S hS) :
    (bigHStageColimitData B S hS p hpS).pc U =
      frobeniusColimitVectPseudococone ((BigHOver.toScheme B S hS).obj U) p
        (isInCharacteristic_bigHOver B S hS p hpS U) := rfl

include hpS in
/-- At a quasi-compact quasi-separated object, the stage data presents the fibre of Stacks Tag
0EXE as the colimit `colim_F Vect` (Stacks Tag 0EXB). -/
lemma isColimitPresentation_bigHStageColimitData_pc (U : BigHOver B S hS)
    [CompactSpace ((BigHOver.toScheme B S hS).obj U)]
    [QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj U)] :
    ((bigHStageColimitData B S hS p hpS).pc U).IsColimitPresentation := by
  rw [bigHStageColimitData_pc]
  exact isColimitPresentation_frobeniusColimitVectPseudococone _ p _

include hpS in
/-- **Effective descent of finite locally free `colim_F 𝒪`-modules along a surjective flat proper
morphism of finite presentation onto an affine object of `(Sch/S)_h`.** -/
theorem isStackFor_frobeniusVectorBundlePseudofunctor_singleton {X Y : BigHOver B S hS}
    (f : X ⟶ Y) (hY : IsAffine ((BigHOver.toScheme B S hS).obj Y))
    (hfl : Flat ((BigHOver.toScheme B S hS).map f))
    (hpr : IsProper ((BigHOver.toScheme B S hS).map f))
    (hsu : Surjective ((BigHOver.toScheme B S hS).map f)) :
    (frobeniusVectorBundlePseudofunctor B S hS p hpS).IsStackFor (Presieve.singleton f) := by
  let sq := ChosenPullback.ofHasPullback f f
  let sq₃ := ChosenPullback₃.ofHasPullbacks sq sq sq
  have := BigHOver.compactSpace_source_of_isProper f hY hpr
  have := BigHOver.quasiSeparatedSpace_source_of_isProper f hY hpr
  have := BigHOver.compactSpace_chosenPullback f hY hpr
  have := BigHOver.quasiSeparatedSpace_chosenPullback f hY hpr
  have := BigHOver.compactSpace_chosenPullback₃ f hY hpr
  have := BigHOver.quasiSeparatedSpace_chosenPullback₃ f hY hpr
  exact (bigHStageColimitData B S hS p hpS).isStackFor_singleton sq₃
    (isColimitPresentation_bigHStageColimitData_pc B S hS p hpS Y)
    (isColimitPresentation_bigHStageColimitData_pc B S hS p hpS X)
    (isColimitPresentation_bigHStageColimitData_pc B S hS p hpS sq.pullback)
    (isColimitPresentation_bigHStageColimitData_pc B S hS p hpS sq₃.pullback)
    (isStackFor_bigHVectPseudofunctor_singleton_of_isProper f)

include hpS in
/-- **Stacks 0EX9, condition (2), for the stack of Stacks Tag 0EXE.**  For every morphism
`f : X ⟶ Y` of `(Sch/S)_h` with `Y` affine and `f` surjective, flat, proper and of finite
presentation, the category fibred in groupoids of finite locally free `colim_F 𝒪`-modules has
effective descent along `{f}`. -/
theorem isAffineFlatProperFinitePresentationDescent_frobeniusVectorBundleGroupoidFibration :
    BigHOver.IsAffineFlatProperFinitePresentationDescent B S hS
      (frobeniusVectorBundleGroupoidFibration B S hS p hpS) :=
  isAffineFlatProperFinitePresentationDescent_frobeniusVectorBundleGroupoidFibration_of B S hS p hpS
    fun f hY hfl hpr hsu _ ↦
      isStackFor_frobeniusVectorBundlePseudofunctor_singleton B S hS p hpS f hY hfl hpr hsu

end AlgebraicGeometry

end
