module

public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.PuncturedSpectrumCompletion
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine

/-!
# Picard classes of a scheme are trivial on an open cover

An invertible module on a scheme is finite locally free of rank one, so it is trivial on a
neighbourhood of every point. Hence every class of the Picard group of a scheme pulls back to
zero along the inclusion of each member of a suitable Zariski open cover: the Picard presheaf
of any topology at least as fine as the Zariski one has zero sheafification.

## Main results

* `Stacks.Picard.exists_mem_schemePullbackClass_eq_zero` — a Picard class pulls back to zero on
  an open neighbourhood of any prescribed point.
* `Stacks.Picard.exists_openCover_schemePullbackClass_eq_zero` — a Picard class pulls back to
  zero on every member of an open cover.
* `Stacks.Picard.eq_zero_iff_nonempty_iso_unit` and
  `Stacks.Picard.schemePullbackClass_eq_zero_iff_nonempty_iso_unit` — a Picard class, or its
  pullback, vanishes exactly when the module representing it, or its pullback, is trivial.

## References

* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Picard

/-- The pullback of a Picard class of a scheme vanishes exactly when the pullback of the module
representing it is trivial. -/
private theorem schemePullbackClass_eq_zero_iff_nonempty_iso_unit_aux {Y Z : Scheme.{u}}
    (g : Y ⟶ Z) (x : ofScheme Z) :
    schemePullbackClass g x = 0 ↔
      Nonempty ((Scheme.Modules.pullback g).obj (picardRepresentative Z.toRingedSpace x).obj ≅
        SheafOfModules.unit Y.ringCatSheaf) := by
  have key := pullbackClass_classOf g.toLRSHom.toShHom
    (picardRepresentative Z.toRingedSpace x).obj
    (picardRepresentative Z.toRingedSpace x).property
  rw [classOf_picardRepresentative] at key
  rw [show schemePullbackClass g x = _ from key]
  exact Stacks.AlgebraicGeometry.PicardBaseChange.classOf_eq_zero_iff_nonempty_iso_unit
    (X := Y.toRingedSpace) _ _

/-- **A Picard class of a scheme pulls back to zero on a neighbourhood of any point**: an
invertible module is finite locally free of rank one, hence trivial near every point. -/
theorem exists_mem_schemePullbackClass_eq_zero {Y : Scheme.{u}} (N : ofScheme Y) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ schemePullbackClass U.ι N = 0 := by
  classical
  have hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (picardRepresentative Y.toRingedSpace N).obj :=
    (picardRepresentative Y.toRingedSpace N).property
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (picardRepresentative Y.toRingedSpace N).obj :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      Y.presheaf _ _).mp hL
  have hrk : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (picardRepresentative Y.toRingedSpace N).obj 1 :=
    AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible Y _
  obtain ⟨U, hyU, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheafOfModules
      (picardRepresentative Y.toRingedSpace N).obj 1 hrk y
  refine ⟨U, hyU, ?_⟩
  have efree : SheafOfModules.free.{u} (R := (U : Scheme.{u}).ringCatSheaf) (ULift (Fin 1)) ≅
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
    Limits.coproductUniqueIso (fun _ : ULift (Fin 1) => SheafOfModules.unit _)
  have epull : (Scheme.Modules.pullback U.ι).obj (picardRepresentative Y.toRingedSpace N).obj ≅
      SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm ≪≫ e ≪≫ efree
  exact (schemePullbackClass_eq_zero_iff_nonempty_iso_unit_aux U.ι N).mpr ⟨epull⟩

/-- **A Picard class of a scheme pulls back to zero on every member of an open cover.** -/
theorem exists_openCover_schemePullbackClass_eq_zero {Y : Scheme.{u}} (N : ofScheme Y) :
    ∃ 𝒰 : Y.OpenCover.{u, u}, ∀ i, schemePullbackClass (𝒰.f i) N = 0 := by
  classical
  choose U hU hzero using fun y : Y => exists_mem_schemePullbackClass_eq_zero N y
  have hcov : IsOpenCover U :=
    .mk <| top_unique fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hU y⟩
  exact ⟨Scheme.openCoverOfIsOpenCover (s := (↥Y : Type u)) Y U hcov, hzero⟩

/-! ### Vanishing of a class read off its representative -/

/-- A Picard class of a scheme is zero exactly when the invertible module representing it is
trivial. -/
theorem eq_zero_iff_nonempty_iso_unit {Y : Scheme.{u}} (x : ofScheme Y) :
    x = 0 ↔ Nonempty ((picardRepresentative Y.toRingedSpace x).obj ≅
      SheafOfModules.unit Y.ringCatSheaf) := by
  have h := Stacks.AlgebraicGeometry.PicardBaseChange.classOf_eq_zero_iff_nonempty_iso_unit
    (X := Y.toRingedSpace) (picardRepresentative Y.toRingedSpace x).obj
    (picardRepresentative Y.toRingedSpace x).property
  rwa [classOf_picardRepresentative] at h

/-- A Picard class of a scheme pulls back to zero along a morphism exactly when the pullback of
the invertible module representing it is trivial. -/
theorem schemePullbackClass_eq_zero_iff_nonempty_iso_unit {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (x : ofScheme Z) :
    schemePullbackClass g x = 0 ↔
      Nonempty ((Scheme.Modules.pullback g).obj (picardRepresentative Z.toRingedSpace x).obj ≅
        SheafOfModules.unit Y.ringCatSheaf) :=
  schemePullbackClass_eq_zero_iff_nonempty_iso_unit_aux g x

end Stacks.Picard

end
