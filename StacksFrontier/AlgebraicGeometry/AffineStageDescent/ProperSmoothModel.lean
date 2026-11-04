module

public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitDescent

/-!
# A proper smooth morphism to an affine scheme comes from a Noetherian base

Let `f : X ⟶ S` be a proper smooth morphism with `S` affine. Writing `S` as the limit of the
spectra of the finitely generated subrings of `Γ(S, ⊤)` (`AlgebraicGeometry.affineStageCone`),
the morphism `f` is the base change of a proper smooth morphism to one of these spectra, which
is Noetherian. This is the absolute Noetherian approximation used to reduce statements about
proper smooth morphisms to the case of a Noetherian base.

## Main results

* `AlgebraicGeometry.exists_isPullback_isNoetherian_properSmooth`: the model over a Noetherian
  affine scheme.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- For a morphism `a : Over.mk g ⟶ Over.mk (𝟙 Y)`, a base change of `a` is smooth iff the
corresponding base change `pullback.snd g b` of `g` is. -/
theorem smooth_overPullback_map_left_iff {Y T Z : Scheme.{u}} {g : Z ⟶ Y}
    (a : Over.mk g ⟶ Over.mk (𝟙 Y)) (b : T ⟶ Y) :
    Smooth ((Over.pullback b).map a).left ↔ Smooth (pullback.snd g b) := by
  have : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hw : ((Over.pullback b).map a).left ≫ pullback.snd (𝟙 Y) b = pullback.snd g b :=
    Over.w ((Over.pullback b).map a)
  rw [← hw]
  exact (MorphismProperty.cancel_right_of_respectsIso (@Smooth.{u}) _ _).symm

/-- **A proper smooth morphism to an affine scheme is the base change of a proper smooth
morphism to a Noetherian affine scheme.** -/
theorem exists_isPullback_isNoetherian_properSmooth {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [IsProper f] [Smooth f] :
    ∃ (T Y : Scheme.{u}) (h : Y ⟶ T) (q : S ⟶ T) (q' : X ⟶ Y),
      IsNoetherian T ∧ IsProper h ∧ Smooth h ∧ IsPullback q' f h q := by
  let D := specAdjoinFinsetDiagram Γ(S, ⊤)
  let c := affineStageCone S
  have hc : IsLimit c := isLimit_affineStageCone S
  have hfp : FinitePresentation f := ⟨inferInstance, inferInstance, inferInstance⟩
  let f' : X ⟶ c.pt := f
  have : IsProper f' := ‹IsProper f›
  have : Flat f' := inferInstanceAs (Flat f)
  obtain ⟨i, X₁, f₁, g₁, hpr₁, hfl₁, hfp₁, hpb₁⟩ :=
    exists_stage_properFlatModel D c hc f' hfp
  have : LocallyOfFinitePresentation f₁ := hfp₁.1
  have : QuasiCompact f₁ := hfp₁.2.1
  have : QuasiSeparated f₁ := hfp₁.2.2
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated f₁
  have : MorphismProperty.RespectsIso (@Smooth.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  -- the morphism `f₁`, as a morphism of `Over (D.obj i)` into the terminal object
  let X₀ : Over (D.obj i) := Over.mk f₁
  let Y₀ : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  let a : X₀ ⟶ Y₀ := Over.homMk f₁ (Category.comp_id f₁)
  have : CompactSpace X₀.left := inferInstanceAs (CompactSpace X₁)
  have : QuasiSeparatedSpace X₀.left := inferInstanceAs (QuasiSeparatedSpace X₁)
  have : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj i))
  have : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have : LocallyOfFinitePresentation a.left := inferInstanceAs (LocallyOfFinitePresentation f₁)
  -- smoothness of a base change of `a` is smoothness of the corresponding base change of `f₁`
  have key : ∀ {T : Scheme.{u}} (b : T ⟶ D.obj i),
      Smooth ((Over.pullback b).map a).left ↔ Smooth (pullback.snd f₁ b) :=
    fun b ↦ smooth_overPullback_map_left_iff a b
  have hsm : Smooth ((Over.pullback (c.π.app i)).map a).left := by
    rw [key, ← MorphismProperty.cancel_left_of_respectsIso (@Smooth.{u}) hpb₁.isoPullback.hom,
      hpb₁.isoPullback_hom_snd]
    exact inferInstanceAs (Smooth f)
  obtain ⟨j, k, hj⟩ := exists_smooth_baseChange_of_smooth_limitBaseChange D c i X₀ Y₀ a hc
  rw [key] at hj
  have hsq : IsPullback (pullback.fst f₁ (D.map k)) (pullback.snd f₁ (D.map k)) f₁ (D.map k) :=
    IsPullback.of_hasPullback f₁ (D.map k)
  have hcond : g₁ ≫ f₁ = (f' ≫ c.π.app j) ≫ D.map k := by
    rw [hpb₁.w, Category.assoc, c.w k]
  have hpb : IsPullback (pullback.lift g₁ (f' ≫ c.π.app j) hcond) f'
      (pullback.snd f₁ (D.map k)) (c.π.app j) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hsq
    rw [pullback.lift_fst, c.w k]
    exact hpb₁
  exact ⟨D.obj j, pullback f₁ (D.map k), pullback.snd f₁ (D.map k), c.π.app j,
    pullback.lift g₁ (f' ≫ c.π.app j) hcond, isNoetherian_specAdjoinFinsetDiagram_obj _ j,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper) hsq hpr₁, hj, hpb⟩

end AlgebraicGeometry
