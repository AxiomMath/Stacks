module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Diagonal
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Diagonal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Unramified morphisms descend to a finite stage

Let a scheme be the limit of a cofiltered diagram of schemes with affine transition morphisms. If
a morphism over one stage is locally of finite type and becomes unramified after base change to
the limit, then it is already unramified after base change to some later stage.

## Main results

* `AlgebraicGeometry.exists_unramified_baseChange_of_unramified_limitBaseChange`: a locally finite
  type morphism whose base change to the limit is unramified is unramified after base change to
  some finite stage.

## Implementation notes

Schemes over a fixed base and their base changes are represented by `CategoryTheory.Over` and
`CategoryTheory.Over.pullback`. A morphism `g : i ⟶ i₀` expresses that `i` is a stage later than
`i₀` in the cofiltered indexing category. The cone leg at `i₀` gives the base change to the limit.

## References

* [Stacks Project, Tag 0C4W](https://stacks.math.columbia.edu/tag/0C4W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Whether the base change of the diagonal of a morphism over a base is an open immersion is
whether the diagonal of the base-changed morphism is. -/
private lemma isOpenImmersion_overPullback_diagonal_iff {S T : Scheme.{u}} (h : T ⟶ S)
    (X Y : Over S) (f : X ⟶ Y) :
    IsOpenImmersion ((Over.pullback h).map (pullback.diagonal f)).left ↔
      IsOpenImmersion (pullback.diagonal ((Over.pullback h).map f).left) :=
  prop_map_pullback_diagonal_iff (@IsOpenImmersion) (Over.pullback h ⋙ Over.forget T) f

/-- The diagonal of a morphism over a base which is locally of finite type is locally of finite
presentation. -/
@[ega "IV 1.4.3.1", ega "IV 17.4.1.2"]
private lemma locallyOfFinitePresentation_diagonal_left {T : Scheme.{u}} {X Y : Over T}
    (f : X ⟶ Y) (hf : LocallyOfFiniteType f.left) :
    LocallyOfFinitePresentation (pullback.diagonal f).left := by
  have : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (prop_map_pullback_diagonal_iff (@LocallyOfFinitePresentation) (Over.forget T) f).mpr
    (locallyOfFinitePresentation_diagonal f.left)

/-- An unramified base change has an open diagonal. -/
private lemma isOpenImmersion_overPullback_diagonal_of_unramified {S T : Scheme.{u}} (h : T ⟶ S)
    (X Y : Over S) (f : X ⟶ Y) (hf : Unramified ((Over.pullback h).map f).left) :
    IsOpenImmersion ((Over.pullback h).map (pullback.diagonal f)).left := by
  apply (isOpenImmersion_overPullback_diagonal_iff h X Y f).mpr
  obtain ⟨_, _⟩ := (unramified_iff_locallyOfFiniteType_and_formallyUnramified
    ((Over.pullback h).map f).left).mp hf
  exact FormallyUnramified.isOpenImmersion_diagonal ((Over.pullback h).map f).left

/-- Openness of the diagonal descends from the limit to a finite stage. -/
private lemma exists_isOpenImmersion_diagonal_baseChange {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i₀ : I) (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [IsCofiltered I] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (hf : LocallyOfFiniteType f₀.left) (hc : IsLimit c)
    (hδlim : IsOpenImmersion
      ((Over.pullback (c.π.app i₀)).map (pullback.diagonal f₀)).left) :
    ∃ (i : I) (g : i ⟶ i₀),
      IsOpenImmersion ((Over.pullback (D.map g)).map (pullback.diagonal f₀)).left := by
  let Z₀ : Over (D.obj i₀) := pullback.diagonalObj f₀
  let δ₀ : X₀ ⟶ Z₀ := pullback.diagonal f₀
  obtain ⟨_, _⟩ : CompactSpace Z₀.left ∧ QuasiSeparatedSpace Z₀.left :=
    compactSpace_and_quasiSeparatedSpace_diagonalObj_left f₀
  have hδlft : LocallyOfFinitePresentation δ₀.left :=
    locallyOfFinitePresentation_diagonal_left f₀ hf
  have : IsOpenImmersion ((Over.pullback (c.π.app i₀)).map δ₀).left := hδlim
  obtain ⟨i, g, hs⟩ :=
    exists_smooth_baseChange_of_smooth_limitBaseChange D c i₀ X₀ Z₀ δ₀ hc
  refine ⟨i, g, ?_⟩
  let fᵢ := ((Over.pullback (D.map g)).map δ₀).left
  have : LocallyOfFinitePresentation fᵢ :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) (D.map g) _ hδlft
  have : Smooth fᵢ := hs
  have : Mono fᵢ := by
    dsimp [fᵢ]
    exact MorphismProperty.overPullbackMap
      (P := MorphismProperty.monomorphisms Scheme) (D.map g) _ inferInstance
  exact IsOpenImmersion.of_flat_of_mono fᵢ

/-- If a morphism over a stage of a cofiltered inverse system is locally of finite type and its
base change to the limit is unramified, then its base change to some later stage is
unramified. -/
@[stacks 0C4W]
theorem exists_unramified_baseChange_of_unramified_limitBaseChange
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [IsCofiltered I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    (hc : IsLimit c)
    [Unramified ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (g : i ⟶ i₀),
      Unramified ((Over.pullback (D.map g)).map f₀).left := by
  obtain ⟨i, g, hg⟩ := exists_isOpenImmersion_diagonal_baseChange D c i₀ X₀ Y₀ f₀ inferInstance hc
    (isOpenImmersion_overPullback_diagonal_of_unramified (c.π.app i₀) X₀ Y₀ f₀ inferInstance)
  refine ⟨i, g, ?_⟩
  apply (unramified_iff_locallyOfFiniteType_and_formallyUnramified
    ((Over.pullback (D.map g)).map f₀).left).mpr
  have := (isOpenImmersion_overPullback_diagonal_iff (D.map g) X₀ Y₀ f₀).mp hg
  exact ⟨MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType) (D.map g) _ inferInstance,
    inferInstance⟩

end AlgebraicGeometry
