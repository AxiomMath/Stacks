module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion

/-!
# The diagonal of a morphism in an over category, and descent of separatedness

A morphism `f : X ⟶ Y` of schemes over a base `S` has a diagonal `pullback.diagonal f` taken in
the over category, and separatedness of `f` is closedness of that diagonal. This file records how
the diagonal in an over category compares with the diagonal of the underlying morphism of schemes,
and uses that comparison to descend separatedness along a cofiltered inverse system of schemes
with affine transition morphisms.

## Main results

* `AlgebraicGeometry.prop_map_pullback_diagonal_iff`: a property of morphisms of schemes which
  respects isomorphisms holds for the image of the diagonal under a pullback-preserving functor
  exactly when it holds for the diagonal of the image.
* `AlgebraicGeometry.exists_isSeparated_baseChange_of_isLimit`: separatedness after base change to
  the inverse limit descends to a finite stage.

## Implementation notes

Schemes over a fixed base and their base changes are represented by `CategoryTheory.Over` and
`CategoryTheory.Over.pullback`. The phrase "some `i ≥ i₀`" is expressed by an object `i` together
with a morphism `i ⟶ i₀` in the cofiltered indexing category. This generalizes the directed
partially ordered index set in the source.

## References

* [Stacks Project, Tag 01ZQ](https://stacks.math.columbia.edu/tag/01ZQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry

/-! ### Comparing the diagonal with its image under a functor -/

section Comparison

/-- A functor preserving the pullback of `f` with itself carries the diagonal of `f` to the
diagonal of `F.map f`, up to the comparison isomorphism of the two pullbacks. -/
lemma map_pullback_diagonal {C : Type u} [Category.{v} C] {D : Type w} [Category.{v} D]
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) [HasPullback f f] [HasPullback (F.map f) (F.map f)]
    [PreservesLimit (cospan f f) F] :
    F.map (pullback.diagonal f) ≫ (PreservesPullback.iso F f f).hom =
      pullback.diagonal (F.map f) := by
  apply pullback.hom_ext
  · rw [Category.assoc, PreservesPullback.iso_hom_fst, ← F.map_comp, pullback.diagonal_fst,
      F.map_id]
    simp
  · rw [Category.assoc, PreservesPullback.iso_hom_snd, ← F.map_comp, pullback.diagonal_snd,
      F.map_id]
    simp

/-- A property of morphisms of schemes which respects isomorphisms holds for the image of the
diagonal under a pullback-preserving functor exactly when it holds for the diagonal of the
image. -/
lemma prop_map_pullback_diagonal_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {C : Type*} [Category.{u} C] (F : C ⥤ Scheme.{u}) {X Y : C} (f : X ⟶ Y) [HasPullback f f]
    [HasPullback (F.map f) (F.map f)] [PreservesLimit (cospan f f) F] :
    P (F.map (pullback.diagonal f)) ↔ P (pullback.diagonal (F.map f)) := by
  rw [← map_pullback_diagonal F f]
  exact (MorphismProperty.cancel_right_of_respectsIso P (F.map (pullback.diagonal f))
    (PreservesPullback.iso F f f).hom).symm

/-- The diagonal of a morphism of schemes over a base is locally of finite type as a morphism of
schemes. -/
lemma locallyOfFiniteType_diagonal_left {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    LocallyOfFiniteType (pullback.diagonal f).left := by
  let F := Over.forget S
  let e := PreservesPullback.iso F f f
  have hc : LocallyOfFiniteType (F.map (pullback.diagonal f) ≫ e.hom) := by
    rw [map_pullback_diagonal F f]
    infer_instance
  change LocallyOfFiniteType (F.map (pullback.diagonal f))
  rw [show F.map (pullback.diagonal f) = (F.map (pullback.diagonal f) ≫ e.hom) ≫ e.inv by simp]
  infer_instance

/-- The source of the diagonal of a morphism of quasi-separated schemes is quasi-separated. -/
lemma quasiSeparatedSpace_pullback_self {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiSeparatedSpace X]
    [QuasiSeparatedSpace Y] : QuasiSeparatedSpace ↑(pullback f f) := by
  have hterm : pullback.fst f f ≫ terminal.from X = terminal.from (pullback f f) :=
    terminal.hom_ext _ _
  rw [quasiSeparatedSpace_iff_quasiSeparated, ← hterm]
  infer_instance

/-- The target of the diagonal of a morphism of quasi-compact quasi-separated schemes over a base
is quasi-compact and quasi-separated. -/
lemma compactSpace_and_quasiSeparatedSpace_diagonalObj_left {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [CompactSpace X.left] [QuasiSeparatedSpace X.left] [CompactSpace Y.left]
    [QuasiSeparatedSpace Y.left] :
    CompactSpace (pullback.diagonalObj f).left ∧
      QuasiSeparatedSpace (pullback.diagonalObj f).left := by
  let F := Over.forget S
  let e := PreservesPullback.iso F f f
  have : CompactSpace ↑(pullback (F.map f) (F.map f)) := by
    change CompactSpace ↑(pullback f.left f.left)
    infer_instance
  have hqs : QuasiSeparatedSpace ↑(pullback (F.map f) (F.map f)) := by
    change QuasiSeparatedSpace ↑(pullback f.left f.left)
    exact quasiSeparatedSpace_pullback_self f.left
  exact ⟨e.hom.homeomorph.symm.compactSpace, (quasiSeparatedSpace_congr e.hom.homeomorph).mpr hqs⟩

/-- A separated base change has a closed diagonal in the base-changed over category. -/
lemma isClosedImmersion_overPullback_diagonal_of_isSeparated {S T : Scheme.{u}} (g : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y) [IsSeparated ((Over.pullback g).map f).left] :
    IsClosedImmersion ((Over.pullback g).map (pullback.diagonal f)).left := by
  let F := Over.pullback g ⋙ Over.forget T
  have hsep : IsSeparated (F.map f) := by
    change IsSeparated ((Over.pullback g).map f).left
    infer_instance
  exact (prop_map_pullback_diagonal_iff (@IsClosedImmersion) F f).mpr ((isSeparated_iff _).mp hsep)

end Comparison

/-! ### Descending separatedness -/

/-- **Stacks Project, Tag 01ZQ.** If a morphism over a stage of a cofiltered inverse system is
separated after base change to the limit, then it is separated after base change to some later
stage. -/
@[stacks 01ZQ]
theorem exists_isSeparated_baseChange_of_isLimit
    {I : Type v} [Category.{v} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (i₀ : I)
    (X₀ Y₀ : Over (D.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [IsCofiltered I] [EssentiallySmall.{u} I]
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [CompactSpace (D.obj i₀)] [QuasiSeparatedSpace (D.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (hc : IsLimit c)
    [IsSeparated ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (g : i ⟶ i₀), IsSeparated ((Over.pullback (D.map g)).map f₀).left := by
  let d : X₀ ⟶ pullback.diagonalObj f₀ := pullback.diagonal f₀
  obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_diagonalObj_left f₀
  have : LocallyOfFiniteType d.left := locallyOfFiniteType_diagonal_left f₀
  have hclosed := isClosedImmersion_overPullback_diagonal_of_isSeparated (c.π.app i₀) f₀
  obtain ⟨i, hi, hclosedStage⟩ :=
    exists_isClosedImmersion_baseChange_of_isLimit (D := D) c hc i₀ X₀
      (pullback.diagonalObj f₀) d
  let F := Over.pullback (D.map hi) ⋙ Over.forget (D.obj i)
  exact ⟨i, hi, (isSeparated_iff _).mpr
    ((prop_map_pullback_diagonal_iff (@IsClosedImmersion) F f₀).mp hclosedStage)⟩

end AlgebraicGeometry
