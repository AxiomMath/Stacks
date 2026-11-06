module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.DiagonalDiagram
public import StacksCore.Tactic.StacksAttribute

/-!
# Separation conditions on a groupoid scheme

For a groupoid scheme over a scheme, the source-target morphism is separated if and only if the
stabilizer is separated over the object scheme, if and only if the stabilizer's identity section
is a closed immersion; and likewise with "separated" and "closed immersion" replaced by
"quasi-separated" and "quasi-compact".

## Main results

* `AlgebraicGeometry.sourceTarget_isSeparated_iff_stabilizer_isSeparated` compares
  separatedness of the source-target morphism and of the stabilizer.
* `AlgebraicGeometry.stabilizer_isSeparated_iff_identity_isClosedImmersion` characterizes
  separatedness of the stabilizer by its identity section.
* `AlgebraicGeometry.sourceTarget_quasiSeparated_iff_stabilizer_quasiSeparated` and
  `AlgebraicGeometry.stabilizer_quasiSeparated_iff_identity_quasiCompact` are the
  quasi-separated analogues.

## References

* [Stacks Project, Tag 02YI](https://stacks.math.columbia.edu/tag/02YI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The diagonal of the arrows, composed with the comparison isomorphism, is the diagonal of the
source-target morphism. -/
private theorem arrowDiagonal_left_comp_iso {S : Scheme.{u}} (G : GroupoidScheme S) :
    (arrowDiagonal G).left ≫
      (PreservesPullback.iso (Over.forget S) (sourceTarget G) (sourceTarget G)).hom =
      pullback.diagonal (sourceTarget G).left := by
  apply pullback.hom_ext
  · rw [Category.assoc,
      PreservesPullback.iso_hom_fst (Over.forget S) (sourceTarget G) (sourceTarget G)]
    show _ = pullback.diagonal (sourceTarget G).left ≫
      pullback.fst (sourceTarget G).left (sourceTarget G).left
    rw [pullback.diagonal_fst]
    have h : arrowDiagonal G ≫ pullback.fst (sourceTarget G) (sourceTarget G) =
        𝟙 G.arrows := by
      show pullback.lift (𝟙 G.arrows) (𝟙 G.arrows) _ ≫
        pullback.fst (sourceTarget G) (sourceTarget G) = _
      rw [pullback.lift_fst]
    have h' := congrArg (fun f => f.left) h
    simp only [Over.comp_left, Over.id_left] at h'
    simpa [Over.forget_map] using h'
  · rw [Category.assoc,
      PreservesPullback.iso_hom_snd (Over.forget S) (sourceTarget G) (sourceTarget G)]
    show _ = pullback.diagonal (sourceTarget G).left ≫
      pullback.snd (sourceTarget G).left (sourceTarget G).left
    rw [pullback.diagonal_snd]
    have h : arrowDiagonal G ≫ pullback.snd (sourceTarget G) (sourceTarget G) =
        𝟙 G.arrows := by
      show pullback.lift (𝟙 G.arrows) (𝟙 G.arrows) _ ≫
        pullback.snd (sourceTarget G) (sourceTarget G) = _
      rw [pullback.lift_snd]
    have h' := congrArg (fun f => f.left) h
    simp only [Over.comp_left, Over.id_left] at h'
    simpa [Over.forget_map] using h'

/-- The identity section of the stabilizer is a section of the stabilizer. -/
private theorem identityStabilizer_left_comp_hom {S : Scheme.{u}} (G : GroupoidScheme S) :
    (identityStabilizer G).left ≫ (stabilizer G).hom = 𝟙 G.objects.left := by
  have h : identityStabilizer G ≫ pullback.snd (sourceTarget G) (diagonal G) =
      𝟙 G.objects := by
    show pullback.lift G.identity (𝟙 G.objects) _ ≫
      pullback.snd (sourceTarget G) (diagonal G) = 𝟙 G.objects
    rw [pullback.lift_snd]
  simpa [stabilizer] using congrArg (fun f => f.left) h

/-- If the identity section of the stabilizer is quasi-compact, then the source-target morphism
is quasi-separated. -/
private theorem quasiSeparated_sourceTarget_of_identity_quasiCompact
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (he : QuasiCompact (identityStabilizer G).left) :
    QuasiSeparated (sourceTarget G).left := by
  have hrv : QuasiCompact (rightVertical G).left :=
    MorphismProperty.of_isPullback
      (by simpa using (rightSquare_isPullback G).map (Over.forget S)) he
  have hcomp : QuasiCompact
      ((arrowDiagonal G).left ≫ (bottomComparison G).left) := by
    have : IsIso (topComparison G) := topComparison_isIso G
    have : IsIso (topComparison G).left := by
      show IsIso ((Over.forget S).map (topComparison G))
      infer_instance
    have : QuasiCompact (topComparison G).left := inferInstance
    have hcomm' : (arrowDiagonal G).left ≫ (bottomComparison G).left =
        (topComparison G).left ≫ (rightVertical G).left := by
      simpa using congrArg (fun f => f.left) (diagonalDiagram_commutes G)
    rw [hcomm']
    exact MorphismProperty.comp_mem @QuasiCompact _ _ inferInstance hrv
  have hdiag : QuasiCompact (arrowDiagonal G).left := by
    have : IsIso (bottomComparison G) := bottomComparison_isIso G
    have : IsIso (bottomComparison G).left := by
      show IsIso ((Over.forget S).map (bottomComparison G))
      infer_instance
    have : QuasiSeparated (bottomComparison G).left := inferInstance
    have : QuasiCompact
        ((arrowDiagonal G).left ≫ (bottomComparison G).left) := hcomp
    exact QuasiCompact.of_comp (arrowDiagonal G).left (bottomComparison G).left
  exact ⟨arrowDiagonal_left_comp_iso G ▸
    MorphismProperty.comp_mem @QuasiCompact _ _ hdiag inferInstance⟩

/-- If the stabilizer is quasi-separated over the object scheme, then its identity section is
quasi-compact. -/
private theorem stabilizer_quasiSeparated_implies_identity_quasiCompact
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (h : QuasiSeparated (stabilizer G).hom) :
    QuasiCompact (identityStabilizer G).left := by
  exact @QuasiCompact.of_comp G.objects.left (stabilizer G).left G.objects.left
    (identityStabilizer G).left (stabilizer G).hom
    (by rw [identityStabilizer_left_comp_hom]; infer_instance) h

/-- The source-target morphism is quasi-separated exactly when the stabilizer is
quasi-separated over the object scheme. -/
@[stacks 02YI "quasi_separated_equivalences"]
theorem sourceTarget_quasiSeparated_iff_stabilizer_quasiSeparated
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    QuasiSeparated (sourceTarget G).left ↔ QuasiSeparated (stabilizer G).hom :=
  ⟨fun h => quasiSeparated_isStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback (sourceTarget G) (diagonal G)).map (Over.forget S)) h,
    fun h => quasiSeparated_sourceTarget_of_identity_quasiCompact G
      (stabilizer_quasiSeparated_implies_identity_quasiCompact G h)⟩

/-- The stabilizer is quasi-separated exactly when its identity section is quasi-compact. -/
@[stacks 02YI "quasi_separated_equivalences"]
theorem stabilizer_quasiSeparated_iff_identity_quasiCompact
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    QuasiSeparated (stabilizer G).hom ↔ QuasiCompact (identityStabilizer G).left :=
  ⟨stabilizer_quasiSeparated_implies_identity_quasiCompact G,
    fun h => (sourceTarget_quasiSeparated_iff_stabilizer_quasiSeparated G).1
      (quasiSeparated_sourceTarget_of_identity_quasiCompact G h)⟩

/-- If the identity section of the stabilizer is a closed immersion, then the source-target
morphism is separated. -/
private theorem sourceTarget_isSeparated_of_identity_closedImmersion
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (he : IsClosedImmersion (identityStabilizer G).left) :
    IsSeparated (sourceTarget G).left := by
  have hright : IsClosedImmersion (rightVertical G).left :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      ((rightSquare_isPullback G).map (Over.forget S)) he
  have : IsClosedImmersion (rightVertical G).left := hright
  have : IsIso (topComparison G) := topComparison_isIso G
  have : IsIso (bottomComparison G) := bottomComparison_isIso G
  have : IsIso (topComparison G).left := by
    show IsIso ((Over.forget S).map (topComparison G))
    infer_instance
  have : IsIso (bottomComparison G).left := by
    show IsIso ((Over.forget S).map (bottomComparison G))
    infer_instance
  have : IsClosedImmersion (topComparison G).left := inferInstance
  have hdiag : IsClosedImmersion (arrowDiagonal G).left := by
    have : IsClosedImmersion ((arrowDiagonal G).left ≫ (bottomComparison G).left) := by
      rw [← Over.comp_left, diagonalDiagram_commutes G, Over.comp_left]
      infer_instance
    have : IsSeparated (bottomComparison G).left := inferInstance
    exact IsClosedImmersion.of_comp (arrowDiagonal G).left (bottomComparison G).left
  rw [isSeparated_iff, ← arrowDiagonal_left_comp_iso G]
  infer_instance

/-- If the stabilizer is separated over the object scheme, then its identity section is a
closed immersion. -/
@[sga "3 II 4.11.4" "more general"]
private theorem stabilizer_identity_closedImmersion_of_isSeparated
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (h : IsSeparated (stabilizer G).hom) :
    IsClosedImmersion (identityStabilizer G).left := by
  have : IsSeparated (stabilizer G).hom := h
  have hcomp : IsClosedImmersion ((identityStabilizer G).left ≫ (stabilizer G).hom) := by
    rw [identityStabilizer_left_comp_hom]
    infer_instance
  have : IsClosedImmersion ((identityStabilizer G).left ≫ (stabilizer G).hom) := hcomp
  exact IsClosedImmersion.of_comp (identityStabilizer G).left (stabilizer G).hom

/-- If the source-target morphism is separated, then so is the stabilizer over the object
scheme. -/
private theorem stabilizer_isSeparated_of_sourceTarget_isSeparated
    {S : Scheme.{u}} (G : GroupoidScheme S)
    (h : IsSeparated (sourceTarget G).left) :
    IsSeparated (stabilizer G).hom :=
  IsSeparated.isStableUnderBaseChange.of_isPullback
    ((IsPullback.of_hasPullback (sourceTarget G) (diagonal G)).map (Over.forget S)) h

/-- The source-target morphism is separated exactly when the stabilizer is separated over
the object scheme. -/
@[stacks 02YI "separated_equivalences"]
theorem sourceTarget_isSeparated_iff_stabilizer_isSeparated
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsSeparated (sourceTarget G).left ↔ IsSeparated (stabilizer G).hom :=
  ⟨stabilizer_isSeparated_of_sourceTarget_isSeparated G,
    fun h => sourceTarget_isSeparated_of_identity_closedImmersion G
      (stabilizer_identity_closedImmersion_of_isSeparated G h)⟩

/-- The stabilizer is separated exactly when its identity section is a closed immersion. -/
@[stacks 02YI "separated_equivalences", sga "3 II 4.11.4" "more general"]
theorem stabilizer_isSeparated_iff_identity_isClosedImmersion
    {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsSeparated (stabilizer G).hom ↔ IsClosedImmersion (identityStabilizer G).left :=
  ⟨stabilizer_identity_closedImmersion_of_isSeparated G,
    fun h => stabilizer_isSeparated_of_sourceTarget_isSeparated G
      (sourceTarget_isSeparated_of_identity_closedImmersion G h)⟩

end AlgebraicGeometry

end
