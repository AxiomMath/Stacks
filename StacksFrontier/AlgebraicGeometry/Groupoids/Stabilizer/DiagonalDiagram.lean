module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The diagonal diagram of a groupoid scheme

For a groupoid scheme, the diagonal of its arrow scheme fits into a cartesian diagram with the
identity section of the stabilizer.  The two comparison morphisms in that diagram are
isomorphisms.  All fibre products are formed in schemes over the original base, and the map from
a pair of parallel arrows `(f, g)` to the stabilizer is the arrow `f⁻¹ ∘ g`.

## Main definitions

* `AlgebraicGeometry.sourceFiberObjects` and `AlgebraicGeometry.sourceFiberStabilizer` are the
  two objects in the right-hand square of the diagram.
* `AlgebraicGeometry.parallelArrows` is the self-fibre product of the source-target morphism.
* `AlgebraicGeometry.topComparison` and `AlgebraicGeometry.bottomComparison` are the displayed
  horizontal comparison morphisms.
* `AlgebraicGeometry.identityStabilizer` is the identity section of the stabilizer.

## Main results

* `AlgebraicGeometry.topComparison_isIso` and `AlgebraicGeometry.bottomComparison_isIso` say
  that the two horizontal comparison morphisms are isomorphisms.
* `AlgebraicGeometry.diagonalDiagram_commutes` records commutativity of the left-hand part of
  the displayed diagram.
* `AlgebraicGeometry.rightSquare_isPullback` says that the right-hand square is cartesian.

## References

* [Stacks Project, Tag 02YH](https://stacks.math.columbia.edu/tag/02YH)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The fibre product `R ×ₛ U`, where the second map to `U` is the identity. -/
noncomputable abbrev sourceFiberObjects {S : Scheme.{u}} (G : GroupoidScheme S) : Over S :=
  pullback G.source (𝟙 G.objects)

/-- The fibre product `R ×ₛ G`, with `G` the stabilizer scheme. -/
noncomputable abbrev sourceFiberStabilizer {S : Scheme.{u}} (G : GroupoidScheme S) : Over S :=
  pullback G.source (pullback.snd (sourceTarget G) (diagonal G))

/-- The scheme of pairs of arrows with the same source and target. -/
noncomputable abbrev parallelArrows {S : Scheme.{u}} (G : GroupoidScheme S) : Over S :=
  pullback (sourceTarget G) (sourceTarget G)

/-- The map `f ↦ (f, s(f))`. -/
noncomputable abbrev topComparison {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.arrows ⟶ sourceFiberObjects G :=
  pullback.lift (𝟙 G.arrows) G.source (by simp)

/-- For parallel arrows `(f, g)`, the arrow `f⁻¹ ∘ g`. -/
noncomputable def differenceArrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    parallelArrows G ⟶ G.arrows :=
  G.compose (pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.inverse)
    (pullback.snd (sourceTarget G) (sourceTarget G)) (by
      have h := pullback.condition (f := sourceTarget G) (g := sourceTarget G)
      have ht := congrArg
        (fun k : parallelArrows G ⟶ G.objects ⊗ G.objects ↦
          k ≫ CartesianMonoidalCategory.fst G.objects G.objects) h
      rw [Category.assoc, G.source_inverse]
      simpa [sourceTarget, Category.assoc] using ht)

/-- The stabilizer-valued arrow `f⁻¹ ∘ g` attached to a pair of parallel arrows. -/
noncomputable def differenceStabilizer {S : Scheme.{u}} (G : GroupoidScheme S) :
    parallelArrows G ⟶ stabilizerOverBase G :=
  pullback.lift (differenceArrow G)
    (pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.source) (by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [sourceTarget, diagonal, lift_fst, Category.assoc]
        rw [differenceArrow, GroupoidScheme.compose, Category.assoc, G.target_comp]
        simp only [pullback.lift_fst_assoc, Category.assoc, G.target_inverse,
          Category.comp_id]
      · simp only [sourceTarget, diagonal, lift_snd, Category.assoc]
        rw [differenceArrow, GroupoidScheme.compose, Category.assoc, G.source_comp]
        simp only [pullback.lift_snd_assoc]
        have h := pullback.condition (f := sourceTarget G) (g := sourceTarget G)
        have hs := congrArg
          (fun k : parallelArrows G ⟶ G.objects ⊗ G.objects ↦
            k ≫ CartesianMonoidalCategory.snd G.objects G.objects) h
        simpa [sourceTarget, Category.assoc] using hs.symm)

/-- The map `(f, g) ↦ (f, f⁻¹ ∘ g)`. -/
noncomputable abbrev bottomComparison {S : Scheme.{u}} (G : GroupoidScheme S) :
    parallelArrows G ⟶ sourceFiberStabilizer G :=
  pullback.lift (pullback.fst (sourceTarget G) (sourceTarget G))
    (differenceStabilizer G) (by
      simp only [differenceStabilizer, pullback.lift_snd])

/-- The identity section of the stabilizer: the arrow `e(u)` at an object `u`. -/
noncomputable def identityStabilizer {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.objects ⟶ stabilizerOverBase G :=
  pullback.lift G.identity (𝟙 G.objects) (by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [sourceTarget, diagonal, G.source_identity, G.target_identity])

/-- The right-hand vertical map of the diagonal diagram, induced by the identity section of the
stabilizer. -/
noncomputable abbrev rightVertical {S : Scheme.{u}} (G : GroupoidScheme S) :
    sourceFiberObjects G ⟶ sourceFiberStabilizer G :=
  pullback.lift (pullback.fst G.source (𝟙 G.objects))
    (pullback.snd G.source (𝟙 G.objects) ≫ identityStabilizer G) (by
      rw [Category.assoc, identityStabilizer, pullback.lift_snd, Category.comp_id]
      exact pullback.condition)

/-- The diagonal of the source-target morphism, `f ↦ (f, f)`. -/
noncomputable abbrev arrowDiagonal {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.arrows ⟶ parallelArrows G :=
  pullback.lift (𝟙 G.arrows) (𝟙 G.arrows) (by simp)

/-- The projection of the stabilizer to the arrow scheme has target the base object. -/
private lemma stabilizerProjection_target {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst (sourceTarget G) (diagonal G) ≫ G.target =
      pullback.snd (sourceTarget G) (diagonal G) := by
  have h := pullback.condition (f := sourceTarget G) (g := diagonal G)
  rw [← Category.comp_id (pullback.snd (sourceTarget G) (diagonal G)),
    ← lift_fst (𝟙 G.objects) (𝟙 G.objects), ← Category.assoc, ← h]
  simp [sourceTarget]

/-- The projection of the stabilizer to the arrow scheme has source the base object. -/
private lemma stabilizerProjection_source {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst (sourceTarget G) (diagonal G) ≫ G.source =
      pullback.snd (sourceTarget G) (diagonal G) := by
  have h := pullback.condition (f := sourceTarget G) (g := diagonal G)
  rw [← Category.comp_id (pullback.snd (sourceTarget G) (diagonal G)),
    ← lift_snd (𝟙 G.objects) (𝟙 G.objects), ← Category.assoc, ← h]
  simp [sourceTarget]

/-- Two parallel arrows have the same target. -/
private lemma parallelArrows_target_eq {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.target =
      pullback.snd (sourceTarget G) (sourceTarget G) ≫ G.target := by
  have h := congrArg
    (fun k : parallelArrows G ⟶ G.objects ⊗ G.objects ↦
      k ≫ CartesianMonoidalCategory.fst G.objects G.objects)
    (pullback.condition (f := sourceTarget G) (g := sourceTarget G))
  simpa [sourceTarget, Category.assoc] using h

/-- In `R ×ₛ G`, the arrow `f` is composable with the stabilizer element `h`. -/
private lemma sourceFiberStabilizer_compose_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback.fst G.source (pullback.snd (sourceTarget G) (diagonal G)) ≫ G.source =
      (pullback.snd G.source (pullback.snd (sourceTarget G) (diagonal G)) ≫
        pullback.fst (sourceTarget G) (diagonal G)) ≫ G.target := by
  rw [Category.assoc, stabilizerProjection_target]
  exact pullback.condition

/-- Composing `f` with `f⁻¹ ∘ g` recovers `g`. -/
private lemma composeRightDifference {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} (f g : T ⟶ G.arrows) (ht : f ≫ G.target = g ≫ G.target) :
    G.compose f (G.compose (f ≫ G.inverse) g (by
      rw [Category.assoc, G.source_inverse, ht])) (by
      rw [groupoidCompose_target, Category.assoc, G.target_inverse]) = g := by
  let fi := f ≫ G.inverse
  have wfi : f ≫ G.source = fi ≫ G.target := by
    dsimp [fi]
    rw [Category.assoc, G.target_inverse]
  have wig : fi ≫ G.source = g ≫ G.target := by
    dsimp [fi]
    rw [Category.assoc, G.source_inverse, ht]
  have w₁ : G.compose f fi wfi ≫ G.source = g ≫ G.target := by
    rw [groupoidCompose_source, Category.assoc, G.source_inverse, ht]
  have w₂ : f ≫ G.source = G.compose fi g wig ≫ G.target := by
    rw [groupoidCompose_target, Category.assoc, G.target_inverse]
  change G.compose f (G.compose fi g wig) w₂ = g
  rw [← groupoidCompose_assoc G f fi g wfi wig w₁ w₂]
  calc
    G.compose (G.compose f fi wfi) g w₁ =
        G.compose (g ≫ G.target ≫ G.identity) g (by
          simp [Category.assoc, G.source_identity]) := by
      congr 1
      calc
        G.compose f fi wfi = f ≫ G.target ≫ G.identity :=
          G.right_inverse T f wfi
        _ = g ≫ G.target ≫ G.identity :=
          congrArg (fun k : T ⟶ G.objects => k ≫ G.identity) ht
    _ = g := G.left_identity T g (by simp [Category.assoc, G.source_identity])

/-- Composing `f⁻¹` with `f ∘ h` recovers `h`. -/
private lemma composeLeftDifference {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} (f h : T ⟶ G.arrows)
    (wh : f ≫ G.source = h ≫ G.target) :
    G.compose (f ≫ G.inverse) (G.compose f h wh) (by
      rw [Category.assoc, G.source_inverse, groupoidCompose_target]) = h := by
  let fi := f ≫ G.inverse
  have wfi : fi ≫ G.source = f ≫ G.target := by
    dsimp [fi]
    rw [Category.assoc, G.source_inverse]
  have wfh : f ≫ G.source = h ≫ G.target := wh
  have w₁ : G.compose fi f wfi ≫ G.source = h ≫ G.target := by
    rw [groupoidCompose_source, wfh]
  have w₂ : fi ≫ G.source = G.compose f h wfh ≫ G.target := by
    rw [groupoidCompose_target, Category.assoc, G.source_inverse]
  change G.compose fi (G.compose f h wfh) w₂ = h
  rw [← groupoidCompose_assoc G fi f h wfi wfh w₁ w₂]
  calc
    G.compose (G.compose fi f wfi) h w₁ =
        G.compose (h ≫ G.target ≫ G.identity) h (by
          simp [Category.assoc, G.source_identity]) := by
      congr 1
      calc
        G.compose fi f wfi = f ≫ G.source ≫ G.identity :=
          G.left_inverse T f wfi
        _ = h ≫ G.target ≫ G.identity :=
          congrArg (fun k : T ⟶ G.objects => k ≫ G.identity) wh
    _ = h := G.left_identity T h (by simp [Category.assoc, G.source_identity])

/-- The inverse of the lower comparison morphism, `(f, h) ↦ (f, f ∘ h)`. -/
private noncomputable def bottomInverse {S : Scheme.{u}} (G : GroupoidScheme S) :
    sourceFiberStabilizer G ⟶ parallelArrows G := by
  let f := pullback.fst G.source (pullback.snd (sourceTarget G) (diagonal G))
  let h := pullback.snd G.source (pullback.snd (sourceTarget G) (diagonal G)) ≫
    pullback.fst (sourceTarget G) (diagonal G)
  let c := G.compose f h (sourceFiberStabilizer_compose_condition G)
  refine pullback.lift f c ?_
  apply CartesianMonoidalCategory.hom_ext
  · dsimp [c]
    simp only [sourceTarget, lift_fst, Category.assoc]
    rw [GroupoidScheme.compose, Category.assoc, G.target_comp]
    rw [pullback.lift_fst_assoc]
  · dsimp [c]
    simp only [sourceTarget, lift_snd, Category.assoc]
    simp only [GroupoidScheme.compose, Category.assoc, G.source_comp]
    rw [pullback.lift_snd_assoc]
    dsimp [h]
    rw [Category.assoc, stabilizerProjection_source]
    exact pullback.condition

/-- The first projection of `bottomInverse`. -/
private theorem bottomInverse_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    bottomInverse G ≫ pullback.fst (sourceTarget G) (sourceTarget G) =
      pullback.fst G.source (pullback.snd (sourceTarget G) (diagonal G)) := by
  unfold bottomInverse
  dsimp
  rw [pullback.lift_fst]

/-- The second projection of `bottomInverse`. -/
private theorem bottomInverse_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    bottomInverse G ≫ pullback.snd (sourceTarget G) (sourceTarget G) =
      G.compose (pullback.fst G.source (pullback.snd (sourceTarget G) (diagonal G)))
        (pullback.snd G.source (pullback.snd (sourceTarget G) (diagonal G)) ≫
          pullback.fst (sourceTarget G) (diagonal G))
        (sourceFiberStabilizer_compose_condition G) := by
  unfold bottomInverse
  dsimp
  rw [pullback.lift_snd]

/-- The first projection of the lower comparison morphism. -/
private theorem bottomComparison_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    bottomComparison G ≫ pullback.fst G.source
      (pullback.snd (sourceTarget G) (diagonal G)) =
      pullback.fst (sourceTarget G) (sourceTarget G) := by
  unfold bottomComparison
  rw [pullback.lift_fst]

/-- The second projection of the lower comparison morphism. -/
private theorem bottomComparison_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    bottomComparison G ≫ pullback.snd G.source
      (pullback.snd (sourceTarget G) (diagonal G)) = differenceStabilizer G := by
  unfold bottomComparison
  rw [pullback.lift_snd]

/-- The arrow component of the second projection of the lower comparison morphism. -/
private theorem bottomComparison_differenceArrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    bottomComparison G ≫ pullback.snd G.source
      (pullback.snd (sourceTarget G) (diagonal G)) ≫
      pullback.fst (sourceTarget G) (diagonal G) = differenceArrow G := by
  rw [← Category.assoc, bottomComparison_snd]
  unfold differenceStabilizer
  rw [pullback.lift_fst]

/-- The arrow component of the stabilizer-valued difference. -/
private theorem differenceStabilizer_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    differenceStabilizer G ≫ pullback.fst (sourceTarget G) (diagonal G) =
      differenceArrow G := by
  unfold differenceStabilizer
  rw [pullback.lift_fst]

/-- The base component of the stabilizer-valued difference. -/
private theorem differenceStabilizer_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    differenceStabilizer G ≫ pullback.snd (sourceTarget G) (diagonal G) =
      pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.source := by
  unfold differenceStabilizer
  rw [pullback.lift_snd]

/-- The target of the difference of two parallel arrows. -/
private theorem differenceArrow_target {S : Scheme.{u}} (G : GroupoidScheme S) :
    differenceArrow G ≫ G.target =
      pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.source := by
  calc
    differenceArrow G ≫ G.target =
        (differenceStabilizer G ≫ pullback.fst (sourceTarget G) (diagonal G)) ≫
          G.target :=
      congrArg (fun k => k ≫ G.target) (differenceStabilizer_fst G).symm
    _ = differenceStabilizer G ≫
        (pullback.fst (sourceTarget G) (diagonal G) ≫ G.target) := Category.assoc _ _ _
    _ = differenceStabilizer G ≫ pullback.snd (sourceTarget G) (diagonal G) :=
      congrArg (fun k => differenceStabilizer G ≫ k) (stabilizerProjection_target G)
    _ = pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.source :=
      differenceStabilizer_snd G

/-- The source of the difference of two parallel arrows. -/
private theorem differenceArrow_source {S : Scheme.{u}} (G : GroupoidScheme S) :
    differenceArrow G ≫ G.source =
      pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.source := by
  calc
    differenceArrow G ≫ G.source =
        (differenceStabilizer G ≫ pullback.fst (sourceTarget G) (diagonal G)) ≫
          G.source :=
      congrArg (fun k => k ≫ G.source) (differenceStabilizer_fst G).symm
    _ = differenceStabilizer G ≫
        (pullback.fst (sourceTarget G) (diagonal G) ≫ G.source) := Category.assoc _ _ _
    _ = differenceStabilizer G ≫ pullback.snd (sourceTarget G) (diagonal G) :=
      congrArg (fun k => differenceStabilizer G ≫ k) (stabilizerProjection_source G)
    _ = pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.source :=
      differenceStabilizer_snd G

/-- The first projection of the diagonal of the arrow scheme. -/
private theorem arrowDiagonal_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowDiagonal G ≫ pullback.fst (sourceTarget G) (sourceTarget G) = 𝟙 G.arrows := by
  unfold arrowDiagonal
  rw [pullback.lift_fst]

/-- The second projection of the diagonal of the arrow scheme. -/
private theorem arrowDiagonal_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowDiagonal G ≫ pullback.snd (sourceTarget G) (sourceTarget G) = 𝟙 G.arrows := by
  unfold arrowDiagonal
  rw [pullback.lift_snd]

/-- The first projection of the upper comparison morphism. -/
private theorem topComparison_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    topComparison G ≫ pullback.fst G.source (𝟙 G.objects) = 𝟙 G.arrows := by
  unfold topComparison
  rw [pullback.lift_fst]

/-- The second projection of the upper comparison morphism. -/
private theorem topComparison_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    topComparison G ≫ pullback.snd G.source (𝟙 G.objects) = G.source := by
  unfold topComparison
  rw [pullback.lift_snd]

/-- The first projection of the right-hand vertical map. -/
private theorem rightVertical_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    rightVertical G ≫ pullback.fst G.source
      (pullback.snd (sourceTarget G) (diagonal G)) =
      pullback.fst G.source (𝟙 G.objects) := by
  unfold rightVertical
  rw [pullback.lift_fst]

/-- The second projection of the right-hand vertical map. -/
private theorem rightVertical_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    rightVertical G ≫ pullback.snd G.source
      (pullback.snd (sourceTarget G) (diagonal G)) =
      pullback.snd G.source (𝟙 G.objects) ≫ identityStabilizer G := by
  unfold rightVertical
  rw [pullback.lift_snd]

/-- The arrow component of the identity section of the stabilizer. -/
private theorem identityStabilizer_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    identityStabilizer G ≫ pullback.fst (sourceTarget G) (diagonal G) = G.identity := by
  unfold identityStabilizer
  rw [pullback.lift_fst]

/-- The base component of the identity section of the stabilizer. -/
private theorem identityStabilizer_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    identityStabilizer G ≫ pullback.snd (sourceTarget G) (diagonal G) = 𝟙 G.objects := by
  unfold identityStabilizer
  rw [pullback.lift_snd]

/-- The difference of a pair of equal arrows is an identity. -/
private theorem differenceArrow_diagonal {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowDiagonal G ≫ differenceArrow G =
      𝟙 G.arrows ≫ G.source ≫ G.identity := by
  let f := pullback.fst (sourceTarget G) (sourceTarget G)
  let g := pullback.snd (sourceTarget G) (sourceTarget G)
  have hfg : f ≫ G.target = g ≫ G.target := parallelArrows_target_eq G
  have w : (f ≫ G.inverse) ≫ G.source = g ≫ G.target := by
    rw [Category.assoc, G.source_inverse, hfg]
  have w' : (arrowDiagonal G ≫ (f ≫ G.inverse)) ≫ G.source =
      (arrowDiagonal G ≫ g) ≫ G.target := by
    simpa only [Category.assoc] using arrowDiagonal G ≫= w
  have w0 : (𝟙 G.arrows ≫ G.inverse) ≫ G.source =
      𝟙 G.arrows ≫ G.target := by
    simpa [Category.assoc] using G.source_inverse
  calc
    arrowDiagonal G ≫ differenceArrow G =
        G.compose (arrowDiagonal G ≫ (f ≫ G.inverse)) (arrowDiagonal G ≫ g) w' :=
      (groupoidCompose_precomp G (arrowDiagonal G) (f ≫ G.inverse) g w w').symm
    _ = G.compose (𝟙 G.arrows ≫ G.inverse) (𝟙 G.arrows) w0 := by
      congr 1
      · rw [← Category.assoc, arrowDiagonal_fst]
      · exact arrowDiagonal_snd G
    _ = 𝟙 G.arrows ≫ G.source ≫ G.identity :=
      G.left_inverse G.arrows (𝟙 G.arrows) w0

/-- The difference arrow restricted along the diagonal of arrows is the identity stabilizer
over the source. -/
lemma arrowDiagonal_differenceStabilizer {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowDiagonal G ≫ differenceStabilizer G = G.source ≫ identityStabilizer G := by
  apply pullback.hom_ext
  · calc
      (arrowDiagonal G ≫ differenceStabilizer G) ≫
          pullback.fst (sourceTarget G) (diagonal G) =
          arrowDiagonal G ≫
            (differenceStabilizer G ≫ pullback.fst (sourceTarget G) (diagonal G)) :=
        Category.assoc _ _ _
      _ = arrowDiagonal G ≫ differenceArrow G :=
        congrArg (fun k => arrowDiagonal G ≫ k) (differenceStabilizer_fst G)
      _ = 𝟙 G.arrows ≫ G.source ≫ G.identity := differenceArrow_diagonal G
      _ = G.source ≫ G.identity := by simp
      _ = G.source ≫ (identityStabilizer G ≫
          pullback.fst (sourceTarget G) (diagonal G)) := by
        rw [identityStabilizer_fst]
  · calc
      (arrowDiagonal G ≫ differenceStabilizer G) ≫
          pullback.snd (sourceTarget G) (diagonal G) =
          arrowDiagonal G ≫
            (differenceStabilizer G ≫ pullback.snd (sourceTarget G) (diagonal G)) :=
        Category.assoc _ _ _
      _ = arrowDiagonal G ≫
          (pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.source) :=
        congrArg (fun k => arrowDiagonal G ≫ k) (differenceStabilizer_snd G)
      _ = G.source := by
        calc
          _ = (arrowDiagonal G ≫ pullback.fst (sourceTarget G) (sourceTarget G)) ≫
              G.source := (Category.assoc _ _ _).symm
          _ = 𝟙 G.arrows ≫ G.source :=
            congrArg (fun k => k ≫ G.source) (arrowDiagonal_fst G)
          _ = G.source := Category.id_comp _
      _ = G.source ≫ (identityStabilizer G ≫
          pullback.snd (sourceTarget G) (diagonal G)) := by
        rw [identityStabilizer_snd, Category.comp_id]

/-- The left-hand part of the displayed diagonal diagram commutes. -/
@[stacks 02YH "commutativity of the diagram"]
lemma diagonalDiagram_commutes {S : Scheme.{u}} (G : GroupoidScheme S) :
    arrowDiagonal G ≫ bottomComparison G = topComparison G ≫ rightVertical G := by
  have hstab := arrowDiagonal_differenceStabilizer G
  apply pullback.hom_ext
  · calc
      (arrowDiagonal G ≫ bottomComparison G) ≫
          pullback.fst G.source (pullback.snd (sourceTarget G) (diagonal G)) =
          arrowDiagonal G ≫ (bottomComparison G ≫
            pullback.fst G.source (pullback.snd (sourceTarget G) (diagonal G))) :=
        Category.assoc _ _ _
      _ = arrowDiagonal G ≫ pullback.fst (sourceTarget G) (sourceTarget G) :=
        congrArg (fun k => arrowDiagonal G ≫ k) (bottomComparison_fst G)
      _ = 𝟙 G.arrows := arrowDiagonal_fst G
      _ = topComparison G ≫
          (rightVertical G ≫ pullback.fst G.source
            (pullback.snd (sourceTarget G) (diagonal G))) := by
        rw [rightVertical_fst, topComparison_fst]
  · calc
      (arrowDiagonal G ≫ bottomComparison G) ≫
          pullback.snd G.source (pullback.snd (sourceTarget G) (diagonal G)) =
          arrowDiagonal G ≫
            (bottomComparison G ≫
              pullback.snd G.source (pullback.snd (sourceTarget G) (diagonal G))) :=
        Category.assoc _ _ _
      _ = arrowDiagonal G ≫ differenceStabilizer G :=
        congrArg (fun k => arrowDiagonal G ≫ k) (bottomComparison_snd G)
      _ = G.source ≫ identityStabilizer G := hstab
      _ = topComparison G ≫
          (rightVertical G ≫ pullback.snd G.source
            (pullback.snd (sourceTarget G) (diagonal G))) := by
        rw [rightVertical_snd, ← Category.assoc, topComparison_snd]

/-- The upper comparison morphism in the diagonal diagram is an isomorphism. -/
@[stacks 02YH "the upper horizontal arrow"]
lemma topComparison_isIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsIso (topComparison G) := by
  have h : topComparison G = inv (pullback.fst G.source (𝟙 G.objects)) := by
    apply (cancel_mono (pullback.fst G.source (𝟙 G.objects))).1
    rw [IsIso.inv_hom_id]
    change pullback.lift (𝟙 G.arrows) G.source (by simp) ≫
      pullback.fst G.source (𝟙 G.objects) = _
    rw [pullback.lift_fst]
  rw [h]
  infer_instance

private lemma bottomComparison_comp_bottomInverse {S : Scheme.{u}} (G : GroupoidScheme S) :
    bottomComparison G ≫ bottomInverse G = 𝟙 _ := by
  apply pullback.hom_ext
  · change (bottomComparison G ≫ bottomInverse G) ≫
      pullback.fst (sourceTarget G) (sourceTarget G) = _
    rw [Category.assoc, bottomInverse_fst]
    dsimp [bottomComparison]
    rw [pullback.lift_fst]
    simp
  · rw [Category.assoc]
    dsimp [bottomInverse]
    rw [pullback.lift_snd]
    let f := pullback.fst G.source (pullback.snd (sourceTarget G) (diagonal G))
    let h := pullback.snd G.source (pullback.snd (sourceTarget G) (diagonal G)) ≫
      pullback.fst (sourceTarget G) (diagonal G)
    have w := sourceFiberStabilizer_compose_condition G
    have w' : (bottomComparison G ≫ f) ≫ G.source =
        (bottomComparison G ≫ h) ≫ G.target := by
      rw [bottomComparison_fst, bottomComparison_differenceArrow]
      exact (differenceArrow_target G).symm
    change bottomComparison G ≫ G.compose f h w =
      pullback.snd (sourceTarget G) (sourceTarget G)
    calc
      bottomComparison G ≫ G.compose f h w =
          G.compose (bottomComparison G ≫ f) (bottomComparison G ≫ h) w' :=
        (groupoidCompose_precomp G (bottomComparison G) f h w w').symm
      _ = pullback.snd (sourceTarget G) (sourceTarget G) := by
        convert composeRightDifference G
          (pullback.fst (sourceTarget G) (sourceTarget G))
          (pullback.snd (sourceTarget G) (sourceTarget G)) (parallelArrows_target_eq G) using 1
        congr 1
        · exact bottomComparison_fst G
        · exact bottomComparison_differenceArrow G

private lemma bottomInverse_bottomComparison_differenceArrow {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    bottomInverse G ≫ (bottomComparison G ≫
      (pullback.snd G.source (pullback.snd (sourceTarget G) (diagonal G)) ≫
        pullback.fst (sourceTarget G) (diagonal G))) =
      pullback.snd G.source (pullback.snd (sourceTarget G) (diagonal G)) ≫
        pullback.fst (sourceTarget G) (diagonal G) := by
  let f := pullback.fst G.source (pullback.snd (sourceTarget G) (diagonal G))
  let h := pullback.snd G.source (pullback.snd (sourceTarget G) (diagonal G)) ≫
    pullback.fst (sourceTarget G) (diagonal G)
  have wfh := sourceFiberStabilizer_compose_condition G
  have wdiff :
      (pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.inverse) ≫ G.source =
        pullback.snd (sourceTarget G) (sourceTarget G) ≫ G.target := by
    rw [Category.assoc, G.source_inverse, parallelArrows_target_eq G]
  have wdiff' :
      (bottomInverse G ≫
          (pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.inverse)) ≫
        G.source =
        (bottomInverse G ≫ pullback.snd (sourceTarget G) (sourceTarget G)) ≫
          G.target := by
    calc
      _ = bottomInverse G ≫
          ((pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.inverse) ≫
            G.source) :=
        Category.assoc _ _ _
      _ = bottomInverse G ≫
          (pullback.snd (sourceTarget G) (sourceTarget G) ≫ G.target) :=
        congrArg (fun k => bottomInverse G ≫ k) wdiff
      _ = _ := (Category.assoc _ _ _).symm
  have h1 : bottomInverse G ≫
      (pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.inverse) =
        f ≫ G.inverse :=
    congrArg (fun k => k ≫ G.inverse) (bottomInverse_fst G)
  have h2 : bottomInverse G ≫ pullback.snd (sourceTarget G) (sourceTarget G) =
      G.compose f h wfh := bottomInverse_snd G
  rw [bottomComparison_differenceArrow]
  change bottomInverse G ≫ G.compose
    (pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.inverse)
    (pullback.snd (sourceTarget G) (sourceTarget G)) wdiff = _
  calc
    bottomInverse G ≫ G.compose
        (pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.inverse)
        (pullback.snd (sourceTarget G) (sourceTarget G)) wdiff =
        G.compose
          (bottomInverse G ≫
            (pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.inverse))
          (bottomInverse G ≫
            pullback.snd (sourceTarget G) (sourceTarget G)) wdiff' :=
      (groupoidCompose_precomp G (bottomInverse G)
        (pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.inverse)
        (pullback.snd (sourceTarget G) (sourceTarget G)) wdiff wdiff').symm
    _ = G.compose (f ≫ G.inverse) (G.compose f h wfh) _ := by
      congr 1
    _ = h := composeLeftDifference G f h wfh

private lemma bottomInverse_comp_bottomComparison {S : Scheme.{u}} (G : GroupoidScheme S) :
    bottomInverse G ≫ bottomComparison G = 𝟙 _ := by
  apply pullback.hom_ext
  · change (bottomInverse G ≫ bottomComparison G) ≫
      pullback.fst G.source (pullback.snd (sourceTarget G) (diagonal G)) = _
    rw [Category.assoc]
    dsimp [bottomComparison]
    rw [pullback.lift_fst]
    exact bottomInverse_fst G
  · apply pullback.hom_ext
    · exact bottomInverse_bottomComparison_differenceArrow G
    · calc
        ((bottomInverse G ≫ bottomComparison G) ≫
            pullback.snd G.source (pullback.snd (sourceTarget G) (diagonal G))) ≫
            pullback.snd (sourceTarget G) (diagonal G) =
            bottomInverse G ≫
              ((bottomComparison G ≫
                pullback.snd G.source
                  (pullback.snd (sourceTarget G) (diagonal G))) ≫
                pullback.snd (sourceTarget G) (diagonal G)) := by
          simp only [Category.assoc]
        _ = bottomInverse G ≫
            (pullback.fst (sourceTarget G) (sourceTarget G) ≫ G.source) := by
          rw [bottomComparison_snd, differenceStabilizer_snd]
        _ = pullback.snd G.source (pullback.snd (sourceTarget G) (diagonal G)) ≫
            pullback.snd (sourceTarget G) (diagonal G) := by
          have h := congrArg (fun k => k ≫ G.source) (bottomInverse_fst G)
          simpa [Category.assoc] using h.trans (pullback.condition (f := G.source)
            (g := pullback.snd (sourceTarget G) (diagonal G)))

/-- The lower comparison morphism in the diagonal diagram is an isomorphism, with inverse
`(f, h) ↦ (f, f ∘ h)`. -/
@[stacks 02YH "the lower horizontal arrow"]
lemma bottomComparison_isIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsIso (bottomComparison G) :=
  ⟨⟨bottomInverse G, bottomComparison_comp_bottomInverse G,
    bottomInverse_comp_bottomComparison G⟩⟩

/-- The right-hand square in the diagonal diagram is a pullback square. -/
@[stacks 02YH "the right square"]
lemma rightSquare_isPullback {S : Scheme.{u}} (G : GroupoidScheme S) :
    IsPullback (pullback.snd G.source (𝟙 G.objects)) (rightVertical G)
      (identityStabilizer G) (pullback.snd G.source
        (pullback.snd (sourceTarget G) (diagonal G))) := by
  let q := pullback.snd (sourceTarget G) (diagonal G)
  let a₁ := pullback.fst G.source (𝟙 G.objects)
  let a₂ := pullback.snd G.source (𝟙 G.objects)
  let b₁ := pullback.fst G.source q
  let b₂ := pullback.snd G.source q
  let c := PullbackCone.mk a₂ (rightVertical G) (by rw [rightVertical_snd])
  let lift (s : PullbackCone (identityStabilizer G) b₂) : s.pt ⟶
      pullback G.source (𝟙 G.objects) := by
    have hbase : s.fst = (s.snd ≫ b₁) ≫ G.source := by
      calc
        s.fst = s.fst ≫ (identityStabilizer G ≫ q) := by
          rw [identityStabilizer_snd, Category.comp_id]
        _ = (s.fst ≫ identityStabilizer G) ≫ q := (Category.assoc _ _ _).symm
        _ = (s.snd ≫ b₂) ≫ q := congrArg (fun k => k ≫ q) s.condition
        _ = s.snd ≫ (b₂ ≫ q) := Category.assoc _ _ _
        _ = s.snd ≫ (b₁ ≫ G.source) :=
          congrArg (fun k => s.snd ≫ k)
            (pullback.condition (f := G.source) (g := q)).symm
        _ = (s.snd ≫ b₁) ≫ G.source := (Category.assoc _ _ _).symm
    have w : (s.snd ≫ b₁) ≫ G.source = s.fst ≫ 𝟙 G.objects := by
      rw [Category.comp_id]
      exact hbase.symm
    exact pullback.lift (s.snd ≫ b₁) s.fst w
  have lift_fst (s : PullbackCone (identityStabilizer G) b₂) :
      lift s ≫ a₁ = s.snd ≫ b₁ := by
    dsimp [lift]
    rw [pullback.lift_fst]
  have lift_snd (s : PullbackCone (identityStabilizer G) b₂) :
      lift s ≫ a₂ = s.fst := by
    dsimp [lift]
    rw [pullback.lift_snd]
  refine IsPullback.of_isLimit (c := c) ?_
  refine PullbackCone.IsLimit.mk c.condition lift ?_ ?_ ?_
  · intro s
    exact lift_snd s
  · intro s
    change lift s ≫ rightVertical G = s.snd
    apply pullback.hom_ext
    · calc
        (lift s ≫ rightVertical G) ≫ b₁ = lift s ≫ (rightVertical G ≫ b₁) :=
          Category.assoc _ _ _
        _ = lift s ≫ a₁ := congrArg (fun k => lift s ≫ k) (rightVertical_fst G)
        _ = s.snd ≫ b₁ := lift_fst s
    · calc
        (lift s ≫ rightVertical G) ≫ b₂ = lift s ≫ (rightVertical G ≫ b₂) :=
          Category.assoc _ _ _
        _ = lift s ≫ (a₂ ≫ identityStabilizer G) :=
          congrArg (fun k => lift s ≫ k) (rightVertical_snd G)
        _ = (lift s ≫ a₂) ≫ identityStabilizer G :=
          (Category.assoc _ _ _).symm
        _ = s.fst ≫ identityStabilizer G :=
          congrArg (fun k => k ≫ identityStabilizer G) (lift_snd s)
        _ = s.snd ≫ b₂ := s.condition
  · intro s m hm₁ hm₂
    apply pullback.hom_ext (f := G.source) (g := 𝟙 G.objects)
    · calc
        m ≫ a₁ = m ≫ (rightVertical G ≫ b₁) :=
          congrArg (fun k => m ≫ k) (rightVertical_fst G).symm
        _ = (m ≫ rightVertical G) ≫ b₁ := (Category.assoc _ _ _).symm
        _ = s.snd ≫ b₁ := congrArg (fun k => k ≫ b₁) hm₂
        _ = lift s ≫ a₁ := (lift_fst s).symm
    · calc
        m ≫ a₂ = s.fst := hm₁
        _ = lift s ≫ a₂ := (lift_snd s).symm

end AlgebraicGeometry

end
