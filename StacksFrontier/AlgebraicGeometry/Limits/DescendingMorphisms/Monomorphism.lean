module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Diagonal

/-!
# Monomorphisms descend to a finite stage

Let a scheme be the limit of a cofiltered diagram of schemes with affine transition morphisms. A
morphism at one stage which is locally of finite type and becomes a monomorphism after base change
to the limit is already a monomorphism after base change to some later stage.

## Main results

* `AlgebraicGeometry.exists_mono_baseChange_of_mono_limitBaseChange` descends the monomorphism
  property from the inverse limit to a finite stage.

## Implementation notes

Schemes over the chosen stage are represented by objects of its over category, and their base
changes by `CategoryTheory.Over.pullback`. A morphism `g : i ⟶ i₀` expresses that `i` is a later
stage than `i₀`. The source uses a directed preorder; a cofiltered category is the natural
categorical generalization.

A morphism is a monomorphism exactly when its diagonal is an isomorphism, and the diagonal is here
realised inside the over category on the underlying pullback of schemes, which is what makes the
finite-presentation statement for diagonals directly applicable.

## References

* [Stacks Project, Tag 07RQ](https://stacks.math.columbia.edu/tag/07RQ)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A square in an over category is a pullback as soon as the underlying square is. -/
private theorem isPullback_over_of_isPullback_left {C : Type*} [Category C] {S : C}
    {P X Y Z : Over S} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst.left snd.left f.left g.left) : IsPullback fst snd f g :=
  IsPullback.of_isLimit <| PullbackCone.IsLimit.mk (Over.OverMorphism.ext (by simpa using h.w))
    (fun s => Over.homMk (h.lift s.fst.left s.snd.left
      (by simpa using congrArg CommaMorphism.left s.condition))
      (by rw [← Over.w fst, ← Category.assoc, h.lift_fst, Over.w s.fst]))
    (fun s => Over.OverMorphism.ext (by simp)) (fun s => Over.OverMorphism.ext (by simp))
    fun s m hm₁ hm₂ => Over.OverMorphism.ext <| h.hom_ext
      (by simpa using congrArg CommaMorphism.left hm₁)
      (by simpa using congrArg CommaMorphism.left hm₂)

/-- In a pullback square of a morphism with itself, a common section of the two projections is an
isomorphism as soon as the morphism is a monomorphism. -/
private theorem isIso_diagonal_of_isPullback {C : Type*} [Category C] {P X Y : C} {p₁ : P ⟶ X}
    {p₂ : P ⟶ X} {f : X ⟶ Y} (h : IsPullback p₁ p₂ f f) (d : X ⟶ P) (hd₁ : d ≫ p₁ = 𝟙 X)
    [Mono f] : IsIso d := by
  have : IsIso p₁ := h.isIso_fst_of_mono
  exact isIso_of_comp_hom_eq_id p₁ hd₁

/-- Conversely, a morphism whose diagonal is an isomorphism is a monomorphism. -/
private theorem mono_of_isIso_diagonal_of_isPullback {C : Type*} [Category C] {P X Y : C}
    {p₁ : P ⟶ X} {p₂ : P ⟶ X} {f : X ⟶ Y} (h : IsPullback p₁ p₂ f f) (d : X ⟶ P)
    (hd₁ : d ≫ p₁ = 𝟙 X) (hd₂ : d ≫ p₂ = 𝟙 X) [IsIso d] : Mono f := by
  refine ⟨fun a b hab => ?_⟩
  calc
    a = h.lift a b hab ≫ p₁ := (h.lift_fst a b hab).symm
    _ = h.lift a b hab ≫ p₂ :=
      congrArg _ ((IsIso.inv_eq_of_hom_inv_id hd₁).symm.trans (IsIso.inv_eq_of_hom_inv_id hd₂))
    _ = b := h.lift_snd a b hab

/-- **Stacks 07RQ.** A locally finite type morphism which becomes a monomorphism over the
inverse limit is a monomorphism at some later stage. -/
@[stacks 07RQ]
lemma exists_mono_baseChange_of_mono_limitBaseChange
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (S : I ⥤ Scheme.{u})
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (S.map g)]
    (c : Cone S) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (S.obj i₀)) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace (S.obj i₀)] [QuasiSeparatedSpace (S.obj i₀)]
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFiniteType f₀.left]
    [Mono ((Over.pullback (c.π.app i₀)).map f₀).left] :
    ∃ (i : I) (g : i ⟶ i₀), Mono ((Over.pullback (S.map g)).map f₀).left := by
  have : QuasiSeparated f₀.left := QuasiSeparated.of_comp f₀.left Y₀.hom
  let D : Over (S.obj i₀) := Over.mk (pullback.fst f₀.left f₀.left ≫ X₀.hom)
  let p₁ : D ⟶ X₀ := Over.homMk (pullback.fst f₀.left f₀.left) rfl
  let p₂ : D ⟶ X₀ := Over.homMk (pullback.snd f₀.left f₀.left) (by
    dsimp [D]
    rw [← Over.w f₀, pullback.condition_assoc])
  let d : X₀ ⟶ D := Over.homMk (pullback.diagonal f₀.left) (by
    dsimp [D]
    simp)
  have hD : IsPullback p₁ p₂ f₀ f₀ :=
    isPullback_over_of_isPullback_left (IsPullback.of_hasPullback f₀.left f₀.left)
  have : LocallyOfFinitePresentation d.left := locallyOfFinitePresentation_diagonal f₀.left
  have : CompactSpace D.left := by
    dsimp [D]
    infer_instance
  have : QuasiSeparatedSpace D.left := by
    dsimp [D]
    apply (quasiSeparatedSpace_iff_quasiSeparated _).mpr
    have : QuasiSeparated (pullback.fst f₀.left f₀.left) := inferInstance
    convert (inferInstance : QuasiSeparated
      (pullback.fst f₀.left f₀.left ≫ terminal.from X₀.left)) using 1
    ext
  let F := Over.pullback (c.π.app i₀)
  have : PreservesLimitsOfSize.{u, u} F :=
    (Over.mapPullbackAdj (c.π.app i₀)).rightAdjoint_preservesLimits
  have hd₁ : d ≫ p₁ = 𝟙 X₀ := by
    apply (Over.forget (S.obj i₀)).map_injective
    simp [d, p₁]
  have hd₂ : d ≫ p₂ = 𝟙 X₀ := by
    apply (Over.forget (S.obj i₀)).map_injective
    simp [d, p₂]
  have : Mono (F.map f₀) := Over.mono_of_mono_left (F.map f₀)
  have : IsIso (F.map d) := isIso_diagonal_of_isPullback (hD.map F) (F.map d)
    (by rw [← F.map_comp, hd₁, F.map_id])
  have : IsIso (F.map d).left := by
    simpa using (inferInstance : IsIso ((Over.forget _).map (F.map d)))
  obtain ⟨i, g, hi⟩ :=
    exists_isIso_baseChange_of_isIso_limitBaseChange S c hc i₀ X₀ D d
  refine ⟨i, g, ?_⟩
  let G := Over.pullback (S.map g)
  have : IsIso (G.map d).left := hi
  have : IsIso ((Over.forget _).map (G.map d)) := by
    simpa using (inferInstance : IsIso (G.map d).left)
  have : IsIso (G.map d) := isIso_of_reflects_iso (G.map d) (Over.forget _)
  have : Mono (G.map f₀) := mono_of_isIso_diagonal_of_isPullback (hD.map G) (G.map d)
    (by rw [← G.map_comp, hd₁, G.map_id]) (by rw [← G.map_comp, hd₂, G.map_id])
  exact Over.mono_left_of_mono (G.map f₀)

end AlgebraicGeometry
