module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# Descending a retract of a base change along a cofiltered limit

Let a scheme be the limit of a cofiltered system of quasi-compact and quasi-separated schemes
whose transition morphisms are affine, and let `X` be a scheme over that limit.  If `X` is a
retract, over the limit, of the base change of a scheme of finite presentation over one stage,
then `X` itself is the base change of a scheme of finite presentation over some stage.

This is the second half of the proof of part (1) of tag 01ZM: the first half exhibits a scheme of
finite presentation over the limit as such a retract.  Nothing here uses finite presentation of
`X` as a hypothesis -- it is a *consequence*, because finite presentation is stable under
retracts in an over category.

## Main results

* `AlgebraicGeometry.LimitFPObjectDescent.finitePresentation_of_retract`: finite presentation is
  stable under retracts in an over category.
* `AlgebraicGeometry.LimitFPObjectDescent.exists_model_of_retract`: a retract of a base change
  of a scheme of finite presentation over a stage is itself such a base change.

## Implementation notes

The retraction `s ≫ r = 𝟙 X` makes `p = r ≫ s` an idempotent endomorphism of the base change
whose image is `X`.  Part (2) of tag 01ZM descends `p` to a morphism `g` at a later stage, and
part (3) makes `g` itself idempotent at a yet later stage; splitting that idempotent in the over
category of the stage -- which has equalizers, schemes having all finite limits -- produces the
model.  The identification of the two comparison isomorphisms supplied by part (2) uses
`AlgebraicGeometry.iso_eq_overPullbackCompIso`: compatibility with the first pullback projection
pins such an isomorphism down, so the isomorphism produced for the source equals the one produced
for the target and the descended morphism is an endomorphism rather than a morphism between two
different objects.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace AlgebraicGeometry.LimitFPObjectDescent

/-- Base change preserves finite presentation of a scheme over a base. -/
theorem finitePresentation_overPullback {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S)
    (hX : FinitePresentation X.hom) :
    FinitePresentation ((Over.pullback f).obj X).hom := by
  change FinitePresentation (pullback.snd X.hom f)
  obtain ⟨_, _, _⟩ := hX
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Finite presentation is stable under retracts in an over category: if `X` is a retract of `Y`
over `S` and `Y` is of finite presentation over `S`, then so is `X`.

The section `X ⟶ Y` is of finite presentation by tag 02FV, because its composite with `Y ⟶ S` is
the structure morphism of `X`, which is of finite presentation since it is a retraction composed
with that morphism. -/
theorem finitePresentation_of_retract {S : Scheme.{u}} {X Y : Over S}
    (s : X ⟶ Y) (r : Y ⟶ X) (hsr : s ≫ r = 𝟙 X) (hY : FinitePresentation Y.hom) :
    FinitePresentation X.hom := by
  obtain ⟨_, _, _⟩ := hY
  have : LocallyOfFiniteType (r.left ≫ X.hom) := by rw [Over.w r]; infer_instance
  have : QuasiSeparated (r.left ≫ X.hom) := by rw [Over.w r]; infer_instance
  have : LocallyOfFiniteType r.left := locallyOfFiniteType_of_comp r.left X.hom
  have : QuasiSeparated r.left := QuasiSeparated.of_comp r.left X.hom
  obtain ⟨_, _, _⟩ := finitePresentation_of_comp s.left r.left (by
    rw [← Over.comp_left, hsr, Over.id_left]
    exact ⟨inferInstance, inferInstance, inferInstance⟩)
  rw [← Over.w s]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) (c : Cone D)
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

/-- A scheme over the limit which is a retract of the base change of a scheme of finite
presentation over some stage is itself the base change of a scheme of finite presentation over
some stage. -/
theorem exists_model_of_retract (hc : IsLimit c) (X : Over c.pt) (i : I) (Y : Over (D.obj i))
    (hY : FinitePresentation Y.hom) (s : X ⟶ (Over.pullback (c.π.app i)).obj Y)
    (r : (Over.pullback (c.π.app i)).obj Y ⟶ X) (hsr : s ≫ r = 𝟙 X) :
    ∃ (j : I) (Xⱼ : Over (D.obj j)), FinitePresentation Xⱼ.hom ∧
      Nonempty (X ≅ (Over.pullback (c.π.app j)).obj Xⱼ) := by
  -- Name the idempotent `p = r ≫ s` opaquely, with its defining equation, so that the rewrites
  -- below cannot unfold it.
  obtain ⟨p, hp0⟩ : ∃ p : (Over.pullback (c.π.app i)).obj Y ⟶ (Over.pullback (c.π.app i)).obj Y,
      p = r ≫ s := ⟨_, rfl⟩
  have hp : p ≫ p = p := by
    rw [hp0, Category.assoc, ← Category.assoc s r s, hsr, Category.id_comp]
  have hpr : p ≫ r = r := by rw [hp0, Category.assoc, hsr, Category.comp_id]
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ := exists_morphism_after_baseChange D c hc i Y Y hY hY p
  -- Compatibility with the first pullback projection identifies the two comparison isomorphisms,
  -- so `g` is an endomorphism of a single object rather than a morphism between two.
  obtain rfl : α = β :=
    (iso_eq_overPullbackCompIso _ _ _ (c.w e) Y α hα).trans
      (iso_eq_overPullbackCompIso _ _ _ (c.w e) Y β hβ).symm
  have hYj : FinitePresentation ((Over.pullback (D.map e)).obj Y).hom :=
    finitePresentation_overPullback _ Y hY
  -- `g` is idempotent after base change to the limit, hence at some later stage.
  have hgg : (Over.pullback (c.π.app j)).map (g ≫ g) = (Over.pullback (c.π.app j)).map g := by
    apply (cancel_mono α.hom).1
    rw [Functor.map_comp, Category.assoc, ← hg, ← Category.assoc, ← hg, Category.assoc, hp, hg]
  obtain ⟨k, a, ha⟩ := eventually_eq_of_baseChange_eq D c hc j _ _ hYj hYj (g ≫ g) g hgg
  obtain ⟨q, hq0⟩ : ∃ q : (Over.pullback (D.map a)).obj ((Over.pullback (D.map e)).obj Y) ⟶
      (Over.pullback (D.map a)).obj ((Over.pullback (D.map e)).obj Y),
      q = (Over.pullback (D.map a)).map g := ⟨_, rfl⟩
  have hq : q ≫ q = q := by rw [hq0, ← Functor.map_comp]; exact ha
  -- Split the idempotent `q` in the over category of the stage `k`.  Schemes have all finite
  -- limits, so that over category has equalizers and is idempotent complete.
  have : IsIdempotentComplete (Over (D.obj k)) :=
    (Idempotents.isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent _).2
      (fun _ _ _ => inferInstance)
  obtain ⟨Z, z, t, hzt, htz⟩ := IsIdempotentComplete.idempotents_split _ q hq
  have hZ : FinitePresentation Z.hom :=
    finitePresentation_of_retract z t hzt
      (finitePresentation_overPullback _ _ hYj)
  obtain ⟨δ, hδ0⟩ : ∃ δ : (Over.pullback (c.π.app k)).obj
        ((Over.pullback (D.map a)).obj ((Over.pullback (D.map e)).obj Y)) ≅
        (Over.pullback (c.π.app i)).obj Y,
      δ = overPullbackCompIso (D.map a) (c.π.app k) (c.π.app j) (c.w a)
        ((Over.pullback (D.map e)).obj Y) ≪≫ α := ⟨_, rfl⟩
  have hδ : (Over.pullback (c.π.app k)).map q ≫ δ.hom = δ.hom ≫ p := by
    rw [hδ0, hq0, Iso.trans_hom, ← Category.assoc,
      ← overPullbackCompIso_naturality (D.map a) (c.π.app k) (c.π.app j) (c.w a) g,
      Category.assoc, Category.assoc, hg]
  have htz' : (Over.pullback (c.π.app k)).map t ≫ (Over.pullback (c.π.app k)).map z =
      (Over.pullback (c.π.app k)).map q := by rw [← Functor.map_comp, htz]
  have hzt' : (Over.pullback (c.π.app k)).map z ≫ (Over.pullback (c.π.app k)).map t = 𝟙 _ := by
    rw [← Functor.map_comp, hzt]
    simp
  refine ⟨k, Z, hZ, ⟨{
    hom := s ≫ δ.inv ≫ (Over.pullback (c.π.app k)).map t
    inv := (Over.pullback (c.π.app k)).map z ≫ δ.hom ≫ r
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩⟩
  · simp only [Category.assoc, reassoc_of% htz', reassoc_of% hδ, δ.inv_hom_id_assoc]
    rw [hpr]
    exact hsr
  · have hzq : (Over.pullback (c.π.app k)).map z ≫ (Over.pullback (c.π.app k)).map q =
        (Over.pullback (c.π.app k)).map z := by
      rw [← htz', ← Category.assoc, hzt', Category.id_comp]
    have he : (Over.pullback (c.π.app k)).map z ≫ δ.hom ≫ p ≫ δ.inv ≫
        (Over.pullback (c.π.app k)).map t = 𝟙 _ := by
      rw [← reassoc_of% hδ, δ.hom_inv_id_assoc, ← Category.assoc, hzq, hzt']
    rw [hp0] at he
    simpa only [Category.assoc] using he

end AlgebraicGeometry.LimitFPObjectDescent
