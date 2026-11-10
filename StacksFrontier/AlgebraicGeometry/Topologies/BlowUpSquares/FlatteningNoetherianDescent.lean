module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianApproximation.Absolute
public import StacksFrontier.AlgebraicGeometry.LimitFPObjectDescent.Retract
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.FlatOverOpenBaseChange

/-!
# A finitely presented morphism, flat over a quasi-compact open, descends to a Noetherian stage

Let `Y` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ Y` be of finite presentation
and let `V ⊆ Y` be a quasi-compact open over which `f` is flat.  Writing `Y` as the inverse limit
of a cofiltered system of schemes with affine transition morphisms — absolute Noetherian
approximation, Stacks 01ZA — all three pieces of data descend to one stage: the morphism by
Stacks 01ZM, the open by Stacks 01Z4 and the flatness by Stacks 04AI.

This is the reduction step of the proof of Stacks 0EVC, which is proved over a Noetherian base
and then transported to the general case by base change.

## Main results

* `AlgebraicGeometry.exists_stage_model_of_flat_over_open`: the descent of the triple to a stage
  of a cofiltered limit.
* `AlgebraicGeometry.exists_noetherian_model_of_flat_over_open`: the same with the stage
  Noetherian, for a quasi-compact quasi-separated base.

## Implementation notes

The three descents happen at three different stages and are merged by passing to a common later
stage, which is where `AlgebraicGeometry.exists_isPullback_pullback_snd_of_stage` is used: it
transports the cartesian square exhibiting `f` as the base change of a stage morphism along a
transition morphism of the system.  The open is transported by taking its inverse image, which
stays quasi-compact because the transition morphisms are affine, hence quasi-compact.

Flatness over an open is not of the shape the descent result Stacks 04AI is stated in — that one
descends a property of the structure morphism of an object over a stage — so it is first
translated by `AlgebraicGeometry.flat_morphismRestrict_iff_flat_pullback_snd_of_isPullback` into
flatness of the base change of the morphism `f₀⁻¹(V₀) ⟶ Y₀`, and translated back at the later
stage by the same lemma.

## References

* [Stacks Project, Tag 0EVC](https://stacks.math.columbia.edu/tag/0EVC)
* [Stacks Project, Tag 01ZA](https://stacks.math.columbia.edu/tag/01ZA)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The cartesian square exhibiting a morphism to the limit as a base change moves to a later
stage.** If `f` is the base change of the structure morphism of an object over the stage `i`, it
is also the base change of the structure morphism of the inverse image of that object over any
later stage `j`. -/
public theorem exists_isPullback_pullback_snd_of_stage {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) {X : Scheme.{u}} (f : X ⟶ c.pt) {i j : I} (g : j ⟶ i)
    (X₀ : Over (D.obj i)) {w : X ⟶ X₀.left} (hw : IsPullback f w (c.π.app i) X₀.hom) :
    ∃ w' : X ⟶ pullback X₀.hom (D.map g),
      IsPullback f w' (c.π.app j) (pullback.snd X₀.hom (D.map g)) := by
  have hcw : c.π.app j ≫ D.map g = c.π.app i := c.w g
  refine ⟨pullback.lift w (f ≫ c.π.app j) (by rw [Category.assoc, hcw, ← hw.w]), ?_⟩
  refine IsPullback.of_bot (h₂₁ := pullback.snd X₀.hom (D.map g)) ?_ ?_
    (IsPullback.of_hasPullback X₀.hom (D.map g)).flip
  · rwa [pullback.lift_fst, hcw]
  · rw [pullback.lift_snd]

/-- **Flatness over a quasi-compact open descends along a cofiltered limit.** If `f` is the base
change of a finitely presented `X₀` over the stage `i` and `f` is flat over the inverse image of a
quasi-compact open `V₀` of that stage, then over some later stage `j` the base change of `X₀` is
flat over the inverse image of `V₀`. -/
public theorem exists_flat_morphismRestrict_pullback_snd_of_stage {I : Type u} [Category.{u} I]
    [IsCofiltered I] [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) {i : I} (X₀ : Over (D.obj i)) {w : X ⟶ X₀.left}
    (hsq : IsPullback f w (c.π.app i) X₀.hom) (hX₀ : FinitePresentation X₀.hom)
    (V₀ : (D.obj i).Opens) (hV₀ : IsCompact (V₀ : Set (D.obj i)))
    (hflat : Flat (f ∣_ (c.π.app i ⁻¹ᵁ V₀))) :
    ∃ (j : I) (g : j ⟶ i), Flat (pullback.snd X₀.hom (D.map g) ∣_ (D.map g ⁻¹ᵁ V₀)) := by
  -- the data the flatness descent is applied to
  have _ : LocallyOfFinitePresentation X₀.hom := hX₀.1
  have _ : QuasiCompact X₀.hom := hX₀.2.1
  have _ : QuasiSeparated X₀.hom := hX₀.2.2
  have _ : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
  have _ : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated X₀.hom
  let U₀ : X₀.left.Opens := X₀.hom ⁻¹ᵁ V₀
  have hU₀c : IsCompact (U₀ : Set X₀.left) :=
    X₀.hom.isCompact_preimage hV₀
  let W₀ : Over (D.obj i) := Over.mk (U₀.ι ≫ X₀.hom)
  have _ : CompactSpace W₀.left := isCompact_iff_compactSpace.mp hU₀c
  have _ : QuasiSeparatedSpace W₀.left :=
    QuasiSeparatedSpace.of_isOpenEmbedding U₀.isOpenEmbedding
  have _ : LocallyOfFinitePresentation W₀.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (U₀.ι ≫ X₀.hom))
  have _ : CompactSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (CompactSpace (D.obj i))
  have _ : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj i))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  let t₀ : W₀ ⟶ Over.mk (𝟙 (D.obj i)) := Over.homMk W₀.hom
  have _ : LocallyOfFinitePresentation t₀.left :=
    inferInstanceAs (LocallyOfFinitePresentation (U₀.ι ≫ X₀.hom))
  have _ : Flat ((Over.pullback (c.π.app i)).map t₀).left :=
    (flat_overPullback_terminal_iff (c.π.app i) W₀).mpr
      ((flat_morphismRestrict_iff_flat_pullback_snd_of_isPullback hsq V₀ rfl).mp hflat)
  -- the flatness descends, by Stacks 04AI
  obtain ⟨j, g, hg⟩ := exists_flat_baseChange_of_limitBaseChange D c i W₀
    (Over.mk (𝟙 (D.obj i))) t₀ hc
  exact ⟨j, g, (flat_morphismRestrict_iff_flat_pullback_snd_of_isPullback
    (IsPullback.of_hasPullback X₀.hom (D.map g)).flip V₀ rfl).mpr
    ((flat_overPullback_terminal_iff (D.map g) W₀).mp hg)⟩

/-- **A finitely presented morphism, flat over a quasi-compact open, descends to a stage.** For a
cofiltered limit of schemes with affine transition morphisms, a morphism of finite presentation to
the limit which is flat over a quasi-compact open of the limit is the base change of a morphism of
finite presentation over some stage which is flat over a quasi-compact open of that stage pulling
back to the given one. -/
public theorem exists_stage_model_of_flat_over_open {I : Type u} [Category.{u} I]
    [IsCofiltered I] [EssentiallySmall.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    {X : Scheme.{u}} (f : X ⟶ c.pt) (hf : FinitePresentation f)
    (V : c.pt.Opens) (hV : IsCompact (V : Set c.pt)) (hflat : Flat (f ∣_ V)) :
    ∃ (i : I) (X₀ : Over (D.obj i)) (V₀ : (D.obj i).Opens) (w : X ⟶ X₀.left),
      FinitePresentation X₀.hom ∧ IsCompact (V₀ : Set (D.obj i)) ∧
        IsPullback f w (c.π.app i) X₀.hom ∧ c.π.app i ⁻¹ᵁ V₀ = V ∧ Flat (X₀.hom ∣_ V₀) := by
  classical
  -- the open descends, by Stacks 01Z4
  obtain ⟨i₁, V₁, hV₁c, hV₁⟩ := exists_preimage_eq D c hc V hV
  -- the morphism descends, by Stacks 01ZM
  obtain ⟨i₂, X₂, hX₂, ⟨e₂⟩⟩ :=
    LimitFPObjectDescent.exists_model_of_finitePresentation D c hc (Over.mk f) hf
  have he₂ : ((Over.forget c.pt).mapIso e₂).hom ≫ pullback.snd X₂.hom (c.π.app i₂) = f :=
    Over.w e₂.hom
  have hX₂sq : IsPullback f
      (((Over.forget c.pt).mapIso e₂).hom ≫ pullback.fst X₂.hom (c.π.app i₂))
      (c.π.app i₂) X₂.hom :=
    (IsPullback.of_iso_pullback (CommSq.mk (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, he₂]))
      ((Over.forget c.pt).mapIso e₂) rfl he₂).flip
  -- merge the two stages
  let i₃ := IsCofiltered.min i₁ i₂
  let a : i₃ ⟶ i₁ := IsCofiltered.minToLeft i₁ i₂
  let b : i₃ ⟶ i₂ := IsCofiltered.minToRight i₁ i₂
  let V₃ : (D.obj i₃).Opens := D.map a ⁻¹ᵁ V₁
  have hV₃c : IsCompact (V₃ : Set (D.obj i₃)) :=
    (D.map a).isCompact_preimage hV₁c
  have hV₃ : c.π.app i₃ ⁻¹ᵁ V₃ = V := by
    change c.π.app i₃ ⁻¹ᵁ (D.map a ⁻¹ᵁ V₁) = V
    rw [← Scheme.Hom.comp_preimage, c.w a, hV₁]
  obtain ⟨w₃, hX₃sq⟩ := exists_isPullback_pullback_snd_of_stage D c f b X₂ hX₂sq
  let X₃ : Over (D.obj i₃) := Over.mk (pullback.snd X₂.hom (D.map b))
  have hX₃ : FinitePresentation X₃.hom :=
    LimitFPObjectDescent.finitePresentation_overPullback (D.map b) X₂ hX₂
  obtain ⟨i₄, g, hg⟩ := exists_flat_morphismRestrict_pullback_snd_of_stage D c hc f X₃ hX₃sq hX₃
    V₃ hV₃c (by rwa [hV₃])
  -- transport everything to that stage
  obtain ⟨w₄, hX₄sq⟩ := exists_isPullback_pullback_snd_of_stage D c f g X₃ hX₃sq
  refine ⟨i₄, Over.mk (pullback.snd X₃.hom (D.map g)), D.map g ⁻¹ᵁ V₃, w₄,
    LimitFPObjectDescent.finitePresentation_overPullback (D.map g) X₃ hX₃,
    (D.map g).isCompact_preimage hV₃c, hX₄sq, ?_, hg⟩
  rw [← Scheme.Hom.comp_preimage, c.w g, hV₃]

/-- **A finitely presented morphism to a quasi-compact quasi-separated scheme, flat over a
quasi-compact open, descends to a Noetherian stage.** This is the reduction of Stacks 0EVC to its
Noetherian case: the data is the base change of the same data over a Noetherian scheme. -/
public theorem exists_noetherian_model_of_flat_over_open {X Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (f : X ⟶ Y) (hf : FinitePresentation f) (V : Y.Opens)
    (hV : IsCompact (V : Set Y)) (hflat : Flat (f ∣_ V)) :
    ∃ (Y₀ X₀ : Scheme.{u}) (f₀ : X₀ ⟶ Y₀) (u : Y ⟶ Y₀) (w : X ⟶ X₀) (V₀ : Y₀.Opens),
      IsNoetherian Y₀ ∧ FinitePresentation f₀ ∧ IsCompact (V₀ : Set Y₀) ∧
        IsPullback f w u f₀ ∧ u ⁻¹ᵁ V₀ = V ∧ Flat (f₀ ∣_ V₀) := by
  let Q := LimitFPObjectDescent.finiteTypeSchemeApproximation Y
  let _ : Preorder Q.indexType := Q.indexPreorder
  have _ : Nonempty Q.indexType := Q.indexNonempty
  have _ : IsDirected Q.indexType (· ≤ ·) := Q.indexDirected
  let D := Q.stages
  let c : Cone D := Cone.mk Y Q.projection
  have _ : ∀ {i j : Q.indexTypeᵒᵖ} (v : i ⟶ j), IsAffineHom (D.map v) := Q.transition_affine
  have _ : ∀ i : Q.indexTypeᵒᵖ, LocallyOfFiniteType (terminal.from (D.obj i)) :=
    Q.stage_locallyOfFiniteType
  have _ : ∀ i : Q.indexTypeᵒᵖ, QuasiCompact (terminal.from (D.obj i)) := Q.stage_quasiCompact
  have hnoeth (i : Q.indexTypeᵒᵖ) : IsNoetherian (D.obj i) :=
    isNoetherian_of_locallyOfFiniteType_terminalFrom (D.obj i)
      (Q.stage_locallyOfFiniteType i) (Q.stage_quasiCompact i)
  have _ : ∀ i : Q.indexTypeᵒᵖ, CompactSpace (D.obj i) := fun i => (hnoeth i).toCompactSpace
  have _ : ∀ i : Q.indexTypeᵒᵖ, QuasiSeparatedSpace (D.obj i) := fun i => inferInstance
  obtain ⟨i, X₀, V₀, w, hX₀, hV₀, hsq, hV₀pre, hflat₀⟩ :=
    exists_stage_model_of_flat_over_open D c Q.limit f hf V hV hflat
  exact ⟨D.obj i, X₀.left, X₀.hom, c.π.app i, w, V₀, hnoeth i, hX₀, hV₀, hsq, hV₀pre, hflat₀⟩

end AlgebraicGeometry

end
