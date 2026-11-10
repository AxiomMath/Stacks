module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Limits.OverPullbackId
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtalePairBare

/-!
# Models of a flat sectioned morphism over a stage of a cofiltered limit

Let `S = lim Sᵢ` be a cofiltered limit of affine schemes with affine transition morphisms, and
let `f : X ⟶ S` be flat and of finite presentation with a specified section `s`. Then the whole
package descends to one of the stages: there is an index `k`, a flat morphism `f₀ : X₀ ⟶ Sₖ` of
finite presentation with a section `s₀`, and a cartesian square presenting `f` as the base
change of `f₀` along `S ⟶ Sₖ` and `s` as the base change of `s₀`.

## Main results

* `AlgebraicGeometry.ConnectedAlongSection.exists_flat_section_model_of_isLimit`: the descent of
  the flat sectioned morphism to a stage.

## Implementation notes

The morphism and its section are descended by Stacks Tag 01ZM, parts (1) and (2), in the form in
which the library has them, namely for an essentially small index category and in the
`CategoryTheory.Over.pullback` idiom; flatness is then descended by Stacks Tag 04AI, which costs
one further change of stage. That change of stage is performed in the language of cartesian
squares rather than of `CategoryTheory.Over`, by factoring the cartesian square over `Sⱼ`
through the cartesian square of the transition morphism `Sₖ ⟶ Sⱼ`.

Everything up to the flatness step repeats the construction of the private
`AlgebraicGeometry.ConnectedAlongSection.exists_noetherian_section_model` of the module
`LocallyConstructibleLocus` in this directory (`MoreMorphisms/ConnectedComponentSection`), which
is not exported; it is reproduced here for an arbitrary diagram of affine schemes, and with the
conclusion stated as a cartesian square.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace AlgebraicGeometry

namespace ConnectedAlongSection

noncomputable section

section Diagram

/-- Two morphisms in `Over S` out of the terminal object `Over.mk (𝟙 S)` into an object whose
structure morphism is an isomorphism agree on underlying morphisms. -/
theorem left_eq_of_isIso_hom {C : Type*} [Category C] {S : C} {Y : Over S} [IsIso Y.hom]
    (a b : Over.mk (𝟙 S) ⟶ Y) : a.left = b.left :=
  (cancel_mono Y.hom).mp ((Over.w a).trans (Over.w b).symm)

/-- The base change of an isomorphism in `Over T` has an isomorphism as structure morphism. -/
theorem isIso_overPullback_obj_hom {C : Type*} [Category C] [HasPullbacks C] {S T : C}
    (g : S ⟶ T) (Y : Over T) [IsIso Y.hom] : IsIso ((Over.pullback g).obj Y).hom :=
  inferInstanceAs (IsIso (pullback.snd Y.hom g))

private alias finitePresentation_pullback_snd := AlgebraicGeometry.finitePresentation_pullback_snd

/-- An isomorphism `Over.mk f ≅ (Over.pullback g).obj Y` presents `f` as the base change of
`Y.hom` along `g`. -/
theorem isPullback_of_iso_overPullback {X S T : Scheme.{u}} {f : X ⟶ S} {g : S ⟶ T}
    {Y : Over T} (e : Over.mk f ≅ (Over.pullback g).obj Y) :
    IsPullback (e.hom.left ≫ pullback.fst Y.hom g) f Y.hom g := by
  refine (IsPullback.of_hasPullback Y.hom g).of_iso ((Over.forget S).mapIso e).symm
    (Iso.refl Y.left) (Iso.refl S) (Iso.refl T) ?_ ?_ ?_ ?_
  · simp
  · have hw : e.hom.left ≫ pullback.snd Y.hom g = f := Over.w e.hom
    calc
      pullback.snd Y.hom g = (((Over.forget S).mapIso e).inv ≫ e.hom.left) ≫
          pullback.snd Y.hom g := by simp
      _ = ((Over.forget S).mapIso e).inv ≫ f := by rw [Category.assoc, hw]
  · simp
  · simp

/-- Flatness is invariant under isomorphism. -/
private instance respectsIso_flat :
    MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- Along a morphism `F : X ⟶ Y` in `Over T` with `Y.hom` an isomorphism, the base change of `F`
along `g` is flat if and only if the base change of `X.hom` along `g` is. -/
theorem flat_overPullback_map_left_iff {S T : Scheme.{u}} (g : S ⟶ T) {X Y : Over T}
    [IsIso Y.hom] (F : X ⟶ Y) :
    Flat ((Over.pullback g).map F).left ↔ Flat (pullback.snd X.hom g) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso (@Flat) _ (pullback.snd Y.hom g),
    overPullback_map_left_snd g F]

variable {I : Type v} [Category.{w} I] [IsCofiltered I] [EssentiallySmall.{u} I]
  (D : I ⥤ Scheme.{u}) (c : Cone D)
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)] [∀ i : I, IsAffine (D.obj i)]
  {X : Scheme.{u}}

/-- A sectioned morphism of finite presentation over the limit is the base change of a sectioned
morphism of finite presentation over one of the stages, with the section downstairs inducing the
given one. This is Stacks Tag 01ZM, parts (1) and (2). -/
private theorem exists_section_model (hc : IsLimit c) (f : X ⟶ c.pt) (s : c.pt ⟶ X)
    (hsec : s ≫ f = 𝟙 c.pt) (hf : FinitePresentation f) :
    ∃ (j : I) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ D.obj j) (s₀ : D.obj j ⟶ X₀) (g' : X ⟶ X₀),
      FinitePresentation f₀ ∧ s₀ ≫ f₀ = 𝟙 (D.obj j) ∧
        IsPullback g' f f₀ (c.π.app j) ∧ s ≫ g' = c.π.app j ≫ s₀ := by
  obtain ⟨i, Xi, hXi, eX⟩ :=
    LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall D c hc (Over.mk f) hf
  let Bi : Over (D.obj i) := Over.mk (𝟙 (D.obj i))
  have hBi : FinitePresentation Bi.hom := by
    change FinitePresentation (𝟙 (D.obj i))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  let uIso : (Over.pullback (c.π.app i)).obj Bi ≅ Over.mk (𝟙 c.pt) :=
    overPullbackIdIso (c.π.app i)
  let XLim := (Over.pullback (c.π.app i)).obj Xi
  have hXcomm : eX.some.hom.left ≫ XLim.hom = f := Over.w eX.some.hom
  have hsLim : (s ≫ eX.some.hom.left) ≫ XLim.hom = 𝟙 c.pt := by
    rw [Category.assoc, hXcomm, hsec]
  let sLim : Over.mk (𝟙 c.pt) ⟶ XLim := Over.homMk (s ≫ eX.some.hom.left) hsLim
  obtain ⟨j, eij, gj, α, β, hα, hβ, hgj⟩ :=
    exists_morphism_after_baseChange D c hc i Bi Xi hBi hXi (uIso.hom ≫ sLim)
  let Xj := (Over.pullback (D.map eij)).obj Xi
  let Bj := (Over.pullback (D.map eij)).obj Bi
  let uIsoj : Bj ≅ Over.mk (𝟙 (D.obj j)) := overPullbackIdIso (D.map eij)
  let sj : Over.mk (𝟙 (D.obj j)) ⟶ Xj := uIsoj.inv ≫ gj
  let e : Over.mk f ≅ (Over.pullback (c.π.app j)).obj Xj := eX.some ≪≫ β.symm
  have hcompat : s ≫ e.hom.left = (overPullbackIdIso (c.π.app j)).inv.left ≫
      ((Over.pullback (c.π.app j)).map sj).left := by
    have h3 : sLim ≫ β.inv = uIso.inv ≫ α.inv ≫ (Over.pullback (c.π.app j)).map gj := by
      rw [← cancel_epi (α.hom ≫ uIso.hom), Category.assoc, reassoc_of% hgj]
      simp
    have : IsIso Bi.hom := inferInstanceAs (IsIso (𝟙 _))
    have := isIso_overPullback_obj_hom (D.map eij) Bi
    have := isIso_overPullback_obj_hom (c.π.app j) Bj
    have hsource : (uIso.inv ≫ α.inv).left =
        ((overPullbackIdIso (c.π.app j)).inv ≫
          (Over.pullback (c.π.app j)).map uIsoj.inv).left :=
      left_eq_of_isIso_hom _ _
    calc
      s ≫ e.hom.left =
          (uIso.inv ≫ α.inv).left ≫ ((Over.pullback (c.π.app j)).map gj).left := by
        simpa [sLim, e] using congrArg Over.Hom.left h3
      _ = (overPullbackIdIso (c.π.app j)).inv.left ≫
            ((Over.pullback (c.π.app j)).map sj).left := by
        rw [hsource]
        have hmap : (Over.pullback (c.π.app j)).map uIsoj.inv ≫
            (Over.pullback (c.π.app j)).map gj = (Over.pullback (c.π.app j)).map sj := by
          simp [sj]
        simpa only [Over.comp_left, Category.assoc] using
          congrArg (fun k => (overPullbackIdIso (c.π.app j)).inv.left ≫ k.left) hmap
  refine ⟨j, Xj.left, Xj.hom, sj.left, e.hom.left ≫ pullback.fst Xj.hom (c.π.app j),
    finitePresentation_pullback_snd _ _ hXi, Over.w sj, isPullback_of_iso_overPullback e, ?_⟩
  rw [← Category.assoc, hcompat, Category.assoc, overPullback_map_left_fst (c.π.app j) sj,
    ← Category.assoc]
  exact overPullbackIdIso_inv_left_comp_fst (c.π.app j) =≫ sj.left

/-- **The descent of a flat sectioned morphism to a stage.** Let `S` be the limit of a cofiltered
diagram of affine schemes with affine transition morphisms. A flat sectioned morphism of finite
presentation over `S` is the base change of a flat sectioned morphism of finite presentation over
one of the stages. -/
theorem exists_flat_section_model_of_isLimit (hc : IsLimit c) (f : X ⟶ c.pt) (s : c.pt ⟶ X)
    (hsec : s ≫ f = 𝟙 c.pt) (hf : FinitePresentation f) (hflat : Flat f) :
    ∃ (k : I) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ D.obj k) (s₀ : D.obj k ⟶ X₀) (g' : X ⟶ X₀),
      FinitePresentation f₀ ∧ Flat f₀ ∧ s₀ ≫ f₀ = 𝟙 (D.obj k) ∧
        IsPullback g' f f₀ (c.π.app k) ∧ s ≫ g' = c.π.app k ≫ s₀ := by
  obtain ⟨j, X₁, f₁, s₁, g₁, hf₁, hs₁, hpb₁, hsc₁⟩ := exists_section_model D c hc f s hsec hf
  have : LocallyOfFinitePresentation f₁ := hf₁.1
  have : QuasiCompact f₁ := hf₁.2.1
  have : QuasiSeparated f₁ := hf₁.2.2
  let F₁ : Over.mk f₁ ⟶ Over.mk (𝟙 (D.obj j)) := Over.homMk f₁
  -- The hypotheses of Tag 04AI, in the shape its instance arguments are synthesized in.
  have : CompactSpace (Over.mk f₁).left := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace (Over.mk f₁).left := quasiSeparatedSpace_of_quasiSeparated f₁
  have : CompactSpace (Over.mk (𝟙 (D.obj j))).left := inferInstanceAs (CompactSpace (D.obj j))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.obj j))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj j))
  have : LocallyOfFinitePresentation F₁.left := hf₁.1
  -- Flatness of the base change of `f₁` to the limit, as Tag 04AI consumes it.
  have hb : Flat (pullback.snd (Over.mk f₁).hom (c.π.app j)) :=
    (MorphismProperty.arrow_mk_iso_iff (@Flat)
      (Arrow.isoMk hpb₁.isoPullback (Iso.refl c.pt) (by simp))).mp hflat
  have : IsIso (Over.mk (𝟙 (D.obj j))).hom := inferInstanceAs (IsIso (𝟙 _))
  have : Flat ((Over.pullback (c.π.app j)).map F₁).left :=
    (flat_overPullback_map_left_iff (c.π.app j) F₁).mpr hb
  obtain ⟨k, ekj, hFk⟩ := exists_flat_baseChange_of_limitBaseChange D c j
    (Over.mk f₁) (Over.mk (𝟙 (D.obj j))) F₁ hc
  -- The model over the later stage `k`.
  have hu : c.π.app k ≫ D.map ekj = c.π.app j := c.w ekj
  have hR := IsPullback.of_hasPullback f₁ (D.map ekj)
  have hcomp : IsPullback g₁ f f₁ (c.π.app k ≫ D.map ekj) := hu ▸ hpb₁
  have hL : IsPullback (hR.lift g₁ (f ≫ c.π.app k)
      (hcomp.w.trans (Category.assoc _ _ _).symm)) f (pullback.snd f₁ (D.map ekj))
      (c.π.app k) := hcomp.of_right' hR
  have hcond : (D.map ekj ≫ s₁) ≫ f₁ = 𝟙 (D.obj k) ≫ D.map ekj := by
    rw [Category.assoc, hs₁, Category.comp_id, Category.id_comp]
  refine ⟨k, pullback f₁ (D.map ekj), pullback.snd f₁ (D.map ekj),
    pullback.lift (D.map ekj ≫ s₁) (𝟙 _) hcond, _, finitePresentation_pullback_snd _ _ hf₁,
    (flat_overPullback_map_left_iff (D.map ekj) F₁).mp hFk, pullback.lift_snd _ _ _, hL, ?_⟩
  refine pullback.hom_ext ?_ ?_
  · rwa [Category.assoc, hR.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hu]
  · rw [Category.assoc, hR.lift_snd, Category.assoc, pullback.lift_snd, Category.comp_id,
      ← Category.assoc, hsec, Category.id_comp]

end Diagram

end

end ConnectedAlongSection

end AlgebraicGeometry

end
