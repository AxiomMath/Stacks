module

public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyProperOverLimit
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic

/-!
# Spreading out a scheme over the local ring at a point

In the proof of [Stacks, Tag 0EA3] a resolution `W ⟶ Spec(𝒪_{X, x})` is spread out to a proper
morphism `b : X' ⟶ U` over an affine open neighbourhood `U` of `x` with
`X' ×_U Spec(𝒪_{X, x}) = W`. This file proves the first step: `Spec(𝒪_{X, x})` is the limit of
the affine open neighbourhoods of `x` ([Stacks, Tag 01Z2] in the form of
`AlgebraicGeometry.isLimitSpecStalkCone`), so a scheme of finite presentation over it is the base
change of one over some affine open neighbourhood ([Stacks, Tag 01ZM]).

## Main results

* `AlgebraicGeometry.exists_isPullback_specStalk_of_finitePresentation`
* `AlgebraicGeometry.exists_isProper_model_specStalk`: a proper `g` has a proper model
  ([Stacks, Tag 081F]).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Spreading out over the local ring at a point ([Stacks, Tag 01ZM]).** Every morphism
`g : W ⟶ Spec(𝒪_{X, x})` of finite presentation is the base change, along
`Spec(𝒪_{X, x}) ⟶ U`, of a morphism of finite presentation `b : X' ⟶ U` for some affine open
neighbourhood `U` of `x`. -/
theorem exists_isPullback_specStalk_of_finitePresentation (X : Scheme.{u}) (x : X)
    {W : Scheme.{u}} (g : W ⟶ Spec (X.presheaf.stalk x)) (hg : FinitePresentation g) :
    ∃ (i : AffineOpenNhds X x) (X' : Scheme.{u}) (b : X' ⟶ (affineOpenNhdsDiagram X x).obj i)
      (w : W ⟶ X'), FinitePresentation b ∧ IsPullback w g b ((specStalkCone X x).π.app i) := by
  obtain ⟨i, Xi, hfp, ⟨e⟩⟩ := LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall
    (affineOpenNhdsDiagram X x) (specStalkCone X x) (isLimitSpecStalkCone X x) (Over.mk g) hg
  refine ⟨i, Xi.left, Xi.hom, e.hom.left ≫ pullback.fst _ _, hfp, ?_⟩
  refine IsPullback.of_iso (IsPullback.of_hasPullback Xi.hom ((specStalkCone X x).π.app i))
    ((Over.forget _).mapIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change _ = e.inv.left ≫ e.hom.left ≫ _
    rw [← Category.assoc, ← Over.comp_left, e.inv_hom_id]
    exact (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Over.w e.inv).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Shrinking the neighbourhood of a model: base changing a model over `U_i` along `U_j ⊆ U_i`
gives a model over `U_j`. -/
noncomputable def specStalkModelShrinkIso (X : Scheme.{u}) (x : X) {i j : AffineOpenNhds X x}
    (f : j ⟶ i) {T : Over (Spec (X.presheaf.stalk x))}
    {Y : Over ((affineOpenNhdsDiagram X x).obj i)}
    (e : T ≅ (Over.pullback ((specStalkCone X x).π.app i)).obj Y) :
    T ≅ (Over.pullback ((specStalkCone X x).π.app j)).obj
      ((Over.pullback ((affineOpenNhdsDiagram X x).map f)).obj Y) :=
  e ≪≫ eqToIso (congrArg (fun h ↦ (Over.pullback h).obj Y) ((specStalkCone X x).w f).symm) ≪≫
    (Over.pullbackComp ((specStalkCone X x).π.app j) ((affineOpenNhdsDiagram X x).map f)).app Y

/-- Finite presentation is stable under base change, in the `Over.pullback` idiom. -/
theorem finitePresentation_overPullback_obj {S T : Scheme.{u}} (h : T ⟶ S) (Y : Over S)
    (hY : FinitePresentation Y.hom) : FinitePresentation ((Over.pullback h).obj Y).hom := by
  have := hY.1
  have := hY.2.1
  have := hY.2.2
  exact ⟨inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Y.hom h)),
    inferInstanceAs (QuasiCompact (pullback.snd Y.hom h)),
    inferInstanceAs (QuasiSeparated (pullback.snd Y.hom h))⟩

/-- **A proper model ([Stacks, Tags 01ZM and 081F]).** A proper morphism of finite
presentation `g : W ⟶ Spec(𝒪_{X, x})` is the base change, along `Spec(𝒪_{X, x}) ⟶ U`, of a
proper morphism of finite presentation over some affine open neighbourhood `U` of `x`. -/
theorem exists_isProper_model_specStalk (X : Scheme.{u}) (x : X) {W : Scheme.{u}}
    (g : W ⟶ Spec (X.presheaf.stalk x)) [IsProper g] (hg : FinitePresentation g) :
    ∃ (j : AffineOpenNhds X x) (Z : Over ((affineOpenNhdsDiagram X x).obj j)),
      FinitePresentation Z.hom ∧ IsProper Z.hom ∧
        Nonempty (Over.mk g ≅ (Over.pullback ((specStalkCone X x).π.app j)).obj Z) := by
  have hc := isLimitSpecStalkCone X x
  obtain ⟨i, Y, hfp, ⟨e⟩⟩ := LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall
    (affineOpenNhdsDiagram X x) (specStalkCone X x) hc (Over.mk g) hg
  have := hfp.2.1
  have := hfp.2.2
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : IsSeparated ((Over.pullback ((specStalkCone X x).π.app i)).obj Y).hom := by
    rw [← Over.w e.inv]
    exact inferInstanceAs (IsSeparated (e.inv.left ≫ g))
  obtain ⟨j, f, hsep⟩ := exists_isSeparated_overPullbackObj_of_isLimit
    (affineOpenNhdsDiagram X x) (specStalkCone X x) hc i Y
  let Y' := (Over.pullback ((affineOpenNhdsDiagram X x).map f)).obj Y
  let e' := specStalkModelShrinkIso X x f e
  have hfp' : FinitePresentation Y'.hom := finitePresentation_overPullback_obj _ Y hfp
  have : IsSeparated Y'.hom := hsep
  have : IsProper ((Over.pullback ((specStalkCone X x).π.app j)).obj Y').hom := by
    have : IsIso e'.inv.left := inferInstanceAs (IsIso ((Over.forget _).mapIso e').inv)
    rw [← Over.w e'.inv]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsProper e'.inv.left g).mpr ‹_›
  obtain ⟨k, f', hprop⟩ := exists_isProper_overPullbackObj_of_isLimit
    (affineOpenNhdsDiagram X x) (specStalkCone X x) hc j Y' hfp'
  exact ⟨k, _, finitePresentation_overPullback_obj _ Y' hfp', hprop,
    ⟨specStalkModelShrinkIso X x f' e'⟩⟩

end AlgebraicGeometry

end
