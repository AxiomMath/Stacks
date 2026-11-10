module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCriteria

/-!
# The equalizer of two morphisms of formal algebraic spaces over a scheme-valued point

Let `x₁, x₂ : F ⟶ W` be morphisms of fppf sheaves of `Type (u + 1)` on the big fppf site of `S`
whose equalizer `E ⟶ F` is a closed immersion (Stacks 0ANP). Over every scheme-valued point
`ξ : Q ⟶ F` the equalizer is represented by a closed subscheme `R ⟶ Q`: a morphism `t : T ⟶ Q`
of the site factors through `R` exactly when `x₁ ∘ ξ ∘ t = x₂ ∘ ξ ∘ t`.

This is the form in which the equalizer `E_W` of the two formal components of a pair of triples
enters the injectivity half of the proof of Stacks 0GI5: over the thickenings `Spec (A / Iⁿ)` of a
stage it becomes a closed subscheme, cut out by an ideal.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isClosedImmersion_represents_equalizer`.
* `AlgebraicGeometry.FormalSpace.exists_comp_eq_iff_ker_le`: factoring through a closed subscheme
  of an affine object of the site is killing the kernel on global sections.

## References

* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The equalizer of two morphisms into a sheaf, when a closed immersion, is represented over
every scheme-valued point by a closed subscheme.** -/
theorem exists_isClosedImmersion_represents_equalizer {F W : FppfSheaf B S hS} (x₁ x₂ : F ⟶ W)
    (hE : IsClosedImmersion B S hS (equalizer.ι x₁ x₂)) (Q : BigFppfOver B S hS)
    (ξ : (uliftYoneda.{u + 1}).obj Q ⟶ F.obj) :
    ∃ (R : BigFppfOver B S hS) (r : R ⟶ Q),
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map r) ∧
      ∀ (T : BigFppfOver B S hS) (t : T ⟶ Q), (∃ s : T ⟶ R, s ≫ r = t) ↔
        (uliftYoneda.{u + 1}).map t ≫ ξ ≫ x₁.hom = (uliftYoneda.{u + 1}).map t ≫ ξ ≫ x₂.hom := by
  obtain ⟨hrep, hP⟩ := hE
  have h := hP Q ξ
  let rep := h.rep
  let R := rep.pullback (𝟙 ((uliftYoneda.{u + 1}).obj Q))
  let r := rep.snd (𝟙 ((uliftYoneda.{u + 1}).obj Q))
  have hsq := rep.isPullback (𝟙 ((uliftYoneda.{u + 1}).obj Q))
  refine ⟨R, r, h.property_snd (𝟙 _), fun T t => ⟨?_, ?_⟩⟩
  · rintro ⟨s, rfl⟩
    have hw : rep.fst (𝟙 _) ≫ pullback.fst ξ (equalizer.ι x₁ x₂).hom =
        (uliftYoneda.{u + 1}).map r := by simpa using hsq.w
    have hc : (equalizer.ι x₁ x₂).hom ≫ x₁.hom = (equalizer.ι x₁ x₂).hom ≫ x₂.hom :=
      congrArg (fun k => k.hom) (equalizer.condition x₁ x₂)
    have key : (uliftYoneda.{u + 1}).map r ≫ ξ = rep.fst (𝟙 _) ≫
        pullback.snd ξ (equalizer.ι x₁ x₂).hom ≫ (equalizer.ι x₁ x₂).hom := by
      rw [← hw, Category.assoc, pullback.condition]
    rw [Functor.map_comp, Category.assoc, Category.assoc, ← Category.assoc _ ξ, key,
      ← Category.assoc _ ξ, key]
    simp only [Category.assoc, hc]
  · intro heq
    let φ : yonedaSheaf B S hS T ⟶ F := ObjectProperty.homMk ((uliftYoneda.{u + 1}).map t ≫ ξ)
    let e := equalizer.lift φ (ObjectProperty.hom_ext _ (by
      change ((uliftYoneda.{u + 1}).map t ≫ ξ) ≫ x₁.hom = ((uliftYoneda.{u + 1}).map t ≫ ξ) ≫ x₂.hom
      simpa only [Category.assoc] using heq))
    have he : e.hom ≫ (equalizer.ι x₁ x₂).hom = (uliftYoneda.{u + 1}).map t ≫ ξ :=
      congrArg (fun k => k.hom) (equalizer.lift_ι φ _)
    let k := pullback.lift ((uliftYoneda.{u + 1}).map t) e.hom he.symm
    let m := hsq.lift k ((uliftYoneda.{u + 1}).map t) (by
      rw [Category.comp_id]
      exact pullback.lift_fst _ _ _)
    have hm : m ≫ (uliftYoneda.{u + 1}).map r = (uliftYoneda.{u + 1}).map t := hsq.lift_snd _ _ _
    refine ⟨(uliftYoneda.{u + 1}).preimage m, (uliftYoneda.{u + 1}).map_injective ?_⟩
    rw [Functor.map_comp, Functor.map_preimage, hm]

/-- **Factoring through a closed subscheme of an affine object of the site.** For a closed
immersion `r : R ⟶ Q` of objects of the big fppf site with `Q` affine, a morphism `t : T ⟶ Q`
factors through `r` exactly when it kills the kernel of `Γ(Q) ⟶ Γ(R)` on global sections. -/
theorem exists_comp_eq_iff_ker_le {Q R T : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q)] (r : R ⟶ Q)
    [AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map r)] (t : T ⟶ Q) :
    (∃ s : T ⟶ R, s ≫ r = t) ↔
      RingHom.ker ((BigFppfOver.toScheme B S hS).map r).appTop.hom ≤
        RingHom.ker ((BigFppfOver.toScheme B S hS).map t).appTop.hom := by
  constructor
  · rintro ⟨s, rfl⟩ a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ha,
      map_zero]
  · intro hJ
    have H : ((BigFppfOver.toScheme B S hS).map r).ker ≤
        ((BigFppfOver.toScheme B S hS).map t).ker := by
      rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
      refine Scheme.IdealSheafData.le_of_isAffine ?_
      simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
      exact Ideal.map_mono hJ
    let s₀ := IsClosedImmersion.lift ((BigFppfOver.toScheme B S hS).map r)
      ((BigFppfOver.toScheme B S hS).map t) H
    have hs₀ : s₀ ≫ (BigFppfOver.toScheme B S hS).map r = (BigFppfOver.toScheme B S hS).map t :=
      IsClosedImmersion.lift_fac _ _ _
    let s : T ⟶ R := Over.homMk (ObjectProperty.homMk s₀) (by
      apply ObjectProperty.hom_ext
      have hr := congrArg (fun k => k.hom) (Over.w r)
      have ht := congrArg (fun k => k.hom) (Over.w t)
      simp only [ObjectProperty.FullSubcategory.comp_hom] at hr ht ⊢
      change s₀ ≫ R.hom.hom = T.hom.hom
      rw [← hr, ← Category.assoc]
      change (s₀ ≫ (BigFppfOver.toScheme B S hS).map r) ≫ Q.hom.hom = T.hom.hom
      rw [hs₀]
      exact ht)
    exact ⟨s, (BigFppfOver.toScheme B S hS).map_injective ((Functor.map_comp _ _ _).trans hs₀)⟩

end AlgebraicGeometry.FormalSpace

end
