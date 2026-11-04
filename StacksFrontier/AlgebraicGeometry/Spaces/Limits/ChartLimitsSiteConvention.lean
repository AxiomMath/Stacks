module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitContainment

/-!
# Contained chart limits give the chapter's standing convention

`AlgebraicGeometry.Space.HasContainedChartLimits` asks of an inverse system of presheaves on the
big fppf site that, over every stage and every scheme-valued point of it, the diagram of affine
fibre products has a limit inside the site. `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`
is the chapter's convention of Section 70.2 (tag 07SD) read for the same system: every limit of
the base changes, over a fixed stage, of the later stages to an affine object of the site is in
the site. The first gives the second, which is what the descent results of Chapter 70 are stated
under.

## Main results

* `AlgebraicGeometry.Space.HasContainedChartLimits.siteContainsBaseChangeLimits`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Contained chart limits give the convention of tag 07SD.** If over every stage and every
scheme-valued point of a cofiltered inverse system the diagram of affine fibre products has a
limit inside the site, then every limit of the base changes, over a stage, of the later stages to
an affine object of the site is in the site. -/
theorem HasContainedChartLimits.siteContainsBaseChangeLimits {I : Type u} [Category.{u} I]
    [IsCofiltered I] {D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : HasContainedChartLimits B S hS D) : SiteContainsBaseChangeLimits B S hS D := by
  intro i Z g W e c hc
  let P := Over.post (X := i) D ⋙ Over.pullback g
  let fstNat : P ⋙ Over.forget _ ⟶ Over.forget i ⋙ D :=
    { app := fun k => pullback.fst (D.map k.hom) g
      naturality := fun {k l} f => by
        simp only [P, Over.pullback, Over.post, Functor.comp_map]
        exact pullback.lift_fst _ _ _ }
  let π : (W ⋙ BigAffineFppf.inclusion B S hS) ⋙ yoneda ⟶ Over.forget i ⋙ D :=
    e.hom ≫ fstNat
  let b : (W ⋙ BigAffineFppf.inclusion B S hS) ⋙ yoneda ⟶ (Functor.const (Over i)).obj
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)) :=
    e.hom ≫ Functor.whiskerLeft P (Over.forgetCocone _).ι
  have hpb : ∀ k : Over i, IsPullback (π.app k) (b.app k) (D.map k.hom) g := fun k =>
    IsPullback.of_iso_pullback
      ⟨(Category.assoc _ _ _).trans ((congrArg (e.hom.app k ≫ ·)
        (pullback.condition (f := D.map k.hom) (g := g))).trans (Category.assoc _ _ _).symm)⟩
      (e.app k) rfl rfl
  obtain ⟨c', ⟨hc'⟩, hcont⟩ := h i ((BigAffineFppf.inclusion B S hS).obj Z) g
    (W ⋙ BigAffineFppf.inclusion B S hS) π b
    (fun k => (W.obj k).property) hpb
  show c.pt.size < B.cutoff
  rwa [show c.pt.size = c'.pt.size from Scheme.size_congr (hc.conePointUniqueUpToIso hc')]

end AlgebraicGeometry.Space

end
