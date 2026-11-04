module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartLimitsInSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescent

/-!
# Stacks 07SK, essential surjectivity, from limit bridges of all chart systems

If every chart system of every stage of a cofiltered inverse system of quasi-compact,
quasi-separated algebraic spaces with affine transition morphisms has a limit bridge (a limit in
the big fppf site which is also the limit of the underlying affine schemes), the system satisfies
the chapter's convention of Section 70.2
(`AlgebraicGeometry.Space.siteContainsBaseChangeLimits_iff`), so Stacks 07SK holds for it
(`AlgebraicGeometry.Space.exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits`).

## Main results

* `AlgebraicGeometry.Space.exists_model_of_finitePresentation_of_limitBridges`.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))
  {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 07SK, essential surjectivity, from limit bridges.** For a cofiltered inverse system
of quasi-compact, quasi-separated algebraic spaces with affine transition morphisms and algebraic
limit, every chart system of which has a limit bridge, every algebraic space of finite
presentation over the limit is the base change of one of finite presentation over a stage. -/
theorem exists_model_of_finitePresentation_of_limitBridges
    (hlim : IsAlgebraicSpace B S hS (limit D))
    (hbr : ∀ (i₀ : I) (U₀ : BigAffineFppf B S hS)
      (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)
      (C : AffineChartSystem B S hS i₀ D U₀ f₀), Nonempty C.LimitBridge)
    (_hπ : ∀ i, IsAffineHom B S hS (limit.π D i))
    (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hQc : ∀ i, IsQuasiCompactSpace B S hS (D.obj i))
    (hQs : ∀ i, IsAbsolutelyQuasiSeparated B S hS hZ (D.obj i))
    (Y : Over (limit D)) (hY : IsAlgebraicSpace B S hS Y.left)
    (hFp : IsFinitePresentation B S hS Y.hom) :
    ∃ (i : I) (Yᵢ : Over (D.obj i)),
      IsAlgebraicSpace B S hS Yᵢ.left ∧ IsFinitePresentation B S hS Yᵢ.hom ∧
        Nonempty (Y ≅ (Over.pullback (limit.π D i)).obj Yᵢ) :=
  exists_model_of_finitePresentation_of_siteContainsBaseChangeLimits (B := B) (S := S)
    (hS := hS) (hZ := hZ) (D := D) (hD := hD) (hAffine := hAffine) (hQc := hQc) (hQs := hQs)
    (hconv := (siteContainsBaseChangeLimits_iff D).2 fun i₀ U₀ f₀ C =>
      (hbr i₀ U₀ f₀ C).some.exists_cone)
    (hDlim := hlim) Y hY hFp

end AlgebraicGeometry.Space

end
