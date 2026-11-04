module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Comp
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmoothSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# A smooth morphism of algebraic spaces is formally smooth after an étale atlas

A smooth morphism `f : X ⟶ Y` of algebraic spaces over `S` need not be known to be formally
smooth — that is the content of step (II) of [Stacks Project, Tag 04AM], which descends formal
smoothness along a surjective étale chart.  What *is* available with no descent at all is formal
smoothness of the composite of `f` with a surjective étale atlas of its source: on a commuting
square of étale charts the induced morphism of schemes is smooth, hence formally smooth by
[Stacks Project, Tag 02H6], and the chart of the target is formally étale by
[Stacks Project, Tag 04AL].

This is the hypothesis `FormallySmooth (a ≫ b)` of
`AlgebraicGeometry.Space.exists_etale_affine_local_lift`, so this file is what makes that
étale-local lifting statement applicable to a morphism known only to be smooth.

## Main results

* `AlgebraicGeometry.Space.exists_atlas_formallySmooth_comp_of_isSmooth`: a smooth morphism of
  algebraic spaces admits a surjective étale atlas of its source whose composite with it is
  formally smooth.

## References

* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A smooth morphism of algebraic spaces becomes formally smooth after an étale atlas of its
source.** There is a surjective étale atlas `a : U ⟶ X` of the source, from a representable
presheaf, with `a ≫ f` formally smooth.

The atlas is the one of [Stacks Project, Tag 02X1] lying over a chosen atlas `b : V ⟶ Y` of the
target, so that `a ≫ f = yoneda.map ψ ≫ b` for a morphism `ψ` of the site.  Smoothness of `f`
makes the scheme morphism underlying `ψ` smooth, hence formally smooth by
[Stacks Project, Tag 02H6]; the atlas `b` is formally étale by [Stacks Project, Tag 04AL], in
particular formally smooth; and formal smoothness is stable under composition. -/
theorem exists_atlas_formallySmooth_comp_of_isSmooth
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsSmooth B S hS f) :
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X),
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      FormallySmooth (a ≫ f) := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, ψ, hdiag, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  have hψ : Smooth ((BigFppfOver.toScheme B S hS).map ψ) :=
    hf U V a b ψ haEtale hbEtale hdiag.symm
  have hψF : FormallySmooth (yoneda.map ψ) :=
    formallySmooth_yoneda_map_of_formallySmoothScheme
      (Stacks.Smooth.formallySmoothScheme_of_smooth _)
  have hbF : FormallySmooth b := fun T T' hT hT' i hi z w hzw =>
    let ⟨v, hv⟩ := formallyEtale_of_etale B S hS b hbEtale T T' hT hT' i hi z w hzw
    ⟨v, hv.1⟩
  refine ⟨U, a, haSurj, haEtale, ?_⟩
  rw [hdiag]
  exact FormallySmooth.comp _ _ hψF hbF

end AlgebraicGeometry.Space

end
