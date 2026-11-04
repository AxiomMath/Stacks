module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale

/-!
# Transporting a section through an étale chart along a square-zero thickening

Let `a : yoneda.obj U ⟶ X` be an étale representable chart of a presheaf `X` on the big fppf
site of `S`, and let `i : W₀ ⟶ W` be a square-zero closed immersion of affine objects of the
site. Two morphisms `p q : W ⟶ U` whose images `a ∘ p` and `a ∘ q` in `X` agree over `W₀` need
not agree over `W`, and need not even have the same restriction to `W₀` as morphisms into the
chart: a section of `X` has many preimages in the chart.

`AlgebraicGeometry.Space.exists_chart_hom_of_restrict_app_eq` says that one of the two can
nevertheless be rechosen to have the restriction of the other: there is a `q' : W ⟶ U` with
`i ≫ q' = i ≫ q` and `a ∘ q' = a ∘ p`.

## Main results

* `AlgebraicGeometry.Space.exists_chart_hom_of_restrict_app_eq`: the transport just described.

## Implementation notes

The proof is the universal property of `R = U ×_X U`, which is an object of the site because
`a` is representable, together with the fact that its second projection `R ⟶ U` is étale,
being a base change of `a`, hence formally étale by Tag 04AL.

The pair `(i ≫ q, i ≫ p)` is a section of `R` over `W₀`, because the two have the same image
in `X` there. Its second component is the restriction of `p`, which is defined over all of
`W`; so formal étaleness of the second projection extends the section of `R` over `W₀` to a
section `ρ` of `R` over `W`, uniquely, with second component `p` itself. The first component of
`ρ` is the morphism `q'` wanted: it restricts to `i ≫ q` because `ρ` restricts to the given
section of `R`, and its image in `X` is that of `p` because the two projections of `R` have the
same image in `X` by the defining pullback square.

Nothing here is specific to formal smoothness, and no hypothesis on `X` is needed beyond
étaleness and representability of the chart.

## References

* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A section of an étale chart can be rechosen with a prescribed restriction.** Let
`a : yoneda.obj U ⟶ X` be an étale representable chart, let `i : W₀ ⟶ W` be a square-zero
closed immersion of affine objects of the site, and let `p q : W ⟶ U` be such that the sections
`a ∘ p` and `a ∘ q` of `X` over `W` have the same restriction to `W₀`. Then some `q' : W ⟶ U`
has the restriction of `q` to `W₀` and the image of `p` in `X`.

Thus a section of `X` over `W` which comes from the chart comes from the chart by a morphism
with any prescribed restriction to `W₀` that is compatible with it. This is what lets the
comparison of two chart presentations of one section of `X` be carried out at the level of the
chart, which is a scheme, rather than at the level of `X`. -/
theorem exists_chart_hom_of_restrict_app_eq
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    (a : yoneda.obj U ⟶ X)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    {W₀ W : BigFppfOver B S hS}
    (hW₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj W₀))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    {i : W₀ ⟶ W} (hi : IsSquareZeroClosedImmersion B S hS i) (p q : W ⟶ U)
    (h : a.app (op W₀) (i ≫ p) = a.app (op W₀) (i ≫ q)) :
    ∃ q' : W ⟶ U, i ≫ q' = i ≫ q ∧ a.app (op W) q' = a.app (op W) p := by
  have key : ∀ {V : BigFppfOver B S hS} (f : V ⟶ U),
      yonedaEquiv (yoneda.map f ≫ a) = a.app (op V) f := fun f => by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  -- The hypothesis, read as an equality of morphisms of presheaves.
  have htr : yoneda.map (i ≫ q) ≫ a = yoneda.map (i ≫ p) ≫ a :=
    yonedaEquiv.injective (by rw [key, key, h])
  -- The section of `R = U ×_X U` over `W₀` carried by the two restrictions.
  set ρ₀ : W₀ ⟶ ha.rep.pullback a := ha.rep.lift' (i ≫ q) (i ≫ p) htr with hρ₀def
  have hρ₀fst : ρ₀ ≫ ha.rep.fst' a = i ≫ q := by
    rw [hρ₀def]; exact ha.rep.lift'_fst _ _ _
  have hρ₀snd : ρ₀ ≫ ha.rep.snd a = i ≫ p := by
    rw [hρ₀def]; exact ha.rep.lift'_snd _ _ _
  -- The second projection of `R` is étale, hence formally étale.
  have hsnd : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (ha.rep.snd a)) :=
    (presheaf_yoneda_map_etale_iff B S hS (ha.rep.snd a)).2 (ha.property_snd a)
  -- It extends the section of `R` over `W₀` to one over `W` whose second component is `p`.
  obtain ⟨ρ, hρ, -⟩ := formallyEtale_of_etale B S hS (yoneda.map (ha.rep.snd a)) hsnd
    W₀ W hW₀ hW i hi ρ₀ p hρ₀snd
  have hρrestrict : i ≫ ρ = ρ₀ := hρ.1
  have hρsnd : ρ ≫ ha.rep.snd a = p := hρ.2
  -- Its first component is the morphism wanted.
  refine ⟨ρ ≫ ha.rep.fst' a, ?_, ?_⟩
  · rw [← Category.assoc, hρrestrict, hρ₀fst]
  · have hw : yoneda.map (ha.rep.fst' a) ≫ a = yoneda.map (ha.rep.snd a) ≫ a :=
      (ha.rep.isPullback' a).w
    rw [← key, ← key p, Functor.map_comp, Category.assoc, hw, ← Category.assoc,
      ← Functor.map_comp, hρsnd]

end AlgebraicGeometry.Space

end
