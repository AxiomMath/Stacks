module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtaleTargetDescent

/-!
# The containment locus along an étale morphism of the base

Let `X` be an algebraic space over `S`, let `V' ⟶ V` be a morphism of the big fppf site and let
`g : X ⟶ schemeSpace V'` be a morphism of algebraic spaces. The relative assassin containment
locus `AlgebraicGeometry.Space.relativeAssassinContainmentLocus` of `g` lives in `|V'|` and that
of `g ≫ schemeSpaceMap ψ` lives in `|V|`. This file compares the two: when the scheme morphism
underlying `ψ` is étale and injective on points — an open immersion, for instance — the first is
the inverse image of the second.

## Main results

* `AlgebraicGeometry.Space.relativeAssassinContainmentLocus_comp_schemeSpaceMap`: the locus over
  `V'` is the inverse image, under the scheme morphism underlying `ψ`, of the locus over `V`.
* `AlgebraicGeometry.Space.relativeAssassinContainmentLocus_comp_schemeSpaceMap_of_isOpenImmersion`
  is its specialization to an open immersion of the site, where both hypotheses on `ψ` are
  automatic.

## References

* [Stacks Project, Tag 0CVV](https://stacks.math.columbia.edu/tag/0CVV)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 03BV](https://stacks.math.columbia.edu/tag/03BV)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The containment locus over an étale, injective morphism of the base.** For `ψ : V' ⟶ V` a
morphism of the site whose underlying scheme morphism is étale and injective on points, and for
`g : X ⟶ schemeSpace V'`, the containment locus of `g` in `|V'|` is the inverse image of the
containment locus of `g ≫ schemeSpaceMap ψ` in `|V|`. -/
theorem relativeAssassinContainmentLocus_comp_schemeSpaceMap {X : AlgebraicSpaces B S hS}
    {V' V : BigFppfOver B S hS} (ψ : V' ⟶ V) (g : X ⟶ schemeSpace V')
    (hψ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map ψ))
    (hinj : Function.Injective ((BigFppfOver.toScheme B S hS).map ψ).base)
    (F : Modules.{u, u} B S hS X.1 X.2) (U : Set (points B S hS X.1)) :
    relativeAssassinContainmentLocus B S hS V' g F U =
      ((BigFppfOver.toScheme B S hS).map ψ).base ⁻¹'
        relativeAssassinContainmentLocus B S hS V (g ≫ schemeSpaceMap ψ) F U := by
  have hψet : IsEtale B S hS (schemeSpaceMap ψ).hom :=
    (isEtale_iff_presheaf_of_yoneda B S hS _).2 ((presheaf_yoneda_map_etale_iff B S hS ψ).2 hψ)
  have hass : relativeWeaklyAssociatedPoints B S hS (g ≫ schemeSpaceMap ψ) F =
      relativeWeaklyAssociatedPoints B S hS g F :=
    relativeWeaklyAssociatedPoints_comp_eq_of_isEtale B S hS g (schemeSpaceMap ψ) hψet F
  have hpt : ∀ x : points B S hS X.1,
      schemeSpacePointToScheme B S hS V
          (pointsMap B S hS X.1 (g ≫ schemeSpaceMap ψ).hom x) =
        ((BigFppfOver.toScheme B S hS).map ψ).base
          (schemeSpacePointToScheme B S hS V' (pointsMap B S hS X.1 g.hom x)) := by
    intro x
    have hcomp : pointsMap B S hS X.1 (g ≫ schemeSpaceMap ψ).hom x =
        pointsMap B S hS (schemeSpace V').1 (schemeSpaceMap ψ).hom
          (pointsMap B S hS X.1 g.hom x) :=
      congrArg (fun k => k x)
        (pointsMap_comp B S hS X.1 g.hom (schemeSpaceMap ψ).hom)
    rw [hcomp]
    exact schemeSpacePointToScheme_pointsMap B S hS ψ (pointsMap B S hS X.1 g.hom x)
  ext y'
  simp only [Set.mem_preimage, mem_relativeAssassinContainmentLocus_iff, hass]
  exact ⟨fun h x hx hxy ↦ h x hx (hinj ((hpt x).symm.trans hxy)),
    fun h x hx hxy ↦ h x hx ((hpt x).trans (congrArg _ hxy))⟩

/-- **The containment locus over an open immersion of the base.** For `ψ : V' ⟶ V` a morphism of
the site whose underlying scheme morphism is an open immersion, the containment locus of
`g : X ⟶ schemeSpace V'` in `|V'|` is the inverse image of the containment locus of
`g ≫ schemeSpaceMap ψ` in `|V|`. -/
theorem relativeAssassinContainmentLocus_comp_schemeSpaceMap_of_isOpenImmersion
    {X : AlgebraicSpaces B S hS} {V' V : BigFppfOver B S hS} (ψ : V' ⟶ V)
    (g : X ⟶ schemeSpace V')
    (hψ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ψ))
    (F : Modules.{u, u} B S hS X.1 X.2) (U : Set (points B S hS X.1)) :
    relativeAssassinContainmentLocus B S hS V' g F U =
      ((BigFppfOver.toScheme B S hS).map ψ).base ⁻¹'
        relativeAssassinContainmentLocus B S hS V (g ≫ schemeSpaceMap ψ) F U :=
  have := hψ
  relativeAssassinContainmentLocus_comp_schemeSpaceMap B S hS ψ g inferInstance
    ((BigFppfOver.toScheme B S hS).map ψ).isOpenEmbedding.injective F U

end AlgebraicGeometry.Space

end
