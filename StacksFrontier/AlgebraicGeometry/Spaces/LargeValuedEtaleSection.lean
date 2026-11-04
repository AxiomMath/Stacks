module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType

/-!
# Sections of étale morphisms onto a representable presheaf

Let `S` be a scheme contained in a big fppf site `B`, let `T` be an object of the big fppf
site of `S`, let `X` be an algebraic space over `S` with values in `Type (u + 1)` and let
`p : X ⟶ uliftYoneda.obj T` be étale in the sense of [Stacks, Tag 03FR]. Every section
`s : uliftYoneda.obj T ⟶ X` of `p` is then étale after every represented base change: it is
representable by objects of the site, and each of those base changes is an étale morphism of
schemes.

## Main results

* `AlgebraicGeometry.Space.relative_etale_of_section`: a section of an étale morphism onto a
  universe-lifted Yoneda presheaf is étale after every represented base change.

## References

* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A section of an étale morphism onto a universe-lifted Yoneda presheaf is étale after every
represented base change.

Here `X` is an algebraic space over `S` with values in `Type (u + 1)`, the morphism
`p : X ⟶ uliftYoneda.obj T` is étale in the sense of [Stacks, Tag 03FR], and `s` is a section of
`p`.
-/
theorem relative_etale_of_section {T : BigFppfOver B S hS}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hX : IsAlgebraicSpaceULift.{u + 1} B S hS X)
    {p : X ⟶ (uliftYoneda.{u + 1}).obj T} (hp : IsEtaleULift.{u + 1} B S hS p)
    (s : (uliftYoneda.{u + 1}).obj T ⟶ X) (hs : s ≫ p = 𝟙 _) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) s := by
  obtain ⟨W, q, hqS, hqE⟩ := hX.exists_atlas
  have hsrep : (uliftYoneda.{u + 1}).relativelyRepresentable s :=
    Functor.relativelyRepresentable.of_diag hX.diagonal_representable s
  obtain ⟨T₁, σ, ψ, hpb⟩ := hqE.rep s
  have hσS : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map σ) :=
    hqS.property s ψ σ hpb
  have hσE : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map σ) :=
    hqE.property s ψ σ hpb
  obtain ⟨ψ₀, hψ₀⟩ := (uliftYoneda.{u + 1}).map_surjective ψ
  obtain ⟨π, hπ⟩ := (uliftYoneda.{u + 1}).map_surjective (q ≫ p)
  have hπE : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map π) :=
    (relative_etale_uliftYoneda_map_iff B S hS π).mp (hπ ▸ hp W q hqE)
  have hcompσ : ψ₀ ≫ π = σ := by
    apply (uliftYoneda.{u + 1}).map_injective
    rw [Functor.map_comp, hψ₀, hπ, ← Category.assoc, hpb.w, Category.assoc, hs,
      Category.comp_id]
  have hψE : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map ψ₀) := by
    have : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map ψ₀ ≫
        (BigFppfOver.toScheme B S hS).map π) := by
      rwa [← Functor.map_comp, hcompσ]
    exact AlgebraicGeometry.Etale.of_comp ((BigFppfOver.toScheme B S hS).map ψ₀)
      ((BigFppfOver.toScheme B S hS).map π)
  refine FormalSpace.relative_etale_of_comp_surjective_etale' B S hS σ s hsrep ?_
  rw [← hpb.w, ← hψ₀]
  exact relative_comp B S hS ((relative_etale_uliftYoneda_map_iff B S hS ψ₀).mpr hψE) hqE

end AlgebraicGeometry.Space

end
