module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.CartesianArrowIsoLargeSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCartesianLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentIsLocallyQuasicoherentLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LocallyQuasiCoherentModulesAndAffines

/-!
# A locally quasi-coherent module is cartesian along étale arrows, at a large module universe

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and `𝓖` a locally quasi-coherent
module on `𝒳` (Stacks 06WJ) with sections in `Type (max (u + 1) v w m)`. For an arrow
`f : x ⟶ x'` of `𝒳` lying over an étale morphism of affine schemes, the base-change comparison
`𝒪(x) ⊗_{𝒪(x')} 𝓖(x') ⟶ 𝓖(x)` is bijective. This is the implication (2) ⇒ (1) of Stacks 0H0F
(`AlgebraicGeometry.Stack.isIso_restrictionBaseChange_of_isLocallyQuasicoherent`, at module
universe `u`) at a module universe above the universe of the schemes, for an arbitrary arrow of
`𝒳` rather than one of the affine subcategory: the arrow is isomorphic to the image of a morphism
of affine objects of the small étale site of the scheme below `x'`, where the restriction of `𝓖`
is quasi-coherent, hence cartesian.

## Main results

* `bijective_restrictionBaseChange_of_isLocallyQuasicoherent_freeModuleUniverse` (namespace
  `AlgebraicGeometry.Stack`).

## References

* [Stacks Project, Tag 0H0F](https://stacks.math.columbia.edu/tag/0H0F)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
-/

@[expose] public section

open CategoryTheory Stacks.PresheafOfModules

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **A locally quasi-coherent module is cartesian along an arrow lying over an étale morphism
of affine schemes**, at the module universe `max (u + 1) v w m`. -/
theorem bijective_restrictionBaseChange_of_isLocallyQuasicoherent_freeModuleUniverse
    (G : PresheafOfModules.{max (u + 1) v w m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hG : IsLocallyQuasicoherent B E h S hS p hp G) {x x' : 𝒳} (f : x ⟶ x')
    (hf : Etale (B.inclusion.map (p.map f).left))
    (hx : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x))
    (hx' : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj x')) :
    Function.Bijective (restrictionBaseChange.{v, w, u, max (u + 1) v w m}
      (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
      G f.op) := by
  obtain ⟨hM, hqc⟩ := hG.2 x'
  obtain ⟨e₁, e₂, hsq⟩ := exists_arrowIso_etaleIndex B E h S hS p hp f hf
  have hT : IsAffine ((SmallEtale.toScheme E _ _).obj (etaleChart B E h S hS p f hf)) := hx
  have hT' : IsAffine ((SmallEtale.toScheme E _ _).obj (etaleTop B E h S hS p x')) := hx'
  have h1 :=
    SmallEtale.bijective_restrictionBaseChange_of_isQuasicoherentOnSite_freeModuleUniverse.{u,
      max v w m}
      E _ _ _ hqc hT hT' (etaleChartToTop B E h S hS p f hf)
  have h2 :=
    (bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff_freeModuleUniverse.{u, v, w, m}
    B E h S hS p hp G x' (etaleChartToTop B E h S hS p f hf)).1 h1
  exact (bijective_restrictionBaseChange_iff_of_arrowIso_freeModuleUniverse.{v, w, u,
    max (u + 1) v w m}
    (R := (structureSheaf B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) G
    ((etaleIndex B E h S hS p hp x').map (etaleChartToTop B E h S hS p f hf)).op
    f.op e₂.hom.op e₁.hom.op (by rw [← op_comp, ← op_comp, hsq])).1 h2

end AlgebraicGeometry.Stack

end
