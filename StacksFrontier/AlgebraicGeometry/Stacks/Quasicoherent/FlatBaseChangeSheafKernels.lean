module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleSheafifiedBaseChangeComposition

/-!
# The sheafified small étale pullback along a flat arrow is left exact on quasi-coherent modules

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `φ : x ⟶ y` be an arrow
of `𝒳` lying over a morphism of schemes `a : U ⟶ V`.  The functor `a_{small}^*` of
**Stacks 06WC** on *sheaves* of modules is
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison`, which
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso` identifies with the pullback of
sheaves of modules along the morphism of ringed sites `ε_a` of **Stacks 070R (2)**.

Being a left adjoint, that functor is right exact for free.  It is *not* left exact for free:
left exactness is where the source of **Stacks 0764** spends flatness of `a`, and the sharpest
unconditional form available is left exactness on quasi-coherent modules, which is
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_ι_qcohOnSite_comp_pullback`.  This file
carries that across the identification.

## Main results

* `AlgebraicGeometry.Stack.preservesFiniteLimits_ι_qcohOnSite_comp_sheafifiedPullbackComparison`:
  for `a` flat, `a_{small}^*` read on sheaves of modules is left exact on the quasi-coherent
  modules of the small étale site of `V`.
* `AlgebraicGeometry.Stack.isLimit_mapCone_sheafifiedPullbackComparison_of_isQuasicoherentOnSite`:
  the same at one finite limit cone of quasi-coherent modules.

## Implementation notes

The flatness hypothesis is stated as flatness of `B.inclusion.map (p.map φ).left`, the morphism
of schemes below `φ`, which is the reading used by
`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty`; the morphism of the bounded category of the
big étale site that the base change is taken along,
`AlgebraicGeometry.Stack.smallEtaleBaseMorphism`, has that same morphism of schemes underneath
it, so the two flatness statements are the same one.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {x y : 𝒳} (φ : x ⟶ y)

/-- **The pullback of sheaves of modules on small étale sites along an arrow lying over a flat
morphism of schemes is left exact on quasi-coherent modules.** If the morphism of schemes below `φ`
is flat, then `AlgebraicGeometry.Stack.sheafifiedPullbackComparison` restricted to the
quasi-coherent modules on the small étale site of the scheme below `y` preserves finite limits. -/
theorem preservesFiniteLimits_ι_qcohOnSite_comp_sheafifiedPullbackComparison
    (hflat : Flat (B.inclusion.map (p.map φ).left)) :
    PreservesFiniteLimits
      ((SmallEtale.qcohOnSite E (p.obj y).left.1 (contains_base B E h S hS p y)).ι ⋙
        sheafifiedPullbackComparison B E h S hS p hp τ hτ φ) := by
  let : Flat (SmallEtale.schemeHom E (smallEtaleBaseMorphism B E h S hS p φ)) := hflat
  let := SmallEtale.preservesFiniteLimits_ι_qcohOnSite_comp_pullback E
    (smallEtaleBaseMorphism B E h S hS p φ)
  exact preservesFiniteLimits_of_natIso
    (Functor.isoWhiskerLeft _ (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).symm)

section Cone

variable {J : Type} [SmallCategory J] [FinCategory J]
  {K : J ⥤ SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj y).left.1
    (contains_base B E h S hS p y))}
  (hK : ∀ j, (K.obj j).IsQuasicoherentOnSite)
  {c : Cone K} (hpt : c.pt.IsQuasicoherentOnSite)

/-- A cone of quasi-coherent modules on the small étale site of the scheme below `y`, read in
the full subcategory of quasi-coherent modules. -/
def qcohOnSiteCone :
    Cone ((SmallEtale.qcohOnSite E (p.obj y).left.1
      (contains_base B E h S hS p y)).lift K hK) where
  pt := ⟨c.pt, hpt⟩
  π :=
    { app := fun j => ObjectProperty.homMk (c.π.app j)
      naturality := fun i j f => by
        apply ObjectProperty.hom_ext
        simp }

/-- **The pullback of sheaves of modules on small étale sites along a flat arrow carries a finite
limit cone of quasi-coherent modules to a limit cone.** If the morphism of schemes below `φ` is
flat and `c` is a limit cone over a finite diagram of quasi-coherent modules on the small étale
site of the scheme below `y`, with quasi-coherent cone point, then
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison` maps `c` to a limit cone. -/
def isLimit_mapCone_sheafifiedPullbackComparison_of_isQuasicoherentOnSite
    (hflat : Flat (B.inclusion.map (p.map φ).left)) (hc : IsLimit c) :
    IsLimit ((sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).mapCone c) :=
  letI := preservesFiniteLimits_ι_qcohOnSite_comp_sheafifiedPullbackComparison
    B E h S hS p hp τ hτ φ hflat
  letI h₁ : IsLimit ((SmallEtale.qcohOnSite E (p.obj y).left.1
      (contains_base B E h S hS p y)).ι.mapCone
        (qcohOnSiteCone B E h S hS p hK hpt)) := hc
  isLimitOfPreserves ((SmallEtale.qcohOnSite E (p.obj y).left.1
      (contains_base B E h S hS p y)).ι ⋙
    sheafifiedPullbackComparison B E h S hS p hp τ hτ φ)
    (isLimitOfReflects (SmallEtale.qcohOnSite E (p.obj y).left.1
      (contains_base B E h S hS p y)).ι h₁)

end Cone

end AlgebraicGeometry.Stack

end
