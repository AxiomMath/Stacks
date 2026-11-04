module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.MorphismsGeneral

/-!
# Composition of morphisms of ringed sites at independent universes

Stacks 03AD, part (3) is composition of morphisms of ringed sites.  It is formalized as
`AlgebraicGeometry.RingedSite.Hom.comp`, for ringed sites whose objects, morphisms and sections
share a universe — which no site of schemes satisfies, their objects lying one universe above
their morphisms.  This file is the same composition for
`AlgebraicGeometry.RingedSite.HomGeneral`.

What needs it is the change-of-topologies list of Topologies, Section 03FE, whose twenty-seven
morphisms of sites are, as that section says, obtained by *composing* the morphisms `f_big`,
`f_small`, `π_Y` and the identity `(\Sch/X)_τ → (\Sch/X)_{τ'}`.  Stacks 070R asserts that every
one of them is a morphism of ringed sites; with composition available, the assertion for a
composite follows from the assertion for its factors.

## Main definitions

* `AlgebraicGeometry.RingedSite.HomGeneral.comp`: the composite of two morphisms of ringed
  sites.

## Main results

* `AlgebraicGeometry.RingedSite.HomGeneral.comp_u` and
  `AlgebraicGeometry.RingedSite.HomGeneral.comp_fsharp`: its two constituents.

## Implementation notes

The structure map of the composite is the usual
`𝒪_Z ⟶ g_*𝒪_Y ⟶ g_*f_*𝒪_X ≅ (g ∘ f)_*𝒪_X`, the last step being
`CategoryTheory.Functor.sheafPushforwardContinuousComp`.  The site condition of the composite is
Stacks 03CB in its universe-general form, `isMorphismOfSites_comp`.

The three ringed sites have independent object and morphism universes but share the universe of
the sections of their structure sheaves, which is forced: the structure maps compare sheaves of
rings across the sites, so there is one ring universe, and it is also the universe at which the
site conditions are read.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03CB](https://stacks.math.columbia.edu/tag/03CB)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w uX vX uY vY uZ vZ

namespace AlgebraicGeometry.RingedSite

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  {Z : RingedSite.{uZ, vZ, w}}

/-- **Stacks 03AD, part (3), at independent universes.**  Composition of morphisms of ringed
sites.  On structure sheaves it is `𝒪_Z ⟶ g_*𝒪_Y ⟶ g_*f_*𝒪_X ≅ (g ∘ f)_*𝒪_X`. -/
@[stacks 03AD "part (3): composition of morphisms of ringed sites, at independent universes"]
public noncomputable def HomGeneral.comp (f : HomGeneral X Y) (g : HomGeneral Y Z) :
    HomGeneral X Z :=
  letI : IsMorphismOfSites.{w} g.u Z.J Y.J := g.isMorphismOfSites
  letI : IsMorphismOfSites.{w} f.u Y.J X.J := f.isMorphismOfSites
  letI h : IsMorphismOfSites.{w} (g.u ⋙ f.u) Z.J X.J :=
    isMorphismOfSites_comp X.J Y.J Z.J g.u f.u
  { u := g.u ⋙ f.u
    isMorphismOfSites := h
    fsharp := g.fsharp ≫
      (g.u.sheafPushforwardContinuous CommRingCat.{w} Z.J Y.J).map f.fsharp ≫
      (Functor.sheafPushforwardContinuousComp g.u f.u CommRingCat.{w} Z.J Y.J X.J).hom.app X.O }

/-- The underlying functor of a composite is the composite of the underlying functors. -/
@[simp]
public theorem HomGeneral.comp_u (f : HomGeneral X Y) (g : HomGeneral Y Z) :
    (f.comp g).u = g.u ⋙ f.u := rfl

/-- The map on structure sheaves of a composite `f.comp g`. -/
public theorem HomGeneral.comp_fsharp (f : HomGeneral X Y) (g : HomGeneral Y Z) :
    (f.comp g).fsharp = g.fsharp ≫
      (g.u.sheafPushforwardContinuous CommRingCat.{w} Z.J Y.J).map f.fsharp ≫
      (Functor.sheafPushforwardContinuousComp g.u f.u CommRingCat.{w}
        Z.J Y.J X.J).hom.app X.O := rfl

end AlgebraicGeometry.RingedSite

end
