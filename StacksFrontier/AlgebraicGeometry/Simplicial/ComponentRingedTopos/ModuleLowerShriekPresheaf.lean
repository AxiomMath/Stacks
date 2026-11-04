module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriek

/-!
# Lower shriek of modules on a simplicial component, before sheafification

Let `S` be a simplicial-site situation and `O` a sheaf of rings on its total site. Lower shriek
`g_{n!}` of sheaves of modules from the degree-`n` component, defined as the left adjoint of
restriction, is identified here with Mathlib's pullback of sheaves of modules along the component
inclusion, and hence with the presheaf-level pullback followed by sheafification. The
presheaf-level pullback is a colimit over a comma category, which makes the direct-sum formula of
Stacks 0D72 accessible.

The structure map is the identity, the component structure sheaf being the restriction of the
total one.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriek_eq_pullback`: `g_{n!}` is
  Mathlib's pullback of sheaves of modules along the component inclusion.
* `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification`: `g_{n!}`
  is the underlying presheaf of modules, the pullback of presheaves of modules along the
  component inclusion, and sheafification.

## Implementation notes

The sheafification hypotheses are local instances: abelian sheaves on the total site are
sheafifiable at the site universe, and the maps sheafification inverts are the locally bijective
ones. Coefficients therefore sit at the site universe.

Instance search does not unfold the restriction of a sheaf of rings to a component, so Mathlib's
left adjoint of the pushforward of presheaves of modules on small sites is restated at the
spelling of the component structure sheaf by `isRightAdjointPushforwardComponentRingSheaf`.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
  (n : SimplexCategory)

/-- Abelian sheaves on the total site are sheafifiable at the site universe, the total category
being small there. -/
local instance hasWeakSheafifyTotalPresheaf :
    HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
  (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology).1

/-- On the total site at the site universe, the maps inverted by sheafification of abelian
sheaves are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveTotalPresheaf :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  letI : HasSheafify ((equivSmallModel.{u} (S.totalCategory : Type u)).inverse.inducedTopology
      S.totalTopology) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u}
    S.totalTopology

/-- Lower shriek of modules from a simplicial component is Mathlib's pullback of sheaves of
modules along the component inclusion, taken over the identity structure map: the component
structure sheaf is the restriction of the total one, so no comparison of scalars occurs. -/
theorem componentModuleLowerShriek_eq_pullback :
    componentModuleLowerShriek S O n =
      SheafOfModules.pullback.{u} (F := componentFunctor S n)
        (𝟙 (componentRingSheaf S O n)) :=
  rfl

/-- The pushforward of presheaves of modules along the component inclusion, over the identity
structure map, has a left adjoint. -/
local instance isRightAdjointPushforwardComponentRingSheaf :
    (PresheafOfModules.pushforward.{u} (F := componentFunctor S n) (R := O.obj)
      (S := (componentRingSheaf S O n).obj)
      (𝟙 (componentRingSheaf S O n).obj)).IsRightAdjoint :=
  inferInstanceAs (PresheafOfModules.pushforward.{u} (F := componentFunctor S n) (R := O.obj)
    (S := (componentFunctor S n).op ⋙ O.obj)
    (𝟙 ((componentFunctor S n).op ⋙ O.obj))).IsRightAdjoint

/-- **The presheaf description of `g_{n!}`.** Lower shriek of sheaves of modules from the
degree-`n` simplicial component is the underlying presheaf of modules, followed by the pullback
of presheaves of modules along the component inclusion, followed by sheafification. -/
noncomputable def componentModuleLowerShriekIsoSheafification :
    componentModuleLowerShriek S O n ≅
      SheafOfModules.forget (componentRingSheaf S O n) ⋙
        PresheafOfModules.pullback.{u} (F := componentFunctor S n) (R := O.obj)
            (𝟙 (componentRingSheaf S O n).obj) ⋙
          PresheafOfModules.sheafification (R₀ := O.obj) (𝟙 O.obj) :=
  SheafOfModules.pullbackIso.{u} (F := componentFunctor S n) (𝟙 (componentRingSheaf S O n))

end CategoryTheory.SimplicialSiteSituation

end
