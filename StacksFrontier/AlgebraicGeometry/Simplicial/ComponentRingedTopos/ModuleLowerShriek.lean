module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Lower shriek of modules on a simplicial component

Let `S` be a simplicial-site situation and `O` a sheaf of rings on its total site. Restriction of
sheaves of `O`-modules along the inclusion of the degree-`n` component admits a left adjoint
`g_{n!}`. This is the existence assertion of Stacks 0D72, the component structure sheaf being
the restriction of `O` along that inclusion.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentRingSheaf`: the restriction of the total
  sheaf of rings to a component.
* `CategoryTheory.SimplicialSiteSituation.componentModuleRestriction`: restriction of sheaves of
  modules to a component.
* `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriek`: the left adjoint
  `g_{n!}`.
* `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekAdjunction`: its defining
  adjunction.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentModuleRestriction_isRightAdjoint`: the
  existence of the left adjoint.
* `CategoryTheory.SimplicialSiteSituation.componentRingSheaf_structureRingSheaf`: for a sheaf of
  *commutative* rings the component ring sheaf above is, on the nose, the ring sheaf underlying
  the structure sheaf of the component ringed topos of
  `StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/Basic.lean`, so the adjunction
  below is the one over the structure sheaves of that pair of ringed topoi.

## Implementation notes

Mathlib builds the left adjoint of restriction of sheaves of modules by sheafifying the
presheaf-level left adjoint (`SheafOfModules.PullbackConstruction.adjunction`). It needs the
presheaf-level left adjoint, which instance search supplies because the component and the total
category are literally small, together with sheafification of abelian sheaves on the total site
and the identification of the sheafification equivalences with the locally bijective maps. The
latter two are not instances; they are obtained here from
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` at `UnivLE.{u, u}` and, for the
second, by transporting the small-model statement along
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`, and are
declared as local instances.

Coefficients therefore sit at the site universe. That is not an incidental choice: at a
coefficient universe independent of the site universe `HasWeakSheafify S.totalTopology
AddCommGrpCat` does not hold from the data of a situation, and the construction of the left
adjoint has no input. The same restriction governs
`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentInjective.lean` and
`StacksFrontier/CategoryTheory/Sites/Simplicial/ComponentKInjective.lean`.

The componentwise direct-sum formula for `g_{n!}` — the remaining assertion of Stacks 0D72 — is
not proved here.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})
  (n : SimplexCategory)

/-- The sheaf of rings on the degree-`n` component obtained by restricting a sheaf of rings on
the total site along the component inclusion. -/
noncomputable abbrev componentRingSheaf : Sheaf (S.componentTopology n) RingCat.{u} :=
  ((componentFunctor S n).sheafPushforwardContinuous RingCat.{u}
    (S.componentTopology n) S.totalTopology).obj O

/-- Restriction of sheaves of modules along the inclusion of the degree-`n` component, over the
restricted sheaf of rings. This is the functor `g_n^*` of Stacks 0D72, the structure map of the
component being the identity because its structure sheaf is literal restriction. -/
noncomputable def componentModuleRestriction :
    SheafOfModules.{u} O ⥤ SheafOfModules.{u} (componentRingSheaf S O n) :=
  SheafOfModules.pushforward (F := componentFunctor S n) (𝟙 (componentRingSheaf S O n))

section Adjoint

/-- Abelian sheaves on the total site are sheafifiable at the site universe, the total category
being small there. -/
local instance hasWeakSheafifyTotal : HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
  (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology).1

/-- On the total site at the site universe, the maps inverted by sheafification of abelian
sheaves are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveTotal :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  letI : HasSheafify ((equivSmallModel.{u} (S.totalCategory : Type u)).inverse.inducedTopology
      S.totalTopology) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u}
    S.totalTopology

/-- **Stacks 0D72**, existence of `g_{n!}` at the site universe: restriction of sheaves of
modules to a simplicial component admits a left adjoint. -/
instance componentModuleRestriction_isRightAdjoint :
    (componentModuleRestriction S O n).IsRightAdjoint := by
  unfold componentModuleRestriction
  infer_instance

end Adjoint

/-- Lower shriek `g_{n!}` of sheaves of modules from the degree-`n` component to the total
site: the left adjoint of `componentModuleRestriction`. -/
noncomputable def componentModuleLowerShriek :
    SheafOfModules.{u} (componentRingSheaf S O n) ⥤ SheafOfModules.{u} O :=
  (componentModuleRestriction S O n).leftAdjoint

/-- **Stacks 0D72.** The defining adjunction `g_{n!} ⊣ g_n^*` of lower shriek of modules on a
simplicial component, exhibiting the left adjoint `g_{n!}` of `g_n^*` whose existence the tag
asserts. -/
@[stacks 0D72 "existence of the left adjoint g_{n!} of g_n^* on modules"]
noncomputable def componentModuleLowerShriekAdjunction :
    componentModuleLowerShriek S O n ⊣ componentModuleRestriction S O n :=
  Adjunction.ofIsRightAdjoint (componentModuleRestriction S O n)

/-- For a sheaf of commutative rings on the total site, restricting the underlying sheaf of
rings to a component gives the sheaf of rings underlying the structure sheaf of the component
ringed topos. So `componentModuleLowerShriek` is lower shriek for the modules of the ringed
topoi of `CategoryTheory.SimplicialSiteSituation.componentRingedTopos` and
`…totalRingedTopos`. -/
theorem componentRingSheaf_structureRingSheaf (P : Sheaf S.totalTopology CommRingCat.{u}) :
    componentRingSheaf S (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos P).O) n =
      Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos P n).O :=
  rfl

end CategoryTheory.SimplicialSiteSituation

end
