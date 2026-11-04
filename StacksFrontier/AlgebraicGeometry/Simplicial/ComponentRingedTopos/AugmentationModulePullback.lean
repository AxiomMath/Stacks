module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Augmentation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify

/-!
# The restriction to a simplicial degree of a module pulled back along a ringed augmentation

Let `A` be a ringed augmentation of a simplicial-site situation `S` towards a ringed site
`(D, K, O_D)`, with total morphism of ringed topoi `a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` and
component morphisms `a_n = a ∘ g_n` of Stacks 0D9D. For a sheaf of `O_D`-modules `F` the
restriction of `a^*F` to the degree-`n` component is `a_n^*F`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.componentPullbackModulesIso`:
  `a_n^* ≅ a^* ⋙ g_n^*`, that is `(a^*F)|_n ≅ a_n^*F`.

## Implementation notes

The component morphism of ringed topoi `a_n` *is* the composite `a ∘ g_n` — that is how
`CategoryTheory.SimplicialSiteSituation.RingedAugmentation.componentRingedHom` is defined — so
the comparison is the pseudofunctoriality of the pullback of sheaves of modules,
`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso` of Stacks 03D8, and nothing further.
In particular no compatibility of the augmentation with the simplicial transitions is used, and
the comparison is canonical: its mate is the inverse of the comparison of direct images.

Restriction to a component here is the pullback of modules along `g_n`, which is the reading in
which `a_n = a ∘ g_n` holds on the nose. It is isomorphic to, but not syntactically, the literal
restriction functor
`CategoryTheory.SimplicialSiteSituation.componentModuleRestriction` of Stacks 0D72; comparing the
two needs the dependence of the inverse image of sheaves of modules on the chosen functor of
sheaves of sets, which is
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso`, together with the comparison
`CategoryTheory.SimplicialSiteSituation.componentRingedTopos_setRestrictionIso` of Stacks 09WG.

Sheaves of modules on the total site and on a component are formed at the site universe, as in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleLowerShriek.lean`: the
sheafification of abelian sheaves that the pullback of modules is built from is available there
because the categories are small, and not at an independent coefficient universe. The two
instances are therefore supplied locally, exactly as in that file.

## References

* [Stacks Project, Section 85.10 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- Abelian sheaves on the total site of a simplicial-site situation are sheafifiable at the
site universe, the total category being small there. -/
local instance hasWeakSheafifyTotalModulePullback (S : SimplicialSiteSituation.{u}) :
    HasWeakSheafify S.totalTopology AddCommGrpCat.{u} :=
  (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology).1

/-- On the total site at the site universe, the maps inverted by sheafification of abelian
sheaves are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijectiveTotalModulePullback (S : SimplicialSiteSituation.{u}) :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  letI : HasSheafify ((equivSmallModel.{u} (S.totalCategory : Type u)).inverse.inducedTopology
      S.totalTopology) AddCommGrpCat.{u} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u, u + 1, u}
    S.totalTopology

attribute [local instance] hasWeakSheafifyComponent

namespace RingedAugmentation

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

/-- **The restriction of `a^*F` to a simplicial degree is `a_n^*F`.** The pullback of sheaves of
`O_D`-modules along the degree-`n` component morphism of ringed topoi `a_n` of Stacks 0D9D is the
pullback along the total ringed augmentation followed by the pullback along the component
morphism `g_n` of Stacks 0D72.

Since `a_n` is the composite `a ∘ g_n`, this is the pseudofunctoriality of Stacks 03D8. -/
def componentPullbackModulesIso (n : SimplexCategory) :
    ((A.componentRingedHom n).toModulesHom.pullbackModules) ≅
      (A.totalRingedHom.toModulesHom.pullbackModules) ⋙
        ((componentRingedToposHom S A.O n).toModulesHom.pullbackModules) :=
  AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
    (componentRingedToposHom S A.O n) A.totalRingedHom

end RingedAugmentation

end CategoryTheory.SimplicialSiteSituation

end
