module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Situation

/-!
# Sheafification of abelian sheaves on a simplicial component

The category in simplicial degree `n` of a simplicial-site situation is a small category at the
site universe, so abelian sheaves on it are sheafifiable there. Several modules need this to form
direct sums or kernels of sheaves of modules on a component.

The statement is a plain theorem rather than an instance: declaring it globally would export a new
`HasWeakSheafify` instance into typeclass search for every site. A module that needs it activates
it with
`attribute [local instance] CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- Abelian sheaves on a simplicial component are sheafifiable at the site universe, the
component being small there. -/
theorem hasWeakSheafifyComponent (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    HasWeakSheafify (S.componentTopology n) AddCommGrpCat.{u} :=
  (GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} (S.componentTopology n)).1

/-- Abelian sheaves on the total site are sheafifiable at the site universe, with the
sheafification adjunction, the total category being small there; `HasWeakSheafify` follows from it
by the projection instance of `HasSheafify`. It is what the derived tensor product of
Stacks 06YU, the module resolution of Stacks 0D9B and the abelian structure of `Mod(O)` are
constructed over. Activate it with `attribute [local instance]` rather than restating it. -/
theorem hasSheafifyTotal (S : SimplicialSiteSituation.{u}) :
    HasSheafify S.totalTopology AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology

/-- On the degree-`n` simplicial component at the site universe, the maps inverted by
sheafification of abelian sheaves are exactly the locally bijective ones. -/
theorem wEqualsLocallyBijectiveComponent (S : SimplicialSiteSituation.{u})
    (n : SimplexCategory) :
    (S.componentTopology n).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} (S.componentTopology n)

end CategoryTheory.SimplicialSiteSituation

end
