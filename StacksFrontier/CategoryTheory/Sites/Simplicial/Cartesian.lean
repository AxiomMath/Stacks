module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransition

/-!
# Cartesian sheaves on the total site of a simplicial site

Let `S` be a simplicial-site situation. A sheaf `F` on its total site restricts to a sheaf `Fₙ`
on every component site, and an arrow `φ : [m] ⟶ [n]` of the simplex category induces the
canonical transition `f_φ⁻¹ Fₘ ⟶ Fₙ` of Stacks 09WF. The sheaf is *cartesian* when every one of
those transitions is an isomorphism.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.IsCartesianSheaf`: **Stacks 07TF (1)** for a sheaf of
  sets.
* `CategoryTheory.SimplicialSiteSituation.IsCartesianAbSheaf`: **Stacks 07TF (1)** for a sheaf
  of abelian groups.

## Implementation notes

The transition is `CategoryTheory.SimplicialSiteSituation.fiberTransition`, the inverse-image
mate of the direct-image transition induced by the cross-fibre arrows of the total category. It
is therefore the map the source writes `F(φ)`, and not an arbitrary morphism between the
components of `F`.

For a sheaf of abelian groups, the underlying sheaf of sets detects isomorphisms of component
abelian sheaves — `CategoryTheory.sheafCompose` along a faithful, limit-preserving forgetful
functor reflects isomorphisms — so cartesianness of an abelian sheaf is stated as
cartesianness of its underlying sheaf of sets. That avoids committing to a second inverse-image
construction on abelian sheaves at this point and makes the abelian statement literally an
instance of the set-valued one.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.SimplicialSiteSituation

/-- **Stacks 07TF.** A sheaf of sets on the total site of a simplicial site is *cartesian* if
every canonical transition `f_φ⁻¹ Fₘ ⟶ Fₙ` between its components is an isomorphism. -/
@[stacks 07TF "cartesian sheaves of sets"]
abbrev IsCartesianSheaf (S : SimplicialSiteSituation.{u})
    (F : Sheaf S.totalTopology (Type u)) : Prop :=
  ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), IsIso ((fiberTransition S φ).app F)

/-- **Stacks 07TF.** A sheaf of abelian groups on the total site of a simplicial site is
*cartesian* if the canonical transitions of its underlying sheaf of sets are isomorphisms. -/
@[stacks 07TF "cartesian sheaves of abelian groups"]
abbrev IsCartesianAbSheaf (S : SimplicialSiteSituation.{u})
    (F : Sheaf S.totalTopology Ab.{u}) : Prop :=
  IsCartesianSheaf S ((sheafCompose S.totalTopology (forget Ab.{u})).obj F)

end CategoryTheory.SimplicialSiteSituation

end
