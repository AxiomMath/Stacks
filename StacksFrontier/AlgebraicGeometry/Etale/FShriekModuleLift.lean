module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift
public import StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction

/-!
# A `Λ`-linear lift of the direct image with compact support

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site. The direct image with
compact support `f_!` of Stacks 0F6R is a functor on abelian sheaves on the small étale sites;
this file lifts it to sheaves of `Λ`-modules for a ring `Λ`, together with the isomorphism
identifying the lift with `f_!` on underlying abelian sheaves.

Nothing of the construction is specific to `f_!`: it is the lift
`Stacks.ModuleCatLift.moduleLift` of an additive functor on abelian sheaves, applied to `f_!`,
which is additive by Stacks 0F5F.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fShriekMod` — the `Λ`-linear direct image with compact support.

## Main results

* `AlgebraicGeometry.SmallEtale.fShriekModForgetIso` — forgetting the `Λ`-module structure of
  `fShriekMod` gives `f_!` on underlying abelian sheaves. This has exactly the type of the
  `hlift` hypothesis of
  `AlgebraicGeometry.SmallEtale.moduleFShriekDerivedAdjunction`, so the `Λ`-linear form of
  Stacks 0F5N proved there now has a witness for `f_!` itself.

## Implementation notes

The coefficient ring is an arbitrary ring, as it is for
`AlgebraicGeometry.SmallEtale.ModuleSheaf`; commutativity is not needed, see the implementation
notes of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLift`.

The coefficient universe is the cutoff `max (u + 1) v r` at which `f_!` is defined, `u` being
the universe of the schemes. Since that cutoff is unrelated to the universes of the small étale
site itself, the lift is applied with its coefficient universe given explicitly: left implicit,
it produces the level constraint `max (u + 1) ?w = max (u + 1) v r`, which has no unique
solution and which the elaborator reports as a stuck universe constraint.

Nothing here carries a `stacks` attribute. The construction is the one of Stacks 0F6R with
coefficients in a ring, but 0F6R is already attributed to
`AlgebraicGeometry.SmallEtale.fShriekFunctor`, of which this is a lift rather than an
independent construction: the underlying abelian sheaf is literally the one `f_!` produces,
and the only thing added is the module structure, which is formal. A second attribute would
double-count the tag. The new mathematical statement this file unlocks is the `Λ`-linear case
of Stacks 0F5N, which is stated and proved in
`StacksFrontier.AlgebraicGeometry.Etale.DerivedUpperShriekAdjunction`.

## References

* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 0F5N](https://stacks.math.columbia.edu/tag/0F5N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SmallEtale

universe u v r

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The direct image with compact support with coefficients in a ring `Λ`.** The `Λ`-linear
lift of the `f_!` of Stacks 0F6R: a functor on sheaves of `Λ`-modules on the small étale sites
whose underlying abelian sheaf is the one `f_!` produces. -/
public def fShriekMod : ModuleSheaf.{u, v, r} B X Λ ⥤ ModuleSheaf.{u, v, r} B Y Λ :=
  Stacks.ModuleCatLift.moduleLift.{max (u + 1) v r, r, _, _, _, _} Λ
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Y.obj Y.property)
    (fShriekFunctor.{u, max v r} B f)

/-- **The `Λ`-linear direct image with compact support lifts `f_!`.** Forgetting the `Λ`-module
structure of `fShriekMod` gives the `f_!` of Stacks 0F6R on the underlying abelian sheaves.
This is the `hlift` hypothesis of
`AlgebraicGeometry.SmallEtale.moduleFShriekDerivedAdjunction`. -/
public def fShriekModForgetIso :
    fShriekMod.{u, v, r} B Λ f ⋙ forgetModuleSheaf.{u, v, r} B Y Λ ≅
      forgetModuleSheaf.{u, v, r} B X Λ ⋙ fShriekFunctor.{u, max v r} B f :=
  Stacks.ModuleCatLift.moduleLiftForgetIso.{max (u + 1) v r, r, _, _, _, _} Λ
    (SmallEtale.topology B X.obj X.property) (SmallEtale.topology B Y.obj Y.property)
    (fShriekFunctor.{u, max v r} B f)

/-- The `Λ`-linear direct image with compact support preserves finite limits, being a lift of
the `f_!` of Stacks 0F5F, which is exact. -/
public instance fShriekMod_preservesFiniteLimits :
    PreservesFiniteLimits (fShriekMod.{u, v, r} B Λ f) :=
  preservesFiniteLimits_of_forgetModuleSheafIso.{u, v, r} B Λ f _
    (fShriekModForgetIso.{u, v, r} B Λ f)

/-- The `Λ`-linear direct image with compact support is additive. -/
public instance fShriekMod_additive : (fShriekMod.{u, v, r} B Λ f).Additive :=
  additive_of_forgetModuleSheafIso.{u, v, r} B Λ f _ (fShriekModForgetIso.{u, v, r} B Λ f)

end AlgebraicGeometry.SmallEtale

end
