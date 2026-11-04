module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.SliceUnitModule
import StacksCore.Tactic.StacksAttribute

/-!
# The two spellings of `j_{U!} O_U` agree

Let `R` be a sheaf of rings on a site `(C, J)` and let `U : C`. This library builds the
extension by zero of the structure sheaf of the localised site `C/U` in two unrelated ways:

* `Stacks.SheafOfModules.extensionByZeroUnit`, the sheafification of the free module
  `X ↦ (X ⟶ U) →₀ R(X)` of Stacks 093C, which exists for a site, a ring and a module universe
  that are mutually independent;
* `Stacks.Sites.OverModules.extensionByZeroUnit`, the extension by zero along `Over.forget U`
  — Mathlib's `SheafOfModules.pullback` for the identity of `R|_U` — applied to the rank-one
  module of `C/U`, which is the form Stacks 03DI is stated in.

No comparison between the two existed. This file supplies it: both corepresent the functor
sending a sheaf of modules to its sections over `U` — the first by Stacks 0G1V in the form
`Stacks.SheafOfModules.extensionByZeroUnitHomEquiv`, the second by
`Stacks.Sites.OverModules.extensionByZeroHomEquiv` — so the two are canonically isomorphic.

## Main definitions

* `Stacks.Sites.OverModules.extensionByZeroUnitCorepresentableBy`: the extension by zero of the
  rank-one module corepresents the sections over `U`. The matching statement for the sheafified
  free module is `Stacks.SheafOfModules.extensionByZeroUnitCorepresentableBy`, next to
  Stacks 0G1V itself.
* `Stacks.SheafOfModules.extensionByZeroUnitIsoSliceUnit`: the resulting isomorphism of the two
  spellings.

## Implementation notes

The isomorphism is `CategoryTheory.Functor.CorepresentableBy.uniqueUpToIso`; nothing is proved
here beyond packaging the two existing bijections, and in particular no new corepresentability
argument is carried out.

The four universes stay independent. Writing `C : Type u₁`, `Category.{v₁} C` and
`R : Sheaf J RingCat.{w}`, both objects live in `SheafOfModules.{max u₁ v₁ w t}` for a free
`t`: that is the universe `Stacks.SheafOfModules.extensionByZeroUnit.{u₁, v₁, w, t}` lands in,
and it is `Stacks.Sites.OverModules.extensionByZeroUnit.{v₁, u₁, w, t}`'s universe
`max u v w m` after renaming. So the comparison needs no universe hypothesis at all, and in
particular does not force the four universes to agree — which is what the docstring of
`Stacks.SheafOfModules.extensionByZeroUnitHomEquiv` records as the reason for preferring the
sheafified-free spelling.

The two sheafification instances that `Stacks.Sites.OverModules.extensionByZeroUnit` asks for
are discharged rather than hypothesised, by `Stacks.SheafOfModules.siteHasSheafify` and
`Stacks.SheafOfModules.siteWEqualsLocallyBijective`: at the module universe `max u₁ v₁ w t` the
site is essentially small, so both hold unconditionally.

## References

* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u₁ v₁ w t

namespace Stacks.Sites.OverModules

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J AddCommGrpCat.{max u₁ v₁ w t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u₁ v₁ w t}]

/-- **Stacks 0G1V as a corepresentability statement, for the extension by zero of the rank-one
module.** `Stacks.Sites.OverModules.extensionByZeroUnit` corepresents the sections over `U`;
this is `extensionByZeroHomEquiv` together with its naturality. -/
@[stacks 0G1V "corepresentability of the extension-by-zero spelling"]
def extensionByZeroUnitCorepresentableBy (O : Sheaf J RingCat.{w}) (U : C) :
    (SheafOfModules.evaluation O (op U) ⋙
        forget (ModuleCat.{max u₁ v₁ w t} (O.obj.obj (op U)))).CorepresentableBy
      (extensionByZeroUnit.{v₁, u₁, w, t} J O U) where
  homEquiv := extensionByZeroHomEquiv.{v₁, u₁, w, t} J O U _
  homEquiv_comp g f := extensionByZeroHomEquiv_naturality.{v₁, u₁, w, t} J O U f g

end Stacks.Sites.OverModules

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

attribute [local instance] siteHasSheafify siteWEqualsLocallyBijective

/-- **The two spellings of `j_{U!} O_U` are isomorphic.** The sheafified free module of
Stacks 093C and the extension by zero of the rank-one module of `C/U` both corepresent the
sections over `U`, so they are canonically isomorphic — with the site, its morphisms, the ring
values and the module sections in four independent universes. -/
def extensionByZeroUnitIsoSliceUnit (R : Sheaf J RingCat.{w}) (U : C) :
    extensionByZeroUnit.{u₁, v₁, w, t} R U ≅
      Stacks.Sites.OverModules.extensionByZeroUnit.{v₁, u₁, w, t} J R U :=
  (extensionByZeroUnitCorepresentableBy.{u₁, v₁, w, t} R U).uniqueUpToIso
    (Stacks.Sites.OverModules.extensionByZeroUnitCorepresentableBy.{u₁, v₁, w, t} J R U)

end Stacks.SheafOfModules

end
