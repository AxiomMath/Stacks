module

public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIso
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.HgroupAndDerivedSections

/-!
# Cohomology groups are transported along an isomorphism of schemes

For an isomorphism `f : X ⟶ Y` of schemes the abelian-group-valued cohomology functor
`Hfunctor` of [Stacks, Tag 01E3] on `X` is the cohomology functor on `Y` precomposed with the
direct image: `Hⁿ(X, -) ≅ Hⁿ(Y, f_* -)`, as an isomorphism of functors on *all* sheaves of
`𝒪_X`-modules.

Being an isomorphism of functors rather than a statement about vanishing, this carries a
cohomology class and a morphism of modules from one model of a scheme to another.

## Main definitions

* `Stacks.Cohomology.ModuleComparison.hfunctorIsoPushforward`: the natural isomorphism
  `Hⁿ(X, -) ≅ Hⁿ(Y, f_* -)`.
* `Stacks.Cohomology.ModuleComparison.hgroupIsoPushforward`: its component,
  `Hⁿ(X, M) ≅ Hⁿ(Y, f_* M)`.
* `Stacks.Cohomology.ModuleComparison.hfunctorPullbackIso` and
  `Stacks.Cohomology.ModuleComparison.hgroupPullbackIso`: the inverse-image form,
  `Hⁿ(X, e^* F) ≅ Hⁿ(Y, F)` for `e : X ≅ Y`, which is the form a transported statement consumes.

## Implementation notes

Sections over the whole space of a direct image are sections over the whole space, so
`Scheme.Modules.pushforward f ⋙ secF Y.ringCatSheaf ⊤` and `secF X.ringCatSheaf ⊤` are the same
functor, by definitional unfolding. The direct image along an isomorphism is an equivalence,
hence exact and preserving injective objects, so
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` applies and nothing beyond that
identity is needed.

Instance arguments are supplied positionally. At the `CategoryTheory.sheafCompose` expression
`X.ringCatSheaf` instance search does not find the additivity of sections over an open, which is
why `secFAdditive` is passed as a term; the remaining arguments are determined by unification
with the stated type, where `Hfunctor` carries them.

## References

* [Stacks Project, Tag 01E3](https://stacks.math.columbia.edu/tag/01E3)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Cohomology.ModuleComparison

variable {X Y : Scheme.{u}}

/-- **Cohomology along an isomorphism of schemes, naturally in the module.** For an isomorphism
`f : X ⟶ Y` of schemes, `Hⁿ(X, -)` is `Hⁿ(Y, f_* -)` as functors on sheaves of `𝒪_X`-modules. -/
def hfunctorIsoPushforward (f : X ⟶ Y) [IsIso f] (n : ℕ) :
    Hfunctor X.ringCatSheaf ⊤ n ≅
      Scheme.Modules.pushforward f ⋙ Hfunctor Y.ringCatSheaf ⊤ n :=
  @Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
    _ _ _ _ _ _ _ _ _ _ _ (Scheme.Modules.pushforward f) (secF Y.ringCatSheaf ⊤)
    _ (secFAdditive _ _) _ _ _ n

/-- The component of `hfunctorIsoPushforward` at a module: `Hⁿ(X, M) ≅ Hⁿ(Y, f_* M)` for an
isomorphism `f : X ⟶ Y` of schemes. -/
def hgroupIsoPushforward (f : X ⟶ Y) [IsIso f] (n : ℕ) (M : X.Modules) :
    Hgroup X.ringCatSheaf ⊤ n M ≅
      Hgroup Y.ringCatSheaf ⊤ n ((Scheme.Modules.pushforward f).obj M) :=
  (hfunctorIsoPushforward f n).app M

/-- **Cohomology of an inverse image along an isomorphism of schemes, naturally in the module.**
For `e : X ≅ Y` the functor `Hⁿ(X, e^* -)` on sheaves of `𝒪_Y`-modules is `Hⁿ(Y, -)`.

The inverse image along `e.hom` is the direct image along `e.inv`, by
`AlgebraicGeometry.Scheme.Modules.pullbackIsoPushforward`. -/
def hfunctorPullbackIso (e : X ≅ Y) (n : ℕ) :
    Scheme.Modules.pullback e.hom ⋙ Hfunctor X.ringCatSheaf ⊤ n ≅
      Hfunctor Y.ringCatSheaf ⊤ n :=
  Functor.isoWhiskerRight (Scheme.Modules.pullbackIsoPushforward e.symm)
      (Hfunctor X.ringCatSheaf ⊤ n) ≪≫
    (hfunctorIsoPushforward e.inv n).symm

/-- The component of `hfunctorPullbackIso` at a module: `Hⁿ(X, e^* F) ≅ Hⁿ(Y, F)` for an
isomorphism `e : X ≅ Y` of schemes. -/
def hgroupPullbackIso (e : X ≅ Y) (n : ℕ) (F : Y.Modules) :
    Hgroup X.ringCatSheaf ⊤ n ((Scheme.Modules.pullback e.hom).obj F) ≅
      Hgroup Y.ringCatSheaf ⊤ n F :=
  (hfunctorPullbackIso e n).app F

end Stacks.Cohomology.ModuleComparison

end
