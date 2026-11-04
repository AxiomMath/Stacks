module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageEssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualFiniteLocallyFreeSiteTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel

/-!
# The dual of a finite locally free module on the small étale site of an algebraic space

The small étale site of an algebraic space is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`:
its objects lie one universe above its morphisms and above the sections of its structure sheaf.
The duality cluster of [Stacks, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY) is pinned to
a structure sheaf in `CommRingCat.{max u v}`, `u` and `v` being the universes of the objects and
the arrows of the site, because its dual object is the internal Hom of Tag 03EM; so that cluster
reaches the small étale ringed site at neither universe.

`Stacks.SheafOfModules.hasRightDualOfIsFiniteLocallyFreeOnSite` removes the obstruction by
transport along an equivalence of sites at independent universes, and
`AlgebraicGeometry.Space.smallEtaleModelEquivalence` is the equivalence to feed it: the
equi-universe model of the small étale ringed site is an
`AlgebraicGeometry.RingedSite.{u, u, u}`, where the cluster does apply. This file performs that
instantiation.

## Main results

* `AlgebraicGeometry.Space.smallEtaleModelEquivalence_functor_isCocontinuous`: the model
  equivalence is cocontinuous in the direction from the model to the small étale site, which is
  the hypothesis the covering transport consumes.
* `AlgebraicGeometry.Space.hasRightDual_of_isFiniteLocallyFreeOnSite`: **an `𝒪_F`-module which
  is finite locally free on the small étale site of the algebraic space `F` has a right dual**,
  for `AlgebraicGeometry.Space.modulesMonoidalCategory`, the tensor product of Tag 01CA on
  `AlgebraicGeometry.Space.Modules`.

## Implementation notes

**No hypothesis is added.** The statement takes an algebraic space, an `𝒪_F`-module with
sections in `Type u`, and the finite local freeness of Stacks 03DL (2), and nothing else;
`Stacks.SheafOfModules.ReindexLeftDual.reindexIsSheaf` discharges the sheaf condition of the
transported structure presheaf, which the general statement takes as an argument for the reason
recorded in its implementation notes. The
`CategoryTheory.GrothendieckTopology.HasSheafCompose` instance for `forget₂ CommRingCat RingCat`
on the model topology comes from `Stacks.hasSheafCompose_forget₂_commRingCat`, which holds on
every site at every universe of sections and is made a local instance below.

Cocontinuity of `AlgebraicGeometry.Space.smallEtaleModelEquivalence` in the forward direction is
`SheafOfModules.isDenseSubsite_smallModel`, whose induced topology is literally
`AlgebraicGeometry.Space.smallEtaleModelTopology`; the two continuity instances, and the
sheafification instances of the small étale site and of its model, are found by instance search.

The structure sheaf is named as `AlgebraicGeometry.Space.structureSheaf` and never as the
projection `(smallEtaleRingedSite B S hS F hF).O`. The two are equal by `rfl`, but instance
search does not unfold a projection of a structure instance, so at the projection spelling the
sheafification instances of the small étale site are never found and the monoidal structure is
never synthesized.

The module universe of `AlgebraicGeometry.Space.Modules` is `u`, the universe of the sections of
the structure sheaf: that is `max u' v'` for the model site, which is the universe the duality
cluster forces there. No constraint ties it to `u + 1`, the universe of the objects of the small
étale site.

## References

* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL) (2)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **The model equivalence is cocontinuous from the model to the small étale site.** It is the
inverse of `CategoryTheory.equivSmallModel`, and the small étale site is essentially small at the
universe of its morphisms, so `SheafOfModules.isDenseSubsite_smallModel` applies — its induced
topology being `AlgebraicGeometry.Space.smallEtaleModelTopology` on the nose. -/
instance smallEtaleModelEquivalence_functor_isCocontinuous :
    (smallEtaleModelEquivalence B S hS F).functor.IsCocontinuous
      (smallEtaleModelTopology B S hS F) (SmallEtale.topology B S hS F) :=
  have := SheafOfModules.isDenseSubsite_smallModel (SmallEtale.topology B S hS F)
  inferInstanceAs ((equivSmallModel.{u} (SmallEtale B S hS F)).inverse.IsCocontinuous _ _)

variable (hF : IsAlgebraicSpace B S hS F)

attribute [local instance] modulesMonoidalCategory

/-- **An `𝒪_F`-module which is finite locally free on the small étale site of the algebraic
space `F` has a right dual**, for `AlgebraicGeometry.Space.modulesMonoidalCategory`, the tensor
product of Tag 01CA.

This is Tag 0FNY's duality on a ringed site whose objects lie one universe above the sections of
its structure sheaf, which the duality cluster of that tag cannot itself reach. It is
`Stacks.SheafOfModules.hasRightDualOfIsFiniteLocallyFreeOnSite` applied to
`AlgebraicGeometry.Space.smallEtaleModelEquivalence`, the equivalence onto the equi-universe
model of the small étale ringed site, with
`Stacks.SheafOfModules.ReindexLeftDual.reindexIsSheaf` supplying the sheaf condition of the
transported structure presheaf. -/
@[instance_reducible]
noncomputable def hasRightDual_of_isFiniteLocallyFreeOnSite (M : Modules.{u, u} B S hS F hF)
    (hM : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite M) :
    HasRightDual M :=
  Stacks.SheafOfModules.hasRightDualOfIsFiniteLocallyFreeOnSite
    (J' := smallEtaleModelTopology B S hS F)
    (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF)
    (smallEtaleModelEquivalence B S hS F)
    (Stacks.SheafOfModules.ReindexLeftDual.reindexIsSheaf
      (J' := smallEtaleModelTopology B S hS F)
      (structureSheaf B S hS F hF).obj (structureRingPresheaf_isSheaf B S hS F hF)
      (smallEtaleModelEquivalence B S hS F)) M hM

end AlgebraicGeometry.Space

end
