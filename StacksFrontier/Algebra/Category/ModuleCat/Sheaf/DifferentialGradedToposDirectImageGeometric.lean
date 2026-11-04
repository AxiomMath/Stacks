module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackMonoidal

/-!
# The comparison of underlying sheaves of sets for the geometric direct image

`DifferentialGradedToposDirectImage.lean` builds the direct image of sheaves of differential
graded modules out of three parameters about *ordinary* sheaves of modules: a functor `G`, its
additivity and lax monoidal structure, and a comparison

`ν : (-)^set ⋙ f_* ≅ G ⋙ (-)^set`

identifying the underlying sheaf of sets of `G M` with the direct image of the underlying sheaf
of sets of `M`. This file discharges `ν` for the one `G` that matters, the direct image
`Stacks.Sheaves.RingedToposModules.pushforwardModules` of a morphism of ringed topoi: there
`ν` is the **identity**, because `pushforwardModules` is *defined* as "restrict scalars, push
forward, restrict along the unit" and the middle step is the direct image of sheaves of sets.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.toposPushforwardSetIso`: **the comparison `ν` for the
  geometric direct image, as the identity isomorphism.** Naturality is therefore free.

## Implementation notes

**What this removes from the residual, and what it does not.** Of the three parameters that
`DifferentialGradedToposDirectImage.lean` quantifies, two are now known not to be obstructions
at the geometric direct image:

* `ν` is the identity, proved here;
* `G.Additive` is already an instance, `Stacks.Sheaves.RingedToposModules`
  `.additive_pushforwardModules`, so it needs nothing.

The remaining one is `G.LaxMonoidal`, and it is the coherence residual named in this
development: `Stacks.SheafOfModules.RingedToposPullback.pushforwardLaxMonoidal` turns
`Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence f` — compatibility of the binary
comparison of Tag 03EL with the associator and the two unitors, three fields — into
`(pushforwardModules f).LaxMonoidal`. That hypothesis is available:
`Stacks.SheafOfModules.RingedToposPullback.pullbackCoherence`, tagged 03EL in
`RingedToposPullbackCoherence.lean`, proves it for every morphism of ringed topoi, from the
associativity and the two unitality theorems in the files beside it. A binary tensor
isomorphism alone is not a monoidal structure, which is why the instance is assembled there
rather than postulated here.

**That instantiation is done, and what it does and does not give.** Instantiating
`SheafOfModules.nonempty_corepresentableBy_and_flat` at `G = pushforwardModules f` is
`SheafOfModules.freeDGModule_isGoodToposBaseChange` of
`FreeDifferentialGradedModuleToposPullback.lean`: condition (3) of Tag 0FSA for `A[S]` at a
genuine morphism of ringed topoi, with no hypothesis at all, `PullbackCoherence f` being
supplied for every such morphism by `RingedToposPullbackCoherence.lean`. The plumbing it needed
— reconciling `Stacks.TensorSheafWorld.monoidalCategory`, keyed on the
`CategoryTheory.Sheaf.toRingCat` spelling of the ring sheaf and used throughout the differential
graded development, with `Stacks.Sheaves.RingedToposModules.structureMonoidalCategory`, keyed on
the `structureRingSheaf` spelling in which `pushforwardModules` is typed — is done there, by
threading the `LaxMonoidal` structure explicitly rather than by instance search; the two
structures are equal by `rfl`.

It gives condition (3) for `A[S]` **and for nothing else.** In particular it says nothing about
the cone `C(𝟙_{A[S]})` on the identity of `A[S]`, which the tower of the first proof of
Tag 0FSH also needs: a morphism out of that cone is a degree `-1` right `A`-linear family out of
`A[S]`, which is a homomorphism of *graded* modules into
`SheafOfModules.DifferentialGradedModule.gradedShiftDown`, and every clause of
`SheafOfModules.IsGoodToposBaseChange` is about homomorphisms of *differential* graded modules
out of the module in question, so none of them constrains such a datum. The base change of the
cone is proved separately, in
`ConeIdentityFreeDifferentialGradedModuleToposPullback.lean`.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf AlgebraicGeometry
open SheafOfModules SheafOfModules.DifferentialGradedModule

universe w v u v' u'

namespace Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The comparison `ν` for the geometric direct image is the identity.** The direct image of
sheaves of modules along a morphism of ringed topoi is defined as restriction of scalars
followed by the direct image of sheaves of abelian groups and a restriction along the unit, none
of which changes the underlying sheaf of sets; so the underlying sheaf of sets of `f_*M` is the
direct image of the underlying sheaf of sets of `M` on the nose, and naturality in `M` is free.
This is the datum `ν` of `SheafOfModules.DifferentialGradedModule.toposPushforward`. -/
noncomputable def toposPushforwardSetIso (f : RingedToposHom X Y) :
    _root_.SheafOfModules.toSetSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        f.toToposHom.pushforward ≅
      pushforwardModules f ⋙
        _root_.SheafOfModules.toSetSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  Iso.refl _

omit [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison is the identity on each module, by construction. -/
@[simp]
theorem toposPushforwardSetIso_hom_app (f : RingedToposHom X Y)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (toposPushforwardSetIso f).hom.app M = CategoryStruct.id _ :=
  rfl

end Stacks.Sheaves.RingedToposModules

end
