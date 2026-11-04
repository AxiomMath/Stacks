module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Homology.KFlat.Pullback

/-!
# The K-flat resolving datum for the derived pullback

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces. Tag 079W constructs the derived
pullback `Lf^*` out of a *resolving datum* for degreewise pullback: a class of complexes of
`𝒪_Y`-modules resolving every complex, on which degreewise pullback inverts
quasi-isomorphisms. This file records what makes the K-flat complexes such a datum.

Half of the datum is available: every complex admits a quasi-isomorphism from a K-flat complex,
which is Tag 06YS. The other half is the content of Tag 06YJ, and in the source it is deduced
from the stalkwise criterion for K-flatness (Tag 06YB) through Tag 06YC. It is recorded as the
structure `PullbackKFlatInput`, whose two fields are Tag 06YC and the quasi-isomorphism claim
inside the proof of Tag 06YJ; both are proved by
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.pullbackKFlatInput`.

The consequences for the derived pullback hold for any models of the derived categories and take
no datum: `Lf^*` exists by the instance
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy`, its
comparison map with degreewise pullback is invertible at a K-flat complex
(`Stacks.Cohomology.KFlatDerivedPullback.isIso_derivedPullbackComparison_app_of_kFlat`), and
`Lf^*(P) ≅ f^*P` in `D(𝒪_X)` for `P` K-flat is
`Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat`.

## Main definitions

* `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.PullbackKFlatInput`: the two facts about
  degreewise pullback and K-flatness
  which Tag 06YJ takes from the stalkwise criterion.

## Implementation notes

The two fields of `PullbackKFlatInput` are quantified over *all* morphisms of ringed spaces,
not over `f` alone. Both are used at `f` and at the restrictions of `f` to open subspaces, and
a hypothesis attached to one morphism would have to be re-supplied at every restriction.

Complexes carry the type `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules`, and
  degreewise pullback is the retyping
`StacksDraft.KFlat.modulePullback` of `RingedSpaceModuleAdjunction.modulePullback`: the
instances of the tensor product are keyed on `Stacks.SheafOfModules.Tensor.ringSheaf`, and at the
  other,
`rfl`-equal, spelling of the ring sheaf they are searched for before the two are unified, which
fails. Tag 079W is stated at the other spelling, so the two meet at `modulePullback_eq_
modulePullback`, which is `rfl`.

## References

* [Stacks Project, Tag 06YB](https://stacks.math.columbia.edu/tag/06YB)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

universe u

/-- **The two inputs Tag 06YJ takes from the stalkwise criterion for K-flatness.**

The first field is Tag 06YC: degreewise pullback along a morphism of ringed spaces carries a
K-flat complex to a K-flat complex. The second is the claim established inside the proof of Tag
06YJ: degreewise pullback carries a quasi-isomorphism between K-flat complexes to a
quasi-isomorphism. In the source both are consequences of Tag 06YB, which characterises
K-flatness stalkwise. -/
structure PullbackKFlatInput : Prop where
  /-- **Tag 06YC.** The pullback of a K-flat complex is K-flat. -/
  kFlat_pullback : ∀ {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (K : CochainComplex (Modules Y) ℤ), KFlat Y K →
    KFlat X (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K)
  /-- **The quasi-isomorphism claim inside Tag 06YJ.** Degreewise pullback carries a
  quasi-isomorphism between K-flat complexes to a quasi-isomorphism. -/
  quasiIso_pullback : ∀ {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    {K L : CochainComplex (Modules Y) ℤ} (s : K ⟶ L), QuasiIso s →
    KFlat Y K → KFlat Y L →
    QuasiIso (((StacksDraft.KFlat.modulePullback f).mapHomologicalComplex
      (ComplexShape.up ℤ)).map s)

end AlgebraicGeometry.RingedSpace.KFlatDerivedPullback

end
