module

public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportSiteTensorHomDiagonal
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalCurrying

/-!
# What the route through `Ri_*` of [Stacks, Tag 0E2N] still needs, as two equations

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces and write `G = Ri_* 𝒪_Z`. The
second of the three items [Stacks, Tag 0E2N] is reduced to in the module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/TensorHomTorAmplitude.lean` is the
identification of `Ri_*` of the canonical map with the diagonal of [Stacks, Tag 0BYS] at `G`.
There are now three morphisms of one type in play, for objects `K` and `L` of `D(𝒪_X)`:

`K ⊗^𝐋_{𝒪_X} RSheafHom(G, L) ⟶ RSheafHom(G, K ⊗^𝐋_{𝒪_X} L)`,

namely `Stacks.Duality.TensorHomTorAmplitude.tensorHomDiagonalAtPushforwardStructureSheaf`, the
adjunct under the composite of the adjunctions of [Stacks, Tag 079W] and [Stacks, Tag 0A76];
`AlgebraicGeometry.RingedSite.curryTensorHomDiagonal`, the adjunct under [Stacks, Tag 08J8]; and
`AlgebraicGeometry.RingedSite.interfaceDerivedTensorHomDiagonal`, the class of the complex-level
morphism of [Stacks, Tag 0BYR].

The first two are adjuncts of the **same** interchange under two adjunctions on the **same** pair
of functors, so by `CategoryTheory.Adjunction.tensorHomDiagonal_eq_of_counit_eq` they agree as
soon as the two counits do. That is the content of this file.

## Main results

* `tensorHomDiagonalAtPushforwardStructureSheaf_eq_curryTensorHomDiagonal`:
  **the two adjunction-theoretic diagonals agree as soon as the two evaluation morphisms do.**
* `derivedTensorHomDiagonal_eq_tensorHomDiagonalAtPushforwardStructureSheaf_of`:
  the whole of item 2, from those two equations: the complex-model diagonal is the adjunct under
  the composite adjunction.

## What is proved and what is not

Neither hypothesis is discharged, and no tag is placed below. What is supplied is that item 2 is
now **two** equations, each between morphisms the library has:

* the **evaluation comparison**. The counit of
  `Stacks.Duality.TensorHomTorAmplitude.tensorSheafHomAdjunctionAtPushforwardStructureSheaf` — the
  evaluation `G ⊗^𝐋 RSheafHom(G, L) ⟶ L` assembled from the units and counits of
  [Stacks, Tag 079W] and [Stacks, Tag 0A76] — against the counit of
  `AlgebraicGeometry.RingedSite.interfaceDerivedTensorSheafHomAdjunction`, which by
  `AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction_counit_app` is the transpose of
  the identity under `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, carried along the
  commutativity constraint of [Stacks, Tag 0FPT] and the comparison of the site's two derived
  tensor products.
* the **diagonal comparison**, which is
  `AlgebraicGeometry.RingedSite.interfaceDerivedTensorHomDiagonal_eq_curryTensorHomDiagonal_iff`
  and lives entirely inside the derived-internal-Hom development: no pushforward, no projection
  formula, no closed immersion.

The diagonal is pinned by `CategoryTheory.Adjunction.eq_tensorHomDiagonal`, whose equation
mentions the counit alone, so the comparison that item 2 needs is of the two evaluation
morphisms rather than of the units of the two adjunctions.

## Implementation notes

Both statements below are closed by a single term. In this context the ringed-space structure
sheaf `S.X.sheaf` has type `TopCat.Sheaf CommRingCat _` where
`AlgebraicGeometry.RingedSite.O` asks for `Sheaf (Opens.grothendieckTopology _) CommRingCat`, and
the two are definitionally but not reducibly equal, so a goal mentioning both the tensor
bifunctor at `S.X.sheaf` and the derived category of modules over `structureSheafRing S.X` is not
type-correct at `implicit` transparency and `rw` fails on it. This is the discipline of the
neighbouring files, and the rewriting all happens one level up, over an abstract bifunctor in
`StacksFrontier/CategoryTheory/Adjunction/TensorHomDiagonal.lean`.

That the ringed site of opens of `X` carried by
`Stacks.SheafOfModules.ringedSite S.X.sheaf` presents the same two functors as the ringed-space
spelling needs no bridging lemma: `Stacks.SheafOfModules.ringedSite` is an abbreviation whose
`O` field is the given sheaf, and `Stacks.SheafOfModules.derivedSheafHom` is an abbreviation for
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` at that site.

## References

* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DerivedTensor.RingedSite
open RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality.TensorHomTorAmplitude

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The ringed site of opens of the ambient space `X`, the site over which
[Stacks, Tag 08J8] and the complex-model diagonal of [Stacks, Tag 0BYS] are stated. -/
abbrev ambientRingedSite : AlgebraicGeometry.RingedSite.{u, u, u} :=
  Stacks.SheafOfModules.ringedSite S.X.sheaf

/-- **The two adjunction-theoretic diagonals at `Ri_* 𝒪_Z` agree as soon as the two evaluation
morphisms do.** `Stacks.Duality.TensorHomTorAmplitude.tensorHomDiagonalAtPushforwardStructureSheaf`
is the adjunct of the interchange under the composite of the adjunctions of [Stacks, Tag 079W]
and [Stacks, Tag 0A76], and `AlgebraicGeometry.RingedSite.curryTensorHomDiagonal` is the adjunct
of the *same* interchange under [Stacks, Tag 08J8] with its tensor slot moved. The two
adjunctions have the same left and the same right adjoint, and by
`CategoryTheory.Adjunction.tensorHomDiagonal_eq_of_counit_eq` the adjunct depends on an
adjunction only through its counit.

The hypothesis is **not** discharged in this library: it is the comparison of the evaluation
morphism assembled from the two adjunctions of `i` with the evaluation morphism of
[Stacks, Tag 08J8]. -/
theorem tensorHomDiagonalAtPushforwardStructureSheaf_eq_curryTensorHomDiagonal
    (hcounit : (tensorSheafHomAdjunctionAtPushforwardStructureSheaf S).counit =
      (RingedSite.interfaceDerivedTensorSheafHomAdjunction (ambientRingedSite S)
        (pushforwardDerivedStructureSheaf S)).counit)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    tensorHomDiagonalAtPushforwardStructureSheaf S K L =
      RingedSite.curryTensorHomDiagonal (ambientRingedSite S)
        (pushforwardDerivedStructureSheaf S) K L :=
  Adjunction.tensorHomDiagonal_eq_of_counit_eq _ _ hcounit _

/-- **Item 2 of the reduction of [Stacks, Tag 0E2N], from the two equations it comes down to.**
Given the comparison of the two evaluation morphisms and the comparison of the complex-model
diagonal of [Stacks, Tag 0BYR] with the adjunct under [Stacks, Tag 08J8], the complex-model
diagonal of [Stacks, Tag 0BYS] at `Ri_* 𝒪_Z` *is* the morphism obtained by adjointness under
`Stacks.Duality.TensorHomTorAmplitude.tensorSheafHomAdjunctionAtPushforwardStructureSheaf`,
which is what that item asserts.

Neither hypothesis is proved here. The second is
`AlgebraicGeometry.RingedSite.interfaceDerivedTensorHomDiagonal_eq_curryTensorHomDiagonal_iff`
read as an equation; the first is discussed in the module documentation. -/
theorem derivedTensorHomDiagonal_eq_tensorHomDiagonalAtPushforwardStructureSheaf_of
    (hcounit : (tensorSheafHomAdjunctionAtPushforwardStructureSheaf S).counit =
      (RingedSite.interfaceDerivedTensorSheafHomAdjunction (ambientRingedSite S)
        (pushforwardDerivedStructureSheaf S)).counit)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))
    (hdiagonal : RingedSite.interfaceDerivedTensorHomDiagonal (ambientRingedSite S)
        (pushforwardDerivedStructureSheaf S) K L =
      RingedSite.curryTensorHomDiagonal (ambientRingedSite S)
        (pushforwardDerivedStructureSheaf S) K L) :
    RingedSite.interfaceDerivedTensorHomDiagonal (ambientRingedSite S)
        (pushforwardDerivedStructureSheaf S) K L =
      tensorHomDiagonalAtPushforwardStructureSheaf S K L :=
  hdiagonal.trans
    (tensorHomDiagonalAtPushforwardStructureSheaf_eq_curryTensorHomDiagonal S hcounit K L).symm

end Stacks.Duality.TensorHomTorAmplitude

end
