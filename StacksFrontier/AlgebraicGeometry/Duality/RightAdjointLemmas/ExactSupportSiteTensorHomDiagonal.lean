module

public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedHomPushforward
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportSiteTensorHomAdjunction
public import StacksFrontier.CategoryTheory.Adjunction.TensorHomDiagonal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.MiddleSwap

/-!
# The adjunction-theoretic diagonal of [Stacks, Tag 0BYS] at `Ri_* 𝒪_Z`

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces and write `G = Ri_* 𝒪_Z`. The
derived tensor–Hom adjunction at `G`,

`G ⊗^𝐋_{𝒪_X} - ⊣ RSheafHom(G, -)`,

is available as
`Stacks.Duality.TensorHomTorAmplitude.tensorSheafHomAdjunctionAtPushforwardStructureSheaf`, the
composite of the two adjunctions of `i`. This file builds the **diagonal of [Stacks, Tag 0BYS]
out of that adjunction**: for objects `K` and `L` of `D(𝒪_X)` the morphism

`K ⊗^𝐋_{𝒪_X} RSheafHom(G, L) ⟶ RSheafHom(G, K ⊗^𝐋_{𝒪_X} L)`

that is the transpose, under the adjunction, of

`G ⊗^𝐋 (K ⊗^𝐋 RSheafHom(G, L)) ≅ K ⊗^𝐋 (G ⊗^𝐋 RSheafHom(G, L)) ⟶ K ⊗^𝐋 L`,

the commutativity-and-associativity interchange followed by `K ⊗^𝐋 -` of the counit of the
adjunction — which is the evaluation morphism. Together with the adjunction equation
characterizing it and the uniqueness of a morphism satisfying that equation, this is the side of
the identification that [Stacks, Tag 0E2N] needs and that the library did not have: the diagonal
*as an adjunct*, as against the diagonal as the class of a morphism of chosen complexes.

## Main definitions

* `Stacks.Duality.TensorHomTorAmplitude.derivedSheafHomSitePushforwardStructureSheaf`: the
  functor `RSheafHom(G, -)`, the right adjoint of the adjunction.
* `Stacks.Duality.TensorHomTorAmplitude.tensorMiddleSwapAtPushforwardStructureSheaf`: the
  interchange `G ⊗^𝐋 (K ⊗^𝐋 A) ≅ K ⊗^𝐋 (G ⊗^𝐋 A)` at `G`, read off
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.middleSwapIso`.
* `Stacks.Duality.TensorHomTorAmplitude.tensorHomDiagonalAtPushforwardStructureSheaf`: **the
  adjunction-theoretic diagonal of [Stacks, Tag 0BYS] at `G`.**

## Main results

* `Stacks.Duality.TensorHomTorAmplitude.tensorHomDiagonalAtPushforwardStructureSheaf_mate`: the
  adjunction equation characterizing it.
* `Stacks.Duality.TensorHomTorAmplitude.eq_tensorHomDiagonalAtPushforwardStructureSheaf`: that
  equation determines it; nothing else of its type satisfies it.
* `tensorHomDiagonalAtPushforwardStructureSheaf_natural_right` (in the same namespace):
  functoriality in `L`.

## What this is for, and what it is not

[Stacks, Tag 0E2N] is reduced, in the module documentation of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/TensorHomTorAmplitude.lean`, to three
steps of which the second is the identification of `Ri_*` of the canonical map with the diagonal
of [Stacks, Tag 0BYS] at `G`. That step has two halves. The adjunction-theoretic half is proved:
the tensor–Hom adjunction at `G` is the composite of the two adjunctions of `i`, and its
hom-bijection pastes, by
`tensorSheafHomAdjunctionAtPushforwardStructureSheaf_homEquiv`. **The half this file supplies is
the other end of the comparison**: the morphism that half has to be compared *with*, built from
the adjunction and from nothing else, with the adjunction equation that pins it down.

**It is still not the identification, and [Stacks, Tag 0E2N] is not proved here.** What remains
is one equation: that `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal` at the ringed site
of opens of `X` — the class of the complex-level morphism of [Stacks, Tag 0BYR] between a chosen
K-flat and a chosen K-injective representative, conjugated by the two model comparisons —
satisfies the adjunction equation `tensorHomDiagonalAtPushforwardStructureSheaf_mate`, and hence
by `eq_tensorHomDiagonalAtPushforwardStructureSheaf` *is* the morphism below. Both sides are now
pinned by a characterisation — the complex-level one by
`AlgebraicGeometry.RingedSite.eq_derivedTensorHomDiagonal` and the adjunction-theoretic one by
`eq_tensorHomDiagonalAtPushforwardStructureSheaf` — so the comparison is an equation between two
*stated* descriptions rather than between a morphism and a gap, which it was before.

Why that equation is not discharged here, precisely. It asks for the counit of the adjunction —
the evaluation morphism `G ⊗^𝐋 RSheafHom(G, L) ⟶ L` — to be computed on complex
representatives. The adjunction is the composite of [Stacks, Tag 079W] and [Stacks, Tag 0A76],
so its counit is built from the units and counits of those two, whereas the complex-level
diagonal is built from the currying isomorphism of [Stacks, Tag 0A90]. The bridge between the
two is the tensor–internal-Hom bijection of [Stacks, Tag 08J8], and this development has that
bijection — `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` — with naturality in the source
and in the target variable, and **bundled as an adjunction**.
The source clause is `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_source`, the
target clause is `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_naturality_target`, and the
adjunction is `AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction`, all of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrySourceNaturality` and
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality`. The
*object-level* naturality of [Stacks, Tag 08J9] is proved and unconditional in all three
variables, as `AlgebraicGeometry.RingedSite.derivedCurryIso_natural`.

**Two things separate that adjunction from the equation.** First, the slot of the tensor
product: [Stacks, Tag 08J8] fixes the second slot — so
`derivedTensorSheafHomAdjunction` is `- ⊗^𝐋 G ⊣ RSheafHom(G, -)` while
`tensorSheafHomAdjunctionAtPushforwardStructureSheaf` has left adjoint `G ⊗^𝐋 -` — and
`CategoryTheory.Adjunction.ofNatIsoLeft` needs a natural *isomorphism* `- ⊗^𝐋 G ≅ G ⊗^𝐋 -`,
which the commutativity constraint of [Stacks, Tag 0FPT] supplies:
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.isIso_braidingTrans` and the
isomorphism of bifunctors `braidingNatIso` are in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/BraidingNatIso.lean`, carried to the
tensor product [Stacks, Tag 08J8] is stated over along
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso` as
`AlgebraicGeometry.RingedSite.derivedTensorFlipNatIso`, and the slot-moved adjunctions
`AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunctionFlip` and
`AlgebraicGeometry.RingedSite.interfaceDerivedTensorSheafHomAdjunction` are in
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedTensorSheafHomAdjunctionSlot.lean`.
The second of those has exactly the left and right adjoint of
`tensorSheafHomAdjunctionAtPushforwardStructureSheaf` at `G`, with nothing further to transport.

Second, the equation that does not reduce: those are then two adjunctions on the *same* pair of
functors, and an adjunction is data, not a property, so they do not agree for free. The comparison
belongs at their **counits**, not their units. The
units are indeed what distinguishes two adjunctions, but the diagonal is pinned by
`CategoryTheory.Adjunction.eq_tensorHomDiagonal`, whose equation mentions the counit alone, so by
`CategoryTheory.Adjunction.tensorHomDiagonal_eq_of_counit_eq` the comparison this file needs is
of the two **counits** — the evaluation morphism `G ⊗^𝐋 RSheafHom(G, L) ⟶ L` assembled from the
units and counits of [Stacks, Tag 079W] and [Stacks, Tag 0A76] against the evaluation morphism of
[Stacks, Tag 08J8], which is the transpose of the identity under `derivedCurryHomEquiv` by
`AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction_counit_app`. That comparison is
still not proved, and with it item 2 of [Stacks, Tag 0E2N] reduces to one further equation inside
the derived-internal-Hom development; both are stated, and item 2 is deduced from the two, in
`ExactSupportSiteTensorHomDiagonalCurrying.lean` in this directory.

No `@[stacks]` registration is placed on anything below: [Stacks, Tag 0BYS] is registered on
`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal` and its functorialities, the two
morphisms are not yet identified, and a second registration of the tag on a morphism that has
not been compared with the first would assert exactly the identification that is missing.

## Implementation notes

Every proof below is a term or a single `exact`. In this context the ringed-space structure
sheaf `S.X.sheaf` has type `TopCat.Sheaf CommRingCat _` where `AlgebraicGeometry.RingedSite.O`
asks for `Sheaf (Opens.grothendieckTopology _) CommRingCat`, and the two are definitionally but
not reducibly equal, so a goal mentioning both `derivedTensorProductFunctor S.X.sheaf` and
`DerivedCategory (SheafOfModules (structureSheafRing S.X))` is not type-correct at `implicit`
transparency and `rw` fails on it outright. The rewriting all happens one level up, in
`StacksFrontier/CategoryTheory/Adjunction/TensorHomDiagonal.lean` over an abstract bifunctor and in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/MiddleSwap.lean` at a bare ringed
site, where it costs nothing. This is the discipline of `ExactSupportSiteTensorHomAdjunction.lean`
in this directory.

The interchange is taken at the commutativity constraint of [Stacks, Tag 0FPT] and not around
it. A braiding-free monoidal step was caught as a false lemma earlier in this development, and
the involutivity of the commutativity constraint is one of the coherence clauses of
[Stacks, Tag 0FPT] that this library does not have, so nothing below assumes the braiding away.

## References

* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
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

/-- `RSheafHom(Ri_* 𝒪_Z, -)`, the right adjoint of the derived tensor–Hom adjunction at
`Ri_* 𝒪_Z` of `tensorSheafHomAdjunctionAtPushforwardStructureSheaf`. -/
abbrev derivedSheafHomSitePushforwardStructureSheaf :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) :=
  (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj (op (pushforwardDerivedStructureSheaf S))

/-- **The interchange that moves `Ri_* 𝒪_Z` past a tensor factor**:
`(Ri_* 𝒪_Z) ⊗^𝐋 (K ⊗^𝐋 A) ≅ K ⊗^𝐋 ((Ri_* 𝒪_Z) ⊗^𝐋 A)`. This is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.middleSwapIso` at the ringed site of opens
of `X`, that is the associativity constraint of [Stacks, Tag 0FPT], then its commutativity
constraint on the two outer factors, then associativity again. -/
abbrev tensorMiddleSwapAtPushforwardStructureSheaf
    (K A : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    ((derivedTensorProductFunctor S.X.sheaf).obj (pushforwardDerivedStructureSheaf S)).obj
        (((derivedTensorProductFunctor S.X.sheaf).obj K).obj A) ≅
      ((derivedTensorProductFunctor S.X.sheaf).obj K).obj
        (((derivedTensorProductFunctor S.X.sheaf).obj
          (pushforwardDerivedStructureSheaf S)).obj A) :=
  (canonicalDerivedTensorProduct S.X.sheaf).middleSwapIso S.ambientSite
    (pushforwardDerivedStructureSheaf S) K A

/-- **The diagonal of [Stacks, Tag 0BYS] at `Ri_* 𝒪_Z`, built from the adjunction.** For objects
`K` and `L` of `D(𝒪_X)`, the morphism

`K ⊗^𝐋_{𝒪_X} RSheafHom(Ri_* 𝒪_Z, L) ⟶ RSheafHom(Ri_* 𝒪_Z, K ⊗^𝐋_{𝒪_X} L)`

obtained by adjointness under `tensorSheafHomAdjunctionAtPushforwardStructureSheaf` from the
interchange followed by `K ⊗^𝐋 -` of the counit of that adjunction, the counit being the
evaluation morphism `(Ri_* 𝒪_Z) ⊗^𝐋 RSheafHom(Ri_* 𝒪_Z, L) ⟶ L`.

It is `CategoryTheory.Adjunction.tensorHomDiagonal` at that adjunction and that interchange, so
it is not an arbitrary morphism between the two objects; it is **not** identified with
`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal`, and the module documentation says what
such an identification would still take. -/
def tensorHomDiagonalAtPushforwardStructureSheaf
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    ((derivedTensorProductFunctor S.X.sheaf).obj K).obj
        ((derivedSheafHomSitePushforwardStructureSheaf S).obj L) ⟶
      (derivedSheafHomSitePushforwardStructureSheaf S).obj
        (((derivedTensorProductFunctor S.X.sheaf).obj K).obj L) :=
  Adjunction.tensorHomDiagonal (tensorSheafHomAdjunctionAtPushforwardStructureSheaf S)
    (tensorMiddleSwapAtPushforwardStructureSheaf S K
      ((derivedSheafHomSitePushforwardStructureSheaf S).obj L)).hom

/-- **The adjunction equation characterizing the diagonal at `Ri_* 𝒪_Z`.** Tensoring it with
`Ri_* 𝒪_Z` and composing with the counit of the adjunction — the evaluation morphism — gives the
interchange followed by `K ⊗^𝐋 -` of that counit. This is what "obtained by adjointness" means,
and it is the equation the complex-model diagonal of [Stacks, Tag 0BYS] would have to satisfy to
be this morphism. -/
theorem tensorHomDiagonalAtPushforwardStructureSheaf_mate
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    ((derivedTensorProductFunctor S.X.sheaf).obj (pushforwardDerivedStructureSheaf S)).map
          (tensorHomDiagonalAtPushforwardStructureSheaf S K L) ≫
        (tensorSheafHomAdjunctionAtPushforwardStructureSheaf S).counit.app
          (((derivedTensorProductFunctor S.X.sheaf).obj K).obj L) =
      (tensorMiddleSwapAtPushforwardStructureSheaf S K
            ((derivedSheafHomSitePushforwardStructureSheaf S).obj L)).hom ≫
        ((derivedTensorProductFunctor S.X.sheaf).obj K).map
          ((tensorSheafHomAdjunctionAtPushforwardStructureSheaf S).counit.app L) :=
  Adjunction.tensorHomDiagonal_mate (tensorSheafHomAdjunctionAtPushforwardStructureSheaf S) _

/-- **The adjunction equation determines the diagonal at `Ri_* 𝒪_Z`.** No other morphism of its
type satisfies `tensorHomDiagonalAtPushforwardStructureSheaf_mate`; in particular neither the
zero morphism nor the negative of the diagonal does.

This is the form in which the identification [Stacks, Tag 0E2N] needs is to be discharged: it is
enough to check the displayed equation for
`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal`, transported to these functors. -/
theorem eq_tensorHomDiagonalAtPushforwardStructureSheaf
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))
    {φ : ((derivedTensorProductFunctor S.X.sheaf).obj K).obj
        ((derivedSheafHomSitePushforwardStructureSheaf S).obj L) ⟶
      (derivedSheafHomSitePushforwardStructureSheaf S).obj
        (((derivedTensorProductFunctor S.X.sheaf).obj K).obj L)}
    (hφ : ((derivedTensorProductFunctor S.X.sheaf).obj
            (pushforwardDerivedStructureSheaf S)).map φ ≫
          (tensorSheafHomAdjunctionAtPushforwardStructureSheaf S).counit.app
            (((derivedTensorProductFunctor S.X.sheaf).obj K).obj L) =
        (tensorMiddleSwapAtPushforwardStructureSheaf S K
              ((derivedSheafHomSitePushforwardStructureSheaf S).obj L)).hom ≫
          ((derivedTensorProductFunctor S.X.sheaf).obj K).map
            ((tensorSheafHomAdjunctionAtPushforwardStructureSheaf S).counit.app L)) :
    φ = tensorHomDiagonalAtPushforwardStructureSheaf S K L :=
  Adjunction.eq_tensorHomDiagonal (tensorSheafHomAdjunctionAtPushforwardStructureSheaf S) _ hφ

/-- **The diagonal at `Ri_* 𝒪_Z` is functorial in the target of the internal Hom.** This is
[Stacks, Tag 0BYS]'s functoriality in that variable, for the adjunction-theoretic morphism: it
comes from the naturality of the interchange,
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.middleSwapIso_hom_naturality_right`, and
the naturality of the hom-bijection of the adjunction. -/
theorem tensorHomDiagonalAtPushforwardStructureSheaf_natural_right
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))
    {L L' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))}
    (g : L ⟶ L') :
    ((derivedTensorProductFunctor S.X.sheaf).obj K).map
          ((derivedSheafHomSitePushforwardStructureSheaf S).map g) ≫
        tensorHomDiagonalAtPushforwardStructureSheaf S K L' =
      tensorHomDiagonalAtPushforwardStructureSheaf S K L ≫
        (derivedSheafHomSitePushforwardStructureSheaf S).map
          (((derivedTensorProductFunctor S.X.sheaf).obj K).map g) :=
  Adjunction.tensorHomDiagonal_natural_right
    (tensorSheafHomAdjunctionAtPushforwardStructureSheaf S) g _ _
    ((canonicalDerivedTensorProduct S.X.sheaf).middleSwapIso_hom_naturality_right S.ambientSite
      (pushforwardDerivedStructureSheaf S) K
      ((derivedSheafHomSitePushforwardStructureSheaf S).map g))

end Stacks.Duality.TensorHomTorAmplitude

end
