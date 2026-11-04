module

public import StacksFrontier.AlgebraicGeometry.BaseChange.SheafHomFlatPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPushforwardBaseChange
import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the derived pushforward of a derived internal hom into a finitely presented
complex

Let `f : X ⟶ S` be a morphism of schemes of finite presentation, let `E` be a perfect object of
`D(𝒪_X)` and let `𝒢^•` be a bounded complex of finitely presented `𝒪_X`-modules, flat over `S`,
with support proper over `S`. [Stacks, Tag 0A1J] asserts two things about
`K = Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•)`: that `K` is a perfect object of `D(𝒪_S)`, and that its formation
commutes with arbitrary base change.

**This file proves the base-change half only.** Its precise statement is the one the source's
own proof points at — "the statement on base change is Lemma 08IE" — namely that for every
cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

the canonical map

`Lg^*Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•) ⟶ Rf'_*R𝓗om_{𝒪_{X'}}(L(g')^*E, (g')^*𝒢^•)`

is an isomorphism, with the **ordinary** pullback `(g')^*𝒢^•` on the right — the source sets
that in bold, and `AlgebraicGeometry.sheafHomFlatBaseChangeMap` keeps it.

## Main results

* `AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_finitePresentation` is the base-change
  half of [Stacks, Tag 0A1J].

## Implementation notes

**What this adds to [Stacks, Tag 08IE].**
`AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_perfect`, which is case (1) of that tag,
asks for four things about the data that [Stacks, Tag 0A1J]'s hypotheses do not state in that
form. All four are discharged here:

* quasi-compactness and quasi-separatedness of `f`, from `AlgebraicGeometry.FinitePresentation`
  ([Stacks, Tag 01TP] part (3)) by its own projections;
* the commutativity `g' ≫ f = f' ≫ g` of the square, from the cartesian square itself;
* boundedness above of `𝒢^•` in the sense of `CochainComplex.minus`, from the two-sided
  boundedness [Stacks, Tag 0A1J] asks for;
* quasi-coherence of the terms of `𝒢^•`, from finite presentation of the terms by
  [Stacks, Tag 01BW].

The four conditions on `𝒢^•` are packaged as
`AlgebraicGeometry.FlatProperSupportFinitelyPresented`, the hypothesis of [Stacks, Tag 0A1H]
and of [Stacks, Tag 0A1J] alike — the two tags state the same hypotheses and differ only in
whether the pushforward is of a derived tensor product or of a derived internal hom.

Unlike the tensor-product case, the perfectness hypothesis on `E` is stated here as the source
states it: `Stacks.Cohomology.PerfectComplexes.IsPerfect` is the predicate
`AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_perfect` is written at, and it is
available on `DerivedCategory X.Modules`, the category the base-change map of
[Stacks, Tag 08HY] lives on. So no weaker stand-in for it is needed; compare the `hE` of
`AlgebraicGeometry.isIso_tensorFlatBaseChangeMap_of_finitePresentation`, which has to replace
perfectness by quasi-coherence of the cohomology because
`AlgebraicGeometry.isIso_tensorFlatBaseChangeMap` is written at a perfectness predicate for a
different spelling of the category of `𝒪_X`-modules.

**What is still carried** as explicitly named hypotheses:

* `hK` and `hK'` — quasi-coherence of the cohomology of the two derived internal homs, which
  [Stacks, Tag 0DJ9] asks of its complexes, carried in this library at a spelling of the
  derived internal hom that does not line up with the one the comparison map is written at.

The three steps of the source proof of [Stacks, Tag 08IE] are no longer assumed here:
`AlgebraicGeometry.isIso_sheafHomFlatBaseChangeMap_of_perfect` proves case (1) of that tag
outright, from [Stacks, Tag 0DJ9], conclusion (2) of [Stacks, Tag 0DJA] and the stalk check of
the proof of [Stacks, Tag 0A1D].

**Why the perfection half is absent.** The result this library has for it is
`Stacks.Cohomology.PerfectInternalHomPushforward.isPerfect_derivedPushforward_derivedSheafHom`,
[Stacks, Tag 0DJR], and it assumes `AlgebraicGeometry.IsNoetherian S` and
`AlgebraicGeometry.LocallyOfFiniteType f` together with coherence of the terms of `𝒢^•`.
[Stacks, Tag 0A1J] assumes none of those: its base is arbitrary and its `𝒢^•` is only finitely
presented. The source closes that gap by writing `S` as a limit of a directed system of affine
schemes of finite type over `ℤ`, descending `X`, `E` and `𝒢^•` to a finite stage
([Stacks, Tag 01ZM], [Stacks, Tag 01ZR], [Stacks, Tag 05LY], [Stacks, Tag 081G],
[Stacks, Tag 09RF]), applying [Stacks, Tag 0DJR] over the Noetherian stage and transporting the
conclusion back along the base change — that is, using the half proved here. None of that
descent is assembled in this library, so no statement of the perfection half is given; a
hypothesis standing in for it would be the conclusion itself. This is the same obstruction the
module documentation of
`StacksFrontier/AlgebraicGeometry/Perfect/TensorFinitelyPresentedPushforwardBaseChange.lean`
records for [Stacks, Tag 0A1H].

## References

* [Stacks Project, Tag 0A1J](https://stacks.math.columbia.edu/tag/0A1J)
* [Stacks Project, Tag 08IE](https://stacks.math.columbia.edu/tag/08IE)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0DJR](https://stacks.math.columbia.edu/tag/0DJR)
* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.SheafOfModules (derivedSheafHom)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback

/-! ### The base-change half of Stacks 0A1J -/

/-- **[Stacks, Tag 0A1J], the base-change half of the conclusion.** Let `f : X ⟶ S` be a
morphism of schemes of finite presentation, let `E` be a perfect object of `D(𝒪_X)` and let
`𝒢^•` be a bounded complex of finitely presented `𝒪_X`-modules, flat over `S`, with support
proper over `S`. For every cartesian base-change square the canonical map

`Lg^*Rf_*R𝓗om_{𝒪_X}(E, 𝒢^•) ⟶ Rf'_*R𝓗om_{𝒪_{X'}}(L(g')^*E, (g')^*𝒢^•)`

of `AlgebraicGeometry.sheafHomFlatBaseChangeMap` is an isomorphism — note the ordinary pullback
of `𝒢^•` on the right, as the source's boldface demands.

The perfection half of [Stacks, Tag 0A1J] is not proved; the implementation notes of this file
say what it would need.

The proof is the reduction the source performs: finite presentation of `f` supplies the
quasi-compactness and quasi-separatedness that case (1) of [Stacks, Tag 08IE] asks for, and the
four conditions of `AlgebraicGeometry.FlatProperSupportFinitelyPresented` supply boundedness
above of `𝒢^•` and quasi-coherence and relative flatness of its terms. The source's
proper-support hypothesis on `𝒢^•` is part of that bundle and is not used by this half: the
base-change argument does not appeal to it, and it is kept so that the hypothesis bundle is the
one [Stacks, Tag 0A1J] states. -/
@[stacks 0A1J "the base-change half of the conclusion ONLY, for the canonical map \
sheafHomFlatBaseChangeMap of Stacks 08IE, with the ORDINARY pullback (g')^*𝒢^• on the right as the \
source's boldface demands. The perfection half -- that K is a perfect object of D(O_S) -- is NOT \
proved and is not stated: the library's result for it is Tag 0DJR, which assumes a Noetherian \
base, a locally-of-finite-type f and coherent terms, none of which Tag 0A1J grants, and the source \
closes that gap by a limit descent (Tags 01ZM, 01ZR, 05LY, 081G, 09RF) to a Noetherian stage that \
is not assembled in this library. Of what Tag 08IE case (1) asks beyond Tag 0A1J's hypotheses, all \
four are discharged here: quasi-compactness and quasi-separatedness of f from Tag 01TP part (3), \
commutativity of the square from the cartesian square, boundedness above of the complex from its \
two-sided boundedness, and quasi-coherence of its terms from their finite presentation by Tag \
01BW. The perfectness of E is the source's own hypothesis, stated at the predicate Tag 08IE is \
written at, not a weaker stand-in. The three steps of the source proof of Tag 08IE are not \
assumed: Tag 08IE case (1) is proved outright in this library. What remains among this statement's \
own conditions is hK and hK', the quasi-coherence of the cohomology of the two derived internal \
homs, which Tag 0DJ9 asks of its complexes and which this library has at a spelling of the derived \
internal hom that does not line up with the one the comparison map is written at. The \
proper-support hypothesis on the complex is carried in the bundle and is not used by this half, \
the source's base-change argument not appealing to it"]
public theorem isIso_sheafHomFlatBaseChangeMap_of_finitePresentation
    {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g)
    (sq : g'.toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      f'.toLRSHom.toShHom ≫ g.toLRSHom.toShHom)
    (hf : FinitePresentation f)
    (E : DerivedCategory X.Modules)
    (hEperfect : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ)
    (hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      FlatProperSupportFinitelyPresented f G)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj
      (((derivedSheafHom X.sheaf).obj (op E)).obj
        (DerivedCategory.Q.obj G))).IsQuasicoherent)
    (hK' : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X'.Modules n).obj
      (((derivedSheafHom X'.sheaf).obj
          (op ((derivedPullback g'.toLRSHom.toShHom).obj E))).obj
        (DerivedCategory.Q.obj
          ((pullbackComplex g'.toLRSHom.toShHom).obj G)))).IsQuasicoherent) :
    IsIso (sheafHomFlatBaseChangeMap f g f' g' sq E G) :=
  letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  isIso_sheafHomFlatBaseChangeMap_of_perfect f g f' g' hsq
    hf.quasiCompact hf.quasiSeparated hsq.w sq E hEperfect G hG.minus hG.isQuasicoherent
    hG.isFlatOver hK hK'

end AlgebraicGeometry

end
