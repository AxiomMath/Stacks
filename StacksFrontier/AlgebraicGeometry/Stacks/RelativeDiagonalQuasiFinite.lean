module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE

/-!
# The relative diagonal of a representable morphism of stacks (Stacks 04YQ, parts (2) and (5))

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over the big fppf site of `S` which is representable by algebraic spaces. Its
relative diagonal

`Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳`

is representable by algebraic spaces (Stacks 04XS, part (1)), so the relative properties of
Stacks 03YK make sense for it. This file proves **parts (5) and (2) of Stacks 04YQ** for it:
`Δ_f` is locally quasi-finite, and `Δ_f` is locally of finite type.

The source's proof is Morphisms of Spaces, Lemma 0463 applied at every scheme-valued point of
`𝒳 ×_{f, 𝒴, f} 𝒳`: the base change of `Δ_f` there is a monomorphism, which is part (3) of
Stacks 04YQ, and it is locally of finite type, which is part (2); a monomorphism which is
locally of finite type is locally quasi-finite.

## Main definitions

There are no new definitions.

## Main results

The three results below live in `namespace AlgebraicGeometry` and are named relative to it,
because their fully qualified names do not fit on a line.

* `Stack.isLocallyQuasiFinite_relativeDiagonal_of_isRepresentableByAlgebraicSpaces` is
  **Stacks 04YQ, part (5)**.
* `Space.isLocallyQuasiFinite_of_mono_of_presheaf_locallyOfFiniteType` is the locally
  quasi-finite half of **Stacks 0463**: a monomorphism of algebraic spaces whose represented base
  changes are locally of finite type is locally quasi-finite.
* `Stack.isLocallyOfFiniteType_relativeDiagonal_of_isRepresentableByAlgebraicSpaces` is
  **Stacks 04YQ, part (2)**, in the every-étale-chart form the source states it in.

## Implementation notes

The §04XB quantifier is written out longhand, exactly as in
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeDiagonalMonomorphism.lean`, and for the same
reason: `AlgebraicGeometry.Stack.HasRelativeProperty` carries two instance arguments on the
tested property which it does not use, so the longhand form is the same `Prop` with no
hypothesis on the property at all.

`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_mono_of_presheaf_locallyOfFiniteType` takes
local finite type in the represented-base-change form
`CategoryTheory.MorphismProperty.presheaf`, because that is the form in which
`AlgebraicGeometry.Stack.presheaf_locallyOfFiniteType_relativeDiagonal` supplies it, and
concludes in the every-étale-chart form, because that is
`AlgebraicGeometry.Space.IsLocallyQuasiFinite`. The passage between the two forms is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_relative` (**Stacks 03MJ** for a
representable morphism) at the meet
`AlgebraicGeometry.LocallyOfFiniteType ⊓ AlgebraicGeometry.LocallyQuasiFinite`, which is étale
local on the source and target by **Stacks 04R3**, stable under base change because each
conjunct is, and local at the target for the fppf topology of schemes by
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le` from the fpqc form **Stacks 02VI**. At a
represented base change the two scheme-level facts then compose by instance synthesis: a
monomorphism of schemes is universally injective, and a universally injective morphism which is
locally of finite type is locally quasi-finite.

**Which tag asserts local finite type of `Δ_f` for an arbitrary 1-morphism.** It is Stacks
**04XS**, part (2) — *"Let `f : 𝒳 → 𝒴` be a morphism of algebraic stacks. Then (1) `Δ_f` is
representable by algebraic spaces, and (2) `Δ_f` is locally of finite type"* — and it is 04XS's
proof that rests on Stacks **04XR**. Stacks **04YQ** opens *"Let `f : 𝒳 → 𝒴` be a morphism of
algebraic stacks **which is representable by algebraic spaces**"* and asserts all five of its
parts under that hypothesis; its slug is
`stacks-morphisms-lemma-properties-diagonal-representable`, and its own proof of part (2) is
one sentence, *"Also Lemma 04XS guarantees (2) holds"*. So part (2) of 04YQ **is** the
representable case, and that is what carries the part key here, exactly as parts (3), (4) and
(5) do — all four take the same hypothesis the source takes.

The arbitrary-1-morphism form is 04XS part (2), proved from Stacks 04XR as
`AlgebraicGeometry.Stack.isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack` of
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeDiagonalFiniteType.lean`; that is the form a
consumer which drops the representability hypothesis, such as Stacks 04Z0, needs, since
registering 04YQ part (2) does not supply it. Stacks 04YT keeps the hypothesis, so part (2)
here is what its implication (2) implies (3) consumes
(`AlgebraicGeometry.Stack.AlgebraicStacks.isFiniteType_relativeDiagonal_of_isQuasiCompact`).

The proof is read off part (5), the every-chart condition being monotone in the tested property
of scheme morphisms. An independent route to the same content in the `MorphismProperty.presheaf`
shape rather than the chart shape is
`AlgebraicGeometry.Stack.presheaf_locallyOfFiniteType_relativeDiagonal`
(`StacksFrontier/AlgebraicGeometry/Stacks/SeparatedDiagonalTFAE.lean`), which reduces the condition
at each scheme-valued point to part (2) of Stacks 03HK and likewise never uses 04XR; the two are
different `Prop`s and the chart one is the shape this tag's part keys are stated in.

**Part (1) of Stacks 04YQ is not proved here**, and is not proved anywhere in this library: it
needs Stacks **03XX** (a separated, locally quasi-finite algebraic space over a scheme is a
scheme), which is not available.

`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_mono_of_presheaf_locallyOfFiniteType` is one
half of a Chapter 67 lemma, proved here untagged, like
`AlgebraicGeometry.Space.isSeparated_of_mono` (Stacks 042N, proved for part (4) of this same
tag): it is a theorem, it coins no notion, and it is stated over this library's own
vocabulary. Stacks 0463 asserts that such a morphism is **both** locally quasi-finite **and**
separated, so one half is not its covering set and no tag is claimed here. The same half with
local finite type taken in the every-étale-chart form instead is
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_mono`, which is where the Stacks 0463 part key
sits; the two differ in the form of the hypothesis, and this one is the form
`AlgebraicGeometry.Stack.presheaf_locallyOfFiniteType_relativeDiagonal` supplies.

## References

* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03XX](https://stacks.math.columbia.edu/tag/03XX)
* [Stacks Project, Tag 04XR](https://stacks.math.columbia.edu/tag/04XR)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace Space

/-- **Stacks 0463, the locally quasi-finite half.** A monomorphism of algebraic spaces over `S`
all of whose represented base changes are locally of finite type is locally quasi-finite.

The hypothesis is local finite type in the represented-base-change form
`CategoryTheory.MorphismProperty.presheaf`; the same half with it in the every-étale-chart form
is `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_mono`, which is where the Stacks 0463 part
key sits.

Untagged: Stacks 0463 asserts that such a morphism is both locally quasi-finite and separated,
so this is one half of a Chapter 67 lemma rather than its covering set. It is proved here
because part (5) of Stacks 04YQ consumes it, like
`AlgebraicGeometry.Space.isSeparated_of_mono`. -/
theorem isLocallyQuasiFinite_of_mono_of_presheaf_locallyOfFiniteType
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (g : F ⟶ G) (hmono : Mono g)
    (hft : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    IsLocallyQuasiFinite B S hS g := by
  have _ : MorphismProperty.IsLocalAtTarget
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        @AlgebraicGeometry.LocallyQuasiFinite.{u}) Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have _ : MorphismProperty.IsStableUnderBaseChange
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        @AlgebraicGeometry.LocallyQuasiFinite.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have := hmono
  refine (holdsOnEveryEtaleChart_iff_relative B S hS _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    hF hG g hft.1).2 ⟨hft.1, ?_⟩
  intro a b h fst snd hpb
  have hlft : AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map snd) := hft.2 h fst snd hpb
  have _ : Mono snd := yoneda.mono_of_mono_map hpb.mono_snd_of_mono
  have _ : Mono ((BigFppfOver.toScheme B S hS).map snd) := inferInstance
  exact ⟨hlft, inferInstance⟩

end Space

namespace Stack

universe t

variable {𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)

include hf

/-- **Stacks 04YQ, part (5).** The relative diagonal of a 1-morphism of algebraic stacks over
the big fppf site of `S` which is representable by algebraic spaces is locally quasi-finite: it
is representable by algebraic spaces, and every algebraic space representing one of its base
changes along a scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` has locally quasi-finite structural
morphism.

That structural morphism is a monomorphism by part (3) and its represented base changes are
locally of finite type by part (2) for a representable 1-morphism
(`AlgebraicGeometry.Stack.presheaf_locallyOfFiniteType_relativeDiagonal`), so Stacks 0463
applies. -/
@[stacks 04YQ "part (5): locally quasi-finite"]
theorem isLocallyQuasiFinite_relativeDiagonal_of_isRepresentableByAlgebraicSpaces :
    ∃ _hΔ : IsRepresentableByAlgebraicSpaces B S hS
        (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom),
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
        (_hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p
          = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
            (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom).toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsLocallyQuasiFinite B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  refine ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f, ?_⟩
  intro U y hy F hF hE
  exact Space.isLocallyQuasiFinite_of_mono_of_presheaf_locallyOfFiniteType B S hS
    ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
    (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) _
    (mono_hom_algebraicSpaceMap_of_subsingleton B S hS U F hF
      (subsingleton_representing_of_relativeDiagonal B S hS 𝒳.val 𝒴.val f.hom hf U y hy F hE))
    (presheaf_locallyOfFiniteType_relativeDiagonal B S hS f hf U y hy F hF hE)

/-- **Stacks 04YQ, part (2).** The relative diagonal of a 1-morphism of algebraic stacks over
the big fppf site of `S` which is representable by algebraic spaces is locally of finite type:
it is representable by algebraic spaces, and every algebraic space representing one of its base
changes along a scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` has locally-of-finite-type structural
morphism — the every-étale-chart form of part (1) of Stacks 03XF.

This is read off part (5), the every-chart condition being monotone in the tested property of
scheme morphisms, local finite type being the first conjunct of the meet part (5) is proved at.

The hypothesis is the source's own: Stacks 04YQ asserts all five parts for a 1-morphism
representable by algebraic spaces. The statement asserted for an *arbitrary* 1-morphism of
algebraic stacks is part (2) of **Stacks 04XS**, which rests on Stacks 04XR and is proved in
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeDiagonalFiniteType.lean`; see the implementation
notes. -/
@[stacks 04YQ "part (2): locally of finite type"]
theorem isLocallyOfFiniteType_relativeDiagonal_of_isRepresentableByAlgebraicSpaces :
    ∃ _hΔ : IsRepresentableByAlgebraicSpaces B S hS
        (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom),
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
        (_hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p
          = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
            (relativeDiagonalBasedFunctor B S hS 𝒳.val 𝒴.val f.hom.hom).toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsLocallyOfFiniteType B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
  ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f,
    fun U y hy F hF hE =>
      Space.holdsOnEveryEtaleChart_mono B S hS (fun _ h => h.1)
        ((isLocallyQuasiFinite_relativeDiagonal_of_isRepresentableByAlgebraicSpaces
          B S hS f hf).2 U y hy F hF hE)⟩

end Stack

end AlgebraicGeometry

end
