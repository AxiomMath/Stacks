module

public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.QuasiProjective
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.AmpleClosedImmersion.Converse
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0BDE: quasi-projectivity descends along a field extension

Stacks Tag 0BDE says that if `X` is a scheme over a field `k` and `X_K` is quasi-projective over
`K` for some field extension `K/k`, then `X` is quasi-projective over `k`.

The source's proof has exactly four steps, and three of them are discharged here with no
hypothesis at all. The fourth is **Stacks Tag 0BDC** — an ample invertible sheaf on `X_K`
descends to one on `X` — which is named as the single hypothesis
`Stacks.QuasiProjectiveFieldDescent.AmpleFieldDescent`.

## Why the statement is phrased over library names

**The registered statement of Tag 0BDE rests on an unproved result, so no proof of it can have
clean axioms.** The chain, declaration by declaration:

* Tag 0BDE's `isQuasiProjective_of_fieldExtension` is stated with Tag 01VW's
  `IsQuasiProjective`, a transparent `abbrev`;
* which unfolds to Tag 01VH's `IsRelativelyAmple`;
* whose body mentions Tag 01PS's `IsAmple`;
* whose body mentions Tag 01CY's `nonvanishingOpen`;
* which is *defined* by `⟨nonvanishingLocus X L s, isOpen_nonvanishingLocus X L s⟩`, and
  Tag 01CY's `isOpen_nonvanishingLocus` has no proof.

So `sorryAx` occurs in the *statement*, and `#print axioms` on any proof of that theorem —
however complete — contains it. The same defect arises for Tag 087S, and the remedy is the
same: restate over library names.

The library-name statement of quasi-projectivity is `Stacks.HProjective.IsQuasiProjective`
(`../HProjective/QuasiProjective.lean`), which is Tag 01VW's `IsQuasiProjective` with
Tag 01VH's `IsRelativelyAmple` replaced by `Stacks.RelativeAmple.IsRelativelyAmple` and the
Tag 01CS class by `Stacks.Ample.IsInvertibleModule`. Nothing else is changed: the base-change
morphism, the field extension and the direction of the implication are those of the tag.

## The three steps that cost nothing

Both schemes sit over *affine* bases, which is what makes the ample half of quasi-projectivity
reduce to absolute ampleness: `Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple` is an
unconditional equivalence over an affine base, and it is applied twice — once at `Spec K` to turn
the hypothesis into absolute ampleness on `X_K`, and once at `Spec k` to turn the conclusion of
Tag 0BDC back into relative ampleness. So Tag 0BDC is needed in its *absolute* form, which is
how the source states it.

* **Locally of finite type** is Algebra Lemma 10.126.1 ([Stacks, Tag 00QP]) in the source. It is
  in pinned Mathlib in geometric form:
  `AlgebraicGeometry.instDescendsAlongLocallyOfFiniteTypeInfSurjectiveFlatQuasiCompact`
  (`Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean:35`), the instance
  `DescendsAlong @LocallyOfFiniteType (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`. The three
  properties of `Spec K ⟶ Spec k` are
  `Stacks.QuasiProjectiveFieldDescent.faithfullyFlat_extensionMap` and the quasi-compactness
  instance for a morphism of affine schemes.
* **Quasi-compactness** is proved topologically rather than by descent, there being no
  `DescendsAlong @QuasiCompact` instance at this pin: over an affine base quasi-compactness of
  the morphism is compactness of the source (`quasiCompact_iff_compactSpace`), `X_K ⟶ X` is
  surjective because `Spec K ⟶ Spec k` is and surjectivity is stable under base change, and a
  continuous surjection out of a compact space has compact target.
* **The passage between relative and absolute ampleness** is Tag 01VK, as above.

## Main definitions

* `Stacks.QuasiProjectiveFieldDescent.extensionMap`: the morphism `Spec K ⟶ Spec k` of a field
extension.
* `Stacks.QuasiProjectiveFieldDescent.HasAmpleModule`: a scheme carries an ample invertible module.
* `Stacks.QuasiProjectiveFieldDescent.AmpleFieldDescent`: **Stacks Tag 0BDC**, the single named
hypothesis.

## Main results

* `Stacks.QuasiProjectiveFieldDescent.faithfullyFlat_extensionMap`: `Spec K ⟶ Spec k` is
  surjective, flat and quasi-compact.
* `Stacks.QuasiProjectiveFieldDescent.locallyOfFiniteType_of_baseChange`: **the finite-type step,
unconditional.**
* `Stacks.AmpleClosedImmersion.compactSpace_of_surjective`: a continuous surjection of
  schemes out of a compact source has compact target.
* `Stacks.QuasiProjectiveFieldDescent.quasiCompact_of_baseChange`: **the quasi-compactness step,
unconditional.**
* `Stacks.QuasiProjectiveFieldDescent.hasAmpleModule_of_isQuasiProjective_of_isAffine` and
  `Stacks.QuasiProjectiveFieldDescent.isQuasiProjective_of_hasAmpleModule_of_isAffine`: the two
  uses of Tag 01VK.
* `Stacks.QuasiProjectiveFieldDescent.isQuasiProjective_of_fieldExtension`: **Stacks Tag 0BDE**,
  from `Stacks.QuasiProjectiveFieldDescent.AmpleFieldDescent` alone.

## Which tags the argument needs

A proof of Tag 0BDE through the registered statements of the neighbouring tags uses three of them:

* Tag 01VT's `ample_relativeVeryAmple_projectiveSpace_tfae`, **only at `.out 2 1` and
  `.out 1 2`** — that is, only the equivalence of conditions (1) and (2) of Tag 01VT, which is
  Stacks Tag 01VK and is **unconditional** in this repository as
  `Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`. So Tag 0BDE needs nothing more
  of Tag 01VT than this clause. The two uses below are the same two.
* Tag 0BDC's `exists_ample_of_fieldExtension`, which is not proved — the genuine gap, which is
  `Stacks.QuasiProjectiveFieldDescent.AmpleFieldDescent` here;
* Tag 09MW's `isAmple_pullback_iff_of_isClosedImmersion_of_isHomeomorph`, not proved either,
  **purely to fix the orientation of a fibre product**: Tag 0BDC is stated about
  `pullback (Spec K ⟶ Spec k) f` while Tag 01VW base-changes along
  `pullback.snd f (Spec K ⟶ Spec k)`, so that route transports ampleness across
  `pullbackSymmetry` and needs a tag to do it.

`Stacks.QuasiProjectiveFieldDescent.AmpleFieldDescent` states Tag 0BDC in the orientation Tag 0BDE
actually base-changes in, so **the Tag 09MW detour disappears and the gap count drops from two to
one.** Neither Tag 0BDC nor Tag 09MW carries a Stacks tag attribute anywhere in this repository.

## What is not done, and how much of Tag 0BDC is reachable

`Stacks.QuasiProjectiveFieldDescent.AmpleFieldDescent` is Stacks Tag 0BDC and nothing more; it is
not equivalent to the conclusion below, being a statement about absolute ampleness with no morphism
to a base in it. Its own four inputs, as the source uses them:

* [Stacks, Tag 0B8W] — on a quasi-compact quasi-separated scheme, an invertible module on a
  cofiltered limit of base changes descends to a finite stage — and [Stacks, Tag 09MT], that the
  stage may be enlarged so that it descends *amply*. Neither has any realisation in this
  repository or in pinned Mathlib: no declaration mentioning `IsAmple` and a
  limit of schemes together exists outside `../AmpleEventualGeneration/`,
  `../HighTwistDevissage/` and `../AmpleFiniteSurjective/`, none of which is about base
  change.
* [Stacks, Tag 0BD4] — ampleness descends along a finite locally free morphism. **This is the
  substantive gap.** No file in this repository mentions finite local freeness and `IsAmple`
  together.
* [Stacks, Tag 00FV], the Hilbert Nullstellensatz, is in pinned Mathlib
  (`Mathlib/RingTheory/Nullstellensatz.lean`, `Mathlib/RingTheory/Jacobson/Ring.lean`).
* [Stacks, Tag 01PU] — ampleness restricts to a closed subscheme — is *available*, in the
  stronger form `Stacks.SectionExtension.isAmple_pullbackModule`, ampleness along a
  quasi-compact immersion.

**No Stacks Tag 0BDE attribute is attached.** The single unlabelled assertion of Tag 0BDE is
the whole theorem, so there is no partial label; and
`Stacks.QuasiProjectiveFieldDescent.isQuasiProjective_of_fieldExtension` carries
`AmpleFieldDescent`, a hypothesis the tag lacks. That alone rules out the attribute, apart from
the fact that the registered statement of the tag depends on an unproved result.

## References

* [Stacks Project, Tag 0BDE](https://stacks.math.columbia.edu/tag/0BDE)
* [Stacks Project, Tag 0BDC](https://stacks.math.columbia.edu/tag/0BDC)
* [Stacks Project, Tag 00QP](https://stacks.math.columbia.edu/tag/00QP)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 01VW](https://stacks.math.columbia.edu/tag/01VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.QuasiProjectiveFieldDescent

/-! ### The morphism of spectra of a field extension -/

/-- The morphism `Spec K ⟶ Spec k` induced by a field extension `K/k`. This is the morphism the
statement of Tag 0BDE base-changes along. -/
def extensionMap (k K : Type u) [Field k] [Field K] [Algebra k K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- **The morphism of spectra of a field extension is surjective, flat and quasi-compact**, which
is the hypothesis of Mathlib's fpqc descent instance for `LocallyOfFiniteType`.

Faithful flatness is `RingHom.faithfullyFlat_algebraMap_iff` together with Mathlib's instance
making a nontrivial free module faithfully flat — `K` is a `k`-vector space — and
`AlgebraicGeometry.flat_and_surjective_SpecMap_iff` turns it into the two geometric properties at
once. Quasi-compactness is automatic for a morphism of affine schemes. -/
@[ega "IV 2.7.3" "(iii)",
  ega "IV 4.4.1" "partial",
  ega "IV 8.1.2" "partial",
  ega "IV 9.1.3" "more general"]
theorem faithfullyFlat_extensionMap :
    Surjective (extensionMap k K) ∧ Flat (extensionMap k K) ∧
      QuasiCompact (extensionMap k K) :=
  have h := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k K))).mpr
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  ⟨h.2, h.1, inferInstance⟩

/-! ### The finite-type step -/

/-- **Locally-of-finite-type descends along a field extension**, unconditionally. This is the
source's appeal to Algebra Lemma 10.126.1 ([Stacks, Tag 00QP]), supplied geometrically by pinned
Mathlib's instance `DescendsAlong @LocallyOfFiniteType (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`
(`Mathlib/AlgebraicGeometry/Morphisms/LocalFlatDescent.lean:35`), whose hypothesis at
`Spec K ⟶ Spec k` is `Stacks.QuasiProjectiveFieldDescent.faithfullyFlat_extensionMap`. -/
theorem locallyOfFiniteType_of_baseChange {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (h : LocallyOfFiniteType (pullback.snd f (extensionMap k K))) :
    LocallyOfFiniteType f := by
  refine MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @LocallyOfFiniteType) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ?_ h
  obtain ⟨hs, hfl, hqc⟩ := faithfullyFlat_extensionMap k K
  exact ⟨⟨hs, hfl⟩, hqc⟩

/-! ### The quasi-compactness step -/

/-- **Quasi-compactness descends along a field extension**, unconditionally.

There is no `DescendsAlong @QuasiCompact` instance at this pin, so the step is taken
topologically: both bases are affine, so `AlgebraicGeometry.quasiCompact_iff_compactSpace` turns
quasi-compactness of each morphism into compactness of its source, and `X_K ⟶ X` is surjective
because `Spec K ⟶ Spec k` is and `@Surjective` is stable under base change. -/
@[ega "IV 1.1.4" "special case"]
theorem quasiCompact_of_baseChange {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (h : QuasiCompact (pullback.snd f (extensionMap k K))) : QuasiCompact f := by
  obtain ⟨hs, -, -⟩ := faithfullyFlat_extensionMap k K
  have := hs
  have hfst : Surjective (pullback.fst f (extensionMap k K)) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback f (extensionMap k K)).flip ‹_›
  refine (quasiCompact_iff_compactSpace f).mpr ?_
  exact Stacks.AmpleClosedImmersion.compactSpace_of_surjective
    (pullback.fst f (extensionMap k K)) hfst
    ((quasiCompact_iff_compactSpace (pullback.snd f (extensionMap k K))).mp h)

/-! ### Stacks Tag 0BDC as a named hypothesis -/

/-- **A scheme carries an ample invertible module.** This is the conclusion of Stacks Tag 01PS
existentially quantified over the module, which is the shape both halves of Stacks Tag 0BDC are
stated in. -/
def HasAmpleModule (X : Scheme.{u}) : Prop :=
  ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
    letI : Stacks.Ample.IsInvertibleModule X L := hL
    Stacks.Ample.IsAmple X L

/-- **A relatively ample module is an ample module.** Recorded so that
`Stacks.QuasiProjectiveFieldDescent.HasAmpleModule` is visibly not vacuous: it holds of any affine
scheme, because `Stacks.RelativeAmple.isRelativelyAmple_unitModule_id` makes `𝒪_X` relatively ample
for the identity and Tag 01VK converts. -/
theorem hasAmpleModule_of_isAffine (X : Scheme.{u}) [IsAffine X] : HasAmpleModule X :=
  ⟨Stacks.Ample.unitModule X, inferInstance,
    (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple (𝟙 X) _).mp
      (Stacks.RelativeAmple.isRelativelyAmple_unitModule_id X)⟩

/-- **Stacks Tag 0BDC, as a named hypothesis**: if the base change of a scheme over a field along
a field extension carries an ample invertible module, then so does the scheme.

This is the one input of `Stacks.QuasiProjectiveFieldDescent.isQuasiProjective_of_fieldExtension`,
and it is stated about absolute ampleness with no morphism to a base, exactly as the source states
it — so it is not a restatement of the conclusion. Its own inputs, and which of them are reachable
here, are listed in the module documentation. -/
def AmpleFieldDescent : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)),
      HasAmpleModule (pullback f (extensionMap k K)) → HasAmpleModule X

/-! ### The two uses of Stacks Tag 01VK -/

/-- **Over an affine base, a quasi-projective morphism has an ample source.** The relatively ample
invertible module of quasi-projectivity is absolutely ample by Stacks Tag 01VK,
`Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple`, which is unconditional. -/
theorem hasAmpleModule_of_isQuasiProjective_of_isAffine {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) (h : Stacks.HProjective.IsQuasiProjective f) : HasAmpleModule X := by
  obtain ⟨-, L, hLinv, hLamp⟩ := h
  have := hLinv
  exact ⟨L, hLinv, (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).mp hLamp⟩

/-- **Over an affine base, a finite-type morphism with an ample source is quasi-projective.** The
converse direction of Stacks Tag 01VK, again unconditional. -/
theorem isQuasiProjective_of_hasAmpleModule_of_isAffine {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) (hft : LocallyOfFiniteType f) (hqc : QuasiCompact f) (h : HasAmpleModule X) :
    Stacks.HProjective.IsQuasiProjective f := by
  obtain ⟨L, hLinv, hLamp⟩ := h
  have := hLinv
  exact
    ⟨⟨hft, hqc⟩, L, hLinv, (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple f L).mpr
      hLamp⟩

/-! ### Stacks Tag 0BDE -/

/-- **Stacks Tag 0BDE: quasi-projectivity descends along a field extension.** If the base change
of `f : X ⟶ Spec k` along `Spec K ⟶ Spec k` is quasi-projective, then `f` is quasi-projective.

The single hypothesis is `Stacks.QuasiProjectiveFieldDescent.AmpleFieldDescent`, which is Stacks
Tag 0BDC. The three remaining steps of the source's proof are unconditional:
`Stacks.QuasiProjectiveFieldDescent.locallyOfFiniteType_of_baseChange`,
`Stacks.QuasiProjectiveFieldDescent.quasiCompact_of_baseChange`, and the two applications of Stacks
Tag 01VK that move between relative and absolute ampleness over the two affine bases.

Quasi-projectivity is `Stacks.HProjective.IsQuasiProjective`, the library-name form of
Tag 01VW's `IsQuasiProjective`; the registered statement of the tag depends on an unproved result
and cannot be proved with clean axioms, as the module documentation records declaration by
declaration.

**No Stacks Tag 0BDE attribute is attached**: this theorem carries a hypothesis the tag lacks. -/
theorem isQuasiProjective_of_fieldExtension (hdesc : AmpleFieldDescent.{u})
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (h : Stacks.HProjective.IsQuasiProjective (pullback.snd f (extensionMap k K))) :
    Stacks.HProjective.IsQuasiProjective f := by
  refine isQuasiProjective_of_hasAmpleModule_of_isAffine f
    (locallyOfFiniteType_of_baseChange k K f h.1.1)
    (quasiCompact_of_baseChange k K f h.1.2) ?_
  exact hdesc k K X f
    (hasAmpleModule_of_isQuasiProjective_of_isAffine
      (pullback.snd f (extensionMap k K)) h)

end Stacks.QuasiProjectiveFieldDescent

end
