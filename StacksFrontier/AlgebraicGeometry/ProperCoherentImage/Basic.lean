module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Locality
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal

/-!
# Coherence of proper higher direct images reduces to an affine base

[Stacks, Tag 02O5] asserts that for a proper morphism `f : X ⟶ S` to a locally Noetherian
scheme and a coherent `𝒪_X`-module `F`, every higher direct image `R ⁱ f_* F` is coherent, and
that the ordinary direct image `f_* F` is coherent. Neither assertion is proved here.

What is proved here is that **the whole of the first assertion is equivalent to its special
case in which the base is affine**, and that the second assertion follows from that same
special case. The source's proof opens with exactly this step — "the assertion is local on `S`,
so we may assume `S` affine Noetherian" — and this file discharges it completely, with no
hypothesis left over.

That is a reduction of [Stacks, Tag 02O5] to **one** named statement,
`HigherDirectImageIsCoherentOverAffineBase`, and the reduction is lossless: the two Props are
proved *equivalent*, not merely one-way implied, so nothing about the general case is being
given away by restricting to an affine base.

## Main definitions

* `AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherent`: the first assertion of
  [Stacks, Tag 02O5], as a `Prop`.
* `AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`: the same
  assertion restricted to an affine base.

## Main results

* `AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_of_cover`: coherence of a
  higher direct image is local on the base, with **no** hypothesis owed. This is the
  `hglue`-free form of
  `AlgebraicGeometry.ProjectiveCoherentImage.isCoherent_higherDirectImage_of_cover`.
* `AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_of_locallyProjective`:
  [Stacks, Tag 02O4] reduced to its projective case, with the same two locality hypotheses
  discharged, so that its only remaining input is the projective case itself.
* `AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherent_iff_overAffineBase`:
  [Stacks, Tag 02O5]'s first assertion holds in general if and only if it holds over an affine
  base.
* `AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_of_isProper` and
  `isCoherent_pushforward_of_isProper`: the two assertions of Tag 02O5 verbatim, each taking the
  affine-base case as its single hypothesis.

## Implementation notes

**Which coherence predicate.** This file is about the root `SheafOfModules.IsCoherent` of
Stacks Tag 01BW, which is what `F.IsCoherent` means for `F : X.Modules`
with `X : Scheme.{u}` — not the separate constant `Stacks.SheafOfModules.IsCoherent` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Coherent.lean`. The two are distinct constants
with the same two fields, bridged by
`AlgebraicGeometry.CoherentAbelian.isCoherent_iff_stacksIsCoherent`. The namespace here
deliberately avoids a `Stacks.` prefix: inside one, `SheafOfModules.IsCoherent` resolves to the
other constant, and the statements below would silently become statements about it.

**The gluing hypothesis is no longer owed.**
`AlgebraicGeometry.ProjectiveCoherentImage.isCoherent_higherDirectImage_of_cover` takes the two
halves of "coherence of a sheaf of modules on a scheme is local on the scheme" as explicit
hypotheses `hglue` and `hres`, and its module documentation names them as missing declarations
that belong in a new file `StacksFrontier/AlgebraicGeometry/Modules/CoherentLocal.lean`. That file
now exists and proves both, for this same root predicate and in this same `restrictFunctor`
spelling: `AlgebraicGeometry.Modules.isCoherent_restrict` and
`AlgebraicGeometry.Modules.isCoherent_of_restrict`. So the hypotheses are discharged here rather
than propagated, and no statement below carries a locality assumption.

**Why an affine base and not `Spec R`.** `IsAffine S` is the hypothesis the locality step
delivers, because the cover used is `S.affineOpens` and an affine open is by definition an open
whose associated scheme is affine. Sharpening it to `S = Spec R` for a Noetherian ring `R` would
need the whole configuration transported along `S ≅ Spec Γ(S, ⊤)`, which buys nothing: local
Noetherianness of an affine scheme is already Noetherianness of its ring of global sections, by
`AlgebraicGeometry.isLocallyNoetherian_Spec`.

**No tag is attached, and none is earned.** Both assertions of Tag 02O5 — the "higher direct
images" assertion and the "ordinary direct image" assertion — are unconditional, and every
declaration below that states one of them carries the affine-base case as a hypothesis the tag
does not have. A labelled assertion may not carry a hypothesis the tag lacks, so attaching
either label here would record as proved something that is not. The docstrings point at
[Stacks, Tag 02O5] instead.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProperCoherentImage

attribute [local instance] HasDerivedCategory.standard

/-- **Coherence of a higher direct image is local on the base.** Let `V` be a family of opens
covering `S`. If for every member the `p`-th higher direct image along `f ∣_ V i` of the
restriction of `F` is coherent, then the `p`-th higher direct image of `F` along `f` is coherent.

This is `AlgebraicGeometry.ProjectiveCoherentImage.isCoherent_higherDirectImage_of_cover` with
its gluing hypothesis discharged by `AlgebraicGeometry.Modules.isCoherent_of_restrict`. No
hypothesis on `f`, on `F` or on the base is used. -/
theorem isCoherent_higherDirectImage_of_cover {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (p : ℕ) {I : Type u} (V : I → S.Opens) (hV : iSup V = ⊤)
    (h : ∀ i, (((Scheme.Modules.pushforward (f ∣_ V i)).rightDerivedPlus (p : ℤ)).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V i).ι).obj F)).IsCoherent) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F).IsCoherent :=
  ProjectiveCoherentImage.isCoherent_higherDirectImage_of_cover f F p V hV
    (fun _ M _ W hW hh => Modules.isCoherent_of_restrict M W hW hh) h

/-- **[Stacks, Tag 02O4] reduced to its projective case, with locality discharged.** This is
`AlgebraicGeometry.ProjectiveCoherentImage.isCoherent_higherDirectImage_of_locallyProjective`
with its two locality hypotheses `hglue` and `hres` supplied from
`AlgebraicGeometry.Modules.isCoherent_of_restrict` and
`AlgebraicGeometry.Modules.isCoherent_restrict`, leaving `hproj` — the projective case — as the
only input owed.

It is included here because [Stacks, Tag 02O4] is what [Stacks, Tag 02O5] consumes over an
affine base, so a caller discharging `HigherDirectImageIsCoherentOverAffineBase` wants this
form rather than the four-hypothesis one. -/
theorem isCoherent_higherDirectImage_of_locallyProjective {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (p : ℕ) [F.IsCoherent]
    (Proj : ∀ {A B : Scheme.{u}}, (A ⟶ B) → Prop)
    (hf : ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ j : 𝒰.I₀, Proj (f ∣_ (𝒰.f j).opensRange))
    (hproj : ∀ V : S.Opens, Proj (f ∣_ V) → ∀ G : (f ⁻¹ᵁ V).toScheme.Modules, G.IsCoherent →
      (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).obj G).IsCoherent) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F).IsCoherent :=
  ProjectiveCoherentImage.isCoherent_higherDirectImage_of_locallyProjective f F p Proj hf
    (fun _ M _ W hW hh => Modules.isCoherent_of_restrict M W hW hh)
    (fun _ M hM U => @Modules.isCoherent_restrict _ M hM U) hproj

/-- **The first assertion of [Stacks, Tag 02O5]**, as a `Prop`: for every proper morphism to a
locally Noetherian scheme and every coherent module on its source, every higher direct image in
nonnegative degree is coherent. -/
def HigherDirectImageIsCoherent : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsLocallyNoetherian S → IsProper f →
    ∀ F : X.Modules, F.IsCoherent → ∀ i : ℕ,
      (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsCoherent

/-- **The affine-base case of [Stacks, Tag 02O5]'s first assertion**: the same statement, with
the base required to be affine. This is the single statement to which this file reduces the whole
tag, and it is the point at which the source's own argument begins — Chow's lemma and the
projective case of [Stacks, Tag 02O4] are applied over an affine Noetherian base. -/
def HigherDirectImageIsCoherentOverAffineBase : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsAffine S → IsLocallyNoetherian S → IsProper f →
    ∀ F : X.Modules, F.IsCoherent → ∀ i : ℕ,
      (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsCoherent

/-- **[Stacks, Tag 02O5]'s first assertion follows from its affine-base case.** Cover `S` by its
affine opens. Properness restricts to each of them by
`AlgebraicGeometry.IsProper.instMorphismRestrict`, local Noetherianness by
`AlgebraicGeometry.instIsLocallyNoetherianToScheme`, and coherence of `F` restricts to the
preimage by `AlgebraicGeometry.Modules.isCoherent_restrict`; the conclusions then glue by
`isCoherent_higherDirectImage_of_cover`. -/
theorem higherDirectImageIsCoherent_of_overAffineBase
    (haff : HigherDirectImageIsCoherentOverAffineBase.{u}) : HigherDirectImageIsCoherent.{u} := by
  intro X S f hS hf F hF i
  have : IsLocallyNoetherian S := hS
  refine isCoherent_higherDirectImage_of_cover f F i
    (fun U : S.affineOpens => (U : S.Opens)) (iSup_affineOpens_eq_top S) fun U => ?_
  have hp : IsProper (f ∣_ (U : S.Opens)) := inferInstance
  exact haff _ _ _ U.2 inferInstance hp _
    (@Modules.isCoherent_restrict _ F hF (f ⁻¹ᵁ (U : S.Opens))) i

/-- **[Stacks, Tag 02O5]'s first assertion is equivalent to its affine-base case.** The forward
implication is the instantiation at an affine base and the reverse is
`higherDirectImageIsCoherent_of_overAffineBase`, so the reduction performed by this file loses
nothing: a proof of the affine case is a proof of the first assertion of Tag 02O5,
and conversely. -/
theorem higherDirectImageIsCoherent_iff_overAffineBase :
    HigherDirectImageIsCoherent.{u} ↔ HigherDirectImageIsCoherentOverAffineBase.{u} :=
  ⟨fun h X S f _ hS hf F hF i => h X S f hS hf F hF i,
    higherDirectImageIsCoherent_of_overAffineBase⟩

/-- **The "higher direct images" assertion of Tag 02O5, verbatim, from the affine-base case.**
Conditional on `HigherDirectImageIsCoherentOverAffineBase`; see [Stacks, Tag 02O5], whose label
for this assertion is unconditional and is therefore **not** attached to this declaration. -/
theorem isCoherent_higherDirectImage_of_isProper
    (haff : HigherDirectImageIsCoherentOverAffineBase.{u}) {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [IsProper f] (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsCoherent :=
  higherDirectImageIsCoherent_of_overAffineBase haff X S f ‹_› ‹_› F ‹_› i

/-- **The "ordinary direct image" assertion of Tag 02O5, verbatim, from the affine-base case.** The
degree-`0` higher direct image of `F` is coherent by
`isCoherent_higherDirectImage_of_isProper`, and coherence transports to `f_* F` along
`AlgebraicGeometry.CoherentAbelian.isCoherent_higherDirectImage_zero_iff`.

Conditional on `HigherDirectImageIsCoherentOverAffineBase`; see [Stacks, Tag 02O5], whose label
for this assertion is unconditional and is therefore **not** attached to this declaration. -/
theorem isCoherent_pushforward_of_isProper
    (haff : HigherDirectImageIsCoherentOverAffineBase.{u}) {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [IsProper f] (F : X.Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent :=
  (CoherentAbelian.isCoherent_higherDirectImage_zero_iff f F).mp
    (isCoherent_higherDirectImage_of_isProper haff f F 0)

end AlgebraicGeometry.ProperCoherentImage

end
