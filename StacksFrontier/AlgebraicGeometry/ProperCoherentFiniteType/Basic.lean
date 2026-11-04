module

public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Devissage
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.QcohInduction.Basic
public import StacksFrontier.AlgebraicGeometry.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# Higher direct images: coherence is finite type, and the dévissage reduction is lossless

[Stacks, Tag 02O5] asserts that for a proper morphism `f : X ⟶ S` to a locally Noetherian
scheme and a coherent `𝒪_X`-module `F`, every higher direct image `R ⁱ f_* F` is coherent, and
that the ordinary direct image `f_* F` is coherent. Neither assertion is proved here; the source
reaches them through Chow's lemma and the projective case of [Stacks, Tag 02O4], and neither of
those is available.

Two files already reduce Tag 02O5. `ProperCoherentImage.Basic` proves that the first assertion
is *equivalent* to its special case over an affine base, and `ProperCoherentImage.Devissage`
proves that the affine-base case *follows from* the integral-ideal case together with the
irreducible case of [Stacks, Tag 01YF]. This file does two further things.

**First, the kernel clause of coherence drops out of the statement entirely.** A proper morphism is
quasi-compact and quasi-separated, so `R ᵖ f_* F` is quasi-coherent for every `p : ℤ` by
[Stacks, Tag 01XJ]; and on a locally Noetherian scheme a quasi-coherent module is coherent as
soon as it is of finite type, by (2) ⇒ (1) of [Stacks, Tag 01XZ]. So for such `f` the predicate
`(R ᵖ f_* F).IsCoherent` is *equivalent* to `(R ᵖ f_* F).IsFiniteType`, and the whole statement is
equivalent to a statement about finite type alone. Nothing of the two conditions of
[Stacks, Tag 01BV] survives except the first.

**Second, `ProperCoherentImage.Devissage`'s reduction is in fact an equivalence.** Its
implementation notes record the converse as unavailable, for a reason they name: deriving the
integral-ideal case from the affine-base case needs the direct image of a quasi-coherent ideal
sheaf along a closed immersion to be coherent, and "neither *quasi-coherent of finite type on a
locally Noetherian scheme is coherent* nor *coherence of a pushforward along a closed immersion*
is proved in this repository". **Both of those are in fact available** — the first as
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType`, the
second, in exactly the needed form, as
`AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit` — so the
converse is a composition, and the dévissage route gives nothing away.

## Main definitions

* `AlgebraicGeometry.ProperCoherentFiniteType.HigherDirectImageIsFiniteType`: the first
  assertion of [Stacks, Tag 02O5] with coherence of the conclusion replaced by finite type.

## Main results

* `isCoherent_rightDerivedPlus_iff_isFiniteType`: for a quasi-compact quasi-separated morphism
  to a locally Noetherian scheme and a quasi-coherent module, coherence of `R ᵖ f_* F` is
  finite type of `R ᵖ f_* F`, in every degree `p : ℤ`.
* `isCoherent_pushforward_iff_isFiniteType`: the same for the ordinary direct image, which is
  [Stacks, Tag 02O5]'s second assertion.
* `higherDirectImageIsCoherent_iff_isFiniteType`: [Stacks, Tag 02O5]'s first assertion is
  equivalent to its finite-type form.
* `exists_isCoherent_rightDerivedPlus_of_le`: **unconditionally**, over a quasi-compact base
  there is a degree beyond which every higher direct image of every quasi-coherent module is
  coherent, because it vanishes. This is [Stacks, Tag 01XJ]'s uniform bound.
* `higherDirectImageIsCoherentOnIntegralIdeals_of_overAffineBase` and
  `higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals`: the converse of
  `ProperCoherentImage.higherDirectImageIsCoherentOverAffineBase_of_integralIdeals`, and the
  resulting equivalence.
* `higherDirectImageIsCoherent_iff_integralIdeals`: the first assertion of Tag 02O5 is equivalent to
  the integral-ideal case, given the irreducible case of [Stacks, Tag 01YF].

## Implementation notes

**Which coherence predicate.** As in `ProperCoherentImage.Basic`, the predicate here is the root
`SheafOfModules.IsCoherent` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`, which is what
`F.IsCoherent` means for `F : X.Modules`. The namespace deliberately avoids a `Stacks.` prefix:
inside one, `SheafOfModules.IsCoherent` resolves to the separate constant
`Stacks.SheafOfModules.IsCoherent`. Verified by elaboration rather than assumed — both
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType` and
`AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit` print
their conclusion as the root constant under `pp.fullNames`, so no bridge along
`AlgebraicGeometry.CoherentAbelian.isCoherent_iff_stacksIsCoherent` is needed.

**Three instances that do not synthesize and are supplied by hand.** `QuasiCompact f` and
`QuasiSeparated f` *do* follow from `IsProper f` by instance search. These do not:
`IsLocallyNoetherian X` from `IsProper f` and `IsLocallyNoetherian S` (it is
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`), `F.IsQuasicoherent` from
`F.IsCoherent` (it is the first half of
`Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent`), and
quasi-coherence of `R ᵖ f_* F`, where
`Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent` is an instance
but is not found through the `def` `Scheme.Modules`.

**The degree range.** `isCoherent_rightDerivedPlus_iff_isFiniteType` is stated for `p : ℤ`, not
for `p : ℕ`, because both of its inputs are: [Stacks, Tag 01XJ]'s quasi-coherence holds for every
integer, and the negative degrees are already known to be coherent outright by
`AlgebraicGeometry.CoherentAbelian.isCoherent_higherDirectImage_of_neg`. The assertions of Tag 02O5
are then the `ℕ`-indexed specialisations.

**Why `exists_isCoherent_rightDerivedPlus_of_le` needs no conditional hypothesis.** The bound
is produced by
`Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.exists_isZero_rightDerived_pushforward`,
which quantifies the module *inside* the existential, so one bound serves every quasi-coherent
module at once; above it the higher direct image is a zero object, and a zero object is coherent
because coherence is a weak Serre class. It is therefore a genuinely unconditional fragment of
the tag's first assertion — but only a fragment: the degree is bounded below by an `n` that
depends on `f`, so it is not a covering set for the label, which quantifies over all `i : ℕ`.

**No tag is attached, and none is earned.** Both of [Stacks, Tag 02O5]'s labels — its "higher
direct images" label and its "ordinary direct image" label — name unconditional assertions over
all degrees. Every statement below either carries a hypothesis the tag lacks (the affine-base
case, the integral-ideal case, the irreducible case of [Stacks, Tag 01YF], or finite type of the
conclusion) or restricts the degree range. A labelled assertion may not carry a hypothesis the
tag lacks, so attaching either label here would record as proved something that is not.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProperCoherentFiniteType

attribute [local instance] HasDerivedCategory.standard

/-! ### Quasi-coherence of a higher direct image, as a plain hypothesis-free statement -/

/-- **Every higher direct image of a quasi-coherent module along a quasi-compact quasi-separated
morphism is quasi-coherent**, in every integer degree. This is
`Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent`, restated
because that declaration is an `instance` which instance search does not find through the `def`
`Scheme.Modules`. -/
theorem isQuasicoherent_rightDerivedPlus {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) (hF : F.IsQuasicoherent) (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsQuasicoherent :=
  @Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent
    X S f ‹_› ‹_› F hF p

/-! ### Coherence of a higher direct image is finite type of it -/

/-- A coherent module is quasi-coherent. -/
private theorem isQuasicoherent_of_isCoherent {X : Scheme.{u}} (F : X.Modules) [F.IsCoherent] :
    F.IsQuasicoherent :=
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1

/-- On a locally Noetherian scheme, a quasi-coherent module of finite type is coherent. -/
private theorem isCoherent_of_isQuasicoherent_of_isFiniteType {S : Scheme.{u}}
    [IsLocallyNoetherian S] {M : S.Modules} (hM : M.IsQuasicoherent) (h : M.IsFiniteType) :
    M.IsCoherent :=
  @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType
    S ‹_› _ hM h

/-- **Finite type suffices for coherence of a higher direct image.** Let `f : X ⟶ S` be
quasi-compact and quasi-separated with `S` locally Noetherian, and let `F` be quasi-coherent. If
`R ᵖ f_* F` is of finite type then it is coherent.

`R ᵖ f_* F` is quasi-coherent by [Stacks, Tag 01XJ], and on a locally Noetherian scheme
quasi-coherent plus finite type is coherent, which is (2) ⇒ (1) of [Stacks, Tag 01XZ]. -/
theorem isCoherent_rightDerivedPlus_of_isFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    (hF : F.IsQuasicoherent) (p : ℤ)
    (h : (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsFiniteType) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsCoherent :=
  isCoherent_of_isQuasicoherent_of_isFiniteType (isQuasicoherent_rightDerivedPlus f F hF p) h

/-- **Coherence of a higher direct image is exactly finite type of it.** Under the hypotheses of
[Stacks, Tag 02O5] weakened to quasi-compactness and quasi-separatedness of `f` and
quasi-coherence of `F`, the two conditions of [Stacks, Tag 01BV] on `R ᵖ f_* F` collapse to the
first: the kernel clause is automatic.

The forward implication is the `isFiniteType` field of coherence; the reverse is
`isCoherent_rightDerivedPlus_of_isFiniteType`. -/
theorem isCoherent_rightDerivedPlus_iff_isFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    (hF : F.IsQuasicoherent) (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsCoherent ↔
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsFiniteType :=
  ⟨fun h => h.isFiniteType, isCoherent_rightDerivedPlus_of_isFiniteType f F hF p⟩

/-- **The same equivalence under the hypotheses of Tag 02O5.** For `f` proper, `S` locally
Noetherian and `F` coherent, coherence of `R ᵖ f_* F` is finite type of `R ᵖ f_* F`. -/
theorem isCoherent_rightDerivedPlus_iff_isFiniteType_of_isProper {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [IsProper f] (F : X.Modules) [F.IsCoherent] (p : ℤ) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsCoherent ↔
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsFiniteType :=
  isCoherent_rightDerivedPlus_iff_isFiniteType f F (isQuasicoherent_of_isCoherent F) p

/-! ### The ordinary direct image -/

/-- **The ordinary direct image of a quasi-coherent module along a quasi-compact quasi-separated
morphism is quasi-coherent.** This is the degree-`0` case of `isQuasicoherent_rightDerivedPlus`
transported along `Stacks.AlgebraicGeometry.HigherDirectImage.higherDirectImageZeroIso`, which
identifies `R ⁰ f_* F` with `f_* F` because the pushforward is a right adjoint, hence left
exact. -/
theorem isQuasicoherent_pushforward {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) (hF : F.IsQuasicoherent) :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
  ObjectProperty.prop_of_iso
    (P := fun M : SheafOfModules.{u} S.ringCatSheaf => M.IsQuasicoherent)
    (Stacks.AlgebraicGeometry.HigherDirectImage.higherDirectImageZeroIso f F)
    (isQuasicoherent_rightDerivedPlus f F hF 0)

/-- **Coherence of the ordinary direct image is exactly finite type of it.** This is the second
assertion of [Stacks, Tag 02O5] with the kernel clause of [Stacks, Tag 01BV] removed: for `f`
proper (indeed merely quasi-compact and quasi-separated), `S` locally Noetherian and `F`
coherent, `f_* F` is coherent if and only if it is of finite type. -/
theorem isCoherent_pushforward_iff_isFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    (hF : F.IsQuasicoherent) :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent ↔
      ((Scheme.Modules.pushforward f).obj F).IsFiniteType :=
  ⟨fun h => h.isFiniteType, isCoherent_of_isQuasicoherent_of_isFiniteType
    (isQuasicoherent_pushforward f F hF)⟩

/-- **The same under the hypotheses of Tag 02O5**, for `f` proper and `F` coherent. -/
theorem isCoherent_pushforward_iff_isFiniteType_of_isProper {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [IsProper f] (F : X.Modules) [F.IsCoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsCoherent ↔
      ((Scheme.Modules.pushforward f).obj F).IsFiniteType :=
  isCoherent_pushforward_iff_isFiniteType f F (isQuasicoherent_of_isCoherent F)

/-! ### The first assertion of Tag 02O5 in finite-type form -/

/-- **[Stacks, Tag 02O5]'s first assertion with coherence replaced by finite type**: for every
proper morphism to a locally Noetherian scheme and every coherent module on its source, every
higher direct image in nonnegative degree is of finite type. -/
def HigherDirectImageIsFiniteType : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsLocallyNoetherian S → IsProper f →
    ∀ F : X.Modules, F.IsCoherent → ∀ i : ℕ,
      (((Scheme.Modules.pushforward f).rightDerivedPlus (i : ℤ)).obj F).IsFiniteType

/-- **[Stacks, Tag 02O5]'s first assertion is equivalent to its finite-type form.** Pointwise
`isCoherent_rightDerivedPlus_iff_isFiniteType_of_isProper`, so the tag asks nothing beyond
finite generation of the higher direct images: the kernel clause of [Stacks, Tag 01BV] is free. -/
theorem higherDirectImageIsCoherent_iff_isFiniteType :
    ProperCoherentImage.HigherDirectImageIsCoherent.{u} ↔ HigherDirectImageIsFiniteType.{u} :=
  ⟨fun h X S f hS hf F hF i => (h X S f hS hf F hF i).isFiniteType, fun h X S f hS hf F hF i =>
    (@isCoherent_rightDerivedPlus_iff_isFiniteType_of_isProper X S f hS hf F hF i).2
      (h X S f hS hf F hF i)⟩

/-! ### An unconditional fragment: coherence in all high degrees -/

/-- **A zero sheaf of modules is coherent.** Coherence is a weak Serre class, so it holds on any
object isomorphic to zero. -/
theorem isCoherent_of_isZero {S : Scheme.{u}} {M : S.Modules} (hM : IsZero M) : M.IsCoherent :=
  ObjectProperty.prop_of_isZero
    (P := fun N : SheafOfModules.{u} S.ringCatSheaf => N.IsCoherent) hM

/-- **Over a quasi-compact base, all sufficiently high higher direct images are coherent, with no
conditional hypothesis at all.** For `f : X ⟶ S` quasi-compact and quasi-separated and `S`
quasi-compact there is an `n : ℤ`, depending only on `f`, such that for every `p ≥ n` and every
quasi-coherent `F` the module `R ᵖ f_* F` is coherent — because it vanishes.

The bound is [Stacks, Tag 01XJ]'s uniform vanishing,
`Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.exists_isZero_rightDerived_pushforward`, whose
existential quantifies `F` inside the bound, so one `n` serves every module. No hypothesis on
the base beyond quasi-compactness is used — in particular no Noetherian hypothesis, since a zero
object is coherent outright rather than through [Stacks, Tag 01XZ]. -/
theorem exists_isCoherent_rightDerivedPlus_of_le {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    [QuasiSeparated f] [CompactSpace S] :
    ∃ n : ℤ, ∀ p : ℤ, n ≤ p → ∀ F : X.Modules, F.IsQuasicoherent →
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsCoherent := by
  obtain ⟨n, hn⟩ :=
    Stacks.AlgebraicGeometry.Tag01XJUniformVanishing.exists_isZero_rightDerived_pushforward f
  exact ⟨n, fun p hp F hF => isCoherent_of_isZero (@hn p hp F hF)⟩

/-- **The same, for a proper morphism to an affine locally Noetherian base and a coherent
module.** This is the configuration of
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase`, so the
remaining content of that statement lives in a bounded range of degrees. -/
theorem exists_isCoherent_rightDerivedPlus_of_le_of_isProper {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffine S] [IsProper f] :
    ∃ n : ℤ, ∀ p : ℤ, n ≤ p → ∀ F : X.Modules, F.IsCoherent →
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).IsCoherent := by
  obtain ⟨n, hn⟩ := exists_isCoherent_rightDerivedPlus_of_le f
  exact ⟨n, fun p hp F _ => hn p hp F (isQuasicoherent_of_isCoherent F)⟩

/-! ### The dévissage reduction is an equivalence -/

/-- **The integral-ideal case of [Stacks, Tag 02O5] follows from its affine-base case.** This is
the converse of
`ProperCoherentImage.higherDirectImageIsCoherentOverAffineBase_of_integralIdeals`, which the
implementation notes of `ProperCoherentImage.Devissage` record as unavailable.

It is a composition. Given `f : X ⟶ S` proper with `S` affine locally Noetherian, `X` is locally
Noetherian by `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`; for a closed immersion
`i : Z ⟶ X` and a quasi-coherent ideal sheaf `I ⊆ 𝒪_Z` the direct image `i_* I` is coherent by
`AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit` — the
closed-immersion case of [Stacks, Tag 01Y6], which uses no higher direct image and no proper
morphism — and the affine-base case applied to `f` and `i_* I` is the conclusion. Integrality of
`Z` is not used. -/
theorem higherDirectImageIsCoherentOnIntegralIdeals_of_overAffineBase
    (haff : ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u}) :
    ProperCoherentImage.HigherDirectImageIsCoherentOnIntegralIdeals.{u} := by
  intro X S f hS hN hf Z i hi hZ I hI p
  have : IsAffine S := hS
  have : IsLocallyNoetherian S := hN
  have : IsProper f := hf
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsClosedImmersion i := hi
  exact haff X S f ‹_› ‹_› ‹_› _
    (ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit i I hI) p

/-- **The affine-base case and the integral-ideal case of [Stacks, Tag 02O5] are equivalent**,
given the irreducible case of [Stacks, Tag 01YF]. The forward implication is
`higherDirectImageIsCoherentOnIntegralIdeals_of_overAffineBase` and needs no hypothesis; the
reverse is `ProperCoherentImage.higherDirectImageIsCoherentOverAffineBase_of_integralIdeals`.

So the dévissage of `ProperCoherentImage.Devissage` loses nothing: whoever proves the
integral-ideal case proves the first assertion of Tag 02O5, and conversely. -/
theorem higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals
    (hirr : ∀ Y : Scheme.{u}, IsNoetherian Y →
      Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage Y) :
    ProperCoherentImage.HigherDirectImageIsCoherentOverAffineBase.{u} ↔
      ProperCoherentImage.HigherDirectImageIsCoherentOnIntegralIdeals.{u} :=
  ⟨higherDirectImageIsCoherentOnIntegralIdeals_of_overAffineBase,
    ProperCoherentImage.higherDirectImageIsCoherentOverAffineBase_of_integralIdeals hirr⟩

/-- **[Stacks, Tag 02O5]'s first assertion is equivalent to its integral-ideal case**, given the
irreducible case of [Stacks, Tag 01YF]. Composed from
`higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals` and the lossless affine reduction
`AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherent_iff_overAffineBase`. -/
theorem higherDirectImageIsCoherent_iff_integralIdeals
    (hirr : ∀ Y : Scheme.{u}, IsNoetherian Y →
      Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage Y) :
    ProperCoherentImage.HigherDirectImageIsCoherent.{u} ↔
      ProperCoherentImage.HigherDirectImageIsCoherentOnIntegralIdeals.{u} :=
  ProperCoherentImage.higherDirectImageIsCoherent_iff_overAffineBase.trans
    (higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals hirr)

/-- **The integral-ideal case in finite-type form.** Combining
`higherDirectImageIsCoherent_iff_integralIdeals` with
`higherDirectImageIsCoherent_iff_isFiniteType`: given the irreducible case of
[Stacks, Tag 01YF], the whole of [Stacks, Tag 02O5]'s first assertion is equivalent to finite
generation of the higher direct images of the ideal sheaves on integral closed subschemes. -/
theorem higherDirectImageIsFiniteType_iff_integralIdeals
    (hirr : ∀ Y : Scheme.{u}, IsNoetherian Y →
      Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage Y) :
    HigherDirectImageIsFiniteType.{u} ↔
      ProperCoherentImage.HigherDirectImageIsCoherentOnIntegralIdeals.{u} :=
  higherDirectImageIsCoherent_iff_isFiniteType.symm.trans
    (higherDirectImageIsCoherent_iff_integralIdeals hirr)

end AlgebraicGeometry.ProperCoherentFiniteType

end
