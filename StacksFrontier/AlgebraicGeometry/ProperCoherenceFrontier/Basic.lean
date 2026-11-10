module

public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.IdealPushforwardCriterion
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.Devissage
public import StacksFrontier.AlgebraicGeometry.ProperCoherentImage.IntegralIdeals
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Locality

/-!
# [Stacks, Tag 02O5] and [Stacks, Tag 02O6] are one unconditional obligation

[Stacks, Tag 02O5] says that the higher direct images of a coherent module along a proper
morphism to a locally Noetherian scheme are coherent; [Stacks, Tag 02O6] says that for `A`
Noetherian and `f : X ⟶ Spec A` proper, each `Hⁱ(X, F)` is a finite `A`-module. Neither is
proved here. What is proved is that each of them is **equivalent**, with nothing assumed, to the
single statement
`AlgebraicGeometry.ProperCoherentImage.HigherDirectImageIsCoherentOnIntegralIdeals`: coherence of
`R ᵖ f_* (i_* I)` for `i : Z ⟶ X` the closed immersion of an integral closed subscheme, `I` a
quasi-coherent ideal sheaf on `Z`, and `f` proper onto an affine locally Noetherian base.

Three reductions already in the library compose into that equivalence:

* the affine-base reduction of [Stacks, Tag 02O5]
  (`AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherent_iff_overAffineBase`);
* the dévissage of [Stacks, Tag 01YG]
  (`Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent`), whose two side
  conditions for the class "every higher direct image is coherent" are
  `AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_terminal` and
  `AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_X₂_of_shortExact`, both
  unconditional;
* the equivalence of the two tags over an affine base
  (`Stacks.AlgebraicGeometry.ProperCohomologyFinite`
  `.forall_isCoherent_rightDerivedPlus_iff_forall_moduleFinite_cohomology`).

`AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherentOverAffineBase_of_integralIdeals`
reaches the same conclusion as the first theorem below, but carries in addition the irreducible
case of [Stacks, Tag 01YF] as a hypothesis `hirr`, in the form
`Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage`. That hypothesis is
unnecessary: [Stacks, Tag 01YG] is itself a theorem of the library, proved from the full
[Stacks, Tag 01YF] filtration
(`Stacks.AlgebraicGeometry.CoherentDevissage.exists_filtration_by_integral_ideal_pushforwards`)
rather than from the irreducible case alone, so the dévissage engine may be applied directly and
nothing about the filtration need be assumed.

## Main results

All of the following live in the namespace `AlgebraicGeometry.ProperCoherenceFrontier`.

* `higherDirectImageIsCoherentOverAffineBase_of_integralIdeals`: the affine-base case of
  [Stacks, Tag 02O5]'s first assertion from the integral-ideal case alone.
* `higherDirectImageIsCoherent_of_integralIdeals`: the whole of that assertion from the same.
* `higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals` and
  `higherDirectImageIsCoherent_iff_integralIdeals`: those two implications upgraded to
  equivalences, the converses being free.
* `moduleFinite_cohomology_of_integralIdeals`: **[Stacks, Tag 02O6]'s conclusion** from the
  integral-ideal case alone.
* `forall_moduleFinite_cohomology_iff_integralIdeals`: [Stacks, Tag 02O6], quantified over all
  of its data, is equivalent to the integral-ideal case.

## Implementation notes

**No `@[stacks 02O5]` and no `@[stacks 02O6]` attribute is attached to anything here.** Both tags
assert their conclusions outright, and every statement below either carries the integral-ideal
case as a hypothesis or is an equivalence between two unproved `Prop`s. The remaining obligation
is exactly the integral-ideal case, and in the source it is where Chow's lemma
([Stacks, Tag 0200], formalized as `AlgebraicGeometry.hasDenseChowModification`) meets the
projective case ([Stacks, Tag 02O4], formalized as
`AlgebraicGeometry.LocallyProjectiveCoherentImage`
`.isCoherent_rightDerived_of_isLocallyProjective`) and the relative-ample vanishing of
[Stacks, Tag 02O1]; the last of these is available only granted
`Stacks.AlgebraicGeometry.RelativeAmpleTwistVanishing.VanishingOverAffineBase`, which no
declaration proves.

**The derived-functor indexing and its instance.** The statements are phrased with
`CategoryTheory.Functor.rightDerivedPlus`, matching the `Prop`s being related, and that functor
takes a `CategoryTheory.HasDerivedCategory` instance. Two are in scope in this import closure:
`CategoryTheory.HasDerivedCategory.standard`, against which the imported `Prop`s and lemmas were
stated, and the global `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which lies at a
lower universe. The former is given priority below, since without it the predicate handed to the
dévissage engine is elaborated at the other instance's universes and no longer matches the
imported lemmas.

**Why the dévissage predicate quantifies over the degree.** [Stacks, Tag 01YG] propagates a
property of coherent modules, and the property at issue is coherence of `R ᵖ f_* F` for *every*
`p` at once: extension stability relates the degree-`p` term of the middle module to the terms of
the outer ones in degrees `p - 1` through `p + 1`, so a single degree is not a propagating class.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Cohomology.AffineBase

universe u

namespace AlgebraicGeometry.ProperCoherenceFrontier

open AlgebraicGeometry.ProperCoherentImage
open Stacks.AlgebraicGeometry.ProperCohomologyFinite

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The dévissage, with nothing assumed about the filtration -/

/-- **The affine-base case of [Stacks, Tag 02O5]'s first assertion from its integral-ideal case,
unconditionally.** Granted that `R ᵖ f_* (i_* I)` is coherent for every closed immersion
`i : Z ⟶ X` of an integral closed subscheme of the source of a proper morphism onto an affine
locally Noetherian base and every quasi-coherent ideal `I ⊆ 𝒪_Z`, every higher direct image of
every coherent module along such a morphism is coherent.

The proof is [Stacks, Tag 01YG] applied to the property "every higher direct image is coherent".
Its `hzero` input is `AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_terminal`
and its `hext` input is
`AlgebraicGeometry.ProperCoherentImage.isCoherent_higherDirectImage_X₂_of_shortExact`, neither of
which uses properness, the base, or any hypothesis on the modules beyond short exactness; the
Noetherianness of `X` that [Stacks, Tag 01YG] requires is
`AlgebraicGeometry.ProperCoherentImage.isNoetherian_of_isProper_of_isAffine`.

Unlike
`AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherentOverAffineBase_of_integralIdeals`
this assumes nothing about the dévissage filtration of [Stacks, Tag 01YF]. -/
theorem higherDirectImageIsCoherentOverAffineBase_of_integralIdeals
    (hideal : HigherDirectImageIsCoherentOnIntegralIdeals.{u}) :
    HigherDirectImageIsCoherentOverAffineBase.{u} := by
  intro X S f hS hN hf F hF p
  have : IsAffine S := hS
  have : IsLocallyNoetherian S := hN
  have : IsProper f := hf
  have : IsNoetherian X := isNoetherian_of_isProper_of_isAffine f
  exact Stacks.AlgebraicGeometry.CoherentDevissage.property_of_isCoherent X
    (fun G => ∀ q : ℕ,
      (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj G).IsCoherent)
    (isCoherent_higherDirectImage_terminal f)
    (fun _ hT _ _ _ hP₁ hP₃ => isCoherent_higherDirectImage_X₂_of_shortExact f hT hP₁ hP₃)
    (fun i _ _ I hI q => hideal X S f ‹_› ‹_› ‹_› i ‹_› ‹_› I hI q)
    F hF p

/-- **[Stacks, Tag 02O5]'s first assertion from its integral-ideal case, unconditionally.** The
previous theorem composed with the affine-base reduction
`AlgebraicGeometry.ProperCoherentImage.higherDirectImageIsCoherent_of_overAffineBase`. -/
theorem higherDirectImageIsCoherent_of_integralIdeals
    (hideal : HigherDirectImageIsCoherentOnIntegralIdeals.{u}) :
    HigherDirectImageIsCoherent.{u} :=
  higherDirectImageIsCoherent_of_overAffineBase
    (higherDirectImageIsCoherentOverAffineBase_of_integralIdeals hideal)

/-! ### The frontier of [Stacks, Tag 02O5] -/

/-- **The integral-ideal case and the affine-base case of [Stacks, Tag 02O5]'s first assertion
are equivalent, unconditionally.** The converse direction is
`AlgebraicGeometry.ProperCoherentImage`
`.higherDirectImageIsCoherentOnIntegralIdeals_of_overAffineBase`, which is free because `i_* I`
is itself a coherent module on `X`. -/
theorem higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals :
    HigherDirectImageIsCoherentOverAffineBase.{u} ↔
      HigherDirectImageIsCoherentOnIntegralIdeals.{u} :=
  ⟨higherDirectImageIsCoherentOnIntegralIdeals_of_overAffineBase,
    higherDirectImageIsCoherentOverAffineBase_of_integralIdeals⟩

/-- **[Stacks, Tag 02O5]'s first assertion is equivalent to its integral-ideal case,
unconditionally.** So the tag is one named statement about ideal sheaves on integral closed
subschemes over an affine base, and no more: a proof of that statement is a proof of the tag, and
the tag yields nothing stronger. -/
theorem higherDirectImageIsCoherent_iff_integralIdeals :
    HigherDirectImageIsCoherent.{u} ↔ HigherDirectImageIsCoherentOnIntegralIdeals.{u} :=
  higherDirectImageIsCoherent_iff_overAffineBase.trans
    higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals

/-! ### The frontier of [Stacks, Tag 02O6] -/

/-- **[Stacks, Tag 02O6]'s conclusion from the integral-ideal case of [Stacks, Tag 02O5],
unconditionally.** For `f : X ⟶ S` proper onto an affine locally Noetherian base and `F`
coherent, `Hⁱ(X, F)` is a finite `Γ(S, ⊤)`-module, granted
`HigherDirectImageIsCoherentOnIntegralIdeals` and nothing else.

The scalars are restricted along `f.appTop`, which is the spelling [Stacks, Tag 01XK] lands in;
`Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_cohomology_ringBase_of_isCoherent`
moves the conclusion to a ring base `A` with `S = Spec A`, which is the tag's own. -/
theorem moduleFinite_cohomology_of_integralIdeals
    (hideal : HigherDirectImageIsCoherentOnIntegralIdeals.{u}) {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsAffine S] [IsLocallyNoetherian S] (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived i).obj F)) :=
  forall_isCoherent_rightDerivedPlus_iff_forall_moduleFinite_cohomology.1
    (fun X₀ S₀ g hg hS₀ G hG j =>
      higherDirectImageIsCoherent_of_integralIdeals hideal X₀ S₀ g hS₀ hg G hG j)
    X S f ‹_› ‹_› ‹_› F ‹_› i

/-- **[Stacks, Tag 02O6] is equivalent to the integral-ideal case of [Stacks, Tag 02O5],
unconditionally.** The tag, quantified over every proper morphism onto an affine locally
Noetherian base and every coherent module, holds if and only if
`HigherDirectImageIsCoherentOnIntegralIdeals` does.

Together with `higherDirectImageIsCoherent_iff_integralIdeals` this says that the two tags are a
single obligation and names it: coherence of the higher direct images of the direct image of a
quasi-coherent ideal sheaf on an integral closed subscheme. -/
theorem forall_moduleFinite_cohomology_iff_integralIdeals :
    (∀ (X S : Scheme.{u}) (f : X ⟶ S), IsProper f → IsAffine S → IsLocallyNoetherian S →
        ∀ F : X.Modules, F.IsCoherent → ∀ i : ℕ,
          Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
            (((moduleGlobalSections X).rightDerived i).obj F))) ↔
      HigherDirectImageIsCoherentOnIntegralIdeals.{u} := by
  refine ⟨fun h => higherDirectImageIsCoherentOverAffineBase_iff_integralIdeals.1 ?_,
    fun hideal X S f hf hS hN F hF i => ?_⟩
  · intro X S f hS hN hf F hF i
    exact forall_isCoherent_rightDerivedPlus_iff_forall_moduleFinite_cohomology.2 h X S f hf hN
      F hF i
  · have : IsProper f := hf
    have : IsAffine S := hS
    have : IsLocallyNoetherian S := hN
    have : F.IsCoherent := hF
    exact moduleFinite_cohomology_of_integralIdeals hideal f F i

end AlgebraicGeometry.ProperCoherenceFrontier

end
