module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerAlgebraization
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionColimitEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionSectionwiseCriteria

/-!
# Lefschetz for the fundamental group: restriction to the zero scheme of an ample section

Let `k` be a field, let `X` be a proper scheme over `k`, let `L` be an ample invertible
`𝒪_X`-module, let `s ∈ Γ(X, L)` and let `Y = Z(s)` be the zero scheme of `s`.
[Stacks, Tag 0ELC] asserts that if

`depth(𝒪_{X, x}) + dim({x}‾) > 1`

at every point `x` of `X` outside `Y`, then the restriction functor `FÉt_X ⟶ FÉt_Y` is fully
faithful, and that in fact `FÉt_V ⟶ FÉt_Y` is fully faithful for every open subscheme `V ⊆ X`
containing `Y`.

The source proves both statements as *formal consequences*: the first of [Stacks, Tag 0EJZ]
together with Algebraic and Formal Geometry, Proposition [Stacks, Tag 0EL1], the second of
Tag 0EJZ together with Algebraic and Formal Geometry, Lemma [Stacks, Tag 0EL2]. This file
names the pieces of that argument: the 0EL1/0EL2 half as the single statement
`Stacks.FundamentalGroup.AmplePowerSectionsCompleteFromDepth`, a general statement about general
objects which is precisely Tag 0EL2 read in the vocabulary of condition (2) of Tag 0EJZ, and the
implications of [Stacks, Tag 0EKP] that Tag 0EJZ consumes. Tag 0ELC itself, both statements, is
proved with none of them as
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_zeroScheme_of_isProper` and
`Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_neighborhood_of_isProper` in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.LefschetzZeroSchemeRestrictionFromDepth`.

## Why the 0EL1/0EL2 half is carried

[Stacks, Tag 0EL1] *is* proved, as
`Stacks.Algebraization.isIso_zeroSchemeComparison_of_depthAddDim_gt`, and the depth and dimension
of `Stacks.FundamentalGroup.DepthAddDimGtOneOutsideSupport` below are spelled in its own
vocabulary — `Stacks.Algebraization.dimClosureAt`, compared in `EInt` through
`Stacks.Algebraization.enatToEInt` and `Stacks.Algebraization.krullDimToEInt` — so that the two
hypotheses are the same arithmetic statement at `σ = 1`. It still cannot be consumed here, for
four independent reasons.

* Its conclusion is `IsIso` of the cohomology comparison `Hⁱ(X, 𝓕) ⟶ lim Hⁱ(Qₙ, 𝓕ₙ)` of
  `Stacks.Algebraization.zeroSchemeComparison`, while condition (2) of Tag 0EJZ is
  `Stacks.Algebraization.IsInfinitesimalSectionsComplete`, phrased by the universal property of
  the limit of the *sections* of the restrictions. Bridging the two in degree zero needs an
  identification of `Hgroup X.ringCatSheaf ⊤ 0 𝓕` with `Γ(𝓕, ⊤)`, and an identification of the
  two towers of thickenings — `zeroScheme X L s ^ n` against
  `Scheme.Hom.liftCoborder.ker ^ (n + 1)` — and this library carries neither.
* Tag 0EL1 itself carries three inputs (the punctured-cone fibre dichotomy, the
  section ring data, since clause (1) of [Stacks, Tag 0B5T] is absent from this library, and the
  algebraization square); none of them can be produced for a given `X`, `L` and `s` here.
* The second statement of Tag 0ELC needs the open-subscheme form, [Stacks, Tag 0EL2], which has
  no carrier in this library at all.
* The depth hypothesis of Tag 0ELC is on `𝒪_X`, whereas Tags 0EL1 and 0EL2 want it on the module
  whose sections are being compared, here `L^{⊗ m}`. The two agree because the stalks of an
  invertible module are free of rank one, which this library does not record either.

## Main definitions

* `Stacks.FundamentalGroup.DepthAddDimGtOneOutsideSupport` — the hypothesis
  `depth(𝒪_{X, x}) + dim({x}‾) > 1` for every `x` outside a closed subscheme, in the arithmetic
  of [Stacks, Tag 0EL1].
* `Stacks.FundamentalGroup.AmplePowerSectionsCompleteFromDepth` — [Stacks, Tag 0EL2] in the shape
  condition (2) of [Stacks, Tag 0EJZ] consumes it, named so that it can be stated once and
  quoted.
* `Stacks.FundamentalGroup.AmplePowersImpliesFiniteLocallyFreeSections`,
  `Stacks.FundamentalGroup.FiniteLocallyFreeSectionsImpliesCompletionFullyFaithful` — the
  implications `(2) ⇒ (3)` and `(3) ⇒ (4)` of [Stacks, Tag 0EKP] that Tag 0EJZ asks
  for, as statements about general objects.

## Main results

* `Stacks.FundamentalGroup.isNoetherian_of_isProper_of_isAmple` — a scheme proper over a field
  carrying an ample invertible module is Noetherian.

## Implementation notes

The open subschemes of `X` containing `Y` are `Stacks.FundamentalGroup.Neighborhood X Y`, and the
closed immersion `Y ⟶ V` is `Stacks.FundamentalGroup.Neighborhood.toSchemeHom`, which
`Stacks.FundamentalGroup.isClosedImmersion_neighborhoodToSchemeHom` makes a closed immersion. So
the second statement is read off the same carried hypothesis as the first, with no lifting of the
zero-scheme immersion along an open immersion to be done by hand.

Tag 0EJZ asks for `IsNoetherian X`, which is not assumed: `X` is locally Noetherian because a
proper morphism is locally of finite type and the base `Spec k` is Noetherian
(`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`), and `X` is quasi-compact because
`AlgebraicGeometry.Scheme.Modules.IsAmple` says so in its first clause. A neighbourhood `V` is
then Noetherian too, by
`Stacks.Coherent.isNoetherian_of_isOpenImmersion`; note that this is `IsNoetherian`, not the
weaker `IsLocallyNoetherian` which the Mathlib instance for open subschemes gives, and
`IsNoetherian` is what Tag 0EJZ asks for.

The two implications of [Stacks, Tag 0EKP] and the two hypotheses of [Stacks, Tag 0EL8] that
Tag 0EJZ carries are passed through; see the module documentation of
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionSectionwiseCriteria` for why they have
no carrier. The two implications of Tag 0EKP are quantified over all Noetherian schemes and all
closed immersions here, rather than taken at the one closed immersion of the statement, so that
condition (4) of that tag can be written down at all: the predicate
`Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree` asks for
`IsLocallyNoetherian` of the ambient scheme, which is derived rather than assumed and so is not
available in the statement of the theorem.

## References

* [Stacks Project, Tag 0ELC](https://stacks.math.columbia.edu/tag/0ELC)
* [Stacks Project, Tag 0EJZ](https://stacks.math.columbia.edu/tag/0EJZ)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EL2](https://stacks.math.columbia.edu/tag/0EL2)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.FundamentalGroup

/-! ### The depth and dimension hypothesis -/

/-- **The hypothesis of [Stacks, Tag 0ELC]:** at every point `x` of `X` outside the closed
subscheme cut out by `Y` one has `depth(𝒪_{X, x}) + dim({x}‾) > 1`.

The depth is the depth of the local ring over itself along its maximal ideal, which is
[Stacks, Tag 0341] part (1) for the structure sheaf, and the dimension is
`Stacks.Algebraization.dimClosureAt`. The sum is formed in `EInt` through
`Stacks.Algebraization.enatToEInt` and `Stacks.Algebraization.krullDimToEInt`, exactly as the
hypothesis `hdepth` of [Stacks, Tag 0EL1] forms it, so that the two are the same
arithmetic statement at `σ = 1`. -/
public def DepthAddDimGtOneOutsideSupport (X : Scheme.{u}) (Y : X.IdealSheafData) : Prop :=
  ∀ x : X, x ∉ (Y.support : Set X) →
    Stacks.Algebraization.enatToEInt
        (Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x)) +
      Stacks.Algebraization.krullDimToEInt (Stacks.Algebraization.dimClosureAt X x) >
        ((1 : ℤ) : EInt)

/-! ### The general statement granted to Tag 0ELC -/

/-- **[Stacks, Tag 0EL2], in the shape condition (2) of [Stacks, Tag 0EJZ] consumes it**, as a
statement about general objects.

Tag 0EL2 says that for `X` proper over a field `k`, `L` an ample invertible `𝒪_X`-module, `s` a
global section of `L` with zero scheme `Y = Z(s)`, and `𝓕` a coherent `𝒪_X`-module whose depth
satisfies `depth(𝓕_x) + dim({x}‾) > 1` outside `Y`, the map
`Γ(V, 𝓕) → lim Γ(Y_n, 𝓕|_{Y_n})` is an isomorphism for every open `V ⊆ X` containing `Y`.
Applied to `𝓕 = L^{⊗ m}` — whose depth at a point is that of `𝒪_{X, x}`, the stalks of an
invertible module being free of rank one — it gives exactly
`Stacks.FundamentalGroup.SectionsCompleteAmplePowers` for the closed immersion of `Y` into `V`,
witnessed by the restriction of `L`, which stays ample along an immersion. Two conclusions are
asked for: the first conjunct is the case `V = X`, taken at the closed immersion `Y ⟶ X` itself
rather than at the neighbourhood `⊤` so that the restriction functor of the first statement of
Tag 0ELC is literally the one along that immersion; the second conjunct is every neighbourhood
`V`, which is the case the source's `V` ranges over.

See the module documentation for why neither [Stacks, Tag 0EL1] nor anything else in
this library discharges this. -/
public def AmplePowerSectionsCompleteFromDepth : Prop :=
  ∀ (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L],
    AlgebraicGeometry.Scheme.Modules.IsAmple X L →
    ∀ s : Γ(L, ⊤), DepthAddDimGtOneOutsideSupport X (zeroScheme X L s) →
      SectionsCompleteAmplePowers (zeroScheme X L s).subschemeι ∧
        ∀ W : Neighborhood X (zeroScheme X L s),
          SectionsCompleteAmplePowers (Neighborhood.toSchemeHom X (zeroScheme X L s) W)

/-! ### Tag 0ELC -/

/-- The implication `(2) ⇒ (3)` of [Stacks, Tag 0EKP], as a statement about general objects: the
first of the two implications of that tag which this library does not carry, and which
[Stacks, Tag 0EJZ] therefore asks for. -/
public def AmplePowersImpliesFiniteLocallyFreeSections : Prop :=
  ∀ {X Y : Scheme.{u}} [IsNoetherian X] (i : Y ⟶ X) [IsClosedImmersion i],
    SectionsCompleteAmplePowers i → SectionsCompleteFiniteLocallyFree i

/-- The implication `(3) ⇒ (4)` of [Stacks, Tag 0EKP], as a statement about general objects:
condition (3) gives full faithfulness of the completion functor on the finite locally free
coherent modules. This is the second implication of that tag which this library does not carry,
and which [Stacks, Tag 0EJZ] therefore asks for. -/
public def FiniteLocallyFreeSectionsImpliesCompletionFullyFaithful : Prop :=
  ∀ {X Y : Scheme.{u}} [IsNoetherian X] (i : Y ⟶ X) [IsClosedImmersion i],
    SectionsCompleteFiniteLocallyFree i →
      Stacks.Algebraization.CompletionFullyFaithfulOnFiniteLocallyFree X i.ker

/-- A scheme proper over a field carrying an ample invertible module is Noetherian: it is locally
Noetherian because a proper morphism is locally of finite type over the Noetherian base `Spec k`,
and quasi-compact because that is the first clause of
`AlgebraicGeometry.Scheme.Modules.IsAmple`. -/
public theorem isNoetherian_of_isProper_of_isAmple (k : Type u) [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsProper g] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) : IsNoetherian X := by
  have : IsNoetherianRing (CommRingCat.of k) := inferInstanceAs (IsNoetherianRing k)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace X := hL.1
  exact ⟨⟩

end Stacks.FundamentalGroup

end

end
