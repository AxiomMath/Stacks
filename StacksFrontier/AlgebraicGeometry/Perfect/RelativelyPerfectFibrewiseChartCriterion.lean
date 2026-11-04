module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectAffineCriterion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical
public import StacksFrontier.Homology.RelativelyPerfect.Criterion

/-!
# Relative perfectness from boundedness below of the derived fibres, on charts

Let `f : X ⟶ S` be flat and locally of finite presentation and let `E` be a pseudo-coherent
object of `D(𝒪_X)` all of whose cohomology sheaves are quasi-coherent. If on every affine
chart — an affine open `U ⊆ X` mapping into an affine open `V ⊆ S` — the complex of
`Γ(X, U)`-modules `RΓ(U, E)` is bounded below and has bounded below derived fibres
`RΓ(U, E) ⊗^L_{Γ(S, V)} κ(𝔭)` over every prime `𝔭` of `Γ(S, V)`, then `E` is `S`-perfect.

The argument is the one the proof of Stacks 0GEH makes after its reduction to the affine case:
the conditions are local, so Stacks 0DI2 reduces the conclusion to the affine charts, and on one
chart the assertion is the ring-level criterion Stacks 0GHJ for the flat finitely presented
algebra `Γ(S, V) ⟶ Γ(X, U)`.

**It is not the implication (2) ⟹ (1) of Stacks 0GEH**, and nothing in this module registers
that tag: the hypothesis is the *chart* reading of the source's condition (2), which is a
condition on sheaves, and the two readings are not identified in this library. The first
implementation note says what is owed.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_of_forall_chart_isBoundedBelow_and_fibres`:
  the composition of Stacks 0DI2 with Stacks 0GHJ.

## Implementation notes

**Which condition (2) this carries, and what separates it from the source's.** The source states
condition (2) on the sheaf side: `E` is locally bounded below on `X`, and for every point `s` of
`S` the derived fibre `L(X_s ⟶ X)^*E` is locally bounded below on `X_s`. The hypothesis below is
that condition read on the charts, where the ring-level criterion can consume it: boundedness
below of `RΓ(U, E)` in `D(Γ(X, U))`, and of its derived fibres over the primes of `Γ(S, V)` —
the two conditions of Stacks 0GHJ, which is the algebra lemma the source cites. The sheaf
reading is not known here to imply the chart reading, so what is below is a different statement
and not a weaker clause of the tag. Two identifications are owed.

*The fibre.* `RΓ(U ∩ X_s, L(X_s ⟶ X)^*E) ≅ RΓ(U, E) ⊗^L_{Γ(S, V)} κ(𝔭)` is Stacks 08IB, of which
the library carries only the Tor-independence input on a chart,
`AlgebraicGeometry.BaseChangeChart.isIso_derivedBaseChangeComparison` in
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/AffineChartComparison.lean`; its
globalisation Stacks 0DJ9 is proved only conditionally on the affine case of its own conclusion,
in `StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/GlobalBaseChange.lean`. The nearest
usable fragment is `Stacks.Cohomology.DerivedPullbackOfATilde.derivedPullbackTildeIso` in
`StacksFrontier/AlgebraicGeometry/DerivedTilde/DerivedPullbackOfATilde.lean`, which identifies the
derived pullback of the sheafification of a K-flat complex — and a pseudo-coherent `E|_U` has a
bounded above finite free, hence K-flat, representative.

*The first clause.* `AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow X.toRingedSpace E` has
to give one lower bound for `RΓ(U, E)` on an affine open `U`. On a quasi-compact space local
boundedness below is global, by
`AlgebraicGeometry.RingedSpace.exists_isGE_of_isLocallyBoundedBelow`, and a total right derived
functor of a left exact functor preserves a lower bound, by
`Stacks.DerivedFunctor.isGE_totalRightDerived_obj`; but the latter asks `E` to be bounded below
on the whole of `X`, and `X` is not assumed quasi-compact. What is missing is that `RΓ(U, -)`
annihilates an object whose restriction to `U` vanishes.

The standing hypothesis of Stacks 0GEH that `E` is pseudo-coherent is, by contrast, taken in the
source's own sheaf form; `AlgebraicGeometry.pseudoCoherent_derivedSections_tfae` is what moves it
onto the charts, where Stacks 0GHJ needs it.

**The algebra structure on the chart.** `𝒪_S(V)`-perfectness of `RΓ(U, E)` cannot be written
without a flat, finitely presented algebra structure on `Γ(X, U)` over `Γ(S, V)`; it is the one
of the chart ring map `f.appLE V U e`, exactly as
`AlgebraicGeometry.Scheme.Hom.SectionsRelativelyPerfect` takes it, and its two properties are
`AlgebraicGeometry.Scheme.Hom.moduleFlat_appLE` and
`AlgebraicGeometry.Scheme.Hom.algebraFinitePresentation_appLE`. That structure is introduced by
a `letI` in the hypothesis, since it depends on the inclusion `e : U ≤ f ⁻¹ᵁ V`.

**Which derived tensor product.** The derived fibre is taken at
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`, as Stacks 0GHJ states it,
and finite Tor dimension on the chart is measured against
`PseudoCoherence.canonicalDerivedTensoringDatum`, the datum
`AlgebraicGeometry.Scheme.Hom.SectionsRelativelyPerfect` is defined at. Nothing is quantified
over an unexhibited structure.

The conclusion is Stacks 0DI0 at the derived tensor product of Stacks 06YU,
`AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect`; clause (1) of Stacks 0DI2 is that predicate
on the nose by `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_canonicalFamily_iff`.

Nothing here is pinned to a universe: `X S : Scheme.{u}` and the rings of sections live in
`Type u`.

## References

* [Stacks Project, Lemma 36.35.13 (Tag 0GEH)](https://stacks.math.columbia.edu/tag/0GEH)
* [Stacks Project, Lemma 15.85.10 (Tag 0GHJ)](https://stacks.math.columbia.edu/tag/0GHJ)
* [Stacks Project, Lemma 36.35.3 (Tag 0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 20.55.3 (Tag 08IB)](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Relative perfectness from the chart reading of the fibrewise criterion.** Let `f : X ⟶ S`
be flat and locally of finite presentation and let `E` be a pseudo-coherent object of `D(𝒪_X)`
with quasi-coherent cohomology sheaves. Suppose that for every affine open `U ⊆ X` mapping into
an affine open `V ⊆ S` the complex `RΓ(U, E)` of `Γ(X, U)`-modules is bounded below and has
bounded below derived fibre `RΓ(U, E) ⊗^L_{Γ(S, V)} κ(𝔭)` for every prime `𝔭` of `Γ(S, V)`. Then
`E` is `S`-perfect.

The two conjuncts of `hchart` are the two conditions of Stacks 0GHJ for the chart ring map
`f.appLE V U e`, which is flat and of finite presentation; Stacks 0GHJ turns them, with the
chart reading of pseudo-coherence, into `Γ(S, V)`-perfection of `RΓ(U, E)`, which is clause (2)
of Stacks 0DI2, and clause (1) of Stacks 0DI2 is the conclusion.

**Three proved inputs are composed here, and no hypothesis is an unproved tag.**

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_tfae`, Stacks 0DI2, at `.out 2 1`: the
  reduction of relative perfectness to the affine charts. It is not assumed.
* `AlgebraicGeometry.pseudoCoherent_derivedSections_tfae`, the pseudo-coherence clause of
  Stacks 0DI2, at `.out 1 2`: it moves pseudo-coherence of `E` — which is the standing
  hypothesis of Stacks 0GEH and is taken here in the source's own sheaf form — onto the charts,
  which is where Stacks 0GHJ consumes it.
* `PseudoCoherence.isRelativelyPerfect_iff_isBoundedBelow_and_fibres_isBoundedBelow`,
  Stacks 0GHJ, in the direction `←`: the ring-level criterion, which is More on Algebra
  Lemma 15.85.10, the algebra lemma the proof of Stacks 0GEH cites.

**This is not the implication (2) ⟹ (1) of Stacks 0GEH, and it carries no attribute for that
tag.** The source's condition (2) is a condition on sheaves: `E` is locally bounded below on
`X`, and for every point `s` of `S` the derived fibre `L(X_s ⟶ X)^*E` is locally bounded below
on `X_s`. The hypothesis `hchart` is the *chart* reading of that condition, and the sheaf
reading is not known in this library to imply it, so the statement below is a different one and
not a sub-clause of the tag. Two identifications are owed, and the implementation notes of the
module record where each stands:

* the derived fibre on a chart, `RΓ(U ∩ X_s, L(X_s ⟶ X)^*E) ≅ RΓ(U, E) ⊗^L_{Γ(S, V)} κ(𝔭)`,
  which is Stacks 08IB — equivalently the affine case of Stacks 0DJ9;
* the locality statement for the first clause, that
  `AlgebraicGeometry.RingedSpace.IsLocallyBoundedBelow X.toRingedSpace E` gives a single lower
  bound for `RΓ(U, E)` on an affine open `U`. The left t-exactness available for the total right
  derived functor of sections, `Stacks.DerivedFunctor.isGE_totalRightDerived_obj`, asks `E` to be
  bounded below on the whole of `X`, and `X` is not assumed quasi-compact, so what is missing is
  that `RΓ(U, -)` annihilates an object whose restriction to `U` vanishes. -/
public theorem isRelativelyPerfect_of_forall_chart_isBoundedBelow_and_fibres [Flat f]
    [LocallyOfFinitePresentation f] (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (hpc : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (hchart : ∀ (U : X.Opens) (_ : IsAffineOpen U) (V : S.Opens) (_ : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      (∃ a : ℤ, ((derivedSectionsUnbounded X U).obj E).IsGE a) ∧
        ∀ p : PrimeSpectrum Γ(S, V), ∃ a : ℤ,
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap Γ(S, V) p.asIdeal.ResidueField)).functor.obj
            ((ModuleCat.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).mapDerivedCategory.obj
              ((derivedSectionsUnbounded X U).obj E))).IsGE a) :
    f.IsRelativelyPerfect E := by
  have hpcsec := ((pseudoCoherent_derivedSections_tfae f E hE).out 1 2).1 hpc
  have hsec : ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V), SectionsRelativelyPerfect f E hV hU e := by
    intro U hU V hV e
    obtain ⟨hbdd, hfib⟩ := hchart U hU V hV e
    let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    let : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hU e rfl
    let : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
      algebraFinitePresentation_appLE f hV hU e rfl
    exact (PseudoCoherence.isRelativelyPerfect_iff_isBoundedBelow_and_fibres_isBoundedBelow
      (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).tensor
      (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).comparison
      (PseudoCoherence.canonicalDerivedTensoringDatum Γ(S, V)).isLeftDerived _
      (hpcsec U hU V hV e)).2 ⟨hbdd, hfib⟩
  exact (isPerfectRelativeTo_canonicalFamily_iff f E).1
    (((isPerfectRelativeTo_tfae f E hE).out 2 1).1 hsec)

end AlgebraicGeometry.Scheme.Hom

end
