module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.RingTheory.TensorProduct.Finite
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsComp
public import StacksFrontier.RingTheory.Dualizing.ExternalTensorFlat
public import StacksFrontier.RingTheory.Dualizing.RelativeCoprojections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composing relative dualizing complexes: the diagonal of a composite

Let `R → A → B` be flat ring maps of finite presentation, let `K_{A/R}` be a relative dualizing
complex for `R → A` and `K_{B/A}` one for `A → B`, both in the sense of [stacks 0E2C],
`Dualizing.IsRelativeDualizingComplex`.  [stacks 0E2H] asserts that
`K = K_{A/R} ⊗ᴸ_A K_{B/A}` is a relative dualizing complex for `R → B`.

**[stacks 0E2H] is not proved here, and nothing in this file carries its attribute.**  What is
proved is the part of the argument that is unconditional: the relative diagonal of the composite
factors through the relative diagonal of `A → B`, and both the derived base change along the
left coprojection and derived Hom from the diagonal are computed in two steps along that
factorisation.  That reduces the diagonal condition of [stacks 0E2C] for `R → B` to a single
isomorphism, which is isolated as the hypothesis of
`Dualizing.diagonalDerivedHom_of_diagonalQuotientIso`.  The last section of this docstring
records why that isomorphism is not available, and the witness that defeats every invertibility
criterion the library has for it.

## Main definitions

* `Dualizing.diagonalQuotient` — the surjection `B ⊗[R] B → B ⊗[A] B`.
* `Dualizing.diagonalBaseMap` — the map `A ⊗[R] A → B ⊗[R] B` of diagonals.
* `Dualizing.diagonalPushoutEquiv` — the identification `B ⊗[A] B ≅ A ⊗[A ⊗[R] A] (B ⊗[R] B)`
  exhibiting `B ⊗[A] B` as the base change of the diagonal `A` along the map of diagonals.

## Main results

* `Dualizing.lmul'_comp_diagonalQuotient` — the diagonal of `R → B` is the diagonal of `A → B`
  precomposed with `Dualizing.diagonalQuotient`; and
  `Dualizing.diagonalQuotient_comp_includeLeftRingHom`, the same for the left coprojections.
* `Dualizing.flat_diagonalBaseMap` — for `B` flat over `A`, the map of diagonals
  `A ⊗[R] A → B ⊗[R] B` is flat; and `Dualizing.diagonalQuotient_comp_diagonalBaseMap`, that it
  carries the diagonal of `R → B` to the diagonal of `R → A`, so that
  `Dualizing.diagonalQuotient` lies over the diagonal `A ⊗[R] A → A`.
* `Dualizing.diagonalPushoutEquiv` — **the square above is a pushout.**  Writing `C = B ⊗[R] B`,
  `C' = B ⊗[A] B` and `D = A ⊗[R] A`, the canonical map `A ⊗[D] C → C'` is an isomorphism of
  `A`-algebras; equivalently `Dualizing.diagonalQuotient` is the base change along the flat map
  `D → C` of the diagonal `D → A`.
* `Dualizing.diagonalBaseMap_comp_includeLeftRingHom` — the left coprojection `A → C` factors
  through `D`; and `Dualizing.diagonalDerivedExtensionBaseChangeIso`, its derived consequence,
  that `K ⊗ᴸ_A C` is the derived base change along `D → C` of `K ⊗ᴸ_A D`.  So the untwisted
  tensor factor `X = K_{A/R} ⊗ᴸ_A C` of the discussion below is extended from `D`.
* `Dualizing.totalDerivedExtensionScalarsSingleIsoOfFlat` — derived extension of scalars along a
  flat ring map carries a module in degree zero to its base change in degree zero; and
  `Dualizing.diagonalDerivedExtensionSingleIso`, the case of `D → C` at the diagonal `A`, which
  identifies the derived base change of `A[0]` with `C'[0]`.  `Dualizing.diagonalPushoutEquiv`
  supplies the module-level input through `Dualizing.diagonalPushoutModuleEquiv`, the `C`-linear
  form `C ⊗[D] A ≅ C'`.
* `Dualizing.flat_tensorProduct`, `Dualizing.finitePresentation_tensorProduct` — the degreewise
  content of transitivity of relative perfection: for `P` an `A`-module flat over `R` and finitely
  presented over `A`, and `Q` a `B`-module flat over `A` and finitely presented over `B`, the
  module `Q ⊗[A] P` is flat over `R` and finitely presented over `B`.  Transitivity itself is
  `Dualizing.isRelativelyPerfect_derivedTensorProductOver` in
  `StacksFrontier.RingTheory.Dualizing.RelativePerfectionTransitivity`, which consumes these two.
* `Dualizing.derivedHomDiagonalCompIso` — derived Hom from the diagonal of `R → B` is derived
  Hom along `Dualizing.diagonalQuotient` followed by derived Hom from the diagonal of `A → B`.
  This is [stacks 0C0F] at the above factorisation.
* `Dualizing.diagonalDerivedExtensionCompIso` — derived base change to `B ⊗[R] B` followed by
  derived base change along `Dualizing.diagonalQuotient` is derived base change to `B ⊗[A] B`.
* `Dualizing.diagonalDerivedHom_of_diagonalQuotientIso` — **the reduction.**  The diagonal
  condition of [stacks 0E2C] for `R → B` at `K` follows from the diagonal condition for `A → B`
  at `L` together with one isomorphism, namely that derived Hom along
  `Dualizing.diagonalQuotient` carries the derived base change of `K` to `B ⊗[R] B` onto the
  derived base change of `L` to `B ⊗[A] B`.

## Why the source's route is not taken

[stacks 0E2H] is proved in the source by reducing to a Noetherian base with [stacks 02JO] and
[stacks 0E2D], [stacks 0E2E], [stacks 0E2F], and then identifying `K_{A/R} ≅ φ^!(R)`,
`K_{B/A} ≅ ψ^!(A)` and `φ^!(R) ⊗ᴸ_A ψ^!(A) ≅ (ψ ∘ φ)^!(R)` by [stacks 0BZU] and [stacks 0BZT].
In this library [stacks 0BZT] is available only for a surjective second map, and [stacks 0BZU]
is unconditional but only at module universe equal to the ring universe
(`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_iso_derivedTensorProduct`, with
its carried conclusion of [stacks 0BZE] discharged); [stacks 0E2D] and [stacks 0E2F] each carry a
documented open hypothesis (`hdiag`, respectively `Dualizing.DiagonalDerivedHomBaseChange`).  So
that route cannot be assembled.  The route below goes straight from the definition
[stacks 0E2C], and carries nothing.

## The direct route, and the one step that is missing

Write `C = B ⊗[R] B`, `C' = B ⊗[A] B` and `D = A ⊗[R] A`, and let `p : B → C` and `p' : B → C'`
be the left coprojections.  The diagonal `Δ_{B/R} : C → B` factors as
`C --f--> C' --Δ_{B/A}--> B` with `f = Dualizing.diagonalQuotient`
(`Dualizing.lmul'_comp_diagonalQuotient`), and `p' = f ∘ p`
(`Dualizing.diagonalQuotient_comp_includeLeftRingHom`).  Hence, by [stacks 0C0F] and by
transitivity of derived extension of scalars,

`RHom_C(B, K ⊗ᴸ_B C) = RHom_{C'}(B, RHom_C(C', K ⊗ᴸ_B C))`  and  `K ⊗ᴸ_B C'
  = (K ⊗ᴸ_B C) ⊗ᴸ_C C'`,

which are `Dualizing.derivedHomDiagonalCompIso` and `Dualizing.diagonalDerivedExtensionCompIso`.
So the diagonal condition for `R → B` at `K` follows from the one for `A → B` at `K_{B/A}` as
soon as

  (★)  `RHom_C(C', K ⊗ᴸ_B C) ≅ K_{B/A} ⊗ᴸ_B C'`,

and that is exactly the hypothesis of
`Dualizing.diagonalDerivedHom_of_diagonalQuotientIso`.

**(★) is a projection formula at a base-change square, with a twist that has no Tor-amplitude
bound.**  Indeed `C' = C ⊗_D A`, so `f` is the base change of `Δ_{A/R} : D → A` along `D → C`,
and `C` is flat over `D` because `B` is flat over `A`.  Writing
`K ⊗ᴸ_B C ≅ (K_{A/R} ⊗ᴸ_A C) ⊗ᴸ_C Y` with `Y = K_{B/A} ⊗ᴸ_B C`, the *untwisted* half of (★),

  `RHom_C(C', K_{A/R} ⊗ᴸ_A C) ≅ C'`,

is [stacks 0A6A] (3) — `Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange`, flat case —
applied at `D → C`: the internal-Hom source is the diagonal `A`, pseudo-coherent over `D` by
`Dualizing.isPseudoCoherent_diagonal`, the target is bounded below because `K_{A/R}` is
`R`-perfect, and `D → C` is flat.  **That derivation is carried out**, as
`Dualizing.nonempty_internalHom_diagonalQuotient_untwisted` of
`StacksFrontier.RingTheory.Dualizing.RelativeCompositionUntwisted`, which carries nothing beyond the
hypotheses on `K_{A/R}`.  It is an isomorphism of `D(C)`, so what it leaves open of the
untwisted half is its *descent to `D(C')`*, for the same reason (★) itself needs one.  **What is
missing besides that descent is the twist by `Y`**, that is the tensor–Hom diagonal

  `Y ⊗ᴸ_C RHom_C(C', X) ⟶ RHom_C(C', Y ⊗ᴸ_C X)`,

and none of the four criteria of [stacks 0ATK],
`Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal`, applies to it:

* `Y` is not perfect over `C`, nor is `X = K_{A/R} ⊗ᴸ_A C`, nor is `C'`: being a quotient of `C`
  by the ideal generated by the diagonal ideal of `A` over `R`, `C'` has no reason to have finite
  projective dimension;
* `Y` has no lower bound on its Tor amplitude over `C`, which is what the third and fourth
  criteria need.  This is defeated by the single witness already recorded in
  `StacksFrontier.RingTheory.Dualizing.RelativeUniqueness`: take `R = A = k` a field,
  `B = k[x, y]/(x, y)²` and `K_{B/A} = Hom_k(B, k)`, which is a relative dualizing complex for
  `k → B`.  The coprojection `p` is flat, so tensoring `Y = K_{B/A} ⊗ᴸ_B C` with the residue
  field of `C` gives `K_{B/A} ⊗ᴸ_B k`, and `K_{B/A}` has two generators and length three over
  the Artinian local ring `B`, hence is not free, hence has infinite projective dimension and
  `Tor_i^B(K_{B/A}, k) ≠ 0` for every `i`.

So (★) is not a corollary of the library's unconditional invertibility criteria, and adding a
perfection or Tor-dimension hypothesis to [stacks 0E2H] would not be the tag.

## Why the degreewise route through [stacks 0E1U] is not the repair

The obvious repair is the one the source uses wherever [stacks 0A6A] is unavailable: produce by
[stacks 0E1U], `StacksDraft.RelativelyPerfect.exists_homComplex_representation`, a bounded below
complex `H` of `C`-modules, flat over `R` and finitely presented over `C`, representing
`RHom_C(C', X)` compatibly with derived base change, and read (★) off it degree by degree.  **That
does not work, and the reason is not a gap in the library.**  Reading the twist off `H` degreewise
requires the chain-level tensor product `Y ⊗_C H` to compute `Y ⊗ᴸ_C H`, and neither factor is
`K`-flat over `C`: `H` is bounded *below* with flat terms, and such a complex is not `K`-flat —
[stacks 064K], `CochainComplex.KFlat.kFlat_of_flat`, asks for a bound *above*, and the increasing
filtration of a cochain complex by bounded subcomplexes that would reduce the bounded-below case
to the bounded one runs the wrong way, the degreewise truncations keeping low degrees being
quotients and not subobjects.  The discrepancy is not hypothetical: a tensor factor that is only
bounded with terms flat over a *subring* — which is all that `Y = K_{B/A} ⊗ᴸ_B C` is, its terms
being flat over `A` and not over `C` — is exactly the situation of the witness recorded in the
documentation of
`Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_relativeKFlat`, where the two
sides of the diagonal have cohomology `k^{(ℕ)}` and `k^ℕ` in every degree.

## The route that does work, and the two transports it needs

What `Y` fails over `C` it passes over `D`, and **that half is now proved**: it is
`Dualizing.isIso_derivedTensorHomDiagonal_diagonal_composite` in
`StacksFrontier.RingTheory.Dualizing.RelativeCompositionTorAmplitude`, which carries nothing beyond
relative perfection of the two given complexes.  Choose by [stacks 0DHV],
`PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation`, a bounded
complex `Q` representing `K_{B/A}` whose terms are flat over `A` and finitely presented over `B`.
The terms of `Q ⊗_B C` are `Q^i ⊗_B (B ⊗[R] B) = Q^i ⊗[R] B`, an external tensor product of two
`A`-flat modules, and such a module is flat over `D = A ⊗[R] A`
(`Dualizing.flat_restrictScalars_diagonalExtendScalars`, the first consumer of
`Dualizing.flat_extTensor`); `Q ⊗_B C` is bounded, so it is then `K`-flat over `D` by
[stacks 064K], and it represents `Y` over `D` because the left coprojection `B → C` is flat
(`Dualizing.exists_kFlat_flat_representative_restrictScalars_diagonalDerivedExtension`).  So `Y`
*does* have Tor amplitude bounded below over `D`
(`Dualizing.torAmplitudeAbove_restrictScalars_diagonalDerivedExtension`, which is [stacks 0BYL]
at that representative), and [stacks 0ATK] (3) does apply to the diagonal taken over `D`,

  `Y ⊗ᴸ_D RHom_D(A, X_D) ⟶ RHom_D(A, Y ⊗ᴸ_D X_D)`,   `X_D = K_{A/R} ⊗ᴸ_A D`,

the internal-Hom source `A` being pseudo-coherent over `D` by `Dualizing.isPseudoCoherent_diagonal`
and the target bounded below because `K_{A/R}` is `R`-perfect
(`Dualizing.exists_isGE_diagonalDerivedExtension_of_relativelyPerfect`).

That the diagonal over `D` computes the right thing is what
`Dualizing.diagonalDerivedExtensionBaseChangeIso` is for: it says `X ≅ X_D ⊗ᴸ_D C`, whence
`Y ⊗ᴸ_C X ≅ Y ⊗ᴸ_C (C ⊗ᴸ_D X_D) ≅ Y_D ⊗ᴸ_D X_D`, so the *internal* diagonal of the single ring
`D` — the only one [stacks 0ATK] provides — has for target exactly `RHom_D(A, (Y ⊗ᴸ_C X)_D)`,
`Y ⊗ᴸ_C X` being `K ⊗ᴸ_B C`.  Its source is `Y_D ⊗ᴸ_D RHom_D(A, X_D) ≅ Y_D ⊗ᴸ_D A`, since
`RHom_D(A, X_D) ≅ A` is the diagonal condition of [stacks 0E2C] for `R → A` at `K_{A/R}`; and
`Y_D ⊗ᴸ_D A ≅ Y ⊗ᴸ_C (C ⊗ᴸ_D A) ≅ Y ⊗ᴸ_C C' ≅ K_{B/A} ⊗ᴸ_B C'` is the right-hand side of (★),
using `C' ≅ A ⊗_D C` — which is `Dualizing.diagonalPushoutEquiv`.  So the mathematics of (★) is
settled; what is missing is formal, and it is two transports:

* **Coextension of scalars along a base change.**  `C' ≅ A ⊗_D C` by
  `Dualizing.diagonalPushoutEquiv`, so `Hom_C(C ⊗_D A, W) = Hom_D(A, W)` as `C'`-modules, the
  `C`-action coming from `W`.  Its *derived* content is already in this library: [stacks 0E1W],
  `Stacks.DerivedHom.ExtensionOfScalars.derivedHomRestrictScalarsNatIso`, gives
  `RHom_D(K, W|_D) ≅ RHom_C(K ⊗ᴸ_D C, W)|_D` for every `K` in `D(D)` and `W` in `D(C)`; at
  `K = A[0]` that is the statement wanted, *read in `D(D)`*.  The first of the two steps this
  left is now done: `Dualizing.diagonalDerivedExtensionSingleIso` is the comparison of complexes
  identifying the derived base change of `A[0]` along `D → C` with `C'[0]`.  What is still left
  is the passage from `D(D)` to `D(C')`, for which restriction along `D → C'` reflects
  isomorphisms (`CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory` at
  `ModuleCat.restrictScalars`) but the `C'`-linear morphism to be inverted has first to exist,
  which is the second transport.
* **A `C'`-linear tensor--Hom diagonal.**  (★) is an isomorphism in `D(C')`, so the morphism it
  inverts is a diagonal `Y ⊗ᴸ_C RHom_C(C', -) ⟶ RHom_C(C', Y ⊗ᴸ_C -)` of functors
  `D(C) ⥤ D(C')`, the source being derived Hom *along a ring map* and not the internal Hom of one
  ring.  [stacks 0ATK] and `StacksDraft.DerivedHom.derivedTensorHomDiagonal` only provide the
  internal diagonal of a single ring (`StacksDraft.DerivedHom.DerivedInternalHom.Model.diagonal`,
  built from the coevaluation and composition of one ring's internal-Hom bifunctor), and no such
  natural transformation is constructed anywhere here.  Nor does the fourth criterion
  `Stacks.DerivedTensorHomDiagonal.isIso_derivedTensorHomDiagonal_of_relativeKFlat` substitute
  for it: that asks for the tensor factor to be *extended* from a `K`-flat complex over the
  subring, and `Y = K_{B/A} ⊗ᴸ_B C` is not extended from `D` — its terms `Q^i ⊗[R] B` would have
  to be `C ⊗_D P^i`, which forces `Q^i ≅ B ⊗_A M` for some `A`-module `M`.

  **The source functor itself is the obstruction, and it is a missing bifunctor.**  `Y ⊗ᴸ_C -`
  read on `D(C')` is a derived tensor product over `C` of a *fixed* object of `D(C)` with a
  *varying* object of `D(C')`, valued in `D(C')`; no such bifunctor `D(C) × D(C') ⥤ D(C')`
  exists in this library for a ring map.  What exists is the opposite slot:
  `CochainComplex.DerivedTensor.DerivedTensorChangeOfRings` and its packaging
  `Dualizing.derivedTensorProductOver` tensor a *varying* object of `D(C)` with a *fixed* object
  of `D(C')`, and partial application in the other variable is not available.  Of the two routes
  out of this, the second is the one taken: rewrite the source by associativity as
  `(- ⊗ᴸ_{C'} (Y ⊗ᴸ_C C'))`, that is
  `Dualizing.ProjectionFormula.tensorRightDerived C' ((K_{B/A} ⊗ᴸ_B C') )`.  That route needs no
  new bifunctor, and it turns out to need no transport either: the projection formula
  `Dualizing.ProjectionFormula.derivedProjNatIso` *is* the required comparison, and mating it
  across the adjunction of [stacks 0A70] produces the morphism directly.  It is
  `Dualizing.ProjectionFormula.derivedTensorHomDiagonalAlongRingHom`, with the canonical
  instantiation `derivedTensorHomDiagonalRestrictScalars` and the characterisation
  `homEquiv_derivedProjDiagonalTranspose` that determines it uniquely.  The first route — build
  the missing bifunctor, for which the structure above is the template and
  `Stacks.Cohomology.MixedDerivedTensor.mixedDerivedTensorPullback` (`D(O) × D(O') ⥤ D(f⁻¹O')`,
  the ringed-topos analogue of [stacks 08I6]) the structural precedent — is therefore not needed.

  What remains is *invertibility*, and it is two comparisons rather than one.  The diagonal
  above is a morphism of `D(C')`, and the only handle on it is conservativity of restriction;
  but restricting along `φ` lands over `C`, not over `D`, and
  `Res_{D → C'} = Res_{D → C} ∘ Res_φ`, so going straight to `D(D)` does not avoid the second
  step.  Writing `X = K_{A/R} ⊗ᴸ_A C` and `Y = K_{B/A} ⊗ᴸ_B C`:

  * **Comparison I** — that `Res_φ` of the along-ring-map diagonal is the single-ring diagonal
    of `C` at `(Y, X, C'[0])`.  Transposing both sides through
    `Dualizing.derivedCoextendRestrictScalars_adj`, or equivalently
    `Dualizing.restrictScalarsDerived_adj_derivedHom` ([stacks 0A70]), and using
    `Dualizing.ProjectionFormula.homEquiv_derivedProjDiagonalTranspose` and
    `Dualizing.derivedTensorHomDiagonalOverRing_homEquiv` reduces this to a single equation:
    that the projection formula is compatible with the counit of extension ⊣ restriction and
    with the derived associator.  Comparison I is worth having on its own, as the general
    statement that the diagonal along a ring map, restricted along that map, is the internal
    diagonal at the algebra; it would also give the along-ring-map diagonal its first consumer.

    **What of Comparison I is now proved**, in
    `StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCounit`: its *counit half*
    and the reduction of the owed equation to chain level.  The counit half is
    `Dualizing.ProjectionFormula.restrict_derivedTensorHomDiagonalAlongRingHom_comp_counit` —
    `Res_φ` of the along-ring-map diagonal, composed with the counit of [stacks 0A70], is the
    projection formula followed by that counit in the first tensor factor — together with
    `Dualizing.ProjectionFormula.eq_derivedTensorHomDiagonalAlongRingHom_iff`, which says that
    equation *characterises* the diagonal along `φ`, so a candidate identification may be
    checked against the projection formula and the counit with the along-ring-map diagonal no
    longer mentioned.  The owed equation itself is now stated,
    `Dualizing.ProjectionFormula.ProjCounitCompat`, and two things are known about it.
    `Dualizing.ProjectionFormula.projCounitCompat_iff` **transposes the lax monoidal structure
    map away**: both `Dualizing.derivedTensorBaseChange` and the derived-Hom base-change
    morphism of [stacks 0E1X] that it is a double transpose of disappear, leaving a closed
    formula for the *inverse* projection formula as a transpose of the counit read backwards
    through [stacks 0E1W].  And `Dualizing.ProjectionFormula.projCounitCompat_of_kFlat`
    **reduces it to representatives**: both sides are natural in both variables
    (`projCounitCompat_of_rep` in the object of `D(C')`, `projCounitCompatAt_of_iso` in the
    object of `D(C)`), so it is enough to prove the equation at the class of a K-flat complex
    and the class of an arbitrary complex — the situation in which the projection formula has a
    value, `Dualizing.ProjectionFormula.derivedProjNatIso_hom_app_Q`, the counit has one,
    `CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_counit_app_eq`,
    and the structure map has one through
    `Dualizing.derivedTensorBaseChange_comp_map`.  What remains of `ProjCounitCompat` itself is
    therefore exactly a pasting of chain-level comparisons: it still has to be done at chain
    level, because `Dualizing.ProjectionFormula.derivedProjNatIso` has no adjunction-level or
    monoidal characterisation — it is descended from pasted chain-level comparisons and is
    pinned only by `derivedProjKFlat_hom_app_Q`, `derivedProjNatIso_hom_app_Q` and two
    naturality lemmas — but of *that equation* no further reduction, invertibility criterion or
    choice of representative is needed.  The same is not true of Comparison I as a whole; the
    next paragraph says what Comparison I costs.

    **Comparison I is proved against two named coherences.**  The object it needs is
    a morphism `Res_φ ∘ derivedHom φ ⟶ hom(op C'[0], −)`.  It exists, and is an
    isomorphism, as `Dualizing.ProjectionFormula.restrictCoextendInternalHomIso` in
    `StacksFrontier.RingTheory.Dualizing.UpperShriek.RestrictedCoextension`: both functors are right
    adjoints — the first by [stacks 0GMT] and [stacks 0A70] composed, the second by [stacks 0A63]
    — of left adjoints identified by `Dualizing.ProjectionFormula.restrictExtendIso`, which is the
    projection formula at the tensor unit of `D(C')`.  With it,
    `Dualizing.ProjectionFormula.restrict_derivedTensorHomDiagonalAlongRingHom_eq_diagonal` is
    Comparison I as a commuting square of morphisms of `D(C)`, and
    `Dualizing.ProjectionFormula.isIso_restrict_derivedTensorHomDiagonalAlongRingHom` transports
    the invertibility.  Both take one hypothesis: that the projection formula is linear for
    `Dualizing.ProjectionFormula.restrictedAction`, the action of the algebra on a restricted
    object.  **That hypothesis is not `ProjCounitCompat`**.  The
    derivation is in
    `StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalComparisonBridge`: cancelling the
    algebra action off both sides, `restrictedAction_comp_derivedProj_iff`, leaves the
    restricted counit against the projection formula, and
    `restrictedAction_comp_derivedProj_of_projCounitCompatAt` supplies the linearity from
    `ProjCounitCompatAt` **together with** a second coherence,
    `Dualizing.ProjectionFormula.ProjTensorBaseChangeCompat`, in which neither counit nor any
    object of `D(C')` occurs.  The two are not independent:
    `Dualizing.ProjectionFormula.projTensorBaseChangeCompat_iff_canonical` in
    `StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCanonical` shows that
    granted `ProjCounitCompatAt` at the three pairs the second coherence mentions the
    projection formula at, it becomes
    `Dualizing.ProjectionFormula.CanonicalProjTensorBaseChangeCompat` — an identity in which no
    projection formula occurs at all, built from the unit and counit of [stacks 0GMT], the
    section of the lax monoidal structure map of derived base change, and the symmetric
    monoidal structure of [stacks 0A63].  So the residue of this bullet is `ProjCounitCompat`
    and the associativity of that structure map, which this library nowhere records.
  * **Comparison II** — that `C`-diagonal against the `D`-internal one at
    `(Res_{D → C} Y, X_D, A[0])`, under `Dualizing.diagonalDerivedExtensionBaseChangeIso` and
    `Dualizing.diagonalDerivedExtensionSingleIso` / `Dualizing.diagonalPushoutEquiv`, which is
    where [stacks 0ATK] (3) becomes usable.  Over `C` itself no disjunct of 0ATK applies: the
    witness recorded below kills the Tor-amplitude one, `C'` is not perfect over `C`, and the
    relative-K-flat disjunct needs `Y` extended from `D`, which the witness below also refutes.
    Descending to `D` needs compatibility of [stacks 0E1W] with evaluation, and 0E1W is itself
    pinned only on K-flat/K-injective representatives, so that is a second chain-level
    coherence of the same kind; no lemma anywhere relates 0E1W to a diagonal.

  **Comparisons I and II are the whole of what is owed.**  The invertibility they are there to
  transport is no longer owed: the `D`-internal diagonal at `(Y_D, X_D, A[0])` is an
  isomorphism, unconditionally, by
  `Dualizing.isIso_derivedTensorHomDiagonal_diagonal_composite` in
  `StacksFrontier.RingTheory.Dualizing.RelativeCompositionTorAmplitude`.  So the residue of (★) is
  purely an identification of morphisms — two equations, each between a diagonal already
  constructed in this library and another one already constructed in it — and no further
  invertibility criterion, Tor-amplitude bound or choice of representative is involved.

  The step is not a single comparison with the diagonal over `D`, for the reason given above:
  restriction along `φ` cannot reach `D` in one step.

What this file supplies of that route is the algebra it rests on: `Dualizing.diagonalBaseMap` with
`Dualizing.flat_diagonalBaseMap` and `Dualizing.diagonalQuotient_comp_diagonalBaseMap`, which say
that `D → C` is flat and that `Dualizing.diagonalQuotient` lies over the diagonal `D → A`; the
pushout property itself, `Dualizing.diagonalPushoutEquiv`; and the factorisation of the left
coprojection through the diagonal with its derived consequence,
`Dualizing.diagonalBaseMap_comp_includeLeftRingHom` and
`Dualizing.diagonalDerivedExtensionBaseChangeIso`.  The algebraic step that gives `Y` its
Tor-amplitude bound over `D` — the flatness over `D = A ⊗[R] A` of an external tensor product
`M ⊗[R] N` of two `A`-flat modules, which is what makes the terms of `Q ⊗_B C` flat over `D` — is
`Dualizing.flat_extTensor` in `StacksFrontier.RingTheory.Dualizing.ExternalTensorFlat`, proved there
for two `R`-algebras `S` and `T` and specialised to `S = T = A` by applying it to the two
`A`-module structures explicitly.  It is not an instance of `Dualizing.flat_tensorProduct` below,
whose conclusion is flatness over the base `R` of a tensor product taken over an intermediate
ring; here the two factors are tensored over the base and the flatness is asserted over the
tensor product of the intermediate ring with itself.  Its passage from the terms to the complex
and on to the Tor-amplitude bound is
`StacksFrontier.RingTheory.Dualizing.RelativeCompositionTorAmplitude`.

## What else [stacks 0E2H] needs, and where it is now proved

Clause (1) of [stacks 0E2C] for `K` is **transitivity of relative perfection**: `K_{A/R}` is
`R`-perfect in `D(A)`, `K_{B/A}` is `A`-perfect in `D(B)`, and one wants
`K_{A/R} ⊗ᴸ_A K_{B/A}` to be `R`-perfect in `D(B)`.  The source does not state it: §15.85 has
only [stacks 0DHU] (perfect tensor relatively perfect, over a fixed base) and [stacks 0DHW]
(base change of the base ring), and [stacks 0E2H] never needs it because the identification with
`(ψ ∘ φ)^!(R)` supplies relative perfection for free.  **It is now proved directly**, in
`StacksFrontier.RingTheory.Dualizing.RelativePerfectionTransitivity`, as
`Dualizing.isRelativelyPerfect_derivedTensorProductOver`.

The degreewise content is this file's: `Dualizing.flat_tensorProduct` and
`Dualizing.finitePresentation_tensorProduct` give that for `P` an `A`-module flat over `R` and
finitely presented over `A`, and `Q` a `B`-module flat over `A` and finitely presented over `B`,
the module `Q ⊗[A] P` is flat over `R` and finitely presented over `B`.  [stacks 0DHV] is an
equivalence, so it reduces both hypotheses and the conclusion to bounded models with exactly
those termwise properties; the object `K_{A/R} ⊗ᴸ_A K_{B/A}` is a derived tensor product over `A`
of a varying object of `D(A)` with the fixed object `K_{B/A}` of `D(B)`, so — unlike the source
functor of (★) — it *is* expressible with what the library has, namely
`Dualizing.derivedTensorProductOver (algebraMap A B) K_{B/A}`.

The passage from the terms to the complexes is what the cited file adds.  Note which factor
carries the `K`-flatness: the *fixed* one.  The varying model has terms flat over `R`, not over
`A`, so it is not `K`-flat over `A` and the counit of the derived functor is not invertible at it
for that reason; but the fixed model is bounded with `A`-flat terms, hence `K`-flat over `A` by
[stacks 064K], and so the chain-level tensor-total functor already inverts quasi-isomorphisms —
its underlying complex of `A`-modules is a total tensor product with that `K`-flat complex, and
restriction of scalars reflects quasi-isomorphisms.  A left derived functor of a functor
inverting the weak equivalences has invertible counit, which makes the comparison hold at *every*
complex (`Dualizing.isIso_alphaF_of_kFlat_restrictScalars`).  Boundedness of the total complex is
read off the same underlying complex of `A`-modules.

## References

* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0C0F](https://stacks.math.columbia.edu/tag/0C0F)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0DHV](https://stacks.math.columbia.edu/tag/0DHV)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- The canonical surjection `B ⊗[R] B → B ⊗[A] B`. -/
def diagonalQuotient : (B ⊗[R] B) →ₐ[R] (B ⊗[A] B) :=
  Algebra.TensorProduct.lift
    (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[A] B)
    ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).restrictScalars R)
    fun _ _ => Commute.all _ _

/-- The surjection `B ⊗[R] B → B ⊗[A] B` on a homogeneous tensor. -/
@[simp]
theorem diagonalQuotient_tmul (b₁ b₂ : B) :
    diagonalQuotient R A B (b₁ ⊗ₜ[R] b₂) = b₁ ⊗ₜ[A] b₂ := by
  simp [diagonalQuotient]

/-- The map `B ⊗[R] B → B ⊗[A] B` is surjective: `B ⊗[A] B` is a quotient of `B ⊗[R] B`, so
the relative diagonal of `A → B` is a closed subscheme of the relative diagonal of `R → B`. -/
theorem surjective_diagonalQuotient : Function.Surjective (diagonalQuotient R A B) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul b₁ b₂ => exact ⟨b₁ ⊗ₜ[R] b₂, by simp⟩
  | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy']⟩

/-- **The diagonal of a composite factors.**  The multiplication map `B ⊗[R] B → B` is the
multiplication map `B ⊗[A] B → B` precomposed with the surjection `B ⊗[R] B → B ⊗[A] B`. -/
theorem lmul'_comp_diagonalQuotient :
    (Algebra.TensorProduct.lmul' A (S := B)).toRingHom.comp
        (diagonalQuotient R A B).toRingHom =
      (Algebra.TensorProduct.lmul' R (S := B)).toRingHom := by
  apply RingHom.ext
  intro z
  simp only [RingHom.comp_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b₁ b₂ => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- **The diagonal of a composite, read on derived Hom.**  Derived Hom from the diagonal of
`R → B` is derived Hom from the diagonal of `A → B` applied after derived Hom along the
surjection `B ⊗[R] B → B ⊗[A] B`.  This is [stacks 0C0F] at the factorisation
`Dualizing.lmul'_comp_diagonalQuotient`. -/
theorem derivedHomDiagonalCompIso :
    Nonempty
      (derivedHom.{u, u} (diagonalQuotient R A B).toRingHom ⋙
          derivedHom.{u, u} (Algebra.TensorProduct.lmul' A (S := B)).toRingHom ≅
        derivedHom.{u, u} (Algebra.TensorProduct.lmul' R (S := B)).toRingHom) := by
  rw [← lmul'_comp_diagonalQuotient R A B]
  exact derivedHomCompIso _ _

/-- The surjection `B ⊗[R] B → B ⊗[A] B` carries the left coprojection of `B ⊗[R] B` to the
left coprojection of `B ⊗[A] B`. -/
theorem diagonalQuotient_comp_includeLeftRingHom :
    (diagonalQuotient R A B).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B) =
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B) := by
  apply RingHom.ext
  intro b
  simp [diagonalQuotient]

variable [Module.Flat R A] [Module.Flat A B]

/-- Derived base change of `K` along the left coprojection `A → A ⊗[R] A` and then along `g` is
derived base change along any `h` that `g` factors through the coprojection. -/
private theorem nonempty_totalDerived_obj_diagonalDerivedExtension {Q : Type u} [CommRing Q]
    (g : A ⊗[R] A →+* Q) (h : A →+* Q)
    (hg : g.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) = h)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty ((totalDerivedExtensionScalars.{u, u, u} g).functor.obj
        ((diagonalDerivedExtension R A).obj K) ≅
      (totalDerivedExtensionScalars.{u, u, u} h).functor.obj K) := by
  subst hg
  exact ⟨(totalDerivedExtensionScalars.{u, u, u} g).functor.mapIso
      ((diagonalDerivedExtensionIsoTotalDerived R A).app K).symm ≪≫
    (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) g).app K⟩

/-- **The derived base change along the left coprojection, for a composite.**  Extending a
complex of `B`-modules to `B ⊗[R] B` and then along the surjection `B ⊗[R] B → B ⊗[A] B` is
extending it to `B ⊗[A] B`. -/
theorem diagonalDerivedExtensionCompIso (K : DerivedCategory (ModuleCat.{u} B)) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((totalDerivedExtensionScalars.{u, u, u} (diagonalQuotient R A B).toRingHom).functor.obj
          ((diagonalDerivedExtension R B).obj K) ≅
        (diagonalDerivedExtension A B).obj K) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨e⟩ := nonempty_totalDerived_obj_diagonalDerivedExtension R B
    (diagonalQuotient R A B).toRingHom _ (diagonalQuotient_comp_includeLeftRingHom R A B) K
  exact ⟨e ≪≫ (diagonalDerivedExtensionIsoTotalDerived A B).app K⟩

/-- **The diagonal condition of [stacks 0E2C] for a composite, reduced to one step.**  Let
`R → A → B` be flat, let `K` be an object of `D(B)` and let `L` be an object of `D(B)`
satisfying the diagonal condition for `A → B`.  If derived Hom along the surjection
`B ⊗[R] B → B ⊗[A] B` carries the derived base change of `K` along the left coprojection of
`B ⊗[R] B` to the derived base change of `L` along the left coprojection of `B ⊗[A] B`, then
`K` satisfies the diagonal condition for `R → B`.

The hypothesis `e` is the one step of [stacks 0E2H] that this library cannot supply; see the
module documentation.  Nothing is assumed about `K` or `L` beyond `e` and `hL`. -/
theorem diagonalDerivedHom_of_diagonalQuotientIso
    (K L : DerivedCategory (ModuleCat.{u} B))
    (e : letI : Module.Flat R B := Module.Flat.trans R A B
      (derivedHom.{u, u} (diagonalQuotient R A B).toRingHom).obj
          ((diagonalDerivedExtension R B).obj K) ≅
        (diagonalDerivedExtension A B).obj L)
    (hL : Nonempty
      ((derivedHom.{u, u} (Algebra.TensorProduct.lmul' A (S := B)).toRingHom).obj
          ((diagonalDerivedExtension A B).obj L) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((derivedHom.{u, u} (Algebra.TensorProduct.lmul' R (S := B)).toRingHom).obj
          ((diagonalDerivedExtension R B).obj K) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨c⟩ := derivedHomDiagonalCompIso R A B
  exact ⟨(c.app ((diagonalDerivedExtension R B).obj K)).symm ≪≫
    (derivedHom.{u, u}
      (Algebra.TensorProduct.lmul' A (S := B)).toRingHom).mapIso e ≪≫ hL.some⟩

end

/-! ### The algebra of the composite diagonal

The two unconditional algebraic ingredients of [stacks 0E2H].  The first is that the map of
diagonals `A ⊗[R] A → B ⊗[R] B` is flat and that `Dualizing.diagonalQuotient` lies over the
diagonal of `R → A`, which is what exhibits `B ⊗[A] B` as a base change of `A` and makes
[stacks 0A6A] (3) available at `A ⊗[R] A → B ⊗[R] B`.  The second is the degreewise content of
transitivity of relative perfection; see the module documentation for both. -/

section CompositeAlgebra

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- The map of diagonals `A ⊗[R] A → B ⊗[R] B` induced by `A → B`. -/
noncomputable def diagonalBaseMap : (A ⊗[R] A) →ₐ[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A B) (IsScalarTower.toAlgHom R A B)

/-- The map of diagonals on a homogeneous tensor. -/
@[simp]
theorem diagonalBaseMap_tmul (a a' : A) :
    diagonalBaseMap R A B (a ⊗ₜ[R] a') = algebraMap A B a ⊗ₜ[R] algebraMap A B a' := rfl

/-- **The map of diagonals lies over `A → B` on the left coprojections.**  The left coprojection
`A → A ⊗[R] A` followed by `Dualizing.diagonalBaseMap` is `A → B` followed by the left
coprojection `B → B ⊗[R] B`; equivalently, the left coprojection `A → B ⊗[R] B` factors through
the diagonal `A ⊗[R] A`. -/
theorem diagonalBaseMap_comp_includeLeftRingHom :
    (diagonalBaseMap R A B).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A) =
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B).comp (algebraMap A B) := by
  apply RingHom.ext
  intro a
  simp

/-- **The map of diagonals is flat when `B` is flat over `A`.**  This is the flatness hypothesis
of [stacks 0A6A] (3) at `A ⊗[R] A → B ⊗[R] B`, used in the module documentation to compute
`RHom_{B ⊗[R] B}(B ⊗[A] B, K_{A/R} ⊗ᴸ_A (B ⊗[R] B))`. -/
theorem flat_diagonalBaseMap [Module.Flat A B] :
    RingHom.Flat (diagonalBaseMap R A B).toRingHom := by
  have h : RingHom.Flat (IsScalarTower.toAlgHom R A B).toRingHom :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  exact RingHom.Flat.tensorProductMap (S := R) h h

/-- **`Dualizing.diagonalQuotient` lies over the diagonal of `R → A`.**  The surjection
`B ⊗[R] B → B ⊗[A] B` precomposed with the map of diagonals `A ⊗[R] A → B ⊗[R] B` is the
multiplication map `A ⊗[R] A → A` followed by `A → B` and the left coprojection of `B ⊗[A] B`.
This is the commuting square expressing `B ⊗[A] B` as a base change of `A` along
`A ⊗[R] A → B ⊗[R] B`. -/
theorem diagonalQuotient_comp_diagonalBaseMap :
    (diagonalQuotient R A B).toRingHom.comp (diagonalBaseMap R A B).toRingHom =
      ((Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B).comp
          (algebraMap A B)).comp
        (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom := by
  have key (b : B) (a : A) : b ⊗ₜ[A] algebraMap A B a = (b * algebraMap A B a) ⊗ₜ[A] (1 : B) :=
    calc b ⊗ₜ[A] algebraMap A B a = b ⊗ₜ[A] (a • (1 : B)) := by rw [Algebra.smul_def, mul_one]
      _ = (a • b) ⊗ₜ[A] (1 : B) := (TensorProduct.smul_tmul a b 1).symm
      _ = (b * algebraMap A B a) ⊗ₜ[A] (1 : B) := by rw [Algebra.smul_def, mul_comm]
  apply RingHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a a' =>
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        diagonalBaseMap_tmul, diagonalQuotient_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
        map_mul, Algebra.TensorProduct.includeLeftRingHom_apply,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      exact key _ _
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end CompositeAlgebra

/-! ### `B ⊗[A] B` as a base change of the diagonal

Writing `C = B ⊗[R] B`, `C' = B ⊗[A] B` and `D = A ⊗[R] A`, the square recorded by
`Dualizing.diagonalQuotient_comp_diagonalBaseMap` is a pushout: `C' ≅ C ⊗[D] A`.  That
identification is what exhibits `Dualizing.diagonalQuotient` as the base change of the diagonal
`D → A` along the flat map `D → C`, and it is the algebraic input of the route described in the
module documentation. -/

section DiagonalPushout

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- `B ⊗[R] B` as an algebra over the diagonal `A ⊗[R] A`, via `Dualizing.diagonalBaseMap`. -/
@[instance_reducible]
noncomputable def diagonalAlgebra : Algebra (A ⊗[R] A) (B ⊗[R] B) :=
  (diagonalBaseMap R A B).toRingHom.toAlgebra

/-- `A` as an algebra over the diagonal `A ⊗[R] A`, via the multiplication map. -/
@[instance_reducible]
noncomputable def diagonalAlgebraSelf : Algebra (A ⊗[R] A) A :=
  (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom.toAlgebra

/-- `B ⊗[A] B` as an algebra over `B ⊗[R] B`, via `Dualizing.diagonalQuotient`. -/
@[instance_reducible]
noncomputable def diagonalQuotientAlgebra : Algebra (B ⊗[R] B) (B ⊗[A] B) :=
  (diagonalQuotient R A B).toRingHom.toAlgebra

/-- `B ⊗[A] B` as an algebra over the diagonal `A ⊗[R] A`. -/
@[instance_reducible]
noncomputable def diagonalAlgebraQuot : Algebra (A ⊗[R] A) (B ⊗[A] B) :=
  ((diagonalQuotient R A B).toRingHom.comp (diagonalBaseMap R A B).toRingHom).toAlgebra

/-- The scalar tower `A ⊗[R] A → B ⊗[R] B → B ⊗[A] B`. -/
theorem diagonalIsScalarTower :
    letI := diagonalAlgebra R A B
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    IsScalarTower (A ⊗[R] A) (B ⊗[R] B) (B ⊗[A] B) :=
  let := diagonalAlgebra R A B
  let := diagonalQuotientAlgebra R A B
  let := diagonalAlgebraQuot R A B
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The scalar tower `A ⊗[R] A → A → B ⊗[A] B`: this is exactly
`Dualizing.diagonalQuotient_comp_diagonalBaseMap`. -/
theorem diagonalIsScalarTowerSelf :
    letI := diagonalAlgebraSelf R A
    letI := diagonalAlgebraQuot R A B
    IsScalarTower (A ⊗[R] A) A (B ⊗[A] B) :=
  let := diagonalAlgebraSelf R A
  let := diagonalAlgebraQuot R A B
  IsScalarTower.of_algebraMap_eq fun x =>
    (RingHom.congr_fun (diagonalQuotient_comp_diagonalBaseMap R A B) x)

section Reduction

attribute [local instance] diagonalAlgebra diagonalAlgebraSelf

/-- In `A ⊗[A ⊗[R] A] (B ⊗[R] B)` the left-hand factor of a homogeneous tensor can always be
reduced to `1`, at the cost of multiplying the right-hand factor by the image of the diagonal
under `Dualizing.diagonalBaseMap`. -/
theorem algebraMap_tmul_eq (d : A ⊗[R] A) (x : B ⊗[R] B) :
    (algebraMap (A ⊗[R] A) A d) ⊗ₜ[A ⊗[R] A] x =
      (1 : A) ⊗ₜ[A ⊗[R] A] (diagonalBaseMap R A B d * x) := by
  have h1 : (algebraMap (A ⊗[R] A) A d) = d • (1 : A) := by
    rw [Algebra.smul_def, mul_one]
  have h2 : d • x = diagonalBaseMap R A B d * x := by rw [Algebra.smul_def]; rfl
  rw [h1, TensorProduct.smul_tmul, h2]

/-- The multiplication map `A ⊗[R] A → A` on a tensor with `1` on the right. -/
theorem algebraMap_diagonal_tmul_one (a : A) :
    (algebraMap (A ⊗[R] A) A) (a ⊗ₜ[R] (1 : A)) = a := by
  show Algebra.TensorProduct.lmul' R (a ⊗ₜ[R] (1 : A)) = a
  rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]

/-- The multiplication map `A ⊗[R] A → A` on a tensor with `1` on the left. -/
theorem algebraMap_diagonal_one_tmul (a : A) :
    (algebraMap (A ⊗[R] A) A) ((1 : A) ⊗ₜ[R] a) = a := by
  show Algebra.TensorProduct.lmul' R ((1 : A) ⊗ₜ[R] a) = a
  rw [Algebra.TensorProduct.lmul'_apply_tmul, one_mul]

/-- `Dualizing.algebraMap_tmul_eq` at the unit, for a diagonal element with image `a`. -/
private theorem tmul_one_eq_of_algebraMap_eq (a : A) (d : A ⊗[R] A)
    (hd : algebraMap (A ⊗[R] A) A d = a) :
    a ⊗ₜ[A ⊗[R] A] (1 : B ⊗[R] B) = (1 : A) ⊗ₜ[A ⊗[R] A] (diagonalBaseMap R A B d) := by
  simpa [hd] using algebraMap_tmul_eq R A B d 1

/-- `Dualizing.algebraMap_tmul_eq` at the unit, read through the left coprojection of
`B ⊗[R] B`. -/
theorem tmul_one_eq_left (a : A) :
    a ⊗ₜ[A ⊗[R] A] (1 : B ⊗[R] B) =
      (1 : A) ⊗ₜ[A ⊗[R] A] ((algebraMap A B a) ⊗ₜ[R] (1 : B)) := by
  simpa using tmul_one_eq_of_algebraMap_eq R A B a (a ⊗ₜ[R] 1) (algebraMap_diagonal_tmul_one R A a)

/-- `Dualizing.algebraMap_tmul_eq` at the unit, read through the right coprojection of
`B ⊗[R] B`. -/
theorem tmul_one_eq_right (a : A) :
    a ⊗ₜ[A ⊗[R] A] (1 : B ⊗[R] B) =
      (1 : A) ⊗ₜ[A ⊗[R] A] ((1 : B) ⊗ₜ[R] (algebraMap A B a)) := by
  simpa using tmul_one_eq_of_algebraMap_eq R A B a (1 ⊗ₜ[R] a) (algebraMap_diagonal_one_tmul R A a)

end Reduction

section Equiv

attribute [local instance] diagonalAlgebra diagonalAlgebraSelf diagonalQuotientAlgebra
  diagonalAlgebraQuot diagonalIsScalarTower diagonalIsScalarTowerSelf

/-- `Dualizing.diagonalQuotient` as a map of `A ⊗[R] A`-algebras. -/
noncomputable def diagonalQuotientAlgHom : (B ⊗[R] B) →ₐ[A ⊗[R] A] (B ⊗[A] B) :=
  { (diagonalQuotient R A B).toRingHom with commutes' := fun _ => rfl }

/-- The comparison map `A ⊗[A ⊗[R] A] (B ⊗[R] B) → B ⊗[A] B`: the base-change along the
diagonal `A ⊗[R] A → A` of `Dualizing.diagonalQuotient`. -/
noncomputable def diagonalPushoutMap :
    (A ⊗[A ⊗[R] A] (B ⊗[R] B)) →ₐ[A] (B ⊗[A] B) :=
  AlgHom.liftEquiv (A ⊗[R] A) A (B ⊗[R] B) (B ⊗[A] B) (diagonalQuotientAlgHom R A B)

/-- `Dualizing.diagonalPushoutMap` sends `a ⊗ x` to `(a ⊗ 1) * x̄`, where `x̄` is the image of `x`
under `Dualizing.diagonalQuotient`. -/
@[simp]
theorem diagonalPushoutMap_tmul (a : A) (x : B ⊗[R] B) :
    diagonalPushoutMap R A B (a ⊗ₜ[A ⊗[R] A] x) =
      (algebraMap A B a ⊗ₜ[A] (1 : B)) * diagonalQuotient R A B x := by
  rw [diagonalPushoutMap, AlgHom.liftEquiv_tmul, Algebra.smul_def]
  rfl

/-- The comparison map `Dualizing.diagonalPushoutMap` is surjective. -/
theorem surjective_diagonalPushoutMap :
    Function.Surjective (diagonalPushoutMap R A B) := by
  intro z
  obtain ⟨x, hx⟩ := surjective_diagonalQuotient R A B z
  refine ⟨(1 : A) ⊗ₜ[A ⊗[R] A] x, ?_⟩
  rw [diagonalPushoutMap_tmul, hx, map_one, ← Algebra.TensorProduct.one_def, one_mul]

/-- The inverse of `Dualizing.diagonalPushoutMap`: the two coprojections of `B ⊗[A] B` are
carried to `1` tensored with the two coprojections of `B ⊗[R] B`. -/
noncomputable def diagonalPushoutInv :
    (B ⊗[A] B) →ₐ[A] (A ⊗[A ⊗[R] A] (B ⊗[R] B)) :=
  let fl : B →ₐ[A] (A ⊗[A ⊗[R] A] (B ⊗[R] B)) :=
    { ((Algebra.TensorProduct.includeRight : (B ⊗[R] B) →ₐ[A ⊗[R] A] _).toRingHom).comp
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B) with
      commutes' := fun a => (tmul_one_eq_left R A B a).symm }
  let fr : B →ₐ[A] (A ⊗[A ⊗[R] A] (B ⊗[R] B)) :=
    { ((Algebra.TensorProduct.includeRight : (B ⊗[R] B) →ₐ[A ⊗[R] A] _).toRingHom).comp
        ((Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toRingHom) with
      commutes' := fun a => (tmul_one_eq_right R A B a).symm }
  Algebra.TensorProduct.lift fl fr fun _ _ => Commute.all _ _

/-- `Dualizing.diagonalPushoutInv` sends `b₁ ⊗ₜ[A] b₂` to `1 ⊗ (b₁ ⊗ₜ[R] b₂)`. -/
@[simp]
theorem diagonalPushoutInv_tmul (b₁ b₂ : B) :
    diagonalPushoutInv R A B (b₁ ⊗ₜ[A] b₂) =
      (1 : A) ⊗ₜ[A ⊗[R] A] (b₁ ⊗ₜ[R] b₂) := by
  show ((1 : A) ⊗ₜ[A ⊗[R] A] (b₁ ⊗ₜ[R] (1 : B))) *
      ((1 : A) ⊗ₜ[A ⊗[R] A] ((1 : B) ⊗ₜ[R] b₂)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    one_mul, mul_one]

/-- `Dualizing.diagonalPushoutInv` is a left inverse of the map `Dualizing.diagonalPushoutMap`. -/
theorem diagonalPushoutInv_diagonalPushoutMap (y : A ⊗[A ⊗[R] A] (B ⊗[R] B)) :
    diagonalPushoutInv R A B (diagonalPushoutMap R A B y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y y' hy hy' => rw [map_add, map_add, hy, hy']
  | tmul a x =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' hx hx' =>
          rw [TensorProduct.tmul_add] at *
          rw [map_add, map_add, hx, hx']
      | tmul b₁ b₂ =>
          rw [diagonalPushoutMap_tmul, diagonalQuotient_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul, diagonalPushoutInv_tmul]
          have h := algebraMap_tmul_eq R A B (a ⊗ₜ[R] (1 : A)) (b₁ ⊗ₜ[R] b₂)
          rw [algebraMap_diagonal_tmul_one, diagonalBaseMap_tmul, map_one,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h
          exact h.symm

/-- **`B ⊗[A] B` is the base change of the diagonal `A` along `A ⊗[R] A → B ⊗[R] B`.**  Writing
`C = B ⊗[R] B`, `C' = B ⊗[A] B` and `D = A ⊗[R] A`, this is the identification
`C' ≅ A ⊗[D] C` as `A`-algebras, the `D`-algebra structure on `C` being
`Dualizing.diagonalBaseMap` and the one on `A` the multiplication map.  Under it
`Dualizing.diagonalQuotient` is the base change of the diagonal `D → A` along `D → C`, which is
flat by `Dualizing.flat_diagonalBaseMap`.  This is the pushout property of the commuting square
`Dualizing.diagonalQuotient_comp_diagonalBaseMap`. -/
noncomputable def diagonalPushoutEquiv :
    (A ⊗[A ⊗[R] A] (B ⊗[R] B)) ≃ₐ[A] (B ⊗[A] B) :=
  AlgEquiv.ofAlgHom (diagonalPushoutMap R A B) (diagonalPushoutInv R A B)
    (AlgHom.ext fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [AlgHom.comp_apply, map_add] at *; rw [hz, hz']
      | tmul b₁ b₂ =>
          simp only [AlgHom.comp_apply, AlgHom.id_apply, diagonalPushoutInv_tmul,
            diagonalPushoutMap_tmul, diagonalQuotient_tmul, map_one,
            ← Algebra.TensorProduct.one_def, one_mul])
    (AlgHom.ext (diagonalPushoutInv_diagonalPushoutMap R A B))

/-- `Dualizing.diagonalPushoutEquiv` sends `a ⊗ x` to `(a ⊗ 1) * x̄`, where `x̄` is the image of
`x` under `Dualizing.diagonalQuotient`. -/
@[simp]
theorem diagonalPushoutEquiv_tmul (a : A) (x : B ⊗[R] B) :
    diagonalPushoutEquiv R A B (a ⊗ₜ[A ⊗[R] A] x) =
      (algebraMap A B a ⊗ₜ[A] (1 : B)) * diagonalQuotient R A B x :=
  diagonalPushoutMap_tmul R A B a x

end Equiv

end DiagonalPushout

/-! ### The derived base change of the diagonal of `R → A` along `A ⊗[R] A → B ⊗[R] B`

The left coprojection `A → B ⊗[R] B` factors through the diagonal `A ⊗[R] A`
(`Dualizing.diagonalBaseMap_comp_includeLeftRingHom`), so the derived base change of `K_{A/R}` to
`C = B ⊗[R] B` is the derived base change along `D → C` of its derived base change to
`D = A ⊗[R] A`.  This is what exhibits the untwisted tensor factor `X = K_{A/R} ⊗ᴸ_A C` of the
module documentation as extended from `D`. -/

section DiagonalBaseChange

noncomputable section

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [Module.Flat R A] [Module.Flat A B]

/-- **The derived base change of `K_{A/R} ⊗ᴸ_A (A ⊗[R] A)` along the map of diagonals.**  For
`K` an object of `D(A)`, extending `K` to the diagonal `A ⊗[R] A` and then along
`Dualizing.diagonalBaseMap` is extending `K` to `B` and then to the diagonal `B ⊗[R] B`.

Writing `C = B ⊗[R] B` and `D = A ⊗[R] A`, this says `K ⊗ᴸ_A C ≅ (K ⊗ᴸ_A D) ⊗ᴸ_D C`: the
tensor factor `X = K_{A/R} ⊗ᴸ_A C` of the module documentation is the derived base change along
the flat map `D → C` of the object `X_D = K_{A/R} ⊗ᴸ_A D` that the diagonal condition of
[stacks 0E2C] for `R → A` computes. -/
theorem diagonalDerivedExtensionBaseChangeIso (K : DerivedCategory (ModuleCat.{u} A)) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((totalDerivedExtensionScalars.{u, u, u} (diagonalBaseMap R A B).toRingHom).functor.obj
          ((diagonalDerivedExtension R A).obj K) ≅
        (diagonalDerivedExtension R B).obj
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj K)) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨e⟩ := nonempty_totalDerived_obj_diagonalDerivedExtension R A
    (diagonalBaseMap R A B).toRingHom _ (diagonalBaseMap_comp_includeLeftRingHom R A B) K
  exact ⟨e ≪≫ ((StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso
      (algebraMap A B)
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)).app K).symm ≪≫
    (diagonalDerivedExtensionIsoTotalDerived R B).app _⟩

end

end DiagonalBaseChange

section RelativePerfectionTerms

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (P Q : Type u) [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
  [AddCommGroup Q] [Module R Q] [Module A Q] [IsScalarTower R A Q]

/-- **Flatness of a term of a relative tensor product.**  If `P` is an `A`-module flat over `R`
and `Q` is an `A`-module flat over `A`, then `Q ⊗[A] P` is flat over `R`.

This is the flatness half of the degreewise content of transitivity of relative perfection: for
an injection of `R`-modules `N → N'`, tensoring with `P` over `R` keeps it injective and `A`-linear
because `P` is flat over `R`, and tensoring that with `Q` over `A` keeps it injective because `Q`
is flat over `A`; the associativity isomorphism identifies the result with the map obtained by
tensoring `N → N'` with `Q ⊗[A] P` over `R`. -/
@[ega "IV 2.1.5" "special case"]
theorem flat_tensorProduct [Module.Flat R P] [Module.Flat A Q] :
    Module.Flat R (Q ⊗[A] P) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have h1 : Function.Injective
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : P →ₗ[A] P) f) :=
    Module.Flat.lTensor_preserves_injective_linearMap f hf
  have h2 : Function.Injective (LinearMap.lTensor (R := A) Q
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : P →ₗ[A] P) f)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (R := A) _ h1
  have hsq : ∀ x : (Q ⊗[A] P) ⊗[R] N,
      TensorProduct.AlgebraTensorModule.assoc R A A Q P N'
          (LinearMap.lTensor (Q ⊗[A] P) f x) =
        LinearMap.lTensor (R := A) Q
          (TensorProduct.AlgebraTensorModule.map (LinearMap.id : P →ₗ[A] P) f)
          (TensorProduct.AlgebraTensorModule.assoc R A A Q P N x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul y n =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul q p => simp
        | add y y' hy hy' =>
            rw [TensorProduct.add_tmul] at *
            simp only [map_add] at *
            rw [hy, hy']
    | add x y hx hy => simp only [map_add, hx, hy]
  intro x y hxy
  exact (TensorProduct.AlgebraTensorModule.assoc R A A Q P N).injective
    (h2 (by rw [← hsq, ← hsq, hxy]))

end RelativePerfectionTerms

section RelativePerfectionTermsFinite

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  (P Q : Type u) [AddCommGroup P] [Module A P]
  [AddCommGroup Q] [Module A Q] [Module B Q] [IsScalarTower A B Q]

/-- **Finite presentation of a term of a relative tensor product.**  If `P` is finitely presented
over `A` and `Q` is a `B`-module finitely presented over `B`, then `Q ⊗[A] P` is finitely presented
over `B`: it is `Q ⊗[B] (B ⊗[A] P)`, and both factors are finitely presented over `B`.

This is the finite-presentation half of the degreewise content of transitivity of relative
perfection. -/
theorem finitePresentation_tensorProduct
    [Module.FinitePresentation A P] [Module.FinitePresentation B Q] :
    Module.FinitePresentation B (Q ⊗[A] P) :=
  Module.FinitePresentation.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B Q P)

end RelativePerfectionTermsFinite

/-! ### Derived base change along a flat ring map, on a module in degree zero

The first of the two transports the module documentation asks for: the derived base change of the
diagonal `A` along the flat map `D → C` is `C'`.  Flatness makes termwise extension of scalars
exact, so the comparison of `Dualizing.totalDerivedExtensionScalarsIsoOfFlat` is an isomorphism and
derived extension of scalars commutes with the degree-zero single-object functor; the module-level
identification `C ⊗[D] A ≅ C'` is `Dualizing.diagonalPushoutEquiv`. -/

section FlatSingle

variable {R A : Type u} [CommRing R] [CommRing A]

/-- Extension of scalars along a flat ring map is exact. -/
theorem preservesFiniteLimits_extendScalars_of_flat (f : R →+* A) (hf : f.Flat) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) := by
  let := f.toAlgebra
  have : Module.Flat R A := hf
  refine ((Functor.exact_tfae (ModuleCat.extendScalars.{u, u, u} f)).out 2 4).mp ?_
  intro T hT
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
  exact Module.Flat.lTensor_exact A hT

/-- **Derived extension of scalars along a flat ring map is the degreewise one.** -/
noncomputable def totalDerivedExtensionScalarsIsoOfFlat (f : R →+* A) (hf : f.Flat) :
    letI := (preservesFiniteLimits_extendScalars_of_flat f hf).1
    letI := (preservesFiniteLimits_extendScalars_of_flat f hf).2
    (totalDerivedExtensionScalars.{u, u, u} f).functor ≅
      (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory := by
  let := (preservesFiniteLimits_extendScalars_of_flat f hf).1
  let := (preservesFiniteLimits_extendScalars_of_flat f hf).2
  let F := ModuleCat.extendScalars.{u, u, u} f
  let D := totalDerivedExtensionScalars.{u, u, u} f
  have : F.PreservesHomology :=
    CochainComplex.DerivedTensor.extensionScalars_preservesHomology f hf
  have : IsIso D.comparison := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    D.functor D.comparison (W := HomologicalComplex.quasiIso
      (ModuleCat.{u} R) (ComplexShape.up ℤ)) (by
      intro X Y g hg
      have : QuasiIso g := hg
      change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex _).map g))
      infer_instance)
  exact Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ D.functor) (DerivedCategory.Q ⋙ F.mapDerivedCategory) _ _
    (asIso D.comparison ≪≫ F.mapDerivedCategoryFactors.symm)

/-- **Derived extension of scalars along a flat ring map, on a module in degree zero.** -/
noncomputable def totalDerivedExtensionScalarsSingleIsoOfFlat (f : R →+* A) (hf : f.Flat)
    (M : ModuleCat.{u} R) :
    (totalDerivedExtensionScalars.{u, u, u} f).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        ((ModuleCat.extendScalars.{u, u, u} f).obj M) :=
  let := (preservesFiniteLimits_extendScalars_of_flat f hf).1
  let := (preservesFiniteLimits_extendScalars_of_flat f hf).2
  (totalDerivedExtensionScalarsIsoOfFlat f hf).app _ ≪≫
    ((ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategorySingleFunctor 0).app M

end FlatSingle

section DiagonalSingle

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- `Dualizing.diagonalPushoutEquiv` with the factors commuted, `A ⊗[R] A`-linearly. -/
noncomputable def diagonalPushoutEquivFlip :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    letI := diagonalIsScalarTowerSelf R A B
    ((B ⊗[R] B) ⊗[A ⊗[R] A] A) ≃ₗ[A ⊗[R] A] (B ⊗[A] B) :=
  let := diagonalAlgebra R A B
  let := diagonalAlgebraSelf R A
  let := diagonalQuotientAlgebra R A B
  let := diagonalAlgebraQuot R A B
  let := diagonalIsScalarTowerSelf R A B
  (TensorProduct.comm (A ⊗[R] A) (B ⊗[R] B) A).trans
    ((diagonalPushoutEquiv R A B).toLinearEquiv.restrictScalars (A ⊗[R] A))

/-- `Dualizing.diagonalPushoutEquivFlip` on a homogeneous tensor. -/
theorem diagonalPushoutEquivFlip_tmul :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    letI := diagonalIsScalarTowerSelf R A B
    ∀ (x : B ⊗[R] B) (a : A),
      diagonalPushoutEquivFlip R A B (x ⊗ₜ[A ⊗[R] A] a) =
        (algebraMap A B a ⊗ₜ[A] (1 : B)) * diagonalQuotient R A B x := by
  let := diagonalAlgebra R A B
  let := diagonalAlgebraSelf R A
  let := diagonalQuotientAlgebra R A B
  let := diagonalAlgebraQuot R A B
  let := diagonalIsScalarTowerSelf R A B
  intro x a
  simp [diagonalPushoutEquivFlip]

/-- The `C`-action on `C ⊗[D] A` on a homogeneous tensor. -/
theorem smul_tmul_diagonalPushout :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    ∀ (c x : B ⊗[R] B) (a : A),
      c • (x ⊗ₜ[A ⊗[R] A] a) = (c * x) ⊗ₜ[A ⊗[R] A] a := fun _ _ _ => rfl

/-- The `C`-action on `C'` is multiplication through `Dualizing.diagonalQuotient`. -/
theorem smul_diagonalQuotientAlgebra :
    letI := diagonalQuotientAlgebra R A B
    ∀ (c : B ⊗[R] B) (y : B ⊗[A] B), c • y = diagonalQuotient R A B c * y :=
  let := diagonalQuotientAlgebra R A B
  fun c y => Algebra.smul_def c y

/-- `Dualizing.diagonalPushoutEquivFlip` is linear over `C`, not only over `D`. -/
theorem diagonalPushoutEquivFlip_smul :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    letI := diagonalIsScalarTowerSelf R A B
    ∀ (c : B ⊗[R] B) (y : (B ⊗[R] B) ⊗[A ⊗[R] A] A),
      diagonalPushoutEquivFlip R A B (c • y) = c • diagonalPushoutEquivFlip R A B y := by
  let := diagonalAlgebra R A B
  let := diagonalAlgebraSelf R A
  let := diagonalQuotientAlgebra R A B
  let := diagonalAlgebraQuot R A B
  let := diagonalIsScalarTowerSelf R A B
  intro c y
  induction y with
  | zero => simp
  | tmul x a =>
      rw [smul_tmul_diagonalPushout, diagonalPushoutEquivFlip_tmul,
        diagonalPushoutEquivFlip_tmul, smul_diagonalQuotientAlgebra, map_mul]
      ring
  | add u v hu hv => simp only [smul_add, map_add, hu, hv]

/-- **`C ⊗[D] A ≅ C'`.**  The base change along `D → C` of the diagonal `A`, as a `C`-module. -/
noncomputable def diagonalPushoutModuleEquiv :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    letI := diagonalIsScalarTowerSelf R A B
    ((B ⊗[R] B) ⊗[A ⊗[R] A] A) ≃ₗ[B ⊗[R] B] (B ⊗[A] B) :=
  let := diagonalAlgebra R A B
  let := diagonalAlgebraSelf R A
  let := diagonalQuotientAlgebra R A B
  let := diagonalAlgebraQuot R A B
  let := diagonalIsScalarTowerSelf R A B
  { diagonalPushoutEquivFlip R A B with map_smul' := diagonalPushoutEquivFlip_smul R A B }

/-- **The derived base change of the diagonal `A` along `D → C` is `C'`.**  Writing
`C = B ⊗[R] B`, `C' = B ⊗[A] B` and `D = A ⊗[R] A`, the derived extension of scalars along the
flat map `Dualizing.diagonalBaseMap` carries the diagonal `A` in degree zero to `C'` in degree
zero.  This is the complex-level form of `Dualizing.diagonalPushoutEquiv`. -/
theorem diagonalDerivedExtensionSingleIso [Module.Flat A B] :
    letI := diagonalAlgebra R A B
    letI := diagonalAlgebraSelf R A
    letI := diagonalQuotientAlgebra R A B
    letI := diagonalAlgebraQuot R A B
    letI := diagonalIsScalarTowerSelf R A B
    Nonempty
      ((totalDerivedExtensionScalars.{u, u, u} (diagonalBaseMap R A B).toRingHom).functor.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
            (ModuleCat.of (A ⊗[R] A) A)) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).obj
          (ModuleCat.of (B ⊗[R] B) (B ⊗[A] B))) := by
  let := diagonalAlgebra R A B
  let := diagonalAlgebraSelf R A
  let := diagonalQuotientAlgebra R A B
  let := diagonalAlgebraQuot R A B
  let := diagonalIsScalarTowerSelf R A B
  refine ⟨totalDerivedExtensionScalarsSingleIsoOfFlat
    (diagonalBaseMap R A B).toRingHom (flat_diagonalBaseMap R A B) _ ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} (B ⊗[R] B)) 0).mapIso ?_⟩
  exact (diagonalPushoutModuleEquiv R A B).toModuleIso

end DiagonalSingle

end Dualizing

end
