module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOverField

/-!
# Pseudo-coherence of the relative dualizing complex

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be a flat morphism of finite presentation in
`AlgebraicGeometry.FTS S`, the category of [Stacks, Tag 0F42]. The relative dualizing complex
`ω^•_{X/Y} = f^!𝒪_Y` is a pseudo-coherent object of `D(𝒪_X)`. Pseudo-coherence is the first of
the two conditions for an object to be perfect relative to `Y` ([Stacks, Tag 0DI0]), so the
`Y`-perfectness asserted by [Stacks, Tag 0E9T] holds exactly when `f^!𝒪_Y` has locally finite
Tor dimension over `f^{-1}𝒪_Y`.

## Main definitions

* `Stacks.Duality.IsShriekOfStructureSheafOnCharts` — the affine-chart description of
  `f^!𝒪_Y`: over an affine open `V ⊆ Y` and an affine open `U ⊆ f^{-1}(V)` the restriction to `U`
  is the associated sheaf of the algebraic upper shriek, along a polynomial presentation of the
  chart ring map `f.appLE V U`, of `Γ(Y, V)` placed in degree zero.

## Main results

* `Stacks.Duality.isPseudoCoherent_of_isShriekOfStructureSheafOnCharts` — **[Stacks, Tag 0E9T]**,
  the pseudo-coherence half of the first assertion: `f^!𝒪_Y` is pseudo-coherent.
* `Stacks.Duality.isPerfectRelativeTo_iff_locallyHasFiniteTorDimension` — `Y`-perfectness of
  `f^!𝒪_Y` is equivalent to the Tor-dimension condition alone.

## Implementation notes

*What is carried.* One hypothesis is carried, the affine-chart description
`Stacks.Duality.IsShriekOfStructureSheafOnCharts`, which is the content of [Stacks, Tag 0AA1]
together with the affine comparison of [Stacks, Tag 0BV2]; the part of Tag 0BV2 in the library,
`Stacks.Duality.restrictedUpperShriekIsoOfOpenSquare`, is its clause (a) only, and the affine
formula of clause (b) is unavailable. Writing the chart ring map as `f.appLE V U` and the model
of `𝒪_Y` over `V` as `Γ(Y, V)` itself is what ties the hypothesis to `f` and to `𝒪_Y`. It is the
same hypothesis carried by
`Stacks.Duality.derivedCategoryBBounded_upperShriek_derivedStructureSheaf` and by
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts`, and it asserts only an isomorphism:
nothing in it says that any complex is bounded, coherent or pseudo-coherent.

What is proved is the rest: the chart models are bounded with finite cohomology by
[Stacks, Tag 0BZK] (2), `Dualizing.upperShriekFunctor_derivedCategoryBBounded_of_isPerfectRingMap`,
whose perfect-ring-map hypothesis is discharged from `Flat f` and `LocallyOfFinitePresentation f`
through [Stacks, Tag 068A] and `AlgebraicGeometry.Perfect.perfect_appLE` at the
canonical derived tensoring; the chart bounds are glued by
`Stacks.Duality.isBounded_of_tildeModels` and `Stacks.Duality.isCoherent_homology_of_tildeModels`;
and `D^b_Coh(𝒪_X)` is turned into pseudo-coherence by [Stacks, Tag 08E8],
`AlgebraicGeometry.isBounded_and_isPseudoCoherent_iff_boundedCoherent`.

*What is not claimed, and why.* The Tor-dimension condition is the second conjunct of
[Stacks, Tag 0DI0] and the source obtains it from [Stacks, Tag 0BZW] (1)(b), that `ω_{A/R}` has
finite Tor dimension over `R`. That ring-level statement *is* in this library, with nothing
carried:
`relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectRingMap` (in the namespace
`Dualizing.PolynomialPresentation`) of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingFiniteTorDimension`. What is
absent is the affine-locality assembly which would carry it from a chart to
`AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension`; the absence of that assembly is
recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativelyPerfectDerivedSections.lean`, and it is the only
thing standing between the ring-level statement and the Tor-dimension conjunct here. The second
assertion of Tag 0E9T, that `𝒪_X ⟶ R SheafHom_{𝒪_X}(f^!𝒪_Y, f^!𝒪_Y)` is an isomorphism, rests on
Tag 0BZW (1)(c), which is proved as
`Dualizing.upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectModule`, but there is no map
`𝒪_X ⟶ R SheafHom(K, K)` on a scheme in this library to state the sheaf-level assertion with.
Neither is carried as a hypothesis here, since either would be the assertion itself.

*The model of the derived category.* Tag 08E8 is proved at
`CategoryTheory.HasDerivedCategory.standard`, and
`Stacks.Duality.upperShriek` is defined at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`; `HasDerivedCategory` carries the
localization as data, so neither statement transports to the other model. The exceptional
inverse image therefore enters as an object of `D⁺_QCoh(𝒪_X)` read at the standard model
together with the chart description above, the idiom of
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts`, rather than as a value of
`Stacks.Duality.upperShriek`. Inside the chart description the derived category of an affine open
is the locally small one, which is the model the chart statements of
`Stacks.Duality.HasTildeModelAt` are read at.

## References

* [Stacks Project, Tag 0E9T](https://stacks.math.columbia.edu/tag/0E9T)
* [Stacks Project, Tag 0B6U](https://stacks.math.columbia.edu/tag/0B6U)
* [Stacks Project, Tag 0BZW](https://stacks.math.columbia.edu/tag/0BZW)
* [Stacks Project, Tag 0BZK](https://stacks.math.columbia.edu/tag/0BZK)
* [Stacks Project, Tag 0DI0](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 0DI2](https://stacks.math.columbia.edu/tag/0DI2)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 0AA1](https://stacks.math.columbia.edu/tag/0AA1)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
* [Stacks Project, Tag 068A](https://stacks.math.columbia.edu/tag/068A)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open StacksDraft.TorAmplitude

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)

/-- **The affine-chart description of `f^!𝒪_Y`.** The object `ω` of `D(𝒪_X)` restricts, on an
affine open `U ⊆ X` lying over an affine open `V ⊆ Y`, to the associated sheaf of the algebraic
upper shriek, along a polynomial presentation of the chart ring map `f.appLE V U`, of the ring
`Γ(Y, V)` placed in cohomological degree zero. -/
def IsShriekOfStructureSheafOnCharts (ω : DerivedCategory X.left.Modules) : Prop :=
  ∀ x : X.left, ∃ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens)
    (_hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧
    ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
      letI := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj ω ≅
        (tilde.functor Γ(X.left, U) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj
            (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)))

/-- The left component of an object of `FTS S` is locally Noetherian. -/
private theorem isLocallyNoetherian_left (Z : AlgebraicGeometry.FTS S) :
    IsLocallyNoetherian Z.left := by
  have : IsLocallyNoetherian ((Functor.fromPUnit S).obj Z.right) :=
    inferInstanceAs (IsLocallyNoetherian S)
  exact LocallyOfFiniteType.isLocallyNoetherian Z.hom

/-- **The chart model of `f^!𝒪_Y` lies in `D^b_Coh` of the chart ring.** For `f` flat of finite
presentation, an affine open `U ⊆ X` over an affine open `V ⊆ Y` and a polynomial presentation
`p` of the chart ring map `f.appLE V U`, the algebraic upper shriek along `p` of `Γ(Y, V)` in
degree zero is cohomologically bounded with finite cohomology modules.

A flat morphism of finite presentation is perfect by [Stacks, Tag 068A], so each chart ring map
is a perfect ring map, and [Stacks, Tag 0BZK] (2) carries `Γ(Y, V)` in degree zero,
which lies in `D^b_Coh(Γ(Y, V))`, into `D^b_Coh(Γ(X, U))`. Nothing is assumed. -/
theorem derivedCategoryBBounded_upperShriekFunctor_structureModel
    [Flat f.left] [LocallyOfFinitePresentation f.left]
    {U : X.left.Opens} (hU : IsAffineOpen U) {V : Y.left.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ f.left ⁻¹ᵁ V)
    (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun N : ModuleCat.{u} Γ(X.left, U) => Module.Finite Γ(X.left, U) N)
      (p.upperShriekFunctor.{u, u}.obj (structureModel (Y := Y) V)) := by
  have hYn := isLocallyNoetherian_left Y
  have hXn := isLocallyNoetherian_left X
  have hVn : IsNoetherianRing Γ(Y.left, V) :=
    IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have hUn : IsNoetherianRing Γ(X.left, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let D : CertifiedDerivedTensoring.{u, u} Γ(Y.left, V) :=
    canonicalCertifiedDerivedTensoring Γ(Y.left, V)
  exact Dualizing.upperShriekFunctor_derivedCategoryBBounded_of_isPerfectRingMap.{u, u} p
    D.tensor D.comparison D.isLeftDerived
    (AlgebraicGeometry.Perfect.perfect_appLE f.left U hU V hV hUV D)
    (derivedCategoryBBounded_structureModel (Y := Y) V)

/-- **Stacks Project, Tag 0E9T, the pseudo-coherence half of the first assertion.** In
Situation 48.16.1, let `f : X ⟶ Y` be a flat morphism of finite presentation of `FTS S`. Then the
relative dualizing complex `ω^•_{X/Y} = f^!𝒪_Y` is a pseudo-coherent object of `D(𝒪_X)`.

Over each chart the model of `f^!𝒪_Y` lies in `D^b_Coh` of the chart ring by
Tag 0BZK (2); the chart bounds glue, and on a Noetherian scheme a bounded object with coherent
cohomology is pseudo-coherent by Tag 08E8. -/
@[stacks 0E9T "the pseudo-coherence half of the first assertion: f^! O_Y is a pseudo-coherent \
  object of D(O_X), which is the first of the two conjuncts of Y-perfectness (Tag 0DI0). NOT \
  claimed: the Tor-dimension conjunct of the first assertion, and the whole of the second \
  assertion that O_X -> R SheafHom(f^! O_Y, f^! O_Y) is an isomorphism. Both rest on Stacks \
  0BZW, whose parts (1)(a), (1)(b) and (1)(c) are all proved in this repository at the level of \
  rings -- (1)(b) as \
  relativeDualizingComplex_hasFiniteTorDimension_of_isPerfectRingMap (in the namespace \
  Dualizing.PolynomialPresentation) \
  and (1)(c) as Dualizing.upperShriekFunctor_unit_isIso_derivedHomothety_of_isPerfectModule -- \
  but what is absent is the affine-locality assembly for Tor dimension that Stacks 0DI2 would \
  need, and there is no map O_X -> R SheafHom(K, K) on a scheme in this repository at all, so \
  the sheaf-level second assertion cannot even be stated. Neither is carried as a \
  hypothesis, since either would be the assertion itself. One hypothesis IS carried, hw: the \
  affine-chart description of f^! O_Y, which is Stacks 0AA1 together with clause (b) of Stacks \
  0BV2; it asserts only an isomorphism, and it is the same hypothesis carried by \
  Tag 0B6U part (a) and Tag 0AA3. Everything asserted about pseudo-coherence is proved, from \
  Tag 0BZK (2) chart by chart -- whose perfect-ring-map hypothesis is discharged, \
  not carried, from Flat and LocallyOfFinitePresentation through Tag 068A -- and \
  Tag 08E8. f^! O_Y enters as an object of D+_QCoh(O_X) at \
  CategoryTheory.HasDerivedCategory.standard characterised by hw, the idiom of Tag 0AA3, rather \
  than as a value of Stacks.Duality.upperShriek, which is defined at the locally small model \
  that Tag 08E8 is not available at"]
theorem isPseudoCoherent_of_isShriekOfStructureSheafOnCharts
    [Flat f.left] [LocallyOfFinitePresentation f.left]
    (ω : quasiCoherentDerivedCategory.{u + 1, u} X.left)
    (hw : IsShriekOfStructureSheafOnCharts f ω.obj) :
    RingedSpace.IsPseudoCoherent (X := X.left.toRingedSpace) ω.obj := by
  have hXn := isLocallyNoetherian_left X
  have hXc : CompactSpace X.left := by
    have : CompactSpace ((Functor.fromPUnit S).obj X.right) :=
      inferInstanceAs (CompactSpace S)
    exact QuasiCompact.compactSpace_of_compactSpace X.hom
  have hXN : IsNoetherian X.left := ⟨⟩
  have hmodels : ∀ x : X.left, HasTildeModelAt.{u, u + 1} ω.obj x := by
    intro x
    obtain ⟨U, hU, V, hV, hUV, hxU, p, he⟩ := hw x
    exact ⟨U, hU, hxU, _,
      derivedCategoryBBounded_upperShriekFunctor_structureModel f hU hV hUV p, he⟩
  have hbdd : DerivedCategoryB.derivedCategoryBBounded
      (fun M : X.left.Modules => _root_.SheafOfModules.IsCoherent M) ω.obj :=
    ⟨isBounded_of_tildeModels hmodels, fun i => isCoherent_homology_of_tildeModels hmodels i⟩
  exact ((AlgebraicGeometry.isBounded_and_isPseudoCoherent_iff_boundedCoherent X.left
    ω.obj).2 hbdd).2

/-- **`Y`-perfectness of `f^!𝒪_Y` is its Tor-dimension condition.** For `f` flat of finite
presentation, the relative dualizing complex `ω^•_{X/Y} = f^!𝒪_Y` is perfect relative to `Y` in
the sense of [Stacks, Tag 0DI0] exactly when it has locally finite Tor dimension over
`f^{-1}𝒪_Y`: the pseudo-coherence conjunct holds unconditionally.

This is the first assertion of [Stacks, Tag 0E9T] reduced to what is not available here; see the
implementation notes of this file. -/
theorem isPerfectRelativeTo_iff_locallyHasFiniteTorDimension
    [Flat f.left] [LocallyOfFinitePresentation f.left]
    (D : ∀ U : Opens
        (RingedSpace.inverseImage Y.left.toRingedSpace f.left.base).carrier,
      RingedSpace.CertifiedDerivedSheafTensoring.{u + 1, u}
        ((RingedSpace.inverseImage Y.left.toRingedSpace f.left.base).restrict
          U.isOpenEmbedding))
    (ω : quasiCoherentDerivedCategory.{u + 1, u} X.left)
    (hw : IsShriekOfStructureSheafOnCharts f ω.obj) :
    f.left.IsPerfectRelativeTo D ω.obj ↔
      RingedSpace.LocallyHasFiniteTorDimension
        (RingedSpace.inverseImage Y.left.toRingedSpace f.left.base) D
        ((Scheme.Hom.derivedScalarRestriction f.left).obj ω.obj) :=
  ⟨fun h => h.2,
    fun h => ⟨isPseudoCoherent_of_isShriekOfStructureSheafOnCharts f ω hw, h⟩⟩

end Stacks.Duality

end
