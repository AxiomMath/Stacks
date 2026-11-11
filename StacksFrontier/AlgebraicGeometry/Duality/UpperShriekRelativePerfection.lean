module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObject
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOverField
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal

/-!
# Pseudo-coherence of the relative dualizing complex

Let `S` be a Noetherian scheme and let `f : X ⟶ Y` be a flat morphism of finite presentation in
`AlgebraicGeometry.FTS S`, the category of [Stacks, Tag 0F42]. The relative dualizing complex
`ω^•_{X/Y} = f^!𝒪_Y`, given through its affine-chart description, is a pseudo-coherent object
of `D(𝒪_X)`. Pseudo-coherence is the first of the two conditions for an object to be perfect
relative to `Y` ([Stacks, Tag 0DI0]); the full statement of [Stacks, Tag 0E9T], both
`Y`-perfectness and the homothety isomorphism, is
`Stacks.Duality.upperShriek_structureSheaf_isPerfectRelativeTo_and_isIso_homothety` in
`StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFlatDualizing`.

## Main definitions

* `Stacks.Duality.IsShriekOfStructureSheafOnCharts` — the affine-chart description of
  `f^!𝒪_Y`: over an affine open `V ⊆ Y` and an affine open `U ⊆ f^{-1}(V)` the restriction to `U`
  is the associated sheaf of the algebraic upper shriek, along a polynomial presentation of the
  chart ring map `f.appLE V U`, of `Γ(Y, V)` placed in degree zero.

## Main results

* `Stacks.Duality.isPseudoCoherent_of_isShriekOfStructureSheafOnCharts` — an object with the
  chart description of `f^!𝒪_Y` is pseudo-coherent.
* `Stacks.Duality.isPerfectRelativeTo_iff_locallyHasFiniteTorDimension` — `Y`-perfectness of
  `f^!𝒪_Y` is equivalent to the Tor-dimension condition alone.

## Implementation notes

*The chart description.* The results here take an object with the affine-chart description
`Stacks.Duality.IsShriekOfStructureSheafOnCharts`. For `f^!𝒪_Y` itself that description is
proved, from [Stacks, Tag 0BV2], by
`Stacks.Duality.isShriekOfStructureSheafOnCharts_of_upperShriekStructureSheafCharts`. Writing the
chart ring map as `f.appLE V U` and the model of `𝒪_Y` over `V` as `Γ(Y, V)` itself is what ties
the description to `f` and to `𝒪_Y`; it asserts only an isomorphism: nothing in it says that any
complex is bounded, coherent or pseudo-coherent.

*The proof.* The chart models are bounded with finite cohomology by
[Stacks, Tag 0BZK] (2), `Dualizing.upperShriekFunctor_derivedCategoryBBounded_of_perfect`,
whose perfect-ring-map hypothesis is discharged from `Flat f` and `LocallyOfFinitePresentation f`
through [Stacks, Tag 068A] and the chart property of [Stacks, Tag 0687]
(`AlgebraicGeometry.HasRingHomProperty.appLE`); the chart bounds are glued by
`Stacks.Duality.isBounded_of_tildeModels` and `Stacks.Duality.isCoherent_homology_of_tildeModels`;
and `D^b_Coh(𝒪_X)` is turned into pseudo-coherence by [Stacks, Tag 08E8],
`AlgebraicGeometry.isBounded_and_isPseudoCoherent_iff_boundedCoherent`.

The Tor-dimension conjunct of [Stacks, Tag 0DI0] and the homothety isomorphism of
[Stacks, Tag 0E9T] are proved, from [Stacks, Tag 0BZW] chart by chart, in
`StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeTorDimension`,
`StacksFrontier.AlgebraicGeometry.Duality.UpperShriekHomothety` and
`StacksFrontier.AlgebraicGeometry.Duality.UpperShriekFlatDualizing`.

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
  exact Dualizing.upperShriekFunctor_derivedCategoryBBounded_of_perfect.{u, u} p
    (HasRingHomProperty.appLE @Perfect f.left inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV)
    (derivedCategoryBBounded_structureModel (Y := Y) V)

/-- **Pseudo-coherence from the chart description.** In Situation 48.16.1, let `f : X ⟶ Y` be a
flat morphism of finite presentation of `FTS S`. An object `ω` of `D_QCoh(𝒪_X)` with the
affine-chart description of `f^!𝒪_Y` (`Stacks.Duality.IsShriekOfStructureSheafOnCharts`) is a
pseudo-coherent object of `D(𝒪_X)`.

Over each chart the model of `f^!𝒪_Y` lies in `D^b_Coh` of the chart ring by
Tag 0BZK (2); the chart bounds glue, and on a Noetherian scheme a bounded object with coherent
cohomology is pseudo-coherent by Tag 08E8. The chart description holds for `f^!𝒪_Y` itself by
`Stacks.Duality.isShriekOfStructureSheafOnCharts_of_upperShriekStructureSheafCharts`, and the
full statement of [Stacks, Tag 0E9T] is
`Stacks.Duality.upperShriek_structureSheaf_isPerfectRelativeTo_and_isIso_homothety`. -/
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

The first assertion of [Stacks, Tag 0E9T] itself is proved in
`Stacks.Duality.upperShriek_structureSheaf_isPerfectRelativeTo_and_isIso_homothety`. -/
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
