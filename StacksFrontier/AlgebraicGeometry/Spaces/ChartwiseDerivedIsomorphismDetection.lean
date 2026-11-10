module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleFlatTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.ExactnessOfPullback
public import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.DerivedLocality
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStack

/-!
# Étale charts detect isomorphisms in the bounded below derived category of an algebraic space

`AlgebraicGeometry.Space.isIso_of_forall_isIso_etaleModulePullback_chartToSpace` says that a
morphism of `𝒪_Y`-modules is invertible as soon as its restriction along the structure morphism
of every étale scheme chart of `Y` is.  This file carries that criterion to the bounded below
derived category `D⁺(𝒪_Y)`.

The passage is the same two steps as in
`Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_of_isIso_derivedPullback`, which is this
statement for an open covering of a scheme.  A morphism of `D⁺` is invertible exactly when all
of its cohomology maps are — `CategoryTheory.DerivedCategory.Plus.isIso_iff` — and the inverse
image along a chart is exact, so its bounded below right derived functor carries the degree-`n`
cohomology map of a morphism to the degree-`n` cohomology map of the inverse image;  that is
`Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_map_homologyFunctor_map`, stated there for an
arbitrary exact functor between abelian categories with enough injectives on the source.  The
hypothesis therefore says that each cohomology map of `φ` is invertible after inverse image
along every chart, and étale charts detect isomorphisms of `𝒪_Y`-modules.

## Main results

* `AlgebraicGeometry.Space.isIso_of_forall_isIso_rightDerivedFunctorPlus_chartToSpace`:
  **étale charts detect isomorphisms in `D⁺(𝒪_Y)`.**
* `AlgebraicGeometry.Space.isIso_iff_forall_isIso_rightDerivedFunctorPlus_chartToSpace`: the
  same as a criterion.

## Implementation notes

*Why this is stated at `AlgebraicGeometry.Space.modulePullback` and not at
`SheafOfModules.overFunctor`.*  The bounded below locality criterion
`Stacks.SheafOfModules.isIso_rightDerivedFunctorPlus_iff_of_coversTop`
(`DerivedIsomorphismLocalityBoundedBelow.lean`, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Slice/`),
tests invertibility after restriction to the *slice* site over each member of a covering family,
taken by `SheafOfModules.overFunctor`.  The pasting law of **Stacks 0E47** at this development's
seating — `AlgebraicGeometry.Space.toposModuleDerivedBaseChangeMap_horizontal`
(`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleDerivedBaseChangeMap.lean`) — instead composes
the bottom arrow of a square with a further morphism of algebraic spaces, so what it produces is
the inverse image along that morphism, `modulePullback`, and not restriction to a slice.
Identifying the two would be the transport of **Stacks 04M1**
(`AlgebraicGeometry.Space.smallEtaleRingedEquivalenceOverChart`, which is an equivalence of
*sites* together with the equality of structure presheaves) to sheaves of modules, and that
transport is not in this development.  Stating the criterion at `modulePullback` is what makes
its hypothesis the one the pasting law delivers, and costs nothing: the degree-zero locality step
at that seating is the chart statement above.

*The two local instances.*  Both are instances the library already has, restated here because
instance search does not find them with the universes undetermined, exactly as the implementation
notes of `StacksFrontier/AlgebraicGeometry/Spaces/CohomologyFlatBaseChange.lean` record for the two
additivity instances there.  `HasDerivedCategory.standard` is passed its category positionally —
its first explicit argument is that category, so leaving it to be inferred leaves the
derived-category universe a metavariable and the elaborator cannot solve
`u + 1 =?= max (u + 1) ?u` for it.

*This is not Stacks 073K, part (1).*  Part (1) is invertibility of the base change map of
**Stacks 0736**, which nothing here asserts; this is the locality step its reduction to part (2)
runs through, at the seating that reduction's pasting law lives at.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The standard derived category of the `𝒪`-modules of an algebraic space, at the universe the
statements below read it at: `AlgebraicGeometry.Space.instModulesHasDerivedCategory`. -/
@[instance_reducible] alias chartwiseLocalityHasDerivedCategory := instModulesHasDerivedCategory

attribute [local instance] chartwiseLocalityHasDerivedCategory

/-- Additivity of the inverse image of `𝒪`-modules along the structure morphism of an étale
chart.  This is the general additivity of the inverse image of **Stacks 03D6**, part (2),
restated at the seating of the small étale ringed topoi, where instance search does not find it
with the universes undetermined. -/
local instance chartwiseLocalityAdditiveModulePullback (Y : AlgebraicSpaces B S hS)
    (V : SmallEtale B S hS Y.obj) :
    (modulePullback B S hS (chartToSpace B S hS Y V)).Additive :=
  Stacks.Sheaves.DerivedPullback.pullbackModules_additive
    (X := smallEtaleRingedTopos B S hS (chartSpace B S hS Y V))
    (Y := smallEtaleRingedTopos B S hS Y) _

/-- **Étale charts detect isomorphisms in `D⁺(𝒪_Y)`.**  A morphism of the bounded below derived
category of `𝒪_Y`-modules whose image under the bounded below right derived functor of the
inverse image along the structure morphism of every étale scheme chart of `Y` is invertible is
itself invertible.

A morphism of `D⁺` is invertible exactly when all of its cohomology maps are;  the inverse image
along a chart is exact, étale morphisms being flat, so its right derived functor carries the
degree-`n` cohomology map of `φ` to the degree-`n` cohomology map of the inverse image of `φ`;
and étale charts detect isomorphisms of `𝒪_Y`-modules.

The inverse image is converted to étale restriction, which is the form the degree-zero chart
criterion is stated at, by the comparison of **Stacks 03LW**
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`. -/
theorem isIso_of_forall_isIso_rightDerivedFunctorPlus_chartToSpace
    (Y : AlgebraicSpaces B S hS)
    {K L : DerivedCategory.Plus (Modules.{u, u} B S hS Y.obj Y.property)} (φ : K ⟶ L)
    (h : ∀ V : SmallEtale B S hS Y.obj,
      IsIso ((modulePullback B S hS (chartToSpace B S hS Y V)).rightDerivedFunctorPlus.map φ)) :
    IsIso φ := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro n
  refine isIso_of_forall_isIso_etaleModulePullback_chartToSpace B S hS Y
    ((DerivedCategory.Plus.homologyFunctor (Modules.{u, u} B S hS Y.obj Y.property) n).map φ)
    fun V => ?_
  have hflat : (smallEtaleRingedToposHom B S hS (chartToSpace B S hS Y V)).IsFlat :=
    (isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS (chartToSpace B S hS Y V)).1
      (isFlat_of_isEtale B S hS (isEtale_chartToSpace B S hS Y V))
  obtain ⟨hlim, hcolim⟩ :=
    (exactFunctor_iff _).1 (exactFunctor_modulePullback_of_isFlat B S hS
      (chartToSpace B S hS Y V) hflat)
  rw [← NatIso.isIso_map_iff
    (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Y V)
      (isEtale_chartToSpace B S hS Y V))]
  exact Stacks.AlgebraicGeometry.ModuleBaseChange.isIso_map_homologyFunctor_map
    (modulePullback B S hS (chartToSpace B S hS Y V)) φ (h V) n

/-- **Étale charts detect isomorphisms in `D⁺(𝒪_Y)`**, in the `↔` form:  a morphism of
`D⁺(𝒪_Y)` is invertible exactly when all of its derived chart inverse images are.  The forward
direction is functoriality. -/
theorem isIso_iff_forall_isIso_rightDerivedFunctorPlus_chartToSpace
    (Y : AlgebraicSpaces B S hS)
    {K L : DerivedCategory.Plus (Modules.{u, u} B S hS Y.obj Y.property)} (φ : K ⟶ L) :
    IsIso φ ↔ ∀ V : SmallEtale B S hS Y.obj,
      IsIso ((modulePullback B S hS (chartToSpace B S hS Y V)).rightDerivedFunctorPlus.map φ) :=
  ⟨fun hφ V => by
      have := hφ
      exact Functor.map_isIso _ _,
    isIso_of_forall_isIso_rightDerivedFunctorPlus_chartToSpace B S hS Y φ⟩

end AlgebraicGeometry.Space

end
