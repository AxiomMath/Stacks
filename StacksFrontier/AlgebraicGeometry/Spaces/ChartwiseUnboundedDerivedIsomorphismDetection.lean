module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartwiseDerivedIsomorphismDetection
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Étale charts detect isomorphisms in the unbounded derived category of an algebraic space

The inverse image of `𝒪`-modules along a flat morphism of algebraic spaces is exact, so applying
it to complexes gives a functor between the unbounded derived categories. Along the structure
morphism of an étale scheme chart of `Y`, this is restriction of complexes to the chart. These
restrictions detect isomorphisms in `D(𝒪_Y)` for three reasons: a morphism of the derived
category is invertible when all of its cohomology sheaves are, restriction to a chart commutes
with taking cohomology sheaves, and étale charts detect isomorphisms of `𝒪_Y`-modules.

This is the unbounded counterpart of
`AlgebraicGeometry.Space.isIso_of_forall_isIso_rightDerivedFunctorPlus_chartToSpace`, which works
in `D⁺(𝒪_Y)`. It is the reduction "this we may check étale locally on `Y'`" in the proof of
Stacks Tag 0DL7.

## Main definitions

* `AlgebraicGeometry.Space.flatModuleDerivedPullback`: the functor `D(𝒪_{X'}) ⥤ D(𝒪_X)` induced
  by the exact inverse image of modules along a flat morphism `X ⟶ X'`.

## Main results

* `AlgebraicGeometry.Space.isIso_flatModuleDerivedPullback_map_iff`: the induced functor carries
  a morphism to an isomorphism exactly when the inverse image carries each of its cohomology
  sheaf maps to an isomorphism.
* `AlgebraicGeometry.Space.isIso_iff_forall_isIso_flatModuleDerivedPullback_chartToSpace`:
  **étale charts detect isomorphisms in `D(𝒪_Y)`**.

## Implementation notes

The statements hold for any models of the derived categories involved. They are taken over
arbitrary `HasDerivedCategory` instances, and no particular model is fixed.

## References

* [Stacks Project, Tag 0DL7](https://stacks.math.columbia.edu/tag/0DL7)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 073C](https://stacks.math.columbia.edu/tag/073C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Flat

variable {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
  (hg : (smallEtaleRingedToposHom B S hS g).IsFlat)
  [HasDerivedCategory.{w} (Modules.{u, u} B S hS X'.1 X'.2)]
  [HasDerivedCategory.{w'} (Modules.{u, u} B S hS X.1 X.2)]

/-- The functor `D(𝒪_{X'}) ⥤ D(𝒪_X)` induced by the inverse image of modules along a flat
morphism `X ⟶ X'`, which is exact, applied to complexes. -/
def flatModuleDerivedPullback :
    DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
  have h := (exactFunctor_iff (modulePullback B S hS g)).1
    (exactFunctor_modulePullback_of_isFlat B S hS g hg)
  have : (modulePullback B S hS g).Additive :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_additive
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS X') _
  have := h.1
  have := h.2
  (modulePullback B S hS g).mapDerivedCategory

/-- The functor induced by an exact inverse image carries a morphism to an isomorphism exactly
when the inverse image carries every cohomology sheaf map of that morphism to an isomorphism. -/
theorem isIso_flatModuleDerivedPullback_map_iff
    {K L : DerivedCategory (Modules.{u, u} B S hS X'.1 X'.2)} (φ : K ⟶ L) :
    IsIso ((flatModuleDerivedPullback B S hS g hg).map φ) ↔
      ∀ n : ℤ, IsIso ((modulePullback B S hS g).map
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X'.1 X'.2) n).map φ)) := by
  have h := (exactFunctor_iff (modulePullback B S hS g)).1
    (exactFunctor_modulePullback_of_isFlat B S hS g hg)
  have : (modulePullback B S hS g).Additive :=
    Stacks.Sheaves.DerivedPullback.pullbackModules_additive
      (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS X') _
  have := h.1
  have := h.2
  exact (modulePullback B S hS g).isIso_mapDerivedCategory_map_iff φ

end Flat

section Charts

variable (Y : AlgebraicSpaces B S hS)
  [HasDerivedCategory.{w} (Modules.{u, u} B S hS Y.1 Y.2)]
  [∀ V : SmallEtale B S hS Y.obj, HasDerivedCategory.{w'}
    (Modules.{u, u} B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2)]

omit [HasDerivedCategory.{w} (Modules.{u, u} B S hS Y.1 Y.2)]
  [∀ V : SmallEtale B S hS Y.obj, HasDerivedCategory.{w'}
    (Modules.{u, u} B S hS (chartSpace B S hS Y V).1 (chartSpace B S hS Y V).2)] in
/-- The structure morphism of an étale chart is flat, as a morphism of small étale ringed
topoi. -/
theorem smallEtaleRingedToposHom_chartToSpace_isFlat (V : SmallEtale B S hS Y.obj) :
    (smallEtaleRingedToposHom B S hS (chartToSpace B S hS Y V)).IsFlat :=
  (isFlat_iff_smallEtaleRingedToposHom_isFlat B S hS (chartToSpace B S hS Y V)).1
    (isFlat_of_isEtale B S hS (isEtale_chartToSpace B S hS Y V))

/-- **Étale charts detect isomorphisms in `D(𝒪_Y)`.** A morphism of the unbounded derived
category of `𝒪_Y`-modules is invertible exactly when its restriction to every étale scheme chart
of `Y` is. -/
theorem isIso_iff_forall_isIso_flatModuleDerivedPullback_chartToSpace
    {K L : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)} (φ : K ⟶ L) :
    IsIso φ ↔ ∀ V : SmallEtale B S hS Y.obj,
      IsIso ((flatModuleDerivedPullback B S hS (chartToSpace B S hS Y V)
        (smallEtaleRingedToposHom_chartToSpace_isFlat B S hS Y V)).map φ) := by
  refine ⟨fun _ V ↦ inferInstance, fun h ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_forall_isIso_etaleModulePullback_chartToSpace B S hS Y _ fun V ↦ ?_
  rw [← NatIso.isIso_map_iff
    (modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS Y V)
      (isEtale_chartToSpace B S hS Y V))]
  exact (isIso_flatModuleDerivedPullback_map_iff B S hS _ _ φ).1 (h V) n

end Charts

end AlgebraicGeometry.Space
