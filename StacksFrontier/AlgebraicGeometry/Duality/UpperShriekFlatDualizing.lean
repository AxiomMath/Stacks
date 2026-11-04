module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekHomothety
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeTorDimension
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekStructureSheafCharts
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativePerfectionPerfect

/-!
# `f^!𝒪_Y` for a flat morphism of `FTS S`

Let `f : X ⟶ Y` be a flat morphism of `AlgebraicGeometry.FTS S`, `S` Noetherian, and `j` any
compactification of `X` over `Y`. From the affine chart description of `f^!𝒪_Y`
(`Stacks.Duality.UpperShriekStructureSheafCharts f j`) this file deduces the two assertions of
[Stacks, Tag 0E9T]: `f^!𝒪_Y` is `Y`-perfect, and `𝒪_X ⟶ R𝓗om(f^!𝒪_Y, f^!𝒪_Y)` is an
isomorphism.

## Main results

* `Stacks.Duality.upperShriek_structureSheaf_isPerfectRelativeTo_and_isIso_homothety` —
  **[Stacks, Tag 0E9T]**: for `f` flat and every compactification `j`, `f^!𝒪_Y` is `Y`-perfect
  and `𝒪_X ⟶ R𝓗om(f^!𝒪_Y, f^!𝒪_Y)` is an isomorphism.
* `Stacks.Duality.isShriekOfStructureSheafOnCharts_of_upperShriekStructureSheafCharts` — the
  chart description at one chart around each point, from the chart description at every chart.

## Implementation notes

`f^!𝒪_Y` is `Stacks.Duality.relativeDualizingComplexObj f j`, the value at `𝒪_Y` of
`Stacks.Duality.upperShriek f j`, which is defined at the locally small model of `D(𝒪_X)`. Both
assertions are read on the same object at `HasDerivedCategory.standard`, the model at which
relative perfectness (at the genuine tensor family
`RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily`) and the derived internal Hom with its
homothety `Stacks.SheafOfModules.derivedSheafHomothety` are stated; the two models have the same
objects. The proof is the source's: the assertions are local on `X`, so they follow from the
affine chart description `Stacks.Duality.upperShriekStructureSheafCharts` ([Stacks, Tag 0BV2])
and the algebra of [Stacks, Tag 0BZW] on each chart.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {X Y : AlgebraicGeometry.FTS S}
  (f : X ⟶ Y) (j : AlgebraicGeometry.CompactificationOf (Over.mk f.left))

/-- **One chart around each point from every chart.** If `f^!𝒪_Y` has the chart description at
every affine chart and every polynomial presentation, then around each point of `X` it has it at
some chart. -/
theorem isShriekOfStructureSheafOnCharts_of_upperShriekStructureSheafCharts
    (h : UpperShriekStructureSheafCharts f j) :
    letI := HasDerivedCategory.standard X.left.Modules
    IsShriekOfStructureSheafOnCharts f (relativeDualizingComplexObj f j) := by
  intro x
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y.left) (x := f.left.base x) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X.left) (x := x) (U := f.left ⁻¹ᵁ V) hxV
  obtain ⟨p⟩ := Dualizing.nonempty_polynomialPresentation (f.left.appLE V U hUV).hom
    (f.left.finiteType_appLE hV hU hUV)
  refine ⟨U, hU, V, hV, hUV, hxU, p, ?_⟩
  obtain ⟨e⟩ := h V hV U hU hUV p
  let := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme
  exact ⟨Stacks.Injectives.mapDerivedCategoryObjIso X.left.Modules
    (Scheme.Modules.restrictFunctor U.ι) (relativeDualizingComplexObj f j) ≪≫ e⟩

section Flat

attribute [local instance 10000] HasDerivedCategory.standard

variable [Flat f.left]

/-- `f^!𝒪_Y`, with the chart description, as an object of `D_QCoh(𝒪_X)` at the standard model:
its cohomology sheaves are coherent, hence quasi-coherent. -/
def relativeDualizingComplexQCoh (h : UpperShriekStructureSheafCharts f j) :
    quasiCoherentDerivedCategory.{u + 1, u} X.left :=
  have hXn : IsLocallyNoetherian X.left := inferInstance
  haveI := locallyOfFinitePresentation_left f
  ⟨relativeDualizingComplexObj f j, fun i => by
    have hmodels : ∀ x : X.left,
        HasTildeModelAt.{u, u + 1} (relativeDualizingComplexObj f j) x := by
      intro x
      obtain ⟨U, hU, V, hV, hUV, hxU, p, he⟩ :=
        isShriekOfStructureSheafOnCharts_of_upperShriekStructureSheafCharts f j h x
      exact ⟨U, hU, hxU, _,
        derivedCategoryBBounded_upperShriekFunctor_structureModel_of_perfect f hU hV hUV p, he⟩
    have := isCoherent_homology_of_tildeModels hmodels i
    exact isQuasicoherent_of_isCoherent _⟩

/-- **[Stacks, Tag 0E9T] from the chart description, first assertion**: for `f` flat,
`f^!𝒪_Y` is perfect relative to `Y`. -/
theorem isPerfectRelativeTo_relativeDualizingComplex_of_charts
    (h : UpperShriekStructureSheafCharts f j) :
    letI := locallyOfFinitePresentation_left f
    f.left.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      (relativeDualizingComplexObj f j) :=
  isPerfectRelativeTo_of_isShriekOfStructureSheafOnCharts f (relativeDualizingComplexQCoh f j h)
    (isShriekOfStructureSheafOnCharts_of_upperShriekStructureSheafCharts f j h)

/-- **[Stacks, Tag 0E9T] from the chart description, second assertion**: for `f` flat, the
homothety `𝒪_X ⟶ R𝓗om(f^!𝒪_Y, f^!𝒪_Y)` is an isomorphism. -/
theorem isIso_derivedSheafHomothety_relativeDualizingComplex_of_charts
    (h : UpperShriekStructureSheafCharts f j) :
    IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.left.sheaf
      (relativeDualizingComplexObj f j)) :=
  isIso_derivedSheafHomothety_of_isShriekOfStructureSheafOnCharts f _
    (isShriekOfStructureSheafOnCharts_of_upperShriekStructureSheafCharts f j h)

/-- **Stacks Project, Tag 0E9T (Lemma 48.17.10).** In Situation 48.16.1 (`S` Noetherian), let
`f : X ⟶ Y` be a flat morphism of `FTS S`, with `f^!` computed at any compactification `j`. Then
`f^!𝒪_Y` is a `Y`-perfect object of `D(𝒪_X)` and `𝒪_X ⟶ R𝓗om_{𝒪_X}(f^!𝒪_Y, f^!𝒪_Y)` is an
isomorphism. -/
@[stacks 0E9T]
theorem upperShriek_structureSheaf_isPerfectRelativeTo_and_isIso_homothety :
    (letI := locallyOfFinitePresentation_left f;
      Scheme.Hom.IsPerfectRelativeTo.{u + 1, u + 1} f.left
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        (relativeDualizingComplexObj f j)) ∧
      IsIso (Stacks.SheafOfModules.derivedSheafHomothety X.left.sheaf
        (relativeDualizingComplexObj f j)) :=
  ⟨isPerfectRelativeTo_relativeDualizingComplex_of_charts f j
      (upperShriekStructureSheafCharts f j),
    isIso_derivedSheafHomothety_relativeDualizingComplex_of_charts f j
      (upperShriekStructureSheafCharts f j)⟩

end Flat

end Stacks.Duality
