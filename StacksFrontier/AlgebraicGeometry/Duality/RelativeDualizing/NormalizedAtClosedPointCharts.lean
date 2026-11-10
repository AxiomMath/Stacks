module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.AssociatedShiftFunctionRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.NormalizedStalksOfClosedPoints
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexOfCharts

/-!
# Normalization at a closed point over a closed point, from the chart description of `f^!`

Let `S` be a Noetherian scheme with a dualizing complex `ω_S^•`, let `p : X ⟶ S` be of finite type
and let `ω_X^•` be normalized relative to `ω_S^•`: near every point of `X` there is an affine open
`U` with `ω_X^•|_U ≅ (U ⟶ S)^! ω_S^•`. If `x ∈ X` is a closed point over a closed point `s` and
`ω_{S,s}^•` is a normalized dualizing complex over `𝒪_{S,s}`, then `ω_{X,x}^•` is a normalized
dualizing complex over `𝒪_{X,x}`. This is [Stacks, Tag 0AWL]; the closedness of `s` turns out
not to be needed.

The proof is the source's: replace `X` by an affine neighbourhood `U` of `x`, where
`ω_X^• = (U ⟶ S)^! ω_S^•`. On affine charts `(U ⟶ S)^! ω_S^•` is the algebraic upper shriek of a
model of `ω_S^•` ([Stacks, Tag 0BV2]), whose dimension function at a maximal ideal is that of
the model at the prime below it
(`Dualizing.PolynomialPresentation.dualizingDimension_upperShriekFunctor_of_isMaximal`, the
computation the source makes through [Stacks, Tag 0AA2] and [Stacks, Tag 0GEW]). The dimension
function of [Stacks, Tag 0AWF] is local
(`Stacks.Duality.associatedShiftFunction_restrict_of_isOpenImmersion`), and it vanishes at a point
exactly when the stalk is normalized.

## Main results

* `Stacks.Duality.isNormalizedDualizingComplex_derivedStalkOfComplex` — [Stacks, Tag 0AWL].

## Implementation notes

The relative normalization of `ω_X^•` enters only through the local isomorphisms with
`(U ⟶ S)^! ω_S^•`, one affine `U` around each point and any compactification of `U` over `S`.
These are part of the data of a dualizing complex normalized relative to `ω_S^•`
([Stacks, Tag 0AUA]), so the hypothesis is implied by the source's. Normalization of a stalk is
asked of the derived stalk of a representative; it does not depend on the representative.

## References

* [Stacks Project, Tag 0AWL](https://stacks.math.columbia.edu/tag/0AWL)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0AUA](https://stacks.math.columbia.edu/tag/0AUA)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

open ChartCompactification _root_.Stacks.Duality.ProjectiveSpace
  _root_.AlgebraicGeometry.ProjectiveSpace Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Derived categories of modules over a ring are taken at the standard model, as
`Dualizing.IsNormalizedDualizingComplex` requires; those of sheaves of modules are not affected. -/
local instance (priority := 10000) (A : Type u) [CommRing A] :
    HasDerivedCategory (ModuleCat.{u} A) :=
  HasDerivedCategory.standard _

/-- **Stacks Project, Tag 0AWL (Lemma 48.21.1).** Let `S` be a Noetherian scheme with a
dualizing complex `ω_S^•`, let `p : X ⟶ S` be of finite type, and let `ω_X^•` be normalized
relative to `ω_S^•`: every point has an affine open neighbourhood `U` with
`ω_X^•|_U ≅ (U ⟶ S)^! ω_S^•` for a compactification of `U` over `S`. Let `x ∈ X` be a closed
point and `s = p x`. If `ω_{S,s}^•` is a normalized dualizing complex over `𝒪_{S,s}`, then
`ω_{X,x}^•` is a normalized dualizing complex over `𝒪_{X,x}`. The source also asks that `s` be
closed; this is not needed. -/
@[stacks 0AWL]
theorem isNormalizedDualizingComplex_derivedStalkOfComplex
    {S X : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] (p : X ⟶ S) [LocallyOfFiniteType p]
    (ωS : quasiCoherentDerivedCategory S) (hωS : IsDualizingComplex ωS.obj)
    (ωX : DerivedCategory X.Modules)
    (hωX : ∀ x : X, ∃ (U : X.Opens) (_ : IsAffine U.toScheme) (_ : x ∈ U)
      (j : CompactificationOf (Over.mk (ftsHomToBase (U.ι ≫ p)).left)),
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj ωX ≅
        ((upperShriek (ftsHomToBase (U.ι ≫ p)) j).obj ωS).obj))
    (x : X) (hx : IsClosed ({x} : Set X))
    (hωSs : ∃ E : CochainComplex S.Modules ℤ, Nonempty (DerivedCategory.Q.obj E ≅ ωS.obj) ∧
      Dualizing.IsNormalizedDualizingComplex.{u, u} (derivedStalkOfComplex (p x) E)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    ∀ E : CochainComplex X.Modules ℤ, Nonempty (DerivedCategory.Q.obj E ≅ ωX) →
      Dualizing.IsNormalizedDualizingComplex.{u, u} (derivedStalkOfComplex x E) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  rintro E ⟨eE⟩
  have hzero : ∀ {Z : Scheme.{u}} [IsLocallyNoetherian Z] (z : Z) (F : CochainComplex Z.Modules ℤ),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ((derivedStalkOfComplex z F)⟦-(0 : ℤ)⟧) ↔
        Dualizing.IsNormalizedDualizingComplex.{u, u} (derivedStalkOfComplex z F) :=
    fun {Z} _ z F => Dualizing.isNormalizedDualizingComplex_congr.{u, u}
      ((shiftFunctorZero' (DerivedCategory (ModuleCat.{u} (Z.presheaf.stalk z)))
        (-(0 : ℤ)) (by simp)).app _)
  obtain ⟨U, hUa, hxU, j, ⟨e⟩⟩ := hωX x
  let g := ftsHomToBase (U.ι ≫ p)
  let x' : U.toScheme := ⟨x, hxU⟩
  have hx' : IsClosed ({x'} : Set U.toScheme) := by
    have : ({x'} : Set U.toScheme) = U.ι.base ⁻¹' {x} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩
    rw [this]
    exact hx.preimage U.ι.base.hom.continuous
  obtain ⟨ES, hES, hN⟩ := hωSs
  have hδL : associatedShiftFunction ((upperShriek g j).obj ωS).obj x' = 0 :=
    (associatedShiftFunction_eq_of_hasUpperShriekCharts (U.ι ≫ p) hωS
      (UpperShriekCharts.hasUpperShriekCharts g j
        (upperShriekCharts g j ωS (isBoundedBelow_of_isDualizingComplex _ hωS))) hx').trans
      (((isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hωS).2.1 (p x) ES
        hES 0).mp ((hzero (p x) ES).mpr hN)).symm
  have hU : Dualizing.IsNormalizedDualizingComplex.{u, u}
      (derivedStalkOfComplex x' (restrictComplex U.ι E)) :=
    (associatedShiftFunction_eq_zero_iff (isDualizingComplex_upperShriek_obj g j ωS hωS)
      x').mp hδL _
      ⟨((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategoryFactors.app E).symm ≪≫
        (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.mapIso eE ≪≫ e⟩
  exact (hzero x E).mp
    ((isNormalizedDualizingComplex_derivedStalkOfComplex_restrict_iff U.ι x' E 0).mp
      ((hzero x' _).mpr hU))

end Stacks.Duality

end
