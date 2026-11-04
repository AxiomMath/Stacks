module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyBaseChangeFromDerived
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyLocalSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale

/-!
# Parts (2) and (3) of Stacks 0E1J from the inputs of the source's proof

The source proves parts (2) and (3) of Stacks 0E1J for a family of curves `f : X → S` with
`κ(s) = H⁰(X_s, 𝒪_{X_s})` for all `s ∈ S` from two facts about `Rf_*𝒪_X`:

* étale locally on `S`, `Rf_*𝒪_X ≅ 𝒪_S ⊕ M[-1]` with `M` finite free (Stacks 0E6B, part (b),
  sharpened by Stacks 0CTM, part (1), Cohomology, Proposition 02UZ and More on Algebra,
  Lemma 0BCD): `AlgebraicGeometry.CurveFamily.HasLocalDerivedPushforwardSplitting`;
* the formation of `Rf_*𝒪_X` commutes with arbitrary base change (Stacks 0CTM, part (1)):
  `AlgebraicGeometry.CurveFamily.HasDerivedStructureSheafBaseChange`.

This file assembles both parts from these two inputs. The vanishing of `Rf_*𝒪_X` above degree
`1`, used to read the base change isomorphism on `H¹`, is not a further input: it is read off the
local splitting, cohomological amplitude being étale local
(`AlgebraicGeometry.Space.isLE_of_isLE_smallEtaleDerivedModulePullback_chartToSpace`).

## Main results

* `AlgebraicGeometry.CurveFamily.hasDerivedStructureSheafPushforwardIsLEOne_of_localSplitting`:
  an étale-local splitting puts `Rf_*𝒪_X` in `D^{≤ 1}`.
* `AlgebraicGeometry.CurveFamily.firstHigherDirectImage_of_inputs`: the hypotheses `h2` and `h3`
  of the consumers of Stacks 0E1J
  (`AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of_h2_h3`) from the two
  inputs.

## Implementation notes

No declaration here carries a `stacks` attribute: both inputs are statements of other tags, not
proved in this development.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- `A[0] ⊕ M[-1]` has no cohomology above degree `1`. -/
theorem _root_.DerivedCategory.isLE_one_biprod_singleFunctor_zero_one {C : Type*} [Category C]
    [Abelian C] [HasDerivedCategory C] (A M : C) :
    ((DerivedCategory.singleFunctor C 0).obj A ⊞
      (DerivedCategory.singleFunctor C 1).obj M).IsLE 1 := by
  rw [DerivedCategory.isLE_iff]
  intro m hm
  have := preservesBinaryBiproducts_of_preservesBiproducts (DerivedCategory.homologyFunctor C m)
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor C m).mapBiprod _ _)
  exact (DerivedCategory.isZero_of_isLE _ 1 m hm).of_iso
    (isoZeroBiprod (DerivedCategory.isZero_of_isLE _ 0 m (by omega))).symm

/-- **An étale-local splitting `Rf_*𝒪_X ≅ 𝒪_S ⊕ M[-1]` puts `Rf_*𝒪_X` in `D^{≤ 1}`.** On each
chart of the covering the restriction is `𝒪[0] ⊕ 𝒪^{⊕ I}[-1]`, which has no cohomology above
degree `1`, and cohomological amplitude is étale local. -/
theorem hasDerivedStructureSheafPushforwardIsLEOne_of_localSplitting {X : CurveFamily B hZ}
    (h : X.HasLocalDerivedPushforwardSplitting) :
    X.HasDerivedStructureSheafPushforwardIsLEOne := by
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
  obtain ⟨ι, V, hV, hk⟩ := h
  refine Space.isLE_of_isLE_smallEtaleDerivedModulePullback_chartToSpace B integerBase hZ hV _ 1
    fun k => ?_
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ
      (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1
      (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).2)
  obtain ⟨I, -, ⟨e⟩⟩ := hk k
  have := DerivedCategory.isLE_one_biprod_singleFunctor_zero_one
    (C := Space.Modules.{u, u} B integerBase hZ
      (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1
      (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).2) (SheafOfModules.unit _)
    (SheafOfModules.free (R := Space.ringStructureSheaf B integerBase hZ
      (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1) I)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (((Space.smallEtaleDerivedModulePullbackIsoEtale B integerBase hZ
      (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
      (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) (V k))).app _) ≪≫ e).symm
    1

/-- **Parts (2) and (3) of Stacks 0E1J from the inputs of the source's proof**, in the form of
the hypotheses `h2` and `h3` of the consumers: if every family in `Curves^{h0,1}` has an
étale-local splitting `Rf_*𝒪_X ≅ 𝒪_S ⊕ M[-1]` with `M` finite free (Stacks 0E6B, part (b),
sharpened) and the base change clause of Stacks 0CTM, part (1), at `𝒪_X`, then for every such
family `R¹f_*𝒪_X` is finite locally free and its formation commutes with arbitrary base change. -/
theorem firstHigherDirectImage_of_inputs
    (hsplit : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasLocalDerivedPushforwardSplitting)
    (hbc : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasDerivedStructureSheafBaseChange) :
    (∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage) ∧
    (∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.FirstHigherDirectImageCommutesWithBaseChange) :=
  ⟨hasFiniteLocallyFreeFirstHigherDirectImage_of_forall_localSplitting hsplit,
    firstHigherDirectImageCommutesWithBaseChange_of_forall_derived hbc
      fun X hX => hasDerivedStructureSheafPushforwardIsLEOne_of_localSplitting (hsplit X hX)⟩

end CurveFamily

end AlgebraicGeometry

end
