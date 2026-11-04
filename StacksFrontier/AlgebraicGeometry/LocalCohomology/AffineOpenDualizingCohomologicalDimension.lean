module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionConstruction
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings
public import StacksFrontier.RingTheory.LocalCohomology.TopLocalCohomology
public import StacksFrontier.RingTheory.Dualizing.FiniteDimension
public import StacksFrontier.RingTheory.Dualizing.UbiquityStability

/-!
# Affine opens with a dualizing complex and a bound on the cohomological dimension

Let `X` be a locally Noetherian scheme which locally has a dualizing complex, and let `ℐ` be a
quasi-coherent sheaf of ideals such that every point has an affine open neighbourhood `W` with
`cd(Γ(X, W), ℐ(W)) ≤ d`. Then every point has a single affine open neighbourhood `U` on which both
hold: `Γ(X, U)` has a dualizing complex and `cd(Γ(X, U), ℐ(U)) ≤ d`.

Given an affine neighbourhood `V` with a dualizing complex and an affine neighbourhood `W` with the
bound, a basic open `U = D(f) ⊆ V ∩ W` around the point does both: `Γ(X, U)` is the localization
of `Γ(X, V)` at `f`, and a dualizing complex localizes ([Stacks, Tag 0A7G]); and `ℐ(U)` is the
extension of `ℐ(W)` along the restriction `Γ(X, W) → Γ(X, U)`, so the cohomological dimension can
only drop ([Stacks, Tag 0DXA]).

A Noetherian ring with a dualizing complex has finite Krull dimension, and so does its completion
along any ideal, which again has a dualizing complex.

## Main results

* `Stacks.Algebraization.exists_affineOpen_isDualizingComplex_cohomologicalDimension_le` — the
  common affine neighbourhood.
* `Stacks.Algebraization.ringKrullDim_lt_top_and_adicCompletion_of_isDualizingComplex` — a
  Noetherian ring with a dualizing complex and its completion along an ideal have finite Krull
  dimension.

## References

* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0DXA](https://stacks.math.columbia.edu/tag/0DXA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-- A Noetherian ring with a dualizing complex has finite Krull dimension, and so does its
completion along any ideal: the completion again has a dualizing complex. -/
theorem ringKrullDim_lt_top_and_adicCompletion_of_isDualizingComplex {A : Type u} [CommRing A]
    [IsNoetherianRing A] (J : Ideal A)
    (h : ∃ ω : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex ω) :
    ringKrullDim A < ⊤ ∧ ringKrullDim (AdicCompletion J A) < ⊤ := by
  obtain ⟨L, hL⟩ := Dualizing.exists_isDualizingComplex_adicCompletion J h
  obtain ⟨ω, hω⟩ := h
  exact ⟨Dualizing.ringKrullDim_lt_top_of_isDualizingComplex hω,
    Dualizing.ringKrullDim_lt_top_of_isDualizingComplex hL⟩

/-- **An affine open with both a dualizing complex and the bound on the cohomological dimension
around every point.** Let `X` be locally Noetherian, locally with a dualizing complex, and let `ℐ`
be a quasi-coherent sheaf of ideals such that every point has an affine neighbourhood `W` with
`cd(Γ(X, W), ℐ(W)) ≤ d`. Then every point `x` has an affine neighbourhood `U` such that
`Γ(X, U)` has a dualizing complex and `cd(Γ(X, U), ℐ(U)) ≤ d`. -/
theorem exists_affineOpen_isDualizingComplex_cohomologicalDimension_le {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (I : X.IdealSheafData) (d : ℤ)
    (hcd : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
      Stacks.LocalCohomology.cohomologicalDimension Γ(X, U.1) (I.ideal U)
        (Ideal.fg_of_isNoetherianRing _) ≤ d)
    (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
      (∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U.1)), Dualizing.IsDualizingComplex ω) ∧
      Stacks.LocalCohomology.cohomologicalDimension Γ(X, U.1) (I.ideal U)
        (Ideal.fg_of_isNoetherianRing _) ≤ d := by
  obtain ⟨V, hxV, hV⟩ := hdual x
  obtain ⟨W, hxW, hW⟩ := hcd x
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter V.2 W.2 x ⟨hxV, hxW⟩
  let U : X.affineOpens := X.affineBasicOpen f
  have hUW : U ≤ W := hfg.trans_le (X.basicOpen_le g)
  have : IsNoetherianRing Γ(X, V.1) := IsLocallyNoetherian.component_noetherian V
  have : IsNoetherianRing Γ(X, W.1) := IsLocallyNoetherian.component_noetherian W
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  refine ⟨U, hxf, ?_, ?_⟩
  · obtain ⟨ω, hω⟩ := hV
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := V.2.isLocalization_basicOpen f
    exact ⟨_, Dualizing.isDualizingComplex_localization (B := Γ(X, X.basicOpen f))
      (Submonoid.powers f) ω hω⟩
  · let ρ := (X.presheaf.map (homOfLE (show U.1 ≤ W.1 from hUW)).op).hom
    have hmap : (I.ideal W).map ρ = I.ideal U := I.map_ideal hUW
    have hle := Stacks.LocalCohomology.cohomologicalDimension_map_le ρ (I.ideal W)
      (Ideal.fg_of_isNoetherianRing _)
    rw [Stacks.LocalCohomology.cohomologicalDimension_congr _
      (Ideal.fg_of_isNoetherianRing _) hmap] at hle
    exact hle.trans hW

end Stacks.Algebraization

end
