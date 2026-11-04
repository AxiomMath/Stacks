module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.GorensteinBlowupSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingProjective
import StacksCore.Tactic.StacksAttribute

/-!
# A rational surface singularity becomes Gorenstein after blowing up singular points

Let `(A, 𝔪, κ)` be a local normal Nagata domain of dimension two defining a rational singularity
and having a dualizing complex. Then a finite sequence of blowups in singular closed points, with
normal stages, ends in a scheme whose dualizing module is invertible. This is [Stacks, Tag 0BBV].

The statement follows from
`exists_singularPointBlowupChain_isDualizingModule_isInvertible_of_isDualizingComplex`, together
with the fact that the blowup `f : X ⟶ Spec(R)` of a ring `R` of Situation [Stacks, Tag 0B4W] in
its maximal ideal has `f^!(ω_R)` a dualizing complex, which is
`RationalSingularitySituation.isDualizingComplex_relativeDualizingComplex_blowUp`.

## Main results

* `AlgebraicGeometry.exists_singularPointBlowupChain_isDualizingModule_isInvertible` —
  [Stacks, Tag 0BBV].
* `AlgebraicGeometry.exists_singularPointBlowupChain_isGorenstein` — the same with the end of the
  sequence Gorenstein.

## References

* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Let `A` be a local normal Nagata domain of dimension two which defines a rational singularity
and has a dualizing complex. Then there is a finite sequence of blowups in singular closed points
`X = Xₙ ⟶ … ⟶ X₁ ⟶ X₀ = Spec(A)` with every `Xᵢ` normal such that the dualizing module of `X` is
an invertible `𝒪_X`-module. -/
@[stacks 0BBV]
theorem exists_singularPointBlowupChain_isDualizingModule_isInvertible
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    (hN : IsNagataRing A) (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A)
    (hdual : letI : IsNoetherianRing A := hN.1
      letI := HasDerivedCategory.standard (ModuleCat.{u} A)
      ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
      SingularPointBlowupChain IsNormal (Spec (.of A)) X f ∧
        ∃ _ : IsLocallyNoetherian X, ∃ ω : X.Modules, Stacks.Duality.IsDualizingModule ω ∧
          AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ω :=
  exists_singularPointBlowupChain_isDualizingModule_isInvertible_of_isDualizingComplex
    RationalSingularitySituation.isDualizingComplex_relativeDualizingComplex_blowUp A hN hdim hrat
    hdual

/-- Let `A` be a local normal Nagata domain of dimension two which defines a rational singularity
and has a dualizing complex. Then there is a finite sequence of blowups in singular closed points
with normal stages ending in a Gorenstein scheme. -/
theorem exists_singularPointBlowupChain_isGorenstein
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hN : IsNagataRing A) (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A)
    (hdual : letI := HasDerivedCategory.standard (ModuleCat.{u} A)
      ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
      SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsGorenstein Y :=
  exists_singularPointBlowupChain_isGorenstein_of_isDualizingComplex
    RationalSingularitySituation.isDualizingComplex_relativeDualizingComplex_blowUp A hN hdim hrat
    hdual

end AlgebraicGeometry

end
