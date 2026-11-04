module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import StacksFrontier.AlgebraicGeometry.DenseDenominators.Localization
public import StacksFrontier.AlgebraicGeometry.DenseDenominators.Spectrum
public import StacksFrontier.RingTheory.UnitalSplitCoordinates

/-!
# Local sections of a finite morphism over a dense affine open subset

Let `Y` be a reduced scheme, `Ω` a dense affine open subset and `π : Z ⟶ Ω` a morphism whose
algebra of sections over the sections on `Ω` is module-finite, flat and of finite presentation,
with surjective spectrum. Then there is a surjective integral morphism `a : A ⟶ Y` such that
every point of `A` lying over a point of `Ω` has an affine open neighbourhood carrying a
morphism to `Z` over `Y`.

The algebra is passed in as `Stacks.DenseDenominators.SectionsData`, which also carries the
comparison of `Z` with the spectrum of that algebra; what the construction does with it is to
form the algebra of denominators of a presentation of it and take the relative spectrum.

## Main definitions

* `Stacks.DenseDenominators.SectionsData` is the algebraic input.
* `Stacks.DenseDenominators.IsQcohAll` is the quasi-coherence of every denominator algebra
  over `Ω`.

## Main results

* `Stacks.DenseDenominators.exists_integralHom_surjective_section_of_sectionsData` is the
  conclusion.

## Implementation notes

The linear functional sending `1` to `1` that the injectivity of the structure morphism needs
is the zeroth coordinate of the split coordinate system of
`Stacks.UnitalSplitCoordinates.exists_split_coordinates`, which is where the surjectivity of
the spectrum of the algebra is used; nothing else uses it.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.FiniteAlgebraPresentation

universe u

namespace Stacks.DenseDenominators

/-- **The algebraic input of the construction**: an algebra of sections for a morphism over an
affine open subset. It is module-finite, flat and of finite presentation over the sections on
`Ω`, its spectrum surjects onto theirs, and its spectrum maps to the source of the morphism
compatibly over the base. -/
structure SectionsData {Y : Scheme.{u}} {Ω : Y.Opens} (hΩ : IsAffineOpen Ω) {Z : Scheme.{u}}
    (π : Z ⟶ Ω.toScheme) where
  /-- The algebra of sections. -/
  S : Type u
  /-- Its ring structure. -/
  [commRing : CommRing S]
  /-- Its algebra structure over the sections on `Ω`. -/
  [algebra : Algebra Γ(Y, Ω) S]
  /-- It is module-finite. -/
  [finite : Module.Finite Γ(Y, Ω) S]
  /-- It is of finite presentation. -/
  [finitePresentation : Module.FinitePresentation Γ(Y, Ω) S]
  /-- It is flat. -/
  [flat : Module.Flat Γ(Y, Ω) S]
  /-- Its spectrum surjects onto the spectrum of the sections on `Ω`. -/
  specSurjective : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(Y, Ω) S))
  /-- The comparison of its spectrum with the source of the morphism. -/
  σ : Spec (CommRingCat.of S) ⟶ Z
  /-- The comparison is compatible with the two morphisms to the base. -/
  σ_comp : σ ≫ π ≫ Ω.ι
    = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, Ω) S)) ≫ hΩ.fromSpec

attribute [instance] SectionsData.commRing SectionsData.algebra SectionsData.finite
  SectionsData.finitePresentation SectionsData.flat

variable {Y : Scheme.{u}} {Ω : Y.Opens}

/-- **Quasi-coherence of every algebra of denominators over `Ω`.** This is the hypothesis the
construction rests on; it holds whenever `Y` is reduced and `Ω` is dense. -/
def IsQcohAll (Y : Scheme.{u}) (Ω : Y.Opens) : Prop :=
  ∀ (S : Type u) [CommRing S] [Algebra Γ(Y, Ω) S] [Module.Flat Γ(Y, Ω) S]
    (P : Presentation Γ(Y, Ω) S), IsQcoh P

/-- **Every algebra of denominators over a dense affine open of a reduced scheme is
quasi-coherent.** This is `Stacks.DenseDenominators.isLocalization_away_sub`, packaged. -/
theorem isQcohAll [IsReduced Y] (hd : Dense (Ω : Set Y)) : IsQcohAll Y Ω :=
  fun _ _ _ _ P _U hU r => isLocalization_away_sub hd P hU r

/-- **Local sections from the algebraic input.** The algebra of denominators of a presentation
of the algebra of sections has a relative spectrum which is integral and surjective over `Y`,
and over an affine open subset of `Ω` its charts carry a morphism to the spectrum of that
algebra, hence to `Z`. -/
theorem exists_integralHom_surjective_section_of_sectionsData [IsReduced Y]
    (hd : Dense (Ω : Set Y)) (hΩ : IsAffineOpen Ω) {Z : Scheme.{u}}
    {π : Z ⟶ Ω.toScheme} (D : SectionsData hΩ π) (y : Y) (hy : y ∈ Ω) :
    ∃ (A : Scheme.{u}) (a : A ⟶ Y), IsIntegralHom a ∧ Surjective a ∧
      ∀ α : A, a.base α = y → ∃ V : A.Opens, IsAffineOpen V ∧ α ∈ V ∧
        ∃ v : V.toScheme ⟶ Z, v ≫ π ≫ Ω.ι = V.ι ≫ a := by
  have hproj : Module.Projective Γ(Y, Ω) D.S := Module.Flat.projective_of_finitePresentation
  obtain ⟨k, crd, rtr, hrtr, hcrd⟩ :=
    Stacks.UnitalSplitCoordinates.exists_split_coordinates Γ(Y, Ω) D.S D.specSurjective
  obtain ⟨P⟩ := exists_presentation Γ(Y, Ω) D.S
  have hφ : ((LinearMap.proj (0 : Fin (k + 1))).comp crd) 1 = 1 := by
    change crd 1 0 = 1
    rw [hcrd, Pi.single_eq_same]
  obtain ⟨A, a, haint, hasurj, hsec⟩ :=
    exists_integralHom_surjective_specSection P hd ((LinearMap.proj 0).comp crd) hφ
      (isQcohAll hd D.S P) hΩ
  refine ⟨A, a, haint, hasurj, fun α hα => ?_⟩
  obtain ⟨V, hVaff, hαV, v, hv⟩ := hsec α (hα ▸ hy)
  refine ⟨V, hVaff, hαV, v ≫ D.σ, ?_⟩
  calc (v ≫ D.σ) ≫ π ≫ Ω.ι = v ≫ D.σ ≫ π ≫ Ω.ι := by rw [Category.assoc]
    _ = v ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, Ω) D.S)) ≫ hΩ.fromSpec :=
        congrArg (fun g => v ≫ g) D.σ_comp
    _ = V.ι ≫ a := hv

end Stacks.DenseDenominators

end
