module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.GradedSplitting
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import Mathlib.RingTheory.Flat.Localization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness of sections over affine opens

Two flatness inputs of the thickening induction of the cube proof (step
1(a)), where the graded pieces `Iⁿ⁺¹ℒ / Iⁿ⁺²ℒ` of an invertible module `ℒ` on a flat
`X ⟶ Spec R` are identified with copies of `ℒ / Iℒ`.

## Main results

* `Stacks.CubeOpenAtUnit.flat_baseSectionHom`: for a flat morphism `g : X ⟶ Spec R` and an
  affine open `U ⊆ X`, the ring map `R ⟶ Γ(X, U)` is flat.
* `Stacks.CubeOpenAtUnit.flat_sections_of_isInvertible`: the sections of an invertible module
  over an affine open `U` form a flat `Γ(X, U)`-module.

## Implementation notes

The second statement is proved stalkwise: an invertible module is finite locally free of rank
one, so it is quasi-coherent and its stalks are free over the local rings; over an affine open
the stalk at `x` is the localization of the sections at the prime of `x`
(`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ`), and the local rings are
localizations of `Γ(X, U)`, so flatness is checked at the maximal ideals.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.CubeOpenAtUnit

/-- For a flat morphism `g : X ⟶ Spec R` and an affine open `U` of `X`, the ring map
`R ⟶ Γ(X, U)` induced by `g` is flat. -/
@[sga "3 VIB 11.3" "special case"]
theorem flat_baseSectionHom {R : Type u} [CommRing R] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of R)) [Flat g] (U : X.affineOpens) :
    (Stacks.Coherent.baseSectionHom R g U.1).Flat := by
  have hle : U.1 ≤ g ⁻¹ᵁ ⊤ := le_top
  have heq : Stacks.Coherent.baseSectionHom R g U.1 =
      (g.appLE ⊤ U.1 hle).hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom := by
    simp only [Stacks.Coherent.baseSectionHom, Scheme.Hom.appLE, CommRingCat.hom_comp]
    rfl
  rw [heq]
  exact RingHom.Flat.comp
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv))
    (HasRingHomProperty.appLE @Flat g ‹Flat g› ⟨⊤, isAffineOpen_top _⟩ U hle)

section Invertible

variable {X : Scheme.{u}} (N : X.Modules)

/-- An invertible module in the `Stacks.SheafOfModules.IsInvertible` spelling is finite locally
free of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible
    [hN : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := X.Opens)
      (J := Opens.grothendieckTopology X) N 1 :=
  (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one X N).mp hN

/-- The stalk of a finite locally free module of rank one at a point of an affine open `U` is a
flat `Γ(X, U)`-module. -/
theorem flat_stalk_of_isFiniteLocallyFreeOfRank_one
    [hfree : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := X.Opens)
      (J := Opens.grothendieckTopology X) N 1]
    {U : X.Opens} (hU : IsAffineOpen U) (y : U) :
    letI := Stacks.ModuleStalkSpecialization.sectionsStalkModule N y.2
    Module.Flat Γ(X, U) (N.presheaf.stalk y.1) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule N y.1
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule N y.2
  let := (X.presheaf.germ U y.1 y.2).hom.toAlgebra
  have := Stacks.ModuleStalkSpecialization.isScalarTower_sectionsStalk N y.2
  have : Module.Free (X.presheaf.stalk y.1) (N.presheaf.stalk y.1) :=
    AlgebraicGeometry.SheafOfModules.free_stalk_of_isFiniteLocallyFreeOfRank N 1 y.1
  have : IsLocalization.AtPrime (X.presheaf.stalk y.1) (hU.primeIdealOf y).asIdeal :=
    hU.isLocalization_stalk y
  have : Module.Flat Γ(X, U) (X.presheaf.stalk y.1) :=
    IsLocalization.flat _ (hU.primeIdealOf y).asIdeal.primeCompl
  exact Module.Flat.trans Γ(X, U) (X.presheaf.stalk y.1) (N.presheaf.stalk y.1)

/-- The sections of a finite locally free module of rank one over an affine open `U` form a flat
`Γ(X, U)`-module. -/
theorem flat_sections_of_isFiniteLocallyFreeOfRank_one
    [hfree : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := X.Opens)
      (J := Opens.grothendieckTopology X) N 1]
    (U : X.affineOpens) : Module.Flat Γ(X, U.1) Γ(N, U.1) := by
  have : N.IsQuasicoherent := by
    obtain ⟨q, hq, -⟩ := hfree.exists_isFiniteLocallyFreeOfRankData
    have := hq
    exact q.quasiCoherentData.isQuasicoherent
  have hU := U.2
  refine Module.flat_of_localized_maximal (R := Γ(X, U.1)) (M := Γ(N, U.1))
    fun P hP => ?_
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.forgetToTop.map hU.isoSpec.hom)).2 (⟨P, hP.isPrime⟩ : PrimeSpectrum Γ(X, U.1))
  obtain rfl : P = (hU.primeIdealOf y).asIdeal := congrArg PrimeSpectrum.asIdeal hy.symm
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule N y.2
  have : IsLocalizedModule (hU.primeIdealOf y).asIdeal.primeCompl
      (Stacks.ModuleStalkSpecialization.germₗ N y.2) :=
    Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ N hU y.2
  have := flat_stalk_of_isFiniteLocallyFreeOfRank_one N hU y
  exact Module.Flat.of_linearEquiv (IsLocalizedModule.iso (hU.primeIdealOf y).asIdeal.primeCompl
    (Stacks.ModuleStalkSpecialization.germₗ N y.2))

/-- The sections of an invertible module over an affine open `U` form a flat `Γ(X, U)`-module:
an invertible module is finite locally free of rank one. -/
theorem flat_sections_of_isInvertible
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    (U : X.affineOpens) : Module.Flat Γ(X, U.1) Γ(N, U.1) :=
  @flat_sections_of_isFiniteLocallyFreeOfRank_one X N
    (isFiniteLocallyFreeOfRank_one_of_isInvertible N) U

end Invertible

end Stacks.CubeOpenAtUnit

end
