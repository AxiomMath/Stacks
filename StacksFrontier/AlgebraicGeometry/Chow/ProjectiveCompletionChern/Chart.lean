module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.DegreeOneZeroLocus
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Tower

/-!
# The open `T ≠ 0` of the projective completion, on charts

Let `E = Proj_X(Sym^*(𝒞)[T])` be the projective completion of the vector bundle of a finite
locally free `𝒪_X`-module `𝒞`, with twist `𝒪_E(1)` and the section `T` of `𝒪_E(1)` given by the
variable. Write `C ⊆ E` for the open complement of the zero scheme of `T`. Over an affine open
`V` of `X` the inverse image of `E` is the projective spectrum `Proj Γ(V, Sym^*(𝒞)[T])`, and on
it `C` is the standard open `D₊(T)`.

## Main definitions

* `Stacks.Chow.ProjectiveCompletion.sectionT`: the unit of the summand `𝒪_X` of `𝒞 ⊕ 𝒪_X`.
* `Stacks.Chow.ProjectiveCompletion.coordT`: the section `T` of `𝒪_E(1)`.
* `Stacks.Chow.ProjectiveCompletion.openT`: the open `C = {T ≠ 0}` of `E`.
* `Stacks.Chow.ProjectiveCompletion.chart`: the chart `Proj Γ(V, Sym^*(𝒞)[T]) ⟶ E` over an affine
  open `V` of `X`.
* `Stacks.Chow.ProjectiveCompletion.chartT`: the degree-one element `T` of `Γ(V, Sym^*(𝒞)[T])`.

## Main results

* `Stacks.Chow.ProjectiveCompletion.chart_preimage_openT`: on the chart over `V`, the open `C`
  is `D₊(T)`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞]

/-- The graded algebra `Sym^*(𝒞 ⊕ 𝒪_X) = Sym^*(𝒞)[T]` on `X`. -/
abbrev symAlg : Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra X :=
  schemeSheafGradedAlgebra (module 𝒞) (bundlePieces (module 𝒞))

/-- **The unit of the summand `𝒪_X`** of `𝒞 ⊕ 𝒪_X`, a global section. -/
def sectionT : Γ(module 𝒞, ⊤) :=
  Scheme.Modules.Hom.app (inr 𝒞) ⊤ (1 : Γ(X, ⊤))

/-- **The section `T` of `𝒪_E(1)`**, the image of the unit of the summand `𝒪_X` under the
tautological surjection. -/
def coordT : Γ(twist 𝒞, ⊤) :=
  SectionZeroScheme.bundleSectionOf (module 𝒞) (bundlePieces (module 𝒞)) (sectionT 𝒞)

/-- **The open `C = {T ≠ 0}` of the projective completion**: the complement of the zero scheme of
`T`. -/
def openT : (space 𝒞).Opens :=
  zeroSchemeComplement (space 𝒞) (twist 𝒞) (coordT 𝒞)

variable (V : X.Opens) (hV : IsAffineOpen V)

/-- **The chart of `E` over an affine open `V` of `X`**, from the projective spectrum of
`Γ(V, Sym^*(𝒞)[T])`. -/
def chart : AlgebraicGeometry.Proj ((symAlg 𝒞).grading V) ⟶ space 𝒞 :=
  (relativeProj (symAlg 𝒞)).chart V hV

/-- The chart of `E` over an affine open `V` of `X` is an open immersion. -/
instance isOpenImmersion_chart : IsOpenImmersion (chart 𝒞 V hV) :=
  Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart _ V hV

/-- The degree-one element `T` of `Γ(V, Sym^*(𝒞)[T])`. -/
def chartT : (symAlg 𝒞).grading V 1 :=
  ⟨DirectSum.of ((symAlg 𝒞).sectionPieces V) 1
      ((Scheme.Modules.symmetricAlgebraGen X (module 𝒞)).val.app (op V)
        ((module 𝒞).presheaf.map (homOfLE le_top).op (sectionT 𝒞))),
    (symAlg 𝒞).of_mem_grading V _⟩

/-- **On the chart over `V`, the open `C = {T ≠ 0}` is the standard open `D₊(T)`.** -/
theorem chart_preimage_openT :
    chart 𝒞 V hV ⁻¹ᵁ openT 𝒞 =
      AlgebraicGeometry.Proj.basicOpen ((symAlg 𝒞).grading V)
        ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V) := by
  have hadj := adjoin_grading_one_eq_top (module 𝒞) V (bundlePieces (module 𝒞)) hV
  have := algebraicGeometry_isInvertible_twistingSheaf ((symAlg 𝒞).grading V) hadj ((1 : ℕ) : ℤ)
  have hsupp := AlgebraicGeometry.ProjectiveSpectrum.Proj.support_zeroScheme_degreeSection_one
    ((symAlg 𝒞).grading V) hadj (chartT 𝒞 V)
  have hcomap : (Stacks.Divisors.zeroScheme (space 𝒞) (twist 𝒞) (coordT 𝒞)).comap
      (chart 𝒞 V hV) =
      Stacks.Divisors.zeroScheme (AlgebraicGeometry.Proj ((symAlg 𝒞).grading V))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule ((symAlg 𝒞).grading V)
          ((1 : ℕ) : ℤ))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection ((symAlg 𝒞).grading V) 1
          (chartT 𝒞 V)) :=
    SectionZeroScheme.comap_chart_zeroScheme_bundleSectionOf (module 𝒞)
      (bundlePieces (module 𝒞)) (sectionT 𝒞) V hV
  ext x
  have h1 : x ∈ chart 𝒞 V hV ⁻¹ᵁ openT 𝒞 ↔
      x ∉ ((Stacks.Divisors.zeroScheme _ (twist 𝒞) (coordT 𝒞)).comap (chart 𝒞 V hV)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact Iff.rfl
  rw [SetLike.mem_coe, h1, hcomap]
  show x ∉ (AlgebraicGeometry.zeroScheme _ _ _).support ↔ _
  rw [← SetLike.mem_coe, hsupp, Set.mem_compl_iff, not_not, SetLike.mem_coe]

end Stacks.Chow.ProjectiveCompletion
