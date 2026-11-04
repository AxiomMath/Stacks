module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesProjChartBridge
public import StacksFrontier.RingTheory.Blowup.IdealFactorization

/-!
# Homogeneous fractions on a Rees chart, read in the affine blowup algebra

Over an affine open `U` of the base, the standard chart of the blowup of `X` in a quasi-coherent
ideal `I` attached to a section `a ∈ I(U)` is the spectrum of the affine blowup algebra
`Γ(X, U)[I/a]`, by `AlgebraicGeometry.reesToAffineBlowupEquiv`. The elements of the source of
that identification are the homogeneous fractions `x / aⁿ` with `x` a degree-`n` section of the
local Rees algebra, and the elements of the target used by the factorization results of
`StacksFrontier/RingTheory/Blowup/IdealFactorization.lean` are the fractions
`affineBlowupAlgebra.fraction` of elements of `I(U)ⁿ`. This file matches the two.

The two results are independent. The first says that the identification carries a homogeneous
fraction to the fraction of its image in `Γ(X, U)`; the second computes that image for a
homogeneous section written on the `SheafGradedAlgebra` substrate, on which the results about
closed subschemes of a relative `Proj` are stated.

## Main results

* `Stacks.Blowup.reesToAffineBlowupEquiv_awayMk`: **the homogeneous fraction `x / aⁿ` of the
  local Rees algebra is the affine blowup algebra's fraction `reesToBase x / aⁿ`.**
* `Stacks.Blowup.reesToBase_reesChartGradedHom_of`: **the degree-`n` homogeneous section `y` of
  the Rees algebra on the `SheafGradedAlgebra` substrate, transported to the local Rees algebra
  and read in `Γ(X, U)`, is the ambient image `reesPieceAmbient` of `y`.**

## Implementation notes

`AlgebraicGeometry.reesToAffineBlowupEquiv` is `AlgebraicGeometry.reesToAffineBlowup`
corestricted along `RingEquiv.ofBijective`, and that map is in turn
`AlgebraicGeometry.reesToLocalization` corestricted to the blowup subalgebra, so both coercions
are definitional and the first result reduces, by `Subtype.ext`, to
`AlgebraicGeometry.reesToLocalization_mk` together with the identity
`x / aⁿ = (1 / a)ⁿ · x` in the localization. The latter is the only real content: the
localization writes the fraction with a denominator, while `affineBlowupAlgebra.fraction`
writes it multiplicatively as a power of `IsLocalization.Away.invSelf`.

The second result is a chain of four definitional unfoldings and two named lemmas. The
transported section is left where it is by the substrate comparison
(`…RelativeProjBridge.situationSectionRingEquiv_of`) and moved degreewise by the model
comparison (`Stacks.Blowup.ReesModel.sectionHom_of`); `AlgebraicGeometry.reesToBase_of` then
reads it through `AlgebraicGeometry.reesPieceEquiv`, and
`Stacks.Blowup.ReesModel.coe_reesPieceEquiv_compare` replaces that by the model's own
identification, which for `Stacks.Blowup.reesSituationModel` is
`Stacks.Blowup.reesPieceAffineEquiv`. Note that `AlgebraicGeometry.reesSituation` and
`Stacks.Blowup.reesSituation` are *different* terms — the first is built from an opaque choice
— so the passage between them is exactly what `Stacks.Blowup.reesSituationModel` provides and
cannot be done by `rfl`.

## Not done here

No Stacks tag is claimed. The identification of the standard chart with the affine blowup
algebra is Tag 0804, already claimed by
`AlgebraicGeometry.affineBlowupStandardOpenIso` and its two companions; these are computations
of that identification on particular elements, not labelled assertions of the source.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPresentation
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.Blowup

/-! ### The homogeneous fraction is the affine blowup algebra's fraction -/

/-- **The homogeneous fraction `x / aⁿ` is the affine blowup algebra's fraction.** Under the
identification `AlgebraicGeometry.reesToAffineBlowupEquiv` of the degree-zero homogeneous
localization away from the degree-one element of `a` with the affine blowup algebra
`Γ(X, U)[I/a]`, the fraction `x / aⁿ` of a degree-`n` homogeneous section `x` is the fraction
`affineBlowupAlgebra.fraction` of its image `AlgebraicGeometry.reesToBase I U x`, which lies in
`I(U)ⁿ`. -/
public theorem reesToAffineBlowupEquiv_awayMk {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : I.ideal U) (n : ℕ)
    (x : (AlgebraicGeometry.reesSituation I).sectionRing U.1)
    (hx : x ∈ (AlgebraicGeometry.reesSituation I).sectionRingGrading U.1 n) :
    AlgebraicGeometry.reesToAffineBlowupEquiv I U a
        (HomogeneousLocalization.Away.mk
          ((AlgebraicGeometry.reesSituation I).sectionRingGrading U.1)
          (AlgebraicGeometry.reesDegreeOne I U a).2 n x (by simpa using hx)) =
      _root_.affineBlowupAlgebra.fraction (S := Localization.Away (a : Γ(X, U.1)))
        (I.ideal U) (a : Γ(X, U.1)) n
        ⟨AlgebraicGeometry.reesToBase I U x,
          AlgebraicGeometry.reesToBase_mem_pow I U n x hx⟩ := by
  have hx' : x ∈ (AlgebraicGeometry.reesSituation I).sectionRingGrading U.1 (n • 1) := by
    simpa using hx
  have hpow : IsLocalization.Away.invSelf (a : Γ(X, U.1)) ^ n =
      IsLocalization.mk' (Localization.Away (a : Γ(X, U.1))) 1
        (⟨(a : Γ(X, U.1)) ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (a : Γ(X, U.1))) := by
    rw [IsLocalization.Away.invSelf, ← IsLocalization.mk'_pow]
    (congr 1; simp)
  refine Subtype.ext ?_
  rw [_root_.affineBlowupAlgebra.fraction_coe]
  show AlgebraicGeometry.reesToLocalization I U a
      (HomogeneousLocalization.Away.mk
        ((AlgebraicGeometry.reesSituation I).sectionRingGrading U.1)
        (AlgebraicGeometry.reesDegreeOne I U a).2 n x hx') = _
  rw [AlgebraicGeometry.reesToLocalization_mk I U a n x hx', Localization.mk_eq_mk', hpow,
    mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one]

/-! ### The degree-`n` section of the Rees algebra, read in the sections of the base -/

/-- **A degree-`n` homogeneous section of the Rees algebra on the `SheafGradedAlgebra`
substrate, transported to the local Rees algebra and read in `Γ(X, U)`, is its ambient image.**
The graded comparison `Stacks.Blowup.reesChartGradedHom` leaves the section in degree `n` and
moves it through the degreewise identification of the two Rees algebras with `I(U)ⁿ`, and
`AlgebraicGeometry.reesToBase` reads that identification in `Γ(X, U)`; the composite is
`Stacks.Blowup.reesPieceAmbient`. -/
public theorem reesToBase_reesChartGradedHom_of {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ)
    (y : Γ((reesSheafGradedAlgebra I).piece (n : ℤ), U.1)) :
    AlgebraicGeometry.reesToBase I U
        (reesChartGradedHom I ⟨U.1, U.2⟩
          (DirectSum.of ((reesSheafGradedAlgebra I).sectionPieces U.1) n y)) =
      reesPieceAmbient I (n : ℤ) U.1 y := by
  have h1 : reesChartHom I ⟨U.1, U.2⟩
      (DirectSum.of ((reesSheafGradedAlgebra I).sectionPieces U.1) n y) =
      DirectSum.of ((reesSituation I).sectionPieces U.1) n y :=
    situationSectionRingEquiv_of (reesGradedAlgebra I) (reesIsCommutative I)
      (reesVanishesInNegativeDegrees I) (reesIsQuasicoherent I) U.1 n y
  have h2 : (reesSituationModel I).sectionHom U
      (DirectSum.of ((reesSituation I).sectionPieces U.1) n y) =
      DirectSum.of ((AlgebraicGeometry.reesSituation I).sectionPieces U.1) n
        ((reesSituationModel I).compare U n y) :=
    (reesSituationModel I).sectionHom_of U n y
  have h3 : AlgebraicGeometry.reesToBase I U
      (DirectSum.of ((AlgebraicGeometry.reesSituation I).sectionPieces U.1) n
        ((reesSituationModel I).compare U n y)) =
      ((AlgebraicGeometry.reesPieceEquiv I U n ((reesSituationModel I).compare U n y) :
        Γ(X, U.1))) :=
    AlgebraicGeometry.reesToBase_of I U n ((reesSituationModel I).compare U n y)
  have h4 := (reesSituationModel I).coe_reesPieceEquiv_compare U n y
  have h5 := reesPieceAffineEquiv_coe I (n : ℤ) (Int.natCast_nonneg n) U y
  show AlgebraicGeometry.reesToBase I U
    ((reesSituationModel I).sectionHom U
      (reesChartHom I ⟨U.1, U.2⟩
        (DirectSum.of ((reesSheafGradedAlgebra I).sectionPieces U.1) n y))) = _
  refine Eq.trans (congrArg (fun z => AlgebraicGeometry.reesToBase I U
    ((reesSituationModel I).sectionHom U z)) h1) ?_
  refine Eq.trans (congrArg (AlgebraicGeometry.reesToBase I U) h2) ?_
  exact h3.trans (h4.trans h5)

end Stacks.Blowup

end
