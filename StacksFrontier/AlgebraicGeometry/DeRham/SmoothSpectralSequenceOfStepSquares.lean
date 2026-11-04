module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageIdentification
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceStepSquares
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceVanishing

/-!
# The de Rham spectral sequence of a smooth morphism, granted the squares of Section 0FMK

For `f : X ⟶ Y` smooth and `g : Y ⟶ S`, the first page `H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})`
vanishes for `p < 0`, and the higher direct images of the steps of the filtration of `Ω^•_{X/S}`
vanish in large filtration degree. Granted the commutativity of the two squares of Section 0FMK on
each step of the filtration, the higher direct images of the graded pieces are the first page, and
there is a bounded spectral sequence from the first page converging to `R^{p+q}f_*Ω^•_{X/S}`.

## Main definitions

* `Stacks.DeRhamSmooth.StepSquares`: the commutativity of the two squares of Section 0FMK at
  every step of the filtration.

## Main results

* `Stacks.DeRhamSmooth.isZero_deRhamFirstPage_of_neg`: the first page vanishes for `p < 0`.
* `Stacks.DeRhamSmooth.exists_higherDirectImage_deRhamSmoothFiltration_isZero`: in each degree,
  the higher direct images of the steps of the filtration vanish for large `p`.
* `Stacks.DeRhamSmooth.higherDirectImageGradedPieceIsoFirstPage`: granted `StepSquares`, the
  higher direct images of the graded pieces are the first page.
* `Stacks.DeRhamSmooth.exists_boundedDeRhamSpectralSequence_of_stepSquares`: [Stacks, Tag 0FMM],
  granted `StepSquares`.

## References

* [Stacks Project, Tag 0FMM](https://stacks.math.columbia.edu/tag/0FMM)
* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.FilteredComplex (higherDirectImage)

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf StrictlyPerfect.structureSheafOfRings
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- The first page of the de Rham spectral sequence vanishes for `p < 0`:
`H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y}) = 0`. -/
theorem isZero_deRhamFirstPage_of_neg (p q : ℤ) (hp : p < 0) :
    IsZero (deRhamFirstPage f g p q) := by
  let T := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.toRingedSpace.sheaf
  let B := DerivedCategory.Plus.ι.obj (Stacks.DeRhamDirectImage.derivedDeRhamDirectImage f)
  let _ : (T.tensor.flip.obj B).CommShift ℤ := T.commShift_left B
  have _ : (T.tensor.flip.obj B).IsTriangulated := T.exact_left B
  exact (pushforward (toInverseImageBase g)).map_isZero
    ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace)
        q).map_isZero
      ((T.tensor.flip.obj B).map_isZero
        ((DerivedCategory.singleFunctor (StrictlyPerfect.OXMod.{u, u, u} Y.toRingedSpace)
          0).map_isZero (isZero_relativeDifferentialForms_of_neg g p hp))))

/-- In each degree `n` the higher direct images of the steps `F^pΩ^•_{X/S}` of the filtration
vanish for all sufficiently large `p`. -/
theorem exists_higherDirectImage_deRhamSmoothFiltration_isZero (n : ℤ) :
    ∃ p₀ : ℤ, ∀ p : ℤ, p₀ ≤ p →
      IsZero (higherDirectImage (derivedRelativePushforward f g)
        ((deRhamSmoothFiltration f g).filtration.obj (op p)) n) :=
  ⟨max 1 (n + 1), fun p hp =>
    isZero_higherDirectImage_deRhamSmoothFiltration f g p n (by omega) (by omega)⟩

/-- The commutativity, at every cut `k`, of the squares comparing the differential of the `k`-th
graded piece of `Stacks.DeRhamSmooth.deRhamSmoothFiltration f g` with that of
`Stacks.DeRhamSmooth.gradedTargetComplex f g k`: the square in the degree of the cut and the
squares above it. -/
def StepSquares [Smooth f] : Prop :=
  ∀ k : ℕ,
    ((filtrationXIsoCutWedgeSource f g k).hom ≫
        (pushforward (toInverseImageBase (f ≫ g))).map
            (cutWedgeSourceIsoPullbackTensor f g k).hom ≫
          (gradedSourceMixedTensorCoefficientIso f g k
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ))).inv ≫
            ((-1 : ℤ) ^ k • (coefficientRestriction f g).map
                ((pulledBackTargetFormsTensor f g k).map
                  ((deRhamCochainXIso f 0).inv ≫
                    (deRhamCochainComplex f).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) ≫
                      (deRhamCochainXIso f (0 + 1)).hom))) ≫
              (gradedTargetXIso f g k (0 + 1) (k + 1 + 0) (by omega)).inv =
      ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d
          ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + 0 : ℕ) : ℤ) ≫
          (gradedPieceXIsoGradedTargetX f g k 0).hom) ∧
    ∀ j : ℕ, (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + j : ℕ) : ℤ) ≫
        ((gradedPieceXIsoGradedTargetX f g k j).hom ≫
          (gradedTargetComplex f g k).d ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ)) =
      ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d
          ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
          (gradedPieceXIsoGradedTargetX f g k (j + 1)).hom

/-- Granted `Stacks.DeRhamSmooth.StepSquares f g`, the higher direct image in degree `p + q` of
the `p`-th graded piece of the filtration of `Ω^•_{X/S}` is isomorphic to the first-page term
`H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})`. -/
theorem higherDirectImageGradedPieceIsoFirstPage [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    (hsq : StepSquares f g) (p q : ℤ) :
    Nonempty (higherDirectImage (derivedRelativePushforward f g)
      (gradedPiece (inverseImageBase (f ≫ g)) p (deRhamSmoothFiltration f g)) (p + q) ≅
        deRhamFirstPage f g p q) := by
  rcases lt_or_ge p 0 with hp | hp
  · exact ⟨(isZero_higherDirectImage_gradedPiece_of_neg f g p (p + q) hp).iso
      (isZero_deRhamFirstPage_of_neg f g p q hp)⟩
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact ⟨(DerivedCategory.homologyFunctor _ ((k : ℤ) + q)).mapIso
        ((derivedRelativePushforward f g).mapIso (DerivedCategory.Q.mapIso
          (gradedPieceIsoGradedTargetComplexOfStepSquares f g k (hsq k).1 (hsq k).2))) ≪≫
      higherDirectImageGradedTargetIso f g k q⟩

/-- [Stacks, Tag 0FMM], granted `Stacks.DeRhamSmooth.StepSquares f g`: for `f : X ⟶ Y`
quasi-compact, quasi-separated and smooth and `g : Y ⟶ S` there is a bounded spectral sequence
with `E_1^{p,q} = H^q(Ω^p_{Y/S} ⊗^𝐋_{𝒪_Y} Rf_*Ω^•_{X/Y})` converging to
`R^{p+q}f_*Ω^•_{X/S}`. -/
theorem exists_boundedDeRhamSpectralSequence_of_stepSquares
    [QuasiCompact f] [QuasiSeparated f] [Smooth f] (hsq : StepSquares f g) :
    ∃ E : CohomologicalSpectralSequence
        (SheafOfModules.{u} (structureSheafRing (inverseImageBase g))) 1,
      _root_.IsBounded E ∧
      (∀ p q : ℤ, Nonempty ((E.page 1).X (p, q) ≅ deRhamFirstPage f g p q)) ∧
      SpectralSequence.AbutsTo E (fun n => deRhamHigherDirectImage f g n) :=
  exists_boundedDeRhamSpectralSequence_of_pullback f g
    (exists_higherDirectImage_deRhamSmoothFiltration_isZero f g)
    (higherDirectImageGradedPieceIsoFirstPage f g hsq)

end Stacks.DeRhamSmooth

end
