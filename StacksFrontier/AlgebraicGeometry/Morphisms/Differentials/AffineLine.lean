module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackAlgebraIso
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.SpecComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth

/-!
# The differentials of the affine line

The sheaf of relative differentials of the affine line `𝔸¹_S ⟶ S` over any scheme `S` is free of
rank one, on the differential of the coordinate. Over the integers this is the computation of
`Ω_{ℤ[x]/ℤ}`, and the affine line over `S` is the base change of the affine line over the
integers, with which the formation of differentials commutes.

## Main results

* `AlgebraicGeometry.AffineSpace.kaehlerLineIso`: `Ω_{ℤ[x]/ℤ} ≅ ℤ[x]`.
* `AlgebraicGeometry.AffineSpace.isPullback_line`: `𝔸¹_S` is the base change of `𝔸¹_ℤ`.
* `AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension_line`: `𝔸¹_S ⟶ S` is smooth of
  relative dimension one.
* `AlgebraicGeometry.AffineSpace.relativeDifferentialsIsoUnit`: `Ω_{𝔸¹_S/S} ≅ 𝒪_{𝔸¹_S}`.

## Implementation notes

The affine line is Mathlib's `𝔸(PUnit; S)`, affine space on a one-element index type in the
universe of `S`. The algebra structure that `CommRingCat.KaehlerDifferential` reads off the
coefficient inclusion and Mathlib's algebra structure on polynomials agree only propositionally,
so the two modules of differentials are compared by `kaehlerIsoOfAlgebraEq`.

## References

* [Stacks Project, Tag 00RX](https://stacks.math.columbia.edu/tag/00RX)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01V0](https://stacks.math.columbia.edu/tag/01V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AffineSpace

/-- The coefficient inclusion `ℤ → ℤ[x]`, as a morphism of commutative rings. -/
abbrev lineCoeff : CommRingCat.of (ULift.{u} ℤ) ⟶
    CommRingCat.of (MvPolynomial PUnit.{u+1} (ULift.{u} ℤ)) :=
  CommRingCat.ofHom MvPolynomial.C


/-- Kähler differentials for two equal algebra structures are isomorphic. -/
def kaehlerIsoOfAlgebraEq {A B : Type u} [CommRing A] [CommRing B]
    (i₁ i₂ : Algebra A B) (h : i₁ = i₂) :
    (letI := i₁; ModuleCat.of B Ω[B⁄A]) ≅ (letI := i₂; ModuleCat.of B Ω[B⁄A]) := by
  subst h
  exact Iso.refl _

/-- **`Ω_{ℤ[x]/ℤ} ≅ ℤ[x]`**, free on `dx` ([Stacks, Tag 00RX]). -/
def kaehlerLineIso :
    CommRingCat.KaehlerDifferential (lineCoeff.{u}) ≅
      ModuleCat.of (MvPolynomial PUnit.{u+1} (ULift.{u} ℤ))
        (MvPolynomial PUnit.{u+1} (ULift.{u} ℤ)) :=
  kaehlerIsoOfAlgebraEq (lineCoeff.{u}.hom.toAlgebra) (inferInstance :
      Algebra (ULift.{u} ℤ) (MvPolynomial PUnit.{u+1} (ULift.{u} ℤ)))
      (Algebra.algebra_ext _ _ fun _ => rfl) ≪≫
  LinearEquiv.toModuleIso
    ((KaehlerDifferential.mvPolynomialBasis (ULift.{u} ℤ) PUnit.{u+1}).equivFun.trans
      (LinearEquiv.funUnique PUnit.{u+1} _ _))

/-- **`Ω_{𝔸¹_ℤ/ℤ} ≅ 𝒪_{𝔸¹_ℤ}`**: the sheaf of differentials of `Spec ℤ[x] ⟶ Spec ℤ` is the sheaf
associated to `Ω_{ℤ[x]/ℤ}` ([Stacks, Tag 01UT]), which is free on `dx`. -/
def relativeDifferentialsLineIso :
    Scheme.Hom.relativeDifferentials (Spec.map lineCoeff.{u}) ≅
      SheafOfModules.unit
        (Spec (CommRingCat.of (MvPolynomial PUnit.{u+1} (ULift.{u} ℤ)))).ringCatSheaf :=
  (Stacks.AlgebraicGeometry.AffineDifferentialsIso.tildeKaehlerIso lineCoeff).symm ≪≫
    (tilde.functor _).mapIso kaehlerLineIso ≪≫ tildeSelf

/-- The affine line over `S` is the base change of `𝔸¹_ℤ ⟶ Spec ℤ` along `S ⟶ Spec ℤ`. -/
theorem isPullback_line (S : Scheme.{u}) :
    IsPullback (AffineSpace.toSpecMvPoly PUnit.{u+1} S) (𝔸(PUnit.{u+1}; S) ↘ S)
      (Spec.map lineCoeff.{u}) (specULiftZIsTerminal.from S) := by
  have e : ⊤_ Scheme.{u} ≅ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal
  refine (IsPullback.of_hasPullback (terminal.from S)
    (terminal.from (Spec (CommRingCat.of (MvPolynomial PUnit.{u+1} (ULift.{u} ℤ)))))).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_ ?_
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · exact specULiftZIsTerminal.hom_ext _ _
  · exact specULiftZIsTerminal.hom_ext _ _

/-- **`𝔸¹_S ⟶ S` is smooth of relative dimension one**, as the base change of
`Spec ℤ[x] ⟶ Spec ℤ`. -/
instance smoothOfRelativeDimension_line (S : Scheme.{u}) :
    SmoothOfRelativeDimension 1 (𝔸(PUnit.{u+1}; S) ↘ S) := by
  refine (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
    (isPullback_line S) ?_
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  change (algebraMap (ULift.{u} ℤ)
    (MvPolynomial PUnit.{u+1} (ULift.{u} ℤ))).IsStandardSmoothOfRelativeDimension 1
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    (MvPolynomial.renameEquiv (ULift.{u} ℤ) (Equiv.equivPUnit.{1, u+1} (Fin 1)))

/-- **`Ω_{𝔸¹_S/S} ≅ 𝒪_{𝔸¹_S}`**, free on `dx`: the formation of differentials commutes with
the base change `𝔸¹_S = S ×_{Spec ℤ} 𝔸¹_ℤ` ([Stacks, Tag 01V0]). -/
def relativeDifferentialsIsoUnit (S : Scheme.{u}) :
    Scheme.Hom.relativeDifferentials (𝔸(PUnit.{u+1}; S) ↘ S) ≅
      SheafOfModules.unit 𝔸(PUnit.{u+1}; S).ringCatSheaf :=
  haveI := Scheme.Hom.isIso_relativeDifferentialsMap_of_isPullback _ _ _ _ (isPullback_line S)
  (asIso (Scheme.Hom.relativeDifferentialsMap _ _ _ _ (isPullback_line S).w)).symm ≪≫
    (Scheme.Modules.pullback _).mapIso relativeDifferentialsLineIso ≪≫
    (Stacks.PullbackAlgebra.pullbackUnitIso
        (AffineSpace.toSpecMvPoly PUnit.{u+1} S).toLRSHom.toShHom :
      (Scheme.Modules.pullback (AffineSpace.toSpecMvPoly PUnit.{u+1} S)).obj
          (SheafOfModules.unit (Spec (CommRingCat.of
            (MvPolynomial PUnit.{u+1} (ULift.{u} ℤ)))).ringCatSheaf) ≅
        SheafOfModules.unit 𝔸(PUnit.{u+1}; S).ringCatSheaf)

end AlgebraicGeometry.AffineSpace

end
