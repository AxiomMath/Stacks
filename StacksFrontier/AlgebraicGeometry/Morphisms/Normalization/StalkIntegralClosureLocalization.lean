module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Stalk

/-!
# Integral closure in the total ring of fractions of a reduction, under localization

Let `R` be a commutative ring and `S = FractionRing (R ⧸ nilradical R)` the total ring of
fractions of its reduction.  If `C` is a localization of `R` at a submonoid `M` and `S` is
artinian, then the integral closure of `C` in the total ring of fractions of the reduction of
`C` is the localization at the image of `M` of the integral closure of `R` in `S`.

Also recorded is the transitivity of integral closures: over a base over which the intermediate
ring is integral, the integral closure of the base agrees with the integral closure of the
intermediate ring.

## Main results

* `integralClosure_eq_restrictScalars_of_isIntegral`: for a tower `R → A → B` with `A` integral
  over `R`, the integral closure of `R` in `B` is the integral closure of `A` in `B`, viewed as
  an `R`-subalgebra.
* `nonempty_algEquiv_integralClosure_fractionRing_reduction`: the integral closure of a
  localization `C` of `R`, inside the total ring of fractions of the reduction of `C`, is a
  localization of the integral closure of `R` inside the total ring of fractions of the
  reduction of `R`.

## Implementation notes

The localization statement is an existence statement, `Nonempty (_ ≃ₐ[C] _)`. The `C`-algebra
structure on `Localization (Algebra.algebraMapSubmonoid _ M)` is the comparison map
`localizationAlgebra` of a localization of an algebra, and so has to be supplied in the statement;
every other algebra structure appearing is the ambient instance.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

universe u

/-- **Transitivity of integral closures.** In a tower `R → A → B` with `A` integral over `R`,
an element of `B` is integral over `R` precisely when it is integral over `A`; that is, the
integral closure of `R` in `B` is the integral closure of `A` in `B`, regarded as an
`R`-subalgebra. -/
public theorem integralClosure_eq_restrictScalars_of_isIntegral
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.IsIntegral R A] :
    integralClosure R B = (integralClosure A B).restrictScalars R := by
  ext x
  exact ⟨IsIntegral.tower_top, isIntegral_trans (A := A) x⟩

/-- **Taking the integral closure in the total ring of fractions of the reduction commutes with
localization.** Let `C` be the localization of a ring `R` at a submonoid `M`, and suppose the
total ring of fractions `S` of the reduction of `R` is artinian. Then the integral closure of
`C` in the total ring of fractions of the reduction of `C` is the localization, at the image of
`M`, of the integral closure of `R` in `S`. -/
public theorem nonempty_algEquiv_integralClosure_fractionRing_reduction
    (R C : Type*) [CommRing R] [CommRing C] [Algebra R C] (M : Submonoid R)
    [IsLocalization M C]
    [IsArtinianRing (FractionRing (R ⧸ nilradical R))] :
    letI : Algebra C (Localization (Algebra.algebraMapSubmonoid
        ↥(integralClosure R (FractionRing (R ⧸ nilradical R))) M)) :=
      localizationAlgebra M ↥(integralClosure R (FractionRing (R ⧸ nilradical R)))
    Nonempty (↥(integralClosure C (FractionRing (C ⧸ nilradical C))) ≃ₐ[C]
      Localization (Algebra.algebraMapSubmonoid
        ↥(integralClosure R (FractionRing (R ⧸ nilradical R))) M)) := by
  let S := FractionRing (R ⧸ nilradical R)
  let T := ↥(integralClosure R S)
  let L := Localization (Algebra.algebraMapSubmonoid S M)
  let C' := Localization (Algebra.algebraMapSubmonoid T M)
  let : Algebra C L := localizationAlgebra M S
  have : IsScalarTower R C L := isScalarTower_localizationAlgebra M S
  let : Algebra C C' := localizationAlgebra M T
  have : IsScalarTower R C C' := isScalarTower_localizationAlgebra M T
  let eC : C' ≃ₐ[C] integralClosure C L :=
    AlgebraicGeometry.Scheme.integralClosureLocalizationEquiv M
      (AlgEquiv.refl (R := R) (A₁ := T))
  let eL := AlgebraicGeometry.Scheme.fractionRingReductionLocalizationEquiv R C M
  let eL' : L ≃ₐ[C] FractionRing (C ⧸ nilradical C) :=
    AlgEquiv.ofRingEquiv (f := eL.toRingEquiv) eL.commutes
  exact ⟨(eC.trans eL'.mapIntegralClosure).symm⟩

end
