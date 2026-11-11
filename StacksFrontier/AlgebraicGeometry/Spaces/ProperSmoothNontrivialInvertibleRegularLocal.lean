module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmoothNontrivialInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatLocusAdicThickenings

/-!
# A nontrivial invertible module on a proper smooth family over `Spec R`, `R` regular local

The form of
`AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_not_isTrivial_of_isProper_of_closedFibre`
over the big fppf site of `Spec R` itself, for a regular local ring `R`: the base is the terminal
object `Spec R`, its closed point is the closed point of `R`, and the closed fibre is the base
change along the first adic thickening `Spec(R / 𝔪) ⟶ Spec R`.

## Main definitions

* `AlgebraicGeometry.Space.adicThickeningZeroResidueFieldIso`: `Spec(R / 𝔪)` is the spectrum of the
  residue field of `Spec R` at the closed point, over `Spec R`.

## Main results

* `AlgebraicGeometry.Space.exists_isEffectiveCartierDivisor_not_isTrivial_of_isRegularRing`.

## References

* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (R : Type u) [CommRing R] [IsLocalRing R]
  (hA : B.Contains (Spec (.of R)))

/-- The quotient `R / 𝔪 ^ (0 + 1)` of a local ring is its residue field `𝔪.ResidueField`. -/
def quotientMaximalIdealPowOneEquivResidueField :
    R ⧸ maximalIdeal R ^ (0 + 1) ≃+* (maximalIdeal R).ResidueField :=
  (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).trans
    (RingEquiv.ofBijective (algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField)
      (maximalIdeal R).bijective_algebraMap_quotient_residueField)

/-- `quotientMaximalIdealPowOneEquivResidueField` sends the class of `r` to the image of `r`. -/
theorem quotientMaximalIdealPowOneEquivResidueField_mk (r : R) :
    quotientMaximalIdealPowOneEquivResidueField R (Ideal.Quotient.mk _ r) =
      algebraMap R (maximalIdeal R).ResidueField r := by
  change algebraMap (R ⧸ maximalIdeal R) (maximalIdeal R).ResidueField
      (Ideal.quotEquivOfEq (show maximalIdeal R ^ (0 + 1) = maximalIdeal R by
        rw [zero_add, pow_one]) (Ideal.Quotient.mk _ r)) = _
  rw [Ideal.quotEquivOfEq_mk]
  exact (IsScalarTower.algebraMap_apply R (R ⧸ maximalIdeal R) _ r).symm

/-- **The first adic thickening of `Spec R` is the spectrum of the residue field at the closed
point**, over `Spec R`. -/
def adicThickeningZeroResidueFieldIso :
    (BigFppfOver.toScheme B (Spec (.of R)) hA).obj
        (adicThickeningObject R (maximalIdeal R) B hA (contains_adicThickening _ _ B hA) 0) ≅
      Spec ((Spec (.of R)).residueField (IsLocalRing.closedPoint R)) :=
  Scheme.Spec.mapIso (Scheme.Spec.residueFieldIso (.of R) (IsLocalRing.closedPoint R) ≪≫
    (quotientMaximalIdealPowOneEquivResidueField R).symm.toCommRingCatIso).op

/-- The identification `adicThickeningZeroResidueFieldIso` lies over `Spec R`. -/
theorem adicThickeningZeroResidueFieldIso_hom_comp_fromSpecResidueField :
    (adicThickeningZeroResidueFieldIso B R hA).hom ≫
        (Spec (.of R)).fromSpecResidueField (IsLocalRing.closedPoint R) =
      (BigFppfOver.toScheme B (Spec (.of R)) hA).map
        (adicThickeningMap R (maximalIdeal R) B hA (contains_adicThickening _ _ B hA) 0) := by
  have hfrom := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R)
    (IsLocalRing.closedPoint R)
  refine (congrArg (fun g => (adicThickeningZeroResidueFieldIso B R hA).hom ≫ g)
    hfrom.symm).trans ?_
  change Spec.map ((Scheme.Spec.residueFieldIso (.of R) (IsLocalRing.closedPoint R)).hom ≫
      (quotientMaximalIdealPowOneEquivResidueField R).symm.toCommRingCatIso.hom) ≫
      Spec.map (Scheme.Spec.residueFieldIso (.of R) (IsLocalRing.closedPoint R)).inv ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (IsLocalRing.closedPoint R).asIdeal.ResidueField)) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  apply (quotientMaximalIdealPowOneEquivResidueField R).injective
  change (quotientMaximalIdealPowOneEquivResidueField R)
      ((quotientMaximalIdealPowOneEquivResidueField R).symm
        ((Scheme.Spec.residueFieldIso (.of R) (IsLocalRing.closedPoint R)).hom
          ((Scheme.Spec.residueFieldIso (.of R) (IsLocalRing.closedPoint R)).inv
            (algebraMap R (IsLocalRing.closedPoint R).asIdeal.ResidueField r)))) = _
  refine ((quotientMaximalIdealPowOneEquivResidueField R).apply_symm_apply _).trans ?_
  refine (Iso.inv_hom_id_apply
    (Scheme.Spec.residueFieldIso (.of R) (IsLocalRing.closedPoint R)) _).trans ?_
  exact (quotientMaximalIdealPowOneEquivResidueField_mk R r).symm

/-- **A nontrivial invertible module on a proper smooth family over a regular local ring.**
Let `R` be a Noetherian regular local ring and `f : Y ⟶ Spec R` a flat, proper morphism of finite
presentation of algebraic spaces over `Spec R`, with `|Y|` nonempty, whose closed fibre
`Y ×_{Spec R} Spec(R / 𝔪) ⟶ Spec(R / 𝔪)` is smooth of relative dimension `n ≠ 0` on every étale
chart. Then `Y` carries an effective Cartier divisor `D` with `𝒪_Y(D)` not trivial. -/
theorem exists_isEffectiveCartierDivisor_not_isTrivial_of_isRegularRing [IsNoetherianRing R]
    [IsRegularRing R] (Y : AlgebraicSpaces B (Spec (.of R)) hA)
    (f : Y.1 ⟶ yoneda.obj (baseObject R B hA))
    (hfp : IsFinitePresentation B (Spec (.of R)) hA f) (hflat : IsFlat B (Spec (.of R)) hA f)
    (hprop : IsProper B (Spec (.of R)) hA f) (n : ℕ) (hn : n ≠ 0)
    (hfib : HoldsOnEveryEtaleChart B (Spec (.of R)) hA (@SmoothOfRelativeDimension n)
      (pullback.snd f (yoneda.map
        (adicThickeningMap R (maximalIdeal R) B hA (contains_adicThickening _ _ B hA) 0))))
    (hne : Nonempty (points B (Spec (.of R)) hA Y.1)) :
    ∃ (D : ClosedSubspaces B (Spec (.of R)) hA Y.1)
      (hD : IsEffectiveCartierDivisor B (Spec (.of R)) hA Y D),
      ¬ AlgebraicGeometry.SheafOfModules.IsTrivial (structureCommRings B (Spec (.of R)) hA Y)
        (structureRingSheaf B (Spec (.of R)) hA Y).property
        (associatedInvertibleSheaf B (Spec (.of R)) hA Y D hD) := by
  let eΓ : R ≃+* Γ(Spec (.of R), ⊤) :=
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  have : IsAffine ((BigFppfOver.toScheme B (Spec (.of R)) hA).obj (baseObject R B hA)) :=
    inferInstanceAs (IsAffine (Spec (.of R)))
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B (Spec (.of R)) hA).obj
      (baseObject R B hA), ⊤) := isNoetherianRing_of_ringEquiv R eΓ
  have : IsRegularRing Γ((BigFppfOver.toScheme B (Spec (.of R)) hA).obj
      (baseObject R B hA), ⊤) := IsRegularRing.of_ringEquiv eΓ
  exact exists_isEffectiveCartierDivisor_not_isTrivial_of_isProper_of_closedFibre B
    (Spec (.of R)) hA Y (baseObject R B hA)
    (fun _ => ⟨⟨⊤, isAffineOpen_top _⟩, trivial, inferInstance⟩) f hfp hflat hprop
    (IsLocalRing.closedPoint R) (fun s => IsLocalRing.specializes_closedPoint s)
    (adicThickeningObject R (maximalIdeal R) B hA (contains_adicThickening _ _ B hA) 0)
    (adicThickeningMap R (maximalIdeal R) B hA (contains_adicThickening _ _ B hA) 0)
    (adicThickeningZeroResidueFieldIso B R hA)
    (adicThickeningZeroResidueFieldIso_hom_comp_fromSpecResidueField B R hA) n hn hfib hne

end AlgebraicGeometry.Space

end
