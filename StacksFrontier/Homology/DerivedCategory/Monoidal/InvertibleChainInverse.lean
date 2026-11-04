module

public import StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
public import StacksFrontier.Homology.TorAmplitude.Comparison

/-!
# A bounded complex of projectives with a tensor inverse up to homotopy is invertible

Let `R` be a commutative ring and let `P`, `P'` be bounded above complexes of projective
`R`-modules such that the total tensor complex `Tot(P ⊗_R P')` is homotopy equivalent to `R`
placed in degree `0`. Then `P` is an invertible object of `D(R)`, for the monoidal structure of
Stacks 0FNQ.

## References

* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace DerivedCategory.Invertible

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- **A bounded above complex of projectives with a tensor inverse up to homotopy is invertible
in `D(R)`.** -/
public theorem isInvertible_Q_of_homotopyEquiv (P P' : CochainComplex (ModuleCat.{u} R) ℤ)
    (a a' : ℤ) [P.IsStrictlyLE a] [P'.IsStrictlyLE a']
    (hP : ∀ i, Projective (P.X i)) (hP' : ∀ i, Projective (P'.X i))
    (h : HomotopyEquiv (P ⊗ P') (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) :
    letI := (derivedCategory_symmetricMonoidalCategory R).choose
    MonoidalCategory.IsInvertible (DerivedCategory.Q.obj P) := by
  let derivedMonoidal := (derivedCategory_symmetricMonoidalCategory R).choose
  let := derivedMonoidal
  let := (derivedCategory_symmetricMonoidalCategory R).choose_spec.choose
  have hPflat : P.KFlat := StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective P a hP
  have hP'flat : P'.KFlat := StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective P' a' hP'
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R
  let t := (derivedCategory_symmetricMonoidalCategory R).choose_spec.choose_spec.choose
  let eh : DerivedCategory.Q.obj (P ⊗ P') ≅
      DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) :=
    ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app _).symm ≪≫
      DerivedCategory.Qh.mapIso (HomotopyCategory.isoOfHomotopyEquiv h) ≪≫
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).app _
  let e : DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj P' ≅
      𝟙_ (DerivedCategory (ModuleCat.{u} R)) :=
    ((t.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj P')) ≪≫
      T.comparison P P' hPflat hP'flat ≪≫ eh ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app
        (ModuleCat.of R R)).symm ≪≫
      (CochainComplex.DerivedTensor.monoidalUnitIsoSingleFunctorObj R).symm
  exact ⟨⟨DerivedCategory.Q.obj P', e, (β_ (DerivedCategory.Q.obj P') _) ≪≫ e⟩⟩

end DerivedCategory.Invertible

end
