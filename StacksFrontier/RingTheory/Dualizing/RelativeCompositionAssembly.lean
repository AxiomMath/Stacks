module

public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionDiagonalSection
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionSurjectiveDescent
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionTensorFactor
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionUnitDescent
public import StacksFrontier.RingTheory.Dualizing.RelativeCompositionUnitSurjective
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalSection

/-!
# The isomorphism (★) of [stacks 0E2H] in `D(B ⊗[A] B)`

Write `C = B ⊗[R] B`, `C' = B ⊗[A] B`, `i : C → C'` for `Dualizing.diagonalQuotient`,
`W = K_{B/A} ⊗ᴸ_B C` and `X = (K_{A/R} ⊗ᴸ_A B) ⊗ᴸ_B C`.  The isomorphism

  (★)  `RHom_C(C', K ⊗ᴸ_B C) ≅ K_{B/A} ⊗ᴸ_B C'`,   `K = K_{A/R} ⊗ᴸ_A K_{B/A}`,

is assembled here from an isomorphism of `D(C)` between the restrictions of its two sides, by
`Dualizing.nonempty_iso_of_restrictScalars_iso_of_epi_unit`: the right-hand side is the derived
extension of scalars `i^* W`, and the unit `W ⟶ i_* i^* W` is surjective on cohomology.  The
restricted isomorphism is `Dualizing.restrictExtendScalarsIsoDerivedHomTensor`, whose inputs are
the untwisted half of (★) and invertibility of the single-ring tensor--Hom diagonal of `C` at
`(W, X, C')`.

## Main results

* `Dualizing.nonempty_diagonalQuotientDerivedHom_of_isIso_of_epi` -- (★) from the two inputs.
* `Dualizing.epi_homologyFunctor_map_unit_diagonalDerivedExtension` -- the unit input, discharged.
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom
open scoped TensorProduct

universe u

namespace Dualizing

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [Module.Flat R A] [Algebra.FinitePresentation R A]
  [Module.Flat A B] [Algebra.FinitePresentation A B]

omit [Algebra.FinitePresentation A B] in
/-- **(★) from the restricted diagonal and the surjectivity of the unit.**  Let `K_{A/R}` be a
relative dualizing complex for `R → A` and `K_{B/A}` any object of `D(B)`.  If the single-ring
tensor--Hom diagonal of `C = B ⊗[R] B` at `(K_{B/A} ⊗ᴸ_B C, (K_{A/R} ⊗ᴸ_A B) ⊗ᴸ_B C, C')` is
invertible and the unit of derived extension of scalars along `C → C'` at `K_{B/A} ⊗ᴸ_B C` is
surjective on cohomology, then (★) holds for `K = K_{A/R} ⊗ᴸ_A K_{B/A}`. -/
theorem nonempty_diagonalQuotientDerivedHom_of_isIso_of_epi
    (KA : DerivedCategory (ModuleCat.{u} A)) (KB : DerivedCategory (ModuleCat.{u} B))
    (hKA : IsRelativeDualizingComplex R A KA)
    (hdiag : letI : Module.Flat R B := Module.Flat.trans R A B
      IsIso (derivedTensorHomDiagonalOverRing.{u, u}
        ((diagonalDerivedExtension R B).obj KB)
        ((diagonalDerivedExtension R B).obj
          ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj KA))
        (ProjectionFormula.restrictedAlgebra.{u, u}
          (ModuleCat.restrictScalars.{u} (diagonalQuotient R A B).toRingHom).mapDerivedCategory)))
    (hη : letI : Module.Flat R B := Module.Flat.trans R A B
      ∀ n : ℤ, Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} (B ⊗[R] B)) n).map
        ((@derivedExtensionScalarsAdjunction.{u, u, u} (B ⊗[R] B) (B ⊗[A] B) _ _ _ _ _
          (totalDerivedExtensionScalars.{u, u, u} (diagonalQuotient R A B).toRingHom).functor
          (totalDerivedExtensionScalars.{u, u, u} (diagonalQuotient R A B).toRingHom).comparison
          (totalDerivedExtensionScalars.{u, u, u}
            (diagonalQuotient R A B).toRingHom).isLeftDerived).unit.app
          ((diagonalDerivedExtension R B).obj KB)))) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    Nonempty
      ((derivedHom.{u, u} (diagonalQuotient R A B).toRingHom).obj
          ((diagonalDerivedExtension R B).obj
            ((derivedTensorProductOver.{u, u} (algebraMap A B) KB).obj KA)) ≅
        (diagonalDerivedExtension A B).obj KB) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  let i := (diagonalQuotient R A B).toRingHom
  let E := totalDerivedExtensionScalars.{u, u, u} i
  let adjE : E.functor ⊣ (ModuleCat.restrictScalars.{u} i).mapDerivedCategory :=
    @derivedExtensionScalarsAdjunction.{u, u, u} (B ⊗[R] B) (B ⊗[A] B) _ _ _ _ _
      E.functor E.comparison E.isLeftDerived
  let adj := (restrictScalarsDerived_adj_derivedHom.{u, u, u} i).some
  let W := (diagonalDerivedExtension R B).obj KB
  let X := (diagonalDerivedExtension R B).obj
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A B)).functor.obj KA)
  obtain ⟨uh⟩ := nonempty_diagonalQuotientDerivedHom_untwisted R A B KA hKA
  let e : (derivedHom.{u, u, u} i).obj X ≅ derivedTensorUnit.{u} (B ⊗[A] B) :=
    uh ≪≫ (derivedTensorUnitIsoSingleSelf (B ⊗[A] B)).symm
  obtain ⟨eZ⟩ := nonempty_derivedExtension_tensor_iso_composite R A B KA KB
  let σ := restrictExtendScalarsIsoDerivedHomTensor i E adj adjE W X e hdiag ≪≫
    (ModuleCat.restrictScalars.{u} i).mapDerivedCategory.mapIso
      ((derivedHom.{u, u, u} i).mapIso eZ.symm)
  obtain ⟨φ⟩ := nonempty_iso_of_restrictScalars_iso_of_epi_unit i adjE W _ σ hη
  obtain ⟨c⟩ := diagonalDerivedExtensionCompIso R A B KB
  exact ⟨φ.symm ≪≫ c⟩

omit [Algebra.FinitePresentation R A] [Algebra.FinitePresentation A B] in
/-- **The unit hypothesis of `Dualizing.nonempty_diagonalQuotientDerivedHom_of_isIso_of_epi`,
discharged.**  The unit of derived extension of scalars along `C → C'` at `K_{B/A} ⊗ᴸ_B C` is
surjective on cohomology, for any object `K_{B/A}` of `D(B)`: the left coprojections `B → C` and
`B → C'` are flat and `C → C'` is surjective. -/
theorem epi_homologyFunctor_map_unit_diagonalDerivedExtension
    (KB : DerivedCategory (ModuleCat.{u} B)) (n : ℤ) :
    letI : Module.Flat R B := Module.Flat.trans R A B
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} (B ⊗[R] B)) n).map
        ((@derivedExtensionScalarsAdjunction.{u, u, u} (B ⊗[R] B) (B ⊗[A] B) _ _ _ _ _
          (totalDerivedExtensionScalars.{u, u, u} (diagonalQuotient R A B).toRingHom).functor
          (totalDerivedExtensionScalars.{u, u, u} (diagonalQuotient R A B).toRingHom).comparison
          (totalDerivedExtensionScalars.{u, u, u}
            (diagonalQuotient R A B).toRingHom).isLeftDerived).unit.app
          ((diagonalDerivedExtension R B).obj KB))) := by
  let : Module.Flat R B := Module.Flat.trans R A B
  obtain ⟨P, hP, ⟨e⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative.{u, u} KB
  have hp := includeLeftRingHom_flat R B
  have hp' : ((diagonalQuotient R A B).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)).Flat := by
    rw [diagonalQuotient_comp_includeLeftRingHom]
    exact includeLeftRingHom_flat A B
  exact @epi_homologyFunctor_map_derivedUnit_of_flat B (B ⊗[R] B) (B ⊗[A] B) _ _ _ _ _ hp
    (surjective_diagonalQuotient R A B) hp' _ _
    (totalDerivedExtensionScalars.{u, u, u} (diagonalQuotient R A B).toRingHom).isLeftDerived
    P hP _ (diagonalDerivedExtensionIso R B KB P e).symm n

end

end Dualizing

end
