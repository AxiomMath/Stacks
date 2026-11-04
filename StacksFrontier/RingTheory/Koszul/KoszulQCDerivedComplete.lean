module

public import StacksFrontier.RingTheory.Koszul.DerivedCompleteQCLinearEquivalence
public import StacksFrontier.RingTheory.Koszul.SheafSectionKernelQC
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantExtensionTriangulated

/-!
# `D_comp(R, I) ≌ QC(ℬ)` for the Koszul tower

Let `R` be a commutative ring, `f₁, …, f_r ∈ R`, `I = (f₁, …, f_r)` and `ℬ` the sheaf `n ↦ K_{n+1}`
of Koszul algebras on `f₁^{n+1}, …, f_r^{n+1}` on the chaotic site of the natural numbers. The
adjunction `F' ⊣ RΓ` between `D(R)` and `D(ℬ, d)`, `F'(K) = K ⊗^𝐋_R ℬ`, restricts to an
equivalence `D_comp(R, I) ≌ QC(ℬ)` of `R`-linear triangulated categories, with no proregularity
assumption on `f`.

## Main definitions

* `Koszul.derivedCompleteQCEquivalence`: **the equivalence `D_comp(R, I) ≌ QC(ℬ)`**, with functor
  `K ↦ K ⊗^𝐋_R ℬ` and quasi-inverse `RΓ`.
* `Koszul.derivedCompleteQCLinearTriangulatedEquivalence`: the same, as an equivalence of
  `R`-linear triangulated categories.

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.PresheafOfModules Stacks.ChaoticSite

universe u

namespace Koszul

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- **The equivalence `D_comp(R, I) ≌ QC(ℬ)`**, the restriction of the adjunction `F' ⊣ RΓ`, with
functor `K ↦ K ⊗^𝐋_R ℬ` and quasi-inverse `RΓ`. -/
def derivedCompleteQCEquivalence :
    (derivedComplete f).FullSubcategory ≌
      (Chaotic.QC (liftedPowSheafAlgebra f)).FullSubcategory :=
  derivedCompleteQCEquivalenceOfKernel f
    (fun _ hM h => isZero_of_qc_of_isZero_derivedGlobalSections f hM h)

/-- **The equivalence `D_comp(R, I) ≌ QC(ℬ)` as an equivalence of `R`-linear triangulated
categories.** -/
def derivedCompleteQCLinearTriangulatedEquivalence :
    LinearTriangulatedEquivalence R (derivedComplete f).FullSubcategory
      (Chaotic.QC (liftedPowSheafAlgebra f)).FullSubcategory :=
  derivedCompleteQCLinearTriangulatedEquivalenceOfKernel f
    (fun _ hM h => isZero_of_qc_of_isZero_derivedGlobalSections f hM h)

/-- The underlying equivalence of `derivedCompleteQCLinearTriangulatedEquivalence` is
`derivedCompleteQCEquivalence`. -/
theorem derivedCompleteQCLinearTriangulatedEquivalence_equivalence :
    (derivedCompleteQCLinearTriangulatedEquivalence f).equivalence =
      derivedCompleteQCEquivalence f :=
  rfl

/-- The functor of `derivedCompleteQCEquivalence` is the derived extension of scalars. -/
theorem derivedCompleteQCEquivalence_functor_obj (X : (derivedComplete f).FullSubcategory) :
    ((derivedCompleteQCEquivalence f).functor.obj X).obj =
      (derivedExtend (extendInvertsQuasiIso f)).obj X.obj :=
  rfl

/-- The quasi-inverse of `derivedCompleteQCEquivalence` is the derived global sections. -/
theorem derivedCompleteQCEquivalence_inverse_obj
    (M : (Chaotic.QC (liftedPowSheafAlgebra f)).FullSubcategory) :
    ((derivedCompleteQCEquivalence f).inverse.obj M).obj =
      (derivedGlobalSections R (liftedPowSheafAlgebra f)).obj M.obj :=
  rfl

end Koszul

end
