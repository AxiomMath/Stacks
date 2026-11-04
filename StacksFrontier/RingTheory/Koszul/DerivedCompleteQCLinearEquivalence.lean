module

public import StacksFrontier.RingTheory.Koszul.DerivedCompleteQCEquivalence
public import StacksFrontier.Homology.DerivedComplete.CompletionAdjunction
public import StacksFrontier.CategoryTheory.Triangulated.RestrictEquivalenceLinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConstantQuasiCoherent

/-!
# `D_comp(R, I) ≃ QC(ℬ)` as `R`-linear triangulated categories

Let `R` be a commutative ring, `f₁, …, f_r ∈ R`, `I = (f₁, …, f_r)` and `ℬ` the sheaf `n ↦ K_{n+1}`
of Koszul algebras on `f₁^{n+1}, …, f_r^{n+1}` on the chaotic site of the natural numbers. The
derived complete objects form a triangulated subcategory `D_comp(R, I)` of `D(R)`, and `QC(ℬ)` is
a triangulated subcategory of `D(ℬ, d)`. The equivalence `D_comp(R, I) ≌ QC(ℬ)` of step (4) of
the proof of Proposition 0GZK is the restriction of the adjunction `F' ⊣ RΓ`; when the derived
extension of scalars `F'` commutes with the shifts, is triangulated and is `R`-linear, this is an
equivalence of `R`-linear triangulated categories.

## Main definitions

* `Koszul.derivedCompleteQCLinearTriangulatedEquivalenceOfKernel`: **the equivalence
  `D_comp(R, I) ≌ QC(ℬ)` as an equivalence of `R`-linear triangulated categories**, given that the
  derived global sections kill no nonzero quasi-coherent object.

## Main results

* `Koszul.derivedComplete_isTriangulated`: the derived complete objects form a triangulated
  subcategory of `D(R)`.
* `Koszul.derivedCompleteQCLinearTriangulatedEquivalenceOfKernel_equivalence`: its underlying
  equivalence is `Koszul.derivedCompleteQCEquivalenceOfKernel`.

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.PresheafOfModules Stacks.ChaoticSite

universe u

namespace Koszul

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- The derived complete objects of `D(R)` with respect to `(f₁, …, f_r)` form a triangulated
subcategory. -/
instance derivedComplete_isTriangulated : (derivedComplete f).IsTriangulated :=
  CompletionAdjunction.isDerivedComplete_isTriangulated R (Ideal.span (Set.range f))

variable (hker : ∀ M : derivedCategory.{u, u, u} (liftedPowSheafAlgebra f),
      Chaotic.QC (liftedPowSheafAlgebra f) M →
        IsZero ((derivedGlobalSections R (liftedPowSheafAlgebra f)).obj M) → IsZero M)
  [(derivedExtend (extendInvertsQuasiIso f)).CommShift ℤ]
  [(derivedExtend (extendInvertsQuasiIso f)).IsTriangulated]
  [(derivedExtend (extendInvertsQuasiIso f)).Linear R]

/-- **The equivalence `D_comp(R, I) ≌ QC(ℬ)` of step (4) of the proof of Proposition 0GZK, as an
equivalence of `R`-linear triangulated categories**: the restriction of the adjunction `F' ⊣ RΓ`,
given that the derived global sections kill no nonzero quasi-coherent object, for the shift,
triangulated and `R`-linear structures of the derived extension of scalars `F'`. -/
def derivedCompleteQCLinearTriangulatedEquivalenceOfKernel :
    LinearTriangulatedEquivalence R (derivedComplete f).FullSubcategory
      (Chaotic.QC (liftedPowSheafAlgebra f)).FullSubcategory :=
  (derivedExtendAdjunction (extendInvertsQuasiIso f)).restrictLinearTriangulatedEquivalence R
    (P := derivedComplete f) (Q := Chaotic.QC (liftedPowSheafAlgebra f))
    (fun X _ => qc_derivedExtend_obj (extendInvertsQuasiIso f) X)
    (fun Y _ => isDerivedComplete_derivedGlobalSections f Y)
    (fun X hX => isIso_derivedExtendAdjunction_unit_app (extendInvertsQuasiIso f) X hX)
    (fun _ _ g hY hY' hg => isIso_of_isIso_derivedGlobalSections_map_of_kernel R _ hker hY hY' g hg)

/-- The underlying equivalence of `derivedCompleteQCLinearTriangulatedEquivalenceOfKernel` is
`derivedCompleteQCEquivalenceOfKernel`. -/
theorem derivedCompleteQCLinearTriangulatedEquivalenceOfKernel_equivalence :
    (derivedCompleteQCLinearTriangulatedEquivalenceOfKernel f hker).equivalence =
      derivedCompleteQCEquivalenceOfKernel f hker :=
  rfl

end Koszul

end
