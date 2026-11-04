module

public import StacksFrontier.RingTheory.Koszul.ExtendUnitComplete
public import StacksFrontier.RingTheory.Koszul.ExtendInvertsQuasiIso
public import StacksFrontier.RingTheory.Koszul.DerivedGlobalSectionsComplete
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantExtensionQC
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticGlobalSectionsConservative
public import StacksFrontier.CategoryTheory.Adjunction.RestrictEquivalence

/-!
# Derived complete complexes and quasi-coherent modules over the Koszul tower

Let `R` be a commutative ring, `f₁, …, f_r ∈ R`, `I = (f₁, …, f_r)` and `ℬ` the sheaf `n ↦ K_{n+1}`
of Koszul algebras on `f₁^{n+1}, …, f_r^{n+1}` on the chaotic site of the natural numbers. The
derived extension of scalars `F' : D(R) ⥤ D(ℬ, d)` is left adjoint to the derived global sections
`RΓ`; `F'` takes values in `QC(ℬ)`, `RΓ` takes values in `D_comp(R, I)`, the unit is invertible on
`D_comp(R, I)`, and `RΓ` reflects isomorphisms between quasi-coherent objects. Hence `F'` and `RΓ`
restrict to quasi-inverse equivalences `D_comp(R, I) ≌ QC(ℬ)`: step (4) of the proof of
Proposition 0GZK.

## Main definitions

* `Koszul.derivedCompleteQCEquivalence`: **the equivalence `D_comp(R, I) ≌ QC(ℬ)`**, with functor
  `K ↦ K ⊗^𝐋_R ℬ` and quasi-inverse `RΓ`.

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.PresheafOfModules Stacks.ChaoticSite

universe u

namespace Koszul

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- The derived complete objects of `D(R)` with respect to `(f₁, …, f_r)`. -/
abbrev derivedComplete : ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun X => IsDerivedComplete (Ideal.span (Set.range f)) X

/-- **The equivalence `D_comp(R, I) ≌ QC(ℬ)`** induced by the adjunction `F' ⊣ RΓ`, given that the
derived global sections kill no nonzero quasi-coherent object. -/
def derivedCompleteQCEquivalenceOfKernel
    (hker : ∀ M : derivedCategory.{u, u, u} (liftedPowSheafAlgebra f),
      Chaotic.QC (liftedPowSheafAlgebra f) M →
        IsZero ((derivedGlobalSections R (liftedPowSheafAlgebra f)).obj M) → IsZero M) :
    (derivedComplete f).FullSubcategory ≌
      (Chaotic.QC (liftedPowSheafAlgebra f)).FullSubcategory :=
  (derivedExtendAdjunction (extendInvertsQuasiIso f)).restrictEquivalence
    (P := derivedComplete f) (Q := Chaotic.QC (liftedPowSheafAlgebra f))
    (fun X _ => qc_derivedExtend_obj (extendInvertsQuasiIso f) X)
    (fun Y _ => isDerivedComplete_derivedGlobalSections f Y)
    (fun X hX => isIso_derivedExtendAdjunction_unit_app (extendInvertsQuasiIso f) X hX)
    (fun _ _ g hY hY' hg => isIso_of_isIso_derivedGlobalSections_map_of_kernel R _ hker hY hY' g hg)

end Koszul

end
