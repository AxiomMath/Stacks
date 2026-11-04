module

public import StacksFrontier.RingTheory.Koszul.SheafSectionKernel
public import StacksFrontier.RingTheory.Koszul.SheafSectionBimoduleSystemComplex

/-!
# Derived global sections on the Koszul sheaf reflect isomorphisms on `QC`

Let `f₁, …, f_r` be elements of a commutative ring `R` and `ℬ = Koszul.liftedPowSheafAlgebra f` the
sheaf of Koszul differential graded algebras `(K_{n+1})_n` on the chaotic site
`Stacks.LiftedNat`. This file proves the last paragraph of the proof of Proposition 0GZK: an object
of `QC(ℬ, d)` with zero derived global sections is zero, and consequently the derived global
sections `RΓ : D(ℬ, d) ⥤ D(R)` reflect isomorphisms between objects of `QC(ℬ, d)`. No
proregularity is assumed.

## Main results

* `Koszul.isZero_of_qc_of_isZero_derivedGlobalSections`: **an object of `QC(ℬ, d)` with
  `RΓ(M) = 0` is zero.**
* `Koszul.isIso_of_qc_of_isIso_derivedGlobalSections_map`: **a morphism of `QC(ℬ, d)` whose
  derived global sections are an isomorphism is an isomorphism.**

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Koszul

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- **An object of `QC(ℬ, d)` with zero derived global sections is zero.** This is the last
paragraph of the proof of Proposition 0GZK: from `0 = R lim M_n` one gets
`0 = (R lim M_n) ⊗^𝐋_R K_t = R lim (M_n ⊗^𝐋_R K_t) = R lim (M_n ⊗^𝐋_{K_n} K_t)` by Tag 0GZJ, and
the last tower is constant with value `M_t` by quasi-coherence, so `M_t = 0` for every `t`. -/
theorem isZero_of_qc_of_isZero_derivedGlobalSections
    {M : SheafOfModules.DifferentialGradedModule.derivedCategory.{u, u, u}
      (liftedPowSheafAlgebra.{u} f)}
    (hM : SheafOfModules.DifferentialGradedModule.Chaotic.QC _ M)
    (h : IsZero ((Stacks.ChaoticSite.derivedGlobalSections R (liftedPowSheafAlgebra f)).obj M)) :
    IsZero M :=
  isZero_of_qc_of_isZero_derivedGlobalSections_of_baseTower
    (fun ht 𝓜 hΓ _ K' hK' =>
      isZero_of_isDerivedLimit_powBaseDegreeZeroDerivedTensorTower_liftedPowSection f ht 𝓜 hΓ
        K' hK') hM h

/-- **The derived global sections reflect isomorphisms between objects of `QC(ℬ, d)`.** -/
theorem isIso_of_qc_of_isIso_derivedGlobalSections_map
    {M N : SheafOfModules.DifferentialGradedModule.derivedCategory.{u, u, u}
      (liftedPowSheafAlgebra.{u} f)}
    (hM : SheafOfModules.DifferentialGradedModule.Chaotic.QC _ M)
    (hN : SheafOfModules.DifferentialGradedModule.Chaotic.QC _ N) (φ : M ⟶ N)
    (hφ : IsIso ((Stacks.ChaoticSite.derivedGlobalSections R (liftedPowSheafAlgebra f)).map φ)) :
    IsIso φ :=
  Stacks.ChaoticSite.isIso_of_isIso_derivedGlobalSections_map_of_kernel R _
    (fun _ hM' h' => isZero_of_qc_of_isZero_derivedGlobalSections f hM' h') hM hN φ hφ

end Koszul

end
