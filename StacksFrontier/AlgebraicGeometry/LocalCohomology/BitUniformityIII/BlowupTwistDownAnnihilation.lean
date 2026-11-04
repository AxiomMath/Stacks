module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupDegreeZeroScalar
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwistDownCohomology
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.SupportedAnnihilation

/-!
# `ℱ(q) ⟶ p^*K(q-c)` dies against multiplication by `(b⁽¹⁾)^c`

Let `A` be a commutative ring, `I ⊆ A` an ideal and `p : X ⟶ Spec(A)` the blowup of `Spec(A)` in
`I`, and let `ℱ(q)` be the kernel `Stacks.LocalCohomology.UniformityIII.twistedPullbackSupported`.
This file proves that the twisted-down map `ℱ(q) ⟶ p^*K(q) ⟶ p^*K(q - c)`, followed by
multiplication by `(b⁽¹⁾)^c`, is zero for every `b ∈ I`, as used in [Stacks, Tag 0GAA] clause (3).

Twisting down `c` steps followed by multiplication by `(b⁽¹⁾)^c` is multiplication by the
degree-zero homogeneous scalar `Stacks.Blowup.reesConst I (b^c)`, which is `b^c • 𝟙` for the
`A`-linear structure `Stacks.Blowup.blowUpModulesLinear`. Since composition is `A`-bilinear, the
composite equals `b^c • 𝟙 ℱ(q)` followed by the inclusion of `ℱ(q)`, and this vanishes by
[Stacks, Tag 0GA8], `Stacks.LocalCohomology.UniformityIII.smul_twistedPullbackSupported_eq_zero`,
since `b^c ∈ I^c`.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.twistedPullbackTwistScalar`: multiplication by a
  homogeneous scalar as a morphism of twisted-pullback functors, at the
  `CategoryTheory.SheafOfModules` view of the category of sheaves of modules on the blowup.

## Main results

* `Stacks.LocalCohomology.UniformityIII.comp_eq_zero_of_smul_id_eq_zero`: in an `R`-linear
  category, if `φ = r • 𝟙 X` and `r • 𝟙 Z = 0`, then `ι ≫ φ = 0` for every `ι : Z ⟶ X`.
* `Stacks.LocalCohomology.UniformityIII.kernelι_comp_twistDown_comp_twistScalar_eq_zero`: the
  composite above vanishes whenever `b^c` annihilates `ℱ(q)`.
* `Stacks.LocalCohomology.UniformityIII.kernelι_comp_twistDown_comp_twistScalar_eq_zero_of_mem`:
  the composite above vanishes at a chosen presentation of an `(A, n, c)`-module.

## References

* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 0GA8](https://stacks.math.columbia.edu/tag/0GA8)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistedSections (twistScalarSheafMap)

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard

/-- In an `R`-linear category, if an endomorphism `φ` of `X` is `r • 𝟙 X` and `r • 𝟙 Z = 0`,
then `ι ≫ φ = 0` for every `ι : Z ⟶ X`. -/
theorem comp_eq_zero_of_smul_id_eq_zero {R : Type*} [CommRing R] {C : Type*} [Category C]
    [Preadditive C] [Linear R C] {Z X : C} (ι : Z ⟶ X) (φ : X ⟶ X) (r : R)
    (hφ : φ = r • 𝟙 X) (hZ : r • 𝟙 Z = 0) : ι ≫ φ = 0 := by
  subst hφ
  calc ι ≫ (r • 𝟙 X)
      = r • ι := by rw [Linear.comp_smul, Category.comp_id]
    _ = (r • 𝟙 Z) ≫ ι := by rw [Linear.smul_comp, Category.id_comp]
    _ = 0 := by rw [hZ, zero_comp]

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- Multiplication by a homogeneous scalar of degree `i`, tensored into the fixed factor of the
twisted pullback and read at the `CategoryTheory.SheafOfModules` view of the category of sheaves
of modules on the blowup. -/
abbrev twistedPullbackTwistScalar (i : ℕ) (n k : ℤ) (hk : (i : ℤ) + n = k)
    (a : Stacks.Blowup.reesGrading I i) :
    twistedPullbackFunctor I n ⟶ twistedPullbackFunctor I k :=
  Stacks.Blowup.twistScalarFactorMap I i n k hk a

variable {S : ShortComplex (ModuleCat.{u} A)} {c : ℕ}

/-- Let `b ∈ I` and let `q' = q - c`. The inclusion of `ℱ(q) = ker(p^*K(q) ⟶ 𝒢(q))`, followed by
twisting down to `q'` and then by multiplication by the degree-one element `b⁽¹⁾` raised to the
`c`-th power, is the zero morphism, as soon as `b^c` annihilates `ℱ(q)`. -/
theorem kernelι_comp_twistDown_comp_twistScalar_eq_zero (q q' : ℤ) (hq : (c : ℤ) + q' = q)
    (hle : q' ≤ q) {b : A} (hb : b ∈ I)
    (hzero :
      letI : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
        Stacks.Blowup.blowUpModulesLinear I
      (b ^ c) • 𝟙 (twistedPullbackSupported I q (S := S)) = 0) :
    kernel.ι (S.map (twistedPullbackFunctor I q)).toCycles ≫
        (twistedPullbackTwistDown I q q' hle).app S.X₁ ≫
          (twistedPullbackTwistScalar I c q' q hq
              ⟨(Stacks.Blowup.reesDegOne I hb : reesAlgebra I) ^ c,
                Stacks.Blowup.reesDegOnePow_mem_reesGrading I hb c⟩).app S.X₁ = 0 := by
  let : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
    Stacks.Blowup.blowUpModulesLinear I
  have hstep :
      (twistedPullbackTwistDown I q q' hle).app S.X₁ ≫
          (twistedPullbackTwistScalar I c q' q hq
              ⟨(Stacks.Blowup.reesDegOne I hb : reesAlgebra I) ^ c,
                Stacks.Blowup.reesDegOnePow_mem_reesGrading I hb c⟩).app S.X₁ =
        (b ^ c) • 𝟙 ((twistedPullbackFunctor I q).obj S.X₁) :=
    (NatTrans.comp_app _ _ _).symm.trans
      ((NatTrans.congr_app
            (Stacks.Blowup.twistDownFactorMap_comp_twistScalarFactorMap_reesDegOnePow
              I c q q' hq hle hb)
            S.X₁).trans
        (twistScalarFactorMap_reesConst_app_eq_smul_id I q (b ^ c) S.X₁))
  exact comp_eq_zero_of_smul_id_eq_zero _ _ (b ^ c) hstep hzero

/-- Let `M` be an `(A, n, c)`-module with presentation `P`, and let `b ∈ I` and `q' = q - c`. The
inclusion of the kernel `ℱ(q)` attached to `P`, followed by twisting down to `q'` and then by
multiplication by `(b⁽¹⁾)^c`, is the zero morphism. -/
theorem kernelι_comp_twistDown_comp_twistScalar_eq_zero_of_mem {n : ℕ} {M : ANCModule I n c}
    (P : ANCPresentation I n c M) (q q' : ℤ) (hq : (c : ℤ) + q' = q) (hle : q' ≤ q) {b : A}
    (hb : b ∈ I) :
    kernel.ι (P.resShortComplex.map (twistedPullbackFunctor I q)).toCycles ≫
        (twistedPullbackTwistDown I q q' hle).app P.resShortComplex.X₁ ≫
          (twistedPullbackTwistScalar I c q' q hq
              ⟨(Stacks.Blowup.reesDegOne I hb : reesAlgebra I) ^ c,
                Stacks.Blowup.reesDegOnePow_mem_reesGrading I hb c⟩).app
            P.resShortComplex.X₁ = 0 :=
  kernelι_comp_twistDown_comp_twistScalar_eq_zero I q q' hq hle hb
    (smul_twistedPullbackSupported_eq_zero P q (Ideal.pow_mem_pow hb c))

end Stacks.LocalCohomology.UniformityIII

end
