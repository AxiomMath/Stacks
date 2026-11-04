module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveAmbientSections
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectivePushforwardTruncation
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedPullbackSections
public import StacksCore.Tactic.StacksAttribute

/-!
# `H⁰(X, 𝒪_X(q)) = Iᑫ` as an `A`-module, and the twisted derived pullback

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `p : X ⟶ Spec A` the blowup of `Spec A` in `I`.
[Stacks, Tag 0AG6] clause (3) — the canonical map `Iᑫ ⟶ Γ(X, 𝒪_X(q))` is bijective for every large
`q` — is available as `Stacks.Blowup.exists_forall_bijective_ambientSections`, but there it is a
bijection of *additive groups*: `Stacks.LocalCohomology.UniformityIII.ambientSections` is an
`AddMonoidHom`.

This file proves that the canonical map is `A`-linear, hence, for every large `q`, an isomorphism

`Γ(X, 𝒪_X(q)) ≅ Iᑫ`  in `ModuleCat A`.

The canonical map is `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` of the Rees grading
precomposed with the `A`-linear `Stacks.Blowup.reesGradingEquivPow`, and its linearity comes down
to the canonical section attached to `a • b`, for `a : A` and `b` homogeneous in the Rees algebra,
being `a` times the one attached to `b`, where `a` acts on sections through the global function it
pulls back to along `X ⟶ Spec A`.

Together with the vanishing of the higher cohomology of `𝒪_X(n)` for large `n`, this gives
[Stacks, Tag 0G9Z]: `RΓ(X, Lp^*(M̃) ⊗^𝐋 𝒪_X(n)) ≅ M ⊗^𝐋_A Iⁿ` for every large `n` and every
`A`-module `M`.

## Main results

All in the namespace `Stacks.Blowup`:

* `degreeSection_smul`: the formula above — the canonical section map of the Rees grading is
  semilinear over the coefficients.
* `ambientSectionsLinear`: the canonical map `Iᑫ ⟶ Γ(X, 𝒪_X(q))` as an `A`-linear map.
* `sectionsIsoIdealPow`: the isomorphism of `A`-modules it becomes once it is bijective.
* `exists_forall_sectionsIsoIdealPow`: **[Stacks, Tag 0AG6] clause (3) as an isomorphism of
  `A`-modules**, for every `q` above a threshold depending only on `A` and `I`.
* `exists_threshold_nonempty_derivedGlobalSectionsTwistedPullback_iso_derivedTensorIdealPow`:
  **[Stacks, Tag 0G9Z]** — for `A` Noetherian and `I ⊆ A` an ideal there is a `q₀` such that
  `RΓ(X, Lp^*(M̃) ⊗^𝐋 𝒪_X(n)) ≅ M ⊗^𝐋_A Iⁿ` for every `n ≥ q₀` and every `A`-module `M`.

## Implementation notes

`Stacks.Blowup.degreeSection_smul` is stated with the sections typed as in
`Stacks.AlgebraicGeometry.ProjTwistSections`: at the type `AlgebraicGeometry.globalSectionsOver`
gives them, no `HSMul` instance is found for the action of `Stacks.Blowup.blowUpCoeffScalar I a`.

## References

* [Stacks Project, Tag 0AG6](https://stacks.math.columbia.edu/tag/0AG6)
* [Stacks Project, Tag 0AG7](https://stacks.math.columbia.edu/tag/0AG7)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 0G9Z](https://stacks.math.columbia.edu/tag/0G9Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.Cohomology.AffineBase
open Stacks.Cohomology.DerivedPullbackOfATilde
open Stacks.SheafOfModules.Tensor
open Stacks.LocalCohomology.UniformityIII (ambientSections)
open Stacks.AlgebraicGeometry.ProjTwistSections (degreeSection_apply)
open scoped ModuleCat.Algebra
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u

namespace Stacks.Blowup

variable {A : Type u} [CommRing A] (I : Ideal A)

section Sections

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

/-- **A coefficient scaling a homogeneous element of the Rees algebra is the degree-zero
homogeneous scalar it names.** Scaling by `a : A` inside the degree-`q` piece of the Rees algebra
is multiplication by the image of `a` in the degree-zero piece, which is
`Stacks.Blowup.reesGradingZeroEquiv`. -/
theorem coe_smul_reesGrading (q : ℕ) (a : A) (b : reesGrading I q) :
    ((a • b : reesGrading I q) : reesAlgebra I)
      = ((reesGradingZeroEquiv I a : reesGrading I 0) : reesAlgebra I) • (b : reesAlgebra I) := by
  have h0 : ((reesGradingZeroEquiv I a : reesGrading I 0) : reesAlgebra I)
      = algebraMap A (reesAlgebra I) a := rfl
  rw [h0, Submodule.coe_smul, Algebra.smul_def, smul_eq_mul]

/-- **The canonical section map on the blowup is semilinear over the coefficients.** For `a : A`
and `b` homogeneous of degree `q` in the Rees algebra, the canonical global section of `𝒪_X(q)`
attached to `a • b` is `a` acting on the one attached to `b`, where `a` acts as the global function
it pulls back to along the structure morphism `X ⟶ Spec A`. -/
theorem degreeSection_smul (q : ℕ) (a : A) (b : reesGrading I q) :
    degreeSection (reesGrading I) q (a • b)
      = blowUpCoeffScalar I a • degreeSection (reesGrading I) q b := by
  refine Subtype.ext (funext fun x => ?_)
  have hR : (blowUpCoeffScalar I a • degreeSection (reesGrading I) q b).1 x =
      HomogeneousLocalization.val ((blowUpCoeffScalar I a).1 x) •
        (degreeSection (reesGrading I) q b).1 x := rfl
  have h1 : (degreeSection (reesGrading I) q (a • b)).1 x
      = LocalizedModule.mk ((a • b : reesGrading I q) : reesAlgebra I)
          (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    degreeSection_apply (reesGrading I) q (a • b) x
  have h2 : (degreeSection (reesGrading I) q b).1 x
      = LocalizedModule.mk ((b : reesAlgebra I))
          (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    degreeSection_apply (reesGrading I) q b x
  have hval : HomogeneousLocalization.val ((blowUpCoeffScalar I a).1 x)
      = Localization.mk ((reesGradingZeroEquiv I a : reesGrading I 0) : reesAlgebra I)
          (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    blowUpCoeffScalar_val I a x.1
  rw [hR, h1, h2, hval, LocalizedModule.mk_smul_mk, one_mul]
  exact congrArg (fun z : reesAlgebra I =>
      LocalizedModule.mk z (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl))
    (coe_smul_reesGrading I q a b)

/-- **The canonical map `Iᑫ ⟶ Γ(X, 𝒪_X(q))` as an `A`-linear map.** Its underlying additive map is
`Stacks.LocalCohomology.UniformityIII.ambientSections`. -/
def ambientSectionsLinear (n : ℕ) :
    (I ^ n : Ideal A) →ₗ[A]
      ((globalSectionsOver (toSpec I)).obj (blowUpTwist I (n : ℤ)) : Type u) where
  toFun x := ambientSections I n x
  map_add' x y := map_add (ambientSections I n) x y
  map_smul' a x := by
    show degreeSection (reesGrading I) n (reesGradingEquivPow I n (a • x))
      = blowUpCoeffScalar I a • degreeSection (reesGrading I) n (reesGradingEquivPow I n x)
    rw [map_smul]
    exact degreeSection_smul I n a (reesGradingEquivPow I n x)

/-- **`Γ(X, 𝒪_X(n)) ≅ Iⁿ` as `A`-modules**, from bijectivity of the canonical map in degree `n`.
This is the hypothesis `hsections` of
`exists_forall_nonempty_derivedGlobalSectionsTwistedPullback_iso_derivedTensorIdealPow`. -/
def sectionsIsoIdealPow (n : ℕ) (hbij : Function.Bijective (ambientSections I n)) :
    (globalSectionsOver (toSpec I)).obj (blowUpTwist I (n : ℤ)) ≅
      ModuleCat.of A (I ^ n : Ideal A) :=
  (LinearEquiv.ofBijective (ambientSectionsLinear I n) hbij).symm.toModuleIso

/-- **[Stacks, Tag 0AG6] clause (3) on the blowup, as an isomorphism of `A`-modules.** For `A`
Noetherian and `I ⊆ A` an ideal there is a `q₀` such that `Γ(X, 𝒪_X(n)) ≅ Iⁿ` in `ModuleCat A` for
every `n ≥ q₀`. -/
theorem exists_forall_sectionsIsoIdealPow [IsNoetherianRing A] :
    ∃ q₀ : ℕ, ∀ n : ℕ, q₀ ≤ n →
      Nonempty ((globalSectionsOver (toSpec I)).obj (blowUpTwist I (n : ℤ)) ≅
        ModuleCat.of A (I ^ n : Ideal A)) := by
  obtain ⟨q₀, hq₀⟩ := exists_forall_bijective_ambientSections I
  exact ⟨q₀, fun n hn => ⟨sectionsIsoIdealPow I n (hq₀ n hn)⟩⟩

end Sections

section Tensor

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Cohomology of the twisted derived pullback along the affine blowup, unconditionally.** Let
`A` be a Noetherian ring, `I ⊆ A` an ideal and `p : X ⟶ Spec A` the blowup of `Spec A` in `I`.
There is a `q₀` such that for every `n ≥ q₀` and **any** `A`-module `M`,

`RΓ(X, Lp^*(M̃) ⊗^𝐋_{𝒪_X} 𝒪_X(n)) ≅ M ⊗^𝐋_A Iⁿ`  in `D(A)`. -/
@[stacks 0G9Z]
theorem exists_threshold_nonempty_derivedGlobalSectionsTwistedPullback_iso_derivedTensorIdealPow
    [IsNoetherianRing A] :
    ∃ q₀ : ℕ, ∀ n : ℕ, q₀ ≤ n →
      ∀ M : ModuleCat.{u} (CommRingCat.of A),
        Nonempty ((AlgebraicGeometry.derivedGlobalSectionsOver (toSpec I)).obj
            (((Stacks.Cohomology.TorAmplitude.derTensor (blowUpRingedSpace I)).tensor.obj
                ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
                  (toSpecRingedSpace I)).obj (DerivedCategory.Q.obj (tildeComplex
                    ((CochainComplex.singleFunctor (ModuleCat.{u} (CommRingCat.of A)) 0).obj
                      M))))).obj
              (DerivedCategory.Q.obj
                ((CochainComplex.singleFunctor (BlowUpModules I) 0).obj
                  (blowUpTwist I (n : ℤ))))) ≅
          ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor.obj
              (DerivedCategory.Q.obj
                ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M))).obj
            (DerivedCategory.Q.obj
              ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
                (ModuleCat.of A (I ^ n : Ideal A))))) := by
  obtain ⟨q₁, hq₁⟩ := exists_forall_isZero_rightDerivedPlus_twistingSheaf_reesGrading I
  obtain ⟨q₂, hq₂⟩ := exists_forall_sectionsIsoIdealPow I
  refine ⟨max q₁ q₂, fun n hn M => (hq₂ n (le_trans (le_max_right q₁ q₂) hn)).elim fun e => ?_⟩
  exact nonempty_derivedGlobalSectionsTwistedPullback_iso_derivedTensorIdealPow I M n
    (hq₁ n (le_trans (le_max_left q₁ q₂) hn)) e

end Tensor

end Stacks.Blowup

end
