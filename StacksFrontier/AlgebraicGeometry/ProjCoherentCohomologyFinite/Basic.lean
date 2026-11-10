module

public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessCoproduct.RingBase
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
public import StacksFrontier.AlgebraicGeometry.ProjTwistCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreFiniteness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness of the cohomology of a coherent module on `Proj` of a ring generated in degree one

Let `𝒜` be a graded ring generated in degree one over `𝒜 0`, let `R` be a Noetherian ring and let
`Proj 𝒜 ⟶ Spec R` be proper. Then `Hⁿ(Proj 𝒜, ℱ)` is a finite `R`-module for every coherent `ℱ`
and every `n`. Specialised to `𝒜 = R[T₀, …, Tₙ]` this is the finiteness of the cohomology of a
coherent module on `ℙⁿ_R`.

## Main results

* `Stacks.ProjCoherentCohomologyFinite.forall_moduleFinite_cohomology_of_twists`: the general
  statement, for an arbitrary graded ring `𝒜`, assuming that the tensor powers of `𝒪(1)` are the
  twisting sheaves, that every quasi-coherent module of finite type is a quotient of a finite
  direct sum of negative twists, and that every twist is coherent with finite cohomology.
* `Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff`: the structure morphism
  `Proj R[T₀, …, Tₙ] ⟶ Spec R` of `Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff` is
  proper.
* `Stacks.ProjCoherentCohomologyFinite.forall_moduleFinite_cohomology_projectiveSpace`:
  `H^q(ℙⁿ_R, ℱ)` is a finite `R`-module for every coherent `ℱ`, for `R` Noetherian and
  `n = m + 1 ≥ 1`.
* `Stacks.ProjCoherentCohomologyFinite.forall_isCoherent_rightDerived_projectiveSpace`: the
  higher direct images `R^q f_* ℱ` of a coherent `ℱ` along `ℙⁿ_R ⟶ Spec R` are coherent.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.ProperCohomologyFinite

universe u v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasFiniteBiproducts_modules

namespace Stacks.ProjCoherentCohomologyFinite

/-! ### The general statement, with the graded ring abstract -/

section Abstract

variable {S : Type u} [CommRing S] {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1)]

/-- For `Proj 𝒜 ⟶ Spec R` proper with `R` Noetherian, if the tensor powers of `𝒪(1)` are the
twisting sheaves, if every quasi-coherent module of finite type is a quotient of a finite direct
sum of negative tensor powers of `𝒪(1)`, and if every twist is coherent with finite cohomology,
then `H^q(Proj 𝒜, 𝒢)` is a finite `R`-module for every coherent `𝒢` and every `q`. -/
theorem forall_moduleFinite_cohomology_of_twists
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (f : AlgebraicGeometry.Proj 𝒜 ⟶ Spec (.of R)) [IsProper f]
    (htw : ∀ n : ℤ,
      Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) n ≅
        twistingSheaf 𝒜 n)
    (hamp : Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists
      (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1))
    (hTcoh : ∀ d : ℤ, _root_.SheafOfModules.IsCoherent (twistingSheaf 𝒜 d))
    (hTfin : ∀ (d : ℤ) (q : ℕ), Module.Finite R
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections (AlgebraicGeometry.Proj 𝒜)).rightDerived q).obj
          (twistingSheaf 𝒜 d)))) :
    ∀ G : (AlgebraicGeometry.Proj 𝒜).Modules, _root_.SheafOfModules.IsCoherent G →
      ∀ q : ℕ, Module.Finite R
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom).obj
          (((moduleGlobalSections (AlgebraicGeometry.Proj 𝒜)).rightDerived q).obj G)) :=
  AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_epi_coproduct
    R f (fun d : ℤ => twistingSheaf 𝒜 d) hTcoh hTfin
    fun G hG =>
      Stacks.AlgebraicGeometry.Tag0B5QAmpleRoute.exists_epi_coproduct_twistingSheaf_of_isCoherent
        𝒜 htw hamp G hG

end Abstract

/-! ### Projective space over a Noetherian ring -/

section ProjectiveSpace

open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

/-- The structure morphism `Proj R[T₀, …, Tₙ] ⟶ Spec R` is proper. -/
theorem isProper_projToSpecCoeff (n : ℕ) : IsProper (projToSpecCoeff R n) := by
  have hhom : CommRingCat.ofHom ((GradedRing.projZeroRingHom'
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).comp
      (algebraMap R (MvPolynomial (Fin (n + 1)) R)))
      = Stacks.ProjectiveCohomology.polyDegreeZeroHom R n := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
    change ((DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.C r)) 0 : MvPolynomial (Fin (n + 1)) R) = MvPolynomial.C r
    exact DirectSum.decompose_of_mem_same _
      ((MvPolynomial.mem_homogeneousSubmodule 0 _).2 (MvPolynomial.isHomogeneous_C _ r))
  have h : projToSpecCoeff R n = Stacks.ProjectiveCohomology.projModelToSpec R n :=
    congrArg (fun φ => Proj.toSpecZero
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ≫ Spec.map φ) hhom
  rw [h]
  infer_instance

/-- The cohomology `H^q(ℙⁿ_R, 𝒢)` of a coherent module `𝒢` on `ℙⁿ_R` is a finite `R`-module, for
`R` Noetherian and `n = m + 1 ≥ 1`. -/
@[ega "III 2.2.2" "clause (i), special case"]
theorem forall_moduleFinite_cohomology_projectiveSpace [IsNoetherianRing R] (m : ℕ) :
    ∀ G : (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R)).Modules,
      _root_.SheafOfModules.IsCoherent G → ∀ q : ℕ, Module.Finite R
        ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of R)).inv ≫
            (projToSpecCoeff R (m + 1)).appTop).hom).obj
          (((moduleGlobalSections (AlgebraicGeometry.Proj
              (MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R))).rightDerived q).obj G)) :=
  have := isProper_projToSpecCoeff R (m + 1)
  forall_moduleFinite_cohomology_of_twists
    (MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R) R (projToSpecCoeff R (m + 1))
    (Stacks.AlgebraicGeometry.ProjTwistPowers.htw_of_adjoin _ (by
      rw [← Stacks.AlgebraicGeometry.ProjTwistMono.range_coe_degree_one
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R)]
      exact Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule
        (Fin (m + 1 + 1)) R))
    (Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple
      (X := AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R))
      (twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R) 1)
      (Stacks.ProjectiveSpace.isAmple_twistingSheaf_one R (m + 1)))
    (fun d => isCoherent_twistingSheaf_polyGrading R (m + 1) d)
    (fun d q => Stacks.ProjectiveSpace.Cohomology.moduleFinite_twistCohomology_succ R m d q)

/-- The higher direct images `R^q f_* 𝒢` of a coherent module `𝒢` along the structure morphism
`f : ℙⁿ_R ⟶ Spec R` are coherent, for `R` Noetherian and `n = m + 1 ≥ 1`. -/
theorem forall_isCoherent_rightDerived_projectiveSpace [IsNoetherianRing R] (m : ℕ) :
    ∀ G : (AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (Fin (m + 1 + 1)) R)).Modules,
      _root_.SheafOfModules.IsCoherent G → ∀ q : ℕ,
        (((Scheme.Modules.pushforward (projToSpecCoeff R (m + 1))).rightDerived q).obj
          G).IsCoherent := by
  intro G hG q
  have : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  exact isCoherent_rightDerived_of_moduleFinite_cohomology_ringBase
    R (projToSpecCoeff R (m + 1)) G q
    (forall_moduleFinite_cohomology_projectiveSpace R m G hG q)

end ProjectiveSpace

end Stacks.ProjCoherentCohomologyFinite

end
