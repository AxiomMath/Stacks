module

public import StacksFrontier.AlgebraicGeometry.ProjCoherentII.TruncationFinite
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoherentSerreVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistSectionsCoeffAction

/-!
# The twisted global sections of a coherent sheaf on `ℙⁿ_R`, degree by degree

Let `R` be a Noetherian ring, `n ≥ 0` and `ℱ` a coherent sheaf on `ℙⁿ_R = Proj R[T₀, …, Tₙ]`.
This file supplies the *degreewise* input to the sandwich in the proof of [Stacks, Tag 01YS]
clause (5):

* every twist `ℱ(d)` is again coherent, because `𝒪(d)` is invertible and `ℙⁿ_R` is Noetherian;
* hence `Γ(ℙⁿ_R, ℱ(d))` is a finite `R`-module, by clause (3) of the same tag at `i = 0`, the
  identification of `H⁰` with `Γ` being left exactness of sections;
* hence the degree-`d` homogeneous piece of `⨁_{m ∈ ℤ} Γ(ℙⁿ_R, ℱ(m))` spans a finitely generated
  `R[T₀, …, Tₙ]`-submodule, the coefficients acting through the constant polynomials.

Combining the last item with
`Stacks.AlgebraicGeometry.ProjTwistedSections.moduleFinite_twistedGlobalSectionsTruncation`
reduces [Stacks, Tag 01YS] clause (5) to one geometric statement: that above some degree every
homogeneous piece lies in the span of the piece one degree below. That statement is proved in
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/TwistSectionsDegreeOne.lean`, which
therefore carries clause (5) itself.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.isCoherent_twistSheafOfModules`: a twist of a
  coherent sheaf on `Proj 𝒮` is coherent, for `𝒮` generated in degree one with `Proj 𝒮`
  Noetherian.
* `Stacks.ProjectiveSpace.Cohomology.moduleFinite_sections_of_isCoherent`: `Γ(ℙⁿ_R, ℱ)` is a
  finite `R`-module for `ℱ` coherent.
* `Stacks.ProjectiveSpace.Cohomology.moduleFinite_twistedSectionsComponent`: so is each
  `Γ(ℙⁿ_R, ℱ(d))`.
* `Stacks.ProjectiveSpace.Cohomology.fg_span_twistedGlobalSectionsGrading`: the degree-`d`
  homogeneous piece of `⨁_{m ∈ ℤ} Γ(ℙⁿ_R, ℱ(m))` spans a finitely generated
  `R[T₀, …, Tₙ]`-submodule.
* `Stacks.ProjectiveSpace.Cohomology.moduleFinite_truncation_of_span_grading`:
  **[Stacks, Tag 01YS] clause (5) granted the degree-one generation of the high degrees.**

## Where clause (5) itself is

No `stacks` attribute is attached here: the statements of this file are the degreewise half of
the source's sandwich, and `moduleFinite_truncation_of_span_grading` still carries the hypothesis
`hstep` — that for all `d` large enough every global section of `ℱ(d)` is an
`R[T₀, …, Tₙ]`-combination of global sections of the lower twists.

`hstep` is **discharged**, and clause (5) with it, in
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/TwistSectionsDegreeOne.lean`:
`Stacks.ProjectiveSpace.Cohomology.exists_forall_subset_span_twistedGlobalSectionsGrading` is
`hstep` and `Stacks.ProjectiveSpace.Cohomology.moduleFinite_truncation_of_isCoherent` is the
clause, carrying the attribute. The ingredients are the ones the source uses: the surjection
`H⁰(ℙⁿ_R, ⨁_j 𝒪(d_j)(d)) → H⁰(ℙⁿ_R, ℱ(d))` for `d` large, from the vanishing of
`H¹(ℙⁿ_R, 𝒦(d))` for the coherent kernel `𝒦` — clause (4), available as
`Stacks.ProjectiveSpace.SerreVanishing.exists_isZero_Hgroup_twist_of_isCoherent` — and the
computation of `Γ(ℙⁿ_R, 𝒪(e))`, available degreewise as
`Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection_mvPolynomial` and as a graded ring
isomorphism as `Stacks.ProjectiveSpace.Cohomology.polynomialSectionsRingEquiv`.

The three statements that carry the work are:

* the degree-one generation for a *twisting* sheaf — every global section of `𝒪(e)(1 + d)` is a
  combination of global sections of `𝒪(e)(d)` with linear forms as coefficients, for
  `e + d ≥ 0` — which is
  `Stacks.ProjectiveSpace.Cohomology.exists_sum_homogeneousScalar_twistingSheaf`: the comparison
  `𝒪(e)(d) ≅ 𝒪(e + d)` of
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin`, the
  compatibility of that comparison with the degree-one scalar action
  (`Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.mul_comp_twistMultiplicationMap`), and
  `𝒮 (m + 1) = 𝒮 1 · 𝒮 m`
  (`AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_sum_degreeOne_mul`);
* the functoriality in the sheaf that transports it along a presentation,
  `Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.globalSections_map_homogeneousScalar`;
* additivity over the finite direct sum,
  `Stacks.AlgebraicGeometry.ProjTwistDegreeOneStep.eq_sum_bicone_twistedSections`.

## Implementation notes

The `R`-module structure on a section group is restriction of scalars along
`Stacks.ProjectiveSpace.Cohomology.coeffScalar`, which is by definition (and by
`Stacks.ProjectiveSpace.Cohomology.ΓSpecIso_inv_comp_appTop_hom_eq_coeffScalar`, which is `rfl`)
the scalar of the structure morphism that clause (3) is stated with, so no transport intervenes
between clause (3) and the statements here.

`fg_span_twistedGlobalSectionsGrading` is the instance at `ι = MvPolynomial.C` of
`Stacks.AlgebraicGeometry.ProjTwistedSections.fg_span_twistedGlobalSectionsGrading_of_span_eq_top`,
which takes the ring acting on one section group and the compatibility of that action with
`DirectSum.of` as data; the compatibility here is
`Stacks.ProjectiveSpace.Cohomology.C_smul_of`. Keeping the argument in that generality is what
keeps the elaborator away from `polyGrading`, which it otherwise unfolds past the heartbeat
limit while unifying the two spellings of a section group.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 03GK](https://stacks.math.columbia.edu/tag/03GK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistedSections
open Stacks.ProjectiveCohomology (polyGrading)

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

/-- **A twist of a coherent sheaf on `Proj 𝒮` is coherent**, for a graded ring generated in
degree one over its degree-zero part: `𝒪(d)` is invertible there, and the tensor product of a
coherent sheaf with an invertible one is coherent. -/
theorem isCoherent_twistSheafOfModules {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S]
    [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    (F : (AlgebraicGeometry.Proj 𝒮).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (d : ℤ) :
    _root_.SheafOfModules.IsCoherent (twistSheafOfModules 𝒮 F d) :=
  @AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible
    (AlgebraicGeometry.Proj 𝒮) F (twistingSheaf 𝒮 d) hF
    (algebraicGeometry_isInvertible_twistingSheaf 𝒮 hgen d)

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.ProjectiveSpace.Cohomology

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### `Γ(ℙⁿ_R, ℱ)` is a finite `R`-module -/

/-- **`H⁰(ℙⁿ_R, ℱ)` is `Γ(ℙⁿ_R, ℱ)`**, as a module over the coefficients: sections over an open
are left exact, so their zeroth right derived functor is themselves. -/
def cohomologyZeroIsoSections (F : (AlgebraicGeometry.Proj (polyGrading R n)).Modules) :
    (ModuleCat.restrictScalars.{u} (coeffScalar R n)).obj
        (((Stacks.Cohomology.sectionsFunctor
          (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).rightDerived 0).obj F) ≅
      (ModuleCat.restrictScalars.{u} (coeffScalar R n)).obj
        ((Stacks.Cohomology.sectionsFunctor
          (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).obj F) :=
  (ModuleCat.restrictScalars.{u} (coeffScalar R n)).mapIso
    ((Stacks.Cohomology.sectionsFunctor
      (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).rightDerivedZeroIsoSelf.app F)

/-- **The global sections of a coherent sheaf on `ℙⁿ_R` are a finite `R`-module.** This is
[Stacks, Tag 01YS] clause (3) at `i = 0`, with `H⁰` identified with `Γ`. -/
theorem moduleFinite_sections_of_isCoherent [IsNoetherianRing R]
    (F : (AlgebraicGeometry.Proj (polyGrading R n)).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) :
    Module.Finite R ((ModuleCat.restrictScalars.{u} (coeffScalar R n)).obj
      ((Stacks.Cohomology.sectionsFunctor
        (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).obj F)) :=
  have : Module.Finite R ((ModuleCat.restrictScalars.{u} (coeffScalar R n)).obj
      (((Stacks.Cohomology.sectionsFunctor
        (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).rightDerived 0).obj F)) :=
    Stacks.ProjectiveSpace.SerreVanishing.moduleFinite_cohomology_of_isCoherent R n F hF 0
  Module.Finite.equiv (cohomologyZeroIsoSections R n F).toLinearEquiv

variable (F : (AlgebraicGeometry.Proj (polyGrading R n)).Modules)

/-- **Each `Γ(ℙⁿ_R, ℱ(d))` is a finite `R`-module** for `ℱ` coherent: the twist is coherent and
the previous statement applies to it. -/
theorem moduleFinite_twistedSectionsComponent [IsNoetherianRing R]
    (hF : _root_.SheafOfModules.IsCoherent F) (d : ℤ) :
    Module.Finite R ((ModuleCat.restrictScalars.{u} (coeffScalar R n)).obj
      ((Stacks.Cohomology.sectionsFunctor
        (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).obj
          (twistSheafOfModules (polyGrading R n) F d))) :=
  moduleFinite_sections_of_isCoherent R n _
    (isCoherent_twistSheafOfModules (polyGrading R n)
      (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) R) F hF d)

/-! ### The homogeneous pieces span finitely generated submodules -/

/-- **The degree-`d` homogeneous piece of `⨁_{m ∈ ℤ} Γ(ℙⁿ_R, ℱ(m))` spans a finitely generated
`R[T₀, …, Tₙ]`-submodule**, for `ℱ` coherent on `ℙⁿ_R` over a Noetherian ring: the piece is
`Γ(ℙⁿ_R, ℱ(d))`, a finite `R`-module, and a coefficient acts as a constant polynomial. -/
theorem fg_span_twistedGlobalSectionsGrading [IsNoetherianRing R]
    (hF : _root_.SheafOfModules.IsCoherent F)
    (D : TwistedGlobalSectionsModule (polyGrading R n) F) (d : ℤ) :
    letI := D.moduleInst
    (Submodule.span (MvPolynomial (Fin (n + 1)) R)
      (twistedGlobalSectionsGrading (polyGrading R n) F d :
        Set (twistedGlobalSections (polyGrading R n) F))).FG := by
  classical
  let := D.moduleInst
  let : Module R (twistedSectionsComponent (polyGrading R n) F d) :=
    ((ModuleCat.restrictScalars.{u} (coeffScalar R n)).obj
      ((Stacks.Cohomology.sectionsFunctor
        (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).obj
          (twistSheafOfModules (polyGrading R n) F d))).isModule
  have hfin : Module.Finite R (twistedSectionsComponent (polyGrading R n) F d) :=
    moduleFinite_twistedSectionsComponent R n F hF d
  obtain ⟨t, ht⟩ := Module.finite_def.mp hfin
  exact fg_span_twistedGlobalSectionsGrading_of_span_eq_top (polyGrading R n) F d
    (fun r => MvPolynomial.C r) (fun r s => C_smul_of R n F D r d s) t ht

/-! ### Clause (5), granted the generation of the high degrees -/

/-- **[Stacks, Tag 01YS] clause (5), granted the degree-one generation of the high degrees.** For
`R` Noetherian, `ℱ` coherent on `ℙⁿ_R` and any `k ∈ ℤ`, the graded `R[T₀, …, Tₙ]`-module
`⨁_{d ≥ k} H⁰(ℙⁿ_R, ℱ(d))` is a finite `R[T₀, …, Tₙ]`-module, provided that above some degree
`B` each homogeneous piece lies in the span of the piece one degree below.

The hypothesis `hstep` is the only thing standing between this and the tag's clause (5), and it
is produced by
`Stacks.ProjectiveSpace.Cohomology.exists_forall_subset_span_twistedGlobalSectionsGrading`, which
is what makes `Stacks.ProjectiveSpace.Cohomology.moduleFinite_truncation_of_isCoherent` the
clause. -/
theorem moduleFinite_truncation_of_span_grading [IsNoetherianRing R]
    (hF : _root_.SheafOfModules.IsCoherent F)
    (D : TwistedGlobalSectionsModule (polyGrading R n) F) (k B : ℤ)
    (hstep : letI := D.moduleInst
      ∀ d : ℤ, B < d →
        (twistedGlobalSectionsGrading (polyGrading R n) F d :
            Set (twistedGlobalSections (polyGrading R n) F)) ⊆
          Submodule.span (MvPolynomial (Fin (n + 1)) R)
            (twistedGlobalSectionsGrading (polyGrading R n) F (d - 1) :
              Set (twistedGlobalSections (polyGrading R n) F))) :
    letI := D.moduleInst
    Module.Finite (MvPolynomial (Fin (n + 1)) R)
      (TwistedGlobalSectionsModule.truncation (polyGrading R n) F D k) :=
  let := D.moduleInst
  moduleFinite_twistedGlobalSectionsTruncation (polyGrading R n) F D.smul_homogeneous k B
    (fun d => fg_span_twistedGlobalSectionsGrading R n F hF D d) hstep

end Stacks.ProjectiveSpace.Cohomology

end
