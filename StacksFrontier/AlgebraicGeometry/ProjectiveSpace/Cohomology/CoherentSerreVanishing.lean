module

public import StacksFrontier.AlgebraicGeometry.CohomologyFinitenessCoproduct.RingBase
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.ProjSerreDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistCoherence.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.ProjAmple.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness and Serre vanishing for coherent sheaves on projective space

Let `R` be a Noetherian ring and `ℱ` a coherent sheaf on `ℙⁿ_R = Proj R[T₀, …, Tₙ]`. Then every
cohomology module `H^i(ℙⁿ_R, ℱ)` is a finite `R`-module, and the higher cohomology of a
sufficiently high twist vanishes:
$$ H^i(\mathbf{P}^n_R, \mathcal{F}(d)) = 0 \qquad (i > 0,\ d \gg 0). $$

Both are proved as the source proves them, from the presentation of `ℱ` as a quotient of a finite
direct sum of twists together with the computation of `H^i(ℙⁿ_R, 𝒪(d))`.

## Main results

* `Stacks.ProjectiveSpace.SerreVanishing.exists_epi_coproduct_twistingSheaf`: a coherent sheaf on
  `ℙⁿ_R` is a quotient of a finite direct sum of twists of the structure sheaf.
* `Stacks.ProjectiveSpace.SerreVanishing.isZero_Hgroup_twistingSheaf_of_pos`: the higher
  cohomology of a nonnegative twist of the structure sheaf vanishes.
* `Stacks.ProjectiveSpace.SerreVanishing.moduleFinite_cohomology_of_isCoherent`: each
  `H^i(ℙⁿ_R, ℱ)` is a finite `R`-module.
* `Stacks.ProjectiveSpace.SerreVanishing.exists_isZero_Hgroup_twist_of_isCoherent`: the vanishing
  of the higher cohomology of the high twists.

## Implementation notes

`ℙⁿ_R` is `AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)`, the
source's own definition, and the `R`-module structure on the cohomology is the one the structure
morphism `Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff` induces, which is the structure
`Stacks.ProjectiveSpace.Cohomology.coeffScalar` carries.

The presentation as a quotient of twists is the source's own first assertion, and the vanishing
above degree `n` used below is its second. Neither carries a tag attribute here: both are already
attached, on the base-change model of projective space, to
`Stacks.ProjectiveSpace.exists_epi_biproduct_tensorPowModule` and to
`Stacks.ProjectiveSpace.Cohomology.isZero_cohomology_of_lt_zero_or_dim_lt`, and the two models of
`ℙⁿ_R` are not identified for a general coefficient ring, so a second attribute would put one tag
on two unidentified statements.

The last assertion of the tag — finiteness of the graded `R[T₀, …, Tₙ]`-module
`⨁_{d ≥ k} H⁰(ℙⁿ_R, ℱ(d))` — is proved not here but in
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/Cohomology/TwistSectionsDegreeOne.lean`, as
`Stacks.ProjectiveSpace.Cohomology.moduleFinite_truncation_of_isCoherent`, which carries the
attribute for it. Clause (4) below is one of its inputs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistFunctor
open Stacks.AlgebraicGeometry.ProjSerreDevissage
open Stacks.AlgebraicGeometry.ProjTwistPowers
  (exists_epi_coproduct_twistingSheaf_of_isCoherent_of_adjoin)
open Stacks.ProjectiveCohomology (polyGrading)
open Stacks.ProjectiveSpace.Cohomology (twistCohomology isZero_twistCohomology)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ProjectiveSpace.SerreVanishing

variable (R : Type u) [CommRing R] (n : ℕ)

/-- A polynomial ring is generated in degree one over its degree-zero part. -/
theorem adjoin_one_polyGrading :
    Algebra.adjoin (polyGrading R n 0)
      ((polyGrading R n 1 : Set (MvPolynomial (Fin (n + 1)) R))) = ⊤ :=
  MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) R

/-- The degree-one part of a polynomial ring is the range of its own inclusion. -/
theorem range_coe_polyGrading_one :
    (Set.range fun f : polyGrading R n 1 => (f : MvPolynomial (Fin (n + 1)) R))
      = (polyGrading R n 1 : Set (MvPolynomial (Fin (n + 1)) R)) :=
  Set.ext fun x => ⟨fun ⟨f, hf⟩ => hf ▸ f.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/-- A polynomial ring is generated in degree one over its degree-zero part, in the range
spelling. -/
theorem adjoin_range_one_polyGrading :
    Algebra.adjoin (polyGrading R n 0)
      (Set.range fun f : polyGrading R n 1 => (f : MvPolynomial (Fin (n + 1)) R)) = ⊤ := by
  rw [range_coe_polyGrading_one]
  exact adjoin_one_polyGrading R n

/-- The higher cohomology of a nonnegative twist of the structure sheaf of `ℙⁿ_R` vanishes:
`H^m(ℙⁿ_R, 𝒪(e)) = 0` for `m > 0` and `e ≥ 0`. -/
theorem isZero_Hgroup_twistingSheaf_of_pos (e : ℤ) (he : 0 ≤ e) (m : ℕ) (hm : 0 < m) :
    IsZero (Hgroup (projRingSheaf (polyGrading R n)) ⊤ m
      (twistingSheaf (polyGrading R n) e)) := by
  have h0 : IsZero (twistCohomology R n e m) :=
    isZero_twistCohomology R n e m (by
      rintro (⟨hm0, -⟩ | ⟨-, hlt⟩)
      · omega
      · omega)
  have h1 : IsZero (((Stacks.Cohomology.sectionsFunctor
      (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).rightDerived m).obj
      (twistingSheaf (polyGrading R n) e)) := by
    have hs : Subsingleton (twistCohomology R n e m) := ModuleCat.subsingleton_of_isZero h0
    rw [ModuleCat.isZero_iff_subsingleton]
    exact hs
  exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
    (projRingSheaf (polyGrading R n)) ⊤ m (twistingSheaf (polyGrading R n) e)).mp h1

/-- **Serre vanishing for the twisting sheaves of `ℙⁿ_R`.** For every `k` the higher cohomology
of `𝒪(k)(d)` vanishes once `d ≥ -k`, because `𝒪(k)(d) ≅ 𝒪(k + d)`. -/
theorem hasEventuallyAcyclicTwists_polyGrading :
    HasEventuallyAcyclicTwists (polyGrading R n) ⊤ := by
  intro k
  refine ⟨-k, fun d hd m hm => ?_⟩
  have hiso : twistSheafOfModules (polyGrading R n) (twistingSheaf (polyGrading R n) k) d ≅
      twistingSheaf (polyGrading R n) (k + d) :=
    @asIso _ _ _ _
      (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
        (polyGrading R n) k d)
      (Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin
        (polyGrading R n) (adjoin_one_polyGrading R n) k d)
  exact (isZero_Hgroup_twistingSheaf_of_pos R n (k + d) (by omega) m hm).of_iso
    ((Hfunctor (projRingSheaf (polyGrading R n)) ⊤ m).mapIso hiso)

/-- `𝒪(1)` is invertible on `ℙⁿ_R`, in the class the ampleness theory uses. -/
instance isInvertibleModule_twistingSheaf_one :
    Stacks.Ample.IsInvertibleModule
      (AlgebraicGeometry.Proj (polyGrading R n)) (twistingSheaf (polyGrading R n) 1) :=
  Stacks.AlgebraicGeometry.Tag0B5QAmpleRoute.isInvertibleModule_twistingSheaf_of_adjoin_degree_one
    (polyGrading R n) (adjoin_range_one_polyGrading R n) 1

/-- Every finite-type quasi-coherent module on `ℙⁿ_R` is a quotient of a finite direct sum of
negative tensor powers of the ample sheaf `𝒪(1)`. -/
theorem isQuotientOfNegativeTwists_twistingSheaf_one :
    Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists
      (AlgebraicGeometry.Proj (polyGrading R n)) (twistingSheaf (polyGrading R n) 1) :=
  Stacks.AmpleLocalGeneration.isQuotientOfNegativeTwists_of_isAmple
    (X := AlgebraicGeometry.Proj (polyGrading R n)) (twistingSheaf (polyGrading R n) 1)
    (Stacks.PowerFamilyBridge.isAmple_of_modulesIsAmple
      (AlgebraicGeometry.Proj (polyGrading R n)) (twistingSheaf (polyGrading R n) 1)
      (Stacks.ProjAmple.isAmple_twistingModule_one_polyGrading R n))

/-- **A coherent sheaf on `ℙⁿ_R` is a quotient of a finite direct sum of twists of the structure
sheaf**: there are `r ≥ 0`, integers `d₁, …, d_r` and an epimorphism
`⨁_{j} 𝒪(dⱼ) ⟶ ℱ`. The twisting sheaf `𝒪(1)` is ample on `ℙⁿ_R` and the tensor powers of `𝒪(1)`
are the twists `𝒪(d)`. -/
theorem exists_epi_coproduct_twistingSheaf
    (F : (AlgebraicGeometry.Proj (polyGrading R n)).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) :
    ∃ (r : ℕ) (d : Fin r → ℤ),
      ∃ φ : (∐ fun j : Fin r => twistingSheaf (polyGrading R n) (d j)) ⟶ F, Epi φ :=
  exists_epi_coproduct_twistingSheaf_of_isCoherent_of_adjoin (polyGrading R n)
    (adjoin_one_polyGrading R n) (isQuotientOfNegativeTwists_twistingSheaf_one R n) F hF

/-- The same presentation with the direct sum given by a bicone, which is the shape the dévissage
consumes. -/
theorem hasTwistQuotients_polyGrading : HasTwistQuotients (polyGrading R n) := by
  intro F hF
  obtain ⟨r, d, φ, hφ⟩ := exists_epi_coproduct_twistingSheaf R n F hF
  let _ : HasBiproduct (fun j : Fin r => twistingSheaf (polyGrading R n) (d j)) :=
    HasBiproduct.of_hasCoproduct _
  refine ⟨r, d, biproduct.bicone _, biproduct.isBilimit _,
    (biproduct.isoCoproduct _).hom ≫ φ, ?_⟩
  have := hφ
  exact epi_comp _ _

/-- The cohomology of a coherent sheaf on `ℙⁿ_R` vanishes above degree `n`, hence is a finite
`R`-module there. -/
theorem moduleFinite_cohomology_of_dim_lt
    (F : (AlgebraicGeometry.Proj (polyGrading R n)).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (q : ℕ) (hq : n < q) :
    Module.Finite R
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n).appTop).hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (AlgebraicGeometry.Proj (polyGrading R n))).rightDerived q).obj F)) := by
  have := hF
  have hqc : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hz := Stacks.ProjectiveCohomology.isZero_Hgroup_proj_of_lt R n F q hq
  have h1 : IsZero ((((_root_.SheafOfModules.evaluation
      (projRingSheaf (polyGrading R n)) (op ⊤)).rightDerived q).obj F)) :=
    (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      (projRingSheaf (polyGrading R n)) ⊤ q F).mpr hz
  exact Module.finite_of_isZero ((ModuleCat.restrictScalars _).map_isZero h1)

/-- The cohomology of a twist of the structure sheaf of `ℙⁿ_R` is a finite `R`-module, in every
degree and for every twist: this is the computation of [Stacks, Tag 01XT]. -/
theorem moduleFinite_cohomology_twistingSheaf (d : ℤ) (q : ℕ) :
    Module.Finite R
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n).appTop).hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections
            (AlgebraicGeometry.Proj (polyGrading R n))).rightDerived q).obj
          (twistingSheaf (polyGrading R n) d))) :=
  Stacks.ProjectiveSpace.Cohomology.moduleFinite_twistCohomology R n d q

/-- **[Stacks, Tag 01YS] clause (3).** Let `R` be a Noetherian ring, `n ≥ 0` and `ℱ` a coherent
sheaf on `ℙⁿ_R = Proj R[T₀, …, Tₙ]`. For every `i` the cohomology `H^i(ℙⁿ_R, ℱ)` is a finite
`R`-module.

The proof is the source's descending induction on `i`: it holds above degree `n` because the
cohomology vanishes there (clause (2)), the twists `𝒪(d)` have finite cohomology
([Stacks, Tag 01XT]), and `ℱ` is a quotient of a finite direct sum of twists (clause (1) of the
same tag), so the long exact sequence of the kernel sequence places `H^i(ℙⁿ_R, ℱ)` between two
finite modules over the Noetherian ring `R`. -/
@[stacks 01YS "(3) finiteness of the cohomology modules",
  ega "III 2.2.2" "clause (i), special case"]
theorem moduleFinite_cohomology_of_isCoherent [IsNoetherianRing R]
    (F : (AlgebraicGeometry.Proj (polyGrading R n)).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (q : ℕ) :
    Module.Finite R
      ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n).appTop).hom).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (AlgebraicGeometry.Proj (polyGrading R n))).rightDerived q).obj F)) :=
  AlgebraicGeometry.forall_moduleFinite_cohomology_ringBase_of_epi_coproduct_of_le R
    (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R n)
    (fun d : ℤ => twistingSheaf (polyGrading R n) d) (n + 1)
    (fun G hG p hp => moduleFinite_cohomology_of_dim_lt R n G hG p (by omega))
    (fun d => isCoherent_twistingSheaf_polyGrading R n d)
    (fun d p => moduleFinite_cohomology_twistingSheaf R n d p)
    (fun G hG => exists_epi_coproduct_twistingSheaf R n G hG) F hF q

/-- **[Stacks, Tag 01YS] clause (4).** Let `R` be a Noetherian ring, `n ≥ 0` and `ℱ` a coherent
sheaf on `ℙⁿ_R = Proj R[T₀, …, Tₙ]`. For every `i > 0` the cohomology `H^i(ℙⁿ_R, ℱ(d))` vanishes
for all `d` large enough.

The proof is the source's: `ℱ` is a quotient of a finite direct sum of twists
(`hasTwistQuotients_polyGrading`, clause (1) of the same tag), the twists are eventually acyclic
(`hasEventuallyAcyclicTwists_polyGrading`, from the computation of `H^i(ℙⁿ_R, 𝒪(d))` of
[Stacks, Tag 01XT]), and the dévissage descends on the cohomological degree from the degree above
which everything vanishes. -/
@[stacks 01YS "(4) eventual vanishing of the higher cohomology of the twists"]
theorem exists_isZero_Hgroup_twist_of_isCoherent [IsNoetherianRing R] (i : ℕ) (hi : 0 < i)
    (F : (AlgebraicGeometry.Proj (polyGrading R n)).Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projRingSheaf (polyGrading R n)) ⊤ i
        (twistSheafOfModules (polyGrading R n) F d)) :=
  exists_isZero_hgroup_twist_of_presentation_of_adjoin_degree_one (polyGrading R n)
    (adjoin_range_one_polyGrading R n)
    (hasCoherentTwistPresentation_of_hasTwistQuotients (polyGrading R n)
      (hasTwistQuotients_polyGrading R n) (isCoherent_twistingSheaf_polyGrading R n))
    (hasEventuallyAcyclicTwists_polyGrading R n) i hi F hF

end Stacks.ProjectiveSpace.SerreVanishing

end
