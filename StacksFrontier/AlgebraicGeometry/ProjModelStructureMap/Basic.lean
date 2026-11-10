module

public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.TwistCohomologyFiniteness.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-!
# The structure morphism of `Proj R[T₀, …, Tₙ]`, and the Čech finiteness machinery on that model

`AlgebraicGeometry.cohomologyOverField` is the cohomology of a module on a scheme *over a field*
`k`, and it needs a morphism to `Spec k` to say what the `k`-vector space structure is. Mathlib's
structure morphism of a projective spectrum, `AlgebraicGeometry.Proj.toSpecZero`, lands at `Spec`
of the degree-zero part of the grading, which for a polynomial ring is the ring of constants
rather than literally the coefficient ring. This file supplies the one `Spec.map` that closes
that gap and then carries the model-free Čech finiteness machinery of
`StacksFrontier/AlgebraicGeometry/TwistCohomologyFiniteness/Basic.lean` over to `Proj` of a
polynomial ring — the model on which the twisting sheaf `𝒪(d)` and the explicit Čech terms of
[Stacks, Tag 01XT] are described.

**Why this was the missing link.** The finiteness statements of that file are of two kinds. Some
are stated for an *arbitrary* scheme with an arbitrary morphism to `Spec k`, an arbitrary covering
with affine finite intersections and an arbitrary quasi-coherent module; those are
`AlgebraicGeometry.rightDerivedEvaluationCechHomologyIso` and
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_finiteDimensional_cechHomology`. The
rest are stated on `AlgebraicGeometry.projectiveSpaceOverRing`, because that is the model whose
structure morphism already goes to `Spec` of the coefficient ring. The model-free ones apply to
`AlgebraicGeometry.Proj` of a polynomial ring as soon as *some* morphism to `Spec k` exists, and
`Stacks.ProjectiveCohomology.projModelToSpec` below is that morphism. Everything after it is a
direct instantiation with no bridging lemma.

**The degree-zero identification is not new.** `Stacks.ProjectiveChart.degreeZeroEquiv` already
identifies the degree-zero part of the total-degree grading of a polynomial ring with the
coefficient ring, and `AlgebraicGeometry.ProjectiveSpace.gradeZeroEquiv` does the same in the
other direction at an arbitrary index type. What was absent was the *composite* as a
declaration: a morphism `Proj R[T₀, …, Tₙ] ⟶ Spec R`. The nearest thing in the development was a
local `let` and `have` inside the proof of
`AlgebraicGeometry.locallyOfFiniteType_terminal_from_projectiveSpaceAtUniverse`, which builds
exactly this composite for `R = ULift ℤ` and discards it.

## Main definitions

* `Stacks.ProjectiveCohomology.polyDegreeZeroHom`: the coefficient ring as the degree-zero part
  of the total-degree grading, as a map of `CommRingCat`.
* `Stacks.ProjectiveCohomology.projModelSpecZeroIso`: `Spec` of that degree-zero part is `Spec`
  of the coefficient ring.
* `Stacks.ProjectiveCohomology.projModelToSpec`: **the structure morphism
  `Proj R[T₀, …, Tₙ] ⟶ Spec R`.**
* `Stacks.ProjectiveCohomology.projModelRightDerivedCechIso`: the cohomology of a quasi-coherent
  module on `Proj R[T₀, …, Tₙ]` *is* the homology of the explicit Čech complex of the `n + 1`
  standard coordinate opens.

## Main results

The names in this list are relative to the `Stacks.ProjectiveCohomology` namespace where the
fully-qualified form would not fit on a line.

* `Stacks.ProjectiveCohomology.isProper_projModelToSpec`: **the structure morphism is proper**,
  for every commutative ring, and
  `AlgebraicGeometry.isProper_projectiveSpaceOver` (imported): so is the structure
  morphism of the library's model, over every base scheme.
* `finiteDimensional_cohomologyOverField_projModel_of_finiteDimensional_cechHomology`:
  **the Čech bridge on the `Proj` model** — finite dimensionality of the homology of the explicit
  Čech complex gives finite dimensionality of `Hᵖ`.
* `Stacks.ProjectiveCohomology.forall_finiteDimensional_cohomologyOverField_projModel_of_le`:
  on `Proj R[T₀, …, Tₙ]` over a field the degrees `0, …, n` decide every degree.
* `forall_finiteDimensional_cohomologyOverField_projModel_of_cechHomology`:
  the two combined — finite dimensionality of the explicit Čech homology in degrees `≤ n` gives
  finite dimensionality of the cohomology in every degree.
* `forall_finiteDimensional_cohomologyOverField_twistingSheaf_of_cechHomology`:
  **the statement a computation with the weight-split Čech complex has to discharge**, for the
  twisting sheaf `𝒪(d)` itself.
* `forall_finiteDimensional_cohomologyOverField_projModel_of_epi_biprodPow`:
  the dévissage of [Stacks, Tag 02O6] over a field, on the `Proj` model, with no properness
  hypothesis and no vanishing-degree hypothesis.

## Implementation notes

**No tag attribute is attached to anything here, and this file proves no tag.** Every projective
statement below carries the Čech computation of [Stacks, Tag 01XT] as an explicit hypothesis, and
the assembly carries the quotient-of-twists clause of [Stacks, Tag 01YS] as `hgen`; neither is in
the development. The vanishing used is the `Proj`-model counterpart
`Stacks.ProjectiveCohomology.isZero_Hgroup_proj_of_lt`, which itself deliberately carries no
attribute because the tag sits on the library-model statement. The finiteness statements below
are the `Proj`-model counterparts of the ones in
`StacksFrontier/AlgebraicGeometry/TwistCohomologyFiniteness/Basic.lean`, and the two models are
identified only over the integers, so attaching the same tag to both would put one tag on two
unidentified constants.

**Properness is a question of import closure.** Mathlib's
`IsProper (AlgebraicGeometry.Proj.toSpecZero 𝒜)` requires an
`Algebra.FiniteType (𝒜 0) A` instance. That instance *is*
available in this development, twice over — `MvPolynomial.finiteType_of_homogeneousSubmodule_zero`
and an anonymous sibling in `StacksFrontier/AlgebraicGeometry/Limits/ProjectiveSpace.lean` — so
instance search succeeds at the import surface of
`StacksFrontier/AlgebraicGeometry/ProjectiveCohomology/ModelComparison.lean` and fails at the
import surface of `TwistCohomologyFiniteness/Basic.lean`, where the failure is real
and its cause is an absent import, not absent mathematics. Nothing below *uses* properness: the
Čech route needs none, which is why the statements here carry no properness hypothesis.

**For the library's model it is an instance, at the other of two `rfl`-equal
spellings.** `AlgebraicGeometry.ProjectiveSpace` and `AlgebraicGeometry.projectiveSpaceOver` are
the same pullback of two `rfl`-equal spellings of the integral model, and
`StacksFrontier/AlgebraicGeometry/Limits/ProjectiveSpace.lean` registers
`IsProper (ProjectiveSpace n S ↘ S)` as an instance. Indeed
`IsProper (ProjectiveSpace n S ↘ S)` is `inferInstance` and
`IsProper (projectiveSpaceOver n S ↘ S)` is `synthInstanceFailed`, because two `def`-level
`rfl`-equal spellings are different inputs to instance search. Every cohomological statement in
this development is phrased at the second spelling, which is why instance search does not find the
properness there. `AlgebraicGeometry.isProper_projectiveSpaceOver` (in
`StacksFrontier/AlgebraicGeometry/Morphisms/Proper/Projective.lean`) is at that spelling.

**`_root_.SheafOfModules.IsCoherent` is written out.** Inside a namespace beginning `Stacks`, the
relative name `SheafOfModules.IsCoherent` resolves to `Stacks.SheafOfModules.IsCoherent`, which
is a *different constant* from the one the assembly being instantiated consumes. Writing the
relative name compiles the statement about the wrong constant; here it was caught because the
dévissage below feeds its hypotheses straight into that assembly with no bridging lemma, so the
mismatch became a type error instead of a silent success.

**`_root_.SheafOfModules.evaluation` is written out** for the same kind of reason: under
`open AlgebraicGeometry` the relative name resolves to a homonym valued in `CommRingCat`, with
the error appearing at the use site and not at the binder.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01WC](https://stacks.math.columbia.edu/tag/01WC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ProjectiveCohomology

/-! ### The structure morphism of `Proj R[T₀, …, Tₙ]` -/

variable (R : Type u) [CommRing R]

/-- The coefficient ring of a polynomial ring, viewed inside the degree-zero part of its
total-degree grading: the inverse of `Stacks.ProjectiveChart.degreeZeroEquiv`, which says that a
polynomial homogeneous of degree zero is a constant. -/
def polyDegreeZeroHom (n : ℕ) :
    CommRingCat.of R ⟶ CommRingCat.of (polyGrading R n 0) :=
  CommRingCat.ofHom (Stacks.ProjectiveChart.degreeZeroEquiv R n).symm.toRingHom

/-- The inclusion of the coefficient ring into the degree-zero part of `R[T₀, …, Tₙ]` is an
isomorphism. -/
instance isIso_polyDegreeZeroHom (n : ℕ) : IsIso (polyDegreeZeroHom R n) :=
  ((Stacks.ProjectiveChart.degreeZeroEquiv R n).symm.toCommRingCatIso).isIso_hom

/-- `Spec` of the degree-zero part of `R[T₀, …, Tₙ]` is `Spec R`. This is the identification that
turns `AlgebraicGeometry.Proj.toSpecZero`, which lands at the constants, into a morphism to the
spectrum of the coefficient ring. -/
def projModelSpecZeroIso (n : ℕ) :
    Spec (CommRingCat.of (polyGrading R n 0)) ≅ Spec (CommRingCat.of R) :=
  asIso (Spec.map (polyDegreeZeroHom R n))

/-- **The structure morphism `Proj R[T₀, …, Tₙ] ⟶ Spec R`**: Mathlib's morphism to the spectrum
of the degree-zero part, followed by the identification of that part with the coefficient ring.

This is the datum the model-free Čech finiteness machinery needs in order to apply to this model
of projective space, `AlgebraicGeometry.cohomologyOverField` being defined only relative to a
morphism to the spectrum of the coefficient field. -/
def projModelToSpec (n : ℕ) :
    AlgebraicGeometry.Proj (polyGrading R n) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (polyGrading R n) ≫ Spec.map (polyDegreeZeroHom R n)

/-- The structure morphism `Proj R[T₀, …, Tₙ] ⟶ Spec R` is `AlgebraicGeometry.Proj.toSpecZero`
followed by `Spec` of `Stacks.ProjectiveCohomology.polyDegreeZeroHom`. -/
theorem projModelToSpec_eq (n : ℕ) :
    projModelToSpec R n =
      Proj.toSpecZero (polyGrading R n) ≫ Spec.map (polyDegreeZeroHom R n) := rfl

/-- The structure morphism factors the degree-zero identification: composing
`AlgebraicGeometry.Proj.toSpecZero` with
`Stacks.ProjectiveCohomology.projModelSpecZeroIso` gives it. -/
theorem toSpecZero_comp_projModelSpecZeroIso (n : ℕ) :
    Proj.toSpecZero (polyGrading R n) ≫ (projModelSpecZeroIso R n).hom =
      projModelToSpec R n := rfl

/-- **The structure morphism of `Proj R[T₀, …, Tₙ]` is proper**, for every commutative ring `R`.
`AlgebraicGeometry.Proj.toSpecZero` is proper because a polynomial ring in finitely many
variables is of finite type over the degree-zero part of its total-degree grading, and the
remaining factor is an isomorphism. -/
instance isProper_projModelToSpec (n : ℕ) : IsProper (projModelToSpec R n) := by
  rw [projModelToSpec_eq, MorphismProperty.cancel_right_of_respectsIso (P := @IsProper)]
  infer_instance

end Stacks.ProjectiveCohomology

namespace AlgebraicGeometry

/-- **The integral model of projective space is proper over the terminal scheme**, registered as
an instance so that the base-change instances of `AlgebraicGeometry.IsProper` fire on the
library's model. The statement is `AlgebraicGeometry.ProjectiveSpace.isProper_terminal_from`,
which is phrased at `AlgebraicGeometry.ProjectiveSpace.ProjectiveSpaceZ`; the two models of the
integral projective space are the same term. -/
instance isProper_terminal_from_projectiveSpaceAtUniverse (n : ℕ) :
    IsProper (terminal.from (projectiveSpaceAtUniverse.{u} n)) :=
  AlgebraicGeometry.ProjectiveSpace.isProper_terminal_from.{u} n

end AlgebraicGeometry

namespace Stacks.ProjectiveCohomology

variable (R : Type u) [CommRing R]

/-! ### The model-free Čech machinery, at the `Proj` model -/

/-- **The cohomology of a quasi-coherent module on `Proj R[T₀, …, Tₙ]` is the homology of the
explicit Čech complex of the `n + 1` standard coordinate opens** — as an isomorphism, in every
degree, over every coefficient ring and for every quasi-coherent module.

This is `AlgebraicGeometry.rightDerivedEvaluationCechHomologyIso` instantiated at this model,
the two hypotheses being that the standard coordinate opens cover and that their finite
intersections are affine. No morphism to a base and no field appear. -/
def projModelRightDerivedCechIso (n : ℕ)
    (F : (AlgebraicGeometry.Proj (polyGrading R n)).Modules) [F.IsQuasicoherent] (p : ℕ) :
    ((_root_.SheafOfModules.evaluation.{u}
        (AlgebraicGeometry.Proj (polyGrading R n)).ringCatSheaf
        (op (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens))).rightDerived p).obj F ≅
      (cechComplex.{u, u, u, u} (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
        (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm F).homology p :=
  rightDerivedEvaluationCechHomologyIso (AlgebraicGeometry.Proj (polyGrading R n)) ⊤
    (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (fun r s => isAffineOpen_iInf_basicOpenXAtUniverse R n r s) F p

/-- **The Čech bridge on the `Proj` model.** If the `p`-th homology of the explicit Čech complex
of the `n + 1` standard coordinate opens is a finite-dimensional `k`-vector space, so is
`Hᵖ(Proj k[T₀, …, Tₙ], ℱ)`.

This is `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_finiteDimensional_cechHomology`
with `Stacks.ProjectiveCohomology.projModelToSpec` in its morphism slot and the standard
coordinate opens in its covering slot. -/
theorem finiteDimensional_cohomologyOverField_projModel_of_finiteDimensional_cechHomology
    (k : Type u) [Field k] (n : ℕ)
    (F : (AlgebraicGeometry.Proj (polyGrading k n)).Modules) [F.IsQuasicoherent] (p : ℕ)
    (hfd : FiniteDimensional k
      ((ModuleCat.restrictScalars
        (cohomologyOverFieldSectionRingHom k (projModelToSpec k n))).obj
        ((cechComplex.{u, u, u, u} (⊤ : (AlgebraicGeometry.Proj (polyGrading k n)).Opens)
          (basicOpenXAtUniverse k n) (iSup_basicOpenXAtUniverse_eq_top k n).symm
          F).homology p))) :
    FiniteDimensional k (cohomologyOverField k (projModelToSpec k n) F p) :=
  finiteDimensional_cohomologyOverField_of_finiteDimensional_cechHomology k
    (projModelToSpec k n) (basicOpenXAtUniverse k n)
    (iSup_basicOpenXAtUniverse_eq_top k n).symm
    (fun r s => isAffineOpen_iInf_basicOpenXAtUniverse k n r s) F p hfd

/-- **On `Proj k[T₀, …, Tₙ]` the degrees `0, …, n` decide every degree.** For a quasi-coherent
module whose cohomology is a finite-dimensional `k`-vector space in each of the `n + 1` lowest
degrees, it is finite-dimensional in all of them: above degree `n` it vanishes, by the
`Proj`-model vanishing `Stacks.ProjectiveCohomology.isZero_Hgroup_proj_of_lt`. -/
theorem forall_finiteDimensional_cohomologyOverField_projModel_of_le
    (k : Type u) [Field k] (n : ℕ)
    (F : (AlgebraicGeometry.Proj (polyGrading k n)).Modules) [F.IsQuasicoherent]
    (hle : ∀ q ≤ n, FiniteDimensional k (cohomologyOverField k (projModelToSpec k n) F q)) :
    ∀ q : ℕ, FiniteDimensional k (cohomologyOverField k (projModelToSpec k n) F q) :=
  forall_finiteDimensional_cohomologyOverField_of_le_of_isZero_Hgroup_of_lt k
    (projModelToSpec k n) F n hle fun q hq => isZero_Hgroup_proj_of_lt k n F q hq

/-- **The explicit Čech complex in degrees `≤ n` decides every degree.** The hypothesis mentions
no derived category, no higher direct image and no sheaf cohomology: it is a statement about the
homology of an explicit complex of modules of sections over intersections of the standard
coordinate opens of `Proj k[T₀, …, Tₙ]`, in the `n + 1` degrees in which it has content. -/
theorem forall_finiteDimensional_cohomologyOverField_projModel_of_cechHomology
    (k : Type u) [Field k] (n : ℕ)
    (F : (AlgebraicGeometry.Proj (polyGrading k n)).Modules) [F.IsQuasicoherent]
    (hfd : ∀ q ≤ n, FiniteDimensional k
      ((ModuleCat.restrictScalars
        (cohomologyOverFieldSectionRingHom k (projModelToSpec k n))).obj
        ((cechComplex.{u, u, u, u} (⊤ : (AlgebraicGeometry.Proj (polyGrading k n)).Opens)
          (basicOpenXAtUniverse k n) (iSup_basicOpenXAtUniverse_eq_top k n).symm
          F).homology q))) :
    ∀ q : ℕ, FiniteDimensional k (cohomologyOverField k (projModelToSpec k n) F q) :=
  forall_finiteDimensional_cohomologyOverField_projModel_of_le k n F fun q hq =>
    finiteDimensional_cohomologyOverField_projModel_of_finiteDimensional_cechHomology
      k n F q (hfd q hq)

/-- **The statement a computation with the weight-split Čech complex has to discharge.** For the
twisting sheaf `𝒪(d)` on `Proj k[T₀, …, Tₙ]`, finite dimensionality of the homology of the
explicit Čech complex of the standard coordinate opens in the degrees `0, …, n` gives finite
dimensionality of `Hᵖ(ℙⁿ_k, 𝒪(d))` in *every* degree.

Every term of that complex is identified — as a free module on the Laurent monomials of total
degree `d` that are nonnegative on the coordinates that were not inverted, and the complex is
split along that weight — so this is the form in which the content of [Stacks, Tag 01XT] pays out
as a statement about cohomology. Quasi-coherence of the twisting sheaf is supplied
positionally rather than by instance search, as elsewhere on this import surface. -/
theorem forall_finiteDimensional_cohomologyOverField_twistingSheaf_of_cechHomology
    (k : Type u) [Field k] (n : ℕ) (d : ℤ)
    (hfd : ∀ q ≤ n, FiniteDimensional k
      ((ModuleCat.restrictScalars
        (cohomologyOverFieldSectionRingHom k (projModelToSpec k n))).obj
        ((cechComplex.{u, u, u, u} (⊤ : (AlgebraicGeometry.Proj (polyGrading k n)).Opens)
          (basicOpenXAtUniverse k n) (iSup_basicOpenXAtUniverse_eq_top k n).symm
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d)).homology q))) :
    ∀ q : ℕ, FiniteDimensional k (cohomologyOverField k (projModelToSpec k n)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d) q) :=
  @forall_finiteDimensional_cohomologyOverField_projModel_of_cechHomology k _ n
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d)
    (isQuasicoherent_twistingSheaf k n d) hfd

/-! ### The dévissage of [Stacks, Tag 02O6] on the `Proj` model -/

/-- **[Stacks, Tag 02O6] over a field on `Proj k[T₀, …, Tₙ]`, with no properness hypothesis and
no vanishing-degree hypothesis.** Let `𝒯` be a family of coherent modules on
`Proj k[T₀, …, Tₙ]` such that the cohomology of each member is a finite-dimensional `k`-vector
space in each of the degrees `0, …, n`, and such that every coherent module is a quotient of a
power of a member. Then the cohomology of *every* coherent module is a finite-dimensional
`k`-vector space in every degree.

This is the `Proj`-model counterpart of
`AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_projectiveSpace_of_epi_biprodPow`,
and it is the model on which `𝒯` can actually be exhibited: the twists `𝒪(-d)` live here. The
vanishing degree is `n + 1`, by the `Proj`-model vanishing applied to a coherent — hence
quasi-coherent — module, so properness of the structure morphism is not used even though it is
now available. -/
theorem forall_finiteDimensional_cohomologyOverField_projModel_of_epi_biprodPow
    (k : Type u) [Field k] (n : ℕ)
    (T : ℕ → (AlgebraicGeometry.Proj (polyGrading k n)).Modules)
    (hTcoh : ∀ d : ℕ, _root_.SheafOfModules.IsCoherent (T d))
    (hTle : ∀ (d : ℕ), ∀ q ≤ n,
      FiniteDimensional k (cohomologyOverField k (projModelToSpec k n) (T d) q))
    (hgen : ∀ G : (AlgebraicGeometry.Proj (polyGrading k n)).Modules,
      _root_.SheafOfModules.IsCoherent G →
      ∃ d r : ℕ, ∃ φ : (T d).biprodPow r ⟶ G, Epi φ) :
    ∀ G : (AlgebraicGeometry.Proj (polyGrading k n)).Modules,
      _root_.SheafOfModules.IsCoherent G →
      ∀ q : ℕ, FiniteDimensional k (cohomologyOverField k (projModelToSpec k n) G q) := by
  have hTq : ∀ d : ℕ, (T d).IsQuasicoherent :=
    fun d => @_root_.isQuasicoherent_of_isCoherent _ _ _ (T d) (hTcoh d)
  refine forall_finiteDimensional_cohomologyOverField_of_epi_biprodPow_of_le_of_isZero_Hgroup
    k (projModelToSpec k n) T (n + 1) (fun G hG q hq => ?_) hTcoh (fun d q _ => ?_)
    (fun d q hq => ?_) hgen
  · have hGq := @_root_.isQuasicoherent_of_isCoherent _ _ _ G hG
    exact finiteDimensional_cohomologyOverField_of_isZero_Hgroup k (projModelToSpec k n) G q
      (@isZero_Hgroup_proj_of_lt k _ n G hGq q (by omega))
  · rcases le_or_gt q n with h | h
    · exact hTle d q h
    · exact finiteDimensional_cohomologyOverField_of_isZero_Hgroup k (projModelToSpec k n)
        (T d) q (@isZero_Hgroup_proj_of_lt k _ n (T d) (hTq d) q h)
  · exact @isZero_Hgroup_proj_of_lt k _ n (T d) (hTq d) q (by omega)

end Stacks.ProjectiveCohomology

end
