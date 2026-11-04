module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreComputation

/-!
# The two spellings of the coefficient scalars on `ℙⁿ_R`

The cohomology of a module on `ℙⁿ_R = Proj R[T₀, …, Tₙ]` is read as an `R`-module in two ways in
this repository. Serre's computation uses
`Stacks.ProjectiveSpace.Cohomology.coeffScalar`, the ring homomorphism
`R → Γ(ℙⁿ_R, 𝒪)` with its target spelled as the ring of sections of the sheaf of rings that the
twisting sheaves are modules over; the general theory of a scheme over a base uses
`(Γ(Spec R) ≅ R)⁻¹` composed with the map on global sections of the structure morphism
`ℙⁿ_R ⟶ Spec R`. This file records that the two homomorphisms are equal — the first is by
definition the second — and transports a `Γ(ℙⁿ_R, 𝒪)`-linear isomorphism of cohomology modules
to an `R`-linear one, so that `Module.finrank` over the base travels along it.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.ΓSpecIso_inv_comp_appTop_hom_eq_coeffScalar` and
  `Stacks.ProjectiveSpace.Cohomology.ΓSpecIso_inv_comp_appLE_hom_eq_coeffScalar`: the scalar of
  the structure morphism is `Stacks.ProjectiveSpace.Cohomology.coeffScalar`, in the `appTop` and
  the `appLE ⊤ ⊤` spellings.
* `Stacks.ProjectiveSpace.Cohomology.cohomologyOverFieldIsoRestrictScalarsCoeffScalar`: the
  cohomology over the ground field of a module on `ℙⁿ_k` is its cohomology with scalars restricted
  along `coeffScalar`.
* `Stacks.ProjectiveSpace.Cohomology.structureSheafCohomologyIsoTwistCohomology` and
  `Stacks.ProjectiveSpace.Cohomology.finrank_structureSheafCohomology_eq_finrank_twistCohomology`:
  **a `Γ(ℙⁿ_k, 𝒪)`-linear isomorphism of `H^q(ℙⁿ_k, 𝒪)` with `H^q(ℙⁿ_k, 𝒪(d))` is `k`-linear**,
  and the two have the same dimension over `k`.

## References

* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ProjectiveSpace.Cohomology

/-! ### The scalar of the structure morphism is `coeffScalar` -/

/-- **The coefficient scalars of Serre's computation are the scalars of the structure
morphism.** `Stacks.ProjectiveSpace.Cohomology.coeffScalar` is, by definition, the global
sections of `ℙⁿ_R ⟶ Spec R` read through the identification of `R` with `Γ(Spec R, ⊤)`; the only
difference is that its target is spelled as the ring of sections of the sheaf of rings
`Stacks.ProjectiveSpace.Cohomology.projRingSheaf`. -/
theorem ΓSpecIso_inv_comp_appTop_hom_eq_coeffScalar (R : Type u) [CommRing R] (n : ℕ) :
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (projToSpecCoeff R n).appTop).hom =
      coeffScalar R n :=
  rfl

/-- **The coefficient scalars of Serre's computation are the scalars of the structure
morphism**, in the `AlgebraicGeometry.Scheme.Hom.appLE` spelling at the top opens used by
`AlgebraicGeometry.cohomologyOverField`. -/
theorem ΓSpecIso_inv_comp_appLE_hom_eq_coeffScalar (R : Type u) [CommRing R] (n : ℕ) :
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (projToSpecCoeff R n).appLE ⊤ ⊤ (by simp)).hom =
      coeffScalar R n := by
  have happ : (projToSpecCoeff R n).appTop = (projToSpecCoeff R n).appLE ⊤ ⊤ (by simp) := by
    simpa [Scheme.Hom.appTop] using
      (Scheme.Hom.app_eq_appLE (f := projToSpecCoeff R n)
        (U := (⊤ : (Spec (CommRingCat.of R)).Opens)))
  refine Eq.trans ?_ (ΓSpecIso_inv_comp_appTop_hom_eq_coeffScalar R n)
  exact congrArg CommRingCat.Hom.hom
    (congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g) happ.symm)

/-- **Restriction of scalars along the structure morphism of `ℙⁿ_R` is restriction along
`Stacks.ProjectiveSpace.Cohomology.coeffScalar`.** -/
def restrictScalarsAppLEIsoCoeffScalar (R : Type u) [CommRing R] (n : ℕ) :
    ModuleCat.restrictScalars.{u}
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          (projToSpecCoeff R n).appLE ⊤ ⊤ (by simp)).hom ≅
      ModuleCat.restrictScalars.{u} (coeffScalar R n) :=
  ModuleCat.restrictScalarsCongr (ΓSpecIso_inv_comp_appLE_hom_eq_coeffScalar R n)

/-! ### Transporting a `Γ`-linear isomorphism of cohomology to the base field -/

variable (k : Type u) [Field k] (n : ℕ)

/-- **The cohomology over the ground field of a module on `ℙⁿ_k` is its cohomology with scalars
restricted along `Stacks.ProjectiveSpace.Cohomology.coeffScalar`**, which is the module structure
that Serre's computation of the cohomology of the twists is stated in. -/
def cohomologyOverFieldIsoRestrictScalarsCoeffScalar
    (F : (AlgebraicGeometry.Proj (polyGrading k n)).Modules) (q : ℕ) :
    cohomologyOverField k (projToSpecCoeff k n) F q ≅
      (ModuleCat.restrictScalars.{u} (coeffScalar k n)).obj
        (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading k n))
          ⊤).rightDerived q).obj F) :=
  (restrictScalarsAppLEIsoCoeffScalar k n).app _

/-- **A `Γ(ℙⁿ_k, 𝒪)`-linear isomorphism of `H^q(ℙⁿ_k, 𝒪)` with `H^q(ℙⁿ_k, 𝒪(d))` is `k`-linear.**
The left-hand side is the cohomology of the structure sheaf in the spelling the genus is defined
from, the right-hand side is the `k`-module of Serre's computation. -/
def structureSheafCohomologyIsoTwistCohomology (d : ℤ) (q : ℕ)
    (e : ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading k n))
            ⊤).rightDerived q).obj
          (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf) ≅
        ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading k n))
            ⊤).rightDerived q).obj
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d)) :
    structureSheafCohomology (projToSpecCoeff k n) q ≅ twistCohomology k n d q :=
  structureSheafCohomologyIsoCohomologyOverField k (projToSpecCoeff k n) q ≪≫
    cohomologyOverFieldIsoRestrictScalarsCoeffScalar k n _ q ≪≫
      (ModuleCat.restrictScalars.{u} (coeffScalar k n)).mapIso e

/-- **An isomorphism `𝒪 ≅ 𝒪(d)` of sheaves of modules on `ℙⁿ_k` identifies the cohomology of the
structure sheaf with the `k`-module of Serre's computation.** -/
def structureSheafCohomologyIsoTwistCohomologyOfSheafIso (d : ℤ) (q : ℕ)
    (e : SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf ≅
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d) :
    structureSheafCohomology (projToSpecCoeff k n) q ≅ twistCohomology k n d q :=
  structureSheafCohomologyIsoTwistCohomology k n d q
    (((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading k n))
      ⊤).rightDerived q).mapIso e)

/-- **The dimension over `k` of `H^q(ℙⁿ_k, 𝒪)` is that of `H^q(ℙⁿ_k, 𝒪(d))`**, given a
`Γ(ℙⁿ_k, 𝒪)`-linear isomorphism of the two. -/
theorem finrank_structureSheafCohomology_eq_finrank_twistCohomology (d : ℤ) (q : ℕ)
    (e : ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading k n))
            ⊤).rightDerived q).obj
          (SheafOfModules.unit (AlgebraicGeometry.Proj (polyGrading k n)).ringCatSheaf) ≅
        ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading k n))
            ⊤).rightDerived q).obj
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d)) :
    Module.finrank k (structureSheafCohomology (projToSpecCoeff k n) q) =
      Module.finrank k (twistCohomology k n d q) :=
  (structureSheafCohomologyIsoTwistCohomology k n d q e).toLinearEquiv.finrank_eq

end Stacks.ProjectiveSpace.Cohomology

end
