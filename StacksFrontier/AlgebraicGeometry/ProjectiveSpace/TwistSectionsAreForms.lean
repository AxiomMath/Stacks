module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.DegreeSectionSurjective
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistMonomialBasis
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.Basic
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Every section of `𝒪(d)` on projective space is a form of degree `d`

Let `R` be a commutative ring and `d ≥ 0`. The canonical map
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` sends a homogeneous polynomial of
degree `d` in `T₀, …, Tₙ` to a global section of `𝒪(d)` on `ℙⁿ_R = Proj R[T₀, …, Tₙ]`. This
file proves that map is bijective: the degree-`d` forms *exhaust* `Γ(ℙⁿ_R, 𝒪(d))`.

Injectivity is the saturation criterion
`AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_eq_zero_of_degreeSection_eq_zero`
together with the regularity of a power of a variable in a polynomial ring. Surjectivity is
`Stacks.ProjectiveSpace.Cohomology.exists_degreeSection_eq_of_commRing`, the degree-zero
computation of [Stacks, Tag 01XT] carried out on sections: a global section has one monomial
expansion in every chart `D₊(Tᵢ)`, and being regular on all of them it has no negative exponent,
so it is a form.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.injective_degreeSectionLinear`: the degree-`d` section map
  is injective.
* `Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear`: the degree-`d` section map as an
  `R`-linear map into the sections of `𝒪(d)`, the coefficients acting through the structure
  morphism `ℙⁿ_R ⟶ Spec R`.
* `Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection`: **the degree-`d` forms exhaust
  `Γ(ℙⁿ_R, 𝒪(d))`**, and nothing else maps to a given section.
* `Stacks.ProjectiveSpace.Cohomology.exists_degreeSection_eq`: the surjectivity half, in the
  form its consumers use.

## Implementation notes

The `R`-module structure on the sections that [Stacks, Tag 01XT] is stated in is restriction of
scalars along `Stacks.ProjectiveSpace.Cohomology.coeffScalar`, the coefficients read as global
functions. So the content of `degreeSectionLinear` is that `degreeSection` is linear for *that*
action, which is `coeffScalar_smul_apply`: a section is a family of fractions indexed by the
points, the action of a global function is multiplication by its value, and the value of
`coeffScalar R n r` at every point is `C r / 1`.

`homogeneousIsoTwistSections` is the abstract isomorphism of the degree-zero row of
[Stacks, Tag 01XT]. It is recorded here because it is the cohomological form of the same
statement, but it is *not* what makes `degreeSection` bijective: it carries no information about
which map realises it.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ProjectiveSpace.Cohomology

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The sections of a twist as a module over the coefficients -/

/-- The global sections of `𝒪(d)` on `ℙⁿ_R`, as an `R`-module through the structure morphism
`ℙⁿ_R ⟶ Spec R`. This is the target of the degree-zero row of [Stacks, Tag 01XT] once the
derived functor is evaluated. -/
abbrev twistSectionsModule (d : ℤ) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars.{u} (coeffScalar R n)).obj
    ((Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n)) ⊤).obj
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d))

/-- **The degree-`d` forms are `Γ(ℙⁿ_R, 𝒪(d))` as `R`-modules**, for `d ≥ 0`: the degree-zero
row of [Stacks, Tag 01XT] with its cohomological side replaced by the honest module of
sections. -/
def homogeneousIsoTwistSections (d : ℕ) :
    ModuleCat.of R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) ≅
      twistSectionsModule R n (d : ℤ) :=
  (twistCohomologyIsoHomogeneous R n (d : ℤ) (Int.natCast_nonneg d)).symm ≪≫
    twistCohomologyZeroIsoSections R n (d : ℤ)

/-! ### The section map is linear over the coefficients -/

/-- The value at a point of the global function attached to a coefficient is the constant
fraction `C r / 1`. -/
theorem coeffScalar_val (r : R)
    (x : (⊤ : Opens (ProjectiveSpectrum.top (polyGrading R n)))) :
    HomogeneousLocalization.val ((coeffScalar R n r).1 x)
      = algebraMap (MvPolynomial (Fin (n + 1)) R)
          (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl) (MvPolynomial.C r) :=
  Stacks.AlgebraicGeometry.ProjEulerSequence.projToSpecCoeff_appTop_val R n r x.1

/-- The global section of `𝒪(d)` attached to a degree-`d` form, read in the `R`-module
`Stacks.ProjectiveSpace.Cohomology.twistSectionsModule`. -/
abbrev degreeSectionCoeff (d : ℕ)
    (a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) :
    twistSectionsModule R n (d : ℤ) :=
  degreeSection (polyGrading R n) d a

/-- **The degree-`d` section map is linear over the coefficients.** -/
theorem degreeSection_smul (d : ℕ) (r : R)
    (a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) :
    r • degreeSectionCoeff R n d a = degreeSectionCoeff R n d (r • a) := by
  refine Subtype.ext (funext fun x => ?_)
  show HomogeneousLocalization.val ((coeffScalar R n r).1 x) •
      LocalizedModule.mk (a : MvPolynomial (Fin (n + 1)) R)
        (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
    = LocalizedModule.mk
        ((r • a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) :
          MvPolynomial (Fin (n + 1)) R)
        (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  have hval : HomogeneousLocalization.val ((coeffScalar R n r).1 x)
      = Localization.mk (MvPolynomial.C r)
          (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
    (coeffScalar_val R n r ⟨x.1, trivial⟩).trans
      (Localization.mk_one_eq_algebraMap (MvPolynomial.C r)).symm
  rw [hval, LocalizedModule.mk_smul_mk, one_mul, Submodule.coe_smul,
    MvPolynomial.smul_eq_C_mul, smul_eq_mul]

/-- The degree-`d` section map is additive. -/
theorem degreeSection_add (d : ℕ)
    (a b : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) :
    degreeSectionCoeff R n d (a + b)
      = degreeSectionCoeff R n d a + degreeSectionCoeff R n d b := by
  refine Subtype.ext (funext fun x => ?_)
  show LocalizedModule.mk
        ((a + b : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) :
          MvPolynomial (Fin (n + 1)) R)
        (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
      = LocalizedModule.mk (a : MvPolynomial (Fin (n + 1)) R)
          (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
        + LocalizedModule.mk (b : MvPolynomial (Fin (n + 1)) R)
          (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  rw [LocalizedModule.mk_add_mk, one_smul, one_smul, one_mul, Submodule.coe_add]

/-- **The degree-`d` section map as a map of `R`-modules.** It sends a homogeneous polynomial
of degree `d` in `T₀, …, Tₙ` to the global section of `𝒪(d)` on `ℙⁿ_R` whose value at every
point is the fraction `a / 1`; the coefficients act on the sections through the structure
morphism `ℙⁿ_R ⟶ Spec R`. -/
def degreeSectionLinear (d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d →ₗ[R]
      twistSectionsModule R n (d : ℤ) where
  toFun := degreeSectionCoeff R n d
  map_add' := degreeSection_add R n d
  map_smul' r a := (degreeSection_smul R n d r a).symm

/-- The map `degreeSectionLinear` sends a form `a` of degree `d` to `degreeSection` of `a` for the
polynomial grading. -/
@[simp] theorem degreeSectionLinear_apply (d : ℕ)
    (a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d) :
    degreeSectionLinear R n d a = degreeSection (polyGrading R n) d a := rfl

/-! ### Injectivity -/

/-- **A nonzero form of degree `d` has a nonzero section**, over an arbitrary commutative ring. A
vanishing section means a power of `T₀` kills the form, and a power of a variable is a regular
element of a polynomial ring: multiplying by it shifts exponent vectors, so it does not collapse
coefficients. -/
theorem injective_degreeSectionLinear {A : Type u} [CommRing A] (n d : ℕ) :
    Function.Injective (degreeSectionLinear A n d) := by
  refine (injective_iff_map_eq_zero (degreeSectionLinear A n d)).mpr fun c hc => ?_
  obtain ⟨m, hm⟩ := exists_pow_mul_eq_zero_of_degreeSection_eq_zero (polyGrading A n) c hc
    (Stacks.AlgebraicGeometry.ProjPolyChart.X_mem_one A n 0)
  exact Subtype.ext
    ((MvPolynomial.isRegular_X_pow m).left (hm.trans (mul_zero ((MvPolynomial.X 0) ^ m)).symm))

/-! ### The forms exhaust the sections -/

/-- **The degree-`d` forms exhaust `Γ(ℙⁿ_A, 𝒪(d))`**, over an arbitrary commutative ring `A` and
for `d ≥ 0`: the canonical map from the degree-`d` homogeneous polynomials in `T₀, …, Tₙ` to the
global sections of `𝒪(d)` on `ℙⁿ_A = Proj A[T₀, …, Tₙ]` is bijective.

Injectivity is the regularity of a power of a variable, surjectivity is the chart computation
`Stacks.ProjectiveSpace.Cohomology.exists_degreeSection_eq_of_commRing`. -/
@[ega "III 2.1.12" "(ii)"]
theorem bijective_degreeSectionLinear {A : Type u} [CommRing A] (n d : ℕ) :
    Function.Bijective (degreeSectionLinear A n d) :=
  ⟨injective_degreeSectionLinear n d, fun s => exists_degreeSection_eq_of_commRing A n d s⟩

/-- **Every global section of `𝒪(d)` on `ℙⁿ_A` is the section of a form of degree `d`**, and of
exactly one. -/
theorem bijective_degreeSection {A : Type u} [CommRing A] (n d : ℕ) :
    Function.Bijective (degreeSection (polyGrading A n) d) :=
  bijective_degreeSectionLinear n d

/-- **Every global section of `𝒪(d)` on `ℙⁿ_A` comes from a form of degree `d`.** -/
theorem exists_degreeSection_eq {A : Type u} [CommRing A] (n d : ℕ)
    (s : twistGlobalSections (polyGrading A n) d) :
    ∃ a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A d,
      degreeSection (polyGrading A n) d a = s :=
  (bijective_degreeSection n d).2 s

end Stacks.ProjectiveSpace.Cohomology

end
