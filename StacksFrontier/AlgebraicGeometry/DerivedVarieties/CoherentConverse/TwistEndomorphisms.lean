module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentConverse.TwistExt
public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveGeneratorHomGroups
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistSectionsCoeffAction
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoefficientScalars
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# The endomorphisms of a twist on projective space are the scalars

Let `k` be a field and `X = ℙⁿ_k = Proj k[T₀, …, Tₙ]`, viewed over `Spec k` by its structure
morphism. Every endomorphism of `𝒪(d)`, as an `𝒪_X`-module or as an object of the derived
category, is multiplication by a scalar of `k`, for the `k`-linear structure that the structure
morphism induces (`AlgebraicGeometry.modulesLinear`).

## Main definitions

* `Stacks.AlgebraicGeometry.TwistEndomorphisms.projOver`: `ℙⁿ_k` as an object over `Spec k`.

## Main results

* `Stacks.AlgebraicGeometry.TwistEndomorphisms.twistMul_C_eq_smul_id`: multiplication by the
  constant polynomial `r` on `𝒪(d)` is `r • 𝟙`.
* `Stacks.AlgebraicGeometry.TwistEndomorphisms.exists_eq_smul_id`: every endomorphism of
  `𝒪(d)` is a scalar.
* `Stacks.AlgebraicGeometry.TwistEndomorphisms.exists_eq_smul_id_twistObj`: the same in the
  derived category.

## Implementation notes

An endomorphism of `𝒪(d)` is multiplication by a homogeneous polynomial of degree zero
(`Stacks.AlgebraicGeometry.ProjectiveGenerator.exists_twistMul_eq`), that is by a constant
`C r`. Multiplication by `C r` acts on the value of a section at every point as multiplication
by `r / 1`, and so does the scalar `r • 𝟙`: the structure morphism pulls `r` back to the global
function `Stacks.ProjectiveSpace.Cohomology.coeffScalar k n r`, whose value at every point is
`C r / 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart

universe w u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.TwistEndomorphisms

open Stacks.AlgebraicGeometry.ExampleGenerator

variable (k : Type u) [Field k] (n : ℕ)

/-- `ℙⁿ_k = Proj k[T₀, …, Tₙ]` as a scheme over `Spec k`. -/
abbrev projOver : Over (Spec (CommRingCat.of k)) := Over.mk (projToSpecCoeff k n)

/-- The `k`-linear structure on `𝒪_{ℙⁿ_k}`-modules induced by the structure morphism, in the
`SheafOfModules` spelling of the category (it is `AlgebraicGeometry.modulesLinear` there). -/
def centerMap : k →+* CatCenter (Mods k n) := AlgebraicGeometry.baseRingToCenter k (projOver k n)

/-- The `k`-linear structure on `𝒪_{ℙⁿ_k}`-modules. -/
@[instance_reducible]
def modsLinear : Linear k (Mods k n) := Linear.ofRingMorphism (centerMap k n)

/-- Multiplication by the constant polynomial `r` on `𝒪(d)`. -/
def twistScalar (r : k) (d : ℤ) :
    ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d ⟶
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d :=
  Stacks.AlgebraicGeometry.ProjectiveGenerator.twistMul (polyGrading k n) (MvPolynomial.C r)
    0 d d (Stacks.AlgebraicGeometry.ProjectiveGenerator.mem_integerGrading_of_mem
      (polyGrading k n) (Stacks.ProjectiveSpace.Cohomology.C_mem_polyGrading_zero k n r))
    (zero_add d)

/-- The action of the scalar `r` on `𝒪(d)` through the structure morphism. -/
def twistBaseScalar (r : k) (d : ℤ) :
    ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d ⟶
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d :=
  (AlgebraicGeometry.baseScalar k (projOver k n) r).app
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d)

/-- **Multiplication by a constant polynomial is the scalar action of the coefficient.** At every
point both multiply the value of a section by `C r / 1`. -/
theorem twistScalar_eq_twistBaseScalar (r : k) (d : ℤ) :
    twistScalar k n r d = twistBaseScalar k n r d := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext s
  refine Subtype.ext (funext fun x => ?_)
  show LocalizedModule.map _ (LinearMap.mulLeft _ (MvPolynomial.C r)) (s.1 x) =
    HomogeneousLocalization.val (((projToSpecCoeff k n).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)).1 ⟨x.1, trivial⟩) * s.1 x
  rw [Stacks.AlgebraicGeometry.ProjEulerSequence.projToSpecCoeff_appTop_val,
    ← Localization.mk_one_eq_algebraMap]
  induction s.1 x using Localization.induction_on with
  | H y =>
    show LocalizedModule.map _ (LinearMap.mulLeft _ (MvPolynomial.C r))
      (LocalizedModule.mk y.1 y.2) = _
    rw [LocalizedModule.map_mk, Localization.mk_mul]
    simp only [LinearMap.mulLeft_apply, one_mul]
    rfl

/-- Every endomorphism of `𝒪(d)` is multiplication by a constant polynomial. -/
theorem exists_eq_twistScalar (d : ℤ)
    (φ : ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d ⟶
      ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d) :
    ∃ r : k, φ = twistScalar k n r d := by
  obtain ⟨p, hp, hφ⟩ := Stacks.AlgebraicGeometry.ProjectiveGenerator.exists_twistMul_eq k n
    (zero_add d) (Or.inl le_rfl) φ
  have hp' : p ∈ polyGrading k n 0 := by
    rwa [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
      AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading_natCast] at hp
  have hC : p = MvPolynomial.C (p.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.1
      (by simpa using ((MvPolynomial.mem_homogeneousSubmodule 0 p).1 hp').totalDegree_le)
  refine ⟨p.coeff 0, ?_⟩
  rw [← hφ]
  unfold twistScalar
  congr 1

attribute [local instance] modsLinear in
/-- The scalar action through the structure morphism is the `k`-linear structure. -/
theorem twistBaseScalar_eq_smul (d : ℤ) (r : k) :
    twistBaseScalar k n r d = r • 𝟙 _ :=
  (Category.comp_id _).symm

/-- `exists_eq_twistScalar`, with the endomorphism typed in `Mods k n`. -/
theorem exists_eq_twistScalar' (d : ℤ)
    (φ : (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d : Mods k n) ⟶
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k n) d : Mods k n)) :
    ∃ r, φ = twistScalar k n r d := exists_eq_twistScalar k n d φ

/-- The endomorphism of `𝒪(d)` underlying an endomorphism of `𝒪(d)[0]` is multiplication by a
constant. -/
theorem exists_preimage_eq_twistScalar [HasDerivedCategory.{w} (Mods k n)] (d : ℤ)
    (e : TwistExt.twistObj k n d ⟶ TwistExt.twistObj k n d) :
    ∃ r : k, (DerivedCategory.singleFunctor (Mods k n) 0).preimage e = twistScalar k n r d :=
  exists_eq_twistScalar' k n d ((DerivedCategory.singleFunctor (Mods k n) 0).preimage e)

/-- An endomorphism of `𝒪(d)[0]` is the image of the endomorphism of `𝒪(d)` underlying it. -/
theorem eq_map_twistScalar_of_preimage_eq [HasDerivedCategory.{w} (Mods k n)] (d : ℤ)
    (e : TwistExt.twistObj k n d ⟶ TwistExt.twistObj k n d)
    (r : k) (hr : (DerivedCategory.singleFunctor (Mods k n) 0).preimage e = twistScalar k n r d) :
    e = (DerivedCategory.singleFunctor (Mods k n) 0).map (twistScalar k n r d) := by
  rw [← hr, Functor.map_preimage]

attribute [local instance] modsLinear in
/-- Multiplication by a constant, placed in degree zero, is the scalar action on `𝒪(d)[0]`. -/
theorem map_twistScalar_eq_smul_id [HasDerivedCategory.{w} (Mods k n)] (d : ℤ) (r : k) :
    (DerivedCategory.singleFunctor (Mods k n) 0).map (twistScalar k n r d) =
      r • 𝟙 (TwistExt.twistObj k n d) := by
  have h : twistScalar k n r d = r • 𝟙 _ :=
    (twistScalar_eq_twistBaseScalar k n r d).trans (twistBaseScalar_eq_smul k n d r)
  exact (congrArg (DerivedCategory.singleFunctor (Mods k n) 0).map h).trans
    ((Functor.linear_iff k _).1 inferInstance _ r)

attribute [local instance] modsLinear in
/-- **Every endomorphism of `𝒪(d)[0]` in the derived category is a scalar.** -/
theorem exists_eq_smul_id_twistObj [HasDerivedCategory.{w} (Mods k n)] (d : ℤ)
    (e : TwistExt.twistObj k n d ⟶ TwistExt.twistObj k n d) :
    ∃ r : k, e = r • 𝟙 (TwistExt.twistObj k n d) :=
  (exists_preimage_eq_twistScalar k n d e).imp fun r hr =>
    (eq_map_twistScalar_of_preimage_eq k n d e r hr).trans (map_twistScalar_eq_smul_id k n d r)

end Stacks.AlgebraicGeometry.TwistEndomorphisms

end
