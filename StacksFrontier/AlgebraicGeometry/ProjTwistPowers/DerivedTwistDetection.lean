module

public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.DerivedTwistDetection
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.DerivedQCohDetection
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# The twists of `Proj 𝒜` detect the zero object of `D_QCoh(𝒪_X)`

`Stacks.AmpleNonvanishingChart.isZero_of_forall_hom_tensorPowModule_neg_eq_zero` detects the
zero object of `D_QCoh(𝒪_X)`, on a scheme with affine diagonal, by the negative tensor powers
`L ^⊗ (-p)` of an ample invertible module, and
`Stacks.AmpleNonvanishingChart.isZero_of_isGE_of_forall_hom_tensorPowModule_neg_eq_zero` does
so on the bounded-below objects of any scheme. On `X = Proj 𝒜` for a graded ring generated in
degree one those powers are the Serre twists `𝒪_X(-p)` of [Stacks, Tag 01MN], by
`Stacks.AlgebraicGeometry.ProjTwistPowers.tensorPowModuleIsoTwistingSheaf`, and this file
restates the detection in terms of the twists themselves — the vocabulary in which
[Stacks, Tag 0A9V] is stated.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistPowers.isZero_of_forall_hom_twistingSheaf_neg_eq_zero` and
  its bounded-below variant
  `Stacks.AlgebraicGeometry.ProjTwistPowers.isZero_of_isGE_of_forall_hom_twistingSheaf_neg_eq_zero`
  — the detection statement in terms of `𝒪_X(-p)`, for any graded ring whose `𝒪(1)` is ample,
  invertible, and whose degree-one part generates.
* `Stacks.ProjectiveSpace.isZero_of_forall_hom_twistingSheaf_neg_eq_zero` and
  `Stacks.ProjectiveSpace.isZero_of_isGE_of_forall_hom_twistingSheaf_neg_eq_zero` — the same on
  `X = P^n_A = Proj A[T₀, …, Tₙ]`, where all three of those inputs are discharged: ampleness by
  `Stacks.ProjectiveSpace.isAmple_twistingSheaf_one` ([Stacks, Tag 01Q2] at degree one),
  invertibility by [Stacks, Tag 01MW], and degree-one generation by the variables. This is
  [Stacks, Tag 0BQR] for `𝒪(1)`, the input of the last step of [Stacks, Tag 0A9V].

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category TopologicalSpace Opposite
open MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample

universe w u

namespace Stacks.AlgebraicGeometry.ProjTwistPowers

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {S : Type u} [CommRing S] {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable [Stacks.Ample.IsInvertibleModule (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1)]

/-- Vanishing of all maps out of `Y` to `K` transfers along an isomorphism `X ≅ Y`. -/
private theorem eq_zero_of_iso_of_forall_eq_zero {C : Type*} [Category C] [Preadditive C]
    {X Y K : C}
    (e : X ≅ Y) (h : ∀ ψ : Y ⟶ K, ψ = 0) (φ : X ⟶ K) : φ = 0 :=
  (cancel_epi e.inv).1 (by rw [h (e.inv ≫ φ), comp_zero])

/-- **The twists `𝒪_X(-p)`, `p ≥ 0`, detect the zero object among the bounded-below objects of
`D_QCoh(𝒪_X)` on `X = Proj 𝒜`.**

Here `𝒜` is generated in degree one (`hgen`) and `𝒪_X(1)` is ample (`hL`). This is
`Stacks.AmpleNonvanishingChart.isZero_of_isGE_of_forall_hom_tensorPowModule_neg_eq_zero` at
`L = 𝒪_X(1)`, with the hypothesis transported along
`Stacks.AlgebraicGeometry.ProjTwistPowers.tensorPowModuleIsoTwistingSheaf`, which identifies
`𝒪_X(1) ^⊗ (-p)` with `𝒪_X(-p)`. -/
theorem isZero_of_isGE_of_forall_hom_twistingSheaf_neg_eq_zero
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤)
    (hL : IsAmple (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1))
    (K : DerivedCategory (AlgebraicGeometry.Proj 𝒜).Modules) (j₀ : ℤ) (hKge : K.IsGE j₀)
    (hKQ : ∀ m : ℤ, ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.Proj 𝒜).Modules m).obj K).IsQuasicoherent)
    (hvan : ∀ (p : ℕ) (j : ℤ) (φ : (DerivedCategory.singleFunctor
      (AlgebraicGeometry.Proj 𝒜).Modules j).obj (twistingSheaf 𝒜 (-(p : ℤ))) ⟶ K), φ = 0) :
    IsZero K := by
  refine Stacks.AmpleNonvanishingChart.isZero_of_isGE_of_forall_hom_tensorPowModule_neg_eq_zero
    (X := AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) hL K j₀ hKge hKQ (fun p j φ => ?_)
  exact eq_zero_of_iso_of_forall_eq_zero ((DerivedCategory.singleFunctor
    (AlgebraicGeometry.Proj 𝒜).Modules j).mapIso
      (tensorPowModuleIsoTwistingSheaf 𝒜 hgen (-(p : ℤ)))) (hvan p j) φ

/-- **The twists `𝒪_X(-p)`, `p ≥ 0`, detect the zero object of `D_QCoh(𝒪_X)` on `X = Proj 𝒜`.**

Here `𝒜` is generated in degree one (`hgen`) and `𝒪_X(1)` is ample (`hL`). This is
`Stacks.AmpleNonvanishingChart.isZero_of_forall_hom_tensorPowModule_neg_eq_zero` at
`L = 𝒪_X(1)` — `Proj 𝒜` is separated, so its diagonal is affine — with the hypothesis
transported along `Stacks.AlgebraicGeometry.ProjTwistPowers.tensorPowModuleIsoTwistingSheaf`. -/
theorem isZero_of_forall_hom_twistingSheaf_neg_eq_zero
    (hgen : Algebra.adjoin (𝒜 0) ((𝒜 1 : Set S)) = ⊤)
    (hL : IsAmple (AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1))
    (K : DerivedCategory (AlgebraicGeometry.Proj 𝒜).Modules)
    (hKQ : ∀ m : ℤ, ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.Proj 𝒜).Modules m).obj K).IsQuasicoherent)
    (hvan : ∀ (p : ℕ) (j : ℤ) (φ : (DerivedCategory.singleFunctor
      (AlgebraicGeometry.Proj 𝒜).Modules j).obj (twistingSheaf 𝒜 (-(p : ℤ))) ⟶ K), φ = 0) :
    IsZero K := by
  refine Stacks.AmpleNonvanishingChart.isZero_of_forall_hom_tensorPowModule_neg_eq_zero
    (X := AlgebraicGeometry.Proj 𝒜) (twistingSheaf 𝒜 1) hL K hKQ (fun p j φ => ?_)
  exact eq_zero_of_iso_of_forall_eq_zero ((DerivedCategory.singleFunctor
    (AlgebraicGeometry.Proj 𝒜).Modules j).mapIso
      (tensorPowModuleIsoTwistingSheaf 𝒜 hgen (-(p : ℤ)))) (hvan p j) φ

end Stacks.AlgebraicGeometry.ProjTwistPowers

namespace Stacks.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

/-- The degree-one part of `A[T₀, …, Tₙ]` generates it over the degree-zero part. -/
private theorem adjoin_degree_one_homogeneousSubmodule' (A : Type u) [CommRing A] (n : ℕ) :
    Algebra.adjoin (homogeneousSubmodule (Fin (n + 1)) A 0)
      ((homogeneousSubmodule (Fin (n + 1)) A 1 : Set (MvPolynomial (Fin (n + 1)) A))) = ⊤ := by
  rw [← Stacks.AlgebraicGeometry.ProjTwistMono.range_coe_degree_one
    (homogeneousSubmodule (Fin (n + 1)) A)]
  exact Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule
    (Fin (n + 1)) A

/-- **The twists `𝒪(-p)`, `p ≥ 0`, detect the zero object among the bounded-below objects of
`D_QCoh(𝒪_X)` on `X = P^n_A = Proj A[T₀, …, Tₙ]`.** Unconditional in `A` and `n`: the three
inputs of
`Stacks.AlgebraicGeometry.ProjTwistPowers.isZero_of_isGE_of_forall_hom_twistingSheaf_neg_eq_zero`
are all discharged here — ampleness of `𝒪(1)` by
`Stacks.ProjectiveSpace.isAmple_twistingSheaf_one`, its invertibility by [Stacks, Tag 01MW], and
generation in degree one by the variables. -/
theorem isZero_of_isGE_of_forall_hom_twistingSheaf_neg_eq_zero (A : Type u) [CommRing A] (n : ℕ)
    (K : DerivedCategory
      (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (n + 1)) A)).Modules)
    (j₀ : ℤ) (hKge : K.IsGE j₀)
    (hKQ : ∀ m : ℤ, ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (n + 1)) A)).Modules m).obj
        K).IsQuasicoherent)
    (hvan : ∀ (p : ℕ) (j : ℤ) (φ : (DerivedCategory.singleFunctor
      (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (n + 1)) A)).Modules j).obj
        (twistingSheaf (homogeneousSubmodule (Fin (n + 1)) A) (-(p : ℤ))) ⟶ K), φ = 0) :
    IsZero K :=
  Stacks.AlgebraicGeometry.ProjTwistPowers.isZero_of_isGE_of_forall_hom_twistingSheaf_neg_eq_zero
    (homogeneousSubmodule (Fin (n + 1)) A)
    (adjoin_degree_one_homogeneousSubmodule' A n)
    (isAmple_twistingSheaf_one A n) K j₀ hKge hKQ hvan

/-- **The twists `𝒪(-p)`, `p ≥ 0`, detect the zero object of `D_QCoh(𝒪_X)` on
`X = P^n_A = Proj A[T₀, …, Tₙ]`**: an object `K` with quasi-coherent cohomology sheaves such
that every morphism `𝒪(-p)[-j] ⟶ K` vanishes is zero. This is [Stacks, Tag 0BQR] for the ample
invertible sheaf `𝒪(1)` of [Stacks, Tag 01Q2], in the form the proof of [Stacks, Tag 0A9V]
uses it: `Hom(𝒪(-p)[-j], K) = Hʲ(X, K ⊗^𝐋 𝒪(p))`. -/
theorem isZero_of_forall_hom_twistingSheaf_neg_eq_zero (A : Type u) [CommRing A] (n : ℕ)
    (K : DerivedCategory
      (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (n + 1)) A)).Modules)
    (hKQ : ∀ m : ℤ, ((DerivedCategory.homologyFunctor
      (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (n + 1)) A)).Modules m).obj
        K).IsQuasicoherent)
    (hvan : ∀ (p : ℕ) (j : ℤ) (φ : (DerivedCategory.singleFunctor
      (AlgebraicGeometry.Proj (homogeneousSubmodule (Fin (n + 1)) A)).Modules j).obj
        (twistingSheaf (homogeneousSubmodule (Fin (n + 1)) A) (-(p : ℤ))) ⟶ K), φ = 0) :
    IsZero K :=
  Stacks.AlgebraicGeometry.ProjTwistPowers.isZero_of_forall_hom_twistingSheaf_neg_eq_zero
    (homogeneousSubmodule (Fin (n + 1)) A)
    (adjoin_degree_one_homogeneousSubmodule' A n)
    (isAmple_twistingSheaf_one A n) K hKQ hvan

end Stacks.ProjectiveSpace

end
