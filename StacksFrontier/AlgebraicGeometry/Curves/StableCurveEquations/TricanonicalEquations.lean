module

public import StacksFrontier.AlgebraicGeometry.Curves.StableCurveEquations.Equations
public import StacksFrontier.AlgebraicGeometry.Curves.StableCurveEquations.TricanonicalClosedImmersion

/-!
# Every stable curve of genus `g` is cut out of `ℙ^{5g-6}` by forms of a fixed degree

Let `g ≥ 2`. There is `m`, depending only on `g`, such that every proper scheme `X` of dimension
one over a field `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`, with at-worst-nodal singularities and
ample dualizing sheaf — a stable curve of genus `g` over `k` — is isomorphic over `k` to

`Proj (k[T₀, …, T_{5g-6}] ⧸ (s_1, …, s_M))`

for forms `s_j` of degree `m`, `M = dim_k k[T₀, …, T_{5g-6}]_m`. This is the curve side of the
boundedness of stable curves of genus `g` used in the proof of [Stacks, Tag 0E9B].

The tricanonical embedding `X ⟶ ℙ^{5g-6}_k`
(`AlgebraicGeometry.exists_isClosedImmersion_tensorPower_three_dualizingSheafOverField`, from
[Stacks, Tag 0E8X]) pulls `𝒪(1)` back to `ω_X^{⊗ 3}`, of degree `6g - 6`, and `χ(X, 𝒪_X) = 1 - g`;
so the Hilbert polynomial of `X` is `(6g - 6) d + 1 - g` and the ideal sheaf of `X` is `m`-regular
for an `m` depending only on `g` ([Stacks, Tag 08AG],
`AlgebraicGeometry.exists_isMRegular_kernel_closedImmersionQuotient`). A closed subscheme with
`m`-regular ideal sheaf is cut out by forms of degree `m`
(`AlgebraicGeometry.exists_iso_proj_formsGrading_of_isMRegular`).

## Main results

* `AlgebraicGeometry.exists_iso_proj_formsGrading_of_isAmple_dualizingSheafOverField`.

## References

* [Stacks Project, Tag 0E9B](https://stacks.math.columbia.edu/tag/0E9B)
* [Stacks Project, Tag 0E8X](https://stacks.math.columbia.edu/tag/0E8X)
* [Stacks Project, Tag 08AG](https://stacks.math.columbia.edu/tag/08AG)
* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Every stable curve of genus `g ≥ 2` over a field is cut out of `ℙ^{5g-6}` by forms of a
degree `m` depending only on `g`.** There is `m` such that for every field `k` and every proper
scheme `X` of dimension one over `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`, with at-worst-nodal
singularities and ample dualizing sheaf, there are `M = dim_k k[T₀, …, T_{5g-6}]_m` forms
`s_j` of degree `m` and an isomorphism `X ≅ Proj (k[T₀, …, T_{5g-6}] ⧸ (s_1, …, s_M))` over
`k`. -/
theorem exists_iso_proj_formsGrading_of_isAmple_dualizingSheafOverField (g : ℕ) (hg : 2 ≤ g) :
    ∃ m : ℕ, ∀ (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
      [IsProper (X ↘ Spec (.of k))]
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
      (hdim : topologicalKrullDim X = 1) (_ : genus (X ↘ Spec (.of k)) = g)
      (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X)
      (_ : haveI := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
        letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim
          hnodal
        Scheme.Modules.IsAmple X (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k)))),
      ∃ (s : Fin ((5 * g - 6 + 1 + m - 1).choose m) → MvPolynomial (Fin (5 * g - 6 + 1)) k)
        (hs : ∀ j, (s j).IsHomogeneous m)
        (e : X ≅ Proj (Stacks.UniversalForms.formsGrading k s hs)),
        e.hom ≫ Stacks.UniversalForms.formsToSpec k s hs = X ↘ Spec (.of k) := by
  obtain ⟨m, hm⟩ := exists_isMRegular_kernel_closedImmersionQuotient.{u} (5 * g - 6)
    (6 * (g : ℤ) - 6) (1 - (g : ℤ))
  refine ⟨m, fun k _ X _ _ _ hdim hgX hnodal hω => ?_⟩
  subst hgX
  have := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  let := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  obtain ⟨φ, hφci, hφ, ⟨θ⟩⟩ :=
    exists_isClosedImmersion_tensorPower_three_dualizingSheafOverField hdim hg hnodal hω
  have := hφci
  have hφ' : φ ≫ (projectiveSpaceOverRing (5 * genus (X ↘ Spec (.of k)) - 6) (.of k) ↘
      Spec (.of k)) = X ↘ Spec (.of k) := hφ
  have hdim' : topologicalKrullDim X ≤ 1 := hdim.le
  -- the degree of `φ^* 𝒪(1) ≅ ω_X^{⊗ 3}` and the Euler characteristic of `𝒪_X`
  have hχO := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k
    (X ↘ Spec (.of k)) (SheafOfModules.unit X.ringCatSheaf)
    (isZero_cohomologyOverField_two_le k (X ↘ Spec (.of k)) hdim' _)
  have h0O := finrank_cohomologyOverField_unit_zero_eq_one (X ↘ Spec (.of k))
  have h1O := finrank_cohomologyOverField_one_unit_eq_genus k (X ↘ Spec (.of k))
  have hdeg : invertibleCurveDegree k
      (φ ≫ (projectiveSpaceOverRing (5 * genus (X ↘ Spec (.of k)) - 6) (.of k) ↘ Spec (.of k)))
      hdim' ((Scheme.Modules.pullback φ).obj
        (twistOver (5 * genus (X ↘ Spec (.of k)) - 6) (Spec (.of k)) 1)) =
        6 * (genus (X ↘ Spec (.of k)) : ℤ) - 6 := by
    have hL := invertibleCurveDegree_tensorPower_eq_mul_of_topologicalKrullDim_le_one k
      (X ↘ Spec (.of k)) hdim' (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3
    have hω2 := invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k
      (X ↘ Spec (.of k)) hdim'
    unfold invertibleCurveDegree at hL hω2 ⊢
    rw [hφ']
    have hθ : ∀ i, Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
        ((Scheme.Modules.pullback φ).obj
          (twistOver (5 * genus (X ↘ Spec (.of k)) - 6) (Spec (.of k)) 1)) i) =
        Module.finrank k (cohomologyOverField k (X ↘ Spec (.of k))
          (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
            (Stacks.Duality.dualizingSheafOverField (X ↘ Spec (.of k))) 3) i) :=
      fun i => finrank_cohomologyOverField_eq_of_iso k _ θ i
    rw [finsum_congr fun i => by rw [hθ i]]
    rw [hL, hω2]
    ring
  have hχ : ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k (cohomologyOverField k
      (φ ≫ (projectiveSpaceOverRing (5 * genus (X ↘ Spec (.of k)) - 6) (.of k) ↘ Spec (.of k)))
      (SheafOfModules.unit X.ringCatSheaf) i) : ℤ) = 1 - (genus (X ↘ Spec (.of k)) : ℤ) := by
    rw [hφ', hχO, h0O, h1O]
    push_cast
    ring
  have hreg := hm k X φ hdim' hdeg hχ
  obtain ⟨s, hs, e, he⟩ := exists_iso_proj_formsGrading_of_isMRegular φ m
    (fun d hd => hreg d (by exact_mod_cast hd))
  exact ⟨s, hs, e, he.trans hφ'⟩

end AlgebraicGeometry

end
