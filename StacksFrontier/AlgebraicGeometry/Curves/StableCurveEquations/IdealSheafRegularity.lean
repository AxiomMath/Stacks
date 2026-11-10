module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.StableCurveEquations.ClosedSubschemeHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.KernelRegularityInduction

/-!
# Uniform regularity of the ideal sheaf of a curve in projective space

Let `φ : X ⟶ ℙⁿ_k` be a closed immersion over a field, `X` proper of dimension at most one. The
Hilbert polynomial of `φ_* 𝒪_X` is `e d + c` with `e = deg(φ^* 𝒪(1))` and `c = χ(X, 𝒪_X)`
(`AlgebraicGeometry.hilbertPolynomial_pushforward_unit_eq`). By [Stacks, Tag 08AG] the kernel of
`𝒪_{ℙⁿ_k} ⟶ φ_* 𝒪_X`, the ideal sheaf of `X`, is then `m`-regular for an `m` depending only on
`n`, `e` and `c` — not on the field, the curve or the embedding — and it stays regular in every
larger degree by [Stacks, Tag 08A6].

## Main definitions

* `AlgebraicGeometry.closedImmersionQuotient`: the map `𝒪^{⊕ 1} ⟶ φ_* 𝒪_X` of
  [Stacks, Tag 08AG], from the free module of rank one.

## Main results

* `AlgebraicGeometry.hilbertPolynomial_pushforward_unit_eq`: the Hilbert polynomial of a curve.
* `AlgebraicGeometry.exists_isMRegular_kernel_closedImmersionQuotient`: the uniform regularity.

## References

* [Stacks Project, Tag 08AG](https://stacks.math.columbia.edu/tag/08AG)
* [Stacks Project, Tag 08A6](https://stacks.math.columbia.edu/tag/08A6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ projectiveSpaceOverRing n (.of k)) [IsClosedImmersion φ]

/-- **The Hilbert polynomial of a curve in `ℙⁿ_k`.** For a closed immersion `φ` of a proper scheme
of dimension at most one, `χ(ℙⁿ_k, (φ_* 𝒪_X)(d)) = d · deg(φ^* 𝒪(1)) + χ(X, 𝒪_X)`. -/
theorem hilbertPolynomial_pushforward_unit_eq
    [((Scheme.Modules.pushforward φ).obj (SheafOfModules.unit X.ringCatSheaf)).IsCoherent]
    (hdim : topologicalKrullDim X ≤ 1) (d : ℤ) :
    hilbertPolynomial k n ((Scheme.Modules.pushforward φ).obj
        (SheafOfModules.unit X.ringCatSheaf)) d =
      d * invertibleCurveDegree k (φ ≫ (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))) hdim
          ((Scheme.Modules.pullback φ).obj (twistOver n (Spec (.of k)) 1)) +
        ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k (cohomologyOverField k
          (φ ≫ (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)))
          (SheafOfModules.unit X.ringCatSheaf) i) : ℤ) := by
  rw [hilbertPolynomial_pushforward_unit_eq_finsum, ← invertibleCurveDegree_pullback_twistOver]
  unfold invertibleCurveDegree
  ring

/-- **The map `𝒪^{⊕ 1} ⟶ φ_* 𝒪_X`** from the free module of rank one on `ℙⁿ_k`, whose kernel is
the ideal sheaf of the closed subscheme `X`. -/
def closedImmersionQuotient :
    freeModules k n 1 ⟶ (Scheme.Modules.pushforward φ).obj (SheafOfModules.unit X.ringCatSheaf) :=
  Sigma.desc fun _ => ClosedImmersionCoherentImage.unitToPushforwardUnit φ

/-- The map `closedImmersionQuotient φ : 𝒪^{⊕ 1} ⟶ φ_* 𝒪_X` is an epimorphism. -/
instance epi_closedImmersionQuotient : Epi (closedImmersionQuotient φ) := by
  have : Epi (C := (projectiveSpaceOverRing n (.of k)).Modules)
      (ClosedImmersionCoherentImage.unitToPushforwardUnit φ) :=
    ClosedImmersionCoherentImage.epi_unitToPushforwardUnit φ
  have h : Sigma.ι (fun _ : Fin 1 => Stacks.Ample.unitModule (projectiveSpaceOverRing n (.of k)))
      0 ≫ closedImmersionQuotient φ = ClosedImmersionCoherentImage.unitToPushforwardUnit φ :=
    Sigma.ι_comp_desc _ _
  exact epi_of_epi_fac h

/-- For a closed immersion `φ : X ⟶ ℙⁿ_k`, the pushforward `φ_* 𝒪_X` is coherent. -/
instance isCoherent_pushforward_unit_closedImmersion_projectiveSpace :
    ((Scheme.Modules.pushforward φ).obj (SheafOfModules.unit X.ringCatSheaf)).IsCoherent :=
  haveI : IsLocallyNoetherian (projectiveSpaceOverRing n (.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian n (Spec (.of k))
  haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_isClosedImmersion φ
  haveI := Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  isCoherent_pushforward_of_isClosedImmersion φ _

/-- The ideal sheaf `ker(𝒪^{⊕ 1} ⟶ φ_* 𝒪_X)` of `X` in `ℙⁿ_k` is coherent. -/
instance isCoherent_kernel_closedImmersionQuotient :
    (kernel (closedImmersionQuotient φ)).IsCoherent :=
  CoherentAbelian.isCoherent_kernel _

/-- **[Stacks, Tag 08AG] for curves of fixed degree and Euler characteristic.** Given `n`, `e`
and `c` there is `m` such that for every field `k` and every closed immersion `φ : X ⟶ ℙⁿ_k` of a
proper scheme of dimension at most one with `deg(φ^* 𝒪(1)) = e` and `χ(X, 𝒪_X) = c`, the ideal
sheaf of `X` is `d`-regular for every `d ≥ m`. -/
theorem exists_isMRegular_kernel_closedImmersionQuotient (n : ℕ) (e c : ℤ) :
    ∃ m : ℕ, ∀ (k : Type u) [Field k] (X : Scheme.{u})
      (φ : X ⟶ projectiveSpaceOverRing n (.of k)) [IsClosedImmersion φ]
      (hdim : topologicalKrullDim X ≤ 1),
      invertibleCurveDegree k (φ ≫ (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k))) hdim
          ((Scheme.Modules.pullback φ).obj (twistOver n (Spec (.of k)) 1)) = e →
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank k (cohomologyOverField k
          (φ ≫ (projectiveSpaceOverRing n (.of k) ↘ Spec (.of k)))
          (SheafOfModules.unit X.ringCatSheaf) i) : ℤ) = c →
      ∀ d : ℤ, (m : ℤ) ≤ d → IsMRegular k n (kernel (closedImmersionQuotient φ)) d := by
  obtain ⟨m₀, hm₀⟩ := exists_isMRegular_kernel_free_of_hilbertPolynomial n 1
    (Polynomial.C (e : ℚ) * Polynomial.X + Polynomial.C (c : ℚ))
  refine ⟨m₀.toNat, fun k _ X φ _ hdim he hc d hd => ?_⟩
  have hreg := hm₀ k ((Scheme.Modules.pushforward φ).obj (SheafOfModules.unit X.ringCatSheaf))
    (closedImmersionQuotient φ) (fun d => by
      rw [hilbertPolynomial_pushforward_unit_eq φ hdim d, he, hc]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      push_cast
      ring)
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, d = m₀ + j := ⟨(d - m₀).toNat, by omega⟩
  clear hd
  induction j with
  | zero => simpa using hreg
  | succ j ih =>
    have := isMRegular_add_one k n (kernel (closedImmersionQuotient φ)) _ ih
    rwa [Nat.cast_succ, ← add_assoc]

end AlgebraicGeometry

end
