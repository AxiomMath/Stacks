module

public import StacksFrontier.AlgebraicGeometry.Spaces.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerNumericalPolynomialProper

/-!
# The intersection number as a coefficient of the numerical polynomial

Let `k` be a field, `X` a proper algebraic space over `k`, `i : Z ⟶ X` a closed subspace and
`L₁, …, L_r` invertible `𝒪_X`-modules.  By Stacks 0DN4 the function

`(n₁, …, n_r) ↦ χ(X, i_*𝒪_Z ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})`

is the restriction to the integral tuples of a unique rational polynomial,
`AlgebraicGeometry.Space.twistedEulerPolynomial`, of total degree at most `dim Z`.  Definition
0EDF takes the intersection number `(L₁ ⋯ L_d · Z)` of `d = dim Z` invertible modules to be the
coefficient of `n₁ ⋯ n_d` in it; the library's `AlgebraicGeometry.Space.intersectionNumber` is
the mixed finite difference of the function, and this file proves that it is that coefficient.

## Main definitions

* `AlgebraicGeometry.Space.twistedEulerPolynomial`: the numerical polynomial of the twisted Euler
  characteristics of `i_*𝒪_Z`.

## Main results

* `AlgebraicGeometry.Space.exists_representsTwistedEuler_structureSheafPushforward`: the
  polynomial exists, with total degree at most `d` when `dim Z = d`.
* `AlgebraicGeometry.Space.eval_twistedEulerPolynomial` and
  `AlgebraicGeometry.Space.totalDegree_twistedEulerPolynomial_le`: its values and its degree.
* `AlgebraicGeometry.Space.intersectionNumber_eq_coeff_twistedEulerPolynomial`: **Definition 0EDF,
  as the coefficient of `n₁ ⋯ n_d`.**

## References

* [Stacks Project, Tag 0EDF](https://stacks.math.columbia.edu/tag/0EDF)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X Z : AlgebraicSpaces B (Spec (.of k)) hk)

/-- The structure sheaf of a closed subspace of a proper algebraic space over a field is
coherent, the closed subspace being proper over `k` and hence locally Noetherian. -/
theorem isCoherent_unit_of_isClosedImmersion (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom) :
    IsCoherent B (Spec (.of k)) hk Z.1 Z.2
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk Z.1 Z.2).O)) :=
  have : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk Z.1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Z.1 Z.2 (i.hom ≫ f)
      (isProper_comp B (Spec (.of k)) hk Z.2 X.2
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) i.hom f
        (isProper_of_isClosedImmersion B (Spec (.of k)) hk Z.2 X.2 i.hom hi) hf)⟩
  inferInstance

/-- **The twisted Euler characteristics of `i_*𝒪_Z` are a polynomial of total degree at most
`dim Z`** (Stacks 0DN4 at `F = i_*𝒪_Z`), in the bound form with the convention that the zero
polynomial has degree `⊥`. -/
theorem exists_representsTwistedEuler_structureSheafPushforward_withBot {r : ℕ}
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
        ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) L n)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w}
            k B hk X Z f hf i hi L n) : ℤ) : ℚ)) ∧
      (P = 0 ∨ (P.totalDegree : WithBot ℕ∞) ≤ dimension B (Spec (.of k)) hk Z.1 Z.2) :=
  isTwistedEulerNumericalPolynomial_of_isCoherent.{u, w} k B hk X f hf
    (structureSheafPushforward B (Spec (.of k)) hk i)
    (isCoherent_structureSheafPushforward B (Spec (.of k)) hk
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf) i hi) L Z i hi
    _ (isCoherent_unit_of_isClosedImmersion k B hk X Z f hf i hi) (Iso.refl _)

/-- **The twisted Euler characteristics of `i_*𝒪_Z` are a polynomial of total degree at most
`d` when `dim Z = d`** (Stacks 0DN4 at `F = i_*𝒪_Z`).  This is the polynomial with which
`AlgebraicGeometry.Space.intersectionNumber_eq_coeff` identifies the intersection number of
Stacks 0EDF. -/
theorem exists_representsTwistedEuler_structureSheafPushforward {r : ℕ} (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    ∃ P : MvPolynomial (Fin r) ℚ,
      (∀ n : Fin r → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
        ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
          (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
            (structureSheafPushforward B (Spec (.of k)) hk i) L n)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w}
            k B hk X Z f hf i hi L n) : ℤ) : ℚ)) ∧
      P.totalDegree ≤ d := by
  obtain ⟨P, hP, hdeg⟩ := exists_representsTwistedEuler_structureSheafPushforward_withBot.{u, w}
    k B hk X Z f hf i hi L
  refine ⟨P, hP, ?_⟩
  rcases hdeg with rfl | hdeg
  · simp
  · rw [hd] at hdeg
    exact_mod_cast hdeg

/-- **The numerical polynomial of the twisted Euler characteristics of `i_*𝒪_Z`** (Stacks 0DN4):
the unique rational polynomial whose value at every integral tuple `n` is
`χ(X, i_*𝒪_Z ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_r^{⊗ n_r})`.  The intersection number of Definition 0EDF is its
coefficient of `n₁ ⋯ n_d`
(`AlgebraicGeometry.Space.intersectionNumber_eq_coeff_twistedEulerPolynomial`). -/
def twistedEulerPolynomial {r : ℕ} (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    MvPolynomial (Fin r) ℚ :=
  (exists_representsTwistedEuler_structureSheafPushforward_withBot.{u, w} k B hk X Z f hf i hi
    L).choose

/-- The values of `AlgebraicGeometry.Space.twistedEulerPolynomial` at the integral tuples are the
twisted Euler characteristics of `i_*𝒪_Z`. -/
theorem eval_twistedEulerPolynomial {r : ℕ} (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (n : Fin r → ℤ) :
    MvPolynomial.eval (fun j => (n j : ℚ))
        (twistedEulerPolynomial.{u, w} k B hk X Z f hf i hi L) =
      ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) L n)
        (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w}
          k B hk X Z f hf i hi L n) : ℤ) : ℚ) :=
  (exists_representsTwistedEuler_structureSheafPushforward_withBot.{u, w} k B hk X Z f hf i hi
    L).choose_spec.1 n

/-- **`AlgebraicGeometry.Space.twistedEulerPolynomial` has total degree at most `d` when
`dim Z = d`**: it is the polynomial of
`AlgebraicGeometry.Space.exists_representsTwistedEuler_structureSheafPushforward`, a
representing polynomial being unique (`AlgebraicGeometry.Space.eq_of_representsTwistedEuler`). -/
theorem totalDegree_twistedEulerPolynomial_le {r : ℕ} (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    (twistedEulerPolynomial.{u, w} k B hk X Z f hf i hi L).totalDegree ≤ d := by
  obtain ⟨P, hP, hdeg⟩ := exists_representsTwistedEuler_structureSheafPushforward.{u, w}
    k B hk X Z d f hf i hi hd L
  rwa [MvPolynomial.eq_of_eval_intCast_eq fun n =>
    (eval_twistedEulerPolynomial.{u, w} k B hk X Z f hf i hi L n).trans (hP n).symm]

/-- **Definition 0EDF: the intersection number is the coefficient of `n₁ ⋯ n_d`** in the
numerical polynomial of the twisted Euler characteristics of `i_*𝒪_Z`, for a closed subspace
`i : Z ⟶ X` of dimension `d`.  This is `AlgebraicGeometry.Space.intersectionNumber_eq_coeff` at
`AlgebraicGeometry.Space.twistedEulerPolynomial`, whose degree bound is Stacks 0DN4. -/
theorem intersectionNumber_eq_coeff_twistedEulerPolynomial (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    ((intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L : ℤ) : ℚ) =
      (twistedEulerPolynomial.{u, w} k B hk X Z f hf i hi L).coeff
        (Finsupp.equivFunOnFinite.symm fun _ => 1) :=
  intersectionNumber_eq_coeff.{u, w} k B hk X Z d f hf i hi hd L _
    (eval_twistedEulerPolynomial.{u, w} k B hk X Z f hf i hi L)
    (totalDegree_twistedEulerPolynomial_le.{u, w} k B hk X Z d f hf i hi hd L)

end AlgebraicGeometry.Space

end
