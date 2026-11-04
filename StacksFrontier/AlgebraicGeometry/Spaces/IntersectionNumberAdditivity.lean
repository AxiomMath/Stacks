module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntersectionNumberPolynomial
public import StacksFrontier.AlgebraicGeometry.Spaces.NumericalIntersection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Integrality and additivity of the intersection number of a closed subspace

Let `k` be a field, `X` a proper algebraic space over `k`, `i : Z ⟶ X` a closed subspace of
dimension `d` and `L₁, …, L_d` invertible `𝒪_X`-modules.  Stacks 0EDG says that the intersection
number `(L₁ ⋯ L_d · Z)` of Stacks 0EDF, the coefficient of `n₁ ⋯ n_d` in the numerical
polynomial `χ(X, i_*𝒪_Z ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d})`, is an integer, and Stacks 0EDH that it
is additive in each `L_{i₀}`.

`AlgebraicGeometry.Space.intersectionNumber_eq_add_of_iso_tensorSheaf` of
`StacksFrontier/AlgebraicGeometry/Spaces/NumericalIntersection.lean` proves additivity from a
numerical polynomial for the split family of `d + 1` invertible modules, and takes the coherence
of the twists of `i_*𝒪_Z` by each of the four families involved as instance arguments.  Those
instances are discharged here, by
`AlgebraicGeometry.Space.isCoherent_twistedModuleUlift_structureSheafPushforward`: a proper
algebraic space over a field is locally Noetherian, `i_*𝒪_Z` is coherent, and twisting by tensor
powers of invertible modules preserves coherence.  The invertibility of the members of the split
family `Fin.cons L_{i₀}'' L'` is the instance `AlgebraicGeometry.Space.isInvertible_cons`.

## Main results

* `AlgebraicGeometry.Space.intersectionNumber_eq_add_of_iso_tensorSheaf_of_totalDegree_le`:
  additivity of the intersection number, granted a rational polynomial of total degree at most
  `d` in `d + 1` variables whose values are the Euler characteristics of the twists of `i_*𝒪_Z`
  by the split family; no coherence instance is assumed.
* `AlgebraicGeometry.Space.exists_eval_eq_eulerCharacteristic_and_exists_intCast_eq_coeff_one`:
  **Stacks 0EDG**, the twisted Euler characteristics of `i_*𝒪_Z` are a numerical polynomial of
  total degree at most `d`, and its coefficient of `n₁ ⋯ n_d` is an integer.
* `AlgebraicGeometry.Space.intersectionNumber_eq_add_intersectionNumber_of_iso_tensorSheaf`:
  **Stacks 0EDH**, the intersection number is additive in each of its invertible modules.

Both take exactly the hypotheses of the source: the numerical polynomial is supplied by
Stacks 0DN4, `AlgebraicGeometry.Space.exists_representsTwistedEuler_structureSheafPushforward`
of `StacksFrontier/AlgebraicGeometry/Spaces/IntersectionNumberPolynomial.lean`.

## References

* [Stacks Project, Tag 0EDF](https://stacks.math.columbia.edu/tag/0EDF)
* [Stacks Project, Tag 0EDG](https://stacks.math.columbia.edu/tag/0EDG)
* [Stacks Project, Tag 0EDH](https://stacks.math.columbia.edu/tag/0EDH)
* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace AlgebraicGeometry.Space

section IntersectionNumber

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X Z : AlgebraicSpaces B (Spec (.of k)) hk)

/-- **Additivity of the intersection number, with the coherence of the twists discharged.**  Let
`i : Z ⟶ X` be a closed subspace of dimension `d` of a proper algebraic space over a field, let
`L`, `L'` and `L''` be families of `d` invertible `𝒪_X`-modules agreeing away from `i₀`, with
`L_{i₀} ≅ L_{i₀}' ⊗ L_{i₀}''`, and let `Q` be a rational polynomial of total degree at most `d` in
`d + 1` variables whose values at the integral tuples are the Euler characteristics of the twists
of `i_*𝒪_Z` by `L_{i₀}'', L_1', …, L_d'`.  Then
`(L₁ ⋯ L_d · Z) = (L₁' ⋯ L_d' · Z) + (L₁'' ⋯ L_d'' · Z)`.

This is `AlgebraicGeometry.Space.intersectionNumber_eq_add_of_iso_tensorSheaf` with its four
coherence instances supplied by
`AlgebraicGeometry.Space.isCoherent_twistedModuleUlift_structureSheafPushforward`. -/
theorem intersectionNumber_eq_add_of_iso_tensorSheaf_of_totalDegree_le (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d) (i₀ : Fin d)
    (L L' L'' : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L' j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L'' j)]
    (hL' : ∀ j, j ≠ i₀ → L' j = L j) (hL'' : ∀ j, j ≠ i₀ → L'' j = L j)
    (hL : L i₀ ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).obj (L' i₀)).obj (L'' i₀) :
        Modules.{u, u} B (Spec (.of k)) hk X.1 X.2))
    (Q : MvPolynomial (Fin (d + 1)) ℚ) (hQdeg : Q.totalDegree ≤ d)
    (hQ : ∀ m : Fin (d + 1) → ℤ, MvPolynomial.eval (fun p => (m p : ℚ)) Q =
      ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) (Fin.cons (L'' i₀) L') m)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w}
            k B hk X Z f hf i hi (Fin.cons (L'' i₀) L') m) : ℤ) : ℚ)) :
    intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L =
      intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L' +
        intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L'' :=
  have : ∀ {r : ℕ} (M : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
      [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (M j)]
      (n : Fin r → ℤ), IsCoherent B (Spec (.of k)) hk X.1 X.2
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) M n) := fun M _ n =>
    isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w} k B hk X Z f hf i hi M n
  intersectionNumber_eq_add_of_iso_tensorSheaf.{u, w} k B hk X Z d f hf i hi hd i₀ L L' L''
    hL' hL'' hL Q hQdeg hQ

/-- **Stacks 0EDG.**  In the situation of Definition 0EDF — `X` a proper algebraic space over a
field `k`, `i : Z ⟶ X` a closed subspace of dimension `d` and `L₁, …, L_d` invertible
`𝒪_X`-modules — the intersection number `(L₁ ⋯ L_d · Z)` is an integer: the function
`n ↦ χ(X, i_*𝒪_Z ⊗ L₁^{⊗ n₁} ⊗ ⋯ ⊗ L_d^{⊗ n_d})` is the restriction to the integral tuples of a
rational polynomial of total degree at most `d`, and the coefficient of `n₁ ⋯ n_d` in any
rational polynomial with these values is the cast of an integer.

The first conjunct is Stacks 0DN4,
`AlgebraicGeometry.Space.exists_representsTwistedEuler_structureSheafPushforward`, and it is
what makes the second one say something about *the* numerical polynomial of the source: a
rational polynomial is determined by its values at the integral tuples
(`MvPolynomial.eq_of_eval_intCast_eq`), so every polynomial with these values is that one, and
`AlgebraicGeometry.Space.exists_intCast_eq_coeff_one` applies to it, the integer being
`AlgebraicGeometry.Space.intersectionNumber`. -/
@[stacks 0EDG, sga "6 X 2.3.1" "special case"]
theorem exists_eval_eq_eulerCharacteristic_and_exists_intCast_eq_coeff_one (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d)
    (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)] :
    (∃ P : MvPolynomial (Fin d) ℚ, (∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) L n)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w}
            k B hk X Z f hf i hi L n) : ℤ) : ℚ)) ∧ P.totalDegree ≤ d) ∧
    ∀ P : MvPolynomial (Fin d) ℚ, (∀ n : Fin d → ℤ, MvPolynomial.eval (fun j => (n j : ℚ)) P =
      ((@eulerCharacteristic.{u, w} k _ B hk X.1 X.2 f hf
        (twistedModuleUlift.{u, w} B (Spec (.of k)) hk X.1 X.2
          (structureSheafPushforward B (Spec (.of k)) hk i) L n)
          (isCoherent_twistedModuleUlift_structureSheafPushforward.{u, w}
            k B hk X Z f hf i hi L n) : ℤ) : ℚ)) →
      ∃ m : ℤ, P.coeff (Finsupp.equivFunOnFinite.symm fun _ => 1) = (m : ℚ) := by
  obtain ⟨P₀, hP₀, hdeg₀⟩ := exists_representsTwistedEuler_structureSheafPushforward.{u, w}
    k B hk X Z d f hf i hi hd L
  refine ⟨⟨P₀, hP₀, hdeg₀⟩, fun P hP => ?_⟩
  obtain rfl : P = P₀ := MvPolynomial.eq_of_eval_intCast_eq fun n => (hP n).trans (hP₀ n).symm
  exact exists_intCast_eq_coeff_one.{u, w} k B hk X Z d f hf i hi hd L P hP hdeg₀

/-- **Stacks 0EDH.**  In the situation of Definition 0EDF, the intersection number is additive
in each of its invertible modules: if `L_{i₀} ≅ L_{i₀}' ⊗ L_{i₀}''`, and `L'` and `L''` agree with
`L` away from `i₀`, then

`(L₁ ⋯ L_{i₀} ⋯ L_d · Z) = (L₁ ⋯ L_{i₀}' ⋯ L_d · Z) + (L₁ ⋯ L_{i₀}'' ⋯ L_d · Z)`.

The proof is the source's: by Stacks 0DN4
(`AlgebraicGeometry.Space.exists_representsTwistedEuler_structureSheafPushforward`) the twisted
Euler characteristics of `i_*𝒪_Z` by the `d + 1` invertible modules
`L_{i₀}'', L_1', …, L_d'` are the values of a numerical polynomial of total degree at most `d`
in `d + 1` variables, and
`AlgebraicGeometry.Space.intersectionNumber_eq_add_of_iso_tensorSheaf_of_totalDegree_le` reads
the three intersection numbers off it. -/
@[stacks 0EDH]
theorem intersectionNumber_eq_add_intersectionNumber_of_iso_tensorSheaf (d : ℕ)
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (hd : dimension B (Spec (.of k)) hk Z.1 Z.2 = d) (i₀ : Fin d)
    (L L' L'' : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L' j)]
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L'' j)]
    (hL' : ∀ j, j ≠ i₀ → L' j = L j) (hL'' : ∀ j, j ≠ i₀ → L'' j = L j)
    (hL : L i₀ ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).obj (L' i₀)).obj (L'' i₀) :
        Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)) :
    intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L =
      intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L' +
        intersectionNumber.{u, w} k B hk X Z d f hf i hi hd L'' :=
  let ⟨Q, hQ, hQdeg⟩ := exists_representsTwistedEuler_structureSheafPushforward.{u, w}
    k B hk X Z d f hf i hi hd (Fin.cons (L'' i₀) L')
  intersectionNumber_eq_add_of_iso_tensorSheaf_of_totalDegree_le.{u, w} k B hk X Z d f hf i hi hd
    i₀ L L' L'' hL' hL'' hL Q hQdeg hQ

end IntersectionNumber

end AlgebraicGeometry.Space

end
