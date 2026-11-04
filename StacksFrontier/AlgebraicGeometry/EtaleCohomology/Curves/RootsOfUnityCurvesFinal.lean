module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityAffineCurvePicardScheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityPicardScheme
public import StacksFrontier.AlgebraicGeometry.Picard.PicardSchemeCurve
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement

/-!
# Étale cohomology of `μ_n` on smooth curves

The statements of record of [Stacks, Tag 03RQ] (smooth projective curves) and [Stacks, Tag 03RR]
(affine smooth curves) over an algebraically closed field, with every input discharged.

Both were proved earlier over a Jacobian of the (compactified) curve and the rank of multiplication
by `n` on it. The Jacobian is `Pic⁰_{X/k}` (`Stacks.PicardFunctor.picardDegreeZeroSubgroup`): the
Picard functor is representable ([Stacks, Tag 0B9Z],
`Stacks.PicardFunctor.isRepresentable_picardFunctor_of_isSepClosed`), its degree-zero component is
a smooth proper variety of dimension the genus (clause (1) of [Stacks, Tag 0BA0]); both are
`Stacks.AbelMap.picardDegreeZero_inputs_of_isSepClosed`, it is quasi-projective ([Stacks, Tag
0BF7]), and the rank of `[n]` is [Stacks, Tag 0BFG] with the theorem of the cube
`Stacks.Cube.hasTheoremOfTheCube`. The big fppf site, the rational point and geometric
irreducibility needed to speak of the Picard scheme come from
`AlgebraicGeometry.exists_bigFppfSite_picardData`.

## Main results

* `AlgebraicGeometry.etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification`:
  **[Stacks, Tag 03RR]**.
* `AlgebraicGeometry.etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus`:
  **[Stacks, Tag 03RQ]**.

## References

* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe t u

namespace AlgebraicGeometry

open Stacks.PicardFunctor Stacks.AbelMap

section RootsOfUnity

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] (E : BigEtaleSite.{u}) (hX : E.Contains X) (n : ℕ)
  [HasExt.{t} (Sheaf (SmallEtale.topology E X hX) AddCommGrpCat.{u})]

include f in
/-- **Stacks Project, Tag 03RR.** Let `X` be an affine smooth curve over an algebraically closed
field `k`, let `n ∈ k^*`, and let `j : X ⟶ X̄` be a smooth projective compactification, with `g`
the genus of `X̄` and `r` the number of points of `X̄ ∖ X`. Then
1. `H⁰_ét(X, μ_n) = μ_n(k)`;
2. `H¹_ét(X, μ_n) ≅ (𝐙/n𝐙)^{2g + r - 1}`;
3. `H^q_ét(X, μ_n) = 0` for `q ≥ 2`. -/
@[stacks 03RR]
theorem etaleCohomology_rootsOfUnity_affineSmoothCurve_of_compactification (hn : IsUnit (n : k))
    [IsAffine X] {Xbar : Scheme.{u}} (fbar : Xbar ⟶ Spec (.of k)) [IsCurve k fbar] [Smooth fbar]
    [IsProjectiveVariety k fbar] (j : X ⟶ Xbar) [IsOpenImmersion j] (hj : j ≫ fbar = f)
    (r : ℕ) (hr : Nat.card ↥(Set.range j.base)ᶜ = r) :
    Function.Bijective (baseRootsToEtaleH0 E k X hX f n) ∧
      Nonempty (Sheaf.H (kummerSmallEtale E X hX n).X₁ 1 ≃+
        (Fin (2 * genus fbar + r - 1) → ZMod n)) ∧
      ∀ q, 2 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale E X hX n).X₁ q) :=
  etaleCohomology_rootsOfUnity_affineSmoothCurve_of_picardInputs k X f E hX n hn fbar j hj r hr
    fun B hXb hk fb σ hσ _ _ _ _ => picardDegreeZero_inputs_of_isSepClosed B hXb hk fb σ hσ

end RootsOfUnity

section ProjectiveCurve

variable (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [IsCurve k f] [IsProjectiveVariety k f] [Smooth f] (E : BigEtaleSite.{u}) (hX : E.Contains X)
  (n : ℕ) [HasExt.{t} (Sheaf (SmallEtale.topology E X hX) AddCommGrpCat.{u})]

/-- **Stacks Project, Tag 03RQ.** Let `X` be a smooth projective curve of genus `g` over an
algebraically closed field `k` and let `n ∈ k^*`. Then
`H⁰_ét(X, μ_n) = μ_n(k)`, `H¹_ét(X, μ_n) = Pic⁰(X)[n] ≅ (𝐙/n𝐙)^{2g}`,
`H²_ét(X, μ_n) ≅ 𝐙/n𝐙` (by the degree), `H^q_ét(X, μ_n) = 0` for `q ≥ 3`; and the same groups
for the constant sheaf `𝐙/n𝐙`: `𝐙/n𝐙`, `(𝐙/n𝐙)^{2g}`, `𝐙/n𝐙` and `0` for `q ≥ 3`. -/
@[stacks 03RQ]
theorem etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_genus (hn : IsUnit (n : k)) :
    Function.Bijective (baseRootsToEtaleH0 E k X hX f n) ∧
      Function.Bijective (etaleH1RootsOfUnityToCurvePicardDegreeZeroTorsion k X f E hX n hn) ∧
      (∃ e : Sheaf.H (kummerSmallEtale E X hX n).X₁ 2 ≃+ ZMod n,
        ∀ x, e (etaleH2RootsOfUnityFromPicard k X f E hX n hn x) = picardDegreeZMod k X f n x) ∧
      (∀ q, 3 ≤ q → Subsingleton (Sheaf.H (kummerSmallEtale E X hX n).X₁ q)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) 0 ≃+ ZMod n) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) 1 ≃+
        (Fin (2 * genus f) → ZMod n)) ∧
      Nonempty (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) 2 ≃+ ZMod n) ∧
      ∀ q, 3 ≤ q → Subsingleton (Sheaf.H (smallEtaleConstantZModSheaf E X hX n) q) :=
  etaleCohomology_rootsOfUnity_smoothProjectiveCurve_of_picardInputs k X f n E hX hn
    fun B hXb hk fb σ hσ _ _ _ _ => picardDegreeZero_inputs_of_isSepClosed B hXb hk fb σ hσ

end ProjectiveCurve

end AlgebraicGeometry
