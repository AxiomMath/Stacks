module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwistHom
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleZeroSupport
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.ZeroDimensionalTensor

/-!
# The support of a twist, and the twists of a short exact sequence with vanishing kernel

Two bookkeeping steps of [Stacks, Tag 0F27].

The first is that twisting does not move the support: the punctured-spectrum member of every
integer twist of a coherent triple has the same support as the member of the triple. So the
degree bound `dim(Supp F)` of that tag is a bound attached to the whole family of twists at once,
not to any one of them.

The second is the opening move of the induction step of that tag. There the triple
`(F, F₀, α)` is replaced by `(F, F₀/G₀, α)`, where `G₀ ⊆ F₀` is the submodule of sections
supported at the closed point, and the two are compared through the short exact sequence

`0 → (0, G₀, 0) → (F, F₀, α) → (F, F₀/G₀, α) → 0`

whose first member has vanishing punctured-spectrum member. Twisting such a sequence and using
additivity of the Euler characteristic shows that the two functions `n ↦ χ` differ by the
*constant* `χ(0, G₀, 0)` — the first member's Euler characteristic, which the base case of the
tag shows does not depend on `n`. Hence one of the two functions is a polynomial of degree at
most `d` exactly when the other is, for any `d`.

## Main results

* `Stacks.Algebraization.supp_tensorModules_of_isInvertible`: the support of a tensor product
  with an invertible module is the support of the other factor.
* `Stacks.Algebraization.CoherentTriple.supp_twistZ_F`: twisting does not move the support of
  the punctured-spectrum member.
* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_twistZ_eq_add_of_shortExact_isZero`:
  the Euler characteristics of the twists of the middle and the right member of such a sequence
  differ by a constant.
* `Stacks.Algebraization.exists_polynomial_eulerCharacteristic_twistZ_of_shortExact_isZero`:
  polynomiality of a given degree transfers across such a sequence.

## Implementation notes

The support of a tensor product is contained in the support of either factor
(`AlgebraicGeometry.notMem_supp_tensorSheaf_of_notMem_supp`), with no hypothesis on the factors.
The reverse containment for an invertible second factor comes from applying that containment to
`(F ⊗ L) ⊗ L^{⊗ -1}`, which is `F` by the associativity and unit constraints of the tensor
product and the addition law for the tensor powers at the exponent `-1`
(`Stacks.Algebraization.tensorPowSchemeNegOneIso`).

The constant in the second statement is produced by
`Stacks.Algebraization.CoherentTriple.eulerCharacteristic_twistZ_eq_of_isZero`, the base case of
the tag, applied to the left member of the sequence; the sequence is carried to the twists by
`Stacks.Algebraization.CoherentTriple.ShortExact.twistZ`.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Algebraization

/-! ### The support of a tensor product with an invertible module -/

/-- **`F ⊗ L ⊗ L^{⊗ -1}` is `F`** for an invertible `L`: the associativity constraint, the
addition law for the tensor powers at the exponent `-1`, and the right unit constraint. -/
public noncomputable def tensorModulesTensorInverseIso (X : Scheme.{u}) (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    tensorModules X (tensorModules X F L) (tensorPowScheme X L (-1)) ≅ F :=
  Stacks.SheafOfModules.Invertible.tensorProductAssociator X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F L
      (tensorPowScheme X L (-1)) ≪≫
    tensorModulesMapIso X (Iso.refl F)
      (tensorModulesBraidingIso X L (tensorPowScheme X L (-1)) ≪≫
        tensorPowSchemeNegOneIso X L) ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F

/-- **The support of a tensor product with an invertible module is the support of the other
factor.** -/
public theorem supp_tensorModules_of_isInvertible (X : Scheme.{u}) (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    SheafOfModules.supp (tensorModules X F L) = SheafOfModules.supp F := by
  refine Set.Subset.antisymm (fun y hy => ?_) (fun y hy => ?_)
  · by_contra h
    exact AlgebraicGeometry.notMem_supp_tensorSheaf_of_notMem_supp F L h hy
  · by_contra h
    let := isInvertibleModule_tensorPowScheme X L (-1)
    refine (SheafOfModules.supp_eq_of_iso (tensorModulesTensorInverseIso X F L) ▸ ?_ : y ∉ _) hy
    exact AlgebraicGeometry.notMem_supp_tensorSheaf_of_notMem_supp
      (tensorModules X F L) (tensorPowScheme X L (-1)) h

/-- **Twisting does not move the support of the punctured-spectrum member of a coherent
triple.** -/
public theorem CoherentTriple.supp_twistZ_F {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    (T L : CoherentTriple A f) (hL : IsInvertibleTriple L) (n : ℤ) :
    SheafOfModules.supp ((T.twistZ L hL n).F) = SheafOfModules.supp T.F :=
  let := hL.invertible_F
  let := isInvertibleModule_tensorPowScheme
    (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n
  supp_tensorModules_of_isInvertible (Stacks.Divisors.puncturedSpectrum A).toScheme T.F _

/-! ### A short exact sequence whose left member has vanishing punctured-spectrum member -/

/-- **The Euler characteristics of the twists of the middle and of the right member of a short
exact sequence of coherent triples whose left member has vanishing punctured-spectrum member
differ by a constant**, namely the Euler characteristic of the left member. -/
public theorem CoherentTriple.eulerCharacteristic_twistZ_eq_add_of_shortExact_isZero {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A)
    (hreg : IsRegular f) {K T S : CoherentTriple A f} {φ : K.Hom T} {ψ : T.Hom S}
    (hse : CoherentTriple.ShortExact φ ψ) (hK : IsZero K.F) (L : CoherentTriple A f)
    (hL : IsInvertibleTriple L) (n : ℤ) :
    (T.twistZ L hL n).eulerCharacteristic hf hreg =
      K.eulerCharacteristic hf hreg + (S.twistZ L hL n).eulerCharacteristic hf hreg := by
  rw [CoherentTriple.eulerCharacteristic_add_of_shortExact hf hreg (hse.twistZ L hL n),
    K.eulerCharacteristic_twistZ_eq_of_isZero hf hreg L hL hK n]

/-- **Polynomiality of a given degree transfers across a short exact sequence of coherent
triples whose left member has vanishing punctured-spectrum member.** This is the reduction with
which the induction step of [Stacks, Tag 0F27] opens: the triple may be replaced by the quotient
of it by the sections of its closed-fibre member supported at the closed point. -/
public theorem exists_polynomial_eulerCharacteristic_twistZ_of_shortExact_isZero {A : Type u}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A} (hf : f ∈ maximalIdeal A)
    (hreg : IsRegular f) {K T S : CoherentTriple A f} {φ : K.Hom T} {ψ : T.Hom S}
    (hse : CoherentTriple.ShortExact φ ψ) (hK : IsZero K.F) (L : CoherentTriple A f)
    (hL : IsInvertibleTriple L) {d : ℕ} {P : Polynomial ℚ} (hP : P.natDegree ≤ d)
    (hS : ∀ n : ℤ, (((S.twistZ L hL n).eulerCharacteristic hf hreg : ℤ) : ℚ) = P.eval (n : ℚ)) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ d ∧
      ∀ n : ℤ, (((T.twistZ L hL n).eulerCharacteristic hf hreg : ℤ) : ℚ) = Q.eval (n : ℚ) := by
  refine ⟨Polynomial.C ((K.eulerCharacteristic hf hreg : ℤ) : ℚ) + P, ?_, fun n => ?_⟩
  · exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (le_trans (Polynomial.natDegree_C _).le (Nat.zero_le d)) hP)
  · rw [CoherentTriple.eulerCharacteristic_twistZ_eq_add_of_shortExact_isZero hf hreg hse hK L
      hL n]
    simp only [Polynomial.eval_add, Polynomial.eval_C]
    rw [← hS n]
    push_cast
    ring

end Stacks.Algebraization

end
