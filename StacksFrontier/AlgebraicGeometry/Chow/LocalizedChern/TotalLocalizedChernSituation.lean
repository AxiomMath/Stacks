module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.TotalLocalizedChern
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.ChernCommutation

/-!
# The total localized Chern class in Situation 0GUJ

Let `(S, δ)`, `i : Z ⟶ X`, `E` and `p` be as in Situation 0GUJ, with `E|_{X ∖ Z}` a finite locally
free module of rank `< p` placed in degree `0`. Remark 0FBC defines

  `c⁽ᵖ⁾(Z ⟶ X, E) = 1 + c₁(E) + … + c_{p-1}(E) + c_p(Z ⟶ X, E) + c_{p+1}(Z ⟶ X, E) + …`

as an element of the algebra `A⁽ᵖ⁾(Z ⟶ X)` of Remark 0FA0, with `c_i(Z ⟶ X, E)` the localized
Chern classes of Stacks 0FB2. This file defines that element, computes its components, and
identifies it with the class `Stacks.Chow.LocalizedChernData.totalLocalizedChern`, built from the
classes of Remark 0GUK.

## Main definitions

* `Stacks.Chow.LocalizedSituation.localizedChernOfLe` — the class `c_i(Z ⟶ X, E)` of Stacks 0FB2
  in an integer degree `i ≥ p`.
* `Stacks.Chow.LocalizedSituation.totalLocalizedChern` — the class `c⁽ᵖ⁾(Z ⟶ X, E)` of
  Remark 0FBC.

## Main results

* `Stacks.Chow.LocalizedSituation.totalLocalizedChern_fst`,
  `Stacks.Chow.LocalizedSituation.totalLocalizedChern_fst_zero`,
  `Stacks.Chow.LocalizedSituation.totalLocalizedChern_snd` — its components.
* `Stacks.Chow.LocalizedSituation.totalLocalizedChern_toLocalizedChernData` — it is the class
  built from the localized Chern classes of Remark 0GUK.

## References

* [Stacks Project, Tag 0FBC](https://stacks.math.columbia.edu/tag/0FBC)
* [Stacks Project, Tag 0FA0](https://stacks.math.columbia.edu/tag/0FA0)
* [Stacks Project, Tag 0FB2](https://stacks.math.columbia.edu/tag/0FB2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory StrictlyPerfect

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

namespace LocalizedSituation

variable {S : LocalizedSituation.{u}} (h : S.IsFiniteLocallyFreeOfRankLTOnComplement)

/-- **The localized Chern class `c_i(Z ⟶ X, E)` of Stacks 0FB2 in an integer degree `i ≥ p`**: the
class of Stacks 0FB2 for the situation at the cutoff `i`. -/
def localizedChernOfLe (i : {i : ℤ // (S.p : ℤ) ≤ i}) :
    BivariantClass S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl i.1 :=
  bivariantClassDegreeCongr S.base _ (S.i ≫ S.a) S.a S.i rfl
    (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg S.p) i.2))
    ((S.ofLe (q := i.1.toNat) (by have := i.2; omega)).localizedChern
      (h.ofLe (by have := i.2; omega)))

/-- **Stacks 0FBC: the total localized Chern class**
`c⁽ᵖ⁾(Z ⟶ X, E) = 1 + c₁(E) + … + c_{p-1}(E) + c_p(Z ⟶ X, E) + c_{p+1}(Z ⟶ X, E) + …` in the
algebra `A⁽ᵖ⁾(Z ⟶ X)` of Remark 0FA0, in Situation 0GUJ with `E|_{X ∖ Z}` finite locally free of
rank `< p` in degree `0`. Its component in a degree `i < p` is the Chern class `c_i(E) ∈ Aⁱ(X)`
(zero in the negative degrees, `1` in degree `0`), and in a degree `i ≥ p` it is the localized
Chern class `c_i(Z ⟶ X, E) ∈ Aⁱ(Z ⟶ X)` of Stacks 0FB2. -/
@[stacks 0FBC "the total localized Chern class c^(p)(Z → X, E) in A^(p)(Z → X), in Situation \
0GUJ, with the localized Chern classes of 0FB2"]
def totalLocalizedChern :
    localizedBivariantGrading S.base (gysinSystemOfInvertible S.base) (S.i ≫ S.a) S.a S.i rfl S.p :=
  ⟨fun i => (perfectChernClass S.base S.a S.hasDefinedChernClasses_E).intComponent S.base S.a i.1,
    localizedChernOfLe h⟩

/-- The components of `c⁽ᵖ⁾(Z ⟶ X, E)` in the degrees `i < p` are the Chern classes `c_i(E)`
(zero in the negative degrees). -/
@[stacks 0FBC "the components c_i(E) in the degrees i < p"]
theorem totalLocalizedChern_fst (i : {i : ℤ // i < (S.p : ℤ)}) :
    (totalLocalizedChern h).1 i =
      (perfectChernClass S.base S.a S.hasDefinedChernClasses_E).intComponent S.base S.a i.1 :=
  rfl

/-- For `p > 0` the component of `c⁽ᵖ⁾(Z ⟶ X, E)` in degree `0` is `c₀(E) = 1`, the leading term
`1` of the display of Remark 0FBC. -/
@[stacks 0FBC "the leading term 1 = c_0(E) when p > 0"]
theorem totalLocalizedChern_fst_zero (hp : 0 < S.p) :
    (totalLocalizedChern h).1 ⟨0, by exact_mod_cast hp⟩ =
      (1 : TotalChowClass S.base S.a).intComponent S.base S.a 0 := by
  rw [totalLocalizedChern_fst]
  change (perfectChernClass S.base S.a S.hasDefinedChernClasses_E).intComponent S.base S.a
      ((0 : ℕ) : ℤ) = (1 : TotalChowClass S.base S.a).intComponent S.base S.a ((0 : ℕ) : ℤ)
  rw [TotalChowClass.intComponent_natCast, TotalChowClass.intComponent_natCast]
  exact perfectChernClass_apply_zero S.base S.a S.hasDefinedChernClasses_E

/-- The components of `c⁽ᵖ⁾(Z ⟶ X, E)` in the degrees `i ≥ p` are the localized Chern classes
`c_i(Z ⟶ X, E)` of Stacks 0FB2. -/
@[stacks 0FBC "the components c_i(Z → X, E) of 0FB2 in the degrees i ≥ p"]
theorem totalLocalizedChern_snd (i : {i : ℤ // (S.p : ℤ) ≤ i}) :
    (totalLocalizedChern h).2 i = localizedChernOfLe h i :=
  rfl

/-- **In Situation 0GUJ the class `c⁽ᵖ⁾(Z ⟶ X, E)` of Remark 0FBC is the class
`Stacks.Chow.LocalizedChernData.totalLocalizedChern`** built from the localized Chern classes of
Remark 0GUK: in each degree `i ≥ p` the class of Remark 0GUK is that of Stacks 0FB2
(`Stacks.Chow.LocalizedSituation.localizedChern_toLocalizedChernData`). -/
theorem totalLocalizedChern_toLocalizedChernData :
    S.toLocalizedChernData.totalLocalizedChern S.hasDefinedChernClasses_E h =
      totalLocalizedChern h := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · exact LocalizedChernData.totalLocalizedChern_fst _ _ i
  · have hq : S.p ≤ i.1.toNat := by have := i.2; omega
    rw [LocalizedChernData.totalLocalizedChern_snd, totalLocalizedChern_snd,
      LocalizedChernData.localizedChernOfLe, localizedChernOfLe]
    exact congrArg _ (localizedChern_toLocalizedChernData (S := S.ofLe hq) (h.ofLe hq))

end LocalizedSituation

end Stacks.Chow

end
