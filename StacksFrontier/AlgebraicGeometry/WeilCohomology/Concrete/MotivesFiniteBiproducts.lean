module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesAdditive
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLineSummands
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceMonoidal
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiAdditive

/-!
# The category of Chow motives is additive

Stacks 0FGF: the category `M_k` of Chow motives over a field `k` is additive. It is preadditive,
being `ℚ`-linear (Stacks 0FGA), and it has a zero object and direct sums of motives with equal
twists (`StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesAdditive`, the direct sum
of
`(Y, p, m)` and `(Z, q, m)` being `(Y ⨿ Z, p + q, m)`). For motives `(Y, p, m)` and `(Z, q, n)`
with `n < m` the source reduces to equal twists by
`(Z, q, n) ≅ (Z, q, m) ⊗ (X, c₂, 0)^{⊗ (m - n)}`, `X = P¹_k`, using that the Lefschetz motive
`(X, c₂, 0)` is isomorphic to `𝟏(-1)` (Stacks 0FGD): that is
`CategoryTheory.GradedCategory.TwistedKaroubi.hasFiniteBiproducts_of_twist_eq`, applied with the
rational point `0` of `P¹_k`.

## Main definitions

* `Stacks.WeilCohomology.ChowMotiveCat.lefschetzKaroubi`: the Lefschetz motive `(P¹_k, c₂)` as a
  formal direct factor of the category of correspondences of degree zero, and
  `Stacks.WeilCohomology.ChowMotiveCat.lefschetzKaroubiIso`: `(P¹_k, c₂, 0) ≅ 𝟏(-1)`.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.hasFiniteBiproducts`: **Stacks 0FGF**, `M_k` has finite
  direct sums.

## References

* [Stacks Project, Tag 0FGF](https://stacks.math.columbia.edu/tag/0FGF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GradedCategory MonoidalCategory
  Idempotents AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology.ChowMotiveCat

variable {k : Type u} [Field k]
  (x : (fieldChowSituation k).S ⟶ relativeProjectiveLine (Spec (CommRingCat.of k)))
  (hx : x ≫ (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
    𝟙 (fieldChowSituation k).S)

/-- The Lefschetz motive `(P¹_k, c₂)` as a formal direct factor of the category of correspondences
of degree zero. -/
def lefschetzKaroubi : Karoubi (DegreeZero ℚ (CorrespondenceCategory k)) :=
  TwistedKaroubi.untwistOf (lefschetzMotive x hx)

/-- `(P¹_k, c₂, 0) ≅ 𝟏(-1)`: Stacks 0FGD (2), read on the formal direct factor `(P¹_k, c₂)`. -/
def lefschetzKaroubiIso :
    (TwistedKaroubi.untwisted ℚ (CorrespondenceCategory k)).obj (lefschetzKaroubi x hx) ≅
      TwistedKaroubi.tateTriple ℚ (CorrespondenceCategory k) (-1) :=
  projectiveLineFibrePointMotiveIso x hx

variable (k) in
/-- The rational point `0` of `P¹_k`. -/
def projectiveLineZero :
    (fieldChowSituation k).S ⟶ relativeProjectiveLine (Spec (CommRingCat.of k)) :=
  lineSection (Spec (CommRingCat.of k)) 0

/-- The rational point `0` of `P¹_k` is a section of the structure morphism `P¹_k → Spec k`. -/
theorem projectiveLineZero_comp :
    projectiveLineZero k ≫ (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘
      Spec (CommRingCat.of k)) = 𝟙 (fieldChowSituation k).S :=
  lineSection_comp _ 0

/-- The category `M_k` of Chow motives is additive: it is preadditive (`ℚ`-linear, Stacks 0FGA)
and has finite direct sums. A zero object is a motive with zero projector; two motives
`(Y, p, m)`, `(Z, q, m)` with the same twist have the direct sum `(Y ⨿ Z, p + q, m)`; and a
motive `(Z, q, n)` is isomorphic to `(Z, q, m) ⊗ (P¹_k, c₂, 0)^{⊗ (m - n)}`, of twist `m`, since
`(P¹_k, c₂, 0) ≅ 𝟏(-1)`. -/
@[stacks 0FGF "M_k is additive: finite direct sums, via (Y ⨿ Z, p + q, m) for equal twists and
(Z, q, n) ≅ (Z, q, m) ⊗ (P¹, c₂, 0)^{⊗(m-n)}"]
instance hasFiniteBiproducts : HasFiniteBiproducts (ChowMotiveCat k) :=
  TwistedKaroubi.hasFiniteBiproducts_of_twist_eq
    (lefschetzKaroubi (projectiveLineZero k) projectiveLineZero_comp)
    (lefschetzKaroubiIso (projectiveLineZero k) projectiveLineZero_comp)
    hasBinaryBiproduct_of_twist_eq

end Stacks.WeilCohomology.ChowMotiveCat
