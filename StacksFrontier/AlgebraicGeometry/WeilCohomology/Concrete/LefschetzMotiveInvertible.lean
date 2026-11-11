module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CorrespondenceMonoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLineSummands
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleTransport

/-!
# The Lefschetz motive is invertible

Let `k` be a field, `X = P¹_k`, `x` a `k`-rational point of `X` and `c₂ = [X × x]` the
idempotent of Example 0FG6. Remark 0FGE: the Lefschetz motive `L = (X, c₂, 0)` is isomorphic to
`1(-1) = (Spec k, 1, -1)` by Lemma 0FGD, hence it is invertible in the symmetric monoidal
category `M_k` (Categories, Definition 0FFN), with inverse the *Tate motive*
`1(1) = (Spec k, 1, 1)`, also written `L⁻¹`, `𝐋⁻¹`, `𝐓` or `𝐐(1)`.

## Main definitions

* `Stacks.WeilCohomology.ChowMotiveCat.lefschetzMotiveHasInverse`: **Stacks 0FGE**, a two-sided
  tensor inverse of the Lefschetz motive, whose inverse object is the Tate motive `1(1)`
  (`...lefschetzMotiveHasInverse_inv`).

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.isInvertible_lefschetzMotive`: **Stacks 0FGE**, the
  Lefschetz motive is invertible.

## Implementation notes

Everything is on the actual objects: `M_k` is `Stacks.WeilCohomology.ChowMotiveCat k` with the
symmetric monoidal structure of Stacks 0FGC, `L` is
`Stacks.WeilCohomology.ChowMotiveCat.lefschetzMotive x hx`, `1(n)` is
`Stacks.WeilCohomology.ChowMotiveCat.tate k n`. The proof is the remark's: the isomorphism
`L ≅ 1(-1)` of Lemma 0FGD (`...projectiveLineFibrePointMotiveIso`) carries the two-sided inverse
`1(1)` of `1(-1)` — `1(-1) ⊗ 1(1) ≅ 1(0) = 1` and `1(1) ⊗ 1(-1) ≅ 1`, which is
`CategoryTheory.GradedCategory.TwistedKaroubi.unitTwistHasInverse` — to `L`
(`CategoryTheory.MonoidalCategory.hasInverse_of_iso`).

## References

* [Stacks Project, Tag 0FGE](https://stacks.math.columbia.edu/tag/0FGE)
* [Stacks Project, Tag 0FGD](https://stacks.math.columbia.edu/tag/0FGD)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Stacks.Chow

universe u

namespace Stacks.WeilCohomology

namespace ChowMotiveCat

variable {k : Type u} [Field k]
  (x : (fieldChowSituation k).S ⟶ relativeProjectiveLine (Spec (CommRingCat.of k)))
  (hx : x ≫ (relativeProjectiveLine (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) =
    𝟙 (fieldChowSituation k).S)

/-- **Stacks Project, Tag 0FGE.** The Lefschetz motive `L = (P¹_k, c₂, 0)` is invertible in the
symmetric monoidal category `M_k`, with inverse the Tate motive `1(1) = (Spec k, 1, 1)`: a
two-sided tensor inverse `L ⊗ 1(1) ≅ 1`, `1(1) ⊗ L ≅ 1`, obtained by carrying the inverse
`1(1)` of `1(-1)` along the isomorphism `L ≅ 1(-1)` of Lemma 0FGD. -/
@[stacks 0FGE "the Lefschetz motive (P^1_k, c_2, 0) is invertible in M_k, with inverse the Tate
motive 1(1), via the isomorphism with 1(-1) of 0FGD; unconditional"]
def lefschetzMotiveHasInverse : HasInverse (lefschetzMotive x hx) :=
  hasInverse_of_iso (projectiveLineFibrePointMotiveIso x hx).symm
    (GradedCategory.TwistedKaroubi.unitTwistHasInverse (-1) 1 (by norm_num) :
      HasInverse (tate k (-1)))

/-- **Stacks Project, Tag 0FGE.** The inverse of the Lefschetz motive is the Tate motive
`1(1) = (Spec k, 1, 1)`, also written `L⁻¹`, `𝐋⁻¹`, `𝐓` or `𝐐(1)`. -/
@[stacks 0FGE "the inverse of the Lefschetz motive is the Tate motive 1(1) = (Spec k, 1, 1)"]
theorem lefschetzMotiveHasInverse_inv : (lefschetzMotiveHasInverse x hx).inv = tate k 1 :=
  rfl

/-- **Stacks Project, Tag 0FGE.** The Lefschetz motive is invertible in `M_k` in the sense of
Categories, Definition 0FFN, for every field `k` and `k`-rational point `x` of `P¹_k`. -/
@[stacks 0FGE "the Lefschetz motive is invertible in M_k (Categories, Definition 0FFN)"]
theorem isInvertible_lefschetzMotive : IsInvertible (lefschetzMotive x hx) :=
  ⟨lefschetzMotiveHasInverse x hx⟩

end ChowMotiveCat

end Stacks.WeilCohomology

end
