module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.MotivesMonoidal
public import StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTateRealization

/-!
# The realization of the Tate motives in graded vector spaces

Let `k` be a field and `F` a field. Let `G : M_k ⥤ GradedObject ℤ (ModuleCat F)` be a monoidal
functor from Chow motives to `ℤ`-graded `F`-vector spaces with `G(𝟏(1))` concentrated in degree
`-2`. This file proves the second paragraph of the proof of Stacks 0FH1: choosing a basis
`e₁` of `G(𝟏(1))⁻²`, that is an isomorphism `F[2] → G(𝟏(1))`, there are compatible isomorphisms
`F[2n] → G(𝟏(n))` for all `n : ℤ`. Concretely, `G(𝟏(n))` is one dimensional in degree `-2n` and
zero elsewhere, and there are nonzero `eₙ ∈ G(𝟏(n))^{-2n}` with `e₁` the chosen element, `e₀`
the unit of `G`, and `eₙ ⊗ eₘ ↦ e_{n+m}` under the tensorator of `G` followed by
`G(𝟏(n) ⊗ 𝟏(m) ≅ 𝟏(n + m))`. Only the monoidal structure of `G` is used, not a braiding.

## Main definitions

* `Stacks.WeilCohomology.ChowMotiveCat.tateGen`: the generators `eₙ ∈ G(𝟏(n))^{-2n}`.

## Main results

* `Stacks.WeilCohomology.ChowMotiveCat.isZero_tate_apply` and
  `Stacks.WeilCohomology.ChowMotiveCat.finrank_tate_apply`: `G(𝟏(n))` lives in degree `-2n`,
  where it is one dimensional.
* `Stacks.WeilCohomology.ChowMotiveCat.tateGen_one`, `tateGen_zero`, `tateGen_mul`: the
  properties of the generators; they are nonzero by
  `CategoryTheory.GradedCategory.TwistedKaroubi.tateGen_ne_zero`.

## Implementation notes

Everything is proved for an arbitrary graded monoidal category in
`StacksFrontier.CategoryTheory.Graded.TwistedKaroubiTateRealization`, for the twisted units
`(𝟙, 𝟙, n)` of its twisted Karoubi envelope; the Tate motive `𝟏(n)` is the twisted unit of the
graded category of correspondences, and `tateTensorIso` is the product of twisted units, so the
results specialise on the nose.

## References

* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory GradedObject GradedObject.Monoidal
open CategoryTheory.GradedCategory
open scoped TensorProduct

universe u w

namespace Stacks.WeilCohomology.ChowMotiveCat

variable {k : Type u} [Field k] {F : Type w} [Field F]
  {G : ChowMotiveCat k ⥤ GradedObject ℤ (ModuleCat.{w} F)} [G.Monoidal]
  (hG : ∀ i, i ≠ -2 → IsZero ((G.obj (tate k 1)) i))
include hG

/-- **Stacks 0FH1, the degrees of the Tate motives.** If `G(𝟏(1))` is concentrated in degree
`-2`, then `G(𝟏(n))` is zero outside degree `-2n`. -/
theorem isZero_tate_apply (n i : ℤ) (hi : i ≠ -2 * n) : IsZero ((G.obj (tate k n)) i) :=
  TwistedKaroubi.isZero_tateTriple_apply hG n i hi

/-- **Stacks 0FH1, the degrees of the Tate motives.** If `G(𝟏(1))` is concentrated in degree
`-2`, then `G(𝟏(n))` is one dimensional in degree `-2n`. -/
theorem finrank_tate_apply (n : ℤ) : Module.finrank F ((G.obj (tate k n)) (-2 * n)) = 1 :=
  TwistedKaroubi.finrank_tateTriple_apply hG n

variable {e₁ : (G.obj (tate k 1)) (-2)} (he₁ : e₁ ≠ 0)
include he₁

/-- **Stacks 0FH1, the isomorphisms `F[2n] → G(𝟏(n))`.** The generator
`eₙ ∈ G(𝟏(n))^{-2n}` determined by a nonzero `e₁ ∈ G(𝟏(1))⁻²`. -/
noncomputable def tateGen (n : ℤ) : (G.obj (tate k n)) (-2 * n) :=
  TwistedKaroubi.tateGen hG he₁ n

/-- The generator `e₁` is the chosen nonzero element of `G(𝟏(1))⁻²`. -/
theorem tateGen_one : tateGen hG he₁ 1 = e₁ :=
  TwistedKaroubi.tateGen_one hG he₁

/-- `e₀` is the image of `1` under the unit `ε : 𝟏 ⟶ G(𝟏)` of `G`, through `𝟏(0) = 𝟏`. -/
theorem tateGen_zero :
    tateGen hG he₁ 0 =
      (Functor.LaxMonoidal.ε G 0) ((tensorUnit₀ (I := ℤ) (C := ModuleCat.{w} F)).inv (1 : F)) :=
  eq_of_heq (TwistedKaroubi.tateGen_zero_heq hG he₁)

/-- **Stacks 0FH1, compatibility with tensor products.** `eₙ ⊗ eₘ ↦ e_{n+m}` under the
tensorator `G(𝟏(n)) ⊗ G(𝟏(m)) ⟶ G(𝟏(n) ⊗ 𝟏(m))` followed by `G(𝟏(n) ⊗ 𝟏(m) ≅ 𝟏(n + m))`. -/
theorem tateGen_mul (n m : ℤ) :
    (ιTensorObj (G.obj (tate k n)) (G.obj (tate k m)) (-2 * n) (-2 * m) (-2 * (n + m))
        (by ring) ≫ Functor.LaxMonoidal.μ G (tate k n) (tate k m) (-2 * (n + m)) ≫
        (G.map (tateTensorIso n m).hom) (-2 * (n + m))) (tateGen hG he₁ n ⊗ₜ tateGen hG he₁ m) =
      tateGen hG he₁ (n + m) := by
  have h := TwistedKaroubi.tateMul_tateGen hG he₁ n m
  rw [TwistedKaroubi.tateMul_apply, TwistedKaroubi.unitTwistTensorIsoOfEq_hom_rfl] at h
  exact h

end Stacks.WeilCohomology.ChowMotiveCat
