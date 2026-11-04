module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.VanishingUnconditional

/-!
# Total classes are determined on integral schemes, up to modification

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project. By
[Stacks, Tag 02UC] a bivariant class is zero as soon as every integral scheme `T` locally of
finite type over `Y` has a proper birational modification `T' ⟶ T` whose fundamental class it
kills. Applied degreewise to the difference of two total Chow cohomology classes, this says that
two total classes agree as soon as their operations agree on the fundamental classes of such
modifications. This is the reduction to the integral case in the proof of [Stacks, Tag 0ESZ].

## Main results

* `Stacks.Chow.TotalChowClass.eq_of_op_fundamentalChowClass_eq`.

## References

* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow.TotalChowClass

variable {C : ChowSituation.{u}} {Y : Scheme.{u}} {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- **Total classes are determined on integral schemes, up to modification.** Two total Chow
cohomology classes of `Y` are equal if every integral scheme `T` locally of finite type over `Y`
admits a proper birational morphism `π : T' ⟶ T` such that the two classes operate identically
on the fundamental class `[T']`. -/
theorem eq_of_op_fundamentalChowClass_eq {c d : TotalChowClass C sY}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] [IsIntegral T],
      ∃ (T' : Scheme.{u}) (π : T' ⟶ T) (_ : IsProper π), IsBirational π ∧
        ∀ (k : ℤ) (p : ℕ), c.op (π ≫ g) k p (fundamentalChowClass C ((π ≫ g) ≫ sY) k) =
          d.op (π ≫ g) k p (fundamentalChowClass C ((π ≫ g) ≫ sY) k)) :
    c = d := by
  refine ext fun p ↦ sub_eq_zero.1 ?_
  refine ((BivariantClass.eq_zero_tfae_canonical C sY sY (𝟙 Y) (Category.id_comp sY) (p : ℤ)
    (c p - d p)).out 3 1).1 ?_
  intro T g _ _
  obtain ⟨T', π, hπ, hbir, hk⟩ := h g
  refine ⟨T', π, hπ, hbir, fun k ↦ ?_⟩
  refine chowPushforwardOfIso_injective C _ _ (pullback.snd (𝟙 Y) (π ≫ g))
    (pullbackSnd_comp_structureMorphism (Category.id_comp sY) (π ≫ g)) (k - p) ?_
  rw [map_zero]
  change (c p - d p).idRule C sY (gysinSystemOfInvertible C) (π ≫ g) k _ = 0
  rw [BivariantClass.idRule_sub, sub_eq_zero]
  exact hk k p

end Stacks.Chow.TotalChowClass

end
