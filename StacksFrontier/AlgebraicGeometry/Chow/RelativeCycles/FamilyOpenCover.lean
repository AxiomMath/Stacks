module

public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Restriction

/-!
# A family of cycles on fibres is determined by its restrictions to an open cover of the base

Let `p : W ⟶ T` be locally of finite type and let `r ≥ 0`. A family of `r`-cycles on the fibres of
`W/T` is determined by its restrictions `Stacks.Chow.restrictedFamily` to the base changes along
an open cover of `T`. The restriction along an open immersion `i : V ⟶ T` records the cycle over
`i t` through its coefficients at points of the fibre of `W ×_T V ⟶ V` over `t`, pulled back
along `AlgebraicGeometry.restrictedFiberMap`, and this comparison map is an isomorphism.

For a base which is a disjoint union `T = T₁ ⨿ T₂`, covered by the two coproduct injections, two
families of cycles agree as soon as they agree after restriction to each summand. This is the
rigidity half of the coproduct step in the proof of
[Tag 0H59](https://stacks.math.columbia.edu/tag/0H59); the coproduct clause itself is
`Stacks.Chow.pullbackInCycleClassImage_coprod_desc`.

## Main results

* `Stacks.Chow.isIso_restrictedFiberMap_of_isOpenImmersion` — along an open immersion of the
  base, the comparison morphism of fibres is an isomorphism.
* `Stacks.Chow.familyOfCycles_eq_of_openCover` — a family of cycles on fibres is determined by
  its restrictions to an open cover of the base.
* `Stacks.Chow.familyOfCycles_eq_of_coprod_base` — the case of a binary coproduct base.

## References

* [Stacks Project, Lemma 0H59](https://stacks.math.columbia.edu/tag/0H59)
* [Stacks Project, Lemma 0H4P](https://stacks.math.columbia.edu/tag/0H4P)
* [Stacks Project, Lemma 0H4T](https://stacks.math.columbia.edu/tag/0H4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v u

namespace Stacks.Chow

/-! ### The comparison morphism of fibres along an open immersion of the base -/

section OpenImmersion

variable {W T V : Scheme.{u}} (p : W ⟶ T) [LocallyOfFiniteType p] (i : V ⟶ T)
  [IsOpenImmersion i]

omit [LocallyOfFiniteType p] in
/-- For an open immersion `i : V ⟶ T` of the base, the comparison morphism from the fibre of
`W ×_T V ⟶ V` over `t` to the fibre of `W ⟶ T` over `i t` is an isomorphism. -/
theorem isIso_restrictedFiberMap_of_isOpenImmersion (t : V) :
    IsIso (restrictedFiberMap p (pullback.snd p i) (pullback.fst p i) i pullback.condition t) :=
  AlgebraicGeometry.isIso_baseChangeFiberMap p i t

omit [LocallyOfFiniteType p] in
/-- The comparison morphism of fibres along an open immersion of the base is surjective on
points. -/
theorem surjective_restrictedFiberMap_of_isOpenImmersion (t : V) :
    Function.Surjective
      (restrictedFiberMap p (pullback.snd p i) (pullback.fst p i) i pullback.condition t) := by
  have := isIso_restrictedFiberMap_of_isOpenImmersion p i t
  exact (inferInstance : Surjective _).surj

/-- Two families of cycles on the fibres of `W/T` with the same restriction along an open
immersion `i : V ⟶ T` have the same member over every point in the range of `i`. -/
theorem fiberCycle_eq_of_restrictedFamily_eq {r : ℕ} (β γ : FamilyOfCycles p r)
    (h : (restrictedFamily p (pullback.snd p i) (pullback.fst p i) i pullback.condition r β).1 =
      (restrictedFamily p (pullback.snd p i) (pullback.fst p i) i pullback.condition r γ).1)
    (t : V) : β (i t) = γ (i t) := by
  refine Subtype.ext <| Function.locallyFinsuppWithin.ext fun y => ?_
  obtain ⟨x, rfl⟩ := surjective_restrictedFiberMap_of_isOpenImmersion p i t y
  simpa only [(restrictedFamily p (pullback.snd p i) (pullback.fst p i) i
      pullback.condition r β).2 t x,
    (restrictedFamily p (pullback.snd p i) (pullback.fst p i) i pullback.condition r γ).2 t x]
    using congrArg (fun δ : FamilyOfCycles (pullback.snd p i) r =>
      (δ t : AlgebraicCycle ((pullback.snd p i).fiber t) ℤ) x) h

end OpenImmersion

/-! ### Rigidity along an open cover of the base -/

/-- **A family of cycles on fibres is determined by its restrictions to an open cover of the
base.** If two families have the same restriction along every member of a family of open
immersions into `T` whose ranges cover `T`, they are equal. -/
theorem familyOfCycles_eq_of_openCover {W T : Scheme.{u}} (p : W ⟶ T) [LocallyOfFiniteType p]
    {r : ℕ} {ι : Type v} {V : ι → Scheme.{u}} (i : ∀ k, V k ⟶ T)
    [∀ k, IsOpenImmersion (i k)] (hcover : ∀ t : T, ∃ k, t ∈ Set.range (i k))
    (β γ : FamilyOfCycles p r)
    (h : ∀ k, (restrictedFamily p (pullback.snd p (i k)) (pullback.fst p (i k)) (i k)
        pullback.condition r β).1 =
      (restrictedFamily p (pullback.snd p (i k)) (pullback.fst p (i k)) (i k)
        pullback.condition r γ).1) :
    β = γ := by
  funext t
  obtain ⟨k, u, rfl⟩ := hcover t
  exact fiberCycle_eq_of_restrictedFamily_eq p (i k) β γ (h k) u

/-- **Rigidity for a base which is a binary coproduct.** Two families of cycles on the fibres of
`W ⟶ T₁ ⨿ T₂` are equal as soon as their restrictions along the two coproduct injections agree. -/
theorem familyOfCycles_eq_of_coprod_base {W T₁ T₂ : Scheme.{u}}
    (p : W ⟶ (T₁ ⨿ T₂ : Scheme.{u})) [LocallyOfFiniteType p] {r : ℕ}
    (β γ : FamilyOfCycles p r)
    (h₁ : (restrictedFamily p (pullback.snd p (coprod.inl : T₁ ⟶ T₁ ⨿ T₂))
        (pullback.fst p (coprod.inl : T₁ ⟶ T₁ ⨿ T₂)) coprod.inl pullback.condition r β).1 =
      (restrictedFamily p (pullback.snd p (coprod.inl : T₁ ⟶ T₁ ⨿ T₂))
        (pullback.fst p (coprod.inl : T₁ ⟶ T₁ ⨿ T₂)) coprod.inl pullback.condition r γ).1)
    (h₂ : (restrictedFamily p (pullback.snd p (coprod.inr : T₂ ⟶ T₁ ⨿ T₂))
        (pullback.fst p (coprod.inr : T₂ ⟶ T₁ ⨿ T₂)) coprod.inr pullback.condition r β).1 =
      (restrictedFamily p (pullback.snd p (coprod.inr : T₂ ⟶ T₁ ⨿ T₂))
        (pullback.fst p (coprod.inr : T₂ ⟶ T₁ ⨿ T₂)) coprod.inr pullback.condition r γ).1) :
    β = γ := by
  funext t
  obtain ⟨u | u, rfl⟩ := (coprodMk T₁ T₂).surjective t
  · rw [coprodMk_inl]
    exact fiberCycle_eq_of_restrictedFamily_eq p coprod.inl β γ h₁ u
  · rw [coprodMk_inr]
    exact fiberCycle_eq_of_restrictedFamily_eq p coprod.inr β γ h₂ u

end Stacks.Chow

end
