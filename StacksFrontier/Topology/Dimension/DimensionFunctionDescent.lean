module

public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary

/-!
# Descending a dimension function along a surjection

A dimension function on a topological space `A` descends along a continuous surjection
`π : A → C` as soon as three conditions hold: the function is constant on the fibres of `π`,
no fibre contains a specialization (so the fibres are discrete for the specialization order),
and generalizations lift along `π`. The descended function is then determined by
`D (π a) = d a`.

This is the topological content of the descent of a dimension function along a surjective
étale chart of an algebraic space (Stacks 0ED5): the three hypotheses are supplied there by
Tag 03K2 (generalizations lift along a flat morphism) and Tag 03K5 (two points of an étale
chart above the same point, one specializing to the other, are equal).

## Main results

* `TopologicalSpace.exists_dimensionFunction_of_descends`: the descent statement.

## References

* [Stacks Project, Tag 0ED5](https://stacks.math.columbia.edu/tag/0ED5)
* [Stacks Project, Tag 02I8](https://stacks.math.columbia.edu/tag/02I8)
-/

@[expose] public section

namespace TopologicalSpace

/-- A dimension function descends along a continuous surjection `π` which is constant on the
fibres, admits no specialization inside a fibre, and along which generalizations lift. The
descended function is the one determined by `D (π a) = d a`.

This is the topological step in the construction of a dimension function on an algebraic
space from one on an étale chart (Stacks 0ED5). -/
theorem exists_dimensionFunction_of_descends {A C : Type*} [TopologicalSpace A]
    [TopologicalSpace C] (π : A → C) (d : TopologicalSpace.DimensionFunction A)
    (hcont : Continuous π) (hsurj : Function.Surjective π)
    (hconst : ∀ a b : A, π a = π b → d a = d b)
    (hsep : ∀ a b : A, a ⤳ b → π a = π b → a = b)
    (hlift : ∀ y x : C, x ⤳ y → ∀ b : A, π b = y → ∃ a : A, a ⤳ b ∧ π a = x) :
    ∃ D : TopologicalSpace.DimensionFunction C, ∀ a : A, D (π a) = d a := by
  classical
  have hchoose : ∀ c : C, π (hsurj c).choose = c := fun c ↦ (hsurj c).choose_spec
  have hvalue : ∀ (x : C) (a : A), π a = x → d (hsurj x).choose = d a := fun x a hax ↦
    hconst _ _ ((hchoose x).trans hax.symm)
  have hstep : ∀ x y : C, x ⤳ y → x ≠ y →
      ∃ a : A, a ⤳ (hsurj y).choose ∧ π a = x ∧ a ≠ (hsurj y).choose := by
    intro x y hxy hne
    obtain ⟨a, ha, hax⟩ := hlift y x hxy (hsurj y).choose (hchoose y)
    refine ⟨a, ha, hax, fun hEq ↦ hne ?_⟩
    rw [← hax, hEq, hchoose y]
  refine ⟨⟨fun c ↦ d (hsurj c).choose, ?_, ?_⟩, fun a ↦ hvalue (π a) a rfl⟩
  · intro x y hxy hne
    obtain ⟨a, ha, hax, hane⟩ := hstep x y hxy hne
    show d (hsurj y).choose < d (hsurj x).choose
    rw [hvalue x a hax]
    exact d.strictAnti_specializes ha hane
  · intro x y himm
    obtain ⟨a, ha, hax, hane⟩ := hstep x y himm.1 himm.2.1
    show d (hsurj x).choose = d (hsurj y).choose + 1
    rw [hvalue x a hax]
    refine d.step_immediate ⟨ha, hane, fun z hz₁ hz₂ ↦ ?_⟩
    have h₁ : x ⤳ π z := by rw [← hax]; exact hz₁.map hcont
    have h₂ : π z ⤳ y := by rw [← hchoose y]; exact hz₂.map hcont
    rcases himm.2.2 (π z) h₁ h₂ with hz | hz
    · exact Or.inl (hsep a z hz₁ (hax.trans hz.symm)).symm
    · exact Or.inr (hsep z _ hz₂ (hz.trans (hchoose y).symm))

end TopologicalSpace

end
