module

public import StacksFrontier.AlgebraicGeometry.DivisorSum.FittingFiltrations
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleGradedSections

/-!
# The sections of 0ESU's two filtrations on an affine open carrying local equations

`AlgebraicGeometry.mem_fittingIncr_iff` and `AlgebraicGeometry.mem_fittingDecr_iff` describe
membership in the two global subsheaves `AlgebraicGeometry.fittingIncr` and
`AlgebraicGeometry.fittingDecr` of Stacks tag 0ESU over an affine open carrying local equations
`e_1, …, e_N` for the divisors. This file packages those two descriptions as *equalities of
submodules* of `Γ(ℱ, V)`:

```
𝐹ⁱ(V) = Stacks.FittingFiltration.incr Γ(ℱ, V) e N i,
𝐹_{i+1}(V) = Stacks.FittingFiltration.decr Γ(ℱ, V) e N (i + 1).
```

That is the form the ring-level filtration theory `Stacks.FittingFiltration` consumes:
its graded pieces, their Fitting ideals and their finite local freeness are all stated for
`Stacks.FittingFiltration.incr` and `Stacks.FittingFiltration.decr`, so with these two equalities
the sections of a graded piece of either filtration — which
`AlgebraicGeometry.submoduleGradedSectionsEquiv` computes as a
`Stacks.FittingFiltration.gradedQuot` — become the graded piece the ring-level theory knows
about.

## Main results

* `AlgebraicGeometry.sectionsSubmodule_fittingIncr` and
  `AlgebraicGeometry.sectionsSubmodule_fittingDecr`: the two equalities above.

## References

* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Divisors

universe u

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {F : X.Modules}

/-- **The increasing filtration of Stacks tag 0ESU on an affine open, as a submodule of the
sections.** On an affine open carrying local equations `e_1, …, e_N` for the divisors, the
sections of `Fⁱ` are the local increasing filtration `Stacks.FittingFiltration.incr` of
`Γ(ℱ, V)`, namely the multiples of `e_{i+1} ⋯ e_N`. -/
theorem sectionsSubmodule_fittingIncr [F.IsQuasicoherent] {D : ℕ → X.IdealSheafData}
    (hD : IsLocallyFiniteFamily D) (V : X.affineOpens) {N : ℕ} {e : ℕ → Γ(X, V.1)}
    (hlow : ∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)})
    (htop : ∀ j, N ≤ j → (D j).ideal V = ⊤) (i : ℕ) :
    sectionsSubmodule (fittingIncr D F i) V.1
      = Stacks.FittingFiltration.incr Γ(F, V.1) e N i := by
  refine Submodule.ext fun s => ?_
  rw [mem_sectionsSubmodule, mem_fittingIncr_iff F hD V hlow htop i s]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, ht⟩, fun ⟨t, ht⟩ => ⟨t, ht⟩⟩

/-- **The decreasing filtration of Stacks tag 0ESU on an affine open, as a submodule of the
sections.** On an affine open carrying local equations `e_1, …, e_N` for the divisors, the
sections of `F_{i+1}` are the local decreasing filtration `Stacks.FittingFiltration.decr` of
`Γ(ℱ, V)`, namely the sections killed by `e_{i+1} ⋯ e_N`. -/
theorem sectionsSubmodule_fittingDecr [F.IsQuasicoherent] {D : ℕ → X.IdealSheafData}
    (hD : IsLocallyFiniteFamily D) (V : X.affineOpens) {N : ℕ} {e : ℕ → Γ(X, V.1)}
    (hlow : ∀ j, j + 1 ≤ N → (D j).ideal V = Ideal.span {e (j + 1)})
    (htop : ∀ j, N ≤ j → (D j).ideal V = ⊤) (i : ℕ) :
    sectionsSubmodule (fittingDecr D F (i + 1)) V.1
      = Stacks.FittingFiltration.decr Γ(F, V.1) e N (i + 1) := by
  refine Submodule.ext fun s => ?_
  rw [mem_sectionsSubmodule, mem_fittingDecr_iff F hD V hlow htop i s]
  exact ⟨fun h => h, fun h => h⟩

end AlgebraicGeometry

end
