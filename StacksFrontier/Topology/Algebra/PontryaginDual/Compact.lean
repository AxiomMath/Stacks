module

public import StacksFrontier.Topology.Algebra.PontryaginDual.CompactSeparatesPoints
public import StacksFrontier.Topology.Algebra.PontryaginDual.Discrete
public import StacksCore.Tactic.StacksAttribute

/-!
# Pontryagin duality for compact abelian groups

Let `A` be a compact Hausdorff abelian group. The evaluation map
`A → PontryaginDual (PontryaginDual A)` is bijective, using that the characters of a compact
Hausdorff abelian group separate its points (`Stacks.Pontryagin.exists_apply_ne_one`).
Injectivity is separation of points of `A`, and if the (compact, hence closed) image were proper,
a character of the nontrivial compact quotient would give a nontrivial character of
`PontryaginDual (PontryaginDual A)` vanishing on the image; by duality for the discrete group
`PontryaginDual A` it is evaluation at some character
`ψ` of `A`, and vanishing on the image forces `ψ = 1`. A continuous bijection from a compact
space to a Hausdorff space is a homeomorphism.

## Main definitions

* `Stacks.Pontryagin.doubleDualEquivOfCompactSpace`: for `A` compact Hausdorff, the evaluation map
  `A ≃ₜ* PontryaginDual (PontryaginDual A)`.

## Main results

* `Stacks.Pontryagin.eval_bijective_of_compactSpace_of_separatesPoints`: the evaluation map of a
  compact Hausdorff abelian group is bijective, given separation of points by characters for
  compact Hausdorff abelian groups.
* `Stacks.Pontryagin.eval_bijective_of_compactSpace`: the evaluation map of a compact Hausdorff
  abelian group is bijective.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.Pontryagin

variable (A : Type u) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
  [T2Space A]

omit [IsTopologicalGroup A] in
/-- The image of the evaluation map of a compact group is closed. -/
theorem isClosed_range_eval :
    IsClosed ((eval A).toMonoidHom.range : Set (PontryaginDual (PontryaginDual A))) :=
  (isCompact_range (eval A).continuous).isClosed

/-- The evaluation map of a compact Hausdorff abelian group `A` is bijective, provided the
characters of every compact Hausdorff abelian group in the universe of `A` separate its points. -/
theorem eval_bijective_of_compactSpace_of_separatesPoints
    (hsep : ∀ (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] (g : G), g ≠ 1 → ∃ χ : PontryaginDual G, χ g ≠ 1) :
    Function.Bijective (eval A) := by
  refine ⟨(eval_injective_iff).mpr fun a b hab ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨χ, hχ⟩ := hsep A (a / b) (div_ne_one.mpr hab)
    refine ⟨χ, fun h ↦ hχ ?_⟩
    rw [map_div, h, div_self']
  · by_contra hy
    let H : Subgroup (PontryaginDual (PontryaginDual A)) := (eval A).toMonoidHom.range
    have : IsClosed (H : Set (PontryaginDual (PontryaginDual A))) := isClosed_range_eval A
    obtain ⟨θ, hθ⟩ := hsep (PontryaginDual (PontryaginDual A) ⧸ H) (QuotientGroup.mk y) (by
      rw [Ne, QuotientGroup.eq_one_iff]
      rintro ⟨a, rfl⟩
      exact hy ⟨a, rfl⟩)
    let Ψ : PontryaginDual (PontryaginDual (PontryaginDual A)) :=
      θ.comp ⟨QuotientGroup.mk' H, continuous_quot_mk⟩
    obtain ⟨ψ, hψ⟩ := eval_surjective_of_discreteTopology (PontryaginDual A) Ψ
    have hψ1 : ψ = 1 := by
      refine PontryaginDual.ext fun a ↦ ?_
      have h := DFunLike.congr_fun hψ (eval A a)
      change ψ a = θ (QuotientGroup.mk (eval A a)) at h
      rw [h, (QuotientGroup.eq_one_iff (N := H) (eval A a)).mpr ⟨a, rfl⟩, _root_.map_one]
      rfl
    apply hθ
    have h := DFunLike.congr_fun hψ y
    rw [hψ1, _root_.map_one] at h
    exact h.symm

/-- The evaluation map of a compact Hausdorff abelian group is bijective. -/
theorem eval_bijective_of_compactSpace : Function.Bijective (eval A) :=
  eval_bijective_of_compactSpace_of_separatesPoints A fun _ _ _ _ _ _ _ hg ↦
    exists_apply_ne_one hg

/-- Pontryagin duality for a compact Hausdorff abelian group `A`: the evaluation map is an
isomorphism of topological groups `A ≃ₜ* PontryaginDual (PontryaginDual A)`. -/
@[stacks 03VI "Pontryagin duality: a compact abelian group is its double dual"]
def doubleDualEquivOfCompactSpace : A ≃ₜ* PontryaginDual (PontryaginDual A) :=
  let e : A ≃* PontryaginDual (PontryaginDual A) :=
    MulEquiv.ofBijective (eval A) (eval_bijective_of_compactSpace A)
  { e with
    continuous_toFun := (eval A).continuous
    continuous_invFun :=
      ((eval A).continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

/-- The compact double dual isomorphism is the evaluation map. -/
@[simp]
theorem doubleDualEquivOfCompactSpace_apply (a : A) :
    doubleDualEquivOfCompactSpace A a = eval A a :=
  rfl

end Stacks.Pontryagin
