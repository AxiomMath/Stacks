module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionOnePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.SizeBoundFieldPoints

/-!
# Axiom `[-1]` for Artin's contraction functor

In the situation of Stacks 0GH8, the functor `F` of Stacks 0GHA satisfies Artin's
set-theoretic condition `[-1]` of Stacks, Section 07XZ, in the form reviewed in Section 0GE6:
there is an object `T₀` of the big fppf site of `S` such that `#F(U) ≤ size T₀` for every locally
Noetherian object `U` whose underlying scheme is the spectrum of a field locally of finite type
over `S`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.contractionFunctor_sizeBounded`: axiom `[-1]`
  for `F`, the bound `#F(U) ≤ size T₀` above.

## References

* [Stacks Project, Tag 0GE6](https://stacks.math.columbia.edu/tag/0GE6)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GIB](https://stacks.math.columbia.edu/tag/0GIB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- **Axiom `[-1]` for Artin's contraction functor.** There is an object `T₀` of the big fppf
site of `S` such that the triples over any locally Noetherian object `U` whose underlying scheme
is the spectrum of a field locally of finite type over `S` number at most `size T₀`. -/
theorem contractionFunctor_sizeBounded :
    ∃ T₀ : BigFppfOver B S hS, ∀ (U : LocallyNoetherianOver B S hS) (K : Type u) [Field K],
      Nonempty ((LocallyNoetherianOver.toScheme B S hS).obj U ≅ Spec (.of K)) →
      LocallyOfFiniteType (B.inclusion.map U.obj.hom) →
      #((contractionFunctor c).obj (op U)) ≤
        Cardinal.lift.{u + 1} ((BigFppfOver.toScheme B S hS).obj T₀).size := by
  classical
  obtain ⟨ν₁, h₁S, h₁c, h₁⟩ := Space.exists_cardinal_bound_fieldPoints.{u + 1}
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff.{u + 1} B S hS c.X').2
      c.isAlgebraicSpace_X')
  obtain ⟨ν₂, -, h₂c, h₂⟩ := Space.exists_cardinal_bound_fieldPoints.{u + 1}
    c.isReduction_WredInclusion.algebraic
  obtain ⟨T₀, hT₀⟩ := Space.exists_le_size_of_le_of_lt (hS := hS) (max ν₁ ν₂)
    (h₁S.trans (le_max_left _ _)) (max_lt h₁c h₂c)
  refine ⟨T₀, fun U K _ ⟨e⟩ hlft => ?_⟩
  let V := U.obj
  have : Subsingleton ((BigFppfOver.toScheme B S hS).obj V) :=
    ⟨fun a b => (Scheme.homeoOfIso e).injective (Subsingleton.elim _ _)⟩
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj V) :=
    isReduced_of_isOpenImmersion e.hom
  have hred := c.isReduction_WredInclusion.bijective_app V inferInstance
  let eW := Equiv.ofBijective _ hred
  let ψ : Triple c V → ULift.{u + 1} (c.X'.obj (op V)) ⊕ c.Wred.obj.obj (op V) := fun t =>
    if h : t.Z = ∅ then Sum.inl (ULift.up (t.uValue h))
    else Sum.inr (eW.symm (t.xhatValue ((t.Z_eq_empty_or_eq_univ).resolve_left h)))
  have hψ : Function.Injective ψ := by
    intro t t' htt'
    by_cases h : t.Z = ∅ <;> by_cases h' : t'.Z = ∅ <;>
      simp only [ψ, h, h', dite_true, dite_false, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq,
        ULift.up.injEq, EmbeddingLike.apply_eq_iff_eq] at htt'
    · exact Triple.ext_of_Z_eq_empty h h' htt'
    · exact Triple.ext_of_Z_eq_univ _ _ htt'
  have hne : Nonempty ((BigFppfOver.toScheme B S hS).obj V) :=
    ⟨e.inv (Nonempty.some inferInstance)⟩
  have hℵ : ℵ₀ ≤ Cardinal.lift.{u + 1} (max ν₁ ν₂) :=
    aleph0_le_lift.mpr (S.aleph0_le_size.trans (h₁S.trans (le_max_left _ _)))
  calc #(Triple c V) ≤ #(ULift.{u + 1} (c.X'.obj (op V)) ⊕ c.Wred.obj.obj (op V)) :=
        mk_le_of_injective hψ
    _ = #(ULift.{u + 1} (c.X'.obj (op V))) + #(c.Wred.obj.obj (op V)) := mk_sum _ _ |>.trans
        (by simp)
    _ ≤ Cardinal.lift.{u + 1} (max ν₁ ν₂) + Cardinal.lift.{u + 1} (max ν₁ ν₂) :=
        add_le_add ((h₁ V K ⟨e⟩ hlft).trans (lift_le.mpr (le_max_left _ _)))
          ((h₂ V K ⟨e⟩ hlft).trans (lift_le.mpr (le_max_right _ _)))
    _ = Cardinal.lift.{u + 1} (max ν₁ ν₂) := add_eq_self hℵ
    _ ≤ Cardinal.lift.{u + 1} ((BigFppfOver.toScheme B S hS).obj T₀).size :=
        lift_le.mpr (hT₀ V hne)

end AlgebraicGeometry.Artin.ContractionSituation

end
