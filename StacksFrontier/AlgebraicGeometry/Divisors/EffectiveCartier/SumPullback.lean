module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Sum

/-!
# Pulling back a sum of effective Cartier divisors

Let `f : S' ⟶ S` be a morphism of schemes and `D₁, D₂ ⊆ S` effective Cartier divisors.  If the
pullbacks of `D₁` and `D₂` are defined, that is, if the scheme-theoretic inverse images of their
ideal sheaves are again effective Cartier divisors, then the pullback of `D = D₁ + D₂` is defined
and `f^*D = f^*D₁ + f^*D₂`.

## Main results

* `AlgebraicGeometry.comap_mul`: scheme-theoretic inverse image commutes with the product of
  quasi-coherent ideal sheaves; this is the equality `f^*D = f^*D₁ + f^*D₂`.
* `AlgebraicGeometry.isPullbackDefined_mul`: if the pullbacks of two effective Cartier divisors
  are defined, then so is the pullback of their sum.

## References

* [Stacks Project, Tag 01WW](https://stacks.math.columbia.edu/tag/01WW)
-/

@[expose] public section

open CategoryTheory Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- **Scheme-theoretic inverse image commutes with products of ideal sheaves.**  For a morphism
of schemes `f : X ⟶ Y` and quasi-coherent ideal sheaves `I`, `J` on `Y`, the inverse image of
`I * J` is the product of the inverse images.  In divisor language: the pullback of a sum of
effective Cartier divisors is the sum of their pullbacks. -/
@[stacks 01WW "pullback of the sum"]
theorem comap_mul {X Y : Scheme.{u}} (f : X ⟶ Y) (I J : Y.IdealSheafData) :
    (I * J).comap f = I.comap f * J.comap f := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := Σ U : Y.affineOpens, {V : X.affineOpens // (V : X.Opens) ≤ f ⁻¹ᵁ (U : Y.Opens)})
    (fun i ↦ i.2.1) (top_le_iff.mp fun x _ ↦ ?_) ?_
  · obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ f ⁻¹ᵁ U from hxU) (f ⁻¹ᵁ U).isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, hVU⟩, hxV⟩
  · rintro ⟨U, V, hVU⟩
    rw [Stacks.IdealSheaf.ideal_comap_appLE (I * J) f U V hVU,
      show (I.comap f * J.comap f).ideal V = (I.comap f).ideal V * (J.comap f).ideal V from rfl,
      Stacks.IdealSheaf.ideal_comap_appLE I f U V hVU,
      Stacks.IdealSheaf.ideal_comap_appLE J f U V hVU, ← Ideal.map_mul]
    rfl

/-- If the pullbacks of two effective Cartier divisors along a morphism of schemes are defined,
then so is the pullback of their sum. -/
@[stacks 01WW "definedness of the pullback"]
theorem isPullbackDefined_mul {X Y : Scheme.{u}} (f : X ⟶ Y) (I J : Y.IdealSheafData)
    (hI : IsPullbackDefined f I) (hJ : IsPullbackDefined f J) :
    IsPullbackDefined f (I * J) := by
  simpa only [← comap_mul] using isEffectiveCartierDivisor_mul _ _ hI hJ

end AlgebraicGeometry

end
