module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction

/-!
# The valuative identity of a relative cycle over a discrete valuation ring

Let `R` be a discrete valuation ring and let `f : X ⟶ Spec R` be locally of finite type. The
valuative condition of [Stacks, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50) for a
family `α` of `r`-cycles on the fibres of `X/Spec R` quantifies over all discrete valuation rings
and all morphisms of their spectra to `Spec R`; this file reads off its instance at the identity
of `Spec R`, which is the identity `sp_{X/R}(α_η) = α_0` between the two members of `α` over the
two points of `Spec R`.

## Main results

* `Stacks.Chow.specializationCycle_eq_of_isRelativeCycle` — a relative `r`-cycle over the
  spectrum of a discrete valuation ring carries its generic member to its closed member under
  the specialization map.

## Implementation notes

The instance of the valuative condition at `𝟙 (Spec R)` is an identity between cycles on the
fibres of `X ×_{Spec R} Spec R ⟶ Spec R`, not of `X/Spec R`. The identity square with top edge
`𝟙 X` and bottom edge `𝟙 (Spec R)` is cartesian, so `Stacks.Chow.baseChangeFamilyOfIsPullback_id`
says that restricting the base change `(𝟙 Spec R)^*α` along the canonical isomorphism
`X ≅ X ×_{Spec R} Spec R` gives `α` back, member by member. Restriction of fibrewise cycles
along that isomorphism commutes with specialization, which is the open-immersion case of
Tag 0H4L (`Stacks.Chow.specializationCycle_fiberCycleRestrict`), so applying it to the valuative
identity at `𝟙 (Spec R)` turns that identity into the one asserted here.

## References

* [Stacks Project, Definition 0H50](https://stacks.math.columbia.edu/tag/0H50)
* [Stacks Project, Section 0H4H](https://stacks.math.columbia.edu/tag/0H4H)
* [Stacks Project, Lemma 0H4L](https://stacks.math.columbia.edu/tag/0H4L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- **Transport of the valuative identity along an open immersion of the source.** If a family
`β` on `X/Spec R` satisfies the identity `sp(β_η) = β_0` and its restrictions along an open
immersion `j : U ⟶ X` over `Spec R` are the members of a family `γ` on `U/Spec R`, then `γ`
satisfies that identity too. -/
private theorem specializationCycle_eq_of_fiberCycleRestrict {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {X U : Scheme.{u}} (p : X ⟶ Spec (.of R))
    [LocallyOfFiniteType p] (q : U ⟶ Spec (.of R)) [LocallyOfFiniteType q] (j : U ⟶ X)
    [IsOpenImmersion j] (h : j ≫ p = q) (r : ℕ) (β : FamilyOfCycles p r)
    (γ : FamilyOfCycles q r) (hβγ : ∀ t, fiberCycleRestrict p q j h t r (β t) = γ t)
    (hβ : specializationCycle p r (β (genericPoint (Spec (.of R)))) =
      β (IsLocalRing.closedPoint R)) :
    specializationCycle q r (γ (genericPoint (Spec (.of R)))) = γ (IsLocalRing.closedPoint R) := by
  rw [← hβγ (genericPoint (Spec (.of R))),
    specializationCycle_fiberCycleRestrict p q j h r (β (genericPoint (Spec (.of R)))), hβ]
  exact hβγ _

/-- **The valuative identity of a relative cycle over a discrete valuation ring.** If `α` is a
relative `r`-cycle on `X/Spec R` with `R` a discrete valuation ring, then the specialization of
its member over the generic point of `Spec R` is its member over the closed point. -/
theorem specializationCycle_eq_of_isRelativeCycle {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f]
    (r : ℕ) {α : FamilyOfCycles f r} (hα : IsRelativeCycle f r α) :
    specializationCycle f r (α (genericPoint (Spec (.of R)))) = α (IsLocalRing.closedPoint R) :=
  have hsq : IsPullback (𝟙 X) f f (𝟙 (Spec (.of R))) := IsPullback.of_horiz_isIso ⟨by simp⟩
  specializationCycle_eq_of_fiberCycleRestrict (pullback.snd f (𝟙 (Spec (.of R)))) f
    hsq.isoPullback.hom hsq.isoPullback_hom_snd r
    (baseChangeFamily f (𝟙 (Spec (.of R))) r α) α
    (congrFun (baseChangeFamilyOfIsPullback_id f hsq r α)) (hα R (𝟙 (Spec (.of R))))

end Stacks.Chow

end
