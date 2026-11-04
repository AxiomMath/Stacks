module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.DegreeZeroCompactSupport

/-!
# Vanishing of degree-zero compactly supported cohomology

Let `p : X ⟶ Y` be proper with `X`, `Y` Noetherian, `U ⊆ X` an open with nonempty complement and
`K ∈ D^b_{Coh}(𝒪_X)` without cohomology in negative degrees. By [Stacks, Tag 0G5C],
`H^0_c(U, K|_U)` is the group of global sections of `H^0(K)` vanishing near `X ∖ U`. So it vanishes
as soon as `H^0(K)` has no nonzero global section vanishing on a nonempty open; this is how
[Stacks, Tag 0G5E] uses [Stacks, Tag 0G5C].

## Main results

* `Stacks.Duality.Lichtenbaum.subsingleton_degreeZeroCompactSupport_of_forall_eq_zero`.

## References

* [Stacks Project, Tag 0G5C](https://stacks.math.columbia.edu/tag/0G5C)
* [Stacks Project, Tag 0G5E](https://stacks.math.columbia.edu/tag/0G5E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.Duality.Lichtenbaum

/-- **No compactly supported sections in degree zero.** Let `p : X ⟶ Y` be proper with `X` and
`Y` Noetherian, let `K ∈ D^b_{Coh}(𝒪_X)` have no cohomology in negative degrees, and let `U ⊆ X`
be an open whose complement is nonempty. If `H^0(K)` has no nonzero global section vanishing on a
nonempty open of `X`, then `H^0_c(U, K|_U) = 0`.

This is the last step of the proof of [Stacks, Tag 0G5E]: by [Stacks, Tag 0G5C]
(`AlgebraicGeometry.degreeZeroCompactSupportMap_injective` and
`AlgebraicGeometry.range_degreeZeroCompactSupportMap`) `H^0_c(U, K|_U)` is the group of global
sections of `H^0(K)` vanishing on an open neighbourhood of `X ∖ U`, and such a neighbourhood is
nonempty. -/
theorem subsingleton_degreeZeroCompactSupport_of_forall_eq_zero {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Y) [IsProper p] (K : BoundedCoherentDerived X)
    (hK : ∀ i < 0, IsZero ((@DerivedCategory.homologyFunctor X.Modules _ _
      (HasDerivedCategory.standard X.Modules) i).obj K.obj))
    (U : X.Opens) (hU : ((U : Set X)ᶜ).Nonempty)
    (htf : ∀ (V : X.Opens), (V : Set X).Nonempty →
      ∀ σ : Γ((@DerivedCategory.homologyFunctor X.Modules _ _
        (HasDerivedCategory.standard X.Modules) 0).obj K.obj, ⊤),
        ((@DerivedCategory.homologyFunctor X.Modules _ _
          (HasDerivedCategory.standard X.Modules) 0).obj K.obj).presheaf.map
            (homOfLE (le_top : V ≤ ⊤)).op σ = 0 → σ = 0) :
    Subsingleton (degreeZeroCompactSupport p U ((restrictBoundedCoherentLift U.ι).obj K)) := by
  let := HasDerivedCategory.standard X.Modules
  have hK' : K.obj.IsGE 0 := (DerivedCategory.isGE_iff K.obj 0).2 hK
  have hzero : ∀ a, degreeZeroCompactSupportMap p U K hK' a = 0 := fun a => by
    obtain ⟨V, hZV, hV⟩ : ∃ V : X.Opens, (U : Set X)ᶜ ⊆ V ∧ _ := by
      have h := range_degreeZeroCompactSupportMap p U K hK'
      have ha : degreeZeroCompactSupportMap p U K hK' a ∈
          Set.range (degreeZeroCompactSupportMap p U K hK') := ⟨a, rfl⟩
      rw [h] at ha
      exact ha
    exact htf V (hU.mono hZV) _ hV
  refine ⟨fun a b => degreeZeroCompactSupportMap_injective p U K hK' ?_⟩
  rw [hzero a, hzero b]

end Stacks.Duality.Lichtenbaum

end
