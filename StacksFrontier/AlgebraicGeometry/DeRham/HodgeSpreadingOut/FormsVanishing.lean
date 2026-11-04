module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.BaseChange
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.GenericPointCoproduct.Basic

/-!
# Vanishing of the differential forms of high degree, and its base change

For a smooth morphism `f : X ⟶ S` with `X` quasi-compact, the sheaves `Ω^p_{X/S}` vanish for `p`
large, and this vanishing passes to every base change of `f`, because the formation of
`Ω^p_{X/S}` commutes with base change ([Stacks, Tag 0FL5]). In the spreading out argument for the
degeneration of the Hodge-to-de Rham spectral sequence this is how the fibres of a model over a
finitely generated ring get their forms to vanish in degrees at least the residue characteristic,
the hypothesis "`dim X₀ < p`" of Deligne–Illusie in the form that proof uses it.

## Main results

* `AlgebraicGeometry.HodgeSpreadingOut.exists_isZero_relativeDifferentialForms`: the forms of a
  smooth morphism from a quasi-compact scheme vanish in high degree.
* `AlgebraicGeometry.HodgeSpreadingOut.isZero_relativeDifferentialForms_of_isPullback`: vanishing
  of `Ω^n_{X/S}` passes to a base change.

## References

* [Stacks Project, Tag 0FL5](https://stacks.math.columbia.edu/tag/0FL5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.HodgeSpreadingOut

/-- **The relative differential forms of a smooth morphism from a quasi-compact scheme vanish in
high degree.** -/
theorem exists_isZero_relativeDifferentialForms {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    [CompactSpace X] :
    ∃ N : ℕ, ∀ p : ℕ, N < p → IsZero (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) := by
  obtain ⟨N, hN⟩ := ProperSmoothDeRham.exists_forall_subsingleton_relativeDifferentialForms f ⊤
    isCompact_univ
  exact ⟨N, fun p hp =>
    Stacks.AlgebraicGeometry.GenericPointCoproduct.isZero_of_subsingleton_sections _
      fun U => hN p hp U le_top⟩

/-- **Vanishing of `Ω^n_{X/S}` passes to a base change**: in a cartesian square, `Ω^n_{X'/S'}` is
the pullback of `Ω^n_{X/S}` ([Stacks, Tag 0FL5]). -/
theorem isZero_relativeDifferentialForms_of_isPullback {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (H : IsPullback g' f' f g) (n : ℤ)
    (h : IsZero (Scheme.Hom.relativeDifferentialForms f n)) :
    IsZero (Scheme.Hom.relativeDifferentialForms f' n) := by
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback g' f f' g H n
  exact IsZero.of_iso ((Scheme.Modules.pullback g').map_isZero h)
    (asIso (Scheme.Hom.relativeDifferentialFormsMap g' f f' g H.w n)).symm

end AlgebraicGeometry.HodgeSpreadingOut
