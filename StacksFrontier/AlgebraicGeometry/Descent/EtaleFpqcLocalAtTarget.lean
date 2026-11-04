module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.UnramifiedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.EtaleFlatUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# Étaleness is fpqc local on the base

A morphism of schemes is étale as soon as its base change along a surjective flat
quasi-compact morphism is, and more generally as soon as its base change along each member of
an fpqc covering is. Each of the three properties into which étaleness factors — flatness,
local finite presentation and unramifiedness — is already known to be fpqc local on the base,
so their conjunction is, and the conjunction is étaleness.

## Main results

* `AlgebraicGeometry.etale_eq_flat_inf_locallyOfFinitePresentation_inf_unramified` writes
  étaleness as the conjunction of flatness, local finite presentation and unramifiedness.
* `AlgebraicGeometry.etale_isLocalAtTarget_fpqc` is the statement that étaleness is fpqc local
  on the base, and `AlgebraicGeometry.etale_isLocalAtTarget_fppf` is its fppf consequence.

## Implementation notes

The conjuncts of `AlgebraicGeometry.etale_eq_flat_inf_locallyOfFinitePresentation_inf_unramified`
are ordered as `(Flat ⊓ LocallyOfFinitePresentation) ⊓ Unramified`, so that the two instances
supplied by `CategoryTheory.MorphismProperty.IsLocalAtTarget.inf` compose without reassociation.

## References

* [Stacks Project, Tag 02VN](https://stacks.math.columbia.edu/tag/02VN)
* [Stacks Project, Tag 02VM](https://stacks.math.columbia.edu/tag/02VM)
* [Stacks Project, Tag 02GV](https://stacks.math.columbia.edu/tag/02GV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is étale precisely when it is flat, locally of finite presentation
and unramified. -/
@[ega "IV 17.6.2", ega "IV 18.4.9" "(a) ⇔ (b), special case", sga "3 XI 1.4" "more general"]
theorem etale_iff_flat_and_locallyOfFinitePresentation_and_unramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    Etale f ↔ (Flat f ∧ LocallyOfFinitePresentation f) ∧ Unramified f := by
  rw [etale_iff_flat_and_gUnramified,
    gUnramified_iff_locallyOfFinitePresentation_and_formallyUnramified,
    unramified_iff_locallyOfFiniteType_and_formallyUnramified]
  constructor
  · rintro ⟨hflat, hfp, hfu⟩
    have _ : LocallyOfFinitePresentation f := hfp
    exact ⟨⟨hflat, hfp⟩, inferInstance, hfu⟩
  · rintro ⟨⟨hflat, hfp⟩, _, hfu⟩
    exact ⟨hflat, hfp, hfu⟩

/-- Étaleness read as an identity of morphism properties: it is the conjunction of flatness,
local finite presentation and unramifiedness. -/
@[ega "IV 17.6.2", sga "3 XI 1.4" "more general"]
theorem etale_eq_flat_inf_locallyOfFinitePresentation_inf_unramified :
    (@Etale : MorphismProperty Scheme.{u})
      = (@Flat ⊓ @LocallyOfFinitePresentation ⊓ @Unramified : MorphismProperty Scheme.{u}) :=
  MorphismProperty.ext _ _ fun _ _ f =>
    etale_iff_flat_and_locallyOfFinitePresentation_and_unramified f

/-- Étaleness of morphisms of schemes is fpqc local on the base. -/
@[stacks 02VN, stacks 02WH "etale", sga "3 VIB 2.1.2" "partial"]
instance etale_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@Etale : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
  have _ : MorphismProperty.IsLocalAtTarget
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := MorphismProperty.IsLocalAtTarget.inf _ _
  rw [etale_eq_flat_inf_locallyOfFinitePresentation_inf_unramified]
  exact MorphismProperty.IsLocalAtTarget.inf _ _

/-- Étaleness of morphisms of schemes is fppf local on the base. -/
@[stacks 02WH "etale"]
instance etale_isLocalAtTarget_fppf :
    MorphismProperty.IsLocalAtTarget (@Etale : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
  MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage

end AlgebraicGeometry

end
