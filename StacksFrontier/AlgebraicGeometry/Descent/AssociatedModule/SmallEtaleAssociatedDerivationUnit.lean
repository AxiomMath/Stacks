module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsInvertible
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsCorepresentable

/-!
# The associated-module unit carries `d_{X/Y}` to `d^a`

Let `f : X ⟶ Y` be a morphism of schemes with `X` in a big étale site `B`.  The unit
`η : Ω_{X/Y} ⟶ ε_*((Ω_{X/Y})^a)` of the adjunction of Stacks 03DU (4) between the
associated-module functor and restriction to the small Zariski site of `X` carries the universal
relative derivation `d_{X/Y}` to the small Zariski restriction of the canonical derivation `d^a`
of Stacks 04CS.

## Main results

* `universalRelativeDerivation_postcomp_associatedModuleAdjunction_unit`: the statement above, as
  an equality of `Y`-derivations of `𝒪_X` with values in `ε_*((Ω_{X/Y})^a)`.
* `associatedModuleAdjunction_unit_app_universalRelativeDerivation_d`: the same read on a
  section, over an open `W` of `X`.

## Implementation notes

`AlgebraicGeometry.SmallEtale.differentialsComparison_adjunct` is exactly this statement with
the comparison map `c''` of `d^a` in place of the unit, and
`AlgebraicGeometry.SmallEtale.differentialsComparison_associatedDerivation` says that this
comparison map is the identity; the adjunct of the identity is the unit, which is the remaining
step.  So the shuffling between the sections model of Stacks 070S (2) and the associated module
itself is already done inside the proof of the key compatibility and is not repeated here.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), clause (4).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (f : X ⟶ Y)

/-- **The unit of the associated-module adjunction carries `d_{X/Y}` to `d^a`.**  Postcomposing
the universal relative derivation `d_{X/Y}` of `Ω_{X/Y}` with the unit
`Ω_{X/Y} ⟶ ε_*((Ω_{X/Y})^a)` of the adjunction of Stacks 03DU (4) gives the restriction to the
small Zariski site of `X` of the canonical derivation `d^a` of Stacks 04CS.

The unit is the adjunct of the identity of `(Ω_{X/Y})^a`, and
`AlgebraicGeometry.SmallEtale.differentialsComparison_associatedDerivation` says that the
comparison map of `d^a` is that identity, so this is
`AlgebraicGeometry.SmallEtale.differentialsComparison_adjunct` read at `d^a`. -/
theorem universalRelativeDerivation_postcomp_associatedModuleAdjunction_unit :
    (Scheme.Hom.universalRelativeDerivation f).postcomp
        (((associatedModuleAdjunction B X hX).unit.app
          (Scheme.Hom.relativeDifferentials f)).val) =
      zariskiRestriction B hX f (associatedDerivation B hX f)
        (associatedDerivation_pullbackSection_eq_zero B hX f) := by
  have h := differentialsComparison_adjunct B hX f (associatedDerivation B hX f)
    (associatedDerivation_pullbackSection_eq_zero B hX f)
  rw [differentialsComparison_associatedDerivation B hX f] at h
  refine Eq.trans ?_ h
  refine congrArg (fun g : Scheme.Hom.relativeDifferentials f ⟶
      (restrictModule B X hX).obj (associatedRelativeDifferentials B hX f) =>
    (Scheme.Hom.universalRelativeDerivation f).postcomp g.val) ?_
  rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

/-- **The unit of the associated-module adjunction carries `d_{X/Y} a` to `d^a a`.**  For an open
`W` of `X` and a section `a` of `𝒪_X` over `W`, the component at `W` of the unit
`Ω_{X/Y} ⟶ ε_*((Ω_{X/Y})^a)` carries the universal differential `d_{X/Y} a` to the value of the
canonical derivation `d^a` of Stacks 04CS over the object `W ↪ X` of the small étale site of `X`,
on `a` read as a global function of the open subscheme `W`.

This is
`AlgebraicGeometry.SmallEtale.universalRelativeDerivation_postcomp_associatedModuleAdjunction_unit`
read on sections. -/
theorem associatedModuleAdjunction_unit_app_universalRelativeDerivation_d
    (W : X.Opens) (a : Γ(X, W)) :
    ((associatedModuleAdjunction B X hX).unit.app
          (Scheme.Hom.relativeDifferentials f)).val.app (op W)
        ((Scheme.Hom.universalRelativeDerivation f).d a) =
      (associatedDerivation B hX f).d
        (X := op ((opensToSmallEtale B X hX).obj W))
        (((commRingStructureMap B X hX).hom.app (op W)).hom a) := by
  refine Eq.trans (PresheafOfModulesOfCommRing.Derivation.postcomp_d_apply
    (Scheme.Hom.universalRelativeDerivation f) _ a).symm ?_
  exact PresheafOfModulesOfCommRing.Derivation.congr_d
    (universalRelativeDerivation_postcomp_associatedModuleAdjunction_unit B hX f) a

end AlgebraicGeometry.SmallEtale

end
