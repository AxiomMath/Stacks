module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesStalkCore
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModuleStalkCartesianDictionary

/-!
# Formal glueing of quasi-coherent modules (Stacks 0AF0)

In Situation 0AEV — a morphism `f : Y ⟶ X` of algebraic spaces, a closed subspace `Z ⊆ X` with
open complement `U`, `V = f⁻¹(U)`, `f` flat and an isomorphism over `Z` — the functor of
Stacks 0AEW, `QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)`, `ℱ ↦ (ℱ|_U, f^*ℱ, can)`, is an equivalence, with
quasi-inverse the functor of Stacks 0AEX, `(ℋ, 𝒢, φ) ↦ Ker(j_*ℋ ⊕ f_*𝒢 → (f ∘ j')_*𝒢|_V)`.

The source checks this on stalks.  Over `U` and over `V` the comparison maps are isomorphisms
because `j` and `j'` are open immersions; at a geometric point `ȳ` of `f⁻¹(Z)` the stalk of the
module of Stacks 0AEX at `x̄ = f(ȳ)` is the fibre product of `(j_*ℋ)_x̄` and `𝒢_ȳ` over
`(j'_*𝒢|_V)_ȳ` (the omitted diagram chase, with Stacks 0AER on fibres), and Stacks 05ER for the
flat stalk map `𝒪_{X,x̄} ⟶ 𝒪_{Y,ȳ}` makes the map `𝒪_{Y,ȳ} ⊗ (j_*ℋ ×_{j'_*𝒢|_V} 𝒢)_x̄ ⟶ 𝒢_ȳ`
bijective.  Since `f` is flat, pulling back along it is exact and fibres at geometric points
detect isomorphisms, so the unit and the counit of the adjunction of Stacks 0AEY are
isomorphisms.

## Main results

* `AlgebraicGeometry.Space.FormalGlueingSituation.isIso_fiber_glueingCounitRight`: at a
  geometric point of `f⁻¹(Z)`, the second component of the counit of Stacks 0AEY is an
  isomorphism on fibres.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isIso_glueingAdjunction_unit_counit`:
  **Stacks 0AF0**, the unit and the counit of the adjunction of Stacks 0AEY between the
  functors of Stacks 0AEW and 0AEX are isomorphisms.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable (D : FormalGlueingSituation B S hS)

/-- **The second component of the counit of Stacks 0AEY on fibres at a point of `f⁻¹(Z)`.**  At
the image `ȳ` of a geometric point of `f⁻¹(Z)`, the map `(f^*K)_ȳ ⟶ 𝒢_ȳ` from the pullback of the
module `K` of Stacks 0AEX is bijective on fibres. -/
theorem bijective_fiber_glueingCounitRight (t : D.moduleGlueingData)
    (z : GeometricPoint B S hS (D.Z.preimage D.f).toFunctor) :
    Function.Bijective ((moduleFiber B S hS D.spaceY (geometricPointMap (D.Z.preimage D.f).ι z)).map
      (D.glueingCounitRight t)) := by
  have hb := D.bijective_glueingCounitRight_of_isPullback (geometricPointMap (D.Z.preimage D.f).ι z)
    t (D.isPullback_directImageFiberMap _ (D.glueingTriple t).right)
    (D.bijective_localPullbackGenericMap t z)
  have hE := fun m => fiberStalkAddEquiv_naturality B S hS D.spaceY
    (geometricPointMap (D.Z.preimage D.f).ι z) (D.glueingCounitRight t) m
  have hfun : ⇑((moduleFiber B S hS D.spaceY (geometricPointMap (D.Z.preimage D.f).ι z)).map
      (D.glueingCounitRight t)) =
      (fiberStalkAddEquiv B S hS D.spaceY (geometricPointMap (D.Z.preimage D.f).ι z) _).symm ∘
        (geometricModuleStalkMap B S hS D.spaceY (geometricPointMap (D.Z.preimage D.f).ι z)
          (D.glueingCounitRight t)) ∘
        fiberStalkAddEquiv B S hS D.spaceY (geometricPointMap (D.Z.preimage D.f).ι z) _ := by
    funext m
    exact (AddEquiv.eq_symm_apply _).2 (hE m)
  rw [hfun]
  exact (AddEquiv.bijective _).comp (hb.comp (AddEquiv.bijective _))

/-- **The second component of the counit of Stacks 0AEY is an isomorphism on fibres at the points
of `f⁻¹(Z)`.** -/
theorem isIso_fiber_glueingCounitRight (t : D.moduleGlueingData)
    (z : GeometricPoint B S hS (D.Z.preimage D.f).toFunctor) :
    IsIso ((moduleFiber B S hS D.spaceY (geometricPointMap (D.Z.preimage D.f).ι z)).map
      (D.glueingCounitRight t)) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (D.bijective_fiber_glueingCounitRight t z)

/-- **Stacks 0AF0.**  In Situation 0AEV the functor `QCoh(𝒪_X) ⥤ QCoh(Y → X, Z)` of Stacks 0AEW is
an equivalence with quasi-inverse the functor of Stacks 0AEX: the unit and the counit of the
adjunction of Stacks 0AEY between them are isomorphisms. -/
@[stacks 0AF0]
theorem isIso_glueingAdjunction_unit_counit :
    IsIso D.glueingAdjunction.unit ∧ IsIso D.glueingAdjunction.counit :=
  D.isIso_glueingAdjunction_unit_counit_of_fiber D.isIso_fiber_glueingCounitRight

end AlgebraicGeometry.Space.FormalGlueingSituation
