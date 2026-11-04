module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LinearAction
public import StacksFrontier.AlgebraicGeometry.ProjMapData.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist
public import StacksCore.Tactic.StacksAttribute

/-!
# The projective space action as the morphism induced by a graded ring homomorphism

A homomorphism `ψ : 𝒜 →+*ᵍ ℬ` of nonnegatively graded rings induces a morphism to `Proj 𝒜`
only on an open `U(ψ) ⊆ Proj ℬ`, and that morphism comes with comparison maps on all twists.
For the graded homomorphism attached to an invertible linear map `g` of `V`, that open is all of
`Proj (Sym V)`, and the morphism is the one `AlgebraicGeometry.Proj.map` produces, which is the
action of `g` on the projective space of `V`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.mapDomain_eq_top`: an invertible linear map has
  everywhere-defined projective morphism.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mapDomain_ι_comp_map`: on that open the general
  construction agrees with the action of `g`.

## Implementation notes

The identification is obtained from the uniqueness statement
`Stacks.AlgebraicGeometry.ProjTwistChain.eq_mapHom`: a morphism out of the domain of definition
which has the prescribed inverse images of standard opens, and on each of them is induced by the
corresponding map of degree-zero homogeneous localizations, is the glued morphism. Both
conditions hold for the composite of the inclusion with
`AlgebraicGeometry.ProjectiveSpaceOfModule.map` by Mathlib's description of
`AlgebraicGeometry.Proj.map` on standard opens.

## References

* [Stacks Project, Tag 0B2U](https://stacks.math.columbia.edu/tag/0B2U)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public section

open CategoryTheory HomogeneousLocalization TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u v

variable (k : Type u) (V : Type v) [CommRing k] [AddCommGroup V] [Module k V]

/-- An invertible linear map has everywhere-defined projective morphism: the domain of
definition of the induced graded ring homomorphism is all of `P(V)`. -/
@[stacks 0B2U "the invertible locus has full projective domain"]
public theorem mapDomain_eq_top (g : LinearMap.GeneralLinearGroup k V) :
    mapDomain (fun n => SymPow.symmetricPower n k V) (fun n => SymPow.symmetricPower n k V)
      (SymPow.gradedSymAlgMap (g : V →ₗ[k] V)) = ⊤ :=
  mapDomain_eq_top_of_irrelevant_le_map _ _ _ (irrelevant_le_map_gradedSymAlgMap k V g)

/-- On the domain of definition of the induced graded ring homomorphism, the morphism carrying
the comparison maps on all twists is the action of `g` on `P(V)`. -/
@[stacks 0B2U "compatibility with the projective transformation family"]
public theorem mapDomain_ι_comp_map (g : LinearMap.GeneralLinearGroup k V) :
    (mapDomain (fun n => SymPow.symmetricPower n k V) (fun n => SymPow.symmetricPower n k V)
          (SymPow.gradedSymAlgMap (g : V →ₗ[k] V))).ι ≫ map k V g =
      (projMapData (fun n => SymPow.symmetricPower n k V)
        (fun n => SymPow.symmetricPower n k V)
        (SymPow.gradedSymAlgMap (g : V →ₗ[k] V))).hom := by
  set A := fun n => SymPow.symmetricPower n k V with hA
  set ψ := SymPow.gradedSymAlgMap (g : V →ₗ[k] V) with hψ
  set D := mapDomain A A ψ with hD
  have hopen : ∀ (f : SymmetricAlgebra k V) (d : ℕ), f ∈ A d → 0 < d →
      (D.ι ≫ map k V g) ⁻¹ᵁ Proj.basicOpen A f = D.ι ⁻¹ᵁ Proj.basicOpen A (ψ f) := by
    intro f d hf hd
    rw [Scheme.Hom.comp_preimage, map, Proj.map_preimage_basicOpen]
  refine eq_mapHom A A ψ (D.ι ≫ map k V g) hopen ?_
  intro f d hf hd
  rw [← Scheme.Hom.appLE_comp_appLE D.ι (map k V g)
    (Proj.basicOpen A f) (Proj.basicOpen A (ψ f)) (D.ι ⁻¹ᵁ Proj.basicOpen A (ψ f))
    (by rw [map, Proj.map_preimage_basicOpen]) le_rfl]
  simpa [map, ψ] using
    Proj.awayToSection_comp_appLE_assoc (SymPow.gradedSymAlgMap (g : V →ₗ[k] V))
      (irrelevant_le_map_gradedSymAlgMap k V g) hf
      (Scheme.Hom.appLE D.ι (Proj.basicOpen A (ψ f))
        (D.ι ⁻¹ᵁ Proj.basicOpen A (ψ f)) le_rfl)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
