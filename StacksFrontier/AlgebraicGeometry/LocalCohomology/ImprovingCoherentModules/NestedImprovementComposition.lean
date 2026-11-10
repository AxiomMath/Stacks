module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovement
import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtension
import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovement

/-!
# The two steps of the construction of an improvement, composed

Let `X` be a Noetherian scheme, let `T' ⊆ T ⊆ X` with `T` stable under specialization and let `F`
be a coherent `𝒪_X`-module.  The source constructs the improvement of `F` along `T' ⊆ T`
([Stacks, Tag 0EI4]) in two steps: the depth-one quotient `F → F'` of `F` along `T`
([Stacks, Tag 0DX3]), followed by a depth-two extension `F' → F''` of that quotient along `T'`
([Stacks, Tag 0EI3]).  This module proves that the composite is an improvement, for *any*
depth-two extension of the depth-one quotient, with no hypothesis beyond `T' ⊆ T`.

## Main results

* `AlgebraicGeometry.isNestedImprovement_depthOneQuotient_comp`: the depth-one quotient along `T`
  followed by any depth-two extension of it along `T'` is an improvement along `T' ⊆ T`.

## Implementation notes

Away from `T` both steps are isomorphisms on stalks, the second because the complement of `T`
lies in the complement of `T'`; at a point of `T` outside `T'` the first step is surjective and
the second is an isomorphism on stalks, which carries the depth bound of the quotient over to the
target; and at a point of `T'` the depth bound is the one of the depth-two extension.

The existence half of [Stacks, Tag 0EI4] at the source's hypotheses,
`AlgebraicGeometry.exists_isNestedImprovement_of_hasDualizingComplex`, is this composition at the
depth-two extension supplied by [Stacks, Tag 0EI3]; the construction for [Stacks, Tag 0DX5],
`AlgebraicGeometry.isNestedImprovement_toDepthOneQuotient_comp_unit`, is it at the canonical map
to the extension of the restriction to an open.

## References

* [Stacks Project, Tag 0EI4](https://stacks.math.columbia.edu/tag/0EI4)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The two steps of the source's construction, composed.** The depth-one quotient of `F` along
`T` followed by a depth-two extension of that quotient along `T'` is an improvement of `F` along
`T' ⊆ T`.

This is the whole of the source's existence proof of [Stacks, Tag 0EI4]: the first step is
[Stacks, Tag 0DX3] and the second is [Stacks, Tag 0EI3].  Nothing beyond `T' ⊆ T` and the
stability of `T` under specialization is used. -/
public theorem isNestedImprovement_depthOneQuotient_comp (X : Scheme.{u}) [IsNoetherian X]
    (T T' : Set X) (hTT' : T' ⊆ T) (hT : StableUnderSpecialization T)
    (F : X.Modules) [F.IsCoherent] {G : X.Modules}
    (ψ : depthOneQuotient X T hT F ⟶ G) (hψ : IsDepthTwoExtension T' ψ) :
    IsNestedImprovement T T' (toDepthOneQuotient X T hT F ≫ ψ) := by
  have hq := depthOneQuotient_spec X T hT F
  let : Epi (toDepthOneQuotient X T hT F) := hq.2.1
  refine ⟨hψ.1, ?_, ?_, fun x hx' => hψ.2.2 x hx'⟩
  · -- away from `T` both steps are isomorphisms on stalks
    intro x hx
    let S := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
    have : IsIso (S.map (toDepthOneQuotient X T hT F)) := hq.2.2.1 x hx
    have : IsIso (S.map ψ) :=
      isIso_stalkAb_of_isIso_stalkMap ψ x (hψ.2.1 x fun hx' => hx (hTT' hx'))
    change IsIso (S.map (toDepthOneQuotient X T hT F ≫ ψ))
    rw [Functor.map_comp]
    infer_instance
  · -- on `T` outside `T'` the first step is surjective and the second keeps the depth bound
    intro x hx hx'
    have hiso : IsIso (SheafOfModules.stalkMap X.ringCatSheaf x ψ) := hψ.2.1 x hx'
    refine ⟨?_, ?_⟩
    · let S := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
      have : Epi (S.map (toDepthOneQuotient X T hT F)) :=
        epi_stalkAb_of_epi (toDepthOneQuotient X T hT F) x
      have : IsIso (S.map ψ) := isIso_stalkAb_of_isIso_stalkMap ψ x hiso
      change Epi (S.map (toDepthOneQuotient X T hT F ≫ ψ))
      rw [Functor.map_comp]
      exact epi_comp _ _
    · rw [← depth_stalk_eq_of_isIso_stalkMap ψ x hiso]
      exact hq.2.2.2 x hx

end AlgebraicGeometry

end
