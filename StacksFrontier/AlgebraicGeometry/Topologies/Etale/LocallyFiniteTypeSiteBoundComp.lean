module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSite

/-!
# The bound of Stacks 0DC6 along étale maps

For a morphism `f : X ⟶ S` the bound
`d_X = 1 + 2 dim S + sup_{x ∈ X} (trdeg_{κ(s)} κ(x) + 2 dim 𝒪_{X, x})`
(`AlgebraicGeometry.Scheme.Hom.etaleCohomologyBound`) does not grow when `X` is replaced by a
scheme étale over it: the residue field extensions of an étale map are finite separable and its
local rings have the same dimension as those below them.

## Main results

* `AlgebraicGeometry.Scheme.Hom.etaleCohomologyBound_comp_le`: the bound of a scheme étale over
  a locally Noetherian one is at most the bound of the latter.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **The bound does not grow along étale maps.** If `g : X' ⟶ X` is étale (more generally
flat, formally unramified and locally of finite type) and `X` is locally Noetherian, then
`d_{X'} ≤ d_X` for the bounds of `g ≫ f` and `f`: every term
`trdeg_{κ(s)} κ(x') + 2 dim 𝒪_{X', x'}` of the supremum defining `d_{X'}` is the term at `g(x')`
of the supremum defining `d_X`, by
`AlgebraicGeometry.Scheme.Hom.trdeg_residueField_eq_of_formallyUnramified` and
`AlgebraicGeometry.Scheme.Hom.ringKrullDim_stalk_eq_of_formallyUnramified`. -/
public theorem Hom.etaleCohomologyBound_comp_le {X' X S : Scheme.{u}} (g : X' ⟶ X)
    (f : X ⟶ S) [Flat g] [FormallyUnramified g] [LocallyOfFiniteType g]
    [IsLocallyNoetherian X] :
    Hom.etaleCohomologyBound (g ≫ f) ≤ Hom.etaleCohomologyBound f := by
  unfold Hom.etaleCohomologyBound
  gcongr
  refine iSup_le fun x' => ?_
  refine le_trans (le_of_eq ?_) (le_iSup _ (g.base x'))
  rw [g.ringKrullDim_stalk_eq_of_formallyUnramified x']
  congr 2
  rw [← Hom.trdeg_residueField_eq_of_formallyUnramified f g x', Scheme.residueFieldMap_comp]
  rfl

end AlgebraicGeometry.Scheme

end
