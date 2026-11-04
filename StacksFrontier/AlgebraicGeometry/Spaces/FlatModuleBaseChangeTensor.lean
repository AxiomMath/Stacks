module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange

/-!
# Relative flatness of a pullback module, as a tensor condition over the étale local rings

Let

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

be a cartesian square of algebraic spaces over a scheme `S` of a big fppf site, let `F` be a
quasi-coherent `𝒪_X`-module and let `x̄'` be a geometric point of `X'`, with images `x̄` in `X`,
`ȳ'` in `Y'` and `ȳ` in `Y`.  Flatness of the pullback `(g')^* F` over `Y'` at `x̄'`, in the sense
of condition (2) of Stacks 05VU, is the same thing as flatness of

`𝒪_{X', x̄'} ⊗_{𝒪_{X, x̄}} F_{x̄}`

over `𝒪_{Y', ȳ'}`.  This is just the base-change formula of Stacks 05VQ for the geometric stalk
of a pullback, read through the definition of relative flatness at a geometric point; it is an
*equivalence*, where the two parts of Stacks 05VW give the two implications of a comparison with
flatness downstairs.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback_iff_flat_tensor`.

## Implementation notes

The instance setup is the one of
`AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback`, whose proof this
generalises: there the implication is obtained from the tensor statement, and all that is needed
to turn it into an equivalence is that the two transports used — `ModuleCat.flat_iff_of_iso`
along `AlgebraicGeometry.Space.geometricModuleStalkPullbackIso` and
`ModuleCat.flat_extendScalars_obj_iff` — are themselves equivalences.

The homomorphism `𝒪_{Y, ȳ} → 𝒪_{Y', ȳ'}` carries the `eqToHom` correction that the two routes
from `x̄'` to `Y` force: `𝒪_{Y, ȳ}` is spelled at the point
`geometricPointMap f.hom (geometricPointMap g'.hom x̄')`, while the canonical homomorphism out of
`Y'` is indexed by `geometricPointMap g.hom (geometricPointMap f'.hom x̄')`, and the square makes
these equal only propositionally.

## References

* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Relative flatness of a pullback module at a geometric point is a tensor condition.**  For a
cartesian square of algebraic spaces as above and a geometric point `x̄'` of `X'`, the pullback
`(g')^* F` is flat over `Y'` at `x̄'` exactly when `𝒪_{X', x̄'} ⊗_{𝒪_{X, x̄}} F_{x̄}` is flat over
`𝒪_{Y', ȳ'}`.

This is the base-change formula for the geometric stalk of a pullback (Stacks 05VQ,
`AlgebraicGeometry.Space.geometricModuleStalkPullbackIso`) read through the definition of
condition (2) of Stacks 05VU, so it needs nothing of the square beyond that formula. -/
theorem isFlatOverAtGeometricPoint_modulePullback_iff_flat_tensor
    {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g) (F : Modules.{u, u} B S hS X.1 X.2)
    (x' : GeometricPoint B S hS X'.1) :
    letI : Algebra
        ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
        ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
      (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
    letI : Algebra ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
        ↥(etaleLocalRing B S hS X'.1 x') := (etaleLocalRingMap X'.2 g'.hom x').toAlgebra
    letI : Module ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
        (TensorProduct ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
          ↥(etaleLocalRing B S hS X'.1 x')
          ↥(geometricModuleStalk B S hS X (geometricPointMap g'.hom x') F)) :=
      Module.compHom _ (etaleLocalRingMap X'.2 f'.hom x')
    (IsFlatOverAtGeometricPoint B S hS f' ((modulePullback B S hS g').obj F) x' ↔
      Module.Flat ↥(etaleLocalRing B S hS Y'.1 (geometricPointMap f'.hom x'))
        (TensorProduct ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
          ↥(etaleLocalRing B S hS X'.1 x')
          ↥(geometricModuleStalk B S hS X (geometricPointMap g'.hom x') F))) := by
  let : Algebra
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x')) :=
    (etaleLocalRingMap X.2 f.hom (geometricPointMap g'.hom x')).toAlgebra
  let : Algebra ↥(etaleLocalRing B S hS X.1 (geometricPointMap g'.hom x'))
      ↥(etaleLocalRing B S hS X'.1 x') := (etaleLocalRingMap X'.2 g'.hom x').toAlgebra
  exact (ModuleCat.flat_iff_of_iso (etaleLocalRingMap X'.2 f'.hom x')
    (geometricModuleStalkPullbackIso B S hS g' x' F)).trans
      (ModuleCat.flat_extendScalars_obj_iff _ _ _)

end AlgebraicGeometry.Space

end
