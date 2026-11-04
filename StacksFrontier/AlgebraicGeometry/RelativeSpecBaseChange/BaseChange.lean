module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Adjunction

/-!
# The canonical base-change morphism of algebra sheaves

Let `g : T ⟶ S` be a morphism of schemes and let `X` be a scheme over `S`. The fibre product
`X ×_S T` is a scheme over `T`, and this file constructs the canonical morphism of
`𝒪_T`-algebras
```
g⁻¹(X.hom _* 𝒪_X) ⊗_{g⁻¹𝒪_S} 𝒪_T ⟶ (X ×_S T ⟶ T) _* 𝒪_{X ×_S T}
```
and identifies it on underlying sheaves of rings with the comparison
`Stacks.AffineAlgebraEquivalence.pushforwardBaseChangeMap`.

## Main definitions

* `Stacks.AffineAlgebraEquivalence.baseChangeProjection` is the projection
  `X ×_S T ⟶ X`, as a morphism over `S` from the object `X ×_S T ⟶ T ⟶ S`.
* `Stacks.AffineAlgebraEquivalence.baseChangeAlgebraHom` is the canonical morphism of
  `𝒪_T`-algebras above.

## Main results

* `Stacks.AffineAlgebraEquivalence.algebraPullbackMap_comp_baseChangeAlgebraHom`: the canonical
  map `g⁻¹A ⟶ g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T` followed by `baseChangeAlgebraHom` is
  `pushforwardBaseChangeMap`.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AffineAlgebraEquivalence

variable {T S : Scheme.{u}} (g : T ⟶ S)

/-- The projection `X ×_S T ⟶ X` of the fibre product, as a morphism over `S` whose source is
the fibre product regarded as a scheme over `S` through `T`. -/
public noncomputable def baseChangeProjection (X : Over S) :
    (Over.mk (pullback.snd X.hom g ≫ g) : Over S) ⟶ X :=
  Over.homMk (pullback.fst X.hom g) pullback.condition

/-- The canonical morphism of `𝒪_T`-algebras from the base change of `X.hom _* 𝒪_X` to the
pushed-forward structure sheaf of the base-changed scheme. It is adjoint to the contravariant
map on pushed-forward structure sheaves induced by the projection `X ×_S T ⟶ X`. -/
public noncomputable def baseChangeAlgebraHom (X : Over S) :
    (algebraPullback g).obj (pushforwardAlgebra X.hom) ⟶
      pushforwardAlgebra ((Over.pullback g).obj X).hom :=
  ((algebraPullbackPushforwardAdjunction g).homEquiv _ _).symm
    (pushforwardAlgebraMap (baseChangeProjection g X))

/-- The canonical map from the inverse image of `X.hom _* 𝒪_X` to its base change, followed by
`baseChangeAlgebraHom`, is the inverse-image comparison `pushforwardBaseChangeMap`. -/
public theorem algebraPullbackMap_comp_baseChangeAlgebraHom (X : Over S) :
    (algebraPullbackMap g).app (pushforwardAlgebra X.hom) ≫
        (baseChangeAlgebraHom g X).right = pushforwardBaseChangeMap g X := by
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat g.base).homEquiv
    (pushforwardAlgebra X.hom).right
    (pushforwardAlgebra ((Over.pullback g).obj X).hom).right).eq_symm_apply.mpr ?_
  refine Eq.trans ?_ (congrArg Under.Hom.right
    (((algebraPullbackPushforwardAdjunction g).homEquiv (pushforwardAlgebra X.hom)
      (pushforwardAlgebra ((Over.pullback g).obj X).hom)).apply_symm_apply _))
  exact (homEquiv_right g (pushforwardAlgebra X.hom)
    (pushforwardAlgebra ((Over.pullback g).obj X).hom) (baseChangeAlgebraHom g X)).symm

end Stacks.AffineAlgebraEquivalence

end
