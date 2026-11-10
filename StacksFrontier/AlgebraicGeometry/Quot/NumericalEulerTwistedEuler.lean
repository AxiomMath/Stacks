module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariantsTwistPerfect
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerCharacteristic

/-!
# The residue-field point of a coherent family and its fibre square

Let `(T, 𝓕)` be an object of `Coh_{X/B}` and `t` a point of the test scheme `T`.  The canonical
morphism `Spec κ(t) ⟶ T` is a field-valued point of `T`, regarded as an algebraic space, in the
sense of Stacks 03BU; it represents the point at which Stacks 0DNC evaluates the function
`χ_i(t) = χ(K_i ⊗^𝐋 κ(t))`.  The fibre `X_t = X ×_B Spec κ(t)` on which Stacks 0DNF computes
`χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is the base change of `X_T ⟶ T` along this point, so the base change
theorem for `Rf_{T,*}` of Stacks 0A1P applies to the square

```
X_t ⟶ X_T
 |      |
Spec κ(t) ⟶ T
```

and identifies the derived fibre of `K_n = Rf_{T,*}(L^{⊗ n}_T ⊗^𝐋 𝓕)` at `t` with
`Rf_{t,*}` of the derived pullback of `L^{⊗ n}_T ⊗^𝐋 𝓕` to `X_t`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentObject.residuePoint`: the field-valued point
  `Spec κ(t) ⟶ T` of the test space of an object of `Coh_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.CoherentObject.residuePoint_toSpace`: its morphism of algebraic
  spaces is the image of `Spec κ(t) ⟶ T` under the Yoneda embedding.
* `AlgebraicGeometry.Space.CoherentObject.isPullback_fibreSpace`: the square above is cartesian.

## References

* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0A1P](https://stacks.math.columbia.edu/tag/0A1P)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentObject

variable {D : CoherentSituation B S hS}

/-- **The residue-field point of a coherent family.**  For an object `(T, 𝓕)` of `Coh_{X/B}` and a
point `t` of `T`, the field-valued point `Spec κ(t) ⟶ T` of `T` regarded as an algebraic space. -/
def residuePoint (A : CoherentObject D) (t : A.testScheme) :
    FieldValuedPoint B S hS (NumericalSituation.testSpace A).1 where
  carrier := A.testScheme.residueField t
  contained := B.residueField_spec_contains A.T.left.left.property t
  toBase := A.testScheme.fromSpecResidueField t ≫ B.inclusion.map A.T.left.hom
  value := A.pointSchemeHom t

/-- The field spectrum of the residue-field point is `Spec κ(t)` over `S`. -/
theorem residuePoint_siteObject (A : CoherentObject D) (t : A.testScheme) :
    (A.residuePoint t).siteObject = A.pointScheme t := rfl

/-- The morphism of algebraic spaces of the residue-field point is the image of
`Spec κ(t) ⟶ T` under the Yoneda embedding. -/
theorem residuePoint_toSpace (A : CoherentObject D) (t : A.testScheme) :
    (A.residuePoint t).toSpace = (schemeSpaceFunctor B S hS).map (A.pointSchemeHom t) := by
  apply ObjectProperty.hom_ext
  change yonedaEquiv.symm (A.pointSchemeHom t) = yoneda.map (A.pointSchemeHom t)
  ext W g
  simp [yonedaEquiv]

end CoherentObject

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.CoherentObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- **The fibre square is cartesian.**  The morphism `X_t ⟶ X_T` of base changes, the two
projections to `Spec κ(t)` and to `T`, and the residue-field point `Spec κ(t) ⟶ T` form a
cartesian square of algebraic spaces. -/
theorem isPullback_fibreSpace (A : CoherentObject D) (t : A.testScheme) :
    IsPullback (D.relativeMap (A.pointTestHom t)) (D.projection (A.pointTest t))
      (D.projection A.T) (A.residuePoint t).toSpace := by
  rw [residuePoint_toSpace]
  exact isPullback_baseChangeMap D.f (A.pointTestHom t)

end AlgebraicGeometry.Space.CoherentObject
