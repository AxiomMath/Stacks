module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseCohomology

/-!
# The twisted Euler characteristic as an Euler characteristic over the residue field

Let `(T, 𝓕)` be an object of `Coh_{X/B}`, let `t ∈ T` and let `X_t = X ×_B Spec κ(t)` be the
fibre. The twisted Euler characteristic `AlgebraicGeometry.Space.CoherentObject.twistedEuler`
is formed on `X_t` regarded as an algebraic space over the base scheme `S` of the situation, the
cohomology being made a `κ(t)`-vector space along the projection `X_t ⟶ Spec κ(t)`. The fibre is
however an algebraic space *over `Spec κ(t)`*, through that projection (Stacks 04SG), and this
file computes the twisted Euler characteristic there: it is the alternating sum of the
`κ(t)`-dimensions of the cohomology, over the base `Spec κ(t)`, of the corresponding module on
the fibre viewed over `Spec κ(t)`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentObject.pointSchemeHom'`: the morphism `Spec κ(t) ⟶ S` of the
  big fppf site underlying the point.
* `AlgebraicGeometry.Space.CoherentObject.fibreOverPoint`: the fibre `X_t` as an algebraic space
  over `Spec κ(t)`.
* `AlgebraicGeometry.Space.CoherentObject.fibreModulesEquivalence`: the modules on `X_t` over
  `S` and over `Spec κ(t)` are the same.

## Main results

* `AlgebraicGeometry.Space.CoherentObject.fibreFieldHom_eq_smallerBaseRingHom`: the
  `κ(t)`-structure used by `AlgebraicGeometry.Space.CoherentObject.twistedEuler` is the one
  induced by the projection `X_t ⟶ Spec κ(t)`.
* `AlgebraicGeometry.Space.CoherentObject.twistedEuler_eq_finsum_fibreOverPoint`: **the twisted
  Euler characteristic is computed over `Spec κ(t)`.**

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.CoherentObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- The morphism `Spec κ(t) ⟶ S` of the big fppf site underlying a point `t` of the test scheme
of an object of `Coh_{X/B}`. -/
abbrev pointSchemeHom' (A : CoherentObject D) (t : A.testScheme) :
    B.obj (B.residueField_spec_contains A.T.left.left.property t) ⟶ B.obj hS :=
  ObjectProperty.homMk (A.testScheme.fromSpecResidueField t ≫ B.inclusion.map A.T.left.hom)

/-- **The fibre `X_t` as an algebraic space over `Spec κ(t)`**, through its projection to
`Spec κ(t)` (Stacks 04SG). -/
def fibreOverPoint (A : CoherentObject D) (t : A.testScheme) :
    AlgebraicSpaces B (Spec (.of (A.testScheme.residueField t)))
      (B.residueField_spec_contains A.T.left.left.property t) :=
  spaceOverSmallerBase B _ S _ hS (A.pointSchemeHom' t) (A.fibreSpace t)
    (D.projection (A.pointTest t)).hom

/-- **The modules on the fibre over `S` and over `Spec κ(t)` are the same.** -/
def fibreModulesEquivalence (A : CoherentObject D) (t : A.testScheme) :
    Modules.{u, u} B S hS (A.fibreSpace t).1 (A.fibreSpace t).2 ≌
      Modules.{u, u} B _ _ (A.fibreOverPoint t).1 (A.fibreOverPoint t).2 :=
  smallerBaseModulesEquivalence.{u, u} B _ S _ hS (A.pointSchemeHom' t) (A.fibreSpace t)
    (D.projection (A.pointTest t)).hom

/-- The `κ(t)`-structure on the cohomology of the fibre used by
`AlgebraicGeometry.Space.CoherentObject.twistedEuler` is the one induced by the projection
`X_t ⟶ Spec κ(t)`. -/
theorem fibreFieldHom_eq_smallerBaseRingHom (A : CoherentObject D) (t : A.testScheme) :
    A.fibreFieldHom t =
      smallerBaseRingHom B S hS (A.fibreSpace t) (A.testScheme.residueField t) _
        (A.pointSchemeHom' t) (D.projection (A.pointTest t)).hom :=
  rfl

/-- **The twisted Euler characteristic is computed over the residue field.** For an object
`(T, 𝓕)` of `Coh_{X/B}`, a point `t ∈ T` and `n ∈ ℤ`, `χ(X_t, 𝓕_t ⊗ L_t^{⊗ n})` is the
alternating sum of the `κ(t)`-dimensions of the cohomology over the base `Spec κ(t)` of the
corresponding module on the fibre `X_t` viewed as an algebraic space over `Spec κ(t)`. -/
theorem twistedEuler_eq_finsum_fibreOverPoint (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (A : CoherentObject D) (t : A.testScheme) (n : ℤ) :
    twistedEuler L A t n =
      ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * (Module.finrank (A.testScheme.residueField t)
        (cohomologyOverBase.{u, u + 1} (A.testScheme.residueField t) B _ (A.fibreOverPoint t).1
          (A.fibreOverPoint t).2
          (SheafOfModules.uliftForPresentation.{u + 1, u, u, u, u + 1}
            ((A.fibreModulesEquivalence t).functor.obj
              (((Stacks.SheafOfModules.Tensor.sheafTensor
                (smallEtaleRingedSite B S hS (A.fibreSpace t).1 (A.fibreSpace t).2).O).obj
                  (A.fibreModule t)).obj
                ((modulePullback B S hS (baseChangeProjection D.f (A.pointTest t))).obj
                  (invertibleTensorPower B S hS D.X.1 D.X.2 L n))))) i) : ℤ) :=
  eulerCharacteristicAlong_eq_finsum_spaceOverSmallerBase B S hS (A.fibreSpace t)
    (A.testScheme.residueField t) _ (A.pointSchemeHom' t) (D.projection (A.pointTest t)).hom _

end AlgebraicGeometry.Space.CoherentObject

end
