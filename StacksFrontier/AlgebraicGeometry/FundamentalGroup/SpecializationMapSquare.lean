module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapFunctoriality
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.StrictlyHenselianClosedGeometricFibre

/-!
# Specialization maps in a commutative square

Let
```
Y ⟶ X
↓     ↓
T ⟶ S
```
be a commutative square of schemes whose vertical morphisms are proper with geometrically
connected fibres, and let `t' ⇝ t` be a specialization of points of `T`. Every specialization map
`π₁(Y_{t̄'}) → π₁(Y_{t̄})` is accompanied by a specialization map `π₁(X_{s̄'}) → π₁(X_{s̄})`, where
`s̄'` and `s̄` are the images of `t̄'` and `t̄`, making the square of fundamental groups commute.
This is Stacks 0C0K.

## Main results

* `AlgebraicGeometry.exists_isSpecializationMap_comm_square` — Stacks 0C0K.

## Implementation notes

The construction — the strict henselization `A` of the stalk of `S`, the ring map `A → B` to the
strict henselization used on the top row (Stacks 04GU), the factorizations of the two geometric
points of `S` through `Spec A`, and the base-point bookkeeping — is
`AlgebraicGeometry.exists_isSpecializationMap_of_square`. Its one further input, that base change
along the closed geometric fibre `X_{s̄} ⟶ X ×_S Spec A` is an equivalence on finite étale covers,
is `AlgebraicGeometry.isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap`, which
derives it from Stacks 0A48, 0A49 and 0BTW.

## References

* [Stacks Project, Tag 0C0K](https://stacks.math.columbia.edu/tag/0C0K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

variable {Y X T S : Scheme.{u}}

/-- **Stacks Project, Tag 0C0K.** Consider a commutative square of schemes with `a : Y ⟶ X` on
top, `g : Y ⟶ T` and `f : X ⟶ S` vertical and `b : T ⟶ S` on the bottom, where `f` and `g` are
proper with geometrically connected fibres. Let `t'` and `t` be geometric points of `T` and let
`sp : π₁(Y_{t'}) → π₁(Y_t)` be a specialization map. Then there is a specialization map
`sp' : π₁(X_{s'}) → π₁(X_s)`, where `s'` and `s` are the images of `t'` and `t` in `S`, such that
the square formed by `sp`, `sp'` and the maps induced by the morphisms `Y_{t'} ⟶ X_{s'}` and
`Y_t ⟶ X_s` of geometric fibres commutes. -/
@[stacks 0C0K "The whole statement, under the source's hypotheses only."]
theorem exists_isSpecializationMap_comm_square (a : Y ⟶ X) (g : Y ⟶ T) (f : X ⟶ S)
    (b : T ⟶ S) (hab : a ≫ f = g ≫ b) [IsProper f] [GeometricallyConnected f] [IsProper g]
    [GeometricallyConnected g] (t' t : GeometricPoint T)
    (y' : GeometricPoint (fiberOverGeometricPoint g t'))
    (y : GeometricPoint (fiberOverGeometricPoint g t))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint g t') y' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint g t) y)
    (hsp : IsSpecializationMap g t' t y' y sp) :
    ∃ sp' : EtaleFundamentalGroup (fiberOverGeometricPoint f (t'.map b))
          (y'.map (fiberOverGeometricPointSquareMap a g f b hab t')) →ₜ*
        EtaleFundamentalGroup (fiberOverGeometricPoint f (t.map b))
          (y.map (fiberOverGeometricPointSquareMap a g f b hab t)),
      IsSpecializationMap f (t'.map b) (t.map b)
          (y'.map (fiberOverGeometricPointSquareMap a g f b hab t'))
          (y.map (fiberOverGeometricPointSquareMap a g f b hab t)) sp' ∧
        ∀ γ, etaleFundamentalGroupMap
              (fiberOverGeometricPointSquareMap a g f b hab t) y (sp γ)
          = sp' (etaleFundamentalGroupMap
              (fiberOverGeometricPointSquareMap a g f b hab t') y' γ) :=
  exists_isSpecializationMap_of_square a g f b hab t' t y' y sp hsp
    fun C _ _ _ r p hp hpclosed ↦
      isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap f (t.map b) C r p hp
        hpclosed

end AlgebraicGeometry

end
