module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapSquare
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.FinitePointKernel

/-!
# Injectivity of a specialization map descends along a base change

Let
```
Y ⟶ X
↓     ↓
T ⟶ S
```
be a *cartesian* square of schemes whose vertical morphisms are proper with geometrically
connected fibres. A geometric point `t` of `T` has an image `s = t ∘ (T ⟶ S)` in `S`, and the
square induces a morphism `Y_t ⟶ X_s` of geometric fibres. When the square is cartesian that
morphism is an isomorphism: both schemes are the pullback of `X ⟶ S` along
`Spec κ(t) ⟶ T ⟶ S`.

Consequently injectivity of a specialization map transports *downwards*. Stacks 0C0K accompanies
a specialization map `π₁(Y_{t̄'}) → π₁(Y_{t̄})` of the top row by one of the bottom row and makes
the square of fundamental groups commute; the left-hand vertical map of that square is induced by
an isomorphism of schemes, hence injective, so injectivity of the bottom specialization map forces
injectivity of the top one. This is the step by which a statement about specialization maps over an
arbitrary base is reduced to the same statement over a smaller base — a Noetherian model, say — of
which the given situation is a base change.

## Main results

* `AlgebraicGeometry.isIso_fiberOverGeometricPointSquareMap`: the morphism of geometric fibres
  determined by a cartesian square is an isomorphism.
* `AlgebraicGeometry.injective_isSpecializationMap_of_isPullback`: injectivity of every
  specialization map of the bottom row of a cartesian square implies injectivity of a given
  specialization map of the top row.

## Implementation notes

The hypothesis of `AlgebraicGeometry.injective_isSpecializationMap_of_isPullback` quantifies over
the specialization maps of the bottom row rather than naming one: Stacks 0C0K produces a
specialization map of the bottom row from the given one, but which one it produces is not part of
its statement, so the reduction cannot be phrased against a specific bottom map.

## References

* [Stacks Project, Tag 0C0K](https://stacks.math.columbia.edu/tag/0C0K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {Y X T S : Scheme.{u}}

/-- **The morphism of geometric fibres determined by a cartesian square is an isomorphism.** For
a cartesian square with `a : Y ⟶ X` on top, `g : Y ⟶ T` and `f : X ⟶ S` vertical and `b : T ⟶ S`
on the bottom, and a geometric point `t` of `T`, the morphism `Y_t ⟶ X_{t ∘ b}` is an
isomorphism: pasting the cartesian square of the fibre `Y_t` with the given one exhibits `Y_t` as
a pullback of `f` along `t ∘ b`, and the morphism is the comparison of that pullback with the
chosen one. -/
theorem isIso_fiberOverGeometricPointSquareMap (a : Y ⟶ X) (g : Y ⟶ T) (f : X ⟶ S) (b : T ⟶ S)
    (hsq : IsPullback a g f b) (t : GeometricPoint T) :
    IsIso (fiberOverGeometricPointSquareMap a g f b hsq.w t) := by
  have H : IsPullback (pullback.fst g t.hom ≫ a) (pullback.snd g t.hom) f (t.map b).hom :=
    (IsPullback.of_hasPullback g t.hom).paste_horiz hsq
  have heq : fiberOverGeometricPointSquareMap a g f b hsq.w t = H.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [H.isoPullback_hom_fst]
      exact pullback.lift_fst _ _ _
    · rw [H.isoPullback_hom_snd]
      exact pullback.lift_snd _ _ _
  rw [heq]
  infer_instance

/-- **Injectivity of a specialization map descends along a base change.** Let
```
Y ⟶ X
↓     ↓
T ⟶ S
```
be a cartesian square whose vertical morphisms `g : Y ⟶ T` and `f : X ⟶ S` are proper with
geometrically connected fibres, let `t'` and `t` be geometric points of `T` and let
`sp : π₁(Y_{t̄'}) → π₁(Y_{t̄})` be a specialization map. If every specialization map
`π₁(X_{s̄'}) → π₁(X_{s̄})` between the geometric fibres over the images of `t'` and `t`, taken at
the base points induced by the square, is injective, then `sp` is injective.

Stacks 0C0K produces such a specialization map `sp'` of the bottom row together with the
commuting square
```
π₁(Y_{t̄'}) ⟶ π₁(Y_{t̄})
    ↓              ↓
π₁(X_{s̄'}) ⟶ π₁(X_{s̄})
```
whose left vertical map is induced by the morphism `Y_{t̄'} ⟶ X_{s̄'}` of geometric fibres. That
morphism is an isomorphism because the square is cartesian
(`AlgebraicGeometry.isIso_fiberOverGeometricPointSquareMap`), so the left vertical map is
injective, and the commuting square turns injectivity of `sp'` into injectivity of `sp`. -/
theorem injective_isSpecializationMap_of_isPullback (a : Y ⟶ X) (g : Y ⟶ T) (f : X ⟶ S)
    (b : T ⟶ S) (hsq : IsPullback a g f b) [IsProper f] [GeometricallyConnected f] [IsProper g]
    [GeometricallyConnected g] (t' t : GeometricPoint T)
    (y' : GeometricPoint (fiberOverGeometricPoint g t'))
    (y : GeometricPoint (fiberOverGeometricPoint g t))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint g t') y' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint g t) y)
    (hsp : IsSpecializationMap g t' t y' y sp)
    (H : ∀ sp' : EtaleFundamentalGroup (fiberOverGeometricPoint f (t'.map b))
            (y'.map (fiberOverGeometricPointSquareMap a g f b hsq.w t')) →ₜ*
          EtaleFundamentalGroup (fiberOverGeometricPoint f (t.map b))
            (y.map (fiberOverGeometricPointSquareMap a g f b hsq.w t)),
        IsSpecializationMap f (t'.map b) (t.map b)
            (y'.map (fiberOverGeometricPointSquareMap a g f b hsq.w t'))
            (y.map (fiberOverGeometricPointSquareMap a g f b hsq.w t)) sp' →
          Function.Injective sp') :
    Function.Injective sp := by
  obtain ⟨sp', hsp', hcomm⟩ :=
    exists_isSpecializationMap_comm_square a g f b hsq.w t' t y' y sp hsp
  have := isIso_fiberOverGeometricPointSquareMap a g f b hsq t'
  have hinj' : Function.Injective (etaleFundamentalGroupMap
      (fiberOverGeometricPointSquareMap a g f b hsq.w t') y') :=
    injective_etaleFundamentalGroupMap_of_isIso _ y'
  intro γ₁ γ₂ hγ
  refine hinj' (H sp' hsp' ?_)
  rw [← hcomm γ₁, ← hcomm γ₂, hγ]

end AlgebraicGeometry

end
