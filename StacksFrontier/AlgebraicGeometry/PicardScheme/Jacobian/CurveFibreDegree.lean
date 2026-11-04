module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.JacobianOfPicardZero

/-!
# Fibres of a base change of a smooth geometrically irreducible curve

Let `f : X ⟶ Spec k` be smooth and geometrically irreducible, let `T` be a `k`-scheme and let
`π : X_T ⟶ T` be the base change. Every fibre of `π` is integral: it is the base change of `X`
along `Spec κ(t) ⟶ Spec k`, and `X` is geometrically integral over `k`.

## Main results

* `Stacks.RigidifiedPicard.isPullback_fiber_bcProj`: the fibre of `π` over `t` is the base
  change of `f` along `Spec κ(t) ⟶ T ⟶ Spec k`.
* `Stacks.RigidifiedPicard.isIntegral_curveFibre`: the fibre is integral.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The fibre of a base change is a base change.** The fibre of `X_T ⟶ T` over `t` is the
fibre product of `X` and `Spec κ(t)` over `Spec k`. -/
theorem isPullback_fiber_bcProj (T : Over (Spec (.of k))) (t : T.left) :
    IsPullback ((pullback.snd f T.hom).fiberι t ≫ pullback.fst f T.hom)
      ((pullback.snd f T.hom).fiberToSpecResidueField t) f
      (T.left.fromSpecResidueField t ≫ T.hom) :=
  IsPullback.paste_horiz (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback f T.hom)

/-- **The fibres of a base change of a smooth geometrically irreducible scheme over a field are
integral.** -/
theorem isIntegral_curveFibre [Smooth f] [GeometricallyIrreducible f] (T : Over (Spec (.of k)))
    (t : T.left) : IsIntegral ((pullback.snd f T.hom).fiber t) := by
  have := geometricallyIntegral_of_smooth f
  exact GeometricallyIntegral.geometrically_isIntegral (f := f) _ _ _
    (isPullback_fiber_bcProj f T t)

end Stacks.RigidifiedPicard
