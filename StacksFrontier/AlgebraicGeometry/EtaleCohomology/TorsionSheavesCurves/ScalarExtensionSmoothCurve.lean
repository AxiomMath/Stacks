module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

/-!
# Extending an algebraically closed ground field of a smooth curve

Let `k` be an algebraically closed field, `k'/k` an extension of fields and `X` a curve over `k`.
Then the scalar extension `X_{k'} = X ×_k k'` is again a curve over `k'`, and it is smooth over
`k'` when `X` is smooth over `k`. This is the input that lets every result proved for smooth
curves over an algebraically closed field be applied to `X_{k'}` as well, for `k'`
algebraically closed, which is how statements (6) and (7) of Situation 0A52 are reached in Case I
of Tag 0A5B.

The curve clause has two parts. Integrality: over an algebraically closed (hence separably
closed and perfect) field an irreducible reduced scheme is geometrically irreducible
(Tag 020J) and geometrically reduced (Tag 020I), hence geometrically integral, so its base
change to the spectrum of a field is integral. Dimension: the Krull dimension is unchanged by an
extension of the ground field (Tag 0BY9, dimension clause, which needs only local finite type).
Separatedness, finite type and smoothness are stable under base change.

## Main results

* `Stacks.EtaleCohomology.isIntegral_scalarExtension`: `X_{k'}` is integral.
* `Stacks.EtaleCohomology.isCurve_scalarExtension`: `X_{k'}` is a curve over `k'`.
* `Stacks.EtaleCohomology.smooth_scalarExtension`: `X_{k'}` is smooth over `k'` when `X` is
  smooth over `k`.

## References

* [Stacks Project, Tag 0A5B](https://stacks.math.columbia.edu/tag/0A5B)
* [Stacks Project, Tag 020J](https://stacks.math.columbia.edu/tag/020J)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [Algebra k k']

/-- The structure morphism of the scalar extension `X_{k'}` to `Spec k'`. -/
abbrev scalarExtensionSnd {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) :
    scalarExtension k k' g ⟶ Spec (.of k') :=
  pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap k k')))

/-- An integral scheme over an algebraically closed field `k` is geometrically integral, so its
scalar extension to any field `k'` is integral. -/
theorem isIntegral_scalarExtension {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsIntegral X] : IsIntegral (scalarExtension k k' g) := by
  have : GeometricallyIrreducible g :=
    geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X g
  have : GeometricallyReduced g := geometricallyReduced_of_isReduced g
  have : GeometricallyIntegral g :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible g
  exact GeometricallyIntegral.isIntegral_of_subsingleton (scalarExtensionSnd k k' g)

/-- **The scalar extension of a curve over an algebraically closed field is a curve.** If `X` is
a curve over an algebraically closed field `k` and `k'/k` is a field extension, then
`X_{k'} = X ×_k k'` is a curve over `k'`. -/
theorem isCurve_scalarExtension {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] :
    IsCurve k' (scalarExtensionSnd k k' g) := by
  have : IsIntegral (scalarExtension k k' g) := isIntegral_scalarExtension k k' g
  have hdim : topologicalKrullDim (scalarExtension k k' g) = topologicalKrullDim X :=
    topologicalKrullDim_baseChange k k' (scalarExtensionFst k k' g) (scalarExtensionSnd k k' g)
      g (IsPullback.of_hasPullback _ _)
  exact
    { toIsVariety := { }
      topologicalKrullDim_eq_one := hdim.trans (IsCurve.topologicalKrullDim_eq_one (f := g)) }

omit [IsAlgClosed k] in
/-- The scalar extension of a smooth scheme over `k` is smooth over `k'`. -/
theorem smooth_scalarExtension {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [Smooth g] :
    Smooth (scalarExtensionSnd k k' g) :=
  inferInstance

end Stacks.EtaleCohomology

end
