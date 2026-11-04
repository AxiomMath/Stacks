module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibres of locally algebraic schemes

Let `f : X ⟶ Y` be a morphism of schemes over a field, with `X` locally of finite type over
that field. Every scheme-theoretic fibre of `f` is then locally of finite type over the residue
field of its base point, so the dimension theory of locally algebraic schemes applies to it.

## Main results

* `AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField`: the fibres of a
  morphism locally of finite type are locally of finite type over the residue fields of their
  base points.
* `AlgebraicGeometry.locallyOfFiniteType_fiberToSpecResidueField`: every fibre is locally
  algebraic over its residue field.
* `AlgebraicGeometry.isLocallyNoetherian_fiber_of_locallyOfFiniteType`: every fibre of a
  morphism locally of finite type is locally Noetherian.
* `AlgebraicGeometry.finite_irreducibleComponents_fiber`: a fibre of a quasi-compact morphism
  locally of finite type has finitely many irreducible components.

## Implementation notes

Being locally of finite type is stable under base change, and a fibre is a base change, so the
general statement needs no base field at all and is registered as an instance: the hypothesis is
`LocallyOfFiniteType f` and nothing else.

A locally algebraic `k`-scheme is represented by its structure morphism to `Spec k` together
with a `LocallyOfFiniteType` instance, and the equality of structure morphisms records that `f`
is a morphism of `k`-schemes. Only local algebraicity of the source is needed, so no hypothesis
is imposed on `Y` beyond its structure morphism; it enters only to make `f` itself locally of
finite type, which is what the general instance consumes. The conclusion is stated for Mathlib's
canonical morphism `Scheme.Hom.fiberToSpecResidueField`.

## References

* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The fibre of a morphism locally of finite type is locally of finite type over the residue
field of its base point: the fibre is the base change of `f` along
`Scheme.fromSpecResidueField`. -/
@[ega "I 6.4.11" "partial"]
public instance Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y) :
    LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
  change LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField y))
  infer_instance

/-- A fibre of a morphism between locally algebraic schemes is locally algebraic over the
residue field of the corresponding point. -/
@[stacks 0B2L "locally_algebraic_fibre"]
public theorem locallyOfFiniteType_fiberToSpecResidueField
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (y : Y) :
    LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
  let _ : LocallyOfFiniteType (f ≫ pY) := by rw [hf]; infer_instance
  let _ : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f pY
  infer_instance

/-- **The fibres of a morphism locally of finite type are locally Noetherian.** The fibre over
`y` is locally of finite type over the residue field at `y`, and a scheme locally of finite type
over a locally Noetherian scheme is locally Noetherian. -/
public theorem isLocallyNoetherian_fiber_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (y : Y) : IsLocallyNoetherian (f.fiber y) :=
  have : IsLocallyNoetherian (Spec (Y.residueField y)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)

/-- A fibre of a quasi-compact morphism locally of finite type has finitely many irreducible
components: the fibre is locally Noetherian and compact, hence a Noetherian scheme. -/
public theorem finite_irreducibleComponents_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] (y : Y) :
    (irreducibleComponents (f.fiber y)).Finite :=
  have : IsLocallyNoetherian (f.fiber y) := isLocallyNoetherian_fiber_of_locallyOfFiniteType f y
  have : AlgebraicGeometry.IsNoetherian (f.fiber y) := ⟨⟩
  finite_irreducibleComponents_of_isNoetherian

end AlgebraicGeometry

end
