module

public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.NormalMorphism
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fibres of a normal morphism

A normal morphism of schemes, in the sense of Stacks Tag 0390, is flat with geometrically normal
fibres. This file records the two consequences of that definition which the spreading-out
arguments of Tags 057J and 057K use: each fibre, as a scheme over the residue field of its base
point, is geometrically normal, and a normal morphism is flat with geometrically reduced fibres.

A normal scheme stays normal along an open immersion; this is the version of Tag 033J for an
arbitrary open immersion rather than for an open subscheme.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsNormal.isGeometricallyNormal_fiber`: the fibres of a normal
  morphism are geometrically normal over the residue fields of their base points.
* `AlgebraicGeometry.Scheme.Hom.IsNormal.flat` and
  `AlgebraicGeometry.Scheme.Hom.IsNormal.geometricallyReduced`: a normal morphism is flat with
  geometrically reduced fibres.
* `AlgebraicGeometry.isNormal_of_isOpenImmersion`: normality passes to the source of an open
  immersion.

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.IsNormal` is stated pointwise, with the fibre condition attached to
the point `f.asFiber x` of the fibre over `f x`. Recovering the fibrewise statement over an
arbitrary point `s` of the base therefore means producing, for a point `y` of the fibre over `s`,
the point of `X` it comes from and the identification of `f.asFiber` of that point with `y`;
that is `AlgebraicGeometry.Scheme.Hom.isGeometricallyNormalAt_asFiber` below.

## References

* [Stacks Project, Tag 0390](https://stacks.math.columbia.edu/tag/0390)
* [Stacks Project, Tag 033J](https://stacks.math.columbia.edu/tag/033J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Normality passes to the source of an open immersion, the stalks being unchanged. -/
theorem isNormal_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    [IsNormal Y] : IsNormal X := by
  refine (isNormal_iff_stalk_normal X).2 fun x ↦ ?_
  let e := (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
  have : IsDomain (Y.presheaf.stalk (j x)) := IsNormal.stalk_isDomain (j x)
  have : IsIntegrallyClosed (Y.presheaf.stalk (j x)) := IsNormal.stalk_normal (j x)
  have : IsDomain (X.presheaf.stalk x) :=
    Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  exact ⟨inferInstance, id (IsIntegrallyClosed.of_equiv e)⟩

/-- The spectrum of an integrally closed domain is a normal scheme. -/
theorem isNormal_spec_of_isIntegrallyClosed (R : Type u) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsNormal (Spec (.of R)) :=
  isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed R)

namespace Scheme.Hom

/-- A geometrically normal scheme over a field is geometrically reduced. -/
theorem geometricallyReduced_of_isGeometricallyNormal {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (hf : IsGeometricallyNormal f) : GeometricallyReduced f :=
  (geometricallyReduced_iff_forall_isGeometricallyReducedAt f).2
    fun x K _ _ x' hx' ↦ IsNormalRing.isReduced (hf x K x' hx')

/-- Transporting the canonical point of a fibre along an equality of base points does not change
its image in the total space. -/
theorem fiberι_cast_asFiber {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) {y : Y} (hy : f x = y) :
    f.fiberι y (hy ▸ f.asFiber x) = x := by
  cases hy
  exact f.fiberι_asFiber x

/-- The fibre condition in the definition of a normal morphism, read at an arbitrary point of an
arbitrary fibre rather than at a point of the shape `f.asFiber x`. -/
private theorem isGeometricallyNormalAt_of_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : IsNormal f) (x : X) (s : S) (hx : f x = s) :
    ∀ y : f.fiber s, f.fiberι s y = x →
      IsGeometricallyNormalAt (f.fiberToSpecResidueField s) y := by
  cases hx
  intro y hy
  have hy' : y = f.asFiber x :=
    (f.fiberι (f x)).isEmbedding.injective (by simpa only [f.fiberι_asFiber] using hy)
  subst hy'
  exact (hf x).2

/-- **Stacks Project, Tag 0390.** Every fibre of a normal morphism is geometrically normal over
the residue field of its base point. -/
@[ega "IV 6.8.4" "6.8.4(ii)"]
theorem IsNormal.isGeometricallyNormal_fiber {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsNormal f)
    (s : S) : IsGeometricallyNormal (f.fiberToSpecResidueField s) := fun y ↦
  isGeometricallyNormalAt_of_fiberι f hf (f.fiberι s y) s (f.apply_fiberι s y) y rfl

/-- **Stacks Project, Tag 0391**, in the direction needed here: a normal morphism is flat. -/
theorem IsNormal.flat {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsNormal f) : Flat f :=
  Flat.of_stalkMap f fun x ↦ show IsFlatAt f.toLRSHom.toShHom x from (hf x).1

/-- A normal morphism has geometrically reduced fibres. -/
theorem IsNormal.geometricallyReduced {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsNormal f) :
    GeometricallyReduced f := by
  rw [GeometricallyReduced.eq_geometrically, geometrically_iff_forall_fiberToSpecResidueField]
  exact fun s ↦ (geometricallyReduced_of_isGeometricallyNormal _
    (hf.isGeometricallyNormal_fiber s)).geometrically_isReduced

end Scheme.Hom

end AlgebraicGeometry

end
