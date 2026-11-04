module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FieldBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricallyReducedFieldExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.UnibranchCriteria

/-!
# Geometrically irreducible and geometrically integral algebraic spaces

Let `k` be a field and let `X` be an algebraic space over `k`. Then `X` is *geometrically
irreducible* when the space of points of the base change `X_K` is irreducible for every field
extension `K/k`, and *geometrically integral* when `X_K` is an integral algebraic space for
every field extension `K/k`.

## Main definitions

* `AlgebraicGeometry.Space.specMapOfExtension` and `AlgebraicGeometry.Space.fieldBaseChange`:
  the morphism `Spec K ⟶ Spec k` of the big fppf site attached to a field extension, and the
  base change of an algebraic space over `k` along it.
* `AlgebraicGeometry.Space.IsGeometricallyIrreducible` is geometric irreducibility.
* `AlgebraicGeometry.Space.IsGeometricallyIntegral` is geometric integrality.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_fieldBaseChange`: the base change of an algebraic
  space along a field extension is an algebraic space.
* `AlgebraicGeometry.Space.IsGeometricallyIntegral.isGeometricallyIrreducible`: a
  geometrically integral algebraic space is geometrically irreducible.
* `AlgebraicGeometry.Space.isGeometricallyIntegral_iff` is Stacks 0DMX: for a decent algebraic
  space, geometric integrality is geometric reducedness together with geometric
  irreducibility.

## Implementation notes

Base change is restriction along the localization functor of the big fppf site, which is
Stacks 03I5 part (1) — `AlgebraicGeometry.isAlgebraicSpace_relocalizeRestrict` — so field
extensions are quantified over those fields `K` whose spectrum belongs to the chosen site.
This is the usual size restriction imposed by presenting algebraic spaces on a big site, not
a restriction on the extensions themselves.

Irreducibility of the space of points is `IrreducibleSpace` for the canonical topology
`AlgebraicGeometry.Space.pointTopology`; as in the source, an irreducible space is nonempty.
Neither definition carries a decency hypothesis: both conditions make sense without one, and
a client which needs decency — as Stacks 0DMU does in order to know that `|X_K|` is sober —
can carry it alongside.

## References

* [Stacks Project, Tag 0DMU](https://stacks.math.columbia.edu/tag/0DMU)
* [Stacks Project, Tag 0DMW](https://stacks.math.columbia.edu/tag/0DMW)
* [Stacks Project, Tag 0DMX](https://stacks.math.columbia.edu/tag/0DMX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))

/-- The morphism `Spec K ⟶ Spec k` of the big fppf site attached to a field extension
`K/k`. -/
noncomputable def specMapOfExtension (K : Type u) [Field K] [Algebra k K]
    (hK : B.Contains (Spec (.of K))) : B.obj hK ⟶ B.obj hk :=
  ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- The base change `X_K` of an algebraic space `X` over `k` along a field extension `K/k`,
obtained by restricting `X` along the localization functor of
`AlgebraicGeometry.Space.specMapOfExtension`. -/
noncomputable abbrev fieldBaseChange (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (K : Type u) [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K))) :
    (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u :=
  (OverShriek.relocalizeRestrict (specMapOfExtension B k hk K hK)).obj X

/-- The base change of an algebraic space over `k` along a field extension `K/k` is an
algebraic space over `K`. -/
theorem isAlgebraicSpace_fieldBaseChange (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (K : Type u) [Field K] [Algebra k K]
    (hK : B.Contains (Spec (.of K))) :
    IsAlgebraicSpace B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK) :=
  isAlgebraicSpace_relocalizeRestrict B (Spec (.of K)) (Spec (.of k)) hK hk
    (specMapOfExtension B k hk K hK) X hX

/-- **Stacks 0DMU.** An algebraic space over a field `k` is *geometrically irreducible* when
the space of points of its base change to every field extension of `k` is irreducible — in
particular nonempty. -/
@[stacks 0DMU]
def IsGeometricallyIrreducible (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K))),
    @IrreducibleSpace (points B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK))
      (pointTopology B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK))

/-- **Stacks 0DMW.** An algebraic space over a field `k` is *geometrically integral* when its
base change to every field extension of `k` is an integral algebraic space. -/
@[stacks 0DMW]
def IsGeometricallyIntegral (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K))),
    IsIntegralSpace B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK)

variable {B k hk}

/-- A geometrically irreducible algebraic space has irreducible space of points after base
change to any given field extension. -/
theorem IsGeometricallyIrreducible.irreducibleSpace_fieldBaseChange
    {X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (h : IsGeometricallyIrreducible B k hk X) (K : Type u) [Field K] [Algebra k K]
    (hK : B.Contains (Spec (.of K))) :
    @IrreducibleSpace (points B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK))
      (pointTopology B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK)) :=
  h K hK

/-- A geometrically integral algebraic space is integral after base change to any given field
extension. -/
theorem IsGeometricallyIntegral.isIntegralSpace_fieldBaseChange
    {X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u} (h : IsGeometricallyIntegral B k hk X)
    (K : Type u) [Field K] [Algebra k K] (hK : B.Contains (Spec (.of K))) :
    IsIntegralSpace B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK) :=
  h K hK

/-- A geometrically integral algebraic space is geometrically irreducible: an integral
algebraic space has irreducible space of points. -/
theorem IsGeometricallyIntegral.isGeometricallyIrreducible
    {X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u} (h : IsGeometricallyIntegral B k hk X) :
    IsGeometricallyIrreducible B k hk X :=
  fun K _ _ hK => (h K hK).2.2

/-! ### Geometric integrality of a decent algebraic space -/

section Decent

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
  (X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u)

/-- The morphism `Spec K ⟶ Spec k` of the big fppf site used to form the base change of an
algebraic space agrees with `AlgebraicGeometry.Space.fieldExtensionMap`. -/
theorem specMapOfExtension_eq_fieldExtensionMap (K : Type u) [Field K] [Algebra k K]
    (hK : B.Contains (Spec (.of K))) :
    specMapOfExtension B k hk K hK = fieldExtensionMap B k K hk hK :=
  B.inclusion.map_injective (by rw [map_fieldExtensionMap]; rfl)

/-- The base change of a decent algebraic space along a field extension is decent. -/
theorem isDecentSpace_fieldBaseChange (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hdecent : IsDecentSpace B (Spec (.of k)) hk X) (K : Type u) [Field K] [Algebra k K]
    (hK : B.Contains (Spec (.of K))) :
    IsDecentSpace B (Spec (.of K)) hK (fieldBaseChange B k hk X K hK) :=
  isDecentSpace_relocalizeRestrict B (Spec (.of k)) (Spec (.of K)) hk hK
    (specMapOfExtension B k hk K hK) X hX hdecent

/-- **Stacks 0E04 for the base change of this file.** An algebraic space over `k` is
geometrically reduced exactly when its base change to a field extension `K/k` is
geometrically reduced over `K`. -/
theorem isGeometricallyReduced_fieldBaseChange_iff (K : Type u) [Field K] [Algebra k K]
    (hK : B.Contains (Spec (.of K))) (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) :
    IsGeometricallyReduced k B hk X hX ↔
      IsGeometricallyReduced K B hK (fieldBaseChange B k hk X K hK)
        (isAlgebraicSpace_fieldBaseChange B k hk X hX K hK) := by
  rw [isGeometricallyReduced_relocalizeRestrict_iff k K B hk hK X hX,
    ← specMapOfExtension_eq_fieldExtensionMap B k hk K hK]

/-- **Stacks 0DMX.** A decent algebraic space over a field `k` is geometrically integral over
`k` exactly when it is geometrically reduced and geometrically irreducible over `k`. -/
@[stacks 0DMX]
theorem isGeometricallyIntegral_iff (hX : IsAlgebraicSpace B (Spec (.of k)) hk X)
    (hdecent : IsDecentSpace B (Spec (.of k)) hk X) :
    IsGeometricallyIntegral B k hk X ↔
      IsGeometricallyReduced k B hk X hX ∧ IsGeometricallyIrreducible B k hk X := by
  refine ⟨fun h => ⟨?_, h.isGeometricallyIrreducible⟩, fun h K _ _ hK => ?_⟩
  · have hK := contains_specAlgebraicClosure B k hk
    refine (isGeometricallyReduced_fieldBaseChange_iff B k hk X (AlgebraicClosure k) hK hX).mpr ?_
    exact isGeometricallyReduced_of_isReduced (AlgebraicClosure k) B hK _
      (isAlgebraicSpace_fieldBaseChange B k hk X hX (AlgebraicClosure k) hK)
      (h (AlgebraicClosure k) hK).1
  · refine ⟨?_, isDecentSpace_fieldBaseChange B k hk X hX hdecent K hK,
      h.2.irreducibleSpace_fieldBaseChange K hK⟩
    exact hasEtaleLocalProperty_isReduced_of_isGeometricallyReduced K B hK _
      (isAlgebraicSpace_fieldBaseChange B k hk X hX K hK)
      ((isGeometricallyReduced_fieldBaseChange_iff B k hk X K hK hX).mp h.1)

end Decent

end AlgebraicGeometry.Space

end
