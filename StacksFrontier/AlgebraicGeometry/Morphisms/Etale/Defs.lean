module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute

/-!
# Étale morphisms of schemes

A morphism of schemes is étale at a point if, on suitable affine open neighbourhoods of the point
and its image, the induced map on coordinate rings is étale. It is étale if it is étale at every
point of its source.

## Main definitions

* `AlgebraicGeometry.EtaleAt` says that a scheme morphism is étale at a specified point of its
  source.
* `AlgebraicGeometry.Etale` is the property that a morphism of schemes is étale.

## Main results

* `AlgebraicGeometry.etale_iff_forall_etaleAt` identifies the affine-local definition of étaleness
  with being étale at every point.
* `AlgebraicGeometry.etale_resLE_of_appLE_etale` and
  `AlgebraicGeometry.exists_isAffineOpen_etale_comp_ι_of_etaleAt` turn étaleness of a map on
  sections, respectively étaleness at a point, into étaleness of a morphism of schemes.

## Implementation notes

The affine schemes of the source are represented by affine opens. The condition that the image of
the source open lies in the target open is written as containment in its inverse image. The
coordinate-ring map is `AlgebraicGeometry.Scheme.Hom.appLE`, and its étaleness is Mathlib's
`RingHom.Etale`.

Mathlib's `AlgebraicGeometry.Etale` is adopted for the global notion; its affine-local
formulation is identified with the pointwise one by
`AlgebraicGeometry.etale_iff_forall_etaleAt`.

## References

* [Stacks Project, Tag 02GI](https://stacks.math.columbia.edu/tag/02GI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

add_to_stacks 02GI "etale_morphism" AlgebraicGeometry.Etale

/-- A morphism of schemes is étale at `x` if it induces an étale map on the
coordinate rings of some affine open neighbourhood of `x` and some affine
open neighbourhood of its image. -/
@[stacks 02GI "etale_at_point", sga "1 IX 1.1"]
public abbrev EtaleAt (f : X ⟶ S) (x : X) : Prop :=
  ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U) (V : S.Opens)
    (_ : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V), (f.appLE V U hUV).hom.Etale

/-- If the map on sections over a pair of affine opens is étale, so is the induced morphism of
open subschemes. -/
public theorem etale_resLE_of_appLE_etale (f : X ⟶ S)
    (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (h : (f.appLE V U e).hom.Etale) : Etale (f.resLE V U e) := by
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).2
    ((RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f V U e)).2 h)

/-- A morphism which is étale at a point is étale on some affine open neighbourhood of that
point. -/
public theorem exists_isAffineOpen_etale_comp_ι_of_etaleAt (f : X ⟶ S) (x : X)
    (h : EtaleAt f x) :
    ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : x ∈ U), Etale (U.ι ≫ f) := by
  obtain ⟨U, hU, hxU, V, hV, hUV, hEt⟩ := h
  have : Etale (f.resLE V U hUV) := etale_resLE_of_appLE_etale f U hU V hV hUV hEt
  refine ⟨U, hU, hxU, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f hUV]
  infer_instance

/-- A scheme morphism is étale if and only if it is étale at every point of its source. -/
public theorem etale_iff_forall_etaleAt (f : X ⟶ S) :
    Etale f ↔ ∀ x : X, EtaleAt f x := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @Etale)
    (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      (RingHom.Etale.propertyIsLocal.HoldsForLocalizationAway
        RingHom.Etale.containsIdentities)).1]
  constructor <;> intro h x
  · obtain ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, e, he⟩ := h x; exact ⟨U, hU, hx, V, hV, e, he⟩
  · obtain ⟨U, hU, hx, V, hV, e, he⟩ := h x; exact ⟨⟨V, hV⟩, ⟨U, hU⟩, hx, e, he⟩

end AlgebraicGeometry
