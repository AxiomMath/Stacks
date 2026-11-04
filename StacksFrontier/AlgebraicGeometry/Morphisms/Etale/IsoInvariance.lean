module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs

/-!
# Étaleness at a point is invariant under isomorphisms

Étaleness of a morphism of schemes at a point of its source is unchanged by replacing the source
and the target by isomorphic schemes: along an isomorphism of the source, along an isomorphism of
the target, and along a commuting square whose two horizontal maps are isomorphisms.

## Main results

* `AlgebraicGeometry.etaleAt_isIso_comp`: étaleness at a point ascends along an isomorphism of the
  source.
* `AlgebraicGeometry.etaleAt_comp_isIso_iff`: étaleness at a point is unchanged by composing with
  an isomorphism of the target.
* `AlgebraicGeometry.etaleAt_of_isIso_square`: for a commuting square `f ≫ v = u ≫ g` with `u`
  and `v` isomorphisms, étaleness of `f` at `x` gives étaleness of `g` at `u x`.

## Implementation notes

`AlgebraicGeometry.EtaleAt` is the existence of a pair of affine opens, one in the source around
the point and one in the target, over which the map on sections is étale. The two affine opens are
moved across the isomorphisms by `AlgebraicGeometry.IsAffineOpen.preimage_of_isIso`, and the new
map on sections is the composite of the old one with the map on sections of an isomorphism, which
is étale by `AlgebraicGeometry.Etale.etale_appLE`.

## References

* [Stacks Project, Tag 02GI](https://stacks.math.columbia.edu/tag/02GI)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y S T : Scheme.{u}}

/-- **Étaleness at a point ascends along an isomorphism of the source.** -/
theorem etaleAt_isIso_comp (u : X ⟶ Y) [IsIso u] (f : Y ⟶ S) {x : X}
    (h : EtaleAt f (u.base x)) : EtaleAt (u ≫ f) x := by
  obtain ⟨U, hU, hxU, V, hV, hUV, hEt⟩ := h
  refine ⟨u ⁻¹ᵁ U, hU.preimage_of_isIso u, hxU, V, hV, fun z hz => hUV hz, ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE u f V U (u ⁻¹ᵁ U) hUV le_rfl]
  simpa only [CommRingCat.hom_comp] using
    RingHom.Etale.stableUnderComposition _ _ hEt
      (u.etale_appLE hU (hU.preimage_of_isIso u) le_rfl)

/-- Étaleness at a point ascends along an isomorphism of the target. -/
private theorem etaleAt_comp_isIso (f : X ⟶ S) (v : S ⟶ T) [IsIso v] {x : X}
    (h : EtaleAt f x) : EtaleAt (f ≫ v) x := by
  obtain ⟨U, hU, hxU, V, hV, hUV, hEt⟩ := h
  have hpre : v ⁻¹ᵁ (inv v ⁻¹ᵁ V) = V := by
    rw [← Scheme.Hom.comp_preimage, IsIso.hom_inv_id, Scheme.Hom.id_preimage]
  have hUV₂ : U ≤ (f ≫ v) ⁻¹ᵁ (inv v ⁻¹ᵁ V) := by
    rwa [Scheme.Hom.comp_preimage, hpre]
  refine ⟨U, hU, hxU, inv v ⁻¹ᵁ V, hV.preimage_of_isIso (inv v), hUV₂, ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE f v (inv v ⁻¹ᵁ V) V U hpre.ge hUV]
  simpa only [CommRingCat.hom_comp] using
    RingHom.Etale.stableUnderComposition _ _
      (v.etale_appLE (hV.preimage_of_isIso (inv v)) hV hpre.ge) hEt

/-- **Étaleness at a point is unchanged when the target is replaced by an isomorphic scheme.** -/
theorem etaleAt_comp_isIso_iff (f : X ⟶ S) (v : S ⟶ T) [IsIso v] (x : X) :
    EtaleAt (f ≫ v) x ↔ EtaleAt f x := by
  refine ⟨fun h => ?_, fun h => etaleAt_comp_isIso f v h⟩
  simpa only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] using
    etaleAt_comp_isIso (f ≫ v) (inv v) h

/-- **Étaleness at a point is transported by isomorphisms of the source and of the target.** If
```
X --u--> Y
|        |
f        g
↓        ↓
S --v--> T
```
commutes and `u` and `v` are isomorphisms, then étaleness of `f` at `x` is étaleness of `g` at the
image of `x`. -/
theorem etaleAt_of_isIso_square {f : X ⟶ S} {g : Y ⟶ T} (u : X ⟶ Y) [IsIso u] (v : S ⟶ T)
    [IsIso v] (w : f ≫ v = u ≫ g) {x : X} (h : EtaleAt f x) : EtaleAt g (u.base x) := by
  have hg : inv u ≫ f ≫ v = g := by rw [w, IsIso.inv_hom_id_assoc]
  have hx : (inv u).base (u.base x) = x := by
    rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
    rfl
  have h2 : EtaleAt (f ≫ v) ((inv u).base (u.base x)) := by
    rw [hx]; exact etaleAt_comp_isIso f v h
  simpa only [hg] using etaleAt_isIso_comp (inv u) (f ≫ v) h2

end AlgebraicGeometry

end
