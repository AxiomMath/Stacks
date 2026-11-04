module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# The pushout of two open immersions out of a common scheme

Mathlib's locally directed glueing makes `CategoryTheory.Limits.pushout f₁ f₂` exist for *any* two
open immersions `f₁ : Z ⟶ X` and `f₂ : Z ⟶ Y` out of a common scheme, with no glueing datum, no
cocycle condition and no hypothesis beyond the two open immersions.  This file records the two
facts that let that pushout be used as the glueing of `X` and `Y` along `Z`: its two legs cover it,
and they meet exactly in the image of `Z`.

Both are read off the locally directed colimit API of `Mathlib/AlgebraicGeometry/Gluing.lean`:
`pushout f₁ f₂` is the colimit of `CategoryTheory.Limits.span f₁ f₂`, a diagram of open immersions
over the three-object index category `CategoryTheory.Limits.WalkingSpan`, and the colimit of such a
diagram is covered by the images of its objects
(`AlgebraicGeometry.Scheme.IsLocallyDirected.ι_jointly_surjective`) with two points identified in
it exactly when they are already identified somewhere in the diagram
(`AlgebraicGeometry.Scheme.IsLocallyDirected.ι_eq_ι_iff`).

## Main results

* `AlgebraicGeometry.opensRange_pushout_inl_sup_inr`: the two legs of the pushout cover it.
* `AlgebraicGeometry.opensRange_pushout_inl_inf_inr`: the two legs meet exactly in the image of the
  common source.

## Implementation notes

That the two legs are open immersions needs no statement here.  `CategoryTheory.Limits.pushout.inl`
is a reducible abbreviation for `CategoryTheory.Limits.colimit.ι`, so Mathlib's instance
`IsOpenImmersion (colimit.ι F i)` for a locally directed diagram `F` of open immersions already
fires on `pushout.inl f₁ f₂` and `pushout.inr f₁ f₂` by `inferInstance`.

The `⊓` computation uses that `CategoryTheory.Limits.WalkingSpan` has *no* morphism between its two
outer objects: a point of the pushout lying in both legs is therefore identified in the diagram
over the central object, where the two structure morphisms are `f₁` and `f₂`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The two legs of the pushout of two open immersions cover it. -/
public lemma opensRange_pushout_inl_sup_inr {Z X Y : Scheme.{u}} (f₁ : Z ⟶ X) (f₂ : Z ⟶ Y)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] :
    (pushout.inl f₁ f₂).opensRange ⊔ (pushout.inr f₁ f₂).opensRange = ⊤ := by
  apply Opens.ext
  rw [Opens.coe_sup, Opens.coe_top, Set.eq_univ_iff_forall]
  intro x
  obtain ⟨i, xi, hxi⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f₁ f₂) x
  rw [Set.mem_union]
  match i, xi, hxi with
  | WalkingSpan.left, xi, hxi => exact Or.inl ⟨xi, hxi⟩
  | WalkingSpan.right, xi, hxi => exact Or.inr ⟨xi, hxi⟩
  | WalkingSpan.zero, xi, hxi =>
    -- The central object maps to the pushout through the left leg, by `f₁`.
    have h : f₁ ≫ pushout.inl f₁ f₂ = colimit.ι (span f₁ f₂) WalkingSpan.zero :=
      colimit.w (span f₁ f₂) WalkingSpan.Hom.fst
    exact Or.inl ⟨f₁ xi, by rw [← hxi, ← h, Scheme.Hom.comp_apply]⟩

/-- The two legs of the pushout of two open immersions meet exactly in the image of the common
source. -/
public lemma opensRange_pushout_inl_inf_inr {Z X Y : Scheme.{u}} (f₁ : Z ⟶ X) (f₂ : Z ⟶ Y)
    [IsOpenImmersion f₁] [IsOpenImmersion f₂] :
    (pushout.inl f₁ f₂).opensRange ⊓ (pushout.inr f₁ f₂).opensRange
      = (f₁ ≫ pushout.inl f₁ f₂).opensRange := by
  apply Opens.ext
  rw [Opens.coe_inf]
  apply Set.Subset.antisymm
  · rintro x ⟨⟨xi, hxi⟩, ⟨xj, hxj⟩⟩
    have h : colimit.ι (span f₁ f₂) WalkingSpan.left xi
        = colimit.ι (span f₁ f₂) WalkingSpan.right xj := hxi.trans hxj.symm
    obtain ⟨k, fi, fj, z, hzi, -⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f₁ f₂)).mp h
    -- The only object of `WalkingSpan` admitting morphisms to both outer objects is the central
    -- one, and the morphism from it to the left object is `f₁`.
    match k, fi, fj with
    | WalkingSpan.zero, WalkingSpan.Hom.fst, _ =>
      exact ⟨z, by rw [Scheme.Hom.comp_apply]; exact (congrArg _ hzi).trans hxi⟩
    | WalkingSpan.left, _, fj => cases fj
    | WalkingSpan.right, fi, _ => cases fi
  · rintro x ⟨z, rfl⟩
    refine ⟨⟨f₁ z, ?_⟩, ⟨f₂ z, ?_⟩⟩
    · rw [Scheme.Hom.comp_apply]
    · rw [← Scheme.Hom.comp_apply, ← pushout.condition, Scheme.Hom.comp_apply]

end AlgebraicGeometry
