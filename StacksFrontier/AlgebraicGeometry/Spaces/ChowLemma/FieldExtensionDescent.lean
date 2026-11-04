module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic

/-!
# Equality of morphisms of the site descends along a field extension

The surjectivity step of [Stacks, Tag 089J] needs to turn a coincidence detected on *points* —
membership of a point of the fibre power in the range of the diagonal — back into an equality of
*morphisms* out of the spectrum of a field. A point-level coincidence over a field `K` is only a
coincidence after some extension `L/K`, so what is needed is that equality of morphisms out of
the spectrum of a field descends along a field extension.

That holds for a reason having nothing to do with fields: a morphism of schemes which is flat,
surjective and quasi-compact is an effective epimorphism, because representable presheaves are
sheaves for the fpqc topology. A morphism of the big fppf category over `S` is determined by its
underlying morphism of schemes, so the same cancellation holds in the site. For
`Spec L ⟶ Spec K` induced by a homomorphism of fields all three conditions are instances —
a field extension is flat, a morphism of one-point spaces onto a one-point space is surjective,
and an affine morphism is quasi-compact — with no finiteness assumption on `L/K`.

## Main results

* `AlgebraicGeometry.Space.eq_of_comp_eq_of_flat_surjective_quasiCompact`: **equality of
  morphisms of the big fppf category over `S` is cancellable by a flat, surjective,
  quasi-compact morphism.**
* `AlgebraicGeometry.Space.injective_comp_of_flat_surjective_quasiCompact`: the same, as
  injectivity of precomposition.

## What is and is not proved

No declaration here carries a Stacks attribute: the statement is Mathlib's
`AlgebraicGeometry.Scheme` instance making a flat surjective quasi-compact morphism an effective
epimorphism, transported along the faithful functor
`AlgebraicGeometry.BigFppfOver.toScheme` by
`AlgebraicGeometry.BigFppfOver.map_toScheme_injective`.

This is **not** the valuation-ring descent
`AlgebraicGeometry.Space.eq_of_comp_eq_of_isSeparated`, which cancels the inclusion of the
generic point of a valuation ring and needs separatedness of the ambient algebraic space over
the base; here the target is an object of the site, no separatedness is needed, and the morphism
cancelled is a cover rather than a dominant monomorphism.

Nothing about [Stacks, Tag 089J] is proved here; the surjectivity of its cover remains open.

## References

* [Stacks Project, Tag 023Q](https://stacks.math.columbia.edu/tag/023Q)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Equality of morphisms of the big fppf category over `S` is cancellable by a flat,
surjective, quasi-compact morphism.** Such a morphism of schemes is an effective epimorphism,
hence an epimorphism; and a morphism of the site is determined by its underlying morphism of
schemes.

For `ε` whose underlying morphism is `Spec L ⟶ Spec K` induced by a homomorphism of fields the
three hypotheses are instances, with no finiteness assumption on the extension. -/
theorem eq_of_comp_eq_of_flat_surjective_quasiCompact {T' T Z : BigFppfOver B S hS} (ε : T' ⟶ T)
    (hqc : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map ε))
    (hsurj : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map ε))
    (hflat : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map ε))
    (a b : T ⟶ Z) (h : ε ≫ a = ε ≫ b) : a = b := by
  have := hqc
  have := hsurj
  have := hflat
  have hepi : Epi ((BigFppfOver.toScheme B S hS).map ε) := inferInstance
  refine BigFppfOver.map_toScheme_injective B S hS ?_
  refine (cancel_epi ((BigFppfOver.toScheme B S hS).map ε)).mp ?_
  rw [← Functor.map_comp, ← Functor.map_comp, h]

/-- **Precomposition with a flat, surjective, quasi-compact morphism of the big fppf category
over `S` is injective on morphisms into any object.** This is
`AlgebraicGeometry.Space.eq_of_comp_eq_of_flat_surjective_quasiCompact` restated as the
injectivity which the point-to-morphism step of [Stacks, Tag 089J] consumes. -/
theorem injective_comp_of_flat_surjective_quasiCompact {T' T Z : BigFppfOver B S hS} (ε : T' ⟶ T)
    (hqc : AlgebraicGeometry.QuasiCompact ((BigFppfOver.toScheme B S hS).map ε))
    (hsurj : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map ε))
    (hflat : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map ε)) :
    Function.Injective (fun a : T ⟶ Z ↦ ε ≫ a) := fun a b h ↦
  eq_of_comp_eq_of_flat_surjective_quasiCompact B S hS ε hqc hsurj hflat a b h

end AlgebraicGeometry.Space

end
