module

public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Sections of a sheaf of commutative rings form a sheaf of types, in any universe

For a sheaf of commutative rings `𝒯` on a site `(C, J)` the presheaf of *sets* of its sections
`U ↦ 𝒯(U)` is a sheaf of types. No condition relating the universe of the sections to the
universes of the site is needed.

This is the easy half of `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`, whose forgetful
functor has to land in `Type (max v u)` — the join of the two universes of the site — and which
is therefore unusable when the sections of the sheaves of rings live in a universe of their own.
Several files of this development record that obstruction; the way around it for *this* half is
that the sheaf condition for an `A`-valued presheaf is by definition the sheaf condition for
`U ↦ (E ⟶ P U)` for every object `E` of `A`, so it suffices to take `E` corepresenting the
forgetful functor — the free commutative ring on one generator — and transport along the
adjunction. The hard half, which *constructs* a sheaf of rings from the sheaf condition on
sections, is not available this way and is not proved here.

## Main definitions

* `Stacks.Sites.RingSections.coyonedaFreeIso`: the natural identification of
  `U ↦ (ℤ[x] ⟶ 𝒯(U))` with `U ↦ 𝒯(U)`, where `ℤ[x]` is the free commutative ring on one
  generator in the universe of the sections.

## Main results

* `Stacks.Sites.RingSections.isSheaf_sections`: **the sections of a sheaf of commutative rings
  form a sheaf of types**, in any universe.
* `Stacks.Sites.RingSections.section_eq_of_locally_eq`: **two sections agreeing on a covering
  sieve are equal** — the separatedness half, which is what checking an identity of sheaf
  morphisms against local data comes down to.

## References

* [Stacks Project, Tag 00VM](https://stacks.math.columbia.edu/tag/00VM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace Stacks.Sites.RingSections

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The natural identification of the functor corepresented by the free commutative ring on one
generator with the sections functor. The free commutative ring is taken on `PUnit` in the
universe of the sections, so that it is an object of the same `CommRingCat`. -/
noncomputable def coyonedaFreeIso (P : Cᵒᵖ ⥤ CommRingCat.{w}) :
    (P ⋙ coyoneda.obj (op (CommRingCat.free.obj PUnit.{w + 1}))) ≅
      (P ⋙ forget CommRingCat.{w}) :=
  NatIso.ofComponents
    (fun U => Equiv.toIso
      { toFun := fun g => CommRingCat.adj.homEquiv PUnit.{w + 1} (P.obj U) g PUnit.unit
        invFun := fun x =>
          (CommRingCat.adj.homEquiv PUnit.{w + 1} (P.obj U)).symm
            (TypeCat.ofHom (fun _ => x))
        left_inv := fun g => by
          refine (Equiv.symm_apply_eq _).2 ?_
          ext u
          rfl
        right_inv := fun x => by
          simp only [Equiv.apply_symm_apply]
          rfl })
    (fun f => rfl)

/-- **The sections of a sheaf of commutative rings form a sheaf of types.** The ring universe is
arbitrary: no size condition relating it to the universes of the site is imposed. -/
theorem isSheaf_sections {P : Cᵒᵖ ⥤ CommRingCat.{w}} (h : Presheaf.IsSheaf J P) :
    Presieve.IsSheaf J (P ⋙ forget CommRingCat.{w}) :=
  Presieve.isSheaf_iso J (coyonedaFreeIso P) (h _)

/-- **The sections of a sheaf of commutative rings are separated:** two sections over an object
of the site which agree after restriction along every arrow of a covering sieve are equal.

This is the form in which the sheaf condition is used to check an identity between morphisms of
sheaves from local data. -/
theorem section_eq_of_locally_eq {P : Cᵒᵖ ⥤ CommRingCat.{w}} (h : Presheaf.IsSheaf J P)
    {X : C} {S : Sieve X} (hS : S ∈ J X) {s t : P.obj (op X)}
    (hst : ∀ ⦃Y : C⦄ (f : Y ⟶ X), S f → P.map f.op s = P.map f.op t) : s = t :=
  (isSheaf_sections J h S hS).isSeparatedFor.ext (fun _ f hf => hst f hf)

end Stacks.Sites.RingSections

end
