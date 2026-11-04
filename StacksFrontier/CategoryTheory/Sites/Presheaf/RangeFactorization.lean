module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute

/-!
# The image subpresheaf of a map of presheaves of sets

Stacks 00V9. Let `C` be a category and let `φ : F ⟶ G` be a map of presheaves of sets on `C`.
There is a *unique* subpresheaf `G' ⊆ G` through which `φ` factors as `F ⟶ G' ⟶ G` with the
first map surjective, namely the pointwise image `U ↦ φ_U (F(U))`.

Subpresheaves of `G` are `CategoryTheory.Subfunctor G` (Stacks 00V8), the inclusion
`G' ⟶ G` is `CategoryTheory.Subfunctor.ι`, and the pointwise image is
`CategoryTheory.Subfunctor.range φ` (Stacks 00VA). Surjectivity here is the objectwise notion
of Stacks 00V6 (2) — surjective on sections over every object — not local surjectivity for a
topology; no topology occurs in this tag.

## Main results

* `CategoryTheory.Presheaf.eq_range_of_surjective_factorization`: a subpresheaf of `G` through
  which `φ` factors with surjective first map is the pointwise image of `φ`.
* `CategoryTheory.Presheaf.existsUnique_subfunctor_surjective_factorization`: Stacks 00V9, both
  halves at once, as a `∃!` over subpresheaves of `G`.

## Implementation notes

Existence is Mathlib's: `Subfunctor.toRange φ : F ⟶ (Subfunctor.range φ).toFunctor` together
with `Subfunctor.toRange_ι` is the factorization, and its first map is surjective because
`Subfunctor.toRange φ` is an epimorphism. Uniqueness has no named Mathlib lemma; it is the
computation `range φ = range (ψ ≫ G'.ι) = (range ψ).image G'.ι = (⊤).image G'.ι = range G'.ι
= G'`, whose first step uses surjectivity of `ψ` only through `range ψ = ⊤`.

## References

Stacks Project, tag 00V9 (`sites-lemma-image-presheaf`), section "Injective and surjective maps
of presheaves"; its vocabulary is tags 00V6, 00V8 and 00VA.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {F G : Cᵒᵖ ⥤ Type w}

/-- A subpresheaf `G' ⊆ G` through which `φ : F ⟶ G` factors, with the first map `ψ : F ⟶ G'`
surjective on sections over every object, is the pointwise image `Subfunctor.range φ` of `φ` —
the uniqueness half of Stacks 00V9. -/
theorem eq_range_of_surjective_factorization {φ : F ⟶ G} {G' : Subfunctor G}
    (ψ : F ⟶ G'.toFunctor) (hψ : ∀ U, Function.Surjective (ψ.app U)) (hfac : ψ ≫ G'.ι = φ) :
    G' = Subfunctor.range φ := by
  have hψ' : Subfunctor.range ψ = ⊤ := by
    ext U x
    simpa using hψ U x
  rw [← hfac, Subfunctor.range_comp, hψ', Subfunctor.image_top, Subfunctor.range_ι]

/-- **Stacks 00V9.** A map of presheaves of sets `φ : F ⟶ G` factors as `F ⟶ G' ⟶ G` with
`G' ⊆ G` a subpresheaf and the first map surjective on sections over every object, and the
subpresheaf `G'` doing this is unique: it is the pointwise image `U ↦ φ_U (F(U))` of `φ`. -/
@[stacks 00V9 "The unique subpresheaf `G' ⊆ G` through which `φ : F ⟶ G` factors with
  objectwise surjective first map, stated as `∃!` over `Subfunctor G`; the witness is the
  pointwise image `Subfunctor.range φ` with `Subfunctor.toRange φ`.", sga "3 VIB 7.3.0"]
theorem existsUnique_subfunctor_surjective_factorization (φ : F ⟶ G) :
    ∃! G' : Subfunctor G, ∃ ψ : F ⟶ G'.toFunctor,
      (∀ U, Function.Surjective (ψ.app U)) ∧ ψ ≫ G'.ι = φ := by
  refine ⟨Subfunctor.range φ, ⟨Subfunctor.toRange φ, fun U y ↦ ?_, Subfunctor.toRange_ι φ⟩,
    fun G' ⟨ψ, hψ, hfac⟩ ↦ eq_range_of_surjective_factorization ψ hψ hfac⟩
  obtain ⟨x, hx⟩ := y.2
  exact ⟨x, Subtype.ext ((Subfunctor.toRange_app_val φ x).trans hx)⟩

end CategoryTheory.Presheaf
