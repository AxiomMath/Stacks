module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

/-!
# Isomorphisms of categories over a base

Let `𝒞` be a category. An *isomorphism over `𝒞`* between two categories over `𝒞` is an
isomorphism in the 2-category of categories over `𝒞` (Stacks 003Y), that is a pair of functors
over `𝒞` which are mutually inverse *on the nose* — not merely up to natural isomorphism. This is
the relation used to define split fibred categories (Stacks 02XW) and split categories fibred in
groupoids (Stacks 04TL), where the source is explicit that isomorphism rather than equivalence is
meant.

## Main definitions

* `CategoryTheory.BasedCategory.IsoOver`

## Main results

* `CategoryTheory.BasedCategory.isoOver_iff_nonempty_iso`: for two categories over `𝒞` whose
  underlying categories live in the same universes, being isomorphic over `𝒞` is the same as
  being isomorphic as objects of Mathlib's category `BasedCategory 𝒞`.

## Implementation notes

`BasedCategory 𝒞` is a category, so `𝒳 ≅ 𝒴` already expresses isomorphism over `𝒞` — but only
for `𝒳` and `𝒴` whose underlying categories live in the same universes. The constructions this
relation is applied to, such as the Grothendieck construction of a presheaf of categories, land
in a universe determined by both `𝒞` and the presheaf, so a formulation allowing the two sides to
live in different universes is needed. `BasedFunctor` itself is already universe-heterogeneous,
which is what makes this possible; `isoOver_iff_nonempty_iso` checks the two agree whenever both
make sense.
-/

@[expose] public section

namespace CategoryTheory.BasedCategory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- Two categories over `𝒞` are *isomorphic over `𝒞`* if there is a functor over `𝒞` from the one
to the other admitting a strict inverse which is again a functor over `𝒞`. -/
def IsoOver (𝒳 : BasedCategory.{v₂, u₂} 𝒞) (𝒴 : BasedCategory.{v₃, u₃} 𝒞) : Prop :=
  ∃ (G : 𝒳 ⥤ᵇ 𝒴) (H : 𝒴 ⥤ᵇ 𝒳),
    G.toFunctor ⋙ H.toFunctor = 𝟭 𝒳.obj ∧ H.toFunctor ⋙ G.toFunctor = 𝟭 𝒴.obj

namespace IsoOver

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}

/-- Every category over `𝒞` is isomorphic over `𝒞` to itself, via the identity functor. -/
@[refl]
lemma refl (𝒳 : BasedCategory.{v₂, u₂} 𝒞) : IsoOver 𝒳 𝒳 :=
  ⟨BasedFunctor.id 𝒳, BasedFunctor.id 𝒳, rfl, rfl⟩

/-- Isomorphism over `𝒞` is symmetric: exchange the functor with its strict inverse. -/
lemma symm (h : IsoOver 𝒳 𝒴) : IsoOver 𝒴 𝒳 :=
  let ⟨G, H, h₁, h₂⟩ := h; ⟨H, G, h₂, h₁⟩

end IsoOver

/-- Two categories over `𝒞` isomorphic over `𝒞` have the same structure functor up to the
isomorphism: this is the condition `p' ∘ G = p` on the 1-morphisms of the 2-category of categories
over `𝒞`. -/
lemma IsoOver.comp_p {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
    (h : IsoOver 𝒳 𝒴) : ∃ G : 𝒳.obj ⥤ 𝒴.obj, G ⋙ 𝒴.p = 𝒳.p := by
  obtain ⟨G, -, -, -⟩ := h
  exact ⟨G.toFunctor, G.w⟩

/-- A functor over `𝒞` is determined by the underlying functor: the condition `p' ∘ G = p` is a
proposition. -/
lemma BasedFunctor.ext' {𝒳 : BasedCategory.{v₂, u₂} 𝒞} {𝒴 : BasedCategory.{v₃, u₃} 𝒞}
    {G H : 𝒳 ⥤ᵇ 𝒴} (h : G.toFunctor = H.toFunctor) : G = H := by
  obtain ⟨G, hG⟩ := G
  obtain ⟨H, hH⟩ := H
  subst h
  rfl

/-- For two categories over `𝒞` whose underlying categories live in the same universes, being
isomorphic over `𝒞` is being isomorphic in Mathlib's category `BasedCategory 𝒞`, whose morphisms
are the functors over `𝒞`. -/
lemma isoOver_iff_nonempty_iso (𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒞) :
    IsoOver 𝒳 𝒴 ↔ Nonempty (𝒳 ≅ 𝒴) :=
  ⟨fun ⟨G, H, h₁, h₂⟩ => ⟨⟨G, H, BasedFunctor.ext' h₁, BasedFunctor.ext' h₂⟩⟩,
    fun ⟨e⟩ => ⟨e.hom, e.inv, congrArg BasedFunctor.toFunctor e.hom_inv_id,
      congrArg BasedFunctor.toFunctor e.inv_hom_id⟩⟩

end CategoryTheory.BasedCategory
