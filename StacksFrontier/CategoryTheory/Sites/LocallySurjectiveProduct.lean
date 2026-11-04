module

public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange

/-!
# Local surjectivity is closed under binary products

A product of two locally surjective maps of presheaves of types is locally surjective: if
`f : F₁ ⟶ G₁` and `g : F₂ ⟶ G₂` are locally surjective then so is
`CategoryTheory.Limits.prod.map f g : F₁ ⨯ F₂ ⟶ G₁ ⨯ G₂`.

This is the closure property one needs to lift a *pair* of sections along a locally surjective
map: the lift of either one exists only on a cover, so a pair of them exists only on a common
refinement of two covers, and that is exactly what local surjectivity of the product map
packages.

## Main results

* `CategoryTheory.Presheaf.isLocallySurjective_prodMap`: **local surjectivity is closed under
  binary products.**

## Implementation notes

The proof is a factorization into two base changes rather than a computation with sections of a
product presheaf.  Writing `prod.map f g = prod.map f (𝟙 F₂) ≫ prod.map (𝟙 G₁) g`
(`CategoryTheory.Limits.prod.map_map`), each factor is the base change of one of `f`, `g` along a
projection: the squares

```
F₁ ⨯ X --prod.fst--> F₁          X ⨯ F₂ --prod.snd--> F₂
   |                  |             |                  |
   |                  f             |                  g
   v                  v             v                  v
G₁ ⨯ X --prod.fst--> G₁          X ⨯ G₂ --prod.snd--> G₂
```

are pullback squares, the left one by Mathlib's
`CategoryTheory.IsPullback.of_prod_fst_with_id` and the right one by its mirror image, which is
`CategoryTheory.IsPullback.of_prod_snd_with_id` of
`StacksFrontier/AlgebraicGeometry/Spaces/Representable/Bootstrap/Stability.lean`; that module sits
far above this one, so the square is checked inline in the proof rather than imported.  Local
surjectivity of a base change
is `CategoryTheory.Presheaf.isLocallySurjective_of_isPullback` of
`StacksFrontier/CategoryTheory/Sites/LocallySurjectiveBaseChange.lean`, and local surjectivity of a
composite is Mathlib's `CategoryTheory.Presheaf.isLocallySurjective_comp`.

The two routes that do not work are worth recording.  Mathlib's
`CategoryTheory.Limits.prod.map_epi` concludes that `prod.map` of two epimorphisms is an
epimorphism, but it lives in `Mathlib/CategoryTheory/Limits/Shapes/BinaryBiproducts.lean` and
asks for binary *biproducts*, which a category of presheaves of types does not have.  And
`CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget` does not reduce the statement
for a concrete category to this one, because whiskering with the forgetful functor only commutes
with `prod.map` up to the product comparison maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **Local surjectivity of presheaves of types is closed under binary products.**  If
`f : F₁ ⟶ G₁` and `g : F₂ ⟶ G₂` are locally surjective, then so is
`CategoryTheory.Limits.prod.map f g : F₁ ⨯ F₂ ⟶ G₁ ⨯ G₂`.

In sections: a pair of sections of `G₁` and `G₂` over an object of the site is, after restriction
along a covering family, a pair of images of sections of `F₁` and `F₂`. -/
instance isLocallySurjective_prodMap {F₁ G₁ F₂ G₂ : Cᵒᵖ ⥤ Type w} (f : F₁ ⟶ G₁) (g : F₂ ⟶ G₂)
    [IsLocallySurjective J f] [IsLocallySurjective J g] :
    IsLocallySurjective J (prod.map f g) := by
  have h₁ : IsLocallySurjective J (prod.map f (𝟙 F₂)) :=
    isLocallySurjective_of_isPullback J (IsPullback.of_prod_fst_with_id f F₂).flip
  have hsq : IsPullback (prod.snd : G₁ ⨯ F₂ ⟶ F₂) (prod.map (𝟙 G₁) g) g
      (prod.snd : G₁ ⨯ G₂ ⟶ G₂) := by
    refine IsPullback.mk' (by simp)
      (fun _ _ _ h₁ h₂ => prod.hom_ext
        (by simpa [Category.assoc] using congrArg (· ≫ prod.fst) h₂) h₁)
      (fun _ a b h => ⟨prod.lift (b ≫ prod.fst) a, by simp, ?_⟩)
    exact prod.hom_ext (by simp) (by simpa using h)
  have h₂ : IsLocallySurjective J (prod.map (𝟙 G₁) g) :=
    isLocallySurjective_of_isPullback J hsq.flip
  have hfac : prod.map f (𝟙 F₂) ≫ prod.map (𝟙 G₁) g = prod.map f g := by
    rw [prod.map_map, Category.comp_id, Category.id_comp]
  exact hfac ▸ isLocallySurjective_comp J _ _

end CategoryTheory.Presheaf

end
