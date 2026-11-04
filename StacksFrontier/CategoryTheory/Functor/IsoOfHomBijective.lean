module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.Logic.Function.Basic

/-!
# Lifting an isomorphism through a functor bijective on the relevant hom sets

Let `F : C ⥤ D` be a functor and let `G` and `H` be objects of `C` such that `F` is bijective
on each of the four hom sets `G ⟶ H`, `H ⟶ G`, `G ⟶ G` and `H ⟶ H`. Then every isomorphism
`F G ≅ F H` is the image of a unique isomorphism `G ≅ H`.

This is the shape in which full faithfulness is used to turn an isomorphism of images into an
isomorphism of sources when the functor is only known to be bijective on hom sets *at the
objects in question*, so that neither `CategoryTheory.Functor.Full` nor
`CategoryTheory.Functor.Faithful` is available and
`CategoryTheory.Functor.FullyFaithful.preimageIso` does not apply.

## Main results

* `CategoryTheory.Functor.existsUnique_iso_of_map_bijective` — the unique lift.

## Implementation notes

Surjectivity on `G ⟶ H` and on `H ⟶ G` produces the two candidate morphisms; injectivity on
the two endomorphism sets turns the two triangle identities in `D` into the identities in `C`
that make them mutually inverse; injectivity on `G ⟶ H` is uniqueness.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

/-- If `F` is injective on endomorphisms of `X` and `F.map (f ≫ g)` is the identity, so is
`f ≫ g`. -/
private theorem comp_eq_id_of_map_comp_eq_id {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) {X Y : C}
    (h : Function.Injective (fun f : X ⟶ X => F.map f)) (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : F.map f ≫ F.map g = 𝟙 (F.obj X)) : f ≫ g = 𝟙 X :=
  h <| by simpa using hfg

/-- **An isomorphism between the images lifts uniquely** along a functor that is bijective on
the four hom sets between the two objects and their endomorphisms. -/
public theorem existsUnique_iso_of_map_bijective {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (G H : C) (e₀ : F.obj G ≅ F.obj H)
    (hGH : Function.Bijective (fun f : G ⟶ H => F.map f))
    (hHG : Function.Bijective (fun f : H ⟶ G => F.map f))
    (hGG : Function.Bijective (fun f : G ⟶ G => F.map f))
    (hHH : Function.Bijective (fun f : H ⟶ H => F.map f)) :
    ∃! e : G ≅ H, F.map e.hom = e₀.hom := by
  obtain ⟨f, hf⟩ := hGH.2 e₀.hom
  obtain ⟨g, hg⟩ := hHG.2 e₀.inv
  change F.map f = e₀.hom at hf
  change F.map g = e₀.inv at hg
  have hfg : f ≫ g = 𝟙 G := comp_eq_id_of_map_comp_eq_id F hGG.1 f g <| by
    rw [hf, hg, e₀.hom_inv_id]
  have hgf : g ≫ f = 𝟙 H := comp_eq_id_of_map_comp_eq_id F hHH.1 g f <| by
    rw [hg, hf, e₀.inv_hom_id]
  refine ⟨⟨f, g, hfg, hgf⟩, hf, fun e he => Iso.ext (hGH.1 (he.trans hf.symm))⟩

end CategoryTheory.Functor

end
