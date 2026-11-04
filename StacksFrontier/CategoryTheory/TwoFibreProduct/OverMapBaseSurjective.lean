module

public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# Changing the target of a 2-fibre product along a functor that is full on the legs' images

`CategoryTheory.TwoFibreProductOver.isEquivalence_mapBase` says that postcomposing both legs of a
2-fibre product `T ×_ℬ 𝒜` over a base `𝒞` with a fully faithful 1-morphism `b : ℬ ⥤ 𝒟` gives an
equivalence `T ×_ℬ 𝒜 ⥤ T ×_𝒟 𝒜`. Its proof uses fullness of `b` only on the morphisms between
objects in the images of the two legs. This file records the sharper statement: `b` faithful,
and surjective on morphisms from the image of one leg to the image of the other, in both
directions.

That is the form needed for the induced 1-morphism `[U/P] ⟶ [U/R]` of an open subgroupoid: it is
not full, but it is surjective on the morphisms between the objects presented by points lying
over a point `u` of `U` when `P` contains every arrow of `R` with source and target `u`
(Stacks 0DU5).

## Main results

* `CategoryTheory.TwoFibreProductOver.isEquivalence_mapBase_of_surjective`: the comparison is an
  equivalence when `b` is faithful and surjective on the morphisms between the images of the
  legs.
* `CategoryTheory.Functor.map_surjective_of_iso`: surjectivity of a functor on the morphisms
  between two objects is invariant under replacing them by isomorphic objects.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0DU5](https://stacks.math.columbia.edu/tag/0DU5)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

/-- **Surjectivity on morphisms is invariant under isomorphisms of the endpoints.** If `M` is
surjective on the morphisms `X ⟶ Y`, then it is surjective on the morphisms `X' ⟶ Y'` for
`X ≅ X'` and `Y ≅ Y'`. -/
theorem map_surjective_of_iso {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    (M : A ⥤ B) {X Y X' Y' : A} (eX : X ≅ X') (eY : Y ≅ Y')
    (h : Function.Surjective (M.map : (X ⟶ Y) → (M.obj X ⟶ M.obj Y))) :
    Function.Surjective (M.map : (X' ⟶ Y') → (M.obj X' ⟶ M.obj Y')) := by
  intro g
  obtain ⟨f, hf⟩ := h (M.map eX.hom ≫ g ≫ M.map eY.inv)
  refine ⟨eX.inv ≫ f ≫ eY.hom, ?_⟩
  simp [hf, ← M.map_comp_assoc]

end CategoryTheory.Functor

namespace CategoryTheory.TwoFibreProductOver

universe vC vT vA vB vD uC uT uA uB uD

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {T : Type uT} [Category.{vT} T]
  {𝒜 : Type uA} [Category.{vA} 𝒜] {ℬ : Type uB} [Category.{vB} ℬ]
  {𝒟 : Type uD} [Category.{vD} 𝒟]
  {pT : T ⥤ 𝒞} {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}

/-- **Changing the target of a 2-fibre product over `𝒞` along a 1-morphism `b` which is faithful
and surjective on the morphisms between the images of the two legs is an equivalence.**

The objects of the target 2-fibre product carry a comparison isomorphism between objects of the
images of `G ⋙ b` and `F ⋙ b`, and its morphisms are pairs of morphisms of `T` and `𝒜` subject to
an equation in `𝒟` between morphisms of those images. Surjectivity of `b` there produces a
preimage of each comparison isomorphism and of its inverse, faithfulness makes the two preimages
mutually inverse and makes the equation of morphisms reflect, and the preimage of a vertical
morphism is vertical because `b` is over `𝒞`. This is the proof of
`CategoryTheory.TwoFibreProductOver.isEquivalence_mapBase`, which uses no more of `b`. -/
theorem isEquivalence_mapBase_of_surjective {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {b : ℬ ⥤ 𝒟}
    (hb : b ⋙ p𝒟 = pℬ) [b.Faithful]
    (hGF : ∀ x y, Function.Surjective (b.map : (G.obj x ⟶ F.obj y) → _))
    (hFG : ∀ x y, Function.Surjective (b.map : (F.obj y ⟶ G.obj x) → _)) :
    (mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb).IsEquivalence := by
  let K := mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb
  have hfaith : K.Faithful := ⟨fun h => TwoFibreProductOver.Hom.ext'
    (by simpa only [K, mapBase] using congrArg TwoFibreProductOver.Hom.a h)
    (by simpa only [K, mapBase] using congrArg TwoFibreProductOver.Hom.b h)⟩
  have hfull : K.Full := by
    constructor
    intro P Q f
    refine ⟨⟨f.hbase, f.a, f.b, f.ha, f.hb, ?_⟩, ?_⟩
    · apply b.map_injective
      simpa only [K, mapBase, Functor.comp_map, Functor.mapIso_hom, Functor.map_comp] using f.w
    · apply TwoFibreProductOver.Hom.ext' <;> rfl
  have hess : K.EssSurj := by
    constructor
    intro Q
    obtain ⟨ih, hih⟩ := hGF Q.x Q.y Q.iso.hom
    obtain ⟨ii, hii⟩ := hFG Q.x Q.y Q.iso.inv
    let i : G.obj Q.x ≅ F.obj Q.y :=
      { hom := ih
        inv := ii
        hom_inv_id := b.map_injective (by simp [hih, hii])
        inv_hom_id := b.map_injective (by simp [hih, hii]) }
    have hi : b.mapIso i = Q.iso := Iso.ext hih
    have hivert : pℬ.IsHomLift (𝟙 Q.base) i.hom :=
      (Functor.isHomLift_map_iff_of_comp_eq pℬ p𝒟 b hb (𝟙 Q.base) i.hom).1 (by
        rw [show b.map i.hom = Q.iso.hom from hih]
        exact Q.vertical)
    let P : TwoFibreProductOver pT p𝒜 pℬ G F :=
      { base := Q.base, x := Q.x, y := Q.y, hx := Q.hx, hy := Q.hy, iso := i, vertical := hivert }
    have hobj : K.obj P = Q := by
      apply TwoFibreProductOver.obj_ext
      simpa [P, K, mapBase] using hi
    exact ⟨P, ⟨eqToIso hobj⟩⟩
  exact Functor.IsEquivalence.mk

end CategoryTheory.TwoFibreProductOver

end
