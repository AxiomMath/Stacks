module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf

/-!
# Functoriality of the quotient sheaf of a pre-relation

A morphism of pre-relations — a pair `(r, f)` of morphisms of arrow and base objects
commuting with both structure maps — induces a map `U/R → U'/R'` of quotient sheaves,
`Stacks.Groupoids.quotientSheafMap`. This file records that the construction is
*functorial* at the level of the quotient presheaf: it takes a composite pair to the
composite map and the identity pair to the identity map.

The consequence drawn here is the one that the quotient-sheaf arguments actually use:
if both components of a morphism of pre-relations are isomorphisms, then the induced map
of quotient sheaves is an isomorphism. The inverse is the map induced by the inverse
pair, so the isomorphism produced is the *canonical* one and not merely some
isomorphism — which is what lets a statement about `U/R` be transported along a
re-presentation of the relation by a different pair of objects.

## Main results

* `Stacks.Groupoids.quotientPresheafMap_comp` and `Stacks.Groupoids.quotientPresheafMap_id`:
  functoriality at the level of the quotient *presheaf*. The same statements for the
  quotient sheaf are `Stacks.Groupoids.quotientSheafMap_comp` and
  `Stacks.Groupoids.quotientSheafMap_id` of
  `StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf`.
* `Stacks.Groupoids.isIso_quotientSheafMap`: a morphism of pre-relations whose two
  components are isomorphisms induces an isomorphism of quotient sheaves;
  `Stacks.Groupoids.quotientSheafMapIso` of
  `StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf` packages an `Iso` from an explicitly
  given inverse pair.

## Implementation notes

Both functoriality statements are proved at the presheaf level, where the quotient is a
coequalizer, rather than by a `congr` on the sheafified maps; the sheaf-level statements
are obtained from them by `CategoryTheory.Functor.map_comp` and
`CategoryTheory.Functor.map_id`. The presheaf-level statements are the mathematical
content and are independently useful; sheafification contributes nothing but its being a
functor.

At the presheaf level the quotient is a coequalizer, so two maps out of it agree as soon
as they agree after the coequalizer projection, which is
`CategoryTheory.Limits.coequalizer.hom_ext`.
After that projection every map in sight is `yoneda` applied to a morphism of `Over S`
and whiskered along `F.op`, so both statements reduce to functoriality of `yoneda` and of
whiskering.

The compatibility hypotheses `hs`, `ht` of `Stacks.Groupoids.quotientSheafMap` are
propositions, so the induced map does not depend on which proof is supplied and the
composite pair's hypotheses may be discharged inline.

The universe arrangement is inherited unchanged from
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf`: presheaves of sets are valued in
`Type u`, the universe of morphisms of `S`-schemes, while the site `C : Type v` with
`Category.{w} C` is left at two free universes. In particular nothing here constrains the
site to `C : Type u` with `Category.{u} C`, as
`StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafLocallySurjective` must, since no
sheafification-is-locally-surjective instance is used.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.Groupoids

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- The quotient presheaf construction takes a composite morphism of pre-relations to the
composite of the induced maps. -/
theorem quotientPresheafMap_comp (F : C ⥤ Over S)
    {R₁ U₁ R₂ U₂ R₃ U₃ : Over S}
    (j₁ : PreRelation R₁ U₁) (j₂ : PreRelation R₂ U₂) (j₃ : PreRelation R₃ U₃)
    (r₁ : R₁ ⟶ R₂) (f₁ : U₁ ⟶ U₂) (r₂ : R₂ ⟶ R₃) (f₂ : U₂ ⟶ U₃)
    (hs₁ : r₁ ≫ j₂.source = j₁.source ≫ f₁)
    (ht₁ : r₁ ≫ j₂.target = j₁.target ≫ f₁)
    (hs₂ : r₂ ≫ j₃.source = j₂.source ≫ f₂)
    (ht₂ : r₂ ≫ j₃.target = j₂.target ≫ f₂) :
    quotientPresheafMap F j₁ j₂ r₁ f₁ hs₁ ht₁ ≫
        quotientPresheafMap F j₂ j₃ r₂ f₂ hs₂ ht₂ =
      quotientPresheafMap F j₁ j₃ (r₁ ≫ r₂) (f₁ ≫ f₂)
        (by rw [Category.assoc, hs₂, ← Category.assoc, hs₁, Category.assoc])
        (by rw [Category.assoc, ht₂, ← Category.assoc, ht₁, Category.assoc]) := by
  apply coequalizer.hom_ext
  simp [quotientPresheafMap, toQuotientPresheaf, Functor.whiskerLeft_comp,
    Functor.map_comp, Category.assoc]

/-- The quotient presheaf construction takes the identity morphism of pre-relations to the
identity map. -/
theorem quotientPresheafMap_id (F : C ⥤ Over S) {R U : Over S} (j : PreRelation R U)
    (hs : 𝟙 R ≫ j.source = j.source ≫ 𝟙 U)
    (ht : 𝟙 R ≫ j.target = j.target ≫ 𝟙 U) :
    quotientPresheafMap F j j (𝟙 R) (𝟙 U) hs ht = 𝟙 _ := by
  apply coequalizer.hom_ext
  simp only [quotientPresheafMap, toQuotientPresheaf, CategoryTheory.Functor.map_id,
    coequalizer.π_desc]
  exact (Category.comp_id _).symm

/-- A morphism of pre-relations whose two components are isomorphisms induces an
isomorphism of quotient sheaves. The inverse is the map induced by the inverse pair, so
the isomorphism is the canonical one. -/
theorem isIso_quotientSheafMap (J : GrothendieckTopology C) [HasSheafify J (Type u)]
    (F : C ⥤ Over S) {R U R' U' : Over S}
    (j : PreRelation R U) (j' : PreRelation R' U')
    (r : R ⟶ R') (f : U ⟶ U') [IsIso r] [IsIso f]
    (hs : r ≫ j'.source = j.source ≫ f)
    (ht : r ≫ j'.target = j.target ≫ f) :
    IsIso (quotientSheafMap J F j j' r f hs ht) := by
  have hs' : inv r ≫ j.source = j'.source ≫ inv f := by
    rw [IsIso.eq_comp_inv, Category.assoc, ← hs, IsIso.inv_hom_id_assoc]
  have ht' : inv r ≫ j.target = j'.target ≫ inv f := by
    rw [IsIso.eq_comp_inv, Category.assoc, ← ht, IsIso.inv_hom_id_assoc]
  refine ⟨⟨quotientSheafMap J F j' j (inv r) (inv f) hs' ht', ?_, ?_⟩⟩
  · rw [quotientSheafMap_comp J F j j' j r f hs ht (inv r) (inv f) hs' ht']
    simp only [IsIso.hom_inv_id]
    exact quotientSheafMap_id J F j
  · rw [quotientSheafMap_comp J F j' j j' (inv r) (inv f) hs' ht' r f hs ht]
    simp only [IsIso.inv_hom_id]
    exact quotientSheafMap_id J F j'

end Stacks.Groupoids

end
