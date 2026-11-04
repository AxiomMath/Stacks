module

public import StacksFrontier.AlgebraicGeometry.Stacks.SubsitePushforwardAmbientComparison
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphisms

/-!
# The comparison of index categories in the square of Stacks 07AT, on sections

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories over a base `𝒞`, with `𝒴` fibred in groupoids, let
`𝒳' ⊆ 𝒳` and `𝒴' ⊆ 𝒴` be full subcategories with `f(𝒳') ⊆ 𝒴'`, and let `f' : 𝒳' ⥤ 𝒴'` be the
restriction. The square
```
  𝒳' --ι--> 𝒳
  |f'       |f
  v         v
  𝒴' --ι--> 𝒴
```
commutes on the nose, and for an object `y` of `𝒴'` it induces the comparison functor of index
categories
`CostructuredArrow f' y ⥤ CostructuredArrow f y`, `(x', f'(x') ⟶ y) ↦ (x', f(x') ⟶ y)`,
of Stacks 0FN1. The base-change map of right Kan extensions of the square at `y`, the map
`f_*ℱ(y) ⟶ f'_*(ℱ|_{𝒳'})(y)` whose invertibility is the identity `g^{-1}f_* = f'_*(g')^{-1}` of
Stacks 07AT, is restriction of compatible families of sections along this functor.

This file proves that this restriction is a bijection under exactly the conditions under which
`CategoryTheory.SubsitePushforward.primedPushforwardAmbientEquiv` identifies the two sides: the
sheaf condition for `pr^{-1}ℱ` on the 2-fibre product `V ×_{y, 𝒴} 𝒳` and the two
local-factorization conditions of Stacks 07AK for the inclusion of the primed 2-fibre product.
That equivalence is an abstract bijection between the two sets; the point here is that the
*comparison map itself* is bijective, which is what passing to sheaves of modules needs (the
module structures, and the naturality in `ℱ`, are carried by the comparison map and not by an
arbitrary bijection).

The proof is a two-out-of-three argument: under the index functors of Stacks 06W6 from the two
2-fibre products, the restriction along the comparison functor and the restriction along the
inclusion of the primed 2-fibre product agree on the nose, and every other map in the square is
a bijection.

## Main definitions

* `CategoryTheory.SubsitePushforward.indexComparison`: the comparison functor
  `CostructuredArrow f' y ⥤ CostructuredArrow f y`.

## Main results

* `CategoryTheory.SubsitePushforward.bijective_sectionsPrecomp_indexComparison`: restriction of
  compatible families along the comparison functor is bijective.
* `CategoryTheory.SubsitePushforward.bijective_sectionsPrecomp_structuredArrowDownwards`: the
  same for the comparison functor in the shape in which the base-change transformation of right
  Kan extensions reads it, Mathlib's `CategoryTheory.TwoSquare.structuredArrowDownwards` of the
  opposite square.

## References

* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
* [Stacks Project, Tag 0FN1](https://stacks.math.columbia.edu/tag/0FN1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SubsitePushforward

attribute [local implicit_reducible] Functor.Fiber

universe u₁ u₂ u₃ v₁ v₂ v₃ w

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- **The comparison functor of index categories of Stacks 0FN1** for the square formed by the
restriction `f' : 𝒳' ⥤ 𝒴'` of `f` and the two inclusions: an arrow `f'(x') ⟶ y` of `𝒴'` is read
as the arrow `f(x') ⟶ y` of `𝒴`. -/
abbrev indexComparison (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
    (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj)) (y : Q.FullSubcategory) :
    CostructuredArrow (subsiteFunctor f P hPQ) y ⥤ CostructuredArrow f y.obj :=
  costructuredArrowPost f P hPQ y ⋙ CostructuredArrow.pre P.ι f y.obj

/-- **Restriction along the comparison functor of index categories is bijective.** For a
presheaf of sets `ℱ` on `𝒳` and an object `y` of `𝒴'`, restricting a compatible family of
sections of `ℱ` over the index category `CostructuredArrow f y` of `f_*ℱ(y)` to the index
category `CostructuredArrow f' y` of `f'_*(ℱ|_{𝒳'})(y)` is a bijection, provided `pr^{-1}ℱ` is a
sheaf for a topology on the 2-fibre product `V ×_{y, 𝒴} 𝒳` in which every object is covered by
objects admitting a morphism to the primed 2-fibre product and any two such morphisms are
locally connected.

Under the index functors of Stacks 06W6 the restriction along the comparison functor becomes the
restriction from the 2-fibre product to the primed one, which is the degree-zero clause of
Stacks 07AK; the remaining identifications are bijections. -/
theorem bijective_sectionsPrecomp_indexComparison
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
    (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj))
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳) (c : p𝒴.ChoiceOfPullbacks)
    (y : Q.FullSubcategory) (ℱ : 𝒳ᵒᵖ ⥤ Type w)
    (J : GrothendieckTopology (ambientTwoFibreProduct p𝒳 p𝒴 f c y))
    (hℱ : Presieve.IsSheaf J ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ))
    (hfac : Stacks.Sites.HasLocalFactorizations J (primedProperty p𝒳 p𝒴 f P c y).ι)
    (hconn : Stacks.Sites.HasLocallyConnectedFactorizations J
      (primedProperty p𝒳 p𝒴 f P c y).ι) :
    Function.Bijective (Functor.sectionsPrecomp (indexComparison f P hPQ y).op
      (P := (CostructuredArrow.proj f y.obj).op ⋙ ℱ)) := by
  -- the index functor of Stacks 06W6 for `f`, followed by the comparison of 07AK
  let eE := Presheaf.pushforwardIndexSectionsEquiv p𝒳 p𝒴 f (c.sliceDatum y.obj) h𝒴 hf ℱ
  let eL := Stacks.Sites.sectionsEquivOfHasLocallyConnectedFactorizations J hℱ hfac hconn
  -- the comparison of index categories of `f'` and `ι ⋙ f`, the index functor of Stacks 06W6
  -- for `ι ⋙ f`, and the comparison of the two descriptions of the primed 2-fibre product
  let eI := indexSectionsEquiv f P hPQ y (P.ι.op ⋙ ℱ)
  let eS := Presheaf.pushforwardIndexSectionsEquiv (P.ι ⋙ p𝒳) p𝒴 (P.ι ⋙ f)
    (c.sliceDatum y.obj) h𝒴 (ι_comp_comp_structure_eq p𝒳 p𝒴 f P hf) (P.ι.op ⋙ ℱ)
  let eP := primedSectionsEquiv p𝒳 p𝒴 f P c y (P.ι.op ⋙ ℱ)
  let e₁ := eE.trans eL
  let e₂ := eI.trans (eS.trans eP)
  -- the two routes around the square agree on the nose
  have h : Functor.sectionsPrecomp (indexComparison f P hPQ y).op
      (P := (CostructuredArrow.proj f y.obj).op ⋙ ℱ) = e₂.symm ∘ e₁ :=
    funext fun _ ↦ e₂.eq_symm_apply.2 (Subtype.ext (funext fun _ => rfl))
  rw [h]
  exact e₂.symm.bijective.comp e₁.bijective

/-- **Restriction along the comparison functor of index categories is bijective, in the shape of
the base-change transformation of right Kan extensions.** The index categories of the right Kan
extensions along `f.op` and `f'.op` are `StructuredArrow (op y) f.op` and
`StructuredArrow (op y) f'.op`, and the comparison functor between them that the base-change
transformation of the square is computed with
(`Stacks.SheafOfModules.ranBaseChange_π`) is `TwoSquare.structuredArrowDownwards` of the opposite
of the square. Under the equivalences `CategoryTheory.costructuredArrowOpEquivalence` it is the
opposite of `CategoryTheory.SubsitePushforward.indexComparison`, up to an isomorphism lying over
identities, so `CategoryTheory.SubsitePushforward.bijective_sectionsPrecomp_indexComparison`
applies. -/
theorem bijective_sectionsPrecomp_structuredArrowDownwards
    (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) (P : ObjectProperty 𝒳) {Q : ObjectProperty 𝒴}
    (hPQ : ∀ x : P.FullSubcategory, Q (f.obj x.obj))
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hf : f ⋙ p𝒴 = p𝒳) (c : p𝒴.ChoiceOfPullbacks)
    (y : Q.FullSubcategory) (ℱ : 𝒳ᵒᵖ ⥤ Type w)
    (J : GrothendieckTopology (ambientTwoFibreProduct p𝒳 p𝒴 f c y))
    (hℱ : Presieve.IsSheaf J ((ambientProjection p𝒳 p𝒴 f c y).op ⋙ ℱ))
    (hfac : Stacks.Sites.HasLocalFactorizations J (primedProperty p𝒳 p𝒴 f P c y).ι)
    (hconn : Stacks.Sites.HasLocallyConnectedFactorizations J
      (primedProperty p𝒳 p𝒴 f P c y).ι) :
    Function.Bijective (Functor.sectionsPrecomp
      ((Stacks.Sites.CocontinuousExchange.twoSquare
        (subsiteFunctor_comp_ι f P hPQ)).op.structuredArrowDownwards (op y))
      (P := StructuredArrow.proj (op y.obj) f.op ⋙ ℱ)) := by
  let Kf := (costructuredArrowOpEquivalence f y.obj).functor
  let Ku := (costructuredArrowOpEquivalence (subsiteFunctor f P hPQ) y).functor
  have hKf : Function.Bijective (Functor.sectionsPrecomp Kf
      (P := StructuredArrow.proj (op y.obj) f.op ⋙ ℱ)) :=
    Functor.bijective_sectionsPrecomp _ _
  have hKu := Functor.bijective_sectionsPrecomp Ku
    ((Stacks.Sites.CocontinuousExchange.twoSquare
        (subsiteFunctor_comp_ι f P hPQ)).op.structuredArrowDownwards (op y) ⋙
      StructuredArrow.proj (op y.obj) f.op ⋙ ℱ)
  -- the two routes agree, the two comparison functors differing by isomorphisms over identities
  have key : ∀ s : (StructuredArrow.proj (op y.obj) f.op ⋙ ℱ).sections,
      ((Functor.sectionsPrecomp Ku (Functor.sectionsPrecomp
        ((Stacks.Sites.CocontinuousExchange.twoSquare
          (subsiteFunctor_comp_ι f P hPQ)).op.structuredArrowDownwards (op y)) s)).val :
          ∀ _, _) =
        (Functor.sectionsPrecomp (indexComparison f P hPQ y).op
          (Functor.sectionsPrecomp Kf s)).val := by
    intro s
    funext z
    let φ : Kf.obj ((indexComparison f P hPQ y).op.obj z) ⟶
        ((Stacks.Sites.CocontinuousExchange.twoSquare
          (subsiteFunctor_comp_ι f P hPQ)).op.structuredArrowDownwards (op y)).obj (Ku.obj z) :=
      StructuredArrow.homMk (𝟙 _) (by
        dsimp [Kf, Ku, costructuredArrowOpEquivalence, TwoSquare.structuredArrowDownwards,
          CostructuredArrow.toStructuredArrow]
        simp only [StructuredArrow.post, Functor.op_obj, ObjectProperty.ι_obj, Functor.op_map,
          ObjectProperty.ι_map, StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self,
          Quiver.Hom.unop_op, costructuredArrowPost, CostructuredArrow.post,
          CostructuredArrow.mk_left, CostructuredArrow.mk_hom_eq_self, unop_id, Functor.map_id,
          op_id, Category.comp_id, eqToHom_app, Functor.comp_obj, eqToHom_op]
        exact (Category.comp_id _).symm)
    exact ((FunctorToTypes.map_id_apply ℱ _).symm.trans (s.property φ)).symm
  have hsq : Functor.sectionsPrecomp Ku ∘ Functor.sectionsPrecomp
      ((Stacks.Sites.CocontinuousExchange.twoSquare
        (subsiteFunctor_comp_ι f P hPQ)).op.structuredArrowDownwards (op y))
        (P := StructuredArrow.proj (op y.obj) f.op ⋙ ℱ) =
      Functor.sectionsPrecomp (indexComparison f P hPQ y).op ∘ Functor.sectionsPrecomp Kf :=
    funext fun s ↦ Subtype.ext (key s)
  refine (Function.Bijective.of_comp_iff' hKu _).1 ?_
  rw [hsq]
  exact (bijective_sectionsPrecomp_indexComparison p𝒳 p𝒴 f P hPQ h𝒴 hf c y ℱ J hℱ hfac
    hconn).comp hKf

end CategoryTheory.SubsitePushforward

end
