module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# The comparison of scheme charts under a change of base

Let `j = Over.map f` for a morphism `f : V ⟶ U` of a category `C`, and let `Λ` be the presheaf
level lower-shriek extension `CategoryTheory.OverShriek.relocalizePresheafFunctor f`.  A scheme
chart `φ : h_W ⟶ F` of a presheaf `F` on `C/V` is carried to a chart `h_{j W} ⟶ Λ F` of `Λ F`,
and this file constructs that comparison and proves it faithful:
`CategoryTheory.OverShriek.relocalizeChartFunctor`.

**What this is for, and what is still missing.**  For `C` the big fppf site of a scheme and
`f` a morphism of it, viewing an algebraic space `F` over `S` as one over `S'` through the forward
functor of [Stacks Project, Tag 04SG] replaces `F` by `Λ_g F`, and the small étale site is the
full subcategory of the scheme charts cut out by the étale condition
(`AlgebraicGeometry.Space.SmallEtale`).  So an equivalence of small étale sites across a change
of base would follow from this comparison being an **equivalence**, together with
[Stacks Project, Tag 03I6] (`AlgebraicGeometry.presheaf_property_map_base_iff`) identifying the
two étale chart conditions, by `CategoryTheory.Equivalence.congrFullSubcategory`.

That equivalence is **not** proved here.  What is missing is precisely fullness and essential
surjectivity of `relocalizeChartFunctor`; the comparison is faithful below, and the two
ingredients both halves need are here — the inverse of
`CategoryTheory.OverShriek.relocalizeYonedaIso` as a formula on sections
(`relocalizeYonedaIso_inv_app_app_apply`) and the faithfulness of `Λ` on morphisms of presheaves
(`relocalizePresheafFunctor_map_injective`).

What blocks both is now a single narrow step, and it is mechanical rather than mathematical.
Each half must read the chart condition `CostructuredArrow.w` at one section, which means
evaluating a composite of three maps of presheaves at the identity.  The resulting term has the
shape `ConcreteCategory.hom (a ≫ b ≫ c) x`, and `simp` does not break that into the iterated
application `c (b (a x))`, so `relocalizeYonedaIso_inv_app_app_apply` — stated, as it must be,
about an applied inverse — never gets the chance to fire.  Unfolding instead of rewriting is not
open either: `relocalizeYonedaIso`'s `inv` is not `@[expose]`, so the elaborator reports it as
"not unfolded because their definition is not exposed".  What is needed is the composite
application lemma for the concrete category `Type v` in the spelling these terms actually carry.

Why it matters that this is an equivalence of *small étale sites* and not merely of categories of
algebraic spaces: neither
`StacksFrontier/AlgebraicGeometry/Spaces/SmallerBaseEquivalence.lean` nor
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleChartSmallerBase.lean` mentions the small étale site
at all — the former is an equivalence of categories of algebraic spaces onto a slice
(`AlgebraicGeometry.SpacesOverSmallerBase`) and the latter carries the étale chart condition
across a change of base.  The small étale comparison is what the deduction of
[Stacks Project, Tag 04KL] *over a base* from its absolute form over the terminal scheme needs,
and it is the one input that deduction lacks.

## Main definitions

* `CategoryTheory.OverShriek.relocalizeChartFunctor`: the comparison of scheme charts — a chart
  `h_W ⟶ F` of `F` is carried to the chart `h_{j W} ⟶ Λ F` of `Λ F`.

## Main results

* `CategoryTheory.OverShriek.relocalizeYonedaIso_inv_app_app_apply`: the inverse of
  `Λ h_Z ≅ h_{j Z}` on sections, explicitly.
* `CategoryTheory.OverShriek.relocalizeChartFunctor_faithful`: the comparison is faithful.

## Implementation notes

`Λ` carries a representable presheaf to a representable presheaf, `Λ h_W ≅ h_{j W}`, naturally in
`W`; that is `CategoryTheory.OverShriek.relocalizeYonedaIso` of
`StacksFrontier/CategoryTheory/Sites/Localization/RelocalizeRepresentable.lean`, the general site
form of [Stacks Project, Tag 03I4] part (2).  The comparison of charts is that comparison
composed with `Λ` of the chart, and the three properties making it an equivalence are proved from
`Λ`'s action on morphisms of representables being faithful and full with the same underlying
morphism of the ambient category.

The comparison is written with `(relocalizeYonedaIso f).inv.app W.left` rather than
`((relocalizeYonedaIso f).app W.left).inv`, and the chart condition of a morphism is proved from
the naturality of the *inverse* of that comparison rather than by cancelling it against its hom.
Both choices are forced by what the goal is syntactically: `Iso.hom_inv_id_assoc` cannot fire on
a goal in which one factor has been reduced to `inv.app W.left` and the other still reads
`(app W.left).hom`, since the two spellings leave its `?self` unable to unify.  Cancellation is
not needed anyway — the inverse's naturality turns the chart condition directly into
`CostructuredArrow.w`.

Since `(IsEtaleChart B S hS F).FullSubcategory` is how the small étale site is defined, the last
step is `CategoryTheory.Equivalence.congrFullSubcategory` applied to the chart equivalence, whose
hypothesis is exactly that the two chart conditions agree.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03I6](https://stacks.math.columbia.edu/tag/03I6)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.OverShriek

variable {C : Type w} [Category.{v} C] {U V : C} (f : V ⟶ U)

/-! ### The comparison of scheme charts -/

/-- **The inverse of `Λ h_Z ≅ h_{j Z}`, explicitly.**  A morphism `p : W ⟶ j Z` of `C/U` is sent
to the section `(p.left ≫ Z.hom, p.left)` of `Λ h_Z` over `W`.

`CategoryTheory.OverShriek.relocalizeYonedaHom` is given by a formula, but the inverse of
`CategoryTheory.OverShriek.relocalizeYonedaIso` is produced from
`CategoryTheory.OverShriek.bijective_relocalizeYonedaHom_app_app`, bijectivity on sections, and
so is not definitionally a formula.  This recovers the formula, by applying the injectivity of
the comparison itself to both sides. -/
theorem relocalizeYonedaIso_inv_app_app_apply (Z : Over V) (W : (Over U)ᵒᵖ)
    (p : W.unop ⟶ (Over.map f).obj Z) :
    ((relocalizeYonedaIso f).inv.app Z).app W p =
      ⟨⟨p.left ≫ Z.hom, Over.homMk p.left rfl⟩,
        (Category.assoc p.left Z.hom f).trans (Over.w p)⟩ :=
  (bijective_relocalizeYonedaHom_app_app f Z W).injective <|
    (Iso.inv_hom_id_apply (((relocalizeYonedaIso f).app Z).app W) p).trans
      (Over.OverMorphism.ext rfl).symm

variable (F : (Over V)ᵒᵖ ⥤ Type v)

/-- **The comparison of scheme charts under relocalization.**  A chart `φ : h_W ⟶ F` of a
presheaf `F` on `C/V` is carried to the chart `h_{j W} ⟶ Λ F` of `Λ F` obtained from `Λ φ` by
reading `Λ h_W` as `h_{j W}`. -/
noncomputable def relocalizeChartFunctor :
    CostructuredArrow yoneda F ⥤
      CostructuredArrow yoneda ((relocalizePresheafFunctor f).obj F) where
  obj W := CostructuredArrow.mk
    ((relocalizeYonedaIso f).inv.app W.left ≫ (relocalizePresheafFunctor f).map W.hom)
  map {W W'} h := CostructuredArrow.homMk ((Over.map f).map h.left) (by
    have hnat : yoneda.map ((Over.map f).map h.left) ≫
          (relocalizeYonedaIso f).inv.app W'.left =
        (relocalizeYonedaIso f).inv.app W.left ≫
          (relocalizePresheafFunctor f).map (yoneda.map h.left) :=
      (relocalizeYonedaIso f).inv.naturality h.left
    have hw : yoneda.map h.left ≫ W'.hom = W.hom := CostructuredArrow.w h
    dsimp
    rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp, hw])

/-- **The comparison of scheme charts is faithful.**  A morphism of charts is determined by its
underlying morphism of the ambient category, and `j = Over.map f` does not change that. -/
instance relocalizeChartFunctor_faithful : (relocalizeChartFunctor f F).Faithful where
  map_injective h :=
    CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (congrArg (fun k => k.left.left) h))

/-- **`Λ` is faithful on morphisms of presheaves.**  A section of `Λ G` over `j Z` is a pair whose
second component is a section of `G` over `Z`, so a map out of `G` is recovered from `Λ` of it. -/
theorem relocalizePresheafFunctor_map_injective {G H : (Over V)ᵒᵖ ⥤ Type v} {σ τ : G ⟶ H}
    (h : (relocalizePresheafFunctor f).map σ = (relocalizePresheafFunctor f).map τ) : σ = τ := by
  ext Z x
  exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val (congrArg
    (fun k => k.app (Opposite.op ((Over.map f).obj Z.unop)) ⟨⟨Z.unop.hom, x⟩, rfl⟩) h))).2

end CategoryTheory.OverShriek

end
