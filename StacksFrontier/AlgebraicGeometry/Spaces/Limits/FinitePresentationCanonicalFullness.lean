module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationClosedFibreGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationDescentRealised

/-!
# The fullness clause of Stacks 07SK with the canonical comparison isomorphisms

For a factorisation `a ≫ b = c` in a category with pullbacks, base change along `c` and the
iterated base change along `b` then `a` are identified by the canonical comparison isomorphism
`CategoryTheory.Over.pullbackFactorObjIso`. A morphism from the iterated base change
to the base change along the composite which commutes with the projections to the object pulled
back is necessarily the inverse of that comparison.

The fullness clause of Stacks 07SK, in the form for a cone of the big fppf site whose image in
schemes is a limit cone, returns its comparison isomorphisms as unnamed existential witnesses
characterised by exactly that commutation. By the uniqueness statement they are the canonical
comparisons, and the clause can be stated as an equation between composites of named morphisms,
which is the shape of the `full` field of
`AlgebraicGeometry.FinitePresentationSpacesOver.IsFinitePresentationColimit`.

## Main results

* `CategoryTheory.Over.eq_pullbackFactorObjIso_inv_of_fst`: the comparison isomorphism of a
  factorisation is pinned by its composite with the projections.
* `AlgebraicGeometry.Space.exists_morphism_canonical_after_baseChange_of_isLimit`: the fullness
  clause of Stacks 07SK, with no hypothesis on the size of the index category, and with the
  canonical comparison isomorphisms.

## References

* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Over

variable {C : Type*} [Category C] [HasPullbacks C] {X Y T : C} {a : X ⟶ Y} {b : Y ⟶ T}
  {c : X ⟶ T}

/-- **The comparison isomorphism of a factorisation is pinned by its composite with the
projections to the object pulled back.** Any morphism from the iterated base change along a
factorisation `c = a ≫ b` to the base change along `c` whose composite with the projection is
the iterated projection is the inverse of
`CategoryTheory.Over.pullbackFactorObjIso`.

This is what makes the comparison isomorphisms produced by the fullness clause of Stacks 07SK
usable: that clause returns them as unnamed existential witnesses characterised exactly by this
identity, and this lemma turns them into the canonical comparison. -/
theorem eq_pullbackFactorObjIso_inv_of_fst (h : a ≫ b = c) (A : Over T)
    (m : (Over.pullback b ⋙ Over.pullback a).obj A ⟶ (Over.pullback c).obj A)
    (hm : m.left ≫ pullback.fst A.hom c =
      pullback.fst (pullback.snd A.hom b) a ≫ pullback.fst A.hom b) :
    m = (pullbackFactorObjIso h A).inv := by
  have hcomp : (pullbackFactorObjIso h A).hom ≫ m = 𝟙 _ := by
    refine Over.hom_ext_pullback_fst c ?_
    rw [Over.comp_left, Category.assoc, hm, Over.id_left, Category.id_comp]
    exact pullbackFactorObjIso_hom_left_fst h A
  rw [← Category.id_comp m, ← Iso.inv_hom_id (pullbackFactorObjIso h A), Category.assoc, hcomp,
    Category.comp_id]

end CategoryTheory.Over

namespace AlgebraicGeometry.Space

/-- **The fullness clause of Stacks 07SK, with the comparison isomorphisms named.** This is
`AlgebraicGeometry.Space.exists_morphism_after_baseChange_of_isLimit` with its two existential
comparison isomorphisms replaced by the canonical
`CategoryTheory.Over.pullbackFactorObjIso` of the factorisation of `cS.π.app i` through the stage
`j`, which is legitimate because that clause characterises them by exactly the projection
identity that pins them -- `CategoryTheory.Over.eq_pullbackFactorObjIso_inv_of_fst`.

In this form the conclusion is an equation between two composites of named morphisms, which is
what a consumer reading the clause into the `full` field of
`AlgebraicGeometry.FinitePresentationSpacesOver.IsFinitePresentationColimit` needs. No hypothesis
on the size of the index category enters, here or in the clause. -/
theorem exists_morphism_canonical_after_baseChange_of_isLimit
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {Dsite : I ⥤ AlgebraicGeometry.BigFppfOver B S hS}
    (hAffine : ∀ {i j : I} (f : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (Dsite.map f)))
    {cS : Cone Dsite}
    (hcS : IsLimit ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).mapCone cS))
    (hQc : ∀ i, AlgebraicGeometry.Space.IsQuasiCompactSpace B S hS
      (yoneda.obj (Dsite.obj i)))
    (hQs : ∀ i, AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated B S hS
      (AlgebraicGeometry.BigFppfSite.contains_terminal B) (yoneda.obj (Dsite.obj i)))
    (i : I) (Yᵢ Zᵢ : Over (yoneda.obj (Dsite.obj i)))
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Yᵢ.left)
    (hZ' : AlgebraicGeometry.IsAlgebraicSpace B S hS Zᵢ.left)
    (hYfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Yᵢ.hom)
    (hZfp : AlgebraicGeometry.Space.IsFinitePresentation B S hS Zᵢ.hom)
    (f : (Over.pullback (yoneda.map (cS.π.app i))).obj Yᵢ ⟶
      (Over.pullback (yoneda.map (cS.π.app i))).obj Zᵢ) :
    ∃ (j : I) (e : j ⟶ i)
      (g : (Over.pullback (yoneda.map (Dsite.map e))).obj Yᵢ ⟶
        (Over.pullback (yoneda.map (Dsite.map e))).obj Zᵢ),
      (Over.pullbackFactorObjIso (yoneda_map_cone_w B S hS e) Yᵢ).hom ≫
          (Over.pullback (yoneda.map (cS.π.app j))).map g =
        f ≫ (Over.pullbackFactorObjIso (yoneda_map_cone_w B S hS e) Zᵢ).hom := by
  obtain ⟨j, e, g, α, β, hα', hβ', heq⟩ :=
    exists_morphism_after_baseChange_of_isLimit B S hS hAffine hcS hQc hQs i Yᵢ Zᵢ
      hY hZ' hYfp hZfp f
  rw [Over.eq_pullbackFactorObjIso_inv_of_fst (yoneda_map_cone_w B S hS e) Yᵢ _ hα',
    Over.eq_pullbackFactorObjIso_inv_of_fst (yoneda_map_cone_w B S hS e) Zᵢ _ hβ',
    Iso.inv_comp_eq] at heq
  exact ⟨j, e, g, by rw [heq]; simp⟩

end AlgebraicGeometry.Space

end
