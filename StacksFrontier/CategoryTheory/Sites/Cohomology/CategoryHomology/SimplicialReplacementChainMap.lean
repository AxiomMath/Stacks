module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.SimplicialReplacement
import StacksCore.Tactic.StacksAttribute

/-!
# The explicit chain map on simplicial replacements

Let `u : C' ⥤ C` be a functor between small categories, let `F` be an abelian-group-valued
presheaf on `C`, let `F'` be one on `C'`, and let `t : F' ⟶ u^{-1}F` be a morphism of
presheaves on `C'`, where `u^{-1}F = u.op ⋙ F` is the inverse image. Stacks 08PH describes a
map of simplicial replacement complexes `K_•(F') ⟶ K_•(F)` by the rule
`(U'ₙ → ⋯ → U'₀, s') ↦ (u(U'ₙ) → ⋯ → u(U'₀), t(s'))`:
on the summand indexed by a string of composable arrows of `C'` it applies `u` to the string
and the coefficient morphism at its right endpoint.

## Main definitions

* `Stacks.CategoryHomology.replacementSummand`: the generator of the summand of
  `replacementGroup F n` indexed by a string `x`, carrying a section over `x.right`.
* `Stacks.CategoryHomology.replacementGroupMapOfFunctor`: the degreewise map of replacement groups.
* `Stacks.CategoryHomology.replacementSimplicialMap`: these maps assembled into a morphism of
  simplicial abelian groups.
* `Stacks.CategoryHomology.replacementChainMap`: its alternating face map complex, the map
  `K_•(F') ⟶ K_•(F)` of the source.

## Main results

* `Stacks.CategoryHomology.replacementGroupMap_on_summand` and
  `Stacks.CategoryHomology.replacementChainMap_on_summand`: the formula of the source, in each
  degree.

## Implementation notes

Strings are `ComposableArrows`, so applying `u` to a string is `Functor.mapComposableArrows`.
The right endpoint of the image string is the image of the right endpoint, and reindexing by a
simplicial operator commutes with applying `u`, both by `rfl`; so the two generators compared in
the simplicial naturality square carry the same index and only their coefficients differ.

## References

* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped DirectSum Simplicial

universe u u' v

namespace Stacks.CategoryHomology

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C']

/-- The element of `replacementGroup F n` in the summand indexed by the string `x` with
coefficient `s` over the right endpoint of `x`. -/
noncomputable def replacementSummand (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (n : ℕ)
    (x : ComposableArrows C n) (s : F.obj (op x.right)) :
    replacementGroup F n := by
  classical
  exact DirectSum.of (fun y : ComposableArrows C n => F.obj (op y.right)) x s

/-- The degreewise map of replacement groups induced by a functor `f : C' ⥤ C` and a morphism
`t : F' ⟶ f.op ⋙ F` of presheaves: the summand indexed by `x` is sent to the summand indexed
by the image string `x ⋙ f`, the coefficient being moved by `t` at the right endpoint. -/
noncomputable def replacementGroupMapOfFunctor (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) (n : ℕ) :
    replacementGroup F' n ⟶ replacementGroup F n := by
  classical
  exact AddCommGrpCat.ofHom <| DirectSum.toAddMonoid fun x : ComposableArrows C' n =>
    (DirectSum.of (fun y : ComposableArrows C n => F.obj (op y.right))
      ((f.mapComposableArrows n).obj x)).comp (t.app (op x.right)).hom

/-- The value of `replacementGroupMapOfFunctor` on the generator of the summand indexed by `x`. -/
lemma replacementGroupMap_on_summand (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) (n : ℕ)
    (x : ComposableArrows C' n) (s : F'.obj (op x.right)) :
    (replacementGroupMapOfFunctor f t n).hom (replacementSummand F' n x s) =
      replacementSummand F n ((f.mapComposableArrows n).obj x)
        ((t.app (op x.right)).hom s) := by
  classical
  simp only [replacementGroupMapOfFunctor, replacementSummand, AddCommGrpCat.hom_ofHom,
    DirectSum.toAddMonoid_of, AddMonoidHom.coe_comp, Function.comp_apply]

/-- Two maps out of a replacement group agree as soon as they agree on every summand. -/
lemma replacementGroup_hom_ext {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{v}} (n : ℕ)
    {A : AddCommGrpCat.{max u' v}} {φ ψ : replacementGroup F' n ⟶ A}
    (h : ∀ (x : ComposableArrows C' n) (s : F'.obj (op x.right)),
      φ.hom (replacementSummand F' n x s) = ψ.hom (replacementSummand F' n x s)) :
    φ = ψ := by
  classical
  exact AddCommGrpCat.hom_ext (DirectSum.addHom_ext' fun x => AddMonoidHom.ext fun s => h x s)

/-- The maps `replacementGroupMapOfFunctor` commute with the simplicial operators. -/
lemma replacementGroupMap_naturality (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) {Δ Γ : SimplexCategoryᵒᵖ} (g : Δ ⟶ Γ) :
    replacementMap F' g ≫ replacementGroupMapOfFunctor f t Γ.unop.len =
      replacementGroupMapOfFunctor f t Δ.unop.len ≫ replacementMap F g := by
  refine replacementGroup_hom_ext _ fun x s => ?_
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply]
  have hL : (replacementGroupMapOfFunctor f t Γ.unop.len).hom
      ((replacementMap F' g).hom (replacementSummand F' Δ.unop.len x s)) =
      replacementSummand F Γ.unop.len
        ((f.mapComposableArrows Γ.unop.len).obj (x.whiskerLeft (simplexIndexMap g.unop)))
        ((t.app (op (x.whiskerLeft (simplexIndexMap g.unop)).right)).hom
          ((F'.map (op (x.map (homOfLE (Fin.le_last _))))).hom s)) := by
    rw [show (replacementMap F' g).hom (replacementSummand F' Δ.unop.len x s) =
        replacementSummand F' Γ.unop.len (x.whiskerLeft (simplexIndexMap g.unop))
          ((F'.map (op (x.map (homOfLE (Fin.le_last _))))).hom s) from
      replacementMap_on_generator F' g x s]
    exact replacementGroupMap_on_summand f t Γ.unop.len _ _
  have hR : (replacementMap F g).hom
      ((replacementGroupMapOfFunctor f t Δ.unop.len).hom (replacementSummand F' Δ.unop.len x s)) =
      replacementSummand F Γ.unop.len
        (((f.mapComposableArrows Δ.unop.len).obj x).whiskerLeft (simplexIndexMap g.unop))
        ((F.map (op (((f.mapComposableArrows Δ.unop.len).obj x).map
            (homOfLE (Fin.le_last _))))).hom
          ((t.app (op x.right)).hom s)) := by
    rw [replacementGroupMap_on_summand f t Δ.unop.len x s]
    exact replacementMap_on_generator F g _ _
  rw [hL, hR]
  refine congrArg _ ?_
  have hnat := ConcreteCategory.congr_hom
    (t.naturality (op (x.map (homOfLE (Fin.le_last
      ((simplexIndexMap g.unop).obj (Fin.last Γ.unop.len))))))) s
  simp only [ConcreteCategory.comp_apply] at hnat
  exact hnat

/-- The morphism of simplicial abelian groups `K(F') ⟶ K(F)` induced by a functor `f : C' ⥤ C`
and a morphism `t : F' ⟶ f.op ⋙ F` of presheaves. -/
noncomputable def replacementSimplicialMap (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) :
    simplicialReplacement F' ⟶ simplicialReplacement F where
  app Δ := replacementGroupMapOfFunctor f t Δ.unop.len
  naturality _ _ g := replacementGroupMap_naturality f t g

/-- The map of simplicial replacement complexes `K_•(F') ⟶ K_•(F)` induced by a functor
`f : C' ⥤ C` and a morphism `t : F' ⟶ f.op ⋙ F` of abelian presheaves. -/
@[stacks 08PH "the displayed chain map"]
noncomputable def replacementChainMap (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) :
    simplicialReplacementComplex F' ⟶ simplicialReplacementComplex F :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (replacementSimplicialMap f t)

/-- On the summand indexed by a string of arrows of `C'`, the chain map
`Stacks.CategoryHomology.replacementChainMap` applies `f` to that string and the coefficient
morphism `t` at its right endpoint. -/
@[stacks 08PH "the displayed chain map on summands"]
theorem replacementChainMap_on_summand (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) (n : ℕ)
    (x : ComposableArrows C' n) (s : F'.obj (op x.right)) :
    ((replacementChainMap f t).f n).hom (replacementSummand F' n x s) =
      replacementSummand F n ((f.mapComposableArrows n).obj x)
        ((t.app (op x.right)).hom s) := by
  rw [replacementChainMap, AlgebraicTopology.alternatingFaceMapComplex_map_f]
  exact replacementGroupMap_on_summand f t n x s

end Stacks.CategoryHomology

end
