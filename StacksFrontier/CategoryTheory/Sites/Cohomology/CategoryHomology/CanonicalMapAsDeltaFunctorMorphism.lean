module

public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.LeftDerivedCompose
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.LeftDerivedNatTrans
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.SimplicialReplacementChainMap
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map on the homology of a category is a morphism of δ-functors

Fix a functor `f : C' ⥤ C` between small categories. Stacks 08PH asserts that the explicit chain
map on simplicial replacements induces, on homology, the canonical map
`Stacks.CategoryHomology.categoryHomologyMap`. This file shows that, with identity coefficients,
both families of maps are morphisms of homological δ-functors out of

`F ↦ H_n(C', f⁻¹F)`.

The canonical map factors as

`Lₙ colim_{C'} (f⁻¹F) ⟶ Lₙ (f⁻¹ ⋙ colim_{C'}) (F) ⟶ Lₙ colim_C (F)`,

the first map being the comparison `CategoryTheory.Functor.leftDerivedCompApp` for the exact
functor `f⁻¹` and the second the derived functor of the natural transformation
`Stacks.CategoryHomology.colimitRestrictionPre`. The explicit chain map is natural in `F`.

## Main definitions

* `Stacks.CategoryHomology.replacementRestrictionNatTrans`: the chain map of Stacks 08PH with
  identity coefficients, as a natural transformation of functors into chain complexes.
* `Stacks.CategoryHomology.homologyMapAuxDeltaHom`: the canonical maps on homology with identity
  coefficients, as a morphism of homological δ-functors.
* `Stacks.CategoryHomology.replacementChainMapDeltaHom`: the explicit chain map with identity
  coefficients, as a morphism of homological δ-functors.

## Main results

* `Stacks.CategoryHomology.replacementGroupMapOfFunctor_naturality`: the explicit chain map is
  natural in the coefficient presheaf, degreewise.
* `Stacks.CategoryHomology.homologyMapAux_id_eq`: the factorization of the canonical map.
* `Stacks.CategoryHomology.homologyMapAuxDeltaHom_app` and
  `Stacks.CategoryHomology.replacementChainMapDeltaHom_app`: the components of the two morphisms
  of δ-functors are the canonical maps and the maps induced by the explicit chain map.

## Implementation notes

The two categories may live in different universes while the presheaves take values in the
single universe `max u u' v`, where the instance
`Stacks.CategoryHomology.presheafEnoughProjectives` is not found by instance search; the section
`Aux` therefore takes `EnoughProjectives` as a hypothesis.

In `replacementGroupMapOfFunctor_naturality`, `replacementGroupMap_summand` is given its universes
explicitly; without them `rw` is handed a universe metavariable and reports a stuck universe
constraint.

The naturality square of `replacementRestrictionNatTrans` is proved at the `replacementGroup`
spelling, with the two `HomologicalComplex.comp_f`s applied by `Eq.trans`: rewriting inside
`((presheafRestriction f ⋙ replacementComplexFunctor).obj F).X n` leaves the goal not
type-correct at `implicit` transparency.

## References

* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u' v

namespace Stacks.CategoryHomology

variable {C : Type u} {C' : Type u'} [SmallCategory C] [SmallCategory C']

/-! ### The explicit chain map as a natural transformation -/

/-- The degreewise component of `Stacks.CategoryHomology.replacementChainMap`. -/
lemma replacementChainMap_degreewise (f : C' ⥤ C)
    {F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} {F' : C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}}
    (t : F' ⟶ f.op ⋙ F) (n : ℕ) :
    (replacementChainMap f t).f n = replacementGroupMapOfFunctor f t n := by
  rw [replacementChainMap, AlgebraicTopology.alternatingFaceMapComplex_map_f]
  rfl

/-- **The explicit chain map of Stacks 08PH with identity coefficients is natural in the
coefficient presheaf**, degreewise. -/
lemma replacementGroupMapOfFunctor_naturality (f : C' ⥤ C)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}} (η : F ⟶ G) (n : ℕ) :
    replacementGroupMap (Functor.whiskerLeft f.op η) n ≫
        replacementGroupMapOfFunctor f (𝟙 (f.op ⋙ G)) n =
      replacementGroupMapOfFunctor f (𝟙 (f.op ⋙ F)) n ≫ replacementGroupMap η n := by
  refine replacementGroup_hom_ext n fun x s => ?_
  rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply,
    replacementGroupMap_summand.{u', max u v}, replacementGroupMap_on_summand,
    replacementGroupMap_on_summand, replacementGroupMap_summand.{u, max u' v}]
  rfl

/-- **The explicit chain map of Stacks 08PH with identity coefficients, as a natural
transformation** from the simplicial replacement over `C'` of the inverse image to the simplicial
replacement over `C`. -/
def replacementRestrictionNatTrans (f : C' ⥤ C) :
    presheafRestriction.{u, u', v} f ⋙ replacementComplexFunctor (C := C') ⟶
      replacementComplexFunctor (C := C) where
  app F := replacementChainMap f (𝟙 (f.op ⋙ F))
  naturality F G η := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    refine (HomologicalComplex.comp_f _ _ n).trans ?_
    refine Eq.trans ?_ (HomologicalComplex.comp_f _ _ n).symm
    rw [Functor.comp_map, replacementComplexFunctor_map_f, replacementComplexFunctor_map_f,
      replacementChainMap_degreewise, replacementChainMap_degreewise]
    exact replacementGroupMapOfFunctor_naturality f η n

/-- The components of `Stacks.CategoryHomology.replacementRestrictionNatTrans`. -/
@[simp]
lemma replacementRestrictionNatTrans_app (f : C' ⥤ C)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) :
    (replacementRestrictionNatTrans.{u, u', v} f).app F =
      replacementChainMap f (𝟙 (f.op ⋙ F)) :=
  rfl

/-- **The explicit chain map of Stacks 08PH with identity coefficients, as a morphism of
homological δ-functors** from the simplicial replacement δ-functor over `C'`, precomposed with
restriction along `f`, to the simplicial replacement δ-functor over `C`. -/
def replacementChainMapDeltaHom (f : C' ⥤ C) :
    (replacementHomologyDeltaFunctor.{u', max u v} (C := C')).precomp
        (presheafRestriction.{u, u', v} f) ⟶
      replacementHomologyDeltaFunctor.{u, max u' v} (C := C) :=
  HomologicalDeltaFunctor.precompHomOfChainComplexNatTrans (presheafRestriction.{u, u', v} f)
    (fun hS => replacementComplexFunctor_map_shortExact.{u', max u v} hS)
    (fun hS => replacementComplexFunctor_map_shortExact.{u, max u' v} hS)
    (replacementRestrictionNatTrans.{u, u', v} f)

/-- The components of `Stacks.CategoryHomology.replacementChainMapDeltaHom` are the maps on
homology induced by the explicit chain map. -/
lemma replacementChainMapDeltaHom_app (f : C' ⥤ C) (n : ℕ)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) :
    ((replacementChainMapDeltaHom.{u, u', v} f).app n).app F =
      HomologicalComplex.homologyMap (replacementChainMap f (𝟙 (f.op ⋙ F))) n :=
  rfl

/-! ### The canonical map as a morphism of δ-functors -/

section Aux

variable [EnoughProjectives (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]
  [EnoughProjectives (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v})]

/-- **The canonical map on homology, with identity coefficients, factors** through the left
derived functors of the composite `f⁻¹ ⋙ colim_{C'}`: first the comparison
`CategoryTheory.Functor.leftDerivedCompApp` of the two ways of deriving in the `C`-direction,
then the derived functor of the comparison `Stacks.CategoryHomology.colimitRestrictionPre` of the
two colimits. -/
lemma homologyMapAux_id_eq (f : C' ⥤ C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) (n : ℕ) :
    homologyMapAux.{u, u', v} f (𝟙 (f.op ⋙ F)) n =
      Functor.leftDerivedCompApp (presheafRestriction.{u, u', v} f)
          (colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _) n F ≫
        (NatTrans.leftDerived (colimitRestrictionPre.{u, u', v} f) n).app F := by
  rw [ProjectiveResolution.leftDerived_app_eq (colimitRestrictionPre.{u, u', v} f)
    (ProjectiveResolution.of F) n]
  dsimp only [homologyMapAux, Functor.leftDerivedCompApp, Functor.leftDerivedCompAppOf,
    ProjectiveResolution.transferHomology]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.comp_map]
  rw [← Functor.map_comp_assoc]
  rfl

/-- **The canonical maps on homology with identity coefficients, as a morphism of homological
δ-functors.** -/
def homologyMapAuxDeltaHom (f : C' ⥤ C) :
    ((colim : (C'ᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerivedHomologicalDeltaFunctor).precomp
        (presheafRestriction.{u, u', v} f) ⟶
      (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) ⥤ _).leftDerivedHomologicalDeltaFunctor :=
  Functor.leftDerivedCompDeltaHom (presheafRestriction.{u, u', v} f) colim ≫
    NatTrans.leftDerivedDeltaFunctorHom (colimitRestrictionPre.{u, u', v} f)

/-- The components of `Stacks.CategoryHomology.homologyMapAuxDeltaHom` are the canonical maps on
homology with identity coefficients. -/
lemma homologyMapAuxDeltaHom_app (f : C' ⥤ C) (n : ℕ)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{max u u' v}) :
    ((homologyMapAuxDeltaHom.{u, u', v} f).app n).app F =
      homologyMapAux.{u, u', v} f (𝟙 (f.op ⋙ F)) n := by
  rw [homologyMapAux_id_eq]
  rfl

end Aux

end Stacks.CategoryHomology

end
