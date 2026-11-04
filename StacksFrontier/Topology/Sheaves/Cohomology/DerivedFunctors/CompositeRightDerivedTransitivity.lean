module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonOnResolutions
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# The composition law for `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso`

`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L G n` compares, for an exact
functor `L` preserving injective objects and an additive functor `G`, the right-derived functor
of the composite `L ⋙ G` with the composite `L ⋙ G.rightDerived n`. Composing two such exact
functors `L₁ : C ⥤ D` and `L₂ : D ⥤ E` gives two routes from `((L₁ ⋙ L₂) ⋙ G).rightDerived n` to
`(L₁ ⋙ L₂) ⋙ G.rightDerived n`: treat `L₁ ⋙ L₂` as a single exact functor and apply
`compRightDerivedNatIso` once, or apply `compRightDerivedNatIso L₁ (L₂ ⋙ G)` and then
`compRightDerivedNatIso L₂ G` and compose. This file proves the two agree.

## Main results

* `compRightDerivedNatIso_hom_app_comp`: the composition law, pointwise.
* `compRightDerivedNatIso_comp`: the same, as an equality of natural transformations.

## Implementation notes

`(L₁ ⋙ L₂) ⋙ G` and `L₁ ⋙ (L₂ ⋙ G)` are the same functor by `rfl`, since
`CategoryTheory.Functor.comp` composes the underlying functions on objects and morphisms, and
likewise for `((L₁ ⋙ L₂).mapHomologicalComplex _).obj K` against
`(L₂.mapHomologicalComplex _).obj ((L₁.mapHomologicalComplex _).obj K)`; the proof below exploits
both identifications directly, through elaboration against the expected type, rather than
through an explicit `eqToIso`, following the pattern already used for
`Stacks.Cohomology.DerivedCompTransport.compRightDerivedNatIso_hom_app_mapInjRes`. The two
single-step comparisons through `L₁` and through `L₂` are read off that lemma directly; the
one-step comparison through the composite `L₁ ⋙ L₂` is read off
`compRightDerivedNatIso_hom_app_eq` with the identity cochain map, and the middle
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` of `L₁.obj X` then cancels against its
own inverse.

## References

* [The Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedCompTransport

open Stacks.Cohomology.CompositeRightDerived

variable {C : Type*} {D : Type*} {E : Type*} {F : Type*}
  [Category* C] [Category* D] [Category* E] [Category* F]
  [Abelian C] [HasInjectiveResolutions C] [Abelian D] [HasInjectiveResolutions D]
  [Abelian E] [HasInjectiveResolutions E] [Abelian F]
  (L₁ : C ⥤ D) (L₂ : D ⥤ E) (G : E ⥤ F)
  [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [L₁.PreservesInjectiveObjects]
  [L₂.Additive] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [L₂.PreservesInjectiveObjects] [G.Additive]

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] [HasInjectiveResolutions E] in
/-- The augmentation of the image of an injective resolution `I` of `X` under the composite
resolution-pushforward `mapInjRes L₂ (mapInjRes L₁ I)` is the image of the augmentation of `I`
under `L₁ ⋙ L₂`. This is `mapInjRes_ι_f_zero` applied twice, through `Functor.comp.map`. -/
theorem mapInjRes_mapInjRes_ι_f_zero {X : C} (I : InjectiveResolution X) :
    (CompositeRightDerived.mapInjRes L₂ (CompositeRightDerived.mapInjRes L₁ I)).ι.f 0 =
      (L₁ ⋙ L₂).map (I.ι.f 0) :=
  (mapInjRes_ι_f_zero L₂ (CompositeRightDerived.mapInjRes L₁ I)).trans
    (congrArg L₂.map (mapInjRes_ι_f_zero L₁ I))

/-- **The composition law for `compRightDerivedNatIso`, pointwise.** Deriving `L₁`, applying the
comparison against `L₂ ⋙ G`, and then applying the comparison for `L₂` against `G` agrees with
applying the comparison for the single composite functor `L₁ ⋙ L₂` against `G`. -/
theorem compRightDerivedNatIso_hom_app_comp
    [PreservesFiniteLimits (L₁ ⋙ L₂)] [PreservesFiniteColimits (L₁ ⋙ L₂)] (n : ℕ) (X : C) :
    (CompositeRightDerived.compRightDerivedNatIso (L₁ ⋙ L₂) G n).hom.app X =
      (CompositeRightDerived.compRightDerivedNatIso L₁ (L₂ ⋙ G) n).hom.app X ≫
        (CompositeRightDerived.compRightDerivedNatIso L₂ G n).hom.app (L₁.obj X) := by
  set I := injectiveResolution X with hI
  set J := CompositeRightDerived.mapInjRes L₁ I with hJ
  set K := CompositeRightDerived.mapInjRes L₂ J with hK
  have hcomm : (L₁ ⋙ L₂).map (I.ι.f 0) ≫
      (𝟙 K.cocomplex :
        ((L₁ ⋙ L₂).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶
          K.cocomplex).f 0 =
      K.ι.f 0 :=
    (congrArg (fun g => (L₁ ⋙ L₂).map (I.ι.f 0) ≫ g) (HomologicalComplex.id_f K.cocomplex 0)).trans
      ((Category.comp_id _).trans (mapInjRes_mapInjRes_ι_f_zero L₁ L₂ I).symm)
  have h1 : (CompositeRightDerived.compRightDerivedNatIso (L₁ ⋙ L₂) G n).hom.app X =
      (I.isoRightDerivedObj ((L₁ ⋙ L₂) ⋙ G) n).hom ≫ (K.isoRightDerivedObj G n).inv := by
    refine Eq.trans
      (compRightDerivedNatIso_hom_app_eq (L₁ ⋙ L₂) G n I K
        (𝟙 K.cocomplex :
          ((L₁ ⋙ L₂).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ K.cocomplex)
        hcomm) ?_
    refine congrArg (fun g => (I.isoRightDerivedObj ((L₁ ⋙ L₂) ⋙ G) n).hom ≫ g) ?_
    refine Eq.trans (congrArg (fun g => g ≫ (K.isoRightDerivedObj G n).inv) ?_)
      (Category.id_comp _)
    exact CategoryTheory.Functor.map_id (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor F (ComplexShape.up ℕ) n) K.cocomplex
  have h2 : (CompositeRightDerived.compRightDerivedNatIso L₁ (L₂ ⋙ G) n).hom.app X =
      (I.isoRightDerivedObj (L₁ ⋙ L₂ ⋙ G) n).hom ≫ (J.isoRightDerivedObj (L₂ ⋙ G) n).inv :=
    compRightDerivedNatIso_hom_app_mapInjRes L₁ (L₂ ⋙ G) n I
  have h3 : (CompositeRightDerived.compRightDerivedNatIso L₂ G n).hom.app (L₁.obj X) =
      (J.isoRightDerivedObj (L₂ ⋙ G) n).hom ≫ (K.isoRightDerivedObj G n).inv :=
    compRightDerivedNatIso_hom_app_mapInjRes L₂ G n J
  have hassoc : ((I.isoRightDerivedObj (L₁ ⋙ L₂ ⋙ G) n).hom ≫
        (J.isoRightDerivedObj (L₂ ⋙ G) n).inv) ≫
      ((J.isoRightDerivedObj (L₂ ⋙ G) n).hom ≫ (K.isoRightDerivedObj G n).inv) =
      (I.isoRightDerivedObj (L₁ ⋙ L₂ ⋙ G) n).hom ≫ (K.isoRightDerivedObj G n).inv :=
    (Category.assoc (I.isoRightDerivedObj (L₁ ⋙ L₂ ⋙ G) n).hom
        (J.isoRightDerivedObj (L₂ ⋙ G) n).inv
        ((J.isoRightDerivedObj (L₂ ⋙ G) n).hom ≫ (K.isoRightDerivedObj G n).inv)).trans
      (congrArg (fun g => (I.isoRightDerivedObj (L₁ ⋙ L₂ ⋙ G) n).hom ≫ g)
        (Iso.inv_hom_id_assoc (J.isoRightDerivedObj (L₂ ⋙ G) n) (K.isoRightDerivedObj G n).inv))
  rw [h1, h2, h3]
  exact hassoc.symm

/-- **The composition law for `compRightDerivedNatIso`.** Deriving `L₁`, applying the comparison
against `L₂ ⋙ G`, and then applying (the left whiskering of) the comparison for `L₂` against `G`
agrees with the comparison for the single composite functor `L₁ ⋙ L₂` against `G`. This is
`compRightDerivedNatIso_hom_app_comp`, packaged as an equality of natural transformations. -/
theorem compRightDerivedNatIso_comp
    [PreservesFiniteLimits (L₁ ⋙ L₂)] [PreservesFiniteColimits (L₁ ⋙ L₂)] (n : ℕ) :
    (CompositeRightDerived.compRightDerivedNatIso (L₁ ⋙ L₂) G n).hom =
      (CompositeRightDerived.compRightDerivedNatIso L₁ (L₂ ⋙ G) n).hom ≫
        Functor.whiskerLeft L₁ (CompositeRightDerived.compRightDerivedNatIso L₂ G n).hom :=
  NatTrans.ext (funext fun X => compRightDerivedNatIso_hom_app_comp L₁ L₂ G n X)

end Stacks.Cohomology.DerivedCompTransport

end
