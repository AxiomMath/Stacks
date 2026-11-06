module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactMapDerivedPlusIsoApp
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusSingleCompatible
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit

/-!
# For an exact functor, the comparison `F(ℱ)[0] ≅ RF(ℱ[0])` is the canonical map

Let `F : 𝒜 ⥤ ℬ` be an exact additive functor between abelian categories, with `𝒜` having enough
injectives. There are two maps `F(ℱ)[0] ⟶ RF(ℱ[0])` in `D⁺(ℬ)` in this development, built in
different worlds:

* `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso F 0` is an *isomorphism*, obtained
  by identifying `RF` with the degreewise action of `F` — which is possible because the
  derived-functor unit of an exact functor is invertible — and then using Mathlib's comparison
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` of the degreewise action with the
  degree-zero embedding;
* `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F` is the derived-functor *unit* on the
  complexes concentrated in degree zero, available for every additive `F`.

This file proves they agree. The first is what `Stacks.EtaleCohomology.baseChangeTargetIso`
identifies the target of a higher base change map with; the second is what the degreewise
descent of a base change pasting law is stated in terms of
(`Stacks.Cohomology.BaseChange.unitSingle_comp_derived`), so the identification is what lets the
two be composed.

## Main results

* `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_hom`: **the comparison is the
  canonical map.**
* `Stacks.DerivedFunctor.ι_map_mapDerivedCategoryPlus_map`: the degreewise action of an exact
  functor on bounded below derived categories, read through the inclusion into the unbounded
  one. It holds by definition, that action being a `CategoryTheory.ObjectProperty.lift` of the
  unbounded one. The companion statement for
  `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle` is
  `Stacks.DerivedFunctor.ι_map_exactMapDerivedCategoryPlusSingle_inv_app`, already present.
* `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_residual` and
  `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_residual_unbounded`: the identity
  of the two identifications of `(Fℱ)[0]` with the image of `F` applied to the single complex,
  in `D⁺(ℬ)` and in `D(ℬ)`.

## Implementation notes

*Where the content is.* Both maps contain exactly one copy of the derived-functor unit of `F`,
and nothing else about right derivation: the comparison carries it inside
`Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso`, which is a
`CategoryTheory.Localization.liftNatIso` and is therefore computed on the image of `Qh` by
`Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_hom_app_Qh`; the canonical map carries it
openly. So the identity reduces, by the naturality of that comparison along
`CategoryTheory.Functor.singleFunctorPlusIsoCompQh` and the cancellation of one isomorphism, to
an identity between two *degreewise* identifications of `(Fℱ)[0]` with the image in `D⁺(ℬ)` of
`F(ℱ[0])`, with no derived functor left in it. That is
`exactSingleFunctorRightDerivedPlusIso_residual`.

*Why the residual identity is proved in the unbounded derived category.* Each of its factors is
a `DerivedCategory.Plus.ι`-preimage, and the comparisons it is built from
(`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`,
`CategoryTheory.Functor.mapDerivedCategoryFactors`) are stated by Mathlib only on the unbounded
derived category. So the identity is pushed down along the faithful `ι`, where both sides become
the class of `HomologicalComplex.singleMapHomologicalComplex`: the degreewise comparison
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` through the homotopy category contributes a
`DerivedCategory.quotientCompQhIso` that cancels against the one inside
`DerivedCategory.singleFunctorIsoCompQh`, and
`CategoryTheory.Functor.mapHomotopyCategoryFactors` has identity components.

*Why everything is assembled in term mode.* The rearrangements are chains of
`CategoryTheory.eq_whisker`, `CategoryTheory.whisker_eq` and `CategoryTheory.Category.assoc`
used as equations rather than as rewrites. The objects here carry two spellings apiece — the
image of a composite versus the composite of images, `Qh` of a quotient versus `Q` — and a `rw`
that moves a morphism across that boundary builds a motive which is not type-correct at the
transparency the rewriters match at, the localization `HomologicalComplexUpToQuasiIso.Qh` not
being exposed. The same remark is recorded in
`StacksFrontier/Homology/DerivedIndexing/SingleDegreeUnit.lean`.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v v' u u'

namespace Stacks.DerivedFunctor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Exact

/-- A functor maps a composite that is the identity to a composite that is the identity. -/
private theorem map_comp_eq_id {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {P Q : C} {f : P ⟶ Q} {g : Q ⟶ P} (h : f ≫ g = 𝟙 _) : G.map f ≫ G.map g = 𝟙 _ := by
  rw [← G.map_comp, h, G.map_id]

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-! ### The degreewise action, read in the unbounded derived category -/

/-- **The degreewise action of an exact functor on bounded below derived categories is the
restriction of its action on the unbounded one.** It is defined as a
`CategoryTheory.ObjectProperty.lift` of that action, so this holds by definition. -/
public theorem ι_map_mapDerivedCategoryPlus_map {K L : DerivedCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) :=
  rfl

/-! ### The residual identity -/

/-- **The residual identity, in the unbounded derived category.** Mathlib's comparison of the
degreewise action with the degree-zero embedding, read backwards, followed by the degreewise
action of the identification of the degree-zero embedding with the one through the homotopy
category and by the degreewise factorization of the action through the homotopy category, is the
class of `HomologicalComplex.singleMapHomologicalComplex`.

The two `DerivedCategory.quotientCompQhIso` factors cancel,
`CategoryTheory.Functor.mapHomotopyCategoryFactors` has identity components, and what is left is
Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app`
followed by the naturality of `DerivedCategory.quotientCompQhIso`. -/
public theorem exactSingleFunctorRightDerivedPlusIso_residual_unbounded (X : C) :
    (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        F.mapDerivedCategory.map ((DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X) ≫
          F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor C 0).obj X) =
      (DerivedCategory.singleFunctorIsoCompQh D 0).hom.app (F.obj X) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) 0).inv.app X)) := by
  have h₁ : (DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X =
      (DerivedCategory.quotientCompQhIso C).inv.app
        ((CochainComplex.singleFunctor C 0).obj X) :=
    Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app 0 X
  have hm₄ : DerivedCategory.Qh.map
        ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
          ((CochainComplex.singleFunctor C 0).obj X)) =
      𝟙 _ :=
    (congrArg DerivedCategory.Qh.map
        (Stacks.DerivedIndexing.mapHomotopyCategoryFactors_inv_app F _)).trans
      (DerivedCategory.Qh.map_id _)
  have hc : F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor C 0).obj X) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app
            ((CochainComplex.singleFunctor C 0).obj X)) ≫
        F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
          (DerivedCategory.quotientCompQhIso D).inv.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((CochainComplex.singleFunctor C 0).obj X)) := by
    refine (F.mapDerivedCategoryFactorsh_hom_app _).trans ?_
    exact CategoryTheory.whisker_eq _ (CategoryTheory.whisker_eq _
      ((CategoryTheory.whisker_eq _ hm₄).trans (Category.comp_id _)))
  have hbc : F.mapDerivedCategory.map ((DerivedCategory.singleFunctorIsoCompQh C 0).hom.app X) ≫
        F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor C 0).obj X) =
      F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) ≫
        (DerivedCategory.quotientCompQhIso D).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj X)) := by
    refine Eq.trans (CategoryTheory.whisker_eq _ hc) ?_
    refine Eq.trans
      (CategoryTheory.eq_whisker (congrArg F.mapDerivedCategory.map h₁) _) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (CategoryTheory.eq_whisker (map_comp_eq_id _ (Iso.inv_hom_id_app _ _)) _) ?_
    exact Category.id_comp _
  have h₅ : (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
        F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj X) =
      DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F
        (ComplexShape.up ℤ) 0).inv.app X) :=
    F.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app X
  have h₆ : DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.up ℤ) 0).inv.app X) ≫
        (DerivedCategory.quotientCompQhIso D).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor C 0).obj X)) =
      (DerivedCategory.singleFunctorIsoCompQh D 0).hom.app (F.obj X) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) 0).inv.app X)) :=
    ((DerivedCategory.quotientCompQhIso D).inv.naturality _).trans
      (CategoryTheory.eq_whisker
        (Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app 0 (F.obj X)).symm _)
  refine Eq.trans (CategoryTheory.whisker_eq _ hbc) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.eq_whisker h₅ _) ?_
  exact h₆

variable [EnoughInjectives C]

omit [EnoughInjectives C] in
/-- **The residual identity.** The comparison of the degree-zero embedding with the degreewise
action, read backwards, followed by the degreewise action of the identification of `ℱ[0]` with
its image from `K⁺(𝒜)` and by the degreewise factorization through `K⁺(𝒜)`, is
`CategoryTheory.Functor.mapSingleFunctorCompQhIso` read backwards. No derived functor occurs in
it.

Both sides are `DerivedCategory.Plus.ι`-preimages; the identity is
`exactSingleFunctorRightDerivedPlusIso_residual_unbounded`. -/
public theorem exactSingleFunctorRightDerivedPlusIso_residual (X : C) :
    (exactMapDerivedCategoryPlusSingle F 0).inv.app X ≫
        F.mapDerivedCategoryPlus.map
            ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).hom.app X) ≫
          F.mapDerivedCategoryPlusFactorsh.hom.app
            ((HomotopyCategory.Plus.singleFunctor C 0).obj X) =
      (Functor.mapSingleFunctorCompQhIso F).inv.app X := by
  refine DerivedCategory.Plus.ι.map_injective ?_
  refine Eq.trans (DerivedCategory.Plus.ι.map_comp _ _) ?_
  refine Eq.trans (CategoryTheory.whisker_eq _ (DerivedCategory.Plus.ι.map_comp _ _)) ?_
  refine Eq.trans ?_ (Stacks.DerivedIndexing.ι_map_mapSingleFunctorCompQhIso_inv_app F X).symm
  refine Eq.trans (CategoryTheory.eq_whisker
    (ι_map_exactMapDerivedCategoryPlusSingle_inv_app F 0 X) _) ?_
  refine Eq.trans (CategoryTheory.whisker_eq _ (CategoryTheory.eq_whisker
    ((ι_map_mapDerivedCategoryPlus_map F _).trans
      (congrArg F.mapDerivedCategory.map
        (Stacks.DerivedIndexing.ι_map_singleFunctorPlusIsoCompQh_hom_app 0 X))) _)) ?_
  exact exactSingleFunctorRightDerivedPlusIso_residual_unbounded F X

/-- **For an exact functor the comparison `F(ℱ)[0] ≅ RF(ℱ[0])` is the canonical map.** The
isomorphism `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso F 0`, which exists
because the derived-functor unit of an exact functor is invertible, has as its underlying
morphism the canonical map `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F` available for
every additive functor.

Composing with the isomorphism `RF` applied to the identification of `ℱ[0]` with its image from
`K⁺(𝒜)`, both sides become
`CategoryTheory.Functor.mapSingleFunctorCompQhIso` read backwards followed by the derived-functor
unit at the single complex: on the right by definition, on the left by the naturality of
`Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso`, its computation on the image of `Qh`
(`Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso_hom_app_Qh`) and
`exactSingleFunctorRightDerivedPlusIso_residual`. -/
public theorem exactSingleFunctorRightDerivedPlusIso_hom :
    (exactSingleFunctorRightDerivedPlusIso F 0).hom =
      Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F := by
  refine NatTrans.ext (funext fun X => ?_)
  refine (cancel_mono (F.rightDerivedFunctorPlus.map
    ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).hom.app X))).1 ?_
  have hL : (exactSingleFunctorRightDerivedPlusIso F 0).hom.app X =
      (exactMapDerivedCategoryPlusSingle F 0).inv.app X ≫
        (exactMapDerivedCategoryPlusIso F).hom.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj X) := rfl
  have hQh : (exactMapDerivedCategoryPlusIso F).hom.app
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor C 0).obj X)) =
      F.mapDerivedCategoryPlusFactorsh.hom.app
          ((HomotopyCategory.Plus.singleFunctor C 0).obj X) ≫
        F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor C 0).obj X) :=
    exactMapDerivedCategoryPlusIso_hom_app_Qh F _
  have hnat := ((exactMapDerivedCategoryPlusIso F).hom.naturality
    ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).hom.app X)).symm
  have e₁ : (exactSingleFunctorRightDerivedPlusIso F 0).hom.app X ≫
        F.rightDerivedFunctorPlus.map
          ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).hom.app X) =
      (Functor.mapSingleFunctorCompQhIso F).inv.app X ≫
        F.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.singleFunctor C 0).obj X) := by
    refine Eq.trans (CategoryTheory.eq_whisker hL _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (CategoryTheory.whisker_eq _ hnat) ?_
    refine Eq.trans (CategoryTheory.whisker_eq _ (CategoryTheory.whisker_eq _ hQh)) ?_
    refine Eq.trans (CategoryTheory.whisker_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    exact CategoryTheory.eq_whisker
      (exactSingleFunctorRightDerivedPlusIso_residual F X) _
  have e₂ : (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F).app X ≫
        F.rightDerivedFunctorPlus.map
          ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).hom.app X) =
      (Functor.mapSingleFunctorCompQhIso F).inv.app X ≫
        F.rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.singleFunctor C 0).obj X) := by
    refine Eq.trans (CategoryTheory.eq_whisker
      (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle_app F X) _) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (CategoryTheory.whisker_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (CategoryTheory.whisker_eq _ (CategoryTheory.whisker_eq _
      (map_comp_eq_id _ (Iso.inv_hom_id_app _ _)))) ?_
    exact CategoryTheory.whisker_eq _ (Category.comp_id _)
  exact e₁.trans e₂.symm

end Exact

end Stacks.DerivedFunctor

end
