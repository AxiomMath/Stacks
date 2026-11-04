module

public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import StacksFrontier.CategoryTheory.Sites.IntegralCechComplex
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.IntegralComplexIsAResolution

/-!
# Exactness of the integral Čech complex

Let `E` be a family of morphisms `E.f j : E.X j ⟶ X` in a category `C`, presented as a
`CategoryTheory.PreZeroHypercover`, and assume that the finite nonempty fibre products of the
family exist.  The *integral Čech complex* of `E` is the chain complex
`Stacks.CechSite.integralCechComplex` of abelian presheaves whose degree `n` term is
`⨁_{i : Fin (n + 1) → E.I₀} **Z**[U_i]`, with `U_i` the fibre product of the `E.X (i p)` over
`X`.  This file supplies the universe-lifting comparison that identifies that complex with the
free abelian presheaf complex of a Čech nerve; the positive-degree vanishing itself is
`Stacks.CechSite.integralCechComplex_homology_isZero`.

The two substantive ingredients are already available in
`StacksFrontier.CategoryTheory.Sites.IntegralCechComplex`: the identification
`Stacks.IntegralCech.cechSimplicialIso` of the realization of the simplicial formal coproduct
of the fibre products with the Čech nerve of the morphism of presheaves of sets induced by
`E`, and the vanishing `Stacks.IntegralCech.isZero_homology_freeAbelian_cechNerve` of the
positive homology of the free abelian presheaf complex of a Čech nerve.  What this file adds
is the universe crossing between them: the index type `E.I₀` lives in `Type w`, so the
presheaves of *sets* of the comparison live in `Type (max w v a)`, while the integral Čech
complex has coefficients in `AddCommGrpCat.{max v a}`.

## Main definitions

* `AddCommGrpCat.freeCompUliftFunctorIso` and `CategoryTheory.uliftFunctorCompIso`: the free
  abelian group functor commutes with universe lifting, and iterated universe lifting of
  types is a single universe lift.
* `CategoryTheory.Limits.FormalCoproduct.evalCompIso`: a functor preserving `w`-indexed
  coproducts commutes with the extension of a functor along
  `CategoryTheory.Limits.FormalCoproduct.eval`.
* `Stacks.IntegralCech.uliftPresheaf` lifts the coefficient universe of a presheaf of abelian
  groups.

## Main results

* `Stacks.IntegralCech.freeAbelianYonedaCompUliftPresheafIso`: lifting the coefficients of the
  free abelian representable presheaf is the free abelian presheaf on the further lifted
  representable presheaf.
* `Stacks.IntegralCech.typeRealizationIso`: the realization of a formal coproduct as a
  presheaf of sets is the coproduct of the lifted representable presheaves of its members.
* `Stacks.IntegralCech.integralCechRealizationCompUliftPresheafIso`: lifting the coefficients
  of the integral realization of a formal coproduct is the free abelian presheaf on its
  realization as a presheaf of sets.
* `Stacks.CechSite.integralCechComplex_homology_isZero` (elsewhere): **Tag 03AT**, the homology
  presheaves of the integral Čech complex vanish in every positive degree.

## Implementation notes

The index universe `w` of the family is independent of the coefficient universe `max v a`.
Nothing here narrows that: the comparison is carried out in `Type (max w v a)` and the
vanishing is transported back along `uliftPresheaf`, which is additive, faithful and
preserves homology, so `IsZero` is reflected.  The alternative of extracting
`UnivLE.{w, max v a}` from the assumed coproducts is possible but would force the whole
comparison in `IntegralCechComplex` to be reindexed through `Shrink`.

The only hypothesis of `Stacks.CechSite.integralCechComplex_homology_isZero` beyond the existence
of the fibre products is the existence of `w`-indexed coproducts of abelian presheaves in the
coefficient universe, which is what the integral Čech complex needs to be defined at all.
That coproduct is not known to be computed pointwise, since `AddCommGrpCat.{max v a}` need
not have `w`-indexed coproducts; `uliftPresheaf` nevertheless preserves it, because
evaluation at an object of `C` is a left adjoint (`CategoryTheory.evaluationAdjunctionLeft`,
whose hypothesis is products indexed by the hom types of `C`, available in
`AddCommGrpCat.{max v a}`) and `AddCommGrpCat.uliftFunctor` preserves colimits of arbitrary
size.

## References

* [The Stacks Project, Tag 03AT](https://stacks.math.columbia.edu/tag/03AT)
-/

@[expose] public section

universe w v u a m

open CategoryTheory CategoryTheory.Limits Opposite

namespace AddCommGrpCat

/-- Universe lifting commutes with the free abelian group functor: the universe lift of the
free abelian group on a type is the free abelian group on the lifted type. -/
noncomputable def freeCompUliftFunctorIso :
    AddCommGrpCat.free.{m} ⋙ AddCommGrpCat.uliftFunctor.{w, m} ≅
      CategoryTheory.uliftFunctor.{w, m} ⋙ AddCommGrpCat.free.{max w m} :=
  NatIso.ofComponents
    (fun α ↦ ((AddEquiv.ulift (α := FreeAbelianGroup α)).trans
      (FreeAbelianGroup.equivOfEquiv (Equiv.ulift.{w, m}).symm)).toAddCommGrpIso)
    (fun {α _} f ↦ by
      ext x
      exact (FreeAbelianGroup.map_comp_apply (f := (ConcreteCategory.hom f))
          (g := ULift.up.{w, m}) x.down).symm.trans
        (FreeAbelianGroup.map_comp_apply (f := ULift.up.{w, m})
          (g := fun y : ULift.{w, m} α ↦ ULift.up ((ConcreteCategory.hom f) y.down)) x.down))

end AddCommGrpCat

namespace CategoryTheory


namespace Limits.FormalCoproduct

variable {C : Type*} [Category* C] {A : Type*} [Category* A] {B : Type*} [Category* B]
  [HasCoproducts.{w} A] [HasCoproducts.{w} B] (F : C ⥤ A) (G : A ⥤ B)
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) G]

omit [∀ J : Type w, PreservesColimitsOfShape (Discrete J) G] in
/-- The coproduct comparison maps for a functor `G` are compatible with the reindexing maps
between the coproducts attached to formal coproducts. -/
lemma desc_comp_sigmaComparison {U U' : FormalCoproduct.{w} C} (k : U ⟶ U')
    [∀ J : Type w, PreservesColimitsOfShape (Discrete J) G] :
    (Sigma.desc fun i : U.I ↦ G.map (F.map (k.φ i)) ≫
          Sigma.ι (fun j : U'.I ↦ G.obj (F.obj (U'.obj j))) (k.f i)) ≫
        sigmaComparison G (fun j : U'.I ↦ F.obj (U'.obj j)) =
      sigmaComparison G (fun i : U.I ↦ F.obj (U.obj i)) ≫
        G.map (Sigma.desc fun i : U.I ↦ F.map (k.φ i) ≫
          Sigma.ι (fun j : U'.I ↦ F.obj (U'.obj j)) (k.f i)) := by
  refine Sigma.hom_ext _ _ (fun i ↦ ?_)
  rw [Sigma.ι_desc_assoc, Category.assoc, ι_comp_sigmaComparison,
    ι_comp_sigmaComparison_assoc, ← G.map_comp, ← G.map_comp, Sigma.ι_desc]

/-- A functor preserving `w`-indexed coproducts commutes with the extension of a functor to
the category of formal coproducts. -/
noncomputable def evalCompIso :
    (FormalCoproduct.eval C B).obj (F ⋙ G) ≅ (FormalCoproduct.eval C A).obj F ⋙ G :=
  NatIso.ofComponents
    (fun U : FormalCoproduct.{w} C ↦
      (PreservesCoproduct.iso G (fun i : U.I ↦ F.obj (U.obj i))).symm)
    (fun {_ _} k ↦ desc_comp_sigmaComparison F G k)

end Limits.FormalCoproduct

end CategoryTheory

namespace Stacks.IntegralCech

variable {C : Type u} [Category.{v} C]

/-- Lift the coefficient universe of a presheaf of abelian groups. -/
noncomputable abbrev uliftPresheaf :
    (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{max w v a}) :=
  (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{max v a} AddCommGrpCat.{max w v a}).obj
    AddCommGrpCat.uliftFunctor.{w, max v a}

/-- Lifting the coefficient universe preserves `w`-indexed coproducts of abelian presheaves.
These coproducts are not known to be computed pointwise -- `AddCommGrpCat.{max v a}` need not
have them -- so this is proved from the fact that evaluation at an object of `C` is a left
adjoint. -/
instance preservesColimitsOfShape_uliftPresheaf (J : Type w) :
    PreservesColimitsOfShape (Discrete J) (uliftPresheaf.{w, v, u, a} (C := C)) :=
  ⟨fun {_} ↦ ⟨fun c {hc} ↦ ⟨by
    refine evaluationJointlyReflectsColimits _ (fun V ↦ ?_)
    let _ : PreservesColimitsOfShape (Discrete J)
        ((evaluation Cᵒᵖ AddCommGrpCat.{max v a}).obj V) :=
      (Adjunction.leftAdjoint_preservesColimits
        (evaluationAdjunctionLeft AddCommGrpCat.{max v a} V)).preservesColimitsOfShape
    change IsColimit (((evaluation Cᵒᵖ AddCommGrpCat.{max v a}).obj V ⋙
      AddCommGrpCat.uliftFunctor.{w, max v a}).mapCocone c)
    exact isColimitOfPreserves _ hc⟩⟩⟩

/-- The functor of free abelian groups on types, composed with the two universe lifts needed
to compare the coefficient universe of the integral Čech complex with the universe of the
presheaves of sets realizing a formal coproduct. -/
noncomputable def uliftFreeChainIso :
    CategoryTheory.uliftFunctor.{a, v} ⋙ AddCommGrpCat.free.{max v a} ⋙
        AddCommGrpCat.uliftFunctor.{w, max v a} ≅
      CategoryTheory.uliftFunctor.{max w a, v} ⋙ AddCommGrpCat.free.{max w v a} :=
  Functor.isoWhiskerLeft CategoryTheory.uliftFunctor.{a, v}
      AddCommGrpCat.freeCompUliftFunctorIso.{w, max v a} ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight CategoryTheory.uliftFunctorCompIso.{a, w, v}
        AddCommGrpCat.free.{max w v a}

/-- Lifting the coefficients of the free abelian representable presheaf gives the free
abelian presheaf on the further lifted representable presheaf. -/
noncomputable def freeAbelianYonedaCompUliftPresheafIso :
    Stacks.CechSite.freeAbelianYoneda.{v, u, a} (C := C) ⋙ uliftPresheaf.{w, v, u, a} ≅
      uliftYoneda.{max w a} ⋙ Presheaf.freeAbelian.{max w v a} :=
  Functor.isoWhiskerLeft yoneda
    ((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{max w v a}).mapIso
      uliftFreeChainIso.{w, v, a})

variable {X : C}

/-- The inclusion of a summand into the realization of a formal coproduct as a presheaf of
sets is compatible with the maps induced by morphisms of formal coproducts. -/
lemma sigmaPresheafInj_comp_typeRealization_map {U U' : FormalCoproduct.{w} (Over X)}
    (k : U ⟶ U') (i : U.I) :
    sigmaPresheafInj (fun j : U.I ↦ uliftYoneda.{max w a}.obj (U.obj j).left) i ≫
        typeRealization.{w, v, u, a}.map k =
      uliftYoneda.{max w a}.map (k.φ i).left ≫
        sigmaPresheafInj (fun j : U'.I ↦ uliftYoneda.{max w a}.obj (U'.obj j).left) (k.f i) :=
  NatTrans.ext (funext (fun _ ↦ rfl))

/-- The realization of a formal coproduct of objects over `X` as a presheaf of sets is a
coproduct of the lifted representable presheaves of its members. -/
noncomputable def typeRealizationIsoApp (U : FormalCoproduct.{w} (Over X)) :
    (∐ fun i : U.I ↦ uliftYoneda.{max w a}.obj (U.obj i).left) ≅
      typeRealization.{w, v, u, a}.obj U :=
  IsColimit.coconePointUniqueUpToIso
    (coproductIsCoproduct (fun i : U.I ↦ uliftYoneda.{max w a}.obj (U.obj i).left))
    (isColimitSigmaPresheafCofan (fun i : U.I ↦ uliftYoneda.{max w a}.obj (U.obj i).left))

/-- The `i`-th coproduct inclusion followed by `typeRealizationIsoApp U` is the `i`-th inclusion
`sigmaPresheafInj` into the realization of `U`. -/
@[reassoc]
lemma ι_comp_typeRealizationIsoApp_hom (U : FormalCoproduct.{w} (Over X)) (i : U.I) :
    Sigma.ι (fun j : U.I ↦ uliftYoneda.{max w a}.obj (U.obj j).left) i ≫
        (typeRealizationIsoApp.{w, v, u, a} U).hom =
      sigmaPresheafInj (fun j : U.I ↦ uliftYoneda.{max w a}.obj (U.obj j).left) i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ (⟨i⟩ : Discrete U.I)

/-- The isomorphisms `typeRealizationIsoApp` are natural in the formal coproduct: they intertwine
the map of coproducts induced by `k : U ⟶ U'` with `typeRealization.map k`. -/
lemma desc_comp_typeRealizationIsoApp_hom {U U' : FormalCoproduct.{w} (Over X)} (k : U ⟶ U') :
    (Sigma.desc fun i : U.I ↦ uliftYoneda.{max w a}.map (k.φ i).left ≫
          Sigma.ι (fun j : U'.I ↦ uliftYoneda.{max w a}.obj (U'.obj j).left) (k.f i)) ≫
        (typeRealizationIsoApp.{w, v, u, a} U').hom =
      (typeRealizationIsoApp.{w, v, u, a} U).hom ≫ typeRealization.{w, v, u, a}.map k := by
  refine Sigma.hom_ext _ _ (fun i ↦ ?_)
  rw [Sigma.ι_desc_assoc, Category.assoc, ι_comp_typeRealizationIsoApp_hom,
    ι_comp_typeRealizationIsoApp_hom_assoc]
  exact (sigmaPresheafInj_comp_typeRealization_map k i).symm

/-- The realization of a formal coproduct of objects over `X` as a presheaf of sets is the
coproduct of the lifted representable presheaves of its members. -/
noncomputable def typeRealizationIso :
    (FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ Type (max w v a))).obj
        (Over.forget X ⋙ uliftYoneda.{max w a}) ≅ typeRealization.{w, v, u, a} :=
  NatIso.ofComponents typeRealizationIsoApp.{w, v, u, a}
    (fun {_ _} k ↦ desc_comp_typeRealizationIsoApp_hom.{w, v, u, a} k)

/-- A presheaf of abelian groups whose coefficient lift is zero is zero. -/
lemma isZero_of_isZero_uliftPresheaf {Z : Cᵒᵖ ⥤ AddCommGrpCat.{max v a}}
    (h : IsZero (uliftPresheaf.{w, v, u, a}.obj Z)) : IsZero Z := by
  rw [IsZero.iff_id_eq_zero]
  refine uliftPresheaf.{w, v, u, a}.map_injective ?_
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).1 h

/-- Lifting the coefficient universe commutes with taking homology. -/
noncomputable def uliftPresheafHomologyIso
    (K : ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max v a}) ℕ) (n : ℕ) :
    ((uliftPresheaf.{w, v, u, a}.mapHomologicalComplex _).obj K).homology n ≅
      uliftPresheaf.{w, v, u, a}.obj (K.homology n) :=
  ShortComplex.mapHomologyIso (K.sc n) uliftPresheaf.{w, v, u, a}

variable (E : PreZeroHypercover.{w} X) [HasCoproducts.{w} (Cᵒᵖ ⥤ AddCommGrpCat.{max v a})]

/-- Lifting the coefficients of the integral realization of a formal coproduct of objects
over `X` gives the free abelian presheaf on its realization as a presheaf of sets. -/
noncomputable def integralCechRealizationCompUliftPresheafIso :
    Stacks.CechSite.integralCechRealization.{w, v, u, a} (X := X) ⋙
        uliftPresheaf.{w, v, u, a} ≅
      typeRealization.{w, v, u, a} (X := X) ⋙ Presheaf.freeAbelian.{max w v a} :=
  (FormalCoproduct.evalCompIso (Over.forget X ⋙ Stacks.CechSite.freeAbelianYoneda.{v, u, a})
      uliftPresheaf.{w, v, u, a}).symm ≪≫
    (FormalCoproduct.eval (Over X) (Cᵒᵖ ⥤ AddCommGrpCat.{max w v a})).mapIso
      (Functor.isoWhiskerLeft (Over.forget X)
        freeAbelianYonedaCompUliftPresheafIso.{w, v, u, a}) ≪≫
    FormalCoproduct.evalCompIso (Over.forget X ⋙ uliftYoneda.{max w a})
      Presheaf.freeAbelian.{max w v a} ≪≫
    Functor.isoWhiskerRight typeRealizationIso.{w, v, u, a} Presheaf.freeAbelian.{max w v a}

variable [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun p ↦ Over.mk (E.f (i p)))]

/-- The coefficient lift of the integral Čech complex of `E` is the free abelian presheaf
complex of the Čech nerve of the morphism of presheaves of sets induced by `E`. -/
noncomputable def uliftIntegralCechComplexIso :
    (uliftPresheaf.{w, v, u, a}.mapHomologicalComplex _).obj
        (Stacks.CechSite.integralCechComplex.{w, v, u, a} E) ≅
      (AlgebraicTopology.alternatingFaceMapComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max w v a})).obj
        ((Arrow.mk (cechArrow.{w, v, u, a} E)).cechNerve ⋙
          Presheaf.freeAbelian.{max w v a}) :=
  (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      uliftPresheaf.{w, v, u, a}).app
        (Stacks.CechSite.integralCechSimplicialObject.{w, v, u, a} E) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex (Cᵒᵖ ⥤ AddCommGrpCat.{max w v a})).mapIso
      (Functor.isoWhiskerLeft (Stacks.CechSite.cechSimplicialObject E)
          integralCechRealizationCompUliftPresheafIso.{w, v, u, a} ≪≫
        Functor.isoWhiskerRight (cechSimplicialIso.{w, v, u, a} E)
          Presheaf.freeAbelian.{max w v a})

end Stacks.IntegralCech
