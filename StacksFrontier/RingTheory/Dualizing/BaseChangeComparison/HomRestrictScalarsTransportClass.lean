module

public import StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionTransportPrefix
public import StacksFrontier.Homology.HomComplex.RHom.ScalarTransportReconciliation
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorCovariantKFlatLift
import all StacksFrontier.Homology.HomComplex.RHom.ScalarRestrictionComponent

/-!
# The transported restriction comparison of [stacks 0E1W] at a class

This file values the comparison `δ` of [stacks 0E1W], followed by the counit of the scalar lift
over `R`, at the class of a cochain complex: with a morphism `g` in front, with the object of
`D(ULift A)` presented by a morphism `ψ` to the class of a cochain complex `Z`, and with the
factorization of derived restriction along the scalar lift `f'` of the ring map as the trailing
factor, the shape in which the factor `p` of
`Dualizing.tensorBaseChangeMor_eq_iff_scalarLiftEvaluation` ends. The component formula
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q` for `δ` is the input.

The result is a composite whose only factor over the lift of `R` is `DerivedCategory.Q` of an
explicit chain map, `Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison`: the two
evident comparisons of restriction functors, lifted, and the inverse unit of the equivalence of
complexes that both scalar lifts localize. Everything before it is `E.functor` of a morphism of
`D(R)` followed by the scalar-lift presentation `Stacks.DerivedHom.BaseChange.scalarLiftQObjIso`.

Nothing is registered and no caveat is lifted. Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison` -- the chain map the
  bookkeeping collapses to: the two comparisons of restriction functors, lifted, then the inverse
  unit of the equivalence of complexes.
* `Stacks.DerivedHom.BaseChange.functor_map_scalarEquivalenceInverseFactors_inv_comp_counit` --
  the inverse factorization of the scalar lift over `R`, followed by the counit of that lift at a
  class: the scalar-lift presentation of the class and the localized inverse unit.
* `Stacks.DerivedHom.BaseChange.scalarEquivalence_functor_map_Q_map_comp_scalarLiftQObjIso` --
  naturality of the scalar-lift presentation.
* `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q_comp_counit` -- the comparison at a
  class, the counit and the factorization of derived restriction along `f'`, as the scalar-lift
  presentation followed by one localized chain map.
* `Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_comp_counit_comp_eq` -- the same at an
  arbitrary object presented by a morphism to a class.

## Implementation notes

The two reassociations the chain needs are performed by stating the abstract steps with the
associativity the next step consumes: the naturality step ends in
`(g ≫ U.map (S.inverse.map ψ)) ≫ δ.hom.app _`, which is the left-hand side of the valuation at a
class, and the valuation itself peels its two trailing factors through
`Stacks.DerivedHom.BaseChange.map_comp_comp_eq_of_comp_eq`, a two-line fact about a functor whose
hypothesis is the identity being peeled.  No rewriting happens inside a composite of six
comparison components.

`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q` and
`Stacks.DerivedHom.BaseChange.scalarLiftQObjIso` spell the same objects through `Functor.comp` and
through nested `Functor.obj`, so the instantiation of the naturality lemma carries a type
ascription pinning the nested spelling; without it the rewrite reports that it cannot find a
pattern that is printed verbatim.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open Stacks.DerivedHom.ScalarTransportedInternalHom

attribute [local instance] HasDerivedCategory.standard

universe u v uR uA uM u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace Stacks.DerivedHom.BaseChange

/-- **Peeling a trailing factor off a functor applied to a composite.**  If the image of `s`
followed by `c` is `r`, then the image of `h₀ ≫ s` followed by `c` is the image of `h₀` followed by
`r`. -/
private theorem map_comp_comp_eq_of_comp_eq {C : Type u₁} {C' : Type u₃} [Category.{v₁} C]
    [Category.{v₃} C'] (F : C ⥤ C') {X Y Z : C} (h₀ : X ⟶ Y) (s : Y ⟶ Z) {W : C'}
    (c : F.obj Z ⟶ W) (r : F.obj Y ⟶ W) (hr : F.map s ≫ c = r) :
    F.map (h₀ ≫ s) ≫ c = F.map h₀ ≫ r := by
  rw [← hr, CategoryTheory.Functor.map_comp, Category.assoc]

/-- **An inverse presentation of the target absorbed into the counit of an equivalence.**  For
`e : P ≅ P'` and `h` landing in the inverse image of `P'`, the image of `h` followed by the inverse
image of `e.inv`, then the counit at `P` and `e.hom`, is the image of `h` followed by the counit at
`P'`. -/
private theorem functor_map_comp_inverse_map_inv_comp_counit {C : Type u₁} {C' : Type u₃}
    [Category.{v₁} C] [Category.{v₃} C'] (E : C ≌ C') {X : C} {P P' : C'} (e : P ≅ P')
    (h : X ⟶ E.inverse.obj P') :
    E.functor.map (h ≫ E.inverse.map e.inv) ≫ E.counitIso.hom.app P ≫ e.hom =
      E.functor.map h ≫ E.counitIso.hom.app P' := by
  have hn : E.functor.map (E.inverse.map e.inv) ≫ E.counitIso.hom.app P =
      E.counitIso.hom.app P' ≫ e.inv := E.counitIso.hom.naturality e.inv
  rw [CategoryTheory.Functor.map_comp, Category.assoc,
    ← Category.assoc (E.functor.map (E.inverse.map e.inv)), hn, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- **A comparison at an object moved to a class, with a tail.**  Over variable categories: a
comparison `δ` at `Y`, followed by the counit of `E`, the image under `V` of a morphism
`ψ : Y ⟶ Y₀` and any further morphism, is the same with `ψ` restricted into the prefix and `δ`
read at `Y₀`. -/
private theorem functor_map_comp_delta_hom_app_comp_counit_comp
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    (E : C ≌ C') (S : D ≌ D') (U : D ⥤ C) (V : D' ⥤ C')
    (δ : S.inverse ⋙ U ≅ V ⋙ E.inverse)
    {X : C} {Y Y₀ : D'} {P : C'} (g : X ⟶ U.obj (S.inverse.obj Y)) (ψ : Y ⟶ Y₀)
    (p : V.obj Y₀ ⟶ P) :
    E.functor.map (g ≫ δ.hom.app Y) ≫ E.counitIso.hom.app (V.obj Y) ≫ V.map ψ ≫ p =
      E.functor.map ((g ≫ U.map (S.inverse.map ψ)) ≫ δ.hom.app Y₀) ≫
        E.counitIso.hom.app (V.obj Y₀) ≫ p := by
  have h1 : E.counitIso.hom.app (V.obj Y) ≫ V.map ψ =
      E.functor.map (E.inverse.map (V.map ψ)) ≫ E.counitIso.hom.app (V.obj Y₀) :=
    (E.counitIso.hom.naturality (V.map ψ)).symm
  have h2 : U.map (S.inverse.map ψ) ≫ δ.hom.app Y₀ = δ.hom.app Y ≫ E.inverse.map (V.map ψ) :=
    δ.hom.naturality ψ
  have hcore : ∀ {Q : C'} (z : E.functor.obj (E.inverse.obj (V.obj Y₀)) ⟶ Q),
      E.functor.map (δ.hom.app Y) ≫ E.functor.map (E.inverse.map (V.map ψ)) ≫ z =
        E.functor.map (U.map (S.inverse.map ψ)) ≫ E.functor.map (δ.hom.app Y₀) ≫ z := by
    intro Q z
    rw [← Category.assoc, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, h2]
  rw [← Category.assoc (E.counitIso.hom.app (V.obj Y)), h1]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]
  rw [hcore]

/-- **The inverse factorization of the scalar lift, followed by the counit of the lift, at a
class.**

`Stacks.DerivedHom.BaseChange.scalarEquivalenceInverseFactors` read backwards at a cochain complex
`W` of modules over the lifted ring, pushed forward by the lift and followed by the counit of the
lift, is the scalar-lift presentation
`Stacks.DerivedHom.BaseChange.scalarLiftQObjIso` of the restriction of `W` followed by the
localized inverse unit of the equivalence of complexes.

This is
`Stacks.DerivedHom.ScalarTransportedInternalHom.derivedScalarEquivalence_symm_counit_app_Q` with
its leading factor cancelled. -/
public theorem functor_map_scalarEquivalenceInverseFactors_inv_comp_counit (B : Type u)
    [CommRing B] (W : CochainComplex (ModuleCat.{max u v} (ULift.{v} B)) ℤ) :
    (scalarEquivalence.{u, v} B).functor.map
          ((scalarEquivalenceInverseFactors.{u, v} B).inv.app W) ≫
        (scalarEquivalence.{u, v} B).counitIso.hom.app (DerivedCategory.Q.obj W) =
      (scalarLiftQObjIso.{u, v} B (((ModuleCat.restrictScalars.{max u v}
          (ULift.ringEquiv : ULift.{v} B ≃+* B).symm.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj W)).hom ≫
        DerivedCategory.Q.map ((uliftComplexEquivalence.{u, v} B).unitIso.inv.app W) := by
  have hc : (scalarEquivalence.{u, v} B).counitIso.hom.app (DerivedCategory.Q.obj W) =
      (scalarEquivalence.{u, v} B).functor.map
          ((scalarEquivalenceInverseFactors.{u, v} B).hom.app W) ≫
        (scalarLiftQObjIso.{u, v} B (((ModuleCat.restrictScalars.{max u v}
            (ULift.ringEquiv : ULift.{v} B ≃+* B).symm.toRingHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj W)).hom ≫
          DerivedCategory.Q.map ((uliftComplexEquivalence.{u, v} B).unitIso.inv.app W) :=
    (derivedScalarEquivalence_symm_counit_app.{u, v} B _).symm.trans
      (derivedScalarEquivalence_symm_counit_app_Q.{u, v} B W)
  have h1 : (scalarEquivalence.{u, v} B).functor.map
        ((scalarEquivalenceInverseFactors.{u, v} B).inv.app W) ≫
      (scalarEquivalence.{u, v} B).functor.map
        ((scalarEquivalenceInverseFactors.{u, v} B).hom.app W) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [hc, ← Category.assoc, h1, Category.id_comp]

/-- **Naturality of the scalar-lift presentation.**  A localized chain map pushed forward by the
scalar lift, followed by the scalar-lift presentation of its target, is the presentation of its
source followed by the localization of the degreewise restriction of the chain map. -/
public theorem scalarEquivalence_functor_map_Q_map_comp_scalarLiftQObjIso (B : Type u)
    [CommRing B] {Y₁ Y₂ : CochainComplex (ModuleCat.{max u v} B) ℤ} (γ : Y₁ ⟶ Y₂) :
    (scalarEquivalence.{u, v} B).functor.map (DerivedCategory.Q.map γ) ≫
        (scalarLiftQObjIso.{u, v} B Y₂).hom =
      (scalarLiftQObjIso.{u, v} B Y₁).hom ≫
        DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max u v}
          (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map γ) :=
  (ModuleCat.restrictScalars.{max u v}
    (ULift.ringEquiv : ULift.{v} B ≃+* B).toRingHom).mapDerivedCategoryFactors.hom.naturality γ

/-- **The chain map the scalar-lift bookkeeping of [stacks 0E1W] collapses to.**

Restricting a complex of modules over the lift of `A` along the lift of `A`, then along `f`, then
lifting to the lift of `R`, and restricting it along the lifted ring map `f'` are two descriptions
of the same degreewise restriction.  This is the comparison between them: the two evident
comparisons of composites of restriction functors, lifted to the lift of `R`, followed by the
inverse unit of the equivalence of complexes that the scalar lift over `R` localizes. -/
public def scalarRestrictionChainComparison {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    (f : R →+* A) (Z : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) :
    (((ModuleCat.restrictScalars.{max uR uA uM}
          (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((ModuleCat.restrictScalars.{max uR uA uM} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj
        (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z))) ⟶
      ((ModuleCat.restrictScalars.{max uR uA uM}
          (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom.comp f).comp
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z :=
  ((ModuleCat.restrictScalars.{max uR uA uM}
      (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
    (ComplexShape.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso
          (ModuleCat.restrictScalarsComp f
            (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).symm
          (ComplexShape.up ℤ)).hom.app Z ≫
        (Functor.mapHomologicalComplexCompIso
            (ModuleCat.restrictScalarsComp'
              (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).symm.toRingHom
              (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom.comp f).comp
                (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom)
              (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).comp f)
              (RingHom.ext fun _ => rfl)).symm
            (ComplexShape.up ℤ)).inv.app Z) ≫
    (uliftComplexEquivalence.{uR, max uR uA uM} R).unitIso.inv.app
      (((ModuleCat.restrictScalars.{max uR uA uM}
          (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom.comp f).comp
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z)

/-- **The comparison of [stacks 0E1W] at a class, with the counit and the factorization of
derived restriction along the lifted ring map.**

At the class of a cochain complex `Z` of modules over the lift of `A`, the comparison `δ` of
[stacks 0E1W] preceded by any morphism `g`, then the counit of the scalar lift over `R`, then the
factorization of derived restriction along the lifted ring map `f'`, is: `g` followed by the two
leading comparison factors -- the inverse scalar lift over `A` restricted along `f`, and the
factorization of derived restriction along `f` -- pushed forward by the scalar lift over `R`, then
the scalar-lift presentation of the twice-restricted complex, then
`DerivedCategory.Q` of `Stacks.DerivedHom.BaseChange.scalarRestrictionChainComparison`. -/
public theorem scalarRestrictionIso_hom_app_Q_comp_counit {R : Type uR} {A : Type uA}
    [CommRing R] [CommRing A] (f : R →+* A)
    (Z : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    ∀ (X : DerivedCategory (ModuleCat.{max uR uA uM} R))
      (g : X ⟶ (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
        ((scalarEquivalence.{uA, max uR uA uM} A).inverse.obj (DerivedCategory.Q.obj Z))),
    (scalarEquivalence.{uR, max uR uA uM} R).functor.map
          (g ≫ (scalarRestrictionIso.{uR, uA, uM} f).hom.app (DerivedCategory.Q.obj Z)) ≫
        (scalarEquivalence.{uR, max uR uA uM} R).counitIso.hom.app
            ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.obj
              (DerivedCategory.Q.obj Z)) ≫
          (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.hom.app Z =
      ((scalarEquivalence.{uR, max uR uA uM} R).functor.map
            (g ≫ (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
                ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app Z) ≫
              (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategoryFactors.hom.app
                (((ModuleCat.restrictScalars.{max uR uA uM}
                    (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+*
                      A).symm.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) ≫
          (scalarLiftQObjIso.{uR, max uR uA uM} R
              (((ModuleCat.restrictScalars.{max uR uA uM} f).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj
                (((ModuleCat.restrictScalars.{max uR uA uM}
                    (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+*
                      A).symm.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  Z))).hom ≫
            DerivedCategory.Q.map (scalarRestrictionChainComparison.{uR, uA, uM} f Z) :
        (scalarEquivalence.{uR, max uR uA uM} R).functor.obj X ⟶
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj Z) := by
  intro f' X g
  have hbig : g ≫ (scalarRestrictionIso.{uR, uA, uM} f).hom.app (DerivedCategory.Q.obj Z) =
      (((g ≫ (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
                ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app Z) ≫
              ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategoryFactors.hom.app
                (((ModuleCat.restrictScalars.{max uR uA uM} (ULift.ringEquiv : ULift.{max uR uA uM}
                      A ≃+* A).symm.toRingHom).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj Z))) ≫
            DerivedCategory.Q.map (((Functor.mapHomologicalComplexCompIso
                  (ModuleCat.restrictScalarsComp f (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+*
                  A).symm.toRingHom).symm (ComplexShape.up ℤ)).hom.app Z) ≫
                  ((Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsComp'
                  (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).symm.toRingHom f'
                  (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).comp f)
                  (RingHom.ext fun _ => rfl)).symm (ComplexShape.up ℤ)).inv.app Z))) ≫
          ((scalarEquivalenceInverseFactors.{uR, max uR uA uM} R).inv.app
            (((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Z))) ≫
        (scalarEquivalence.{uR, max uR uA uM} R).inverse.map
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.inv.app Z) := by
    rw [scalarRestrictionIso_hom_app_Q.{uR, uA, uM} f Z]
    simp only [Category.assoc, CategoryTheory.Functor.map_comp]
    rfl
  refine (congrArg (fun z => (scalarEquivalence.{uR, max uR uA uM} R).functor.map z ≫
      (scalarEquivalence.{uR, max uR uA uM} R).counitIso.hom.app
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.obj
            (DerivedCategory.Q.obj Z)) ≫
        (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.hom.app Z)
    hbig).trans ?_
  refine (functor_map_comp_inverse_map_inv_comp_counit (scalarEquivalence.{uR, max uR uA uM} R)
    ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.app Z) _).trans ?_
  refine (map_comp_comp_eq_of_comp_eq (scalarEquivalence.{uR, max uR uA uM} R).functor _
    ((scalarEquivalenceInverseFactors.{uR, max uR uA uM} R).inv.app
      (((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z)) _ _
    (functor_map_scalarEquivalenceInverseFactors_inv_comp_counit.{uR, max uR uA uM} R
      (((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
        (ComplexShape.up ℤ)).obj Z))).trans ?_
  refine (map_comp_comp_eq_of_comp_eq (scalarEquivalence.{uR, max uR uA uM} R).functor _
    (DerivedCategory.Q.map (((Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsComp f
          (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).symm (ComplexShape.up
          ℤ)).hom.app Z) ≫ ((Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsComp'
          (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).symm.toRingHom f' (((ULift.ringEquiv :
          ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).comp f) (RingHom.ext fun _ => rfl)).symm
          (ComplexShape.up ℤ)).inv.app Z))) _
    ((scalarLiftQObjIso.{uR, max uR uA uM} R (((ModuleCat.restrictScalars.{max uR uA uM}
          f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (((ModuleCat.restrictScalars.{max uR uA
          uM} (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z))).hom ≫
      DerivedCategory.Q.map (((ModuleCat.restrictScalars.{max uR uA uM}
          (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (((Functor.mapHomologicalComplexCompIso
              (ModuleCat.restrictScalarsComp f (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+*
              A).symm.toRingHom).symm (ComplexShape.up ℤ)).hom.app Z) ≫
              ((Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsComp'
              (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).symm.toRingHom f' (((ULift.ringEquiv
              : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).comp f) (RingHom.ext fun _ =>
              rfl)).symm (ComplexShape.up ℤ)).inv.app Z))) ≫
        DerivedCategory.Q.map ((uliftComplexEquivalence.{uR, max uR uA uM} R).unitIso.inv.app
              (((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex (ComplexShape.up
              ℤ)).obj Z))) ?_).trans ?_
  · rw [← Category.assoc, scalarEquivalence_functor_map_Q_map_comp_scalarLiftQObjIso.{uR,
      max uR uA uM} R ((((Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsComp f
            (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).symm (ComplexShape.up
            ℤ)).hom.app Z) ≫ ((Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsComp'
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).symm.toRingHom f' (((ULift.ringEquiv :
            ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).comp f) (RingHom.ext fun _ => rfl)).symm
            (ComplexShape.up ℤ)).inv.app Z) : (((ModuleCat.restrictScalars.{max uR uA uM}
            f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (((ModuleCat.restrictScalars.{max uR
            uA uM} (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+*
            A).symm.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)) ⟶
            (((ModuleCat.restrictScalars.{max uR uA uM} (ULift.ringEquiv : ULift.{max uR uA uM} R
            ≃+* R).symm.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex (ComplexShape.up
            ℤ)).obj Z)))), Category.assoc]
  · exact congrArg (fun z => (scalarEquivalence.{uR, max uR uA uM} R).functor.map
        (g ≫ (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
            ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app Z) ≫
          ((ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.restrictScalars.{max uR uA uM} (ULift.ringEquiv : ULift.{max uR uA uM} A
                  ≃+* A).symm.toRingHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Z))) ≫
        (scalarLiftQObjIso.{uR, max uR uA uM} R (((ModuleCat.restrictScalars.{max uR uA uM}
              f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (((ModuleCat.restrictScalars.{max uR
              uA uM} (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+*
              A).symm.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z))).hom ≫ z)
      (CategoryTheory.Functor.map_comp DerivedCategory.Q
        (((ModuleCat.restrictScalars.{max uR uA uM}
            (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (((Functor.mapHomologicalComplexCompIso
                (ModuleCat.restrictScalarsComp f (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+*
                A).symm.toRingHom).symm (ComplexShape.up ℤ)).hom.app Z) ≫
                ((Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsComp'
                (ULift.ringEquiv : ULift.{max uR uA uM} R ≃+* R).symm.toRingHom f'
                (((ULift.ringEquiv : ULift.{max uR uA uM} A ≃+* A).symm.toRingHom).comp f)
                (RingHom.ext fun _ => rfl)).symm (ComplexShape.up ℤ)).inv.app Z)))
                ((uliftComplexEquivalence.{uR, max uR uA uM} R).unitIso.inv.app
                (((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
                (ComplexShape.up ℤ)).obj Z))).symm

/-- **The comparison of [stacks 0E1W] at an object presented by a morphism to a class.**

`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_hom_app_Q_comp_counit` at an arbitrary object
`N` of `D(ULift A)`, given a morphism `ψ` from `N` to the class of a cochain complex `Z`, with `ψ`
restricted into the prefix. -/
public theorem scalarRestrictionIso_hom_comp_counit_comp_eq {R : Type uR} {A : Type uA}
    [CommRing R] [CommRing A] (f : R →+* A)
    (Z : CochainComplex (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)) ℤ) :
    let f' : ULift.{max uR uA uM} R →+* ULift.{max uR uA uM} A :=
      (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uA uM} f').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM} f').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uA uM} f').isLeftAdjoint
    ∀ (X : DerivedCategory (ModuleCat.{max uR uA uM} R))
      (N : DerivedCategory (ModuleCat.{max uR uA uM} (ULift.{max uR uA uM} A)))
      (g : X ⟶ (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.obj
        ((scalarEquivalence.{uA, max uR uA uM} A).inverse.obj N))
      (ψ : N ⟶ DerivedCategory.Q.obj Z),
    (scalarEquivalence.{uR, max uR uA uM} R).functor.map
          (g ≫ (scalarRestrictionIso.{uR, uA, uM} f).hom.app N) ≫
        (scalarEquivalence.{uR, max uR uA uM} R).counitIso.hom.app
            ((ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.obj N) ≫
          (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory.map ψ ≫
            (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategoryFactors.hom.app Z =
      ((scalarEquivalence.{uR, max uR uA uM} R).functor.map
            ((g ≫ (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
                  ((scalarEquivalence.{uA, max uR uA uM} A).inverse.map ψ)) ≫
              (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
                  ((scalarEquivalenceInverseFactors.{uA, max uR uA uM} A).hom.app Z) ≫
                (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategoryFactors.hom.app
                  (((ModuleCat.restrictScalars.{max uR uA uM} (ULift.ringEquiv : ULift.{max uR uA
                        uM} A ≃+* A).symm.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                        Z)) ≫
          (scalarLiftQObjIso.{uR, max uR uA uM} R (((ModuleCat.restrictScalars.{max uR uA uM}
                f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (((ModuleCat.restrictScalars.{max
                uR uA uM} (ULift.ringEquiv : ULift.{max uR uA uM} A ≃+*
                A).symm.toRingHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z))).hom ≫
            DerivedCategory.Q.map (scalarRestrictionChainComparison.{uR, uA, uM} f Z) :
        (scalarEquivalence.{uR, max uR uA uM} R).functor.obj X ⟶
          ((ModuleCat.restrictScalars.{max uR uA uM} f').mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q).obj Z) := by
  intro f' X N g ψ
  exact (functor_map_comp_delta_hom_app_comp_counit_comp
      (scalarEquivalence.{uR, max uR uA uM} R) (scalarEquivalence.{uA, max uR uA uM} A)
      (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory
      (ModuleCat.restrictScalars.{max uR uA uM} f').mapDerivedCategory
      (scalarRestrictionIso.{uR, uA, uM} f) g ψ
      ((ModuleCat.restrictScalars.{max uR uA uM}
        f').mapDerivedCategoryFactors.hom.app Z)).trans
    (scalarRestrictionIso_hom_app_Q_comp_counit.{uR, uA, uM} f Z X
      (g ≫ (ModuleCat.restrictScalars.{max uR uA uM} f).mapDerivedCategory.map
        ((scalarEquivalence.{uA, max uR uA uM} A).inverse.map ψ)))

end Stacks.DerivedHom.BaseChange

end
