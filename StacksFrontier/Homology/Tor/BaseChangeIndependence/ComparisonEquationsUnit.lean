module

public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunctionUnit
import all StacksFrontier.Homology.Tor.IndependenceBaseChange

/-!
# The base-change comparison of Stacks 065Z and the units of extension of scalars

`RingTheory.TorIndependence.derivedBaseChangeComparison` compares derived extension of scalars
along the two sides of a commutative square of rings `R → A → A'`, `R → R' → A'`. This file
records its compatibility with the units of the two extension-of-scalars adjunctions.

## Main results

* `RingTheory.TorIndependence.derivedBaseChangeComparison_fst_app_unit` and
  `RingTheory.TorIndependence.derivedBaseChangeComparison_fst_complex_unit`: the underived
  comparison turns the unit of extension of scalars along `R → R'` into the unit of extension of
  scalars along `A → A'`, at a module and degreewise on a complex. Both say that `1 ⊗ m` goes to
  `1 ⊗ m`.
* `RingTheory.TorIndependence.derivedBaseChangeComparison_snd_app_unit`: the compatibility of the
  derived comparison with the two units of derived extension of scalars, at every object of the
  derived category.

## References

* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open scoped TensorProduct ChangeOfRings

namespace RingTheory.TorIndependence

universe uR uA uRp uAp v

attribute [local instance] extendScalarsAdditive
attribute [local instance_reducible] CochainComplex.extendScalarsLarge

variable {R : Type uR} {A : Type uA} {R' : Type uRp} {A' : Type uAp}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R)]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A)]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} R')]
  [HasDerivedCategory (ModuleCat.{max v uR uA uRp uAp} A')]
  (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
  [(ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).IsLeftAdjoint]
  [(ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).IsLeftAdjoint]
  (sq : h.comp f = i.comp g)
  (L_g : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp uAp} R'))
  (L_h : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A'))
  (alpha_g : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} R) ⋙ L_g ⟶
    (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (alpha_h : DerivedCategory.Q (C := ModuleCat.{max v uR uA uRp uAp} A) ⋙ L_h ⟶
    (ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [L_g.IsLeftDerivedFunctor alpha_g
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} R) (ComplexShape.up ℤ))]
  [L_h.IsLeftDerivedFunctor alpha_h
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ))]

/-- The unit `m ↦ 1 ⊗ m` of extension of scalars along `R → R'`, taken at the restriction of `M`
to `R` and followed by the underived base-change comparison, is the unit of extension of scalars
along `A → A'` at `M`, read over `R`. The two readings of `A' ⊗_A M` as an `R`-module, along
`R → R' → A'` and along `R → A → A'`, are identified by the two change-of-rings composition
isomorphisms. -/
theorem derivedBaseChangeComparison_fst_app_unit
    (M : ModuleCat.{max v uR uA uRp uAp} A) :
    (ModuleCat.extendRestrictScalarsAdj.{max v uR uA uAp} g).unit.app
          ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).map
          ((derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
            L_g L_h alpha_g alpha_h).1.app M) =
      (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).map
          ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp} h).unit.app M) ≫
        (ModuleCat.restrictScalarsComp'.{max v uR uA uRp uAp} f h (h.comp f) rfl).inv.app
            ((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).obj M) ≫
          (ModuleCat.restrictScalarsComp'.{max v uR uA uRp uAp} g i (h.comp f) sq).hom.app
            ((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).obj M) := by
  refine ConcreteCategory.hom_ext_iff.mpr fun m => ?_
  simp only [ModuleCat.restrictScalarsComp'_hom_app, ModuleCat.restrictScalarsComp'_inv_app,
    ConcreteCategory.comp_apply, Functor.comp_obj, Functor.id_obj,
    ModuleCat.restrictScalars.map_apply]
  let mA : (M : Type (max v uR uA uRp uAp)) := m
  refine Eq.trans (congrArg (ConcreteCategory.hom
      ((derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
        L_g L_h alpha_g alpha_h).1.app M))
    (ModuleCat.extendRestrictScalarsAdj_unit_app_apply.{max v uR uA uAp} g
      ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).obj M) m)) ?_
  refine Eq.trans (derivedBaseChangeComparison_fst_app_tmul f g h i sq L_g L_h alpha_g alpha_h
    M (1 : R') mA) ?_
  refine Eq.trans (congrArg (fun z : A' => z ⊗ₜ[A,h] mA) (map_one i)) ?_
  refine Eq.symm (Eq.trans (congrArg (ConcreteCategory.hom
      ((ModuleCat.restrictScalarsComp'App f h (h.comp f) rfl
            ((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).obj M)).inv ≫
        (ModuleCat.restrictScalarsComp'App g i (h.comp f) sq
          ((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).obj M)).hom))
    (ModuleCat.extendRestrictScalarsAdj_unit_app_apply.{max v uR uA uRp} h M mA)) ?_)
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom
      (ModuleCat.restrictScalarsComp'App g i (h.comp f) sq
        ((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).obj M)).hom)
    (ModuleCat.restrictScalarsComp'App_inv_apply f h (h.comp f) rfl
      ((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).obj M)
      ((1 : A') ⊗ₜ[A,h] mA))) ?_
  exact ModuleCat.restrictScalarsComp'App_hom_apply g i (h.comp f) sq
    ((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).obj M)
    ((1 : A') ⊗ₜ[A,h] mA)

/-- The unit of extension of scalars along `R → R'`, taken at the restriction of a complex `K`
to `R` and followed by the underived base-change comparison applied degreewise, is the unit of
extension of scalars along `A → A'` at `K`, read over `R` through the composition isomorphisms
of complexes. -/
theorem derivedBaseChangeComparison_fst_complex_unit
    (K : CochainComplex (ModuleCat.{max v uR uA uRp uAp} A) ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uAp} g).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app
          (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex
            (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
              L_g L_h alpha_g alpha_h).1 (ComplexShape.up ℤ)).app K) =
      ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app K) ≫
        (Functor.mapHomologicalComplexCompIso
            (ModuleCat.restrictScalarsComp'.{max v uR uA uRp uAp} f h (h.comp f) rfl).symm
            (ComplexShape.up ℤ)).hom.app
          (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (Functor.mapHomologicalComplexCompIso
            (ModuleCat.restrictScalarsComp'.{max v uR uA uRp uAp} g i (h.comp f) sq).symm
            (ComplexShape.up ℤ)).inv.app
          (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) :=
  HomologicalComplex.hom_ext _ _ fun n =>
    derivedBaseChangeComparison_fst_app_unit f g h i sq L_g L_h alpha_g alpha_h (K.X n)

open CochainComplex.DerivedExtensionScalars in
/-- The unit of derived extension of scalars along `R → R'`, taken at the restriction of `W` to
`R` and followed by the derived comparison restricted along `R → R'`, is the unit of derived
extension of scalars along `A → A'` at `W`, restricted along `R → A`, followed by `rho`. Here
`rho` is a transformation between the two readings of `W ⊗ᴸ_A A'` as an object of `D(R)`, along
`R → R' → A'` and along `R → A → A'`, and `hrho` describes it on the image of the localization
functor through the composition isomorphisms of complexes. -/
theorem derivedBaseChangeComparison_snd_app_unit
    (rho : (ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory ⟶
      (ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory)
    (hrho : ∀ P : CochainComplex (ModuleCat.{max v uR uA uRp uAp} A') ℤ,
      rho.app (DerivedCategory.Q.obj P) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategoryFactors.hom.app
              P) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
              (ModuleCat.restrictScalarsComp'.{max v uR uA uRp uAp} g i (h.comp f) sq).symm
              (ComplexShape.up ℤ)).hom.app P) =
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory.map
            ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapDerivedCategoryFactors.hom.app
              P) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategoryFactors.hom.app
              (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
              (ModuleCat.restrictScalarsComp'.{max v uR uA uRp uAp} f h (h.comp f) rfl).symm
              (ComplexShape.up ℤ)).hom.app P))
    (W : DerivedCategory (ModuleCat.{max v uR uA uRp uAp} A)) :
    (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA uAp} g L_g alpha_g).unit.app
          ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory.obj W) ≫
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory.map
          ((derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
            L_g L_h alpha_g alpha_h).2.1.app W) =
      (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory.map
          ((derivedExtensionScalarsAdjunction.{uA, uAp, max v uR uRp} h L_h alpha_h).unit.app W) ≫
        rho.app (L_h.obj W) := by
  have :=
    CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp.{uA, uAp,
        max v uR uRp} h L_h alpha_h
      ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory)
  refine congr_app (Functor.leftDerived_ext
    (L_h ⋙ ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory))
    ((DerivedCategory.Q.associator L_h
        ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory)).inv ≫
      Functor.whiskerRight alpha_h
        ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory))
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp uAp} A) (ComplexShape.up ℤ))
    ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory)
    (Functor.whiskerLeft ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory)
        (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA uAp} g L_g alpha_g).unit ≫
      Functor.whiskerRight (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
          L_g L_h alpha_g alpha_h).2.1
        ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory))
    (Functor.whiskerRight
          (derivedExtensionScalarsAdjunction.{uA, uAp, max v uR uRp} h L_h alpha_h).unit
        ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory) ≫
      Functor.whiskerLeft L_h rho)
    ?_) W
  ext P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.comp_obj, Functor.comp_map, Functor.id_obj,
    Category.id_comp, Category.assoc]
  rw [← Iso.cancel_iso_hom_right _ _
    ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory.mapIso
        ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapDerivedCategoryFactors.app
          (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P)) ≪≫
      (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso ((Functor.mapHomologicalComplexCompIso
        (ModuleCat.restrictScalarsComp'.{max v uR uA uRp uAp} g i (h.comp f) sq).symm
        (ComplexShape.up ℤ)).app _))]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  have hcounit := congrArg
    ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategory).map
    (derivedBaseChangeComparison_snd_app_comp_counit f g h i sq L_g L_h alpha_g alpha_h P)
  simp only [Functor.map_comp] at hcounit
  rw [reassoc_of% hcounit]
  have hnat :=
    (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA uAp} g L_g alpha_g).unit.naturality
      ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategoryFactors.hom.app P)
  simp only [Functor.id_map, Functor.comp_map] at hnat
  rw [← reassoc_of% hnat,
    reassoc_of% (derivedExtensionScalarsAdjunction_unit_app.{uR, uRp, max v uA uAp} g L_g alpha_g
      (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P))]
  have hFginv :=
    (ModuleCat.restrictScalars.{max v uR uA uRp uAp} g).mapDerivedCategoryFactors.inv.naturality
      (show ((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp uAp} g).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ⟶
          ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} i).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) from
        (NatTrans.mapHomologicalComplex
          (derivedBaseChangeComparison.{uR, uA, uRp, uAp, v} f g h i sq
            L_g L_h alpha_g alpha_h).1 (ComplexShape.up ℤ)).app P)
  simp only [Functor.comp_map] at hFginv
  rw [← reassoc_of% hFginv, Iso.inv_hom_id_app_assoc]
  conv_lhs => rw [← Functor.map_comp, ← Functor.map_comp,
    reassoc_of% (derivedBaseChangeComparison_fst_complex_unit f g h i sq
      L_g L_h alpha_g alpha_h P), Iso.inv_hom_id_app, Category.comp_id]
  have hrhonat := rho.naturality
    (show L_h.obj (DerivedCategory.Q.obj P) ⟶
        DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) from alpha_h.app P)
  simp only [Functor.comp_map] at hrhonat
  rw [← reassoc_of% hrhonat, hrho
    (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P)]
  have hpre :
      (derivedExtensionScalarsAdjunction.{uA, uAp, max v uR uRp} h L_h alpha_h).unit.app
            (DerivedCategory.Q.obj P) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapDerivedCategory.map
            (alpha_h.app P) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapDerivedCategoryFactors.hom.app
            (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) =
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app P) := by
    rw [reassoc_of% (derivedExtensionScalarsAdjunction_unit_app.{uA, uAp, max v uR uRp} h L_h
      alpha_h P), Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hunith := congrArg
    ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategory).map hpre
  simp only [Functor.map_comp] at hunith
  rw [reassoc_of% hunith]
  have hFfhom :=
    (ModuleCat.restrictScalars.{max v uR uA uRp uAp} f).mapDerivedCategoryFactors.hom.naturality
      (show P ⟶ ((ModuleCat.restrictScalars.{max v uR uA uRp uAp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars.{uA, uAp, max v uR uA uRp uAp} h).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) from
        ((ModuleCat.extendRestrictScalarsAdj.{max v uR uA uRp} h).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app P)
  simp only [Functor.comp_map] at hFfhom
  rw [reassoc_of% hFfhom, ← Functor.map_comp]

end RingTheory.TorIndependence

end
