module

public import StacksFrontier.Homology.Tor.BaseChangeIndependence.ComparisonEquations
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunctionUnit
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsComp

/-!
# The underived base-change comparison on cochain complexes

The underived base-change comparison of Stacks 065Z, carried along
`CategoryTheory.NatTrans.mapHomologicalComplex` to cochain complexes, is the composite of a unit,
the canonical merge of the two extensions of scalars and a counit of cochain complexes.

## Main results

* `RingTheory.TorIndependence.derivedBaseChangeComparison_fst_mapHomologicalComplex_app`: the
  degreewise comparison as a unit, a merge and a counit of cochain complexes.

## Implementation notes

The two merges are spelled with `CategoryTheory.Functor.mapHomologicalComplexCompIso` of
`ModuleCat.extendScalarsComp` read backwards rather than with
`CategoryTheory.NatIso.mapHomologicalComplex`; the two are the same term, but the first is the
spelling `StacksDraft.DerivedExtensionScalarsComp.extensionScalarsComplexCompIso` is built from.

## References

* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open scoped TensorProduct ChangeOfRings

namespace RingTheory.TorIndependence

universe u

/-- The transport of degreewise extension of scalars along an equation of ring homomorphisms,
read in one degree. -/
private theorem extendScalars_mapHC_eqToHom_f {R A' : Type u} [CommRing R] [CommRing A']
    {φ ψ : R →+* A'} (hφ : φ = ψ) (D : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (eqToHom (congrArg (fun χ : R →+* A' =>
        ((ModuleCat.extendScalars.{u, u, u} χ).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj D) hφ)).f n =
      eqToHom (congrArg (fun χ : R →+* A' =>
        (ModuleCat.extendScalars.{u, u, u} χ).obj (D.X n)) hφ) := by
  subst hφ; rfl

/-- The underived comparison of Stacks 065Z, carried along
`CategoryTheory.NatTrans.mapHomologicalComplex` to cochain complexes, is the unit of the adjunction
induced on cochain complexes by extension–restriction along `R' → A'`, then restriction of scalars
along `R' → A'` of the degreewise merge of the two extensions of scalars (the composition
isomorphism of `ModuleCat.extendScalarsComp` for `g` and `i` read backwards, the transport along
the square and the composition isomorphism for `f` and `h`), followed by degreewise extension of
scalars along `A → A'` of the degreewise counit for `R → A`. -/
theorem derivedBaseChangeComparison_fst_mapHomologicalComplex_app
    {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
    [HasDerivedCategory (ModuleCat.{u} R')] [HasDerivedCategory (ModuleCat.{u} A')]
    (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    [(ModuleCat.extendScalars.{u, u, u} g).IsLeftAdjoint]
    [(ModuleCat.extendScalars.{u, u, u} h).IsLeftAdjoint]
    (sq : h.comp f = i.comp g)
    (L_g : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R'))
    (L_h : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A'))
    (alpha_g : DerivedCategory.Q (C := ModuleCat.{u} R) ⋙ L_g ⟶
      (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    (alpha_h : DerivedCategory.Q (C := ModuleCat.{u} A) ⋙ L_h ⟶
      (ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [L_g.IsLeftDerivedFunctor alpha_g
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))]
    [L_h.IsLeftDerivedFunctor alpha_h
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    (C : CochainComplex (ModuleCat.{u} A) ℤ) :
    (NatTrans.mapHomologicalComplex (derivedBaseChangeComparison.{u, u, u, u, u} f g h i sq
          L_g L_h alpha_g alpha_h).1 (ComplexShape.up ℤ)).app C =
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} i).mapHomologicalComplex
            (ComplexShape.up ℤ)).unit.app
          (((ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
            (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj C)) ≫
        ((ModuleCat.restrictScalars.{u} i).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp g i).symm
                    (ComplexShape.up ℤ)).hom.app
                  (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj C) ≫
                eqToHom (congrArg (fun φ : R →+* A' =>
                    ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj
                      (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj C)) sq.symm) ≫
                  (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f h).symm
                      (ComplexShape.up ℤ)).inv.app
                    (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex
                      (ComplexShape.up ℤ)).obj C)) ≫
            ((ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex
                (ComplexShape.up ℤ)).map
              (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
                (ComplexShape.up ℤ)).counit.app C)) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Adjunction.mapHomologicalComplex,
    Adjunction.mkOfUnitCounit_unit, Adjunction.mkOfUnitCounit_counit, Iso.symm_hom, Iso.symm_inv,
    Functor.mapHomologicalComplex_obj_X, extendScalars_mapHC_eqToHom_f sq.symm]
  exact (derivedBaseChangeComparison_fst_app_eq_unit_comp_counit_extendScalarsComp.{u}
    f g h i sq L_g L_h alpha_g alpha_h (C.X n)).symm

end RingTheory.TorIndependence

end
