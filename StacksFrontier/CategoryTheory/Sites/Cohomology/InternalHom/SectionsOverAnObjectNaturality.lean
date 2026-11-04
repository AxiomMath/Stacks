module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOverAnObjectModelIndependence

/-!
# Tag 08JA over an object of the site does not depend on the chosen models

Let `(C, O)` be a ringed site and `U` an object of `C`.  The degree-zero identification
`H⁰(U, RSheafHom(L, M)) = Hom_{D(O|_U)}(L|_U, M|_U)` of Tag 08JA,
`AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv`, is **natural in both variables for
arbitrary morphisms of `D(O)`**, and so does not depend on the K-flat and K-injective models
chosen in its construction.

The implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects` record
this statement as absent; the global counterpart is
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality`, and the argument
here is that one with the two representing isomorphisms replaced by their restrictions to the
slice over `U`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_naturality_homologyZero`: **Tag 08JA
  over an object of the site is natural in both variables.**

## Implementation notes

*Why this is a separate module.* The ingredients are collected in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsOverAnObjectModelIndependence`,
whose definitions are `@[expose]`; elaborating this proof alongside them exhausts the
elaborator's budget, exactly as the global proof does alongside its own ingredients.

*Why the two unfoldings are composed rather than rewritten.* `rw` with
`AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_apply_of_isKInjective` has to build a
motive over the whole goal, and the goal mentions the identification at both pairs of objects
together with the slice instances; that search is what overruns the budget. Composing the two
unfoldings with `Eq.trans` and `congrArg` instead gives the same proof in a few seconds.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

/-- **Tag 08JA over an object of the site is natural in both variables for arbitrary morphisms
of `D(O)`** — equivalently, the degree-zero identification
`H⁰(U, RSheafHom(L, M)) = Hom_{D(O|_U)}(L|_U, M|_U)` does not depend on the chosen models.  For
`φ : L' ⟶ L` and `ψ : M ⟶ M'` the morphism induced on `RSheafHom` carries the identification to
precomposition with `φ|_U` and postcomposition with `ψ|_U`.

The argument is the one
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality` makes globally,
with the two representing isomorphisms replaced by their restrictions
`AlgebraicGeometry.RingedSite.restrictModelIso`: the covariant variable moves by a morphism of
complexes because the chosen K-injective model is K-injective, the contravariant variable moves
because the two chosen K-flat models are dominated by one K-flat complex, and
`AlgebraicGeometry.RingedSite.restrictModelIso_hom_naturality` transports the two defining
equations to the slice over `U`. -/
theorem derivedSheafHomSectionsEquiv_naturality_homologyZero
    {L L' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : L' ⟶ L) (ψ : M ⟶ M')
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomSectionsEquiv X U L' M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (((derivedSheafHomBifunctor X).map φ.op).app M ≫
              ((derivedSheafHomBifunctor X).obj (op L')).map ψ)) ξ) =
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map φ ≫
        derivedSheafHomSectionsEquiv X U L M ξ ≫
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map ψ := by
  obtain ⟨m, hm⟩ := exists_Q_map_eq_of_isKInjective X
    ((kInjectiveModelIso X M).hom ≫ ψ ≫ (kInjectiveModelIso X M').inv)
  obtain ⟨R, hR, u, v, hu, huv⟩ := exists_kFlat_common_refinement X
    ((kFlatModelIso X L').hom ≫ φ ≫ (kFlatModelIso X L).inv)
  have : ((sheafHomComplex X (kFlatModel X L) (kInjectiveModel X M)).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X _ _ (isKFlat_kFlatModel X L)
  have : ((sheafHomComplex X (kFlatModel X L') (kInjectiveModel X M')).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X _ _ (isKFlat_kFlatModel X L')
  have : ((sheafHomComplex X R (kInjectiveModel X M')).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X _ _ hR
  let : IsIso (DerivedCategory.Q.map (restrictComplexMap X U u)) :=
    isIso_Q_map_restrictComplexMap X U u hu
  have hmU : DerivedCategory.Q.map (restrictComplexMap X U m) =
      (restrictModelIso X U (kInjectiveModelIso X M)).hom ≫
        (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map ψ ≫
          (restrictModelIso X U (kInjectiveModelIso X M')).inv := by
    have h := restrictModelIso_hom_naturality X U m (kInjectiveModelIso X M)
      (kInjectiveModelIso X M')
    rw [hm] at h
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have huU : DerivedCategory.Q.map (restrictComplexMap X U u) ≫
      (restrictModelIso X U (kFlatModelIso X L')).hom ≫
        (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map φ ≫
          (restrictModelIso X U (kFlatModelIso X L)).inv =
      DerivedCategory.Q.map (restrictComplexMap X U v) := by
    have hU := restrictModelIso_hom_naturality X U u (Iso.refl (DerivedCategory.Q.obj R))
      (kFlatModelIso X L')
    have hV := restrictModelIso_hom_naturality X U v (Iso.refl (DerivedCategory.Q.obj R))
      (kFlatModelIso X L)
    have hvv : DerivedCategory.Q.map v ≫ (kFlatModelIso X L).hom =
        (DerivedCategory.Q.map u ≫ (kFlatModelIso X L').hom) ≫ φ := by
      rw [← huv]; simp
    simp only [Iso.refl_inv, Category.id_comp] at hU hV
    have hcomb : DerivedCategory.Q.map (restrictComplexMap X U v) ≫
        (restrictModelIso X U (kFlatModelIso X L)).hom =
        DerivedCategory.Q.map (restrictComplexMap X U u) ≫
          (restrictModelIso X U (kFlatModelIso X L')).hom ≫
            (SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map φ := by
      rw [hV, hvv, Functor.map_comp, ← Category.assoc, ← hU, Category.assoc]
    rw [← Category.assoc, ← Category.assoc, Iso.comp_inv_eq, hcomb, Category.assoc]
  have hn : DerivedCategory.Q.map (restrictComplexMap X U (𝟙 (kInjectiveModel X M'))) =
      𝟙 _ := by
    simp
  have hzeta := transport_arg_eq_sections X U φ ψ u v m hm huv ξ
  have hI := derivedSheafHomSectionsEquivOfKInjectiveHom_naturality_of_isKInjective X U v m
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
        (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
          (kInjectiveModelIso X M)).hom) ξ)
  have hII := derivedSheafHomSectionsEquivOfKInjectiveHom_naturality_of_isKInjective X U u
    (𝟙 (kInjectiveModel X M'))
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L')
            (kInjectiveModelIso X M')).hom)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
          (((derivedSheafHomBifunctor X).map φ.op).app M ≫
            ((derivedSheafHomBifunctor X).obj (op L')).map ψ)) ξ))
  have hcomb := hI.symm.trans ((congrArg
    (fun z => derivedSheafHomSectionsEquivOfKInjectiveHom X U R
      (kInjectiveModel X M') z) hzeta).trans hII)
  refine (derivedSheafHomSectionsEquiv_apply_of_isKInjective X U L' M' _).trans
    ((?_ : _ = _).trans (congrArg
      (fun z => (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map φ ≫ z ≫
        (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map ψ)
      (derivedSheafHomSectionsEquiv_apply_of_isKInjective X U L M ξ).symm))
  exact conj_of_refinement_of_category _ _ _ _ _ _ _ _ _ _ hn huU hmU _ _ hcomb

/-- **Tag 08JA over an object of the site is natural in the covariant variable.**
`AlgebraicGeometry.RingedSite.derivedSheafHomSectionsEquiv_naturality_homologyZero` with the
identity in the contravariant variable. -/
theorem derivedSheafHomSectionsEquiv_naturality_target
    {L M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (ψ : M ⟶ M')
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomSectionsEquiv X U L M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((Stacks.Cohomology.Localization.derivedSectionsOverObject X U).map
            (((derivedSheafHomBifunctor X).obj (op L)).map ψ)) ξ) =
      derivedSheafHomSectionsEquiv X U L M ξ ≫
        (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          U).mapDerivedCategory.map ψ := by
  have h := derivedSheafHomSectionsEquiv_naturality_homologyZero X U (𝟙 L) ψ ξ
  simpa only [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] using h

end AlgebraicGeometry.RingedSite

end
