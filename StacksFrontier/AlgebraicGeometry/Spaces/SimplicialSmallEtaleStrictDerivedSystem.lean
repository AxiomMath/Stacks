module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleDegreeTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictDerivedEquivalence

/-!
# The strict system of a derived pullback along an augmentation

Let `X` be a simplicial algebraic space with an augmentation `a : X → Z`, `b` the augmentation on
the total site of the strict components and `K` an object of `D(Z)`. This file shows that `Lb^*K`
is cartesian (Stacks 07TF (4)) for every `K`, and that the transport of a degree-`m` map along the
transitions of the systems of `Lb^*K` and `Lb^*E` is, through the component isomorphisms
`Lb^* ⋙ D(g_n^{-1}) ⋙ L realize_n^* ≅ La_n^*`, the transport along `La_m^* ⋙ LX(φ)^* ≅ La_n^*`.

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.isCartesianDerivedModule_strictAugmentation`.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.derivedPullback_map_strictTransport`.

## References

* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry.RingedToposHom
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

namespace CategoryTheory

/-- Transporting a map along two transitions which a functor carries to composites of
isomorphisms: if `F tK = (bK ≫ xK ≫ θK) ≫ cK⁻¹`, `F tE = (bE ≫ xE ≫ θE) ≫ cE⁻¹` and
`F f = bK ≫ y ≫ bE⁻¹`, then `F (tK⁻¹ ≫ f ≫ tE) = cK ≫ θK⁻¹ ≫ xK⁻¹ ≫ y ≫ xE ≫ θE ≫ cE⁻¹`. -/
theorem Functor.map_inv_comp_comp_eq_of_isos {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A A' B' B : C} (tK : A ⟶ A') [IsIso tK] (f : A ⟶ B) (tE : B ⟶ B')
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : D} (bK : F.obj A ≅ P₁) (xK : P₁ ≅ P₂) (θK : P₂ ≅ P₃)
    (cK : F.obj A' ≅ P₃) (bE : F.obj B ≅ Q₁) (xE : Q₁ ≅ Q₂) (θE : Q₂ ≅ Q₃) (cE : F.obj B' ≅ Q₃)
    (y : P₁ ⟶ Q₁) (hK : F.map tK = (bK.hom ≫ xK.hom ≫ θK.hom) ≫ cK.inv)
    (hE : F.map tE = (bE.hom ≫ xE.hom ≫ θE.hom) ≫ cE.inv) (hf : F.map f = bK.hom ≫ y ≫ bE.inv) :
    F.map (CategoryTheory.inv tK ≫ f ≫ tE) =
      cK.hom ≫ θK.inv ≫ xK.inv ≫ y ≫ xE.hom ≫ θE.hom ≫ cE.inv := by
  have hinv : F.map (CategoryTheory.inv tK) = cK.hom ≫ θK.inv ≫ xK.inv ≫ bK.inv := by
    rw [Functor.map_inv]
    apply IsIso.inv_eq_of_hom_inv_id
    rw [hK]
    simp
  rw [Functor.map_comp, Functor.map_comp, hinv, hE, hf]
  simp

end CategoryTheory

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : SimplicialObject (AlgebraicSpaces B S hS)} {Z : AlgebraicSpaces B S hS}
  (a : X ⟶ (Functor.const _).obj Z)

/-- **`Lb^*K` is cartesian** for every `K` in `D(Z)`: the derived transitions of its strict
system are isomorphisms, being so after the equivalence `L realize_n^*`, by the transition
coherence. -/
theorem isCartesianDerivedModule_strictAugmentation
    (K : @DerivedCategory (spacesEtaleRingedTopos B S hS Z).Modules _ _
      (HasDerivedCategory.standard _)) :
    (strictSituation X).IsCartesianDerivedModule (strictStructureSheaf X)
      ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
        (strictAugmentationRingedToposHom a)).obj K) := by
  intro m n φ
  have h := strictAugmentationDegreeDerivedIso_transition_app a φ K
  have hiso : IsIso ((derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
      (strictComponentRingedToposHom X n)).map
      (((strictSituation X).derivedComponentModuleTransition (strictStructureSheaf X) φ).app
        ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
          (strictAugmentationRingedToposHom a)).obj K)) ≫
      (strictAugmentationDegreeDerivedIso a n).hom.app K) := by
    rw [h]
    infer_instance
  have := @IsIso.of_isIso_comp_right _ _ _ _ _ _
    ((strictAugmentationDegreeDerivedIso a n).hom.app K) _ hiso
  exact isIso_of_reflects_iso _ (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
    (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
    (strictComponentRingedToposHom X n))

/-- **The transport along a transition of the strict systems, realized.** For `K, E` in `D(Z)` and
a map `ψ : (Lb^*K)_m ⟶ (Lb^*E)_m`, the transport `(Lb^*K)(φ)⁻¹ ≫ Lf_φ^*ψ ≫ (Lb^*E)(φ)` realizes,
through the component isomorphisms, to the transport of the realization of `ψ` along
`La_m^* ⋙ LX(φ)^* ≅ La_n^*`. -/
theorem derivedPullback_map_strictTransport {m n : SimplexCategory} (φ : m ⟶ n)
    (K E : @DerivedCategory (spacesEtaleRingedTopos B S hS Z).Modules _ _
      (HasDerivedCategory.standard _))
    (ψ : ((strictSituation X).derivedComponentModuleRestriction (strictStructureSheaf X) m).obj
        ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
          (strictAugmentationRingedToposHom a)).obj K) ⟶
      ((strictSituation X).derivedComponentModuleRestriction (strictStructureSheaf X) m).obj
        ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
          (strictAugmentationRingedToposHom a)).obj E)) :
    haveI := isCartesianDerivedModule_strictAugmentation a K φ
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (strictComponentRingedToposHom X n)).map
      (inv (((strictSituation X).derivedComponentModuleTransition (strictStructureSheaf X) φ).app
          ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
            (strictAugmentationRingedToposHom a)).obj K)) ≫
        ((strictSituation X).derivedTransitionPullback (strictStructureSheaf X) φ).map ψ ≫
        ((strictSituation X).derivedComponentModuleTransition (strictStructureSheaf X) φ).app
          ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
            (strictAugmentationRingedToposHom a)).obj E)) =
      (strictAugmentationDegreeDerivedIso a n).hom.app K ≫
        (augmentationTransitionDerivedIso a φ).inv.app K ≫
        (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
            (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
            (spacesEtaleRingedToposHom (X.map φ.op))).map
          ((strictAugmentationDegreeDerivedIso a m).inv.app K ≫
            (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op m)))
              (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
              (strictComponentRingedToposHom X m)).map ψ ≫
            (strictAugmentationDegreeDerivedIso a m).hom.app E) ≫
        (augmentationTransitionDerivedIso a φ).hom.app E ≫
        (strictAugmentationDegreeDerivedIso a n).inv.app E := by
  have e := fun M => (Iso.eq_comp_inv ((strictAugmentationDegreeDerivedIso a n).app M)).mpr
    (strictAugmentationDegreeDerivedIso_transition_app a φ M)
  have eβ := (Iso.eq_comp_inv ((strictComponentDerivedTransitionIso X φ).app _)).mpr
    ((strictComponentDerivedTransitionIso X φ).hom.naturality ψ)
  simp only [Functor.comp_map] at eβ
  have := isCartesianDerivedModule_strictAugmentation a K φ
  have key := CategoryTheory.Functor.map_inv_comp_comp_eq_of_isos
    (derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
      (strictComponentRingedToposHom X n)) _ _ _
    ((strictComponentDerivedTransitionIso X φ).app _)
    ((derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
      (spacesEtaleRingedToposHom (X.map φ.op))).mapIso
        ((strictAugmentationDegreeDerivedIso a m).app K))
    ((augmentationTransitionDerivedIso a φ).app K) ((strictAugmentationDegreeDerivedIso a n).app K)
    ((strictComponentDerivedTransitionIso X φ).app _)
    ((derivedPullback (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
      (spacesEtaleRingedToposHom (X.map φ.op))).mapIso
        ((strictAugmentationDegreeDerivedIso a m).app E))
    ((augmentationTransitionDerivedIso a φ).app E) ((strictAugmentationDegreeDerivedIso a n).app E)
    _ (e K) (e E) (eβ.trans (Category.assoc _ _ _))
  refine key.trans ?_
  simp only [Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc]

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
