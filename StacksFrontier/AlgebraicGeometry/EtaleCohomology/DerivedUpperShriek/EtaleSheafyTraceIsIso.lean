module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.EtaleSheafyTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.SheafyTraceBijection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ProjectionFormula
public import StacksFrontier.CategoryTheory.Adjunction.UnitCupProduct
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductBraidingOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorBraidingNatTrans

/-!
# The sheafy trace map is an isomorphism once the projection formula holds

Let `f : X ⟶ Y` be a morphism of schemes with a compactification `j : X ⟶ X̄`, `f̄ : X̄ ⟶ Y`, so
that `Rf_! = Rf̄_* ∘ j_!` (`Stacks.EtaleCohomology.derivedLowerShriekUnbounded`), let `Λ` be a
commutative ring and suppose `Rf_!` has a right adjoint `Rf^!`. This file proves that the map of
[Stacks, Tag 0GLB]

`Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)`

(`Stacks.EtaleCohomology.etaleSheafyTrace`) is an isomorphism for every `K` as soon as the map

`Rf_!L ⊗^L_Λ M ⟶ Rf_!(L ⊗^L_Λ f^{-1}M)`

of [Stacks, Tag 0GL5] (`Stacks.EtaleCohomology.derivedLowerShriekUnboundedTensorMap`) is an
isomorphism for every `M` (`Stacks.EtaleCohomology.isIso_etaleSheafyTrace_of_isIso_tensorMap`).
That is the proof of [Stacks, Tag 0GLC], whose remaining input is [Stacks, Tag 0GL5].

## The comparison with the map of Tag 0GL5

The abstract argument of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.SheafyTraceBijection` reduces
the statement to the invertibility of the projection map read off the map `α` of
[Stacks, Tag 0GL7], for the adjunction `(j^{-1} ∘ f̄^{-1}) ⊣ (Rf̄_* ∘ Rj_*)`. That map is the unit
of `f̄^{-1} ⊣ Rf̄_*` followed by the relative cup product of `f̄` at `(f̄^{-1}M, j_!L)` and by
isomorphisms; the unit of `j^{-1} ⊣ Rj_*` drops out because `j^{-1}` of it is invertible. The map
of [Stacks, Tag 0GL5] is the projection map of `f̄` at `(j_!L, M)` followed by isomorphisms, and
the projection map of `f̄` is the unit in the *other* factor followed by the cup product. The two
orders are exchanged by the commutativity of the relative cup product, [Stacks, Tag 0FPM]; the
unit of the étale adjunction is read off the one of the constant ringed topoi by
`CategoryTheory.Adjunction.map_transportedUnit_comp`.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleDerivedTensor_map_unit_app_extensionByZero`
* `Stacks.EtaleCohomology.isIso_etaleDerivedTensor_map_unit_comp_relativeCupProduct`
* `Stacks.EtaleCohomology.isIso_etaleSheafyTrace_of_isIso_tensorMap`

## References

* [Stacks Project, Tag 0GLB](https://stacks.math.columbia.edu/tag/0GLB)
* [Stacks Project, Tag 0GLC](https://stacks.math.columbia.edu/tag/0GLC)
* [Stacks Project, Tag 0GL5](https://stacks.math.columbia.edu/tag/0GL5)
* [Stacks Project, Tag 0GL7](https://stacks.math.columbia.edu/tag/0GL7)
* [Stacks Project, Tag 0FPM](https://stacks.math.columbia.edu/tag/0FPM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.DerivedUpperShriek
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Tensoring the unit of `j^{-1} ⊣ Rj_*` with an extension by zero gives an isomorphism**:
`N ⊗^L j_!Z ⟶ Rj_*j^{-1}N ⊗^L j_!Z` is invertible for an open immersion `j`, because by the
projection formula of [Stacks, Tag 0GL1] it is `j_!` of `j^{-1}` of the unit tensored with `Z`, and
`j^{-1}` of the unit is invertible. -/
theorem isIso_etaleDerivedTensor_map_unit_app_extensionByZero
    (N : DerivedCategory (EtaleModules.{u, r} Λ X))
    (Z : DerivedCategory (EtaleModules.{u, r} Λ U)) :
    IsIso (((etaleDerivedTensor.{u, r} Λ X).map
      ((etaleModuleDerivedInverseImageAdj.{u, r} Λ j).unit.app N)).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).obj Z)) := by
  have hη : IsIso ((etaleModuleDerivedInverseImage.{u, r} Λ j).map
      ((etaleModuleDerivedInverseImageAdj.{u, r} Λ j).unit.app N)) := by
    have h := (etaleModuleDerivedInverseImageAdj.{u, r} Λ j).left_triangle_components N
    have : IsIso ((etaleModuleDerivedInverseImage.{u, r} Λ j).map
        ((etaleModuleDerivedInverseImageAdj.{u, r} Λ j).unit.app N) ≫
          (etaleModuleDerivedInverseImageAdj.{u, r} Λ j).counit.app
            ((etaleModuleDerivedInverseImage.{u, r} Λ j).obj N)) := by
      rw [h]; exact IsIso.id _
    exact IsIso.of_isIso_comp_right _
      ((etaleModuleDerivedInverseImageAdj.{u, r} Λ j).counit.app
        ((etaleModuleDerivedInverseImage.{u, r} Λ j).obj N))
  have hP := extensionProjectionMapApp_naturality_left (etaleDerivedExtensionByZeroAdj.{u, r} Λ j)
    (etaleDerivedTensor.{u, r} Λ X) (etaleDerivedTensor.{u, r} Λ U)
    (etaleDerivedInverseImageTensorIso.{u, r} Λ j)
    ((etaleModuleDerivedInverseImageAdj.{u, r} Λ j).unit.app N) Z
  have h₁ : IsIso (extensionProjectionMapApp (etaleDerivedExtensionByZeroAdj.{u, r} Λ j)
      (etaleDerivedTensor.{u, r} Λ X) (etaleDerivedTensor.{u, r} Λ U)
      (etaleDerivedInverseImageTensorIso.{u, r} Λ j)
      ((𝟭 (DerivedCategory (EtaleModules.{u, r} Λ X))).obj N) Z) :=
    isIso_etaleDerivedProjectionMap_app_app.{u, r} Λ j N Z
  have h₂ : IsIso (extensionProjectionMapApp (etaleDerivedExtensionByZeroAdj.{u, r} Λ j)
      (etaleDerivedTensor.{u, r} Λ X) (etaleDerivedTensor.{u, r} Λ U)
      (etaleDerivedInverseImageTensorIso.{u, r} Λ j)
      ((etaleModuleDerivedInverseImage.{u, r} Λ j ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ j).obj N) Z) :=
    isIso_etaleDerivedProjectionMap_app_app.{u, r} Λ j _ Z
  rw [← IsIso.inv_comp_eq] at hP
  have h₃ : IsIso ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j).map
      (((etaleDerivedTensor.{u, r} Λ U).map ((etaleModuleDerivedInverseImage.{u, r} Λ j).map
        ((etaleModuleDerivedInverseImageAdj.{u, r} Λ j).unit.app N))).app Z)) := inferInstance
  rw [← hP]
  infer_instance

end OpenImmersion

section CupProduct

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **The unit-then-cup map is invertible where the projection map is.** For `g : X ⟶ Y`, `G` in
`D(X_étale, Λ)` and `M` in `D(Y_étale, Λ)`, if the projection map
`Rg_*G ⊗^L M ⟶ Rg_*(G ⊗^L g^{-1}M)` (`Stacks.EtaleCohomology.etaleDerivedPushforwardTensorMap`) is
invertible, then so is `M ⊗^L Rg_*G ⟶ Rg_*g^{-1}M ⊗^L Rg_*G ⟶ Rg_*(g^{-1}M ⊗^L G)`, the unit of
`g^{-1} ⊣ Rg_*` followed by the relative cup product. The two maps are exchanged by the
commutativity of the relative cup product ([Stacks, Tag 0FPM]), after reading both on the
constant ringed topoi. -/
theorem isIso_etaleDerivedTensor_map_unit_comp_relativeCupProduct
    (G : DerivedCategory (EtaleModules.{u, r} Λ X)) (M : DerivedCategory (EtaleModules.{u, r} Λ Y))
    [IsIso (etaleDerivedPushforwardTensorMap.{u, r} Λ g G M)] :
    IsIso (((etaleDerivedTensor.{u, r} Λ Y).map
        ((etaleModuleDerivedInverseImageAdj.{u, r} Λ g).unit.app M)).app
          ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).obj G) ≫
      ((etaleRelativeCupProduct.{u, r} Λ g).app
        ((etaleModuleDerivedInverseImage.{u, r} Λ g).obj M)).app G) := by
  have hPF := (isIso_etaleDerivedPushforwardTensorMap_iff.{u, r} Λ g G M).1 inferInstance
  refine (TensorHomAdjunction.isIso_map_comp_transportCupApp_iff
    (etaleDerivedEquivalence.{u, r} Λ X) (etaleDerivedEquivalence.{u, r} Λ Y)
    (etaleDerivedPushforwardIso.{u, r} Λ g) (etaleRingedRelativeCupProduct.{u, r} Λ g)
    ((etaleModuleDerivedInverseImageAdj.{u, r} Λ g).unit.app M) G).2 ?_
  have hX : (etaleDerivedEquivalence.{u, r} Λ Y).functor.map
        ((etaleModuleDerivedInverseImageAdj.{u, r} Λ g).unit.app M) ≫
        (etaleDerivedPushforwardIso.{u, r} Λ g).hom.app
          ((etaleModuleDerivedInverseImage.{u, r} Λ g).obj M) =
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction
          (etaleRingedToposHom.{u, r} Λ g)).unit.app
          ((etaleDerivedEquivalence.{u, r} Λ Y).functor.obj M) ≫
        (etaleRingedDerivedPushforward.{u, r} Λ g).map
          ((etaleRingedDerivedPullbackIso.{u, r} Λ g).hom.app M) :=
    Adjunction.map_transportedUnit_comp _ _ _ _ _ M
  rw [hX, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  have hcup : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (etaleRingedSite.{u, r} Λ Y).O).map ((etaleRingedDerivedPushforward.{u, r} Λ g).map
          ((etaleRingedDerivedPullbackIso.{u, r} Λ g).hom.app M))).app
          ((etaleRingedDerivedPushforward.{u, r} Λ g).obj
            ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj G)) ≫
        ((etaleRingedRelativeCupProduct.{u, r} Λ g).app
          ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj
            ((etaleModuleDerivedInverseImage.{u, r} Λ g).obj M))).app
          ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj G) =
      ((etaleRingedRelativeCupProduct.{u, r} Λ g).app
          ((etaleRingedDerivedPullback.{u, r} Λ g).obj
            ((etaleDerivedEquivalence.{u, r} Λ Y).functor.obj M))).app
          ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj G) ≫
        (etaleRingedDerivedPushforward.{u, r} Λ g).map
          (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
            (etaleRingedSite.{u, r} Λ X).O).map
              ((etaleRingedDerivedPullbackIso.{u, r} Λ g).hom.app M)).app
            ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj G)) :=
    congrArg (fun φ => NatTrans.app φ ((etaleDerivedEquivalence.{u, r} Λ X).functor.obj G))
      ((etaleRingedRelativeCupProduct.{u, r} Λ g).naturality
        ((etaleRingedDerivedPullbackIso.{u, r} Λ g).hom.app M))
  rw [hcup, ← Category.assoc]
  refine (isIso_comp_right_iff _ _).2 ?_
  have hψ : ∀ (W : Scheme.{u}) A B,
      IsIso (Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom
        (etaleRingedSite.{u, r} Λ W).ringedTopos.O A B) := fun W A B => by
    unfold Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom
    exact Iso.isIso_hom _
  exact Stacks.Cohomology.RelativeCupProductOnRingedTopoi.isIso_map_unit_comp_adjunctionCupProduct
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction (etaleRingedToposHom.{u, r} Λ g))
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ Y).O)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (etaleRingedSite.{u, r} Λ X).O)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
      (etaleRingedToposHom.{u, r} Λ g)).hom
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom
      (etaleRingedSite.{u, r} Λ Y).ringedTopos.O)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom
      (etaleRingedSite.{u, r} Λ X).ringedTopos.O) (hψ Y) (hψ X)
    (fun u B => by
      have h := Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom_naturality
        (etaleRingedSite.{u, r} Λ Y).ringedTopos.O u (𝟙 B)
      simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
        Category.comp_id, Category.id_comp] at h
      exact h)
    (fun K K' => Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_braiding
      (etaleRingedToposHom.{u, r} Λ g) K K') _ _ hPF

end CupProduct

section SheafyTrace

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))
  [(derivedLowerShriekUnbounded.{u, r} f j Λ).IsLeftAdjoint]

/-- **The proof of [Stacks, Tag 0GLC], given [Stacks, Tag 0GL5].** If the map
`Rf_!L ⊗^L_Λ M ⟶ Rf_!(L ⊗^L_Λ f^{-1}M)` of [Stacks, Tag 0GL5] is an isomorphism for every `M`,
then the map `Rf_*RHom_Λ(L, Rf^!K) ⟶ RHom_Λ(Rf_!L, K)` of [Stacks, Tag 0GLB] is an isomorphism
for every `K`. -/
theorem isIso_etaleSheafyTrace_of_isIso_tensorMap
    (L : DerivedCategory (EtaleModules.{u, r} Λ X))
    (h : ∀ M, IsIso (derivedLowerShriekUnboundedTensorMap.{u, r} Λ j L M))
    (K : DerivedCategory (EtaleModules.{u, r} Λ Y)) :
    IsIso (etaleSheafyTrace.{u, r} Λ f j L K) := by
  refine (congrArg (fun φ => IsIso φ) (etaleSheafyTrace_eq_sheafyTrace.{u, r} Λ f j L K)).mpr ?_
  have ha : IsIso ((etaleCompactificationLerayIso.{u, r} Λ f j).hom.app
      (((etaleDerivedHom.{u, r} Λ X).obj (op L)).obj
        ((derivedLowerShriekUnbounded.{u, r} f j Λ).rightAdjoint.obj K))) := inferInstance
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ ha ?_
  refine CompactificationData.isIso_sheafyTrace_of_isIso_lowerShriekTensorMap
    (etaleCompactificationData.{u, r} Λ f j)
    (Adjunction.ofIsLeftAdjoint (derivedLowerShriekUnbounded.{u, r} f j Λ))
    ((etaleModuleDerivedInverseImageAdj.{u, r} Λ j.toBase).comp
      (etaleModuleDerivedInverseImageAdj.{u, r} Λ j.immersion)) L (fun M => ?_) K
  have := (isIso_derivedLowerShriekUnboundedTensorMap_iff.{u, r} Λ j L M).1 (h M)
  exact CompactificationData.isIso_lowerShriekTensorMap_comp
    (etaleCompactificationData.{u, r} Λ f j)
    (etaleModuleDerivedInverseImageAdj.{u, r} Λ j.toBase)
    (etaleModuleDerivedInverseImageAdj.{u, r} Λ j.immersion) M L
    (isIso_etaleDerivedTensor_map_unit_app_extensionByZero.{u, r} Λ j.immersion _ L)
    (isIso_etaleDerivedTensor_map_unit_comp_relativeCupProduct.{u, r} Λ j.toBase
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ j.immersion).obj L) M)

end SheafyTrace

end Stacks.EtaleCohomology

end
