module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedGlobalSectionsOfToposHom

/-!
# Derived global sections along a morphism with invertible derived unit

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi. For `K ∈ D(𝒪_D)` the
canonical comparison

`RΓ(D, K) ⟶ RΓ(C, Lf^*K)`

(read in `D(Γ(𝒪_D))`, the right hand side through restriction of scalars along
`Γ(𝒪_D) ⟶ Γ(𝒪_C)`) is `RΓ(D, -)` of the unit `K ⟶ Rf_*Lf^*K` of the derived adjunction followed
by the identification `RΓ(D, -) ∘ Rf_* = RΓ(C, -)` of Stacks 0D6H (Cohomology on Sites,
Remark 08J6). Hence it is an isomorphism as soon as the unit is invertible at `K`. This is the
formal step by which a cohomological descent statement `K = Rf_*Lf^*K` on a class of objects
yields `RΓ(D, K) = RΓ(C, Lf^*K)` on that class. The unit is invertible on a class `P` in
particular when `Lf^*` corestricts to a fully faithful functor from `P` to a class `Q` which
`Rf_*` carries back into `P`, as it does when `Lf^* : P ⟶ Q` is an equivalence with
quasi-inverse `Rf_*`; this is how Stacks 0DHG follows from Stacks 0DHF.

## Main definitions

* `Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsSemilinearNatTrans`: the comparison
  `RΓ(D, -) ⟶ ρ_* RΓ(C, Lf^* -)` as a natural transformation; its component at `K` is
  `Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsSemilinearMap`.
* `Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsIsoOfIsIsoUnit`: the resulting natural
  isomorphism on any class of objects on which the derived unit is invertible.
* `Stacks.Cohomology.LerayOfToposHom.derivedGlobalSectionsIsoOfFullyFaithful`: the same
  isomorphism on a class `P` on which `Lf^*` is fully faithful into a class `Q` with
  `Rf_* Q ⊂ P`.

## Main results

* `Stacks.Cohomology.LerayOfToposHom.isIso_derivedGlobalSectionsSemilinearMap_of_isIso_unit`:
  the comparison is invertible at every `K` at which the derived unit is.
* `CategoryTheory.Adjunction.isIso_unit_app_of_fullyFaithful_lift`: the unit of an adjunction is
  invertible on a class of objects on which the left adjoint is fully faithful, provided the
  right adjoint carries the target class back.

## Implementation notes

The derived adjunction `Lf^* ⊣ Rf_*` of a morphism of ringed topoi and the identification of
Stacks 0D6H are constructed in the standard model `HasDerivedCategory.standard` of the derived
categories of modules; the statements here are about those constructions and so are made in the
same model, which is installed as a file-local instance (the locally small model does not apply
at the free universes of this file).

## References

* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.RingedToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.SiteModules

noncomputable section

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (P : ObjectProperty C) (Q : ObjectProperty D) (hL : ∀ K, P K → Q (L.obj K))

/-- **The unit of an adjunction is invertible on a class `P` of objects as soon as the left
adjoint, corestricted to `P ⟶ Q`, is fully faithful, and the right adjoint carries `Q` into
`P`.** -/
theorem isIso_unit_app_of_fullyFaithful_lift (hR : ∀ K, Q K → P (R.obj K))
    (hff : (Q.lift (P.ι ⋙ L) (fun K ↦ hL K.obj K.property)).FullyFaithful)
    (K : C) (hK : P K) : IsIso (adj.unit.app K) := by
  let adj' := adj.restrictFullyFaithful (L := Q.lift (P.ι ⋙ L) (fun K ↦ hL K.obj K.property))
    (R := P.lift (Q.ι ⋙ R) (fun K ↦ hR K.obj K.property))
    P.fullyFaithfulι Q.fullyFaithfulι (Iso.refl _) (Iso.refl _)
  have := hff.full
  have := hff.faithful
  have : IsIso (P.ι.map (adj'.unit.app ⟨K, hK⟩)) := inferInstance
  rw [adj.map_restrictFullyFaithful_unit_app] at this
  simpa using this

end CategoryTheory.Adjunction

namespace Stacks.Cohomology.LerayOfToposHom

universe v v' u w t s r r'

attribute [local instance] HasDerivedCategory.standard
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {X : RingedTopos.{v, max u t, max w t s}} {Y : RingedTopos.{v', max u s, max w t s}}
  [X.J.HasSheafCompose (forget RingCat.{max w t s})]
  [Y.J.HasSheafCompose (forget RingCat.{max w t s})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{max w t s} RingCat.{max w t s})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max w t s} RingCat.{max w t s})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{max w t s})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{max w t s})]
  [HasSheafify X.J AddCommGrpCat.{max w t s}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max w t s}]
  [HasSheafify Y.J AddCommGrpCat.{max w t s}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max w t s}]
  [HasSheafify X.J (Type (max w t s))] [HasSheafify Y.J (Type (max w t s))]
  [IsGrothendieckAbelian.{max w t s} (SheafOfModules.{max w t s}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))]
  [IsGrothendieckAbelian.{max w t s} (SheafOfModules.{max w t s}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))]
  (f : RingedToposHom X Y)
  {R : Type r} [Ring R] [HasDerivedCategory (ModuleCat.{max u w t s} R)]
  {R' : Type r'} [Ring R'] [HasDerivedCategory (ModuleCat.{max u w t s} R')]
  (ψ : R →+* RingCat.sectionsSubring
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O).obj)
  (ψ' : R' →+* RingCat.sectionsSubring
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O).obj) (ρ : R' →+* R)
  (h : (toposGlobalSectionsRingHom f).comp ψ' = ψ.comp ρ)

/-- **The comparison `RΓ(D, -) ⟶ ρ_* RΓ(C, Lf^* -)` as a natural transformation**: `RΓ(D, -)`
of the unit of the derived adjunction `Lf^* ⊣ Rf_*`, followed by the global-sections clause of
Stacks 0D6H and the compatibility `h` of the ring maps. Its component at `K` is
`derivedGlobalSectionsSemilinearMap`. -/
def derivedGlobalSectionsSemilinearNatTrans :
    Stacks.DerivedFunctor.totalRightDerived
        (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
          ModuleCat.restrictScalars ψ') ⟶
      derivedPullback f ⋙ Stacks.DerivedFunctor.totalRightDerived
          (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
            ModuleCat.restrictScalars ψ) ⋙
        (ModuleCat.restrictScalars ρ).mapDerivedCategory :=
  Functor.whiskerRight (derivedAdjunction f).unit _ ≫
    Functor.whiskerLeft (derivedPullback f)
      ((derivedGlobalSectionsPushforwardIso.{v, v', u, w, t, s, r'} f ψ').hom ≫
        (derivedGlobalSectionsRestrictScalarsIso.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h).hom)

/-- The component of `derivedGlobalSectionsSemilinearNatTrans` at `K` is
`derivedGlobalSectionsSemilinearMap` at `K`. -/
theorem derivedGlobalSectionsSemilinearNatTrans_app
    (K : DerivedCategory (SheafOfModules.{max w t s}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))) :
    (derivedGlobalSectionsSemilinearNatTrans.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h).app K =
      derivedGlobalSectionsSemilinearMap.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h K :=
  rfl

/-- **The comparison `RΓ(D, K) ⟶ ρ_* RΓ(C, Lf^*K)` is invertible wherever the derived unit
`K ⟶ Rf_*Lf^*K` is.** It is `RΓ(D, -)` of that unit followed by two isomorphisms. -/
theorem isIso_derivedGlobalSectionsSemilinearMap_of_isIso_unit
    (K : DerivedCategory (SheafOfModules.{max w t s}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))
    (hK : IsIso ((derivedAdjunction f).unit.app K)) :
    IsIso (derivedGlobalSectionsSemilinearMap.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h K) := by
  unfold derivedGlobalSectionsSemilinearMap
  infer_instance

include h in
/-- **`RΓ(D, -) ≅ ρ_* RΓ(C, Lf^* -)` on any class `P` of objects of `D(𝒪_D)` on which the
derived unit `K ⟶ Rf_*Lf^*K` is invertible.** Its components are
`derivedGlobalSectionsSemilinearMap`. -/
def derivedGlobalSectionsIsoOfIsIsoUnit
    (P : ObjectProperty (DerivedCategory (SheafOfModules.{max w t s}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))))
    (hP : ∀ K, P K → IsIso ((derivedAdjunction f).unit.app K)) :
    P.ι ⋙ Stacks.DerivedFunctor.totalRightDerived
        (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
          ModuleCat.restrictScalars ψ') ≅
      P.ι ⋙ derivedPullback f ⋙ Stacks.DerivedFunctor.totalRightDerived
          (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
            ModuleCat.restrictScalars ψ) ⋙
        (ModuleCat.restrictScalars ρ).mapDerivedCategory :=
  haveI : ∀ K : P.FullSubcategory, IsIso ((Functor.whiskerLeft P.ι
      (derivedGlobalSectionsSemilinearNatTrans.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h)).app K) :=
    fun K ↦ isIso_derivedGlobalSectionsSemilinearMap_of_isIso_unit f ψ ψ' ρ h K.obj
      (hP K.obj K.property)
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerLeft P.ι
    (derivedGlobalSectionsSemilinearNatTrans.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h))
  asIso (Functor.whiskerLeft P.ι
    (derivedGlobalSectionsSemilinearNatTrans.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h))

/-- The component of `derivedGlobalSectionsIsoOfIsIsoUnit` at `K` is
`derivedGlobalSectionsSemilinearMap` at `K`. -/
theorem derivedGlobalSectionsIsoOfIsIsoUnit_hom_app
    (P : ObjectProperty (DerivedCategory (SheafOfModules.{max w t s}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))))
    (hP : ∀ K, P K → IsIso ((derivedAdjunction f).unit.app K)) (K : P.FullSubcategory) :
    (derivedGlobalSectionsIsoOfIsIsoUnit.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h P hP).hom.app K =
      derivedGlobalSectionsSemilinearMap.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h K.obj :=
  rfl

include h in
/-- **`RΓ(D, -) ≅ ρ_* RΓ(C, Lf^* -)` on `P` whenever `Lf^*` corestricts to a fully faithful
functor from `P` to a class `Q` of objects of `D(𝒪_C)` which `Rf_*` carries back into `P`** —
in particular whenever `Lf^* : P ⟶ Q` is an equivalence with quasi-inverse `Rf_*`, which is the
shape of a cohomological descent statement `D_{𝒜'}(𝒪_D) = D_𝒜(𝒪_C)` (Stacks 0D7V). -/
def derivedGlobalSectionsIsoOfFullyFaithful
    (P : ObjectProperty (DerivedCategory (SheafOfModules.{max w t s}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))))
    (Q : ObjectProperty (DerivedCategory (SheafOfModules.{max w t s}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))))
    (hL : ∀ K, P K → Q ((derivedPullback f).obj K))
    (hR : ∀ K, Q K → P ((derivedPushforward f).obj K))
    (hff : (Q.lift (P.ι ⋙ derivedPullback f) (fun K ↦ hL K.obj K.property)).FullyFaithful) :
    P.ι ⋙ Stacks.DerivedFunctor.totalRightDerived
        (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O) ⋙
          ModuleCat.restrictScalars ψ') ≅
      P.ι ⋙ derivedPullback f ⋙ Stacks.DerivedFunctor.totalRightDerived
          (globalSectionsFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O) ⋙
            ModuleCat.restrictScalars ψ) ⋙
        (ModuleCat.restrictScalars ρ).mapDerivedCategory :=
  derivedGlobalSectionsIsoOfIsIsoUnit.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h P
    (fun K hK ↦ (derivedAdjunction f).isIso_unit_app_of_fullyFaithful_lift P Q hL hR hff K hK)

/-- The component of `derivedGlobalSectionsIsoOfFullyFaithful` at `K` is
`derivedGlobalSectionsSemilinearMap` at `K`. -/
theorem derivedGlobalSectionsIsoOfFullyFaithful_hom_app
    (P : ObjectProperty (DerivedCategory (SheafOfModules.{max w t s}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O))))
    (Q : ObjectProperty (DerivedCategory (SheafOfModules.{max w t s}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))))
    (hL : ∀ K, P K → Q ((derivedPullback f).obj K))
    (hR : ∀ K, Q K → P ((derivedPushforward f).obj K))
    (hff : (Q.lift (P.ι ⋙ derivedPullback f) (fun K ↦ hL K.obj K.property)).FullyFaithful)
    (K : P.FullSubcategory) :
    (derivedGlobalSectionsIsoOfFullyFaithful.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h P Q hL hR
      hff).hom.app K =
      derivedGlobalSectionsSemilinearMap.{v, v', u, w, t, s, r, r'} f ψ ψ' ρ h K.obj :=
  rfl

end Stacks.Cohomology.LerayOfToposHom

end
