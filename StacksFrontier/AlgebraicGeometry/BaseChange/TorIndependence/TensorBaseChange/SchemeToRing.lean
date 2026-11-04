module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.RingTensor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMapTransport

/-!
# The map of Stacks 0DJ7 on schemes and on rings

The map of Stacks 0DJ7 at a point of a commutative square of schemes is the ring-level map of the
square of local rings, up to the identification of the two module structures carried by the
cohomology of a derived base change.  It transports along isomorphisms of the source and of the
target.

## Main results

* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_iff_ring`: the map of Stacks 0DJ7 at a point
  is invertible exactly when the ring-level base-change map of the stalks is.
* `RingTheory.TorIndependence.isIso_chosenBaseChangeMap_iff_of_iso`: invertibility of the
  base-change map is preserved under isomorphisms of the source and of the target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open RingTheory.TorIndependence

universe u


namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']

/-- The two `A ⊗_R R'`-module structures on the cohomology of a derived base change agree. -/
def baseChangeCohomologyCatIso (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    baseChangeCohomologyCat (R := R) (R' := R') K n ≅
      baseChangeCohomology (R := R) (R' := R') K n :=
  LinearEquiv.toModuleIso (show baseChangeCohomologyCat (R := R) (R' := R') K n ≃ₗ[A ⊗[R] R']
      baseChangeCohomology (R := R) (R' := R') K n from
    { toFun := fun m => m
      invFun := fun m => m
      map_add' := fun _ _ => rfl
      map_smul' := fun b m =>
        congrArg
          (fun M : Module (A ⊗[R] R') (baseChangeCohomologyOverBase (R := R) (R' := R') K n) =>
            (letI := M; (b • (show baseChangeCohomologyOverBase (R := R) (R' := R') K n from m) :
              baseChangeCohomologyOverBase (R := R) (R' := R') K n)))
          (baseChangeCohomologyModule_eq (R := R) (R' := R') K n)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })

variable {A' : Type u} [CommRing A'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- The base-change map chosen by `exists_unique_ringBaseChangeCohomologyMap` is invertible
exactly when the constructed one is. -/
theorem isIso_choose_ringBaseChangeCohomologyMap_iff (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) :
    IsIso (Classical.choose (exists_unique_ringBaseChangeCohomologyMap
      (R := R) (A := A) (R' := R') (A' := A') K K' φ n).exists) ↔
      IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n) := by
  have key : ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n =
      (ModuleCat.extendScalars (baseChangeTensorRingMap (R := R) (A := A) (R' := R')
          (A' := A'))).map (baseChangeCohomologyCatIso (R := R) (R' := R') K n).hom ≫
        Classical.choose (exists_unique_ringBaseChangeCohomologyMap
          (R := R) (A := A) (R' := R') (A' := A') K K' φ n).exists :=
    ModuleCat.ExtendScalars.hom_ext fun m =>
      (ringBaseChangeCohomologyMap_one_tmul (R := R) (R' := R') K K' φ n m).trans
        (Classical.choose_spec (exists_unique_ringBaseChangeCohomologyMap
          (R := R) (A := A) (R' := R') (A' := A') K K' φ n).exists m).symm
  rw [key]
  have : IsIso ((ModuleCat.extendScalars (baseChangeTensorRingMap (R := R) (A := A) (R' := R')
      (A' := A'))).map (baseChangeCohomologyCatIso (R := R) (R' := R') K n).hom) :=
    ((ModuleCat.extendScalars _).mapIso
      (baseChangeCohomologyCatIso (R := R) (R' := R') K n)).isIso_hom
  exact (isIso_comp_left_iff ((ModuleCat.extendScalars (baseChangeTensorRingMap (R := R) (A := A)
    (R' := R') (A' := A'))).map (baseChangeCohomologyCatIso (R := R) (R' := R') K n).hom) _).symm

/-- The base-change map chosen by `exists_unique_ringBaseChangeCohomologyMap`. -/
abbrev chosenBaseChangeMap (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) :=
  Classical.choose (exists_unique_ringBaseChangeCohomologyMap
      (R := R) (A := A) (R' := R') (A' := A') K K' φ n).exists

/-- The base-change map of `φ ≫ ψ` is the base-change map of `φ` followed by the map induced by
`ψ` on cohomology. -/
theorem chosenBaseChangeMap_comp_target (K : DerivedCategory (ModuleCat.{u} A))
    (K' K'' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (ψ : K' ⟶ K'') (n : ℤ) :
    chosenBaseChangeMap (R := R) (R' := R') K K'' (φ ≫ ψ) n =
      chosenBaseChangeMap (R := R) (R' := R') K K' φ n ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map ψ := by
  have h₁ := Classical.choose_spec (exists_unique_ringBaseChangeCohomologyMap
      (R := R) (A := A) (R' := R') (A' := A') K K'' (φ ≫ ψ) n).exists
  have h₂ := Classical.choose_spec (exists_unique_ringBaseChangeCohomologyMap
      (R := R) (A := A) (R' := R') (A' := A') K K' φ n).exists
  refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
  refine (h₁ m).trans (Eq.trans ?_ (congrArg
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map ψ).hom (h₂ m)).symm)
  have n1 := ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso
    n).hom.naturality ψ
  have hc : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app K ≫
          (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map (φ ≫ ψ)) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app K ≫
          (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map φ) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map ψ) := by
    simp only [Functor.map_comp, Category.assoc]
  have key := congrArg (fun t => t.hom (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app K ≫
          (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map φ)).hom m)) n1
  exact (congrArg (fun t => (((ModuleCat.restrictScalars
    (algebraMap R' A')).mapDerivedCategoryHomologyIso n).app K'').hom.hom (t.hom m)) hc).trans key

/-- The base-change map of the derived extension of scalars of `θ` followed by `φ` is the
extension of scalars of the map induced by `θ` on cohomology, followed by the base-change map of
`φ`. -/
theorem chosenBaseChangeMap_comp_source {K₁ K₂ : DerivedCategory (ModuleCat.{u} A)}
    (K' : DerivedCategory (ModuleCat.{u} A')) (θ : K₁ ⟶ K₂)
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K₂ ⟶ K') (n : ℤ) :
    chosenBaseChangeMap (R := R) (R' := R') K₁ K'
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A A')).functor.map θ ≫ φ) n =
      (ModuleCat.extendScalars (baseChangeTensorRingMap (R := R) (A := A) (R' := R')
          (A' := A'))).map (baseChangeCohomologyMapHom (R := R) (R' := R') K₁ K₂ θ n) ≫
        chosenBaseChangeMap (R := R) (R' := R') K₂ K' φ n := by
  have h₁ := Classical.choose_spec (exists_unique_ringBaseChangeCohomologyMap
      (R := R) (A := A) (R' := R') (A' := A') K₁ K'
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A A')).functor.map θ ≫ φ) n).exists
  have h₂ := Classical.choose_spec (exists_unique_ringBaseChangeCohomologyMap
      (R := R) (A := A) (R' := R') (A' := A') K₂ K' φ n).exists
  have hτ := ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).naturality θ).symm
  refine ModuleCat.ExtendScalars.hom_ext fun m => (h₁ m).trans ?_
  refine Eq.trans ?_
    (h₂ ((baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n).hom m)).symm
  congr 1
  have hc : (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app K₁ ≫
          (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap A A')).functor.map θ ≫ φ)) =
      baseChangeCohomologyOverBaseMap (R := R) (R' := R') K₁ K₂ θ n ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app K₂ ≫
            (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map φ) := by
    dsimp only [Functor.comp_map] at hτ
    rw [Functor.map_comp (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory,
      ← Category.assoc, hτ, Category.assoc, Functor.map_comp]
  exact congrArg (fun l => l.hom m) hc

/-- **The base-change map transports along isomorphisms of the source and of the target.** -/
theorem isIso_chosenBaseChangeMap_iff_of_iso {K₁ K₂ : DerivedCategory (ModuleCat.{u} A)}
    {K₁' K₂' : DerivedCategory (ModuleCat.{u} A')} (θ : K₁ ≅ K₂) (ψ : K₁' ≅ K₂')
    (φ₁ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K₁ ⟶ K₁')
    (φ₂ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K₂ ⟶ K₂')
    (h : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.map θ.hom ≫ φ₂ = φ₁ ≫ ψ.hom) (n : ℤ) :
    IsIso (chosenBaseChangeMap (R := R) (R' := R') K₁ K₁' φ₁ n) ↔
      IsIso (chosenBaseChangeMap (R := R) (R' := R') K₂ K₂' φ₂ n) := by
  have e₁ := chosenBaseChangeMap_comp_target (R := R) (R' := R') K₁ K₁' K₂' φ₁ ψ.hom n
  have e₂ := chosenBaseChangeMap_comp_source (R := R) (R' := R') K₂' θ.hom φ₂ n
  rw [h] at e₂
  rw [e₂] at e₁
  have i₁ := isIso_baseChangeCohomologyMapHom (R := R) (R' := R') θ.hom inferInstance n
  have i₂ : IsIso ((ModuleCat.extendScalars (baseChangeTensorRingMap (R := R) (A := A) (R' := R')
      (A' := A'))).map (baseChangeCohomologyMapHom (R := R) (R' := R') K₁ K₂ θ.hom n)) :=
    @Functor.map_isIso _ _ _ _ _ _ _ _ i₁
  have i₃ : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map ψ.hom) :=
    Functor.map_isIso _ _
  rw [← isIso_comp_right_iff (chosenBaseChangeMap (R := R) (R' := R') K₁ K₁' φ₁ n)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).map ψ.hom), ← e₁]
  exact @isIso_comp_left_iff _ _ _ _ _ _ _ i₂

end RingTheory.TorIndependence

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- **The map of Stacks 0DJ7 is invertible exactly when the ring-level base-change map of the
stalks is.** -/
theorem isIso_baseChangeCohomologyMap_iff_ring
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      g'.toLRSHom.toShHom).obj K ⟶ K') (x' : X') (n : ℤ) :
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
      ((f.stalkMap (g' x')).hom).toAlgebra
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
      (baseStalkMap f g f' g' w x').toAlgebra
    letI : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
      (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
    letI : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
      ((g'.stalkMap x').hom).toAlgebra
    letI : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
      ((f'.stalkMap x').hom).toAlgebra
    letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
        (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
        (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
    IsIso (baseChangeCohomologyMap f g f' g' w K K' φ x' n) ↔
      IsIso (ringBaseChangeCohomologyMap (R := S.presheaf.stalk (f (g' x')))
        (R' := S'.presheaf.stalk (f' x')) ((derivedStalkFunctor (g' x')).obj K)
        ((derivedStalkFunctor x').obj K')
        ((derivedPullbackStalkIso g' x').inv.app K ≫ (derivedStalkFunctor x').map φ) n) := by
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' w x').toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
    (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
    ((f'.stalkMap x').hom).toAlgebra
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
  exact isIso_choose_ringBaseChangeCohomologyMap_iff _ _ _ n

end AlgebraicGeometry
