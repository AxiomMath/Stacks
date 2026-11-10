module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsAlongSurjection
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyFactorsh
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapConstruction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.MapHomologicalComplexHomologyIsoNatTrans
public import StacksFrontier.Homology.HomComplex.RHom.HomModuleBaseChange
public import StacksFrontier.Homology.Perfect.DerivedReduction
public import StacksFrontier.Homology.RelativelyPerfect.BaseChange
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.ComparisonMate
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyIsoId

/-!
# The base-change map on cohomology under a change of the commutative square

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a commutative square of commutative rings,
`K ∈ D(A)`, `K' ∈ D(A')` and `φ : K ⊗ᴸ_A A' ⟶ K'`. The base-change map of Stacks 0DJ7

`A' ⊗_{A ⊗_R R'} H^n(K ⊗ᴸ_R R') ⟶ H^n(K')`

is `RingTheory.TorIndependence.ringBaseChangeCohomologyMap`. This file records the two pieces of
the ring-level argument of Stacks 0DJ8 that do not involve a second square: for a cartesian square
(`A' = A ⊗_R R'`) the map is invertible exactly when the comparison of Stacks 065Z followed by `φ`
is invertible on `H^n`; and, given a second square receiving a map from the first, the morphism
`(K ⊗ᴸ_A A₁) ⊗ᴸ_{A₁} A₁' ⟶ K' ⊗ᴸ_{A'} A₁'` induced by `φ`, which is the datum the second square's
base-change map is formed with.

## Main definitions

* `RingTheory.TorIndependence.extendScalarsBaseChangeHom`: the morphism
  `(K ⊗ᴸ_A A₁) ⊗ᴸ_{A₁} A₁' ⟶ K' ⊗ᴸ_{A'} A₁'` obtained from `φ` through the composition
  isomorphisms of derived extension of scalars along the two factorizations of `A → A₁'`.

## Main results

* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_iff`: for a cartesian square the
  base-change map is invertible exactly when `cohomologyComparisonMap` is.
* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_iff_isBaseChange_compHom`: for any
  square the base-change map is invertible exactly when `cohomologyComparisonLinearMap` is a base
  change along `A ⊗_R R' → A'`.
* `RingTheory.TorIndependence.isBaseChange_of_comp_eq`: base changes transport along a commuting
  square of base changes; this is how invertibility passes from one square to another.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

/-! ### The base-change map of a cartesian square -/

section Cartesian

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A']
  [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- **The base-change map of a cartesian square.** When `A ⊗_R R' → A'` is bijective, the
base-change map `A' ⊗_{A ⊗_R R'} H^n(K ⊗ᴸ_R R') ⟶ H^n(K')` is invertible exactly when the
comparison `H^n(K ⊗ᴸ_R R') ⟶ H^n(K')` of Stacks 065Z followed by `φ` is: the former is the latter
precomposed with the bijection `m ↦ 1 ⊗ m`. -/
theorem isIso_ringBaseChangeCohomologyMap_iff
    (hA' : Function.Bijective (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')))
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n) ↔
      IsIso (cohomologyComparisonMap (R := R) (R' := R') K K' φ n) := by
  let k := baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')
  let H := baseChangeCohomologyCat (R := R) (R' := R') K n
  have hu := Stacks.ModuleCat.bijective_one_tmul (M := H) k hA'.2 fun a ha m => by
    rw [(injective_iff_map_eq_zero k).mp hA'.1 a ha, zero_smul]
  let u : H → (ModuleCat.extendScalars k).obj H := fun m => (1 : A') ⊗ₜ[A ⊗[R] R', k] m
  have hcomp : (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n).hom ∘ u =
      (cohomologyComparisonMap (R := R) (R' := R') K K' φ n).hom :=
    funext fun m => ringBaseChangeCohomologyMap_one_tmul (R := R) (R' := R') K K' φ n m
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective
      (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n).hom ↔
    Function.Bijective (cohomologyComparisonMap (R := R) (R' := R') K K' φ n).hom
  rw [← hcomp]
  exact (Function.Bijective.of_comp_iff _ hu).symm

/-- **The base-change map is invertible exactly when the comparison is a base change.** The
base-change map `A' ⊗_{A ⊗_R R'} H^n(K ⊗ᴸ_R R') ⟶ H^n(K')` is invertible exactly when the
`A ⊗_R R'`-linear comparison `cohomologyComparisonLinearMap` exhibits `H^n(K')` as the base change
of `H^n(K ⊗ᴸ_R R')` along `A ⊗_R R' → A'`, in the sense of `IsBaseChange`. This is the form in
which the comparison composes along a change of square. -/
theorem isIso_ringBaseChangeCohomologyMap_iff_isBaseChange_compHom
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) :
    letI : Algebra (A ⊗[R] R') A' :=
      (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
    letI := baseChangeCohomologyModule (R := R) (R' := R') K n
    letI : Module (A ⊗[R] R') ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
      Module.compHom _ (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'))
    letI : IsScalarTower (A ⊗[R] R') A'
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
      IsScalarTower.of_compHom _ _ _
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n) ↔
      IsBaseChange A'
        (show baseChangeCohomologyCat (R := R) (R' := R') K n →ₗ[A ⊗[R] R']
            (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K' from
          (cohomologyComparisonLinearMap (R := R) (R' := R') K K' φ n).hom) := by
  let : Algebra (A ⊗[R] R') A' :=
    (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
  let := baseChangeCohomologyModule (R := R) (R' := R') K n
  let : Module (A ⊗[R] R') ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
    Module.compHom _ (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'))
  let : IsScalarTower (A ⊗[R] R') A'
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
    IsScalarTower.of_compHom _ _ _
  let C := A ⊗[R] R'
  let H := baseChangeCohomologyCat (R := R) (R' := R') K n
  let H' := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K'
  let ψ := ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n
  let l : H →ₗ[C] H' := (cohomologyComparisonLinearMap (R := R) (R' := R') K K' φ n).hom
  -- the base-change map, as an `A'`-linear map out of `A' ⊗_C H`
  let Ψ : A' ⊗[C] H →ₗ[A'] H' := ψ.hom
  have hΨ : ∀ (t : A') (m : H), Ψ (t ⊗ₜ[C] m) = t • l m := fun t m => by
    have h1 : (t ⊗ₜ[C] m : A' ⊗[C] H) = t • ((1 : A') ⊗ₜ[C] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, Ψ.map_smul]
    exact congrArg (t • ·)
      (ringBaseChangeCohomologyMap_one_tmul (R := R) (R' := R') K K' φ n m)
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective Ψ ↔ IsBaseChange A' l
  constructor
  · intro h
    exact IsBaseChange.of_equiv (LinearEquiv.ofBijective Ψ h) fun m => by
      change Ψ ((1 : A') ⊗ₜ[C] m) = l m
      rw [hΨ, one_smul]
  · intro h
    have heq : (Ψ : A' ⊗[C] H → H') = h.equiv := by
      funext x
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul t m => rw [hΨ, IsBaseChange.equiv_tmul]
    rw [heq]
    exact h.equiv.bijective

end Cartesian

/-! ### Base changes along a change of square -/

/-- **A base change transported along a change of square.** Let `q : H → H'` be `C`-linear with
`H'` a `T`-module, `q₁ : H₁ → H₁'` be `C₁`-linear with `H₁'` a `T₁`-module, and let
`j : H → H₁`, `j' : H' → H₁'` be linear over `C → C₁` and `T → T₁` with `q₁ ∘ j = j' ∘ q`. If `j`
and `j'` are base changes and `q` exhibits `H'` as the base change of `H` along `C → T`, then `q₁`
exhibits `H₁'` as the base change of `H₁` along `C₁ → T₁`. -/
theorem isBaseChange_of_comp_eq {C C₁ T T₁ : Type*} [CommRing C] [CommRing C₁] [CommRing T]
    [CommRing T₁] [Algebra C C₁] [Algebra C T] [Algebra C₁ T₁] [Algebra T T₁] [Algebra C T₁]
    [IsScalarTower C C₁ T₁] [IsScalarTower C T T₁]
    {H H₁ H' H₁' : Type*} [AddCommGroup H] [AddCommGroup H₁] [AddCommGroup H']
    [AddCommGroup H₁'] [Module C H] [Module C H₁] [Module C₁ H₁] [IsScalarTower C C₁ H₁]
    [Module C H'] [Module T H'] [IsScalarTower C T H']
    [Module C H₁'] [Module C₁ H₁'] [Module T H₁'] [Module T₁ H₁']
    [IsScalarTower C C₁ H₁'] [IsScalarTower C₁ T₁ H₁'] [IsScalarTower C T H₁']
    [IsScalarTower T T₁ H₁'] [IsScalarTower C T₁ H₁']
    (q : H →ₗ[C] H') (q₁ : H₁ →ₗ[C₁] H₁') (j : H →ₗ[C] H₁) (j' : H' →ₗ[T] H₁')
    (hcomm : (q₁.restrictScalars C).comp j = (j'.restrictScalars C).comp q)
    (hj : IsBaseChange C₁ j) (hj' : IsBaseChange T₁ j') (hq : IsBaseChange T q) :
    IsBaseChange T₁ q₁ := by
  have h1 : IsBaseChange T₁ ((j'.restrictScalars C).comp q) := hq.comp hj'
  rw [← hcomm] at h1
  exact hj.of_comp h1


/-! ### The morphism induced on a second square -/

section SecondSquare

variable {A A' A₁ A₁' : Type u} [CommRing A] [CommRing A'] [CommRing A₁] [CommRing A₁']
  [Algebra A A'] [Algebra A A₁] [Algebra A₁ A₁'] [Algebra A' A₁'] [Algebra A A₁']
  [IsScalarTower A A₁ A₁'] [IsScalarTower A A' A₁']

/-- The two factorizations `A → A₁ → A₁'` and `A → A' → A₁'` of `A → A₁'` agree. -/
theorem algebraMap_comp_algebraMap_eq :
    (algebraMap A₁ A₁').comp (algebraMap A A₁) = (algebraMap A' A₁').comp (algebraMap A A') :=
  (IsScalarTower.algebraMap_eq A A₁ A₁').symm.trans (IsScalarTower.algebraMap_eq A A' A₁')

/-- **The morphism induced on a second square.** For `φ : K ⊗ᴸ_A A' ⟶ K'` and ring maps
`A → A₁ → A₁'`, `A → A' → A₁'` with the same composite, the morphism
`(K ⊗ᴸ_A A₁) ⊗ᴸ_{A₁} A₁' ≅ K ⊗ᴸ_A A₁' ≅ (K ⊗ᴸ_A A') ⊗ᴸ_{A'} A₁' ⟶ K' ⊗ᴸ_{A'} A₁'`
built from the composition isomorphisms of derived extension of scalars and `φ ⊗ᴸ A₁'`. This is
the datum with which the base-change map of the second square is formed at `K ⊗ᴸ_A A₁` and
`K' ⊗ᴸ_{A'} A₁'`. -/
def extendScalarsBaseChangeHom (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A₁ A₁')).functor.obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A A₁)).functor.obj K) ⟶
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A' A₁')).functor.obj K' :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
      (algebraMap A A₁) (algebraMap A₁ A₁')).hom.app K ≫
    eqToHom (congrArg (fun f : A →+* A₁' =>
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor.obj
        K) (algebraMap_comp_algebraMap_eq (A := A) (A' := A') (A₁ := A₁) (A₁' := A₁'))) ≫
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
      (algebraMap A A') (algebraMap A' A₁')).inv.app K ≫
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A' A₁')).functor.map φ

/-- The unfolding of `extendScalarsBaseChangeHom`. -/
theorem extendScalarsBaseChangeHom_eq (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') :
    extendScalarsBaseChangeHom (A₁ := A₁) (A₁' := A₁') K K' φ =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
          (algebraMap A A₁) (algebraMap A₁ A₁')).hom.app K ≫
        eqToHom (congrArg (fun f : A →+* A₁' =>
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            f).functor.obj K)
          (algebraMap_comp_algebraMap_eq (A := A) (A' := A') (A₁ := A₁) (A₁' := A₁'))) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
          (algebraMap A A') (algebraMap A' A₁')).inv.app K ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A' A₁')).functor.map φ :=
  rfl

/-- `extendScalarsBaseChangeHom` is natural in the target of `φ`. -/
theorem extendScalarsBaseChangeHom_comp (K : DerivedCategory (ModuleCat.{u} A))
    {K' L' : DerivedCategory (ModuleCat.{u} A')}
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (ψ : K' ⟶ L') :
    extendScalarsBaseChangeHom (A₁ := A₁) (A₁' := A₁') K L' (φ ≫ ψ) =
      extendScalarsBaseChangeHom (A₁ := A₁) (A₁' := A₁') K K' φ ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A' A₁')).functor.map ψ := by
  simp only [extendScalarsBaseChangeHom, Functor.map_comp, Category.assoc]

end SecondSquare

/-! ### Flat base change on cohomology -/

section FlatUnit

variable {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]

/-- **The unit of derived base change on cohomology.** For `Y ∈ D(S)` the `S`-linear map
`Hⁿ(Y) ⟶ Hⁿ(Y ⊗ᴸ_S T)` induced by the unit `Y ⟶ (Y ⊗ᴸ_S T)|_S` of Stacks 0GMT. -/
def derivedUnitHomologyMap (Y : DerivedCategory (ModuleCat.{u} S)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).obj Y ⟶
      (ModuleCat.restrictScalars (algebraMap S T)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) n).obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap S T)).functor.obj Y)) :=
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap S T)
  (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).map
      ((@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
        S T _ _ (algebraMap S T) _ _ D.functor D.comparison D.isLeftDerived).unit.app Y) ≫
    ((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategoryHomologyIso n).hom.app
      (D.functor.obj Y)

/-- A natural transformation at `X` is its component at an isomorphic `Y`, conjugated by the
isomorphism. -/
private theorem app_eq_map_hom_comp_app_comp_map_inv {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    α.app X = F.map e.hom ≫ α.app Y ≫ G.map e.inv := by
  rw [α.naturality_assoc, ← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id]

/-- On cohomology, the unit of flat derived base change is the unit `m ↦ 1 ⊗ m` of extension of
scalars, read through the identification `Hⁿ(Y ⊗ᴸ_S T) ≅ T ⊗_S Hⁿ(Y)`. -/
theorem derivedUnitHomologyMap_comp_homologyIso (hf : Module.Flat S T)
    (Y : DerivedCategory (ModuleCat.{u} S)) (n : ℤ) :
    derivedUnitHomologyMap (T := T) Y n ≫
        (ModuleCat.restrictScalars (algebraMap S T)).map
          ((CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, u, u}
            (algebraMap S T) (RingHom.flat_algebraMap_iff.mpr hf) n).hom.app Y) =
      (ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).unit.app
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).obj Y) := by
  let f := algebraMap S T
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f
  let adjD := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
    S T _ _ f _ _ D.functor D.comparison D.isLeftDerived
  let res := ModuleCat.restrictScalars.{u} f
  let ext := ModuleCat.extendScalars.{u, u, u} f
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} f
  let HS := DerivedCategory.homologyFunctor (ModuleCat.{u} S) n
  let HT := DerivedCategory.homologyFunctor (ModuleCat.{u} T) n
  let eH := CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, u, u} f
    (RingHom.flat_algebraMap_iff.mpr hf) n
  let mH := res.mapDerivedCategoryHomologyIso n
  -- both sides are components of natural transformations `HS ⟶ HS ⋙ ext ⋙ res`
  let α : HS ⟶ HS ⋙ ext ⋙ res :=
    Functor.whiskerRight adjD.unit HS ≫
      (Functor.associator D.functor res.mapDerivedCategory HS).hom ≫
      Functor.whiskerLeft D.functor mH.hom ≫
      (Functor.associator D.functor HT res).inv ≫
      Functor.whiskerRight eH.hom res ≫ (Functor.associator HS ext res).hom
  let β : HS ⟶ HS ⋙ ext ⋙ res := Functor.whiskerLeft HS adj.unit
  have hα : ∀ Y, α.app Y = derivedUnitHomologyMap (T := T) Y n ≫ res.map (eH.hom.app Y) := by
    intro Y
    simp only [α, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    rfl
  suffices h : α = β by
    have := congrArg (fun τ => τ.app Y) h
    simp only [hα] at this
    exact this
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ)) fun K => ?_
  rw [hα]
  let Q := DerivedCategory.Q (C := ModuleCat.{u} S)
  let QT := DerivedCategory.Q (C := ModuleCat.{u} T)
  let hf' : f.Flat := RingHom.flat_algebraMap_iff.mpr hf
  let : PreservesFiniteLimits ext := ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ hf'
  let : PreservesFiniteColimits ext := ModuleCat.extendScalars_preservesFiniteColimits _
  let cmp : Q ⋙ D.functor ⟶ ext.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q := D.comparison
  have : D.functor.IsLeftDerivedFunctor cmp
      (HomologicalComplex.quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ)) := D.isLeftDerived
  let hS := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} S) n
  let hT := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} T) n
  let eK := ext.mapHomologicalComplex (ComplexShape.up ℤ) |>.obj K
  let uK : K ⟶ (res.mapHomologicalComplex (ComplexShape.up ℤ)).obj eK :=
    (NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app K
  -- the four ingredients
  have hA : eH.hom.app (Q.obj K) = HT.map (cmp.app K) ≫ hT.hom.app eK ≫
      (ext.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
        ext.map (hS.inv.app K) :=
    CochainComplex.DerivedExtensionScalars.homologyNatIso_hom_app_Q.{u, u, u} f hf' K n
  have hB : mH.hom.app (D.functor.obj (Q.obj K)) ≫ res.map (HT.map (cmp.app K)) =
      HS.map (res.mapDerivedCategory.map (cmp.app K)) ≫ mH.hom.app (QT.obj eK) :=
    (mH.hom.naturality (cmp.app K)).symm
  have hC : HS.map (adjD.unit.app (Q.obj K)) ≫ HS.map (res.mapDerivedCategory.map (cmp.app K)) =
      HS.map (Q.map uK) ≫ HS.map (res.mapDerivedCategoryFactors.inv.app eK) := by
    rw [← HS.map_comp, ← HS.map_comp]
    exact congrArg HS.map
      (StacksDraft.DerivedHom.HomModuleBaseChange.unit_app_Q_comp_map_comparison D.functor cmp K)
  have hD : HS.map (res.mapDerivedCategoryFactors.inv.app eK) ≫ mH.hom.app (QT.obj eK) =
      hS.hom.app ((res.mapHomologicalComplex (ComplexShape.up ℤ)).obj eK) ≫
        (res.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app eK ≫
        res.map (hT.inv.app eK) := by
    rw [Functor.mapDerivedCategoryHomologyIso_hom_app_Q res n eK,
      ← Category.assoc, ← HS.map_comp, Iso.inv_hom_id_app, HS.map_id, Category.id_comp]
  have hE : HS.map (Q.map uK) ≫
      hS.hom.app ((res.mapHomologicalComplex (ComplexShape.up ℤ)).obj eK) =
      hS.hom.app K ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n).map uK :=
    hS.hom.naturality uK
  have hF : (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n).map uK ≫
      (res.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app eK ≫
        res.map ((ext.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K) =
      adj.unit.app
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n).obj K) := by
    refine
      (Stacks.ModulesOnACategory.TopCohomology.mapHomologicalComplexHomologyIso_hom_app_mapNatTrans
        (𝟭 (ModuleCat.{u} S)) ext res adj.unit (ComplexShape.up ℤ) n K).trans ?_
    refine (congrArg (fun t => t ≫ adj.unit.app (K.homology n))
      (CategoryTheory.ShortComplex.mapHomologyIso_id_hom (K.sc n))).trans (Category.id_comp _)
  have hG : adj.unit.app (HS.obj (Q.obj K)) =
      hS.hom.app K ≫ adj.unit.app
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n).obj K) ≫
          res.map (ext.map (hS.inv.app K)) := by
    exact app_eq_map_hom_comp_app_comp_map_inv adj.unit (hS.app K)
  change HS.map (adjD.unit.app (Q.obj K)) ≫ mH.hom.app (D.functor.obj (Q.obj K)) ≫
      res.map (eH.hom.app (Q.obj K)) = adj.unit.app (HS.obj (Q.obj K))
  rw [hA]
  refine Eq.trans ?_ hG.symm
  simp only [Functor.map_comp]
  rw [reassoc_of% hB, reassoc_of% hC, reassoc_of% hD]
  rw [← res.map_comp_assoc, Iso.inv_hom_id_app, res.map_id, Category.id_comp,
    reassoc_of% hE]
  have hF' : (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n).map uK ≫
      (res.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app eK ≫
        res.map ((ext.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app K ≫
          ext.map (hS.inv.app K)) =
      adj.unit.app
          ((HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (ComplexShape.up ℤ) n).obj K) ≫
        res.map (ext.map (hS.inv.app K)) := by
    have h := congrArg (fun t => t ≫ res.map (ext.map (hS.inv.app K))) hF
    simp only [Category.assoc] at h
    exact (congrArg (fun t => _ ≫ _ ≫ t) (res.map_comp _ _)).trans h
  exact congrArg (fun t => hS.hom.app K ≫ t) hF'

/-- **Flat base change on cohomology.** For a flat `S`-algebra `T` and `Y ∈ D(S)`, the unit of
derived base change exhibits `Hⁿ(Y ⊗ᴸ_S T)` as the base change `T ⊗_S Hⁿ(Y)`. -/
theorem isBaseChange_derivedUnitHomologyMap (hf : Module.Flat S T)
    (Y : DerivedCategory (ModuleCat.{u} S)) (n : ℤ) :
    letI : Module S ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) n).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap S T)).functor.obj Y)) :=
      Module.compHom _ (algebraMap S T)
    letI : IsScalarTower S T ((DerivedCategory.homologyFunctor (ModuleCat.{u} T) n).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap S T)).functor.obj Y)) :=
      IsScalarTower.of_compHom _ _ _
    IsBaseChange T (show (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).obj Y →ₗ[S]
        (DerivedCategory.homologyFunctor (ModuleCat.{u} T) n).obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap S T)).functor.obj Y) from (derivedUnitHomologyMap (T := T) Y n).hom) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat.{u} T) n).obj
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap S T)).functor.obj Y)
  let : Module S M := Module.compHom _ (algebraMap S T)
  let : IsScalarTower S T M := IsScalarTower.of_compHom _ _ _
  let N := (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).obj Y
  let eH := (CochainComplex.DerivedTensor.derivedExtensionScalarsHomologyIso.{u, u, u}
    (algebraMap S T) (RingHom.flat_algebraMap_iff.mpr hf) n).app Y
  let e : TensorProduct S T N ≃ₗ[T] M :=
    (StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv N).symm.trans
      eH.symm.toLinearEquiv
  refine IsBaseChange.of_equiv e fun x => ?_
  have h := congrArg (fun φ => φ.hom x)
    (derivedUnitHomologyMap_comp_homologyIso (T := T) hf Y n)
  change eH.inv.hom ((ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).unit.app N x) =
    (derivedUnitHomologyMap (T := T) Y n).hom x
  refine Eq.trans (congrArg eH.inv.hom h.symm) ?_
  exact congrArg (fun φ => φ.hom ((derivedUnitHomologyMap (T := T) Y n).hom x)) eH.hom_inv_id

end FlatUnit

/-! ### Pasting the comparison of Stacks 065Z along a factorization -/

section Paste

variable {R A R' P A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing P]
  [CommRing A']

/-- The comparison of Stacks 065Z for a commutative square of ring homomorphisms, at the chosen
models of derived extension of scalars. -/
abbrev ringHomSquareComparison (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    (sq : h.comp f = i.comp g) :
    (ModuleCat.restrictScalars f).mapDerivedCategory ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).functor ⟶
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h).functor ⋙
        (ModuleCat.restrictScalars i).mapDerivedCategory :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
    R A R' A' _ _ _ _ _ _ _ _ f g h i sq
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      h).isLeftDerived).2.1

/-- The adjunction of Stacks 0GMT for the chosen model of derived extension of scalars. -/
abbrev totalDerivedExtensionScalarsAdjunction (f : A →+* P) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor ⊣
      (ModuleCat.restrictScalars.{u} f).mapDerivedCategory :=
  @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u} A P _ _ f
    _ _ (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived

/-- The composition isomorphism of derived restriction of scalars, at the image of a complex. -/
private theorem derivedRestrictScalarsComp_hom_app_Q_comp {X Y W : Type u} [CommRing X]
    [CommRing Y] [CommRing W] (ρ : X →+* Y) (σ : Y →+* W)
    (L : CochainComplex (ModuleCat.{u} W) ℤ) :
    (StacksDraft.Perfect.derivedRestrictScalarsComp.{u, u} ρ σ).hom.app (DerivedCategory.Q.obj L) ≫
        (ModuleCat.restrictScalars.{u} (σ.comp ρ)).mapDerivedCategoryFactors.hom.app L =
      (ModuleCat.restrictScalars.{u} ρ).mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryFactors.hom.app L) ≫
        (ModuleCat.restrictScalars.{u} ρ).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars.{u} σ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp ρ σ).inv (ComplexShape.up ℤ)).app L) := by
  simp only [StacksDraft.Perfect.derivedRestrictScalarsComp, Localization.liftNatIso,
    Localization.Lifting.iso, Localization.liftNatTrans_app]
  simp
  rfl

/-- **Pasting the comparison of Stacks 065Z along `P → A'`.** For a commutative square
`R → A`, `R → R'`, `A → P`, `R' → P` and a further `σ : P → A'`, the comparison of the square with
corner `A'` is the comparison of the square with corner `P`, followed by the unit of derived base
change along `σ` and the composition isomorphisms of derived restriction and extension of
scalars. -/
theorem ringHomSquareComparison_paste (f : R →+* A) (g : R →+* R') (h₀ : A →+* P)
    (i₀ : R' →+* P) (sq₀ : h₀.comp f = i₀.comp g) (σ : P →+* A')
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (ringHomSquareComparison f g (σ.comp h₀) (σ.comp i₀)
        (by rw [RingHom.comp_assoc, sq₀, ← RingHom.comp_assoc])).app K =
      (ringHomSquareComparison f g h₀ i₀ sq₀).app K ≫
        (ModuleCat.restrictScalars i₀).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsAdjunction σ).unit.app
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              h₀).functor.obj K)) ≫
        (StacksDraft.Perfect.derivedRestrictScalarsComp.{u, u} i₀ σ).hom.app _ ≫
        (ModuleCat.restrictScalars (σ.comp i₀)).mapDerivedCategory.map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
            h₀ σ).hom.app K) := by
  let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g
  let T₀ := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h₀
  let Tσ := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} σ
  let Th := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (σ.comp h₀)
  let Df := (ModuleCat.restrictScalars.{u} f).mapDerivedCategory
  let D₀ := (ModuleCat.restrictScalars.{u} i₀).mapDerivedCategory
  let Dσ := (ModuleCat.restrictScalars.{u} σ).mapDerivedCategory
  let Di := (ModuleCat.restrictScalars.{u} (σ.comp i₀)).mapDerivedCategory
  let E := StacksDraft.Perfect.derivedRestrictScalarsComp.{u, u} i₀ σ
  let Cmp := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u} h₀ σ
  let adj := totalDerivedExtensionScalarsAdjunction σ
  let τ₀ := ringHomSquareComparison f g h₀ i₀ sq₀
  let sq : (σ.comp h₀).comp f = (σ.comp i₀).comp g := by
    rw [RingHom.comp_assoc, sq₀, ← RingHom.comp_assoc]
  let ψ : Df ⋙ Tg.functor ⟶ Th.functor ⋙ Di :=
    { app := fun K => τ₀.app K ≫ D₀.map (adj.unit.app (T₀.functor.obj K)) ≫
        E.hom.app (Tσ.functor.obj (T₀.functor.obj K)) ≫ Di.map (Cmp.hom.app K)
      naturality := fun X Y φ => by
        have h1 := τ₀.naturality φ
        have h2 := adj.unit.naturality (T₀.functor.map φ)
        have h3 := E.hom.naturality (Tσ.functor.map (T₀.functor.map φ))
        have h4 := Cmp.hom.naturality φ
        simp only [Functor.comp_map, Functor.id_map] at h1 h2 h3 h4 ⊢
        rw [reassoc_of% h1, ← D₀.map_comp_assoc, h2, D₀.map_comp_assoc, reassoc_of% h3,
          ← Di.map_comp, h4, Di.map_comp, Category.assoc, Category.assoc]
        simp only [Category.assoc]; rfl }
  have hψ : ψ.app K = τ₀.app K ≫ D₀.map (adj.unit.app (T₀.functor.obj K)) ≫
      E.hom.app _ ≫ Di.map (Cmp.hom.app K) := rfl
  have : (ModuleCat.extendScalars.{u, u, u} g).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u} g).isLeftAdjoint
  have : (ModuleCat.extendScalars.{u, u, u} (σ.comp h₀)).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u} (σ.comp h₀)).isLeftAdjoint
  have := Tg.isLeftDerived
  have := Th.isLeftDerived
  have key : ψ = ringHomSquareComparison f g (σ.comp h₀) (σ.comp i₀) sq := by
    refine @derivedBaseChangeComparison_snd_eq.{u, u, u, u, u} R A R' A' _ _ _ _ _ _ _ _
      f g (σ.comp h₀) (σ.comp i₀) sq Tg.functor Th.functor Tg.comparison Th.comparison
      Tg.isLeftDerived Th.isLeftDerived ψ fun L _ => ?_
    let c := ComplexShape.up ℤ
    let eL := ((ModuleCat.extendScalars.{u, u, u} h₀).mapHomologicalComplex c).obj L
    let QP := DerivedCategory.Q (C := ModuleCat.{u} P)
    -- the composition isomorphism against the comparisons
    have h1 : Cmp.hom.app (DerivedCategory.Q.obj L) ≫ Th.comparison.app L =
        Tσ.functor.map (T₀.comparison.app L) ≫ Tσ.comparison.app eL ≫
          (CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexComp.{u, u, u + 1}
            h₀ σ).inv.app L :=
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_comparison.{u, u}
        h₀ σ L).symm
    -- the unit along `σ` at the image of a complex
    have h4 : adj.unit.app (QP.obj eL) ≫ Dσ.map (Tσ.comparison.app eL) =
        DerivedCategory.Q.map
          (((ModuleCat.extendRestrictScalarsAdj.{u} σ).mapHomologicalComplex c).unit.app eL) ≫
          (ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryFactors.inv.app
            (((ModuleCat.extendScalars.{u, u, u} σ).mapHomologicalComplex c).obj eL) :=
      @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app.{u, u, u}
        P A' _ _ σ _ _ Tσ.functor Tσ.comparison Tσ.isLeftDerived eL
    -- the counit equation of the first square
    have : (ModuleCat.extendScalars.{u, u, u} h₀).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{u} h₀).isLeftAdjoint
    have h5 := @derivedBaseChangeComparison_snd_app_comp_counit.{u, u, u, u, u} R A R' P
      _ _ _ _ _ _ _ _ f g h₀ i₀ sq₀ Tg.functor T₀.functor Tg.comparison T₀.comparison
      Tg.isLeftDerived T₀.isLeftDerived L
    let e2L := ((ModuleCat.extendScalars.{u, u, u} σ).mapHomologicalComplex c).obj eL
    let ehL := ((ModuleCat.extendScalars.{u, u, u} (σ.comp h₀)).mapHomologicalComplex c).obj L
    let fσ := (ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryFactors
    let f₀ := (ModuleCat.restrictScalars.{u} i₀).mapDerivedCategoryFactors
    let fi := (ModuleCat.restrictScalars.{u} (σ.comp i₀)).mapDerivedCategoryFactors
    let xc : e2L ⟶ ehL :=
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp h₀ σ) c).inv.app L
    -- the composition of restrictions at the image of a complex
    let ρ := (Functor.mapHomologicalComplexCompIso (ModuleCat.restrictScalarsComp i₀ σ).symm c).hom
    have hE : ∀ Y : CochainComplex (ModuleCat.{u} A') ℤ,
        E.hom.app (DerivedCategory.Q.obj Y) ≫ fi.hom.app Y =
          D₀.map (fσ.hom.app Y) ≫
            f₀.hom.app (((ModuleCat.restrictScalars.{u} σ).mapHomologicalComplex c).obj Y) ≫
            DerivedCategory.Q.map (ρ.app Y) :=
      derivedRestrictScalarsComp_hom_app_Q_comp i₀ σ
    -- the underived identity
    let t₀ := (@derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
      R A R' P _ _ _ _ _ _ _ _ f g h₀ i₀ sq₀ Tg.functor T₀.functor Tg.comparison T₀.comparison
      Tg.isLeftDerived T₀.isLeftDerived).1
    let t := (@derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
      R A R' A' _ _ _ _ _ _ _ _ f g (σ.comp h₀) (σ.comp i₀) sq Tg.functor Th.functor
      Tg.comparison Th.comparison Tg.isLeftDerived Th.isLeftDerived).1
    let uσ := ((ModuleCat.extendRestrictScalarsAdj.{u} σ).mapHomologicalComplex c).unit.app eL
    have h8 : (NatTrans.mapHomologicalComplex t₀ c).app L ≫
        ((ModuleCat.restrictScalars.{u} i₀).mapHomologicalComplex c).map uσ ≫
        ((ModuleCat.restrictScalars.{u} i₀).mapHomologicalComplex c).map
          (((ModuleCat.restrictScalars.{u} σ).mapHomologicalComplex c).map xc) ≫ ρ.app ehL =
        (NatTrans.mapHomologicalComplex t c).app L := by
      ext n : 1
      refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
      have ht₀ := @derivedBaseChangeComparison_fst_app_tmul.{u, u, u, u, u} R A R' P
        _ _ _ _ _ _ _ _ f g h₀ i₀ _ _ sq₀ Tg.functor T₀.functor Tg.comparison T₀.comparison
        Tg.isLeftDerived T₀.isLeftDerived (L.X n) 1 m
      have ht := @derivedBaseChangeComparison_fst_app_tmul.{u, u, u, u, u} R A R' A'
        _ _ _ _ _ _ _ _ f g (σ.comp h₀) (σ.comp i₀) _ _ sq Tg.functor Th.functor Tg.comparison
        Th.comparison Tg.isLeftDerived Th.isLeftDerived (L.X n) 1 m
      rw [map_one] at ht₀ ht
      change (ModuleCat.extendScalarsComp h₀ σ).inv.app (L.X n)
          ((1 : A') ⊗ₜ[P, σ] (t₀.app (L.X n) ((1 : R') ⊗ₜ[R, g] m))) =
        t.app (L.X n) ((1 : R') ⊗ₜ[R, g] m)
      rw [ht₀, ht]
      exact (congrArg (fun y => ((ModuleCat.extendScalarsComp h₀ σ).inv.app (L.X n)).hom y)
        (ModuleCat.extendScalarsComp_hom_app_one_tmul h₀ σ (L.X n) m).symm).trans
          (congrArg (fun φ => φ.hom ((1 : A') ⊗ₜ[A, σ.comp h₀] m))
            ((ModuleCat.extendScalarsComp h₀ σ).hom_inv_id_app (L.X n)))
    -- objects and arrows of the chase, with canonical spellings
    let QA' := DerivedCategory.Q (C := ModuleCat.{u} A')
    let X0 := DerivedCategory.Q.obj L
    let Y1 := T₀.functor.obj X0
    let Y2 := QP.obj eL
    let Z1 := Tσ.functor.obj Y1
    let Z2 := Tσ.functor.obj Y2
    let Z3 := QA'.obj e2L
    let Z4 := QA'.obj ehL
    let a0 : Y1 ⟶ Y2 := T₀.comparison.app L
    let bσ : Z2 ⟶ Z3 := Tσ.comparison.app eL
    let x : Z3 ⟶ Z4 := QA'.map xc
    let cm : Z1 ⟶ Th.functor.obj X0 := Cmp.hom.app X0
    let ch : Th.functor.obj X0 ⟶ Z4 := Th.comparison.app L
    let η1 : Y1 ⟶ Dσ.obj Z1 := adj.unit.app Y1
    let η2 : Y2 ⟶ Dσ.obj Z2 := adj.unit.app Y2
    let rσ := (ModuleCat.restrictScalars.{u} σ).mapHomologicalComplex c
    let r₀ := (ModuleCat.restrictScalars.{u} i₀).mapHomologicalComplex c
    have e1 : cm ≫ ch = Tσ.functor.map a0 ≫ bσ ≫ x := h1
    have e2 : η1 ≫ Dσ.map (Tσ.functor.map a0) = a0 ≫ η2 := (adj.unit.naturality a0).symm
    have e3 : η2 ≫ Dσ.map bσ = QP.map uσ ≫ fσ.inv.app e2L := h4
    have e4 : fσ.inv.app e2L ≫ Dσ.map x = QP.map (rσ.map xc) ≫ fσ.inv.app ehL :=
      (fσ.inv.naturality xc).symm
    have e4' : fσ.inv.app e2L ≫ Dσ.map x ≫ fσ.hom.app ehL = QP.map (rσ.map xc) := by
      rw [reassoc_of% e4, Iso.inv_hom_id_app]
      exact Category.comp_id _
    have e5 : ∀ φ : Z1 ⟶ Z4, E.hom.app Z1 ≫ Di.map φ = D₀.map (Dσ.map φ) ≫ E.hom.app Z4 :=
      fun φ => (E.hom.naturality φ).symm
    have e6 : E.hom.app Z4 ≫ fi.hom.app ehL =
        D₀.map (fσ.hom.app ehL) ≫ f₀.hom.app (rσ.obj ehL) ≫
          DerivedCategory.Q.map (ρ.app ehL) := hE ehL
    have e7 : D₀.map (QP.map (uσ ≫ rσ.map xc)) ≫ f₀.hom.app (rσ.obj ehL) =
        f₀.hom.app eL ≫ DerivedCategory.Q.map (r₀.map (uσ ≫ rσ.map xc)) :=
      f₀.hom.naturality (uσ ≫ rσ.map xc)
    have hstar : D₀.map η1 ≫ E.hom.app Z1 ≫ Di.map cm ≫ Di.map ch ≫ fi.hom.app ehL =
        D₀.map a0 ≫ f₀.hom.app eL ≫ DerivedCategory.Q.map
          (r₀.map uσ ≫ r₀.map (rσ.map xc) ≫ ρ.app ehL) := by
      rw [← Di.map_comp_assoc, e1, reassoc_of% (e5 _), e6, ← D₀.map_comp_assoc,
        ← D₀.map_comp_assoc, Dσ.map_comp, Dσ.map_comp, reassoc_of% e2, reassoc_of% e3]
      simp only [Category.assoc]
      rw [e4', ← QP.map_comp, D₀.map_comp_assoc]
      refine congrArg (fun t => D₀.map a0 ≫ t) (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ DerivedCategory.Q.map (ρ.app ehL)) e7)).trans ?_)
      refine (Category.assoc _ _ _).trans (congrArg (fun t => f₀.hom.app eL ≫ t) ?_)
      exact (DerivedCategory.Q.map_comp _ _).symm.trans
        (congrArg DerivedCategory.Q.map ((congrArg (fun t => t ≫ ρ.app ehL)
          (r₀.map_comp uσ (rσ.map xc))).trans (Category.assoc _ _ _)))
    have h5' := congrArg (· ≫ DerivedCategory.Q.map
      (r₀.map uσ ≫ r₀.map (rσ.map xc) ≫ ρ.app ehL)) h5
    simp only [Category.assoc] at h5'
    have lhs : ψ.app (DerivedCategory.Q.obj L) ≫ Di.map ch ≫ fi.hom.app ehL =
        τ₀.app X0 ≫ D₀.map η1 ≫ E.hom.app Z1 ≫ Di.map cm ≫ Di.map ch ≫ fi.hom.app ehL := by
      simp only [ψ, Category.assoc]
      rfl
    have fin := lhs.trans ((congrArg (fun t => τ₀.app X0 ≫ t) hstar).trans (h5'.trans
      (congrArg (fun t => _ ≫ _ ≫ t)
        ((DerivedCategory.Q.map_comp _ _).symm.trans (congrArg DerivedCategory.Q.map h8)))))
    exact fin
  rw [← hψ, key]

end Paste

/-! ### The comparison for the tensor square of a flat algebra -/

section TensorSquare

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The tensor square `R → A`, `R → R'`, `A → A ⊗_R R'`, `R' → A ⊗_R R'` commutes. -/
theorem tensorSquare_comm :
    (algebraMap A (A ⊗[R] R')).comp (algebraMap R A) =
      (algebraMap R' (A ⊗[R] R')).comp (algebraMap R R') :=
  (IsScalarTower.algebraMap_eq R A (A ⊗[R] R')).symm.trans
    (IsScalarTower.algebraMap_eq R R' (A ⊗[R] R'))

/-- **Flat base change of the comparison of Stacks 065Z.** For a flat `R`-algebra `A`, the
comparison `K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A (A ⊗_R R')` is an isomorphism (Stacks 0661). -/
theorem isIso_ringHomSquareComparison_tensor [Module.Flat R A] :
    IsIso (ringHomSquareComparison (algebraMap R A) (algebraMap R R') (algebraMap A (A ⊗[R] R'))
      (algebraMap R' (A ⊗[R] R')) tensorSquare_comm) := by
  let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R R')
  let Th := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A (A ⊗[R] R'))
  let cg : DerivedCategory.Q ⋙ Tg.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := Tg.comparison
  let ch : DerivedCategory.Q ⋙ Th.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A (A ⊗[R] R'))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := Th.comparison
  have : Tg.functor.IsLeftDerivedFunctor cg
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := Tg.isLeftDerived
  have : Th.functor.IsLeftDerivedFunctor ch
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := Th.isLeftDerived
  exact derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u, u}
    (PseudoCoherence.torIndependent_of_flat (R := R) (A := A) (B := R')) Tg.functor Th.functor
    cg ch

end TensorSquare

/-! ### Cohomology of a composite of restrictions -/

section RestrictComp

variable {X Y W : Type u} [CommRing X] [CommRing Y] [CommRing W]

/-- On cohomology, the composition isomorphism of derived restriction of scalars is the
composite of the two cohomology comparisons. -/
theorem homology_derivedRestrictScalarsComp (ρ : X →+* Y) (σ : Y →+* W)
    (Z : DerivedCategory (ModuleCat.{u} W)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} X) n).map
          ((StacksDraft.Perfect.derivedRestrictScalarsComp.{u, u} ρ σ).hom.app Z) ≫
        ((ModuleCat.restrictScalars.{u} (σ.comp ρ)).mapDerivedCategoryHomologyIso n).hom.app Z =
      ((ModuleCat.restrictScalars.{u} ρ).mapDerivedCategoryHomologyIso n).hom.app
          ((ModuleCat.restrictScalars.{u} σ).mapDerivedCategory.obj Z) ≫
        (ModuleCat.restrictScalars.{u} ρ).map
          (((ModuleCat.restrictScalars.{u} σ).mapDerivedCategoryHomologyIso n).hom.app Z) := by
  let c := ComplexShape.up ℤ
  let rρ := ModuleCat.restrictScalars.{u} ρ
  let rσ := ModuleCat.restrictScalars.{u} σ
  let rc := ModuleCat.restrictScalars.{u} (σ.comp ρ)
  let HX := DerivedCategory.homologyFunctor (ModuleCat.{u} X) n
  let E := StacksDraft.Perfect.derivedRestrictScalarsComp.{u, u} ρ σ
  let ιρ := (rρ.mapDerivedCategoryHomologyIso n).hom
  let ισ := (rσ.mapDerivedCategoryHomologyIso n).hom
  let ιc := (rc.mapDerivedCategoryHomologyIso n).hom
  -- the identity at the image of a complex
  have hQ : ∀ L : CochainComplex (ModuleCat.{u} W) ℤ,
      HX.map (E.hom.app (DerivedCategory.Q.obj L)) ≫ ιc.app (DerivedCategory.Q.obj L) =
        ιρ.app (rσ.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
          rρ.map (ισ.app (DerivedCategory.Q.obj L)) := by
    intro L
    let fρ := rρ.mapDerivedCategoryFactors
    let fσ := rσ.mapDerivedCategoryFactors
    let fc := rc.mapDerivedCategoryFactors
    let HY := DerivedCategory.homologyFunctor (ModuleCat.{u} Y) n
    let hX := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} X) n
    let hY := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} Y) n
    let hW := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} W) n
    let τ := (ModuleCat.restrictScalarsComp ρ σ).hom
    let Lσ := (rσ.mapHomologicalComplex c).obj L
    have hE : E.hom.app (DerivedCategory.Q.obj L) =
        rρ.mapDerivedCategory.map (fσ.hom.app L) ≫ fρ.hom.app Lσ ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (ModuleCat.restrictScalarsComp ρ σ).inv c).app L) ≫ fc.inv.app L :=
      by
        refine (Iso.eq_comp_inv (fc.app L)).2 (derivedRestrictScalarsComp_hom_app_Q_comp ρ σ L)
          |>.trans ?_
        simp only [Category.assoc]
        rfl
    have hc := Functor.mapDerivedCategoryHomologyIso_hom_app_Q
      rc n L
    have hρ := Functor.mapDerivedCategoryHomologyIso_hom_app_Q
      rρ n Lσ
    have hσ := Functor.mapDerivedCategoryHomologyIso_hom_app_Q
      rσ n L
    have hρn : ιρ.app (rσ.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) =
        HX.map (rρ.mapDerivedCategory.map (fσ.hom.app L)) ≫ ιρ.app (DerivedCategory.Q.obj Lσ) ≫
          rρ.map (HY.map (fσ.inv.app L)) :=
      app_eq_map_hom_comp_app_comp_map_inv ιρ (fσ.app L)
    have hτ :=
      Stacks.ModulesOnACategory.TopCohomology.mapHomologicalComplexHomologyIso_hom_app_mapNatTrans
        rc rσ rρ τ c n L
    have hτid : ∀ M : ModuleCat.{u} W, τ.app M = 𝟙 (rc.obj M) := fun M => rfl
    have hinv : (HomologicalComplex.homologyFunctor (ModuleCat.{u} X) c n).map
          ((NatTrans.mapHomologicalComplex (ModuleCat.restrictScalarsComp ρ σ).inv c).app L) ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} X) c n).map
          ((NatTrans.mapHomologicalComplex τ c).app L) = 𝟙 _ := by
      rw [← Functor.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
        Iso.inv_hom_id, NatTrans.mapHomologicalComplex_id]
      exact (HomologicalComplex.homologyFunctor (ModuleCat.{u} X) c n).map_id _
    have hτ' := congrArg (fun t => (HomologicalComplex.homologyFunctor (ModuleCat.{u} X) c n).map
      ((NatTrans.mapHomologicalComplex (ModuleCat.restrictScalarsComp ρ σ).inv c).app L) ≫ t) hτ
    simp only [reassoc_of% hinv, hτid] at hτ'
    change HX.map (E.hom.app _) ≫ (rc.mapDerivedCategoryHomologyIso n).hom.app _ =
      (rρ.mapDerivedCategoryHomologyIso n).hom.app _ ≫
        rρ.map ((rσ.mapDerivedCategoryHomologyIso n).hom.app _)
    rw [hE, hc, hρn, hρ, hσ]
    simp only [Functor.map_comp, Category.assoc]
    have c1 : HX.map (fc.inv.app L) ≫
        (DerivedCategory.homologyFunctor (ModuleCat X) n).map
          (rc.mapDerivedCategoryFactors.hom.app L) = 𝟙 _ := by
      rw [← HX.map_comp, Iso.inv_hom_id_app]
      exact HX.map_id _
    have c2 : rρ.map ((DerivedCategory.homologyFunctorFactors (ModuleCat Y) n).inv.app Lσ) ≫
        rρ.map (HY.map (fσ.inv.app L)) ≫
        rρ.map ((DerivedCategory.homologyFunctor (ModuleCat Y) n).map
          (rσ.mapDerivedCategoryFactors.hom.app L)) ≫
        rρ.map ((DerivedCategory.homologyFunctorFactors (ModuleCat Y) n).hom.app
          ((rσ.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) = 𝟙 _ := by
      rw [← rρ.map_comp, ← rρ.map_comp, ← rρ.map_comp, ← HY.map_comp_assoc,
        Iso.inv_hom_id_app]
      refine (congrArg rρ.map ((congrArg (fun t => _ ≫ t ≫ _) (HY.map_id _)).trans ?_)).trans
        (rρ.map_id _)
      exact (congrArg (fun t => _ ≫ t) (Category.id_comp _)).trans (Iso.inv_hom_id_app _ _)
    have c3 := hX.hom.naturality
      ((NatTrans.mapHomologicalComplex (ModuleCat.restrictScalarsComp ρ σ).inv c).app L)
    simp only [Functor.comp_map] at c3
    rw [reassoc_of% c1, reassoc_of% c2, reassoc_of% c3]
    refine congrArg (fun t => _ ≫ _ ≫ _ ≫ t) ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ rc.map
      ((DerivedCategory.homologyFunctorFactors (ModuleCat W) n).inv.app L))
        ((congrArg (fun t => _ ≫ t) (Category.comp_id _)).symm.trans hτ'.symm)).trans
          (Category.assoc _ _ _))
  let e := DerivedCategory.Q.objObjPreimageIso Z
  let L := DerivedCategory.Q.objPreimage Z
  have hL : HX.map ((rσ.mapDerivedCategory ⋙ rρ.mapDerivedCategory).map e.hom) ≫
      HX.map (E.hom.app Z) ≫ ιc.app Z =
      (HX.map (E.hom.app (DerivedCategory.Q.obj L)) ≫ ιc.app (DerivedCategory.Q.obj L)) ≫
        rc.map ((DerivedCategory.homologyFunctor (ModuleCat.{u} W) n).map e.hom) := by
    rw [← HX.map_comp_assoc, E.hom.naturality e.hom, HX.map_comp, Category.assoc,
      Category.assoc]
    exact congrArg (fun t => _ ≫ t) (ιc.naturality e.hom)
  have hR : HX.map ((rσ.mapDerivedCategory ⋙ rρ.mapDerivedCategory).map e.hom) ≫
      ιρ.app (rσ.mapDerivedCategory.obj Z) ≫ rρ.map (ισ.app Z) =
      (ιρ.app (rσ.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
          rρ.map (ισ.app (DerivedCategory.Q.obj L))) ≫
        rc.map ((DerivedCategory.homologyFunctor (ModuleCat.{u} W) n).map e.hom) := by
    have h1 := ιρ.naturality (rσ.mapDerivedCategory.map e.hom)
    have h2 := ισ.naturality e.hom
    simp only [Functor.comp_map] at h1 h2 ⊢
    rw [reassoc_of% h1, ← rρ.map_comp, h2, rρ.map_comp]
    exact (Category.assoc _ _ _).symm
  have hiso : IsIso (HX.map ((rσ.mapDerivedCategory ⋙ rρ.mapDerivedCategory).map e.hom)) :=
    inferInstance
  refine (cancel_epi (HX.map ((rσ.mapDerivedCategory ⋙ rρ.mapDerivedCategory).map e.hom))).1 ?_
  exact hL.trans ((congrArg (fun t => t ≫ rc.map
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} W) n).map e.hom)) (hQ L)).trans hR.symm)

end RestrictComp

end RingTheory.TorIndependence

end
