module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap

/-!
# The base-change map on cohomology, constructed rather than chosen

`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap` establishes that for
a commutative square of commutative rings `R → A`, `R → R'`, `A → A'`, `R' → A'`, an object `K`
of `D(A)`, an object `K'` of `D(A')` and a morphism `φ : K ⊗ᴸ_A A' ⟶ K'` there is a *unique*
`A'`-linear map

`A' ⊗_{A ⊗_R R'} H^n(K ⊗ᴸ_R R') ⟶ H^n(K')`

taking `1 ⊗ m` to the comparison of Stacks 065Z followed by `φ`. That is an existence statement,
and the declarations there extract the map and the `A ⊗_R R'`-action on its source from it by
`Classical.choose`.

This file builds both outright. The `A ⊗_R R'`-module structure is `TensorProduct.Algebra.module`
for the two commuting actions, and the map is the image of an `A ⊗_R R'`-linear comparison under
the extension/restriction adjunction. Nothing here chooses data from an existence statement, so
the constructions can be unfolded and are available to consumers which must avoid choice in their
own definitions.

## Main definitions

* `RingTheory.TorIndependence.baseChangeCohomologyAction`: the action of `A` on the cohomology of
  the derived base change, by derived base change of scalar multiplication.
* `RingTheory.TorIndependence.baseChangeCohomologyModule`: the `A ⊗_R R'`-module structure built
  from that action and the ambient `R'`-action.
* `RingTheory.TorIndependence.baseChangeCohomologyCat`: the cohomology of the derived base change
  as an object of `ModuleCat (A ⊗_R R')`.
* `RingTheory.TorIndependence.ringBaseChangeCohomologyMap`: the base-change map on cohomology.

## Main results

* `RingTheory.TorIndependence.baseChangeCohomologyModule_includeRight_smul` and
  `RingTheory.TorIndependence.baseChangeCohomologyModule_includeLeft_smul`: the two restrictions
  of the constructed action.
* `RingTheory.TorIndependence.baseChangeCohomologyCat_eq`: the constructed object is the chosen
  one, `baseChangeCohomology`.
* `RingTheory.TorIndependence.ringBaseChangeCohomologyMap_one_tmul`: the characterizing formula,
  the value of the map on `1 ⊗ m`.
* `RingTheory.TorIndependence.ringBaseChangeCohomologyMap_unique`: any map with that formula is
  the constructed one, so it is the map of
  `exists_unique_ringBaseChangeCohomologyMap`.
* `RingTheory.TorIndependence.ringBaseChangeCohomologyMap_comp`: naturality in `K'`.

## Implementation notes

The underlying additive group of `baseChangeCohomologyCat` is `baseChangeCohomologyOverBase`
unchanged, exactly as for `baseChangeCohomology`: only the action is new. `Module.compHom` is used
rather than an `Algebra` instance because the action of `A` is not an algebra structure on the
cohomology but the action of `A` through derived base change of multiplication by a scalar.

That the action of `A` restricted along `R → A` agrees with the action of `R` through `R'` is
read off the already-available description of the chosen action rather than reproved: the two
composites `R → A → A ⊗_R R'` and `R → R' → A ⊗_R R'` are equal because `(r • 1) ⊗ 1 = 1 ⊗ (r • 1)`
in a tensor product over `R`.

Extension of scalars puts the new ring on the left of the tensor product, which interchanges the
two factors against the displayed formula of the source.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open scoped ChangeOfRings

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

/-! ### The action of the left tensor factor -/

section Action

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- **The action of `A` on the cohomology of a derived base change.** An element `a` of `A` acts
by the derived base change of multiplication by `a` on `K`, read on cohomology over `R'`. This is
the action which, together with the ambient `R'`-action, assembles to the `A ⊗_R R'`-action on the
source of the base-change map. -/
def baseChangeCohomologyAction (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    A →+* Module.End R' (baseChangeCohomologyOverBase (R := R) (R' := R') K n) :=
  let G := (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory ⋙
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).functor ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  { toFun := fun a => (G.map (a • (𝟙 K))).hom
    map_one' := by
      rw [one_smul, G.map_id]
      rfl
    map_mul' := fun a b => by
      have hab : (a * b) • (𝟙 K) = (b • (𝟙 K)) ≫ (a • (𝟙 K)) := by
        simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
      rw [hab, G.map_comp]
      rfl
    map_zero' := by
      rw [zero_smul, G.map_zero]
      rfl
    map_add' := fun a b => by
      rw [add_smul, G.map_add]
      rfl }

/-- The action of `a : A` on the base-changed cohomology is the map induced on `n`-th cohomology
over `R'` by the derived base change of multiplication by `a` on `K`. -/
theorem baseChangeCohomologyAction_apply_eq (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (a : A) (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')
    baseChangeCohomologyAction (R := R) (R' := R') K n a m =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        (T.functor.map ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
          (a • (𝟙 K))))).hom m :=
  rfl

/-- In `A ⊗_R R'` the two images of a scalar `r` of `R` agree: `(r • 1) ⊗ 1 = 1 ⊗ (r • 1)`. -/
theorem includeLeft_algebraMap_eq_includeRight_algebraMap (r : R) :
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (algebraMap R A r) : A ⊗[R] R') =
      Algebra.TensorProduct.includeRight (algebraMap R R' r) := by
  show (algebraMap R A r) ⊗ₜ[R] (1 : R') = (1 : A) ⊗ₜ[R] (algebraMap R R' r)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  exact TensorProduct.smul_tmul r (1 : A) (1 : R')

/-- The action of `A` restricted along `R → A` is multiplication by the image of the scalar in
`R'`. This is what makes the `A`- and `R'`-actions assemble into an action of `A ⊗_R R'`. -/
theorem baseChangeCohomologyAction_algebraMap (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (r : R) :
    baseChangeCohomologyAction (R := R) (R' := R') K n (algebraMap R A r) =
      algebraMap R R' r •
        (1 : Module.End R' (baseChangeCohomologyOverBase (R := R) (R' := R') K n)) := by
  classical
  let := Classical.choose
    (exists_unique_baseChangeCohomologyModule (R := R) (R' := R') K n).exists
  refine LinearMap.ext fun m => ?_
  calc baseChangeCohomologyAction (R := R) (R' := R') K n (algebraMap R A r) m
      = (Algebra.TensorProduct.includeLeft (R := R) (S := R)
          (algebraMap R A r) : A ⊗[R] R') • m :=
        (baseChangeCohomology_includeLeft_smul (R := R) (R' := R') K n (algebraMap R A r) m).symm
    _ = (Algebra.TensorProduct.includeRight (algebraMap R R' r) : A ⊗[R] R') • m := by
        rw [includeLeft_algebraMap_eq_includeRight_algebraMap (A := A) (R' := R') r]
    _ = algebraMap R R' r •
          (show baseChangeCohomologyOverBase (R := R) (R' := R') K n from m) :=
        baseChangeCohomology_includeRight_smul (R := R) (R' := R') K n (algebraMap R R' r) m
    _ = (algebraMap R R' r •
          (1 : Module.End R' (baseChangeCohomologyOverBase (R := R) (R' := R') K n))) m := rfl

/-! ### The module structure over the ordinary tensor product -/

/-- The `A ⊗_R R'`-module structure on the cohomology of a derived base change, together with
its two defining restrictions. Packaging the structure with its properties keeps the local
`A`- and `R`-actions, which only exist inside this construction, out of the statements of the
properties. -/
def baseChangeCohomologyModuleData (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    { M : Module (A ⊗[R] R') (baseChangeCohomologyOverBase (R := R) (R' := R') K n) //
        letI := M
        (∀ (r : R') (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n),
            (Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m = r • m) ∧
        (∀ (a : A) (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n),
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • m =
              baseChangeCohomologyAction (R := R) (R' := R') K n a m) } :=
  let H := baseChangeCohomologyOverBase (R := R) (R' := R') K n
  let ρ := baseChangeCohomologyAction (R := R) (R' := R') K n
  letI : Module R H := Module.compHom H (algebraMap R R')
  letI : IsScalarTower R R' H := IsScalarTower.of_compHom _ _ _
  letI : Module A H := Module.compHom H ρ
  letI : IsScalarTower R A H := ⟨fun r a m => by
    change ρ (r • a) m = algebraMap R R' r • ρ a m
    rw [Algebra.smul_def, map_mul, baseChangeCohomologyAction_algebraMap]
    rfl⟩
  letI : SMulCommClass A R' H := ⟨fun a r m => (ρ a).map_smul r m⟩
  ⟨TensorProduct.Algebra.module,
    fun r m => by
      change (1 : A) • r • m = r • m
      exact one_smul _ _,
    fun a m => by
      change ρ a ((1 : R') • m) = ρ a m
      rw [one_smul]⟩

/-- **The `A ⊗_R R'`-module structure on the cohomology of a derived base change.** The right
tensor factor acts by the `R'`-structure already present and the left factor through derived base
change of scalar multiplication on `K`. -/
@[instance_reducible]
def baseChangeCohomologyModule (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    Module (A ⊗[R] R') (baseChangeCohomologyOverBase (R := R) (R' := R') K n) :=
  (baseChangeCohomologyModuleData (R := R) (R' := R') K n).1

/-- The right tensor factor acts by the base-change `R'`-action already present. -/
theorem baseChangeCohomologyModule_includeRight_smul (K : DerivedCategory (ModuleCat.{u} A))
    (n : ℤ) (r : R') (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    letI := baseChangeCohomologyModule (R := R) (R' := R') K n
    (Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m = r • m :=
  (baseChangeCohomologyModuleData (R := R) (R' := R') K n).2.1 r m

/-- The left tensor factor acts by derived base change of scalar multiplication on `K`. -/
theorem baseChangeCohomologyModule_includeLeft_smul (K : DerivedCategory (ModuleCat.{u} A))
    (n : ℤ) (a : A) (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    letI := baseChangeCohomologyModule (R := R) (R' := R') K n
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • m =
      baseChangeCohomologyAction (R := R) (R' := R') K n a m :=
  (baseChangeCohomologyModuleData (R := R) (R' := R') K n).2.2 a m

/-- **The cohomology of a derived base change as a module over the ordinary tensor product.**
The underlying additive group is `baseChangeCohomologyOverBase` unchanged; only the action is
new. This is the source of the base-change map, before extension of scalars to `A'`. -/
def baseChangeCohomologyCat (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    ModuleCat.{u} (A ⊗[R] R') :=
  letI := baseChangeCohomologyModule (R := R) (R' := R') K n
  ModuleCat.of (A ⊗[R] R') (baseChangeCohomologyOverBase (R := R) (R' := R') K n)

/-- The constructed action is the chosen one of `baseChangeCohomology`: both restrict to the
ambient `R'`-action and to the action of `A` by derived base change of scalar multiplication, and
`exists_unique_baseChangeCohomologyModule` says such an action is unique. -/
theorem baseChangeCohomologyModule_eq (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    baseChangeCohomologyModule (R := R) (R' := R') K n =
      Classical.choose
        (exists_unique_baseChangeCohomologyModule (R := R) (R' := R') K n).exists :=
  (exists_unique_baseChangeCohomologyModule (R := R) (R' := R') K n).unique
    ⟨baseChangeCohomologyModule_includeRight_smul (R := R) (R' := R') K n,
      baseChangeCohomologyModule_includeLeft_smul (R := R) (R' := R') K n⟩
    (Classical.choose_spec
      (exists_unique_baseChangeCohomologyModule (R := R) (R' := R') K n).exists)

end Action

/-! ### The base-change map on cohomology -/

section Map

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A']
  [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- The ring homomorphism `A ⊗_R R' ⟶ A'` of a commutative square of commutative rings, over
which the base-change map is `A'`-linear. -/
def baseChangeTensorRingMap : (A ⊗[R] R') →+* A' :=
  (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R A A')
    (IsScalarTower.toAlgHom R R' A') (fun _ _ => Commute.all _ _)).toRingHom

/-- The ring map `A ⊗_R R' ⟶ A'` sends `a ⊗ r` to the product of the images of `a` and `r`. -/
theorem baseChangeTensorRingMap_tmul (a : A) (r : R') :
    baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') (a ⊗ₜ[R] r) =
      algebraMap A A' a * algebraMap R' A' r :=
  rfl

/-- The commutativity of the square of rings, as an equality of composites. -/
theorem baseChangeSquare :
    (algebraMap A A').comp (algebraMap R A) = (algebraMap R' A').comp (algebraMap R R') :=
  (IsScalarTower.algebraMap_eq R A A').symm.trans (IsScalarTower.algebraMap_eq R R' A')

/-- **The comparison of Stacks 065Z for a commutative square of commutative rings.** The natural
transformation from "restrict to `R`, then derived base change to `R'`" to "derived base change
to `A'`, then restrict to `R'`". -/
def squareDerivedComparison :
    (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R R')).functor ⟶
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A A')).functor ⋙
        (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
    R A R' A' _ _ _ _ _ _ _ _ (algebraMap R A) (algebraMap R R') (algebraMap A A')
    (algebraMap R' A') baseChangeSquare
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).comparison
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')).isLeftDerived
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).isLeftDerived).2.1

/-- **The base-change comparison on cohomology, before adjunction.** The `R'`-linear map
`H^n(K ⊗ᴸ_R R') ⟶ H^n(K')` given by the comparison of Stacks 065Z followed by `φ`, read through
the identification of cohomology with restriction of scalars. -/
def cohomologyComparisonMap
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) :
    baseChangeCohomologyOverBase (R := R) (R' := R') K n ⟶
      (ModuleCat.restrictScalars (algebraMap R' A')).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
      ((squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app K ≫
        (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map φ) ≫
    ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso n).hom.app K'

variable (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
  (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ)

/-- The comparison carries the action of the right tensor factor to multiplication by its image
in `A'`: that is its `R'`-linearity. -/
theorem cohomologyComparisonMap_includeRight_smul (r : R')
    (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    letI := baseChangeCohomologyModule (R := R) (R' := R') K n
    (cohomologyComparisonMap (R := R) (R' := R') K K' φ n).hom
        ((Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m) =
      algebraMap R' A' r •
        (show (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K' from
          (cohomologyComparisonMap (R := R) (R' := R') K K' φ n).hom m) :=
  let := baseChangeCohomologyModule (R := R) (R' := R') K n
  Eq.trans
    (congrArg (fun x => (cohomologyComparisonMap (R := R) (R' := R') K K' φ n).hom x)
      (baseChangeCohomologyModule_includeRight_smul (R := R) (R' := R') K n r m))
    ((cohomologyComparisonMap (R := R) (R' := R') K K' φ n).hom.map_smul r m)

/-- The comparison carries the action of the left tensor factor to multiplication by its image in
`A'`. Together with `cohomologyComparisonMap_includeRight_smul` this makes the comparison linear
over `A ⊗_R R'`. -/
theorem cohomologyComparisonMap_includeLeft_smul (a : A)
    (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    letI := baseChangeCohomologyModule (R := R) (R' := R') K n
    (cohomologyComparisonMap (R := R) (R' := R') K K' φ n).hom
        ((Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • m) =
      algebraMap A A' a •
        (show (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K' from
          (cohomologyComparisonMap (R := R) (R' := R') K K' φ n).hom m) := by
  let := baseChangeCohomologyModule (R := R) (R' := R') K n
  let f : R →+* A := algebraMap R A
  let g : R →+* R' := algebraMap R R'
  let h : A →+* A' := algebraMap A A'
  let i : R' →+* A' := algebraMap R' A'
  let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g
  let Th := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h
  let C := (ModuleCat.restrictScalars i).mapDerivedCategory
  let J := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let J' := DerivedCategory.homologyFunctor (ModuleCat.{u} A') n
  let τ := squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')
  let α := τ.app K ≫ C.map φ
  let H' := J'.obj K'
  have hq : cohomologyComparisonMap (R := R) (R' := R') K K' φ n =
      J.map α ≫ ((ModuleCat.restrictScalars i).mapDerivedCategoryHomologyIso n).hom.app K' := rfl
  have hφ : Th.functor.map (a • 𝟙 K) ≫ φ = φ ≫ (h a • 𝟙 K') := by
    rw [derivedExtension_scalar]
    show (h a • 𝟙 (Th.functor.obj K)) ≫ φ = φ ≫ (h a • 𝟙 K')
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  have hd : ((ModuleCat.restrictScalars f).mapDerivedCategory ⋙ Tg.functor).map
      (a • 𝟙 K) ≫ α = α ≫ C.map (h a • 𝟙 K') := by
    dsimp only [α]
    rw [← Category.assoc, τ.naturality]
    show (τ.app K ≫ C.map (Th.functor.map (a • 𝟙 K))) ≫ C.map φ = _
    rw [Category.assoc, ← C.map_comp, hφ, C.map_comp, Category.assoc]
  have hn := ((ModuleCat.restrictScalars i).mapDerivedCategoryHomologyIso n).hom.naturality
    (h a • 𝟙 K')
  let := DerivedCategory.homologyFunctor_linear (C := ModuleCat.{u} A') A' n
  have hnat : J.map (((ModuleCat.restrictScalars f).mapDerivedCategory ⋙ Tg.functor).map
        (a • 𝟙 K)) ≫ cohomologyComparisonMap (R := R) (R' := R') K K' φ n =
      cohomologyComparisonMap (R := R) (R' := R') K K' φ n ≫
        (ModuleCat.restrictScalars i).map (h a • 𝟙 H') := by
    rw [hq, ← Category.assoc, ← J.map_comp, hd, J.map_comp, Category.assoc]
    show _ ≫ ((C ⋙ J).map (h a • 𝟙 K') ≫
      ((ModuleCat.restrictScalars i).mapDerivedCategoryHomologyIso n).hom.app K') = _
    rw [hn]
    dsimp only [Functor.comp_map]
    rw [Functor.map_smul, J'.map_id]
    exact (Category.assoc _ _ _).symm
  exact Eq.trans
    (congrArg (fun x => (cohomologyComparisonMap (R := R) (R' := R') K K' φ n).hom x)
      (baseChangeCohomologyModule_includeLeft_smul (R := R) (R' := R') K n a m))
    (congrArg (fun l => l.hom m) hnat)

/-- The base-change comparison, as a map of `A ⊗_R R'`-modules. -/
def cohomologyComparisonLinearMap :
    baseChangeCohomologyCat (R := R) (R' := R') K n ⟶
      (ModuleCat.restrictScalars
          (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'))).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
  letI := baseChangeCohomologyModule (R := R) (R' := R') K n
  let H' := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K'
  let k := baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')
  let q := cohomologyComparisonMap (R := R) (R' := R') K K' φ n
  ModuleCat.ofHom (X := baseChangeCohomologyCat (R := R) (R' := R') K n)
      (Y := (ModuleCat.restrictScalars k).obj H')
    (show baseChangeCohomologyCat (R := R) (R' := R') K n →ₗ[A ⊗[R] R']
        ((ModuleCat.restrictScalars k).obj H') from
      { toFun := fun m => q.hom m
        map_add' := fun x y => q.hom.map_add x y
        map_smul' := fun t m => by
          change q.hom (t • m) = k t • (show H' from q.hom m)
          induction t using TensorProduct.induction_on with
          | zero =>
            rw [zero_smul, k.map_zero]
            exact q.hom.map_zero.trans (zero_smul A' (show H' from q.hom m)).symm
          | add x y hx hy =>
            rw [add_smul, k.map_add]
            exact (q.hom.map_add _ _).trans
              ((congrArg₂ (· + ·) hx hy).trans
                (add_smul (k x) (k y) (show H' from q.hom m)).symm)
          | tmul a r =>
            have ht : a ⊗ₜ[R] r =
                (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') *
                  Algebra.TensorProduct.includeRight r := by
              change a ⊗ₜ[R] r = (a ⊗ₜ[R] 1) * (1 ⊗ₜ[R] r)
              rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
            rw [ht, mul_smul]
            refine Eq.trans
              (cohomologyComparisonMap_includeLeft_smul (R := R) (R' := R') K K' φ n a _) ?_
            refine Eq.trans (congrArg (fun z => algebraMap A A' a • z)
              (cohomologyComparisonMap_includeRight_smul (R := R) (R' := R') K K' φ n r _)) ?_
            rw [← ht]
            exact (mul_smul _ _ _).symm })

/-- **Stacks 0DJ7 at the level of rings, constructed.** The base-change map on cohomology
`A' ⊗_{A ⊗_R R'} H^n(K ⊗ᴸ_R R') ⟶ H^n(K')` attached to `φ : K ⊗ᴸ_A A' ⟶ K'`, obtained by
adjunction from the `A ⊗_R R'`-linear comparison `cohomologyComparisonLinearMap`. -/
def ringBaseChangeCohomologyMap :
    (ModuleCat.extendScalars
          (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'))).obj
        (baseChangeCohomologyCat (R := R) (R' := R') K n) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K' :=
  ((ModuleCat.extendRestrictScalarsAdj
      (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'))).homEquiv
    (baseChangeCohomologyCat (R := R) (R' := R') K n)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K')).symm
    (cohomologyComparisonLinearMap (R := R) (R' := R') K K' φ n)

/-- **The characterizing formula for the base-change map.** Its value on `1 ⊗ m` is the
comparison of Stacks 065Z followed by `φ`, which is exactly the normalization pinning the map of
`exists_unique_ringBaseChangeCohomologyMap`. -/
theorem ringBaseChangeCohomologyMap_one_tmul
    (m : baseChangeCohomologyCat (R := R) (R' := R') K n) :
    (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n).hom
        ((1 : A') ⊗ₜ[A ⊗[R] R',
          baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')] m) =
      (cohomologyComparisonMap (R := R) (R' := R') K K' φ n).hom
        (show baseChangeCohomologyOverBase (R := R) (R' := R') K n from m) := by
  let k := baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')
  let H := baseChangeCohomologyCat (R := R) (R' := R') K n
  let H' := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K'
  let adj := ModuleCat.extendRestrictScalarsAdj k
  let l := cohomologyComparisonLinearMap (R := R) (R' := R') K K' φ n
  have hunit := congrArg (fun z => z.hom m)
    (adj.homEquiv_unit (f := ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n))
  have hev := congrArg (fun z => z.hom m) ((adj.homEquiv H H').apply_symm_apply l)
  exact hunit.symm.trans hev

end Map

end RingTheory.TorIndependence

end
