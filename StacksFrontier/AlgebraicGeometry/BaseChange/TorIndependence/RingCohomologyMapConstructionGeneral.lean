module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapConstruction

/-!
# The base-change map on cohomology, constructed, at an arbitrary model of the derived category

`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapConstruction` builds,
for a commutative square of commutative rings `R → A`, `R → R'`, `A → A'`, `R' → A'`, an object
`K` of `D(A)`, an object `K'` of `D(A')` and `φ : K ⊗ᴸ_A A' ⟶ K'`, the `A ⊗_R R'`-module
structure on `H^n(K ⊗ᴸ_R R')` and the `A'`-linear base-change map

`A' ⊗_{A ⊗_R R'} H^n(K ⊗ᴸ_R R') ⟶ H^n(K')`

of Stacks 0DJ7 outright, without choice. Every statement there is elaborated under
`attribute [local instance] HasDerivedCategory.standard`, so the standard model of each of the
four derived categories is part of its type.

The existence and uniqueness statements it refines, in
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap`, are stated at an
arbitrary model. This file carries out the construction at an arbitrary choice of the four models,
with the model binders written in the binder list of every declaration. The consumer that needs
this generality is the affine reduction of Stacks 0DJ8, which reads the comparison of the chart of
a Cartesian square at the locally small model of
`StacksFrontier.Homology.DerivedCategory.LocallySmall` (the global instance on `ModuleCat R`).

The ring homomorphism `RingTheory.TorIndependence.baseChangeTensorRingMap`, the identity
`RingTheory.TorIndependence.baseChangeSquare` and
`RingTheory.TorIndependence.includeLeft_algebraMap_eq_includeRight_algebraMap` mention no derived
category and are used from the base module as they stand.

## Main definitions

* `RingTheory.TorIndependence.baseChangeCohomologyActionGeneral`: the action of `A` on the
  cohomology of the derived base change, by derived base change of scalar multiplication.
* `RingTheory.TorIndependence.baseChangeCohomologyModuleGeneral` and
  `RingTheory.TorIndependence.baseChangeCohomologyCatGeneral`: the `A ⊗_R R'`-module structure
  and the resulting object of `ModuleCat (A ⊗_R R')`.
* `RingTheory.TorIndependence.squareDerivedComparisonGeneral`: the comparison of Stacks 065Z for
  the square, as a natural transformation.
* `RingTheory.TorIndependence.ringComparison`: the composition `K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A' ⟶ K'`,
  read in `D(R')`.
* `RingTheory.TorIndependence.cohomologyComparisonMapGeneral` and
  `RingTheory.TorIndependence.cohomologyComparisonLinearMapGeneral`: its `n`-th cohomology, as a
  map of `R'`-modules and of `A ⊗_R R'`-modules.
* `RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral`: the base-change map on
  cohomology.

## Main results

* `RingTheory.TorIndependence.ringBaseChangeCohomologyMapGeneral_one_tmul`: the characterizing
  formula, the value of the map on `1 ⊗ m`.
* `RingTheory.TorIndependence.ringComparison_map` and
  `RingTheory.TorIndependence.cohomologyComparisonMapGeneral_map`: both comparisons are natural
  in the complex over `A`, the morphism to `K'` being transported along the derived base change.

## References

* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open scoped ChangeOfRings

universe u w

namespace RingTheory.TorIndependence

/-! ### The action of the left tensor factor -/

section Action

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- **The action of `A` on the cohomology of a derived base change.** An element `a` of `A` acts
by the derived base change of multiplication by `a` on `K`, read on cohomology over `R'`. This is
the action which, together with the ambient `R'`-action, assembles to the `A ⊗_R R'`-action on the
source of the base-change map. -/
def baseChangeCohomologyActionGeneral
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
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

/-- An element `a` of `A` acts on `H^n(K ⊗ᴸ_R R')` by the `n`-th cohomology of the derived base
change to `R'` of multiplication by `a` on `K`, restricted to `R`. -/
theorem baseChangeCohomologyActionGeneral_apply_eq
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (a : A) (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    let T := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R R')
    baseChangeCohomologyActionGeneral (R := R) (R' := R') K n a m =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
        (T.functor.map ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
          (a • (𝟙 K))))).hom m :=
  rfl

/-- The action of `A` restricted along `R → A` is multiplication by the image of the scalar in
`R'`. This is what makes the `A`- and `R'`-actions assemble into an action of `A ⊗_R R'`. -/
theorem baseChangeCohomologyActionGeneral_algebraMap
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (r : R) :
    baseChangeCohomologyActionGeneral (R := R) (R' := R') K n (algebraMap R A r) =
      algebraMap R R' r •
        (1 : Module.End R' (baseChangeCohomologyOverBase (R := R) (R' := R') K n)) := by
  classical
  let := Classical.choose
    (exists_unique_baseChangeCohomologyModule (R := R) (R' := R') K n).exists
  refine LinearMap.ext fun m => ?_
  calc baseChangeCohomologyActionGeneral (R := R) (R' := R') K n (algebraMap R A r) m
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
def baseChangeCohomologyModuleDataGeneral
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    { M : Module (A ⊗[R] R') (baseChangeCohomologyOverBase (R := R) (R' := R') K n) //
        letI := M
        (∀ (r : R') (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n),
            (Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m = r • m) ∧
        (∀ (a : A) (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n),
            (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • m =
              baseChangeCohomologyActionGeneral (R := R) (R' := R') K n a m) } :=
  let H := baseChangeCohomologyOverBase (R := R) (R' := R') K n
  let ρ := baseChangeCohomologyActionGeneral (R := R) (R' := R') K n
  letI : Module R H := Module.compHom H (algebraMap R R')
  letI : IsScalarTower R R' H := IsScalarTower.of_compHom _ _ _
  letI : Module A H := Module.compHom H ρ
  letI : IsScalarTower R A H := ⟨fun r a m => by
    change ρ (r • a) m = algebraMap R R' r • ρ a m
    rw [Algebra.smul_def, map_mul, baseChangeCohomologyActionGeneral_algebraMap]
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
def baseChangeCohomologyModuleGeneral
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    Module (A ⊗[R] R') (baseChangeCohomologyOverBase (R := R) (R' := R') K n) :=
  (baseChangeCohomologyModuleDataGeneral (R := R) (R' := R') K n).1

/-- The right tensor factor acts by the base-change `R'`-action already present. -/
theorem baseChangeCohomologyModuleGeneral_includeRight_smul
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] (K : DerivedCategory (ModuleCat.{u} A))
    (n : ℤ) (r : R') (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    letI := baseChangeCohomologyModuleGeneral (R := R) (R' := R') K n
    (Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m = r • m :=
  (baseChangeCohomologyModuleDataGeneral (R := R) (R' := R') K n).2.1 r m

/-- The left tensor factor acts by derived base change of scalar multiplication on `K`. -/
theorem baseChangeCohomologyModuleGeneral_includeLeft_smul
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] (K : DerivedCategory (ModuleCat.{u} A))
    (n : ℤ) (a : A) (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    letI := baseChangeCohomologyModuleGeneral (R := R) (R' := R') K n
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • m =
      baseChangeCohomologyActionGeneral (R := R) (R' := R') K n a m :=
  (baseChangeCohomologyModuleDataGeneral (R := R) (R' := R') K n).2.2 a m

/-- **The cohomology of a derived base change as a module over the ordinary tensor product.**
The underlying additive group is `baseChangeCohomologyOverBase` unchanged; only the action is
new. This is the source of the base-change map, before extension of scalars to `A'`. -/
def baseChangeCohomologyCatGeneral
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    ModuleCat.{u} (A ⊗[R] R') :=
  letI := baseChangeCohomologyModuleGeneral (R := R) (R' := R') K n
  ModuleCat.of (A ⊗[R] R') (baseChangeCohomologyOverBase (R := R) (R' := R') K n)

end Action

/-! ### The base-change map on cohomology -/

section Map

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A']
  [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- **The comparison of Stacks 065Z for a commutative square of commutative rings.** The natural
transformation from "restrict to `R`, then derived base change to `R'`" to "derived base change
to `A'`, then restrict to `R'`". -/
def squareDerivedComparisonGeneral
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')] :
    (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory ⋙
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R R')).functor ⟶
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A A')).functor ⋙
        (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory :=
  (@derivedBaseChangeComparison.{u, u, u, u, u, w, w, w, w}
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

/-- **The ring-level comparison of Stacks 0DJ8 (2).** For a commutative square of rings, an
object `K` of `D(A)`, an object `K'` of `D(A')` and `φ : K ⊗ᴸ_A A' ⟶ K'`, the composition

`K ⊗ᴸ_R R' ⟶ K ⊗ᴸ_A A' ⟶ K'`

in `D(R')`: the comparison of Stacks 065Z followed by `φ`, read over `R'`. -/
def ringComparison
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R R')).functor.obj
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ⟶
      (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj K' :=
  (squareDerivedComparisonGeneral (R := R) (A := A) (R' := R') (A' := A')).app K ≫
    (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map φ

/-- **The base-change comparison on cohomology, before adjunction.** The `R'`-linear map
`H^n(K ⊗ᴸ_R R') ⟶ H^n(K')` given by the `n`-th cohomology of `ringComparison`, read through
the identification of cohomology with restriction of scalars. -/
def cohomologyComparisonMapGeneral
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) :
    baseChangeCohomologyOverBase (R := R) (R' := R') K n ⟶
      (ModuleCat.restrictScalars (algebraMap R' A')).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
      (ringComparison (R := R) (R' := R') K K' φ) ≫
    ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso n).hom.app K'

/-- **The ring-level comparison is natural in the complex over `A`.** For `ψ : K₀ ⟶ K₁` in
`D(A)`, the comparison attached to the morphism `ψ ⊗ᴸ A' ≫ φ` is the derived base change of `ψ`
followed by the comparison attached to `φ`. This is the naturality of the Tag 065Z comparison
`RingTheory.TorIndependence.squareDerivedComparisonGeneral`.

It is what moves the complex of a square along a morphism while keeping the target fixed; the
affine reduction of Stacks 0DJ8 uses it at the unit `K ⟶ (K ⊗ᴸ_A A₂)|_A` of the derived
change-of-rings adjunction, which is the morphism underlying
`RingTheory.TorIndependence.localizedBaseChangeCohomologyComparison`. -/
theorem ringComparison_map
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (K₀ K₁ : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A')) (ψ : K₀ ⟶ K₁)
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K₁ ⟶ K') :
    ringComparison (R := R) (R' := R') K₀ K'
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A A')).functor.map ψ ≫ φ) =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            (algebraMap R R')).functor.map
          ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map ψ) ≫
        ringComparison (R := R) (R' := R') K₁ K' φ := by
  dsimp only [ringComparison]
  have h := (squareDerivedComparisonGeneral (R := R) (A := A) (R' := R') (A' := A')).naturality ψ
  dsimp only [Functor.comp_map] at h
  rw [Functor.map_comp, ← Category.assoc, ← h, Category.assoc]

/-- **The base-change comparison on cohomology is natural in the complex over `A`**, by
`RingTheory.TorIndependence.ringComparison_map`. -/
theorem cohomologyComparisonMapGeneral_map
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (K₀ K₁ : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A')) (ψ : K₀ ⟶ K₁)
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K₁ ⟶ K') (n : ℤ) :
    cohomologyComparisonMapGeneral (R := R) (R' := R') K₀ K'
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (algebraMap A A')).functor.map ψ ≫ φ) n =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
              (algebraMap R R')).functor.map
            ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map ψ)) ≫
        cohomologyComparisonMapGeneral (R := R) (R' := R') K₁ K' φ n := by
  dsimp only [cohomologyComparisonMapGeneral]
  rw [ringComparison_map (R := R) (R' := R') K₀ K₁ K' ψ φ, Functor.map_comp, Category.assoc]

/-- The comparison carries the action of the right tensor factor to multiplication by its image
in `A'`: that is its `R'`-linearity. -/
theorem cohomologyComparisonMapGeneral_includeRight_smul
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) (r : R')
    (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    letI := baseChangeCohomologyModuleGeneral (R := R) (R' := R') K n
    (cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n).hom
        ((Algebra.TensorProduct.includeRight r : A ⊗[R] R') • m) =
      algebraMap R' A' r •
        (show (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K' from
          (cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n).hom m) :=
  let := baseChangeCohomologyModuleGeneral (R := R) (R' := R') K n
  Eq.trans
    (congrArg (fun x => (cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n).hom x)
      (baseChangeCohomologyModuleGeneral_includeRight_smul (R := R) (R' := R') K n r m))
    ((cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n).hom.map_smul r m)


/-- The comparison carries the action of the left tensor factor to multiplication by its image in
`A'`. Together with `cohomologyComparisonMapGeneral_includeRight_smul` this makes the comparison
linear over `A ⊗_R R'`. -/
theorem cohomologyComparisonMapGeneral_includeLeft_smul
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) (a : A)
    (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    letI := baseChangeCohomologyModuleGeneral (R := R) (R' := R') K n
    (cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n).hom
        ((Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • m) =
      algebraMap A A' a •
        (show (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K' from
          (cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n).hom m) := by
  let := baseChangeCohomologyModuleGeneral (R := R) (R' := R') K n
  let f : R →+* A := algebraMap R A
  let g : R →+* R' := algebraMap R R'
  let h : A →+* A' := algebraMap A A'
  let i : R' →+* A' := algebraMap R' A'
  let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g
  let Th := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h
  let C := (ModuleCat.restrictScalars i).mapDerivedCategory
  let J := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let J' := DerivedCategory.homologyFunctor (ModuleCat.{u} A') n
  let τ := squareDerivedComparisonGeneral (R := R) (A := A) (R' := R') (A' := A')
  let α := τ.app K ≫ C.map φ
  let H' := J'.obj K'
  have hq : cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n =
      J.map α ≫ ((ModuleCat.restrictScalars i).mapDerivedCategoryHomologyIso n).hom.app K' := rfl
  have hφ : Th.functor.map (a • 𝟙 K) ≫ φ = φ ≫ (h a • 𝟙 K') := by
    rw [derivedExtension_scalar]
    change (h a • 𝟙 (Th.functor.obj K)) ≫ φ = φ ≫ (h a • 𝟙 K')
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  have hd : ((ModuleCat.restrictScalars f).mapDerivedCategory ⋙ Tg.functor).map
      (a • 𝟙 K) ≫ α = α ≫ C.map (h a • 𝟙 K') := by
    dsimp only [α]
    rw [← Category.assoc, τ.naturality]
    change (τ.app K ≫ C.map (Th.functor.map (a • 𝟙 K))) ≫ C.map φ = _
    rw [Category.assoc, ← C.map_comp, hφ, C.map_comp, Category.assoc]
  have hn := ((ModuleCat.restrictScalars i).mapDerivedCategoryHomologyIso n).hom.naturality
    (h a • 𝟙 K')
  let := DerivedCategory.homologyFunctor_linear (C := ModuleCat.{u} A') A' n
  have hnat : J.map (((ModuleCat.restrictScalars f).mapDerivedCategory ⋙ Tg.functor).map
        (a • 𝟙 K)) ≫ cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n =
      cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n ≫
        (ModuleCat.restrictScalars i).map (h a • 𝟙 H') := by
    rw [hq, ← Category.assoc, ← J.map_comp, hd, J.map_comp, Category.assoc]
    change _ ≫ ((C ⋙ J).map (h a • 𝟙 K') ≫
      ((ModuleCat.restrictScalars i).mapDerivedCategoryHomologyIso n).hom.app K') = _
    rw [hn]
    dsimp only [Functor.comp_map]
    rw [Functor.map_smul, J'.map_id]
    exact (Category.assoc _ _ _).symm
  exact Eq.trans
    (congrArg (fun x => (cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n).hom x)
      (baseChangeCohomologyModuleGeneral_includeLeft_smul (R := R) (R' := R') K n a m))
    (congrArg (fun l => l.hom m) hnat)

/-- The base-change comparison, as a map of `A ⊗_R R'`-modules. -/
def cohomologyComparisonLinearMapGeneral
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) :
    baseChangeCohomologyCatGeneral (R := R) (R' := R') K n ⟶
      (ModuleCat.restrictScalars
          (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'))).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K') :=
  letI := baseChangeCohomologyModuleGeneral (R := R) (R' := R') K n
  let H' := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K'
  let k := baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')
  let q := cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n
  ModuleCat.ofHom (X := baseChangeCohomologyCatGeneral (R := R) (R' := R') K n)
      (Y := (ModuleCat.restrictScalars k).obj H')
    (show baseChangeCohomologyCatGeneral (R := R) (R' := R') K n →ₗ[A ⊗[R] R']
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
              (cohomologyComparisonMapGeneral_includeLeft_smul (R := R) (R' := R') K K' φ n a _) ?_
            refine Eq.trans (congrArg (fun z => algebraMap A A' a • z)
              (cohomologyComparisonMapGeneral_includeRight_smul (R := R) (R' := R')
                K K' φ n r _)) ?_
            rw [← ht]
            exact (mul_smul _ _ _).symm })

/-- **The `A ⊗_R R'`-linear comparison is the cohomology of `ringComparison`.** Forgetting the
action, it is the `n`-th cohomology of the ring-level comparison read through the identification
of the cohomology of a restriction of scalars with the restriction of scalars of the
cohomology. -/
theorem cohomologyComparisonLinearMapGeneral_apply
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ)
    (m : baseChangeCohomologyCatGeneral (R := R) (R' := R') K n) :
    (cohomologyComparisonLinearMapGeneral (R := R) (R' := R') K K' φ n).hom m =
      (((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategoryHomologyIso n
          ).hom.app K').hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
          (ringComparison (R := R) (R' := R') K K' φ)).hom
            (show baseChangeCohomologyOverBase (R := R) (R' := R') K n from m)) :=
  rfl

/-- **Stacks 0DJ7 at the level of rings, constructed.** The base-change map on cohomology
`A' ⊗_{A ⊗_R R'} H^n(K ⊗ᴸ_R R') ⟶ H^n(K')` attached to `φ : K ⊗ᴸ_A A' ⟶ K'`, obtained by
adjunction from the `A ⊗_R R'`-linear comparison `cohomologyComparisonLinearMapGeneral`. -/
def ringBaseChangeCohomologyMapGeneral
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ) :
    (ModuleCat.extendScalars
          (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'))).obj
        (baseChangeCohomologyCatGeneral (R := R) (R' := R') K n) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K' :=
  ((ModuleCat.extendRestrictScalarsAdj
      (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A'))).homEquiv
    (baseChangeCohomologyCatGeneral (R := R) (R' := R') K n)
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K')).symm
    (cohomologyComparisonLinearMapGeneral (R := R) (R' := R') K K' φ n)

/-- **The characterizing formula for the base-change map.** Its value on `1 ⊗ m` is the
comparison of Stacks 065Z followed by `φ`, which is exactly the normalization pinning the map of
`exists_unique_ringBaseChangeCohomologyMap`. -/
theorem ringBaseChangeCohomologyMapGeneral_one_tmul
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') (n : ℤ)
    (m : baseChangeCohomologyCatGeneral (R := R) (R' := R') K n) :
    (ringBaseChangeCohomologyMapGeneral (R := R) (R' := R') K K' φ n).hom
        ((1 : A') ⊗ₜ[A ⊗[R] R',
          baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')] m) =
      (cohomologyComparisonMapGeneral (R := R) (R' := R') K K' φ n).hom
        (show baseChangeCohomologyOverBase (R := R) (R' := R') K n from m) := by
  let k := baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')
  let H := baseChangeCohomologyCatGeneral (R := R) (R' := R') K n
  let H' := (DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K'
  let adj := ModuleCat.extendRestrictScalarsAdj k
  let l := cohomologyComparisonLinearMapGeneral (R := R) (R' := R') K K' φ n
  have hunit := congrArg (fun z => z.hom m)
    (adj.homEquiv_unit (f := ringBaseChangeCohomologyMapGeneral (R := R) (R' := R') K K' φ n))
  have hev := congrArg (fun z => z.hom m) ((adj.homEquiv H H').apply_symm_apply l)
  exact hunit.symm.trans hev

end Map

end RingTheory.TorIndependence

end
