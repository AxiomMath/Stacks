module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologyFunctor
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTorObj

/-!
# The base-change cohomology of a module is `Tor`, with its left action

Let `R → A` and `R → R'` be homomorphisms of commutative rings and `M` an `A`-module. Reading `M`
as the object `M[0]` of `D(A)`, the degree `-i` cohomology of its derived base change is
`Tor_i^R(R', M)`, and the action of the left tensor factor `A` of `A ⊗_R R'` on it is
functoriality of `Tor_i^R(R', ·)` in its second variable.

## Main definitions

* `RingTheory.TorIndependence.baseChangeCohomologySingleIsoTor`: for `M` an `A`-module,
  `H^{-i}(M[0] ⊗ᴸ_R R') ≅ Tor_i^R(R', M)`, naturally in `M`.

## Main results

* `RingTheory.TorIndependence.baseChangeCohomologySingleIsoTor_includeLeft_smul`: this
  isomorphism carries the action of `Algebra.TensorProduct.includeLeft a` to `Tor_i^R(R', ·)`
  applied to multiplication by `a` on `M`.

## Implementation notes

The model of the derived category is free for each of the three rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u w

namespace RingTheory.TorIndependence

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- **The base-change cohomology of a module in degree zero is `Tor`.** For `M` an `A`-module,

`H^{-i}(M[0] ⊗ᴸ_R R') ≅ Tor_i^R(R', M)`,

naturally in `M`, both sides read over `R`. -/
def baseChangeCohomologySingleIsoTor (i : ℕ) :
    DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ)) ⋙
            ModuleCat.restrictScalars.{u, u, u} (algebraMap R R') ≅
      ModuleCat.restrictScalars.{u, u, u} (algebraMap R A) ⋙
        (Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R') :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerRight
        ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).mapDerivedCategorySingleFunctor 0)
        ((totalDerivedExtensionScalars.{u, u, u, w, w} (algebraMap R R')).functor ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R') (-(i : ℤ))))
      (ModuleCat.restrictScalars.{u, u, u} (algebraMap R R')) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A))
      (derivedExtensionSingleIsoTor i)

/-- **The left tensor factor acts by functoriality of `Tor` in its second variable.** -/
theorem baseChangeCohomologySingleIsoTor_includeLeft_smul (i : ℕ) (M : ModuleCat.{u} A) (a : A)
    (m : baseChangeCohomology (R := R) (R' := R')
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (-(i : ℤ))) :
    ((baseChangeCohomologySingleIsoTor (R := R) (R' := R') i).hom.app M).hom
        ((Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] R') • m) =
      (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R R')).map
          ((ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)).map (a • 𝟙 M))).hom
        (((baseChangeCohomologySingleIsoTor (R := R) (R' := R') i).hom.app M).hom m) := by
  have hs : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (a • 𝟙 M) =
      a • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  have hnat0 := (baseChangeCohomologySingleIsoTor (R := R) (R' := R') i).hom.naturality
    (a • 𝟙 M)
  dsimp only [Functor.comp_map] at hnat0
  rw [hs] at hnat0
  have hnat := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hnat0) m
  exact (congrArg _ (baseChangeCohomology_includeLeft_smul (R := R) (R' := R')
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) (-(i : ℤ)) a m)).trans hnat

end RingTheory.TorIndependence

end
