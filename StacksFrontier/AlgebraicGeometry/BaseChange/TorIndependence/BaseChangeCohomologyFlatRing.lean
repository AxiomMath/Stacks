module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologyFlatExtension
public import StacksFrontier.Homology.Tor.BaseChangeCohomologyDevissage

/-!
# A flat extension of the ring is equivariant for the algebra

`RingTheory.TorIndependence.flatCompDerivedHomologyIso` moves a flat extension `R' → C` of the
*ring* slot of a derived base change through cohomology:

`H^n(N ⊗ᴸ_R C)  ≅  C ⊗_{R'} H^n(N ⊗ᴸ_R R')`,

naturally in the object `N` of `D(R)`. When `N` is an `A`-complex read over `R` both sides carry
an action of `A` as well — on the left it is the left tensor factor of the `A ⊗_R C`-module
`RingTheory.TorIndependence.baseChangeCohomology`, on the right it is the flat extension of the
same action over `R'` — and the affine reduction of [stacks 0DJ8] consumes the identification as
one of `A`-modules, not merely of `C`-modules.

This module records that second half of the linearity. There is nothing to prove beyond
naturality: the action of `a : A` on either side is, by
`RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul`, the base change of scalar
multiplication `a • 𝟙` on the `A`-complex, and the comparison is natural in the complex.

## Main results

* `RingTheory.TorIndependence.flatCompDerivedHomologyIso_app_includeLeft_smul`: the comparison
  carries the action of the left tensor factor `A` of `A ⊗_R C` to the flat extension of the
  action of the left tensor factor `A` of `A ⊗_R R'`.

## Implementation notes

The `R → C` algebra structure is the composite `R → R' → C` taken as data, written as a `letI`
in the statement, because `RingTheory.TorIndependence.flatCompDerivedHomologyIso` is stated at
the composite ring map `g.comp f` and `RingTheory.TorIndependence.baseChangeCohomology` at
`algebraMap R C`; with the composite installed as the algebra structure the two are the same map
and no transport is needed. This is the same shape in which
`AlgebraicGeometry.BaseChangeChart.homologyBaseChangeLocalizedIso` supplies the chart's rings.

The action on the right-hand side is written as the image under
`ModuleCat.extendScalars` of a morphism of `R'`-modules rather than as a scalar multiplication:
the carrier `C ⊗_{R'} H^n(N ⊗ᴸ_R R')` has no `Module A` instance, exactly as in
`RingTheory.TorIndependence.localizedBaseChangeCohomologyComparison_app_includeRight_smul`,
so there is no `A ⊗_R C`-valued object to state the equivariance as a morphism between.

## References

* [The Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [The Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct ChangeOfRings

universe u

namespace RingTheory.TorIndependence

section FlatRing

variable {R A R' C : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing C]
  [Algebra R A] [Algebra R R'] [Algebra R' C]
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} A)]
  [HasDerivedCategory.{u} (ModuleCat.{u} R')] [HasDerivedCategory.{u} (ModuleCat.{u} C)]

/-- **A flat extension of the ring slot is equivariant for the algebra.** For `R' → C` flat and
`L` an object of `D(A)`, the comparison

`H^n(L|_R ⊗ᴸ_R C)  ≅  C ⊗_{R'} H^n(L|_R ⊗ᴸ_R R')`

of `RingTheory.TorIndependence.flatCompDerivedHomologyIso` carries the action of the left tensor
factor `A` of `A ⊗_R C` on its source to the flat extension along `R' → C` of the action of the
left tensor factor `A` of `A ⊗_R R'` on its target.

Both actions are, by
`RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul`, the derived base change of
scalar multiplication `a • 𝟙` on `L`, so this is the naturality of the comparison at that
morphism of `D(A)` read over `R`. -/
theorem flatCompDerivedHomologyIso_app_includeLeft_smul
    (hflat : (algebraMap R' C).Flat) (n : ℤ) (L : DerivedCategory (ModuleCat.{u} A)) (a : A) :
    letI := ((algebraMap R' C).comp (algebraMap R R')).toAlgebra
    ∀ m : baseChangeCohomology (R := R) (R' := C) L n,
      ((flatCompDerivedHomologyIso.{u, u} (algebraMap R R') (algebraMap R' C) hflat n).hom.app
            ((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory.obj L)).hom
          ((Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] C) • m) =
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap R' C)).map
            ((derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map (a • 𝟙 L))).hom
          (((flatCompDerivedHomologyIso.{u, u} (algebraMap R R') (algebraMap R' C)
                hflat n).hom.app
              ((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory.obj L)).hom
            m) := by
  let := ((algebraMap R' C).comp (algebraMap R R')).toAlgebra
  intro m
  have hnat := (flatCompDerivedHomologyIso.{u, u} (algebraMap R R') (algebraMap R' C)
      hflat n).hom.naturality
    ((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory.map (a • 𝟙 L))
  rw [baseChangeCohomology_includeLeft_smul]
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hnat) m

end FlatRing

end RingTheory.TorIndependence

end
