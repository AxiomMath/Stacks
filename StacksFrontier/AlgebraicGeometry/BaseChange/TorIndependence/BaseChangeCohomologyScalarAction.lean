module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologyFunctor
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap
public import StacksFrontier.Homology.Tor.BaseChangeCohomologyDevissage
import all StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMap

/-!
# Scalar multiplication on the complex, through base-change cohomology

The base-change cohomology of a complex `L` of `A₂`-modules *read over `A`* is a module over
`A ⊗_R R'` only; the action of `A₂` on it exists because `D(A₂)` is `A₂`-linear, and it is the
image of `x • 𝟙 L` under the base-change functor followed by `H^n`. The affine reduction of
[stacks 0DJ8] transports modules along a chain whose steps are induced by morphisms of `D(A₂)`
and whose linearity has to be tracked over `A₂`, and the two general facts it uses are here.

The first is that scalar multiplication is central: `x • 𝟙` commutes with every morphism of a
linear category, so the map induced on base-change cohomology by a morphism of `D(A₂)` is
equivariant for the action of `A₂`, with no hypothesis on the morphism.

The second is that restriction of scalars along `σ : A₂ → A₃` turns multiplication by `σ x` into
multiplication by `x`, on derived categories. That is how a complex living over one local ring is
read over another presentation of it: the identification of
`AlgebraicGeometry.BaseChangeChart.germDerivedStalkSectionsIso` is `𝒪_{Spec 𝒪_X(U), q}`-linear
with the derived stalk of `K` restricted along the comparison of the two local rings, and the
action of `𝒪_{X, g' x'}` on the derived stalk is what has to appear on the other side.

## Main results

* `RingTheory.TorIndependence.mapDerivedCategory_restrictScalars_smul`: restriction of scalars
  along `σ` carries `σ x • 𝟙` to `x • 𝟙`, on derived categories.
* `RingTheory.TorIndependence.baseChangeCohomologyMap_restrict_smul`: the map induced on
  base-change cohomology by a morphism of `D(A₂)`, read over `A`, is equivariant for the action
  of `A₂`.

## Implementation notes

The first statement is `RingTheory.TorIndependence.exactFunctor_scalar` at restriction of
scalars. It is recorded here because the affine reduction needs it at a ring map which is not
the `algebraMap` of any instance in scope — the comparison of two presentations of one local
ring — so the instance-level
`RingTheory.TorIndependence.baseChangeCohomologyRestrictMap_includeLeft_smul` does not apply.

The action of `A₂` is written throughout as the image of `x • 𝟙` under
`(ModuleCat.restrictScalars _).mapDerivedCategory ⋙ derivedBaseChangeFunctor ⋙ H^n`, which is
the form `RingTheory.TorIndependence.baseChangeCohomology_includeLeft_smul` uses to characterize
the action it installs; there is no `Module A₂` instance on the carrier to write it as a scalar
multiplication.

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

section RestrictSmul

variable {A₂ A₃ : Type u} [CommRing A₂] [CommRing A₃]
  [HasDerivedCategory.{u} (ModuleCat.{u} A₂)] [HasDerivedCategory.{u} (ModuleCat.{u} A₃)]

/-- **Restriction of scalars along `σ : A₂ → A₃` carries `σ x • 𝟙` to `x • 𝟙`.** Restriction of
scalars is exact and additive, and on a module it carries multiplication by `σ x` to
multiplication by `x` by the definition of the restricted action; so it does so on the derived
category. -/
public theorem mapDerivedCategory_restrictScalars_smul (σ : A₂ →+* A₃) (x : A₂)
    (L : DerivedCategory (ModuleCat.{u} A₃)) :
    (ModuleCat.restrictScalars.{u} σ).mapDerivedCategory.map (σ x • 𝟙 L) =
      x • 𝟙 ((ModuleCat.restrictScalars.{u} σ).mapDerivedCategory.obj L) :=
  exactFunctor_scalar (ModuleCat.restrictScalars.{u} σ) (σ x) x (fun M => by ext m; rfl) L

end RestrictSmul

section MapSmul

variable {R A A₂ R' : Type u} [CommRing R] [CommRing A] [CommRing A₂] [CommRing R']
  [Algebra R A] [Algebra A A₂] [Algebra R R']
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} A)]
  [HasDerivedCategory.{u} (ModuleCat.{u} A₂)] [HasDerivedCategory.{u} (ModuleCat.{u} R')]

/-- **The map induced on base-change cohomology by a morphism of `D(A₂)` is equivariant for
`A₂`.** Both actions are the image of `x • 𝟙` under the base-change functor followed by `H^n`,
and `x • 𝟙` is central in a linear category: it commutes with every morphism. No hypothesis on
the morphism is needed — in particular it need not be an isomorphism. -/
public theorem baseChangeCohomologyMap_restrict_smul (n : ℤ)
    {P Q : DerivedCategory (ModuleCat.{u} A₂)} (φ : P ⟶ Q) (x : A₂)
    (m : baseChangeCohomology (R := R) (R' := R')
      ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj P) n) :
    (baseChangeCohomologyMap (R := R) (R' := R') n
          ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.map φ)).hom
        (show baseChangeCohomology (R := R) (R' := R')
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj P) n from
          ((((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
                derivedBaseChangeFunctor (R := R) (A := A) (R' := R')) ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map (x • 𝟙 P)).hom m) =
      ((((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
            derivedBaseChangeFunctor (R := R) (A := A) (R' := R')) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map (x • 𝟙 Q)).hom
        (show baseChangeCohomology (R := R) (R' := R')
            ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.obj Q) n from
          (baseChangeCohomologyMap (R := R) (R' := R') n
              ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.map φ)).hom
            m) := by
  have hcentral : (x • 𝟙 P) ≫ φ = φ ≫ (x • 𝟙 Q) := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  have hmap := congrArg
    ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ⋙
      derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map hcentral
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hmap
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hmap) m

end MapSmul

end RingTheory.TorIndependence

end
