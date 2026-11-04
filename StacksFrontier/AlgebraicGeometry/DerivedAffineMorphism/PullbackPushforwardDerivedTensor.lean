module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PushforwardTExactness
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.CategoryTheory.Category.CompositionChains
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaInvertibility
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQuasiCoherent
import StacksCore.Tactic.StacksAttribute

/-!
# `Rf_*Lf^*E = E ⊗^𝐋 f_*𝒪_X` for an affine morphism

Let `f : X ⟶ S` be an affine morphism of schemes.  [Stacks, Tag 08I9] asserts that

`Rf_* Lf^* E ≅ E ⊗^𝐋_{𝒪_S} f_*𝒪_X`

for every `E` in `D_QCoh(𝒪_S)`, with the *derived* tensor product and with no boundedness
hypothesis on `E`.  It is the case `E = 𝒪_X[0]` of the projection formula [Stacks, Tag 08EU],
combined with the left unit law of the derived tensor product and with `Rf_*𝒪_X = f_*𝒪_X`, which
holds because `f` is affine.

## Main results

* `isQuasicoherent_homology_singleFunctor_obj`: every cohomology sheaf of a quasi-coherent sheaf
  placed in one degree is quasi-coherent.
* `isIso_projectionFormulaMap_singleUnit`: [Stacks, Tag 08EU] at the source complex `𝒪_X[0]`,
  for a quasi-compact quasi-separated `f`.
* `derivedPushforwardDerivedPullbackTensorIso`: `f_*𝒪_X ⊗^𝐋_{𝒪_S} E ≅ Rf_* Lf^* E` for an affine
  `f` and `E` with quasi-coherent cohomology.
* `derivedPushforwardDerivedPullbackTensorIso_hom_naturality`: that isomorphism is natural in
  `E`, over the morphisms between complexes that both satisfy its quasi-coherence hypothesis.

## Implementation notes

The model of the derived category is `CategoryTheory.HasDerivedCategory.standard`.

The isomorphism carries a quasi-coherence hypothesis on `E`, because [Stacks, Tag 08EU] does, so
its naturality is naturality over the morphisms of the full subcategory of `D(𝒪_S)` that the
hypothesis cuts out, not a natural isomorphism of functors on `D(𝒪_S)`.

## References

* [Stacks Project, Tag 08I9](https://stacks.math.columbia.edu/tag/08I9)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPullback)
open Stacks.Cohomology.DerivedProjectionFormula (projectionFormulaMap singleUnit
  derivedPushforwardDerivedPullbackIsoOfIsIso
  derivedPushforwardDerivedPullbackIsoOfIsIso_hom_natural)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open RingedSpaceModuleAdjunction (modulePushforward)

universe u

namespace Stacks.AlgebraicGeometry.AffinePushforwardTExactness

attribute [local instance 10000] HasDerivedCategory.standard

variable {X S : Scheme.{u}}

/-- Every cohomology sheaf of a quasi-coherent sheaf placed in one degree is quasi-coherent: in
degree `n` it is the sheaf itself and in the other degrees it is a zero object. -/
theorem isQuasicoherent_homology_singleFunctor_obj (n : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (hM : M.IsQuasicoherent)
    (k : ℤ) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) k).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj M)).IsQuasicoherent := by
  have hP : (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).ContainsZero :=
    containsZero_isQuasicoherent X
  by_cases hk : k = n
  · subst hk
    exact (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) k).app M).symm hM
  · refine (SheafOfModules.isQuasicoherent (structureSheafRing X.toRingedSpace)).prop_of_isZero ?_
    exact (((DerivedCategory.homologyFunctorFactors
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) k).app
        ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj M)).isZero_iff).2
      (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) n M k hk)

/-- For a quasi-compact and quasi-separated morphism of schemes `f : X ⟶ S` and a complex `K` on
`S` with quasi-coherent cohomology, the derived projection-formula map

`Rf_*𝒪_X ⊗^𝐋_{𝒪_S} K ⟶ Rf_*(𝒪_X ⊗^𝐋_{𝒪_X} Lf^*K)`

is invertible. -/
theorem isIso_projectionFormulaMap_singleUnit (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj K).IsQuasicoherent) :
    IsIso (projectionFormulaMap f.toLRSHom.toShHom (singleUnit X.toRingedSpace) K) :=
  Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_quasiCoherent f
    (singleUnit X.toRingedSpace)
    (fun j => isQuasicoherent_homology_singleFunctor_obj 0 _
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X) j) K hK

/-- For an affine morphism of schemes `f : X ⟶ S` and a complex `E` on `S` with quasi-coherent
cohomology,

`f_*𝒪_X ⊗^𝐋_{𝒪_S} E ≅ Rf_* Lf^* E`,

with the derived tensor product and with no boundedness hypothesis on `E`. -/
@[stacks 08I9]
def derivedPushforwardDerivedPullbackTensorIso (f : X ⟶ S) [IsAffineHom f]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj E).IsQuasicoherent) :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) 0).obj
          ((modulePushforward f.toLRSHom.toShHom).obj
            (SheafOfModules.unit (structureSheafRing X.toRingedSpace))))).obj E ≅
      (derivedPushforward f.toLRSHom.toShHom).obj
        ((derivedPullback f.toLRSHom.toShHom).obj E) :=
  ((derivedTensorProductFunctor S.toRingedSpace.sheaf).mapIso
      (derivedPushforwardSingleIso f 0 (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
        (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X))).app E ≪≫
    Stacks.Cohomology.DerivedProjectionFormula.derivedPushforwardDerivedPullbackIsoOfIsIso
      f.toLRSHom.toShHom (Stacks.RingedSpace.derivedTensorLeftUnitIso X.toRingedSpace) E
      (isIso_projectionFormulaMap_singleUnit f E hE)

/-- The isomorphism `derivedPushforwardDerivedPullbackTensorIso` is natural in the complex: for
an affine morphism of schemes `f : X ⟶ S` and a morphism `e : E ⟶ E'` of `D(𝒪_S)` *between
complexes that both have quasi-coherent cohomology*, the square

```
f_*𝒪_X ⊗^𝐋_{𝒪_S} E  ⟶  Rf_* Lf^* E
        |                    |
  1 ⊗ e |                    | Rf_* Lf^* e
        v                    v
f_*𝒪_X ⊗^𝐋_{𝒪_S} E' ⟶  Rf_* Lf^* E'
```

commutes, the horizontal arrows being the isomorphism of
`derivedPushforwardDerivedPullbackTensorIso`. -/
theorem derivedPushforwardDerivedPullbackTensorIso_hom_naturality (f : X ⟶ S) [IsAffineHom f]
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hE : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj E).IsQuasicoherent)
    (hE' : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) j).obj E').IsQuasicoherent)
    (e : E ⟶ E') :
    ((derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) 0).obj
            ((modulePushforward f.toLRSHom.toShHom).obj
              (SheafOfModules.unit (structureSheafRing X.toRingedSpace))))).map e ≫
        (derivedPushforwardDerivedPullbackTensorIso f E' hE').hom =
      (derivedPushforwardDerivedPullbackTensorIso f E hE).hom ≫
        (derivedPushforward f.toLRSHom.toShHom).map
          ((derivedPullback f.toLRSHom.toShHom).map e) :=
  iso_trans_chain_square _ _ _ _
    (((derivedTensorProductFunctor S.toRingedSpace.sheaf).map
      (derivedPushforwardSingleIso f 0 (SheafOfModules.unit (structureSheafRing X.toRingedSpace))
        (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X)).hom).naturality e)
    (derivedPushforwardDerivedPullbackIsoOfIsIso_hom_natural f.toLRSHom.toShHom
      (Stacks.RingedSpace.derivedTensorLeftUnitIso X.toRingedSpace)
      (fun w ↦ Stacks.RingedSpace.derivedTensorLeftUnitor_naturality X.toRingedSpace w) e
      (isIso_projectionFormulaMap_singleUnit f E hE)
      (isIso_projectionFormulaMap_singleUnit f E' hE'))

end Stacks.AlgebraicGeometry.AffinePushforwardTExactness

end
