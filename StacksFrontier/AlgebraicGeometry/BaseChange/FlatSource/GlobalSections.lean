module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.Global
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeUnitSingle
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardDerivedTensor
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLeray
public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison

/-!
# Cohomology and base change for the structure sheaf of a flat morphism over an affine base

Let `φ : A ⟶ A'` be a homomorphism of commutative rings, let `h : W ⟶ Spec A` be flat,
quasi-compact and quasi-separated, and let

```
W' --q--> W
|         |
h'        h
v         v
Spec A' --> Spec A
```

be cartesian. This file proves that the derived global sections of the structure sheaves satisfy

`RΓ(W, 𝒪_W) ⊗^L_{A, φ} A' ≅ RΓ(W', 𝒪_{W'})`

in `D(A')`. This is [Stacks, Tag 08IB] for `E = 𝒪_W`, read on global sections over the affine
base: flatness of `h` makes `W` and `Spec A'` Tor independent over `Spec A`.

## Main results

* `AlgebraicGeometry.derivedGlobalSectionsSpecPullbackIso`: for an object `M` of `D(𝒪_{Spec A})`
  with quasi-coherent cohomology, `RΓ(Spec A', Lφ^*M) ≅ RΓ(Spec A, M) ⊗^L_{A, φ} A'`.
* `AlgebraicGeometry.nonempty_extendScalarsDerived_derivedGlobalSectionsOver_iso_of_flat`:
  **cohomology and base change for the structure sheaf** over an affine base.

## The proof

The base change map of [Stacks, Tag 08HY] is an isomorphism at `𝒪_W` by [Stacks, Tag 08IB],
`AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`, since a flat `h` is Tor independent from
every morphism to `Spec A` (`AlgebraicGeometry.torIndependent_of_flat_left`) and `𝒪_W` is
quasi-coherent. Global sections over `Spec A'` of its source are computed by the affine comparison
square of [Stacks, Tag 08DW] (2) together with the derived Spec–Γ equivalence of
[Stacks, Tag 06Z0], which apply because `Rh_*𝒪_W` has quasi-coherent cohomology
([Stacks, Tag 08D5]); global sections over `Spec A'` of its target are global sections over `W'`
by [Stacks, Tag 0D5W], and `Lq^*𝒪_W = 𝒪_{W'}`.

## References

* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Modules (toShHom_comm)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange

universe u

namespace AlgebraicGeometry

-- Standard model only: `derivedBaseChangeIsIsoOnQuasicoherent` (08IB),
-- `derivedGlobalSectionsOver`.
attribute [local instance 10000] HasDerivedCategory.standard

section Affine

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- Derived extension of scalars of [Stacks, Tag 06Y5], in the two constructions of the library:
`StacksDraft.PseudoCoherence.extendScalarsDerived` and the unbounded functor of
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`. Both are total left derived
functors of termwise extension of scalars, so they agree. -/
def totalDerivedExtensionScalarsIso :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ).functor ≅
      StacksDraft.PseudoCoherence.extendScalarsDerived φ :=
  have := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    φ).isLeftDerived
  Functor.leftDerivedNatIso _ _
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ).comparison
    (StacksDraft.PseudoCoherence.extendScalarsDerivedCounit φ)
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) (Iso.refl _)

/-- **Global sections over an affine base commute with derived base change.** For an object `M` of
`D(𝒪_{Spec A})` with quasi-coherent cohomology sheaves,
`RΓ(Spec A', Lφ^*M) ≅ RΓ(Spec A, M) ⊗^L_{A, φ} A'` in `D(A')`.

`M` is the complex associated to `RΓ(Spec A, M)` by [Stacks, Tag 06Z0], derived pullback of an
associated complex is the complex associated to its derived base change by [Stacks, Tag 08DW] (2),
and global sections recover a complex of modules from its associated complex, again by
[Stacks, Tag 06Z0]. -/
def derivedGlobalSectionsSpecPullbackIso (M : DerivedCategory (Spec (.of A)).Modules)
    (hM : ∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec (.of A)).Modules i).obj
      M).IsQuasicoherent) :
    (derivedGlobalSectionsOver (𝟙 (Spec (.of A')))).obj
        ((StandardModel.specDerivedPullback (CommRingCat.ofHom φ)).obj M) ≅
      (StacksDraft.PseudoCoherence.extendScalarsDerived φ).obj
        ((derivedGlobalSectionsOver (𝟙 (Spec (.of A)))).obj M) :=
  have : IsIso ((derivedTildeGlobalSectionsAdjunction (CommRingCat.of A)).val.counit.app M) :=
    StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_counit_app (CommRingCat.of A) ⟨M, hM⟩
  have := StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit (CommRingCat.of A')
  let N := (derivedGlobalSectionsOver (𝟙 (Spec (.of A)))).obj M
  let P := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    φ).functor.obj N
  (derivedGlobalSectionsOver (𝟙 (Spec (.of A')))).mapIso
      ((StandardModel.specDerivedPullback (CommRingCat.ofHom φ)).mapIso
          (asIso ((derivedTildeGlobalSectionsAdjunction (CommRingCat.of A)).val.counit.app
            M)).symm ≪≫
        (StandardModel.specDerivedPullback (CommRingCat.ofHom φ)).mapIso
          ((derivedTildeCompι (CommRingCat.of A)).app N) ≪≫
        (StandardModel.affinePullbackComparison (CommRingCat.of A) (CommRingCat.of A')
          (CommRingCat.ofHom φ)).app N ≪≫
        ((derivedTildeCompι (CommRingCat.of A')).app P).symm) ≪≫
    (asIso ((derivedTildeGlobalSectionsAdjunction (CommRingCat.of A')).val.unit.app P)).symm ≪≫
    (totalDerivedExtensionScalarsIso φ).app N

/-- **Cohomology and base change for the structure sheaf over an affine base.** Let
`φ : A ⟶ A'` be a homomorphism of commutative rings, let `h : W ⟶ Spec A` be flat, quasi-compact
and quasi-separated, and let `W'` be the base change of `W` along `Spec φ`. Then

`RΓ(W, 𝒪_W) ⊗^L_{A, φ} A' ≅ RΓ(W', 𝒪_{W'})`

in `D(A')`. This is [Stacks, Tag 08IB] at `E = 𝒪_W`, read on global sections over the affine
base: flatness of `h` makes `W` and `Spec A'` Tor independent over `Spec A`. -/
theorem nonempty_extendScalarsDerived_derivedGlobalSectionsOver_iso_of_flat {W W' : Scheme.{u}}
    (h : W ⟶ Spec (.of A)) (h' : W' ⟶ Spec (.of A')) (q : W' ⟶ W)
    (hsq : IsPullback q h' h (Spec.map (CommRingCat.ofHom φ))) [QuasiCompact h]
    [QuasiSeparated h] [Flat h] :
    Nonempty ((StacksDraft.PseudoCoherence.extendScalarsDerived φ).obj
        ((derivedGlobalSectionsOver h).obj
          ((DerivedCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf))) ≅
      (derivedGlobalSectionsOver h').obj
        ((DerivedCategory.singleFunctor W'.Modules 0).obj
          (SheafOfModules.unit W'.ringCatSheaf))) := by
  let K := (DerivedCategory.singleFunctor W.Modules 0).obj (SheafOfModules.unit W.ringCatSheaf)
  have hβ := derivedBaseChangeIsIsoOnQuasicoherent q h' h (Spec.map (CommRingCat.ofHom φ)) hsq
    inferInstance inferInstance (torIndependent_of_flat_left h _) (toShHom_comm hsq.w) K
    (Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_homology_singleFunctor_obj
      0 (SheafOfModules.unit W.ringCatSheaf)
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit W))
  have hqc := isQuasicoherent_homology_derivedPushforward_single_zero h
    (SheafOfModules.unit W.ringCatSheaf)
    (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit W)
  exact ⟨(StacksDraft.PseudoCoherence.extendScalarsDerived φ).mapIso
      ((derivedGlobalSectionsOverPushforwardIso h).app K) ≪≫
    (derivedGlobalSectionsSpecPullbackIso φ _ hqc).symm ≪≫
    (derivedGlobalSectionsOver (𝟙 (Spec (.of A')))).mapIso
      (@asIso _ _ _ _ (derivedBaseChangeMap q.toLRSHom.toShHom h'.toLRSHom.toShHom
          h.toLRSHom.toShHom (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
          (toShHom_comm hsq.w) K) hβ ≪≫
        (derivedPushforward h'.toLRSHom.toShHom).mapIso
          (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso q.toLRSHom.toShHom)) ≪≫
    ((derivedGlobalSectionsOverPushforwardIso h').app _).symm⟩

end Affine

end AlgebraicGeometry
