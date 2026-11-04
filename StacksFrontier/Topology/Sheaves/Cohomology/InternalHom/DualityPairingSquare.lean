module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DualityPairingSquareOnClasses
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualLeftDual
public import StacksFrontier.Topology.Sheaves.RingedSpace.SheafifyOverOpen

/-!
# The duality pairing square

Let `(X, O_X)` be a ringed space and let `K` and `E` be objects of `D(O_X)` with `E` perfect,
`E^∨ = RSheafHom(E, O_X)` and `ε : E^∨ ⊗^L E ⟶ O_X` the evaluation map. The diagram

`H⁰(X, K ⊗^L E^∨) × H⁰(X, E) ⟶ H⁰(X, K ⊗^L E^∨ ⊗^L E)`
`        ↓                               ↓`
`Hom_X(E, K) × H⁰(X, E)        ⟶       H⁰(X, K)`

commutes, where the top arrow is the cup product, the right arrow is induced by `ε`, the left
arrow is the identification of Lemma 08DQ and the bottom arrow evaluates a morphism on a class
(Stacks 0FVB). This file proves it with the top arrow in the form of Stacks 0FP2, the tensor
product of the morphisms out of `O_X` that two classes name;
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DualityPairingCupProduct` identifies that
form with the cup product.

The proof follows the source. The canonical map `Φ : K ⊗^L E^∨ ⟶ RSheafHom(E, K)` of
Stacks 08I1 followed by the application morphism of Stacks 08J8 is the contraction against `ε`:

`(Φ ▷ E) ≫ app_{E,K} = α ≫ (K ◁ ε) ≫ ρ`,

which is the associativity of the composition of Stacks 0A8V against the application morphism
(`Stacks.SheafOfModules.compositionApplicationLaw`) at intermediate object `O_X`. Hence the
morphism `E ⟶ K` that Lemma 08DQ attaches to `ξ` is `(1_K ⊗ ε) ∘ (ξ̃ ⊗ 1_E)`, and the square
becomes `(1_K ⊗ ε) ∘ (ξ̃ ⊗ η̃) = (1_K ⊗ ε) ∘ (ξ̃ ⊗ 1_E) ∘ (1_O ⊗ η̃)`.

## Main results

* `Stacks.SheafOfModules.derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit`:
  the canonical map of Stacks 08I1 followed by application is the contraction against `ε`.
* `Stacks.SheafOfModules.derivedDualPairingSquare`: the square of Stacks 0FVB with the top
  arrow the tensor product of the morphisms out of the structure sheaf; the square with the cup
  product is `Stacks.SheafOfModules.derivedDualPairingSquare_cup`.

## References

* [Stacks Project, Tag 0FVB](https://stacks.math.columbia.edu/tag/0FVB)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 0FP2](https://stacks.math.columbia.edu/tag/0FP2)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

-- The ring sheaf of `ringedSite Rc` is `Stacks.SheafOfModules.Tensor.ringSheaf Rc`, which pairs
-- `Rc.obj ⋙ forget₂ CommRingCat RingCat` with the sheaf condition directly, while the objects
-- below live over `StructureSheafModules Rc = SheafOfModules (structureSheaf Rc)`, i.e. over
-- `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`. The two sheaves of rings are the same
-- sheaf, but seeing it needs `Tensor.ringSheaf` and `CategoryTheory.sheafCompose` unfolded, which
-- instance search does not do at reducible transparency: without this the derived category of one
-- spelling has no `Preadditive` instance at the other, so the identification
-- `H⁰(X, Z) ≃+ (O_X ⟶ Z)` of Stacks 08JA cannot be applied. Same attribute, on the same
-- declaration, for the same reason as in the neighbour that defines `ringedSite`,
-- `StacksDraft.Topology.Sheaves.Cohomology.HomComplexAndStrictPerfection`
-- `.InternalHomComplexQuasiIso`.
attribute [local implicit_reducible] CategoryTheory.sheafCompose Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- **The canonical map of Stacks 08I1 followed by application is the contraction against the
evaluation of the dual.** For objects `L` and `M` of `D(O_X)`, with
`Φ : M ⊗^L L^∨ ⟶ RSheafHom(L, M)` the canonical map and `app` the application morphism of
Stacks 08J8,

`(Φ ▷ L) ≫ app = α_{M, L^∨, L} ≫ (M ◁ ε) ≫ ρ_M`. -/
theorem derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit
    (L M : DerivedCategory (StructureSheafModules Rc)) :
    (letI := derivedMonoidalStructure Rc
    derivedTensorDualToSheafHom Rc L M ▷ L ≫ derivedSheafHomCounit Rc L M =
      derivedDualContraction Rc M L) := by
  have h := compositionApplicationLaw Rc L (RingedSite.derivedStructureSheaf (ringedSite Rc)) M
  unfold CompositionApplicationLaw at h
  rw [derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation] at h
  exact derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit_of_laws
    Rc L M (RingedSite.derivedDualEvaluation (ringedSite Rc) L) h
    (derivedStructureSheafHomIso_inv_whiskerRight_comp_derivedSheafHomCounit_monoidal Rc M)

section RingedSpace

variable (X : RingedSpace.{u, u}) (K E : DerivedCategory (StructureSheafModules X.sheaf))

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.hasSheafifyOverOpen
  Stacks.Topology.RingedSpaceSheafifyOpens.wEqualsLocallyBijectiveOverOpen

/-- **The square of Stacks 0FVB with the top arrow the tensor product of the morphisms out of the
structure sheaf.** Let `(X, O_X)` be a ringed space and let `K` and `E` be objects of `D(O_X)`
with `E` perfect (Tag 08CM). The diagram

`H⁰(X, K ⊗^L E^∨) × H⁰(X, E) ⟶ H⁰(X, K ⊗^L E^∨ ⊗^L E)`
`        ↓                               ↓`
`Hom_X(E, K) × H⁰(X, E)        ⟶       H⁰(X, K)`

commutes: for `ξ ∈ H⁰(X, K ⊗^L E^∨)` and `η ∈ H⁰(X, E)`, the class of the tensor product of
the morphisms out of `O_X` that `ξ` and `η` name, followed by the map induced on `H⁰` by `ε : E^∨ ⊗^L E ⟶ O_X` (Example 0FPC) is the morphism
`E ⟶ K` attached to `ξ` by the identification `H⁰(X, K ⊗^L E^∨) = Hom_{D(O_X)}(E, K)` of
Lemma 08DQ (`Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap`), evaluated on `η`.

A class of `H⁰(X, Z)` is identified with a morphism `O_X ⟶ Z` by
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv`; the top arrow is
`Stacks.SheafOfModules.derivedSectionTensor` read through it, which is the cup product by
`Stacks.SheafOfModules.derivedStructureSheafGlobalSectionsEquiv_globalCupProductZero`, and the
square with the cup product itself is `Stacks.SheafOfModules.derivedDualPairingSquare_cup`. The
right arrow is `H⁰` of
`Stacks.SheafOfModules.derivedDualContraction`, which is `1_K ⊗ ε` followed by the unit
constraint `K ⊗^L O_X = K`. The structure sheaf is a perfect object
(`Stacks.SheafOfModules.isPerfect_derivedStructureSheaf_space`). -/
theorem derivedDualPairingSquare
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X) E)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
        (((derivedTensor X.sheaf).obj K).obj (derivedDual X.sheaf E))) : Type u))
    (η : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj E) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).map
          (derivedDualContraction X.sheaf K E))
        ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf)
          (((derivedTensor X.sheaf).obj
            (((derivedTensor X.sheaf).obj K).obj (derivedDual X.sheaf E))).obj E)).symm
          (derivedSectionTensor X.sheaf
            (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf)
              (((derivedTensor X.sheaf).obj K).obj (derivedDual X.sheaf E)) ξ)
            (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite X.sheaf) E η))) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).map
          (derivedTensorDualGlobalSectionsMap X.sheaf E K ξ)) η := by
  have hE' := Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X E hE
  have happ := derivedTensorDualToSheafHom_whiskerRight_comp_derivedSheafHomCounit X.sheaf E K
  have h := derivedDualPairingSquareOnClasses_of_applicationLaw X.sheaf K E hE' happ ξ η
  convert h using 1

end RingedSpace

end Stacks.SheafOfModules

end
