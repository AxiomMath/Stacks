module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectDetectedByGlobalSections
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom
import StacksCore.Tactic.StacksAttribute

/-!
# The vanishing of Stacks 0GET with the two duality inputs discharged

`AlgebraicGeometry.eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect` of
`StacksFrontier/AlgebraicGeometry/Perfect/RelativelyPerfectDetectedByGlobalSections.lean` proves,
for a perfect generator `G` of `D_QCoh(𝒪_X)` and an object `K` of `D_QCoh(𝒪_X)` whose perfect
twists have perfect derived global sections, that `Ext^i_X(G, K)` and `Hom(G⟦-i⟧, K)` vanish for
`i ≪ 0`. It takes two inputs about the perfect object `G` as explicit arguments: perfectness of
the dual `G^∨`, and invertibility of the canonical map `K⟦i⟧ ⊗^L G^∨ ⟶ R𝓗om(G, K⟦i⟧)` of
[Stacks, Tag 08I1]. Both are assertions of [Stacks, Tag 08DQ] and both are proved in the library
for a perfect object at a free universe:

* the first assertion of 08DQ is `Stacks.SheafOfModules.isPerfect_derivedDual`;
* the third assertion of 08DQ is
  `Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect`.

`eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect'` below is that theorem with both
arguments discharged; its hypotheses are those of the source together with the perfect generator
`G`, whose existence is Stacks 09IS (`Stacks.SheafOfModules.exists_isPerfect_generator`). The
full statement of Stacks 0GET is
`AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_of_isPerfect_derivedGlobalSectionsOver_tensor`.

## Implementation notes

A perfect generator of `D_QCoh(𝒪_X)` at a quasi-compact quasi-separated scheme, Stacks 09IS, is
`Stacks.SheafOfModules.exists_isPerfect_generator` of
`StacksFrontier/AlgebraicGeometry/Perfect/QcqsPerfectGenerator.lean`, stated at
`HasDerivedCategory.standard` like this file; the generator is an argument here so that the lemma
applies to any chosen one.

**A further obstruction on the way to Stacks 0FYH: 0FYG cannot be applied where 0FYD lives.**
The abstract representability theorem Stacks 0FYG,
`CategoryTheory.exists_iso_comp_linearYoneda_of_finiteDimensional` of
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/RepresentabilityTheorem/Basic.lean`, demands
`[Category.{v} D]`, `[HasCoproducts.{v} D]` and `IsCompactlyGenerated.{v} D` at one and the
same `v`. Compact generation of `D_QCoh(𝒪_X)` is proved only at the locally small model, where
`v = u`, and it has to be: at `HasDerivedCategory.standard` the hom universe is `u + 1`, and
`HasCoproducts.{u + 1}` of `𝒪_X`-modules is false rather than merely unavailable — the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCompactGeneration.lean` set this
out. But Stacks 0FYD
(`StacksFrontier/AlgebraicGeometry/DerivedVarieties/CoherentCharacterization.lean`), Stacks 08DT
(`AlgebraicGeometry.hasCoproducts_quasicoherentDerivedCategory`, which supplies only
`HasCoproducts.{u}`) and the perfectness machinery of this file all live at the standard model.
So a cross-model transport is part of any proof of Stacks 0FYH, and not an afterthought to
one.

The transport is not hopeless: `StacksDraft.DerivedModel.modelEquiv` of
`StacksFrontier/Homology/DerivedCategory/ModelComparison.lean` compares any two chosen derived
categories, `StacksDraft.DerivedModel.schemeModulesComparison` of
`StacksFrontier/Homology/DerivedCategory/ModelComparisonTransport.lean` is the scheme-specific
bridge, and `StacksDraft.CompactDevissage.isIso_of_isIso_app_freeYoneda_anyModel` and
`AlgebraicGeometry.derivedCategoryB_derivedPushforward_of_qcqs` are worked examples. What does
*not* transport is the universe: `CategoryTheory.IsCompactObject.{w}` carries across an
additive equivalence only at a fixed `w`, so compactness arrives at the standard model still at
`w = u` while 0FYG there would want `w = u + 1`. See
`StacksFrontier/Homology/Perfect/CompactObjectAnyModel.lean`.

## References

* [Stacks Project, Lemma 37.69.6 (Tag 0GET)](https://stacks.math.columbia.edu/tag/0GET)
* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 0FYG](https://stacks.math.columbia.edu/tag/0FYG)
* [Stacks Project, Tag 0FYH](https://stacks.math.columbia.edu/tag/0FYH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.SheafOfModules

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (ComplexShape.up ℤ)]

/-- **The vanishing of Stacks 0GET, with the duality inputs proved.** Let `A` be a ring, let `X`
be a scheme separated, of finite presentation and flat over `A`, let `G` be a perfect generator
of `D_QCoh(𝒪_X)`, and let `K` be an object of `D_QCoh(𝒪_X)`. If `RΓ(X, K ⊗^L_{𝒪_X} E)` is a
perfect object of `D(A)` for every perfect object `E` of `D(𝒪_X)`, then `Ext^i_X(G, K)` and
`Hom_{D(𝒪_X)}(G⟦-i⟧, K)` vanish for `i ≪ 0`.

This is `eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect` with its two arguments
about `G` discharged by [Stacks, Tag 08DQ]: the dual `G^∨` is perfect by the first assertion,
`Stacks.SheafOfModules.isPerfect_derivedDual`, and the map of [Stacks, Tag 08I1] out of
`K⟦i⟧ ⊗^L G^∨` is invertible for every `i` by the third,
`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect`.

That `K` is `Spec(A)`-perfect, the conclusion of Stacks 0GET, is
`AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_of_isPerfect_derivedGlobalSectionsOver_tensor`
of `StacksFrontier/AlgebraicGeometry/Perfect/RelativelyPerfectFromGlobalSections.lean`. -/
public theorem eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect'
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [QuasiCompact f] [Flat f]
    [LocallyOfFinitePresentation f]
    (hqc : CompactSpace X) (hqs : QuasiSeparatedSpace X)
    (G K : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (hgen : ∀ L : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj L).IsQuasicoherent) →
        (∀ (n : ℤ) (g : G⟦n⟧ ⟶ L), g = 0) → IsZero L)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent)
    (hperf : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      (ringedSite X.sheaf).IsPerfect E →
        ∃ M : DerivedCategory (ModuleCat.{u} A), StacksDraft.Perfect.IsPerfect M ∧
          Nonempty ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
              (((derivedTensor X.sheaf).obj K).obj E) ≅
            (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapDerivedCategory.obj M)) :
    (∃ N : ℤ, ∀ i ≤ N, Subsingleton (DerivedCategory.Ext G K i)) ∧
      ∃ N : ℤ, ∀ i ≤ N, Subsingleton (G⟦-i⟧ ⟶ K) :=
  eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect f hqc hqs G K hG
    (isPerfect_derivedDual X.sheaf G hG) hgen hK
    (fun i => isIso_derivedTensorDualToSheafHom_of_isPerfect X.sheaf G (K⟦i⟧) hG) hperf

end AlgebraicGeometry

end
