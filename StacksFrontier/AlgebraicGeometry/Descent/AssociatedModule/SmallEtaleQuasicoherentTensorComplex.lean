module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleMonoidal
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleKFlatRepresentative
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleTensorComplexQIso
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.DerivedSectionsTensorPseudoCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionWithFlatTerms
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Total tensor complexes with quasi-coherent cohomology on the small étale site of a scheme

Let `S` be a scheme and let `S_étale` be its small étale site.  This file proves that for a
K-flat complex `P` of `𝒪`-modules on `S_étale` and an arbitrary complex `L`, both with
quasi-coherent cohomology sheaves, the total tensor complex `Tot(P ⊗_𝒪 L)` again has
quasi-coherent cohomology sheaves.  Since `Tot(P ⊗_𝒪 L)` computes `P ⊗^𝐋_𝒪 L` for K-flat `P`,
this is the case of a scheme, read on its small étale site, of Derived Categories of Spaces,
Lemma 75.5.6 (Stacks 08F5); the scheme case on the Zariski site is Derived Categories of Schemes,
Lemma 36.3.9 (Stacks 08DX).

## The proof

The small étale and the Zariski site are compared through the morphism of ringed sites
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` of Stacks 08H7.

1. By Stacks 071Q, `AlgebraicGeometry.SmallEtale.derivedAssociatedModule_isEquivalence`, the
   classes of `P` and `L` in `D(S_étale, 𝒪)` are of the form `ε^*A` and `ε^*B` with `A`, `B` in
   `D_QCoh(𝒪_S)`.  Representing `A` and `B` by K-flat complexes `P₁`, `L₁` with flat terms
   (Stacks 06YS, `Stacks.SheafOfModules.exists_kFlatResolution`), the classes of `P` and `L` are
   those of the degreewise pullbacks `ε^*P₁` and `ε^*L₁`.
2. `ε^*P₁` is K-flat by Stacks 0G7E,
   `Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.kFlat_pullbackComplex`, which is
   stated for a morphism of ringed topoi at free universes and so applies to `ε`.
3. Two K-flat complexes with the same class compute the same derived tensor product, so
   `Q(Tot(P ⊗ L)) ≅ Q(Tot(ε^*P₁ ⊗ ε^*L₁))`; this is read off the K-flat comparisons of the
   canonical derived tensor product of the small étale ringed site.
4. `Tot(ε^*P₁ ⊗ ε^*L₁) ≅ ε^*Tot(P₁ ⊗ L₁)` is
   `Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso`, Stacks 03EL in each bidegree.
   Steps 3 and 4 together are `AlgebraicGeometry.SmallEtale.tensorComplexQIsoEtalePullback`.
5. `ε^*` is exact (Stacks 08H8) and preserves quasi-coherence (Stacks 03DV (2)), and the
   cohomology sheaves of `Tot(P₁ ⊗ L₁)` are quasi-coherent by Stacks 08DX, read on K-flat
   representatives in `Stacks.Duality.isQuasicoherent_homology_totalTensorComplex`.

## Main results

* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_homology_tensorComplex`: the statement of
  the title.

## Implementation notes

The complexes on `S_étale` are written at the spelling `AlgebraicGeometry.RingedSite.Modules` of
the small étale ringed site, with its three universes given explicitly.  The `ε^*` layer —
exactness, K-flatness of pullbacks, and the representative given by Stacks 071Q — is in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleKFlatRepresentative.lean`.

## References

* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-! ### The small étale site of a scheme -/

namespace AlgebraicGeometry.SmallEtale

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The case of a scheme of Stacks 08F5, on the small étale site and on representatives.**  Let
`P` be a K-flat complex of `𝒪`-modules on `S_étale` and `L` an arbitrary complex of `𝒪`-modules,
both with quasi-coherent cohomology sheaves.  Then every cohomology sheaf of the total tensor
complex `Tot(P ⊗_𝒪 L)` is quasi-coherent.

See the module docstring for the proof. -/
theorem isQuasicoherentOnSite_homology_tensorComplex
    (P L : CochainComplex (EtaleModules B S hS) ℤ)
    (hP : Stacks.SheafOfModules.IsKFlat (smallEtaleRingedSite B S hS).O P)
    (hPq : ∀ n : ℤ, ((HomologicalComplex.homologyFunctor (EtaleModules B S hS)
      (ComplexShape.up ℤ) n).obj P).IsQuasicoherentOnSite)
    (hLq : ∀ n : ℤ, ((HomologicalComplex.homologyFunctor (EtaleModules B S hS)
      (ComplexShape.up ℤ) n).obj L).IsQuasicoherentOnSite)
    (n : ℤ) :
    ((HomologicalComplex.homologyFunctor (EtaleModules B S hS) (ComplexShape.up ℤ) n).obj
      (((Stacks.SheafOfModules.Tensor.tensorComplex (smallEtaleRingedSite B S hS).O).obj P).obj
        L)).IsQuasicoherentOnSite := by
  obtain ⟨P₁, hP₁, hP₁flat, hP₁q, ⟨eP⟩⟩ := exists_etalePullbackComplex_iso B S hS P hPq
  obtain ⟨L₁, hL₁, hL₁flat, hL₁q, ⟨eL⟩⟩ := exists_etalePullbackComplex_iso B S hS L hLq
  let e := tensorComplexQIsoEtalePullback B S hS P L hP P₁ L₁ hP₁ hP₁flat eP eL
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((DerivedCategory.homologyFunctorFactors (EtaleModules B S hS) n).app _).symm ≪≫
      (DerivedCategory.homologyFunctor (EtaleModules B S hS) n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (EtaleModules B S hS) n).app _)
    (isQuasicoherentOnSite_homology_etalePullbackComplex B S hS _ n ?_)
  exact Stacks.Duality.isQuasicoherent_homology_totalTensorComplex S P₁ L₁ hP₁ hL₁ hP₁q hL₁q n

end AlgebraicGeometry.SmallEtale

end
