module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleMonoidal
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleKFlatRepresentative
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionWithFlatTerms
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesCompare
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Total tensor complexes on the small étale site against pulled-back ones

Let `S` be a scheme and `ε : S_étale ⟶ S_Zar` the comparison morphism of ringed sites.  For
K-flat representatives `ε^*P₁` of `P` and `ε^*L₁` of `L`, the total tensor complex `Tot(P ⊗ L)`
on `S_étale` is isomorphic in the derived category to `ε^*Tot(P₁ ⊗ L₁)`.  This is step 3–4 of
the proof of `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_homology_tensorComplex`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.tensorComplexQIsoEtalePullback`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-! ### The small étale site of a scheme -/

namespace AlgebraicGeometry.SmallEtale

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The total tensor complex on `S_étale` against the pullback of a total tensor complex on
`S_Zar`.**  Given a K-flat complex `P` and a complex `L` of `𝒪`-modules on `S_étale`, a K-flat
complex `P₁` with flat terms and a complex `L₁` on `S_Zar`, and isomorphisms `Q(ε^*P₁) ≅ Q(P)`
and `Q(ε^*L₁) ≅ Q(L)` in the derived category, this is the isomorphism
`Q(Tot(P ⊗ L)) ≅ Q(ε^*Tot(P₁ ⊗ L₁))`: both sides compute the canonical derived tensor product of
the small étale ringed site, on the K-flat factors `P` and `ε^*P₁`, and
`Tot(ε^*P₁ ⊗ ε^*L₁) ≅ ε^*Tot(P₁ ⊗ L₁)` is Stacks 03EL in each bidegree. -/
def tensorComplexQIsoEtalePullback
    (P L : CochainComplex (EtaleModules B S hS) ℤ)
    (hP : Stacks.SheafOfModules.IsKFlat (smallEtaleRingedSite B S hS).O P)
    (P₁ L₁ : CochainComplex (SheafOfModules.{u} S.ringCatSheaf) ℤ)
    (hP₁ : Stacks.SheafOfModules.IsKFlat S.zariskiRingedSite.O P₁)
    (hP₁flat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := S.zariskiRingedSite.O) (P₁.X i))
    (eP : DerivedCategory.Q.obj ((etalePullbackComplex B S hS).obj P₁) ≅
      (DerivedCategory.Q.obj P : DerivedCategory (EtaleModules B S hS)))
    (eL : DerivedCategory.Q.obj ((etalePullbackComplex B S hS).obj L₁) ≅
      (DerivedCategory.Q.obj L : DerivedCategory (EtaleModules B S hS))) :
    (DerivedCategory.Q.obj (((Stacks.SheafOfModules.Tensor.tensorComplex
        (smallEtaleRingedSite B S hS).O).obj P).obj L) : DerivedCategory (EtaleModules B S hS)) ≅
      DerivedCategory.Q.obj ((etalePullbackComplex B S hS).obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex S.zariskiRingedSite.O).obj P₁).obj L₁)) :=
  let T := Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
    (smallEtaleRingedSite B S hS)
  (T.comparisonLeft P L hP).symm ≪≫
    (T.tensor.mapIso eP.symm).app _ ≪≫ (T.tensor.obj _).mapIso eL.symm ≪≫
    T.comparisonLeft _ _ (isKFlat_etalePullbackComplex B S hS P₁ hP₁ hP₁flat) ≪≫
    DerivedCategory.Q.mapIso
      (Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso
        (toZariskiHom B S hS).toModulesHom P₁ L₁).symm

end AlgebraicGeometry.SmallEtale

end
