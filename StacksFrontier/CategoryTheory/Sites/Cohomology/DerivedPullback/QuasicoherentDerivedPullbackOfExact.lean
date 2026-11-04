module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalenceModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescentOfToposHom

/-!
# Derived pullback and quasi-coherent cohomology along an exact pullback

Let `f : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪')` be a morphism of ringed topoi whose pullback of modules is
exact. Then `H^q(Lf^*K) = f^*H^q(K)`, and pullback of modules preserves quasi-coherence
(Stacks 03DO), so `Lf^*` carries `D_{QCoh}(𝒪')` into `D_{QCoh}(𝒪)`. Along an equivalence of
ringed topoi quasi-coherence is intrinsic (Stacks 03DM), so `Lf^*` also reflects `D_{QCoh}`.

## Main results

* `OfRingedToposHom.derivedCategoryB_isQuasicoherentOnSite_derivedPullback_of_exact`
* `OfRingedToposHom.derivedCategoryB_isQuasicoherentOnSite_of_derivedPullback`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom

universe w

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

section Exact

variable [PreservesFiniteLimits f.toModulesHom.pullbackModules]

/-- `H^q(Lf^*K) ≅ f^*H^q(K)` for a morphism of ringed topoi whose pullback of modules is
exact. -/
def homologyDerivedPullbackObjIso
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (q : ℤ) :
    (DerivedCategory.homologyFunctor _ q).obj
        ((DerivedPullbackOfToposHom.derivedPullback f).obj K) ≅
      f.toModulesHom.pullbackModules.obj ((DerivedCategory.homologyFunctor _ q).obj K) :=
  letI := RingedToposHom.pullbackModules_preservesFiniteColimits f
  homologyObjIsoOfIsoAdjunctionBoundedBelowDescent f.toModulesHom.pullbackModules
    (derivedPullbackNatIso f) K q

/-- **`Lf^*` carries `D_{QCoh}(𝒪')` into `D_{QCoh}(𝒪)`** along a morphism of ringed topoi whose
pullback of modules is exact: `H^q(Lf^*K) = f^*H^q(K)` and `f^*` preserves quasi-coherence
(Stacks 03DO). -/
theorem derivedCategoryB_isQuasicoherentOnSite_derivedPullback_of_exact
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{w, w, w, w}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) K) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{w, w, w, w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((DerivedPullbackOfToposHom.derivedPullback f).obj K) := fun q ↦
  SheafOfModules.IsQuasicoherentOnSite.of_iso (homologyDerivedPullbackObjIso f K q).symm
    (RingedToposHom.isQuasicoherentOnSite_pullbackModules f _ (hK q))

end Exact

/-- **`Lf^*` reflects `D_{QCoh}` along an equivalence of ringed topoi**: `H^q(Lf^*K) = f^*H^q(K)`
and quasi-coherence is intrinsic (Stacks 03DM). -/
theorem derivedCategoryB_isQuasicoherentOnSite_of_derivedPullback
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{w, w, w, w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((DerivedPullbackOfToposHom.derivedPullback f).obj K)) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{w, w, w, w}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) K := fun q ↦
  (RingedToposHom.isQuasicoherentOnSite_iff_pullbackModules f _).2
    (SheafOfModules.IsQuasicoherentOnSite.of_iso (homologyDerivedPullbackObjIso f K q) (hK q))

end Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom
