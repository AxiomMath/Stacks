module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DerivedPullbackReflection

/-!
# One Tor test descends along an exact, zero-reflecting pullback

The single-test form of
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_hasTorAmplitude_derivedPullback`
of `StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/DerivedPullbackReflection.lean`:
the vanishing of `Hⁱ(E ⊗^L 𝓕[0])` is read off that of `Hⁱ(Lf^*E ⊗^L (f^*𝓕)[0])`, test module by
test module, with the same proof.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_of_derivedPullback`.

## References

* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi
open Stacks.Cohomology.CohomologicalDescent
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.SheafOfModules.DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X.toRingedSite) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} Y.toRingedSite) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]

include hmos in
/-- **One Tor test descends along an exact, zero-reflecting pullback.**  If the degreewise
pullback `f^*` of sheaves of modules along `f` reflects the zero object and
`Hⁱ(Lf^*E ⊗^L_{T'} (f^*𝓕)[0]) = 0` for a derived tensor product datum `T'` on the source, then
`Hⁱ(E ⊗^L_T 𝓕[0]) = 0` for *any* derived tensor product datum `T` on the target.

For a sheaf of `O'`-modules `𝓕`, the derived tensor products `E ⊗^L_T 𝓕[0]` and
`Lf^*E ⊗^L_{T'} (f^*𝓕)[0]` are computed by `Tot(K ⊗_{O'} L)` and `Tot(f^*K ⊗_O f^*L)` for a
K-flat representative `K` of `E` and a K-flat resolution `L` of `𝓕[0]`; those two total
complexes correspond under `f^*`, which also commutes with the cohomology functors.  So the
cohomology sheaves of the first are carried to those of the second by `f^*`, and `f^*` detects
their vanishing. -/
theorem isZero_homology_tensor_single_of_derivedPullback
    (hzero : ∀ M : RingedSite.Modules.{u, u, u} Y.toRingedSite,
      IsZero (f.pullbackTopos.obj M) → IsZero M)
    (T : DerivedTensorProduct Y.toRingedSite) (T' : DerivedTensorProduct X.toRingedSite)
    (E : RingedSite.DerivedModules Y.toRingedSite)
    (F : RingedSite.Modules.{u, u, u} Y.toRingedSite) (i : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules X.toRingedSite) i).obj
      ((T'.tensor.obj ((derivedPullback f).obj E)).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules X.toRingedSite) 0).obj
          (f.pullbackTopos.obj F))))) :
    IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules Y.toRingedSite) i).obj
      ((T.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules Y.toRingedSite) 0).obj F))) := by
  obtain ⟨K, g, hK, hKt, hKq, -⟩ := Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution
    Y.O (DerivedCategory.Q.objPreimage E)
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ g).2 hKq
  obtain ⟨L, p, hL, hLt, hLq, -⟩ := Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution
    Y.O ((CochainComplex.singleFunctor _ 0).obj F)
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hLq
  have eE : DerivedCategory.Q.obj K ≅ E :=
    asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have eF : DerivedCategory.Q.obj L ≅
      (DerivedCategory.singleFunctor (RingedSite.Modules Y.toRingedSite) 0).obj F :=
    asIso (DerivedCategory.Q.map p)
  have eA : (T.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules Y.toRingedSite) 0).obj F) ≅
      DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex Y.O).obj K).obj L) :=
    ((T.tensor.mapIso eE).app _).symm ≪≫
      ((T.tensor.obj (DerivedCategory.Q.obj K)).mapIso eF).symm ≪≫
      T.comparisonRight K L hL
  have hpf : Stacks.Sheaves.InverseImageExactness.PullbackPreservesIsFlatUniv.{u} :=
    AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlatUniv
  have hg := Stacks.Sheaves.InverseImageExactness.inverseImagePreservesShortExact f
  have hLf := Stacks.Sheaves.InverseImageExactness.kFlat_pullbackComplex_of_univ f hmos hpf hg
    L hL hLt
  have eE' : DerivedCategory.Q.obj ((pullbackComplex f).obj K) ≅ (derivedPullback f).obj E :=
    ((f.pullbackTopos.mapDerivedCategoryFactors).app K).symm ≪≫
      (derivedPullbackObjIso f (DerivedCategory.Q.obj K)).symm ≪≫
      (derivedPullback f).mapIso eE
  have eF' : DerivedCategory.Q.obj ((pullbackComplex f).obj L) ≅
      (DerivedCategory.singleFunctor (RingedSite.Modules X.toRingedSite) 0).obj
        (f.pullbackTopos.obj F) :=
    ((f.pullbackTopos.mapDerivedCategoryFactors).app L).symm ≪≫
      (derivedPullbackObjIso f (DerivedCategory.Q.obj L)).symm ≪≫
      (derivedPullback f).mapIso eF ≪≫ derivedPullbackSingleFunctorObjIso f F
  have eBig : (derivedPullback f).obj ((T.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules Y.toRingedSite) 0).obj F)) ≅
      (T'.tensor.obj ((derivedPullback f).obj E)).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules X.toRingedSite) 0).obj
          (f.pullbackTopos.obj F)) :=
    (derivedPullback f).mapIso eA ≪≫
      derivedPullbackObjIso f _ ≪≫
      (f.pullbackTopos.mapDerivedCategoryFactors).app _ ≪≫
      DerivedCategory.Q.mapIso
        (Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso f hmos K L) ≪≫
      (T'.comparisonRight ((pullbackComplex f).obj K) ((pullbackComplex f).obj L) hLf).symm ≪≫
      (T'.tensor.mapIso eE').app _ ≪≫
      (T'.tensor.obj ((derivedPullback f).obj E)).mapIso eF'
  exact hzero _ <| IsZero.of_iso
    (h.of_iso ((DerivedCategory.homologyFunctor (RingedSite.Modules X.toRingedSite) i).mapIso eBig))
    (derivedPullbackHomologyObjIso f ((T.tensor.obj E).obj
      ((DerivedCategory.singleFunctor (RingedSite.Modules Y.toRingedSite) 0).obj F)) i).symm

end Stacks.SheafOfModules.DerivedTensorProduct

end
