module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DerivedPullbackAlongRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackTensorAlongASiteMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness

/-!
# Derived pullback *reflects* Tor amplitude when it is exact and detects the zero sheaf

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi presented by a morphism of the
underlying sites along which the degreewise pullback `f^*` of sheaves of modules is exact and
reflects the zero object. Then an object `E` of `D(O')` has Tor amplitude in `[a, b]` as soon as
`Lf^* E` has, which is the converse of Stacks 08H5. The two hypotheses on `f^*` are the two
assertions that Stacks 08H8 makes about the comparison of the small étale and the Zariski site.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_hasTorAmplitude_derivedPullback`:
  Tor amplitude in a fixed interval descends along an exact, zero-reflecting pullback.
* `hasFiniteTorDimension_of_hasFiniteTorDimension_derivedPullback`, in the same namespace: the
  same for finite Tor dimension.

## Implementation notes

The source argues with the flat base change `Lf^*(E ⊗^L 𝓕) ≅ Lf^*E ⊗^L f^*𝓕` of Stacks 07A4.
Here the argument is a computation on representatives, which needs no comparison of two derived
tensor product data and so applies to the *arbitrary* data `T`, `T'` that
`Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude` is measured against:

* `E` is represented by a K-flat complex `K` with flat terms and `𝓕[0]` by a K-flat resolution
  `L` with flat terms, both by Stacks 06YF
  (`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution`); the right-hand K-flat
  comparison field of `T` then identifies `E ⊗^L_T 𝓕[0]` with `Tot(K ⊗_{O'} L)`;
* `f^*K` and `f^*L` are again K-flat with flat terms, by Stacks 0G7E
  (`Stacks.Sheaves.InverseImageExactness.kFlat_pullbackComplex_of_univ`), so the same field of
  `T'` identifies `Lf^*E ⊗^L_{T'} (f^*𝓕)[0]` with `Tot(f^*K ⊗_O f^*L)`;
* `f^*Tot(K ⊗_{O'} L) ≅ Tot(f^*K ⊗_O f^*L)` is Stacks 03EL read on total complexes,
  `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso`;
* exactness of `f^*` turns `Lf^*` into the functor induced by `f^*` on derived categories
  (`Stacks.Cohomology.CohomologicalDescent.derivedPullbackObjIso`), identifies `Lf^*(𝓕[0])` with
  `(f^*𝓕)[0]` and commutes `Lf^*` with the cohomology functors.

Only *objects* are compared, never morphisms: the conclusion is the vanishing of a cohomology
sheaf, and `CategoryTheory.Limits.IsZero` transports along any isomorphism, so no coherence
between the isomorphisms above is needed.

## References

* [Stacks Project, Tag 08HF](https://stacks.math.columbia.edu/tag/08HF)
* [Stacks Project, Tag 08H5](https://stacks.math.columbia.edu/tag/08H5)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
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
/-- The converse of Stacks 08H5 for a pullback which is exact and reflects the zero sheaf: if the
degreewise pullback `f^*` of sheaves of modules along `f` reflects the zero object, and `Lf^* E`
has Tor amplitude in `[a, b]` for a derived tensor product datum `T'` on the source, then `E` has
Tor amplitude in `[a, b]` for *any* derived tensor product datum `T` on the target. -/
theorem hasTorAmplitude_of_hasTorAmplitude_derivedPullback
    (hzero : ∀ M : RingedSite.Modules.{u, u, u} Y.toRingedSite,
      IsZero (f.pullbackTopos.obj M) → IsZero M)
    (T : DerivedTensorProduct Y.toRingedSite) (T' : DerivedTensorProduct X.toRingedSite)
    (E : RingedSite.DerivedModules Y.toRingedSite) (a b : ℤ)
    (hamp : HasTorAmplitude T' ((derivedPullback f).obj E) a b) :
    HasTorAmplitude T E a b := by
  intro F i hi
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
  have hKf := Stacks.Sheaves.InverseImageExactness.kFlat_pullbackComplex_of_univ f hmos hpf hg
    K hK hKt
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
  refine hzero _ (IsZero.of_iso ?_ (derivedPullbackHomologyObjIso f ((T.tensor.obj E).obj
    ((DerivedCategory.singleFunctor (RingedSite.Modules Y.toRingedSite) 0).obj F)) i).symm)
  exact (hamp (f.pullbackTopos.obj F) i hi).of_iso
    ((DerivedCategory.homologyFunctor (RingedSite.Modules X.toRingedSite) i).mapIso eBig)

include hmos in
/-- Finite Tor dimension descends along an exact, zero-reflecting pullback: the interval in which
`Lf^* E` has Tor amplitude is one in which `E` has it. -/
theorem hasFiniteTorDimension_of_hasFiniteTorDimension_derivedPullback
    (hzero : ∀ M : RingedSite.Modules.{u, u, u} Y.toRingedSite,
      IsZero (f.pullbackTopos.obj M) → IsZero M)
    (T : DerivedTensorProduct Y.toRingedSite) (T' : DerivedTensorProduct X.toRingedSite)
    (E : RingedSite.DerivedModules Y.toRingedSite)
    (h : HasFiniteTorDimension T' ((derivedPullback f).obj E)) :
    HasFiniteTorDimension T E := by
  obtain ⟨a, b, hamp⟩ := h
  exact ⟨a, b, hasTorAmplitude_of_hasTorAmplitude_derivedPullback f hmos hzero T T' E a b hamp⟩

end Stacks.SheafOfModules.DerivedTensorProduct

end
