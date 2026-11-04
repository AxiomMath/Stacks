module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentTorTests
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.SiteEquivalenceDerivedTensorTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.ModuleEquivalenceTransport

/-!
# Quasi-coherent Tor tests on the small étale site of a quasi-separated scheme

Let `S` be a quasi-separated scheme and `E` an object of `D_QCoh(S_étale, 𝒪)`.  If
`Hⁱ(E ⊗^L 𝒢[0]) = 0` for `i ∉ [a, b]` and every quasi-coherent `𝒪`-module `𝒢` on the small étale
site, then `E` has Tor amplitude in `[a, b]`.

This is the representable case of Stacks 08IL, the second paragraph of the source's proof: by
Stacks 071Q write `E = ε^*E₀` with `E₀` in `D_QCoh(𝒪_S)`; the quasi-coherent modules `ε^*𝓕₀` are
among the tests, and
`AlgebraicGeometry.SmallEtale.hasTorAmplitude_derivedPullback_of_quasicoherent_tests` (flatness of
`ε`, Stacks 08H8, then Stacks 08EA and Stacks 08HF) gives Tor amplitude of `ε^*E₀`.

## Main results

* `AlgebraicGeometry.SmallEtale.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent`: **the
  representable case of Stacks 08IL** on the small étale site of a quasi-separated scheme, for an
  arbitrary derived tensor product datum.

## Implementation notes

Stacks 08HF is stated on the `Type u`-presented model of the small étale ringed topos
(`AlgebraicGeometry.SmallEtale.smallModelRingedTopos`).  The passage between the small étale site
and the model is the reindexing of sheaves of modules along the comparison of sites,
`Stacks.SheafOfModules.SiteEquivalenceDerivedTensor.reindexMod`, which is
`AlgebraicGeometry.SmallEtale.modelModulesEquiv` on the nose and carries the tensor product to
the tensor product (Stacks 01CU); Tor tests cross it by
`Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_iff_of_equivalence`,
and `ε` read on the model is `ε` followed by it
(`AlgebraicGeometry.SmallEtale.pullbackToposIsoAssociatedModel`).

The comparison of sites is continuous and cocontinuous in both directions; the instances are
restated here at the spelling `(smallModelEquiv B S hS).symm`, the one the reindexing is formed
at, because Mathlib's instances for an equivalence of sites are keyed at
`(smallModelEquiv B S hS).inverse` and `.functor`.

All derived categories carry `CategoryTheory.HasDerivedCategory.standard`, the instance at which
Stacks 08HF and 08EA are stated.

`𝒪_S`-modules are spelled `SheafOfModules S.ringCatSheaf` by Stacks 071Q and
`SheafOfModules (ringSheaf S.zariskiRingedTopos.O)` by Stacks 08HF; the two are the same category.
`AlgebraicGeometry.SmallEtale.derivedPullbackModelIso` is stated at the first spelling, and the
exactness instances of `ε_model^*` it needs at that spelling are passed to
`Stacks.DerivedQCoh.mapDerivedCategoryCompIso` as terms, since instance search does not cross
between the two spellings.

## References

* [Stacks Project, Lemma 75.13.8 (Tag 08IL)](https://stacks.math.columbia.edu/tag/08IL)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08HF](https://stacks.math.columbia.edu/tag/08HF)
* [Stacks Project, Tag 08EA](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

open Stacks.Cohomology.CohomologicalDescent Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.SheafOfModules Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance 20000] HasDerivedCategory.standard

-- `moduleSheavesAbelian` is stated at a module universe `max u v w` that elaboration cannot solve
-- for at the small étale site, and `ResolutionByExtensionsByZero.instAbelian` names the abelian
-- structure of `Mod(𝒪_S)` a second way, after which the derived categories of the two spellings of
-- `Mod(𝒪_S)` (Stacks 071Q's and Stacks 08HF's) are compared by unfolding the abelian structures,
-- which does not terminate in budget.  The abelian structure meant is Mathlib's.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The comparison with the model, at the spelling of the reindexing -/

/-- The comparison of the model with the small étale site, read from the model, is continuous. -/
instance isContinuous_smallModelEquiv_symm_functor_smallModelTopology :
    (smallModelEquiv B S hS).symm.functor.IsContinuous
      (smallModelTopology B S hS) (topology B S hS) :=
  inferInstanceAs ((smallModelEquiv B S hS).inverse.IsContinuous
    (smallModelTopology B S hS) (topology B S hS))

/-- The comparison of the small étale site with the model is continuous. -/
instance isContinuous_smallModelEquiv_symm_inverse_smallModelTopology :
    (smallModelEquiv B S hS).symm.inverse.IsContinuous
      (topology B S hS) (smallModelTopology B S hS) :=
  inferInstanceAs ((smallModelEquiv B S hS).functor.IsContinuous
    (topology B S hS) (smallModelTopology B S hS))

/-- The comparison of the model with the small étale site, read from the model, is
cocontinuous: its quasi-inverse is cover preserving. -/
instance isCocontinuous_smallModelEquiv_symm_functor :
    (smallModelEquiv B S hS).symm.functor.IsCocontinuous
      (smallModelTopology B S hS) (topology B S hS) :=
  (Equivalence.toAdjunction _).isCocontinuous_iff_coverPreserving _ _ |>.2
    ((Functor.isContinuous_iff_coverPreserving
      (F := (smallModelEquiv B S hS).symm.inverse)).1 inferInstance)

/-- **Transport of sheaves of modules to the model, as a reindexing along the comparison of
sites.**  This is `AlgebraicGeometry.SmallEtale.modelModulesEquiv` on the nose
(`AlgebraicGeometry.SmallEtale.modelModulesReindex_functor`), at the spelling at which the
comparison of tensor products of Stacks 01CU is stated. -/
abbrev modelModulesReindex :=
  SiteEquivalenceDerivedTensor.reindexMod
    (smallModelTopology B S hS) (smallModelEquiv B S hS).symm (commRingStructureSheaf B S hS)

/-- The reindexing to the model is `AlgebraicGeometry.SmallEtale.modelModulesEquiv`. -/
theorem modelModulesReindex_functor :
    (modelModulesReindex B S hS).functor = (modelModulesEquiv B S hS).functor := rfl

/-! ### `Lε^*` on the model is `ε^*` followed by the transport to the model -/

/-- Transport of sheaves of modules to the model is additive, being a left adjoint. -/
instance additive_modelModulesEquiv_functor : (modelModulesEquiv B S hS).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Transport of sheaves of modules to the model is left exact, being a right adjoint. -/
instance preservesFiniteLimits_modelModulesEquiv_functor :
    PreservesFiniteLimits (modelModulesEquiv B S hS).functor :=
  @PreservesLimitsOfSize.preservesFiniteLimits _ _ _ _ _
    (Adjunction.rightAdjoint_preservesLimits.{0, 0} (modelModulesEquiv B S hS).symm.toAdjunction)

/-- Transport of sheaves of modules to the model is right exact, being a left adjoint. -/
instance preservesFiniteColimits_modelModulesEquiv_functor :
    PreservesFiniteColimits (modelModulesEquiv B S hS).functor :=
  @PreservesColimitsOfSize.preservesFiniteColimits _ _ _ _ _
    (Adjunction.leftAdjoint_preservesColimits.{0, 0} (modelModulesEquiv B S hS).toAdjunction)

/-- **`Lε^*` read on the model is `ε^*` followed by the transport to the model**, on derived
categories: `Lε_model^* E ≅ (ε^* E)|_model`.  All three functors are exact, `Lε_model^*` is then
the functor induced by `ε_model^*`, and `ε_model^* ≅ ε^* ⋙ (transport)` is
`AlgebraicGeometry.SmallEtale.pullbackToposIsoAssociatedModel`. -/
def derivedPullbackModelIso
    (E : DerivedCategory (_root_.SheafOfModules.{u} S.ringCatSheaf)) :
    (derivedPullback (toZariskiSmallModelHom B S hS)).obj E ≅
      (modelModulesEquiv B S hS).functor.mapDerivedCategory.obj
        ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E) :=
  derivedPullbackObjIso (toZariskiSmallModelHom B S hS) E ≪≫
    ((@Stacks.DerivedQCoh.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _
      (associatedModuleOfSheaf B S hS) (modelModulesEquiv B S hS).functor
      (toZariskiSmallModelHom B S hS).pullbackTopos
      (pullbackToposIsoAssociatedModel B S hS).symm _ _ _ _ _ _
      ⟨(RingedToposSiteHom.pullbackTopos_additive (toZariskiSmallModelHom B S hS)).map_add⟩
      (preservesFiniteLimits_pullbackTopos_toZariskiSmallModelHom B S hS)
      (preservesFiniteColimits_pullbackTopos_toZariskiSmallModelHom B S hS)).app E).symm

/-! ### The representable case -/

/-- **The representable case of Stacks 08IL.**  Let `S` be a quasi-separated scheme and `E` an
object of `D(S_étale, 𝒪)` with quasi-coherent cohomology sheaves.  If `Hⁱ(E ⊗^L_T 𝒢[0]) = 0` for
every `i ∉ [a, b]` and every quasi-coherent `𝒪`-module `𝒢` on the small étale site, then `E` has
Tor amplitude in `[a, b]`, for an arbitrary derived tensor product datum `T`.

By Stacks 071Q, `E = ε^*E₀` for `E₀` in `D_QCoh(𝒪_S)`.  Reindexed to the `Type u` model, `E`
becomes `Lε^*E₀`, and the tests at the quasi-coherent modules `ε^*𝓕₀` become the hypotheses of
`AlgebraicGeometry.SmallEtale.hasTorAmplitude_derivedPullback_of_quasicoherent_tests`; its
conclusion is reindexed back. -/
theorem hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent [QuasiSeparatedSpace S]
    (T : DerivedTensorProduct.{u + 1, u, u, u + 1}
      (_root_.AlgebraicGeometry.smallEtaleRingedSite B S hS))
    (E : RingedSite.DerivedModules.{u + 1, u, u, u + 1}
      (_root_.AlgebraicGeometry.smallEtaleRingedSite B S hS))
    (a b : ℤ)
    (hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (RingedSite.Modules (_root_.AlgebraicGeometry.smallEtaleRingedSite B S hS)) n).obj
        E).IsQuasicoherentOnSite)
    (h : ∀ G : RingedSite.Modules (_root_.AlgebraicGeometry.smallEtaleRingedSite B S hS),
      G.IsQuasicoherentOnSite → ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor
            (RingedSite.Modules (_root_.AlgebraicGeometry.smallEtaleRingedSite B S hS)) i).obj
          ((T.tensor.obj E).obj ((DerivedCategory.singleFunctor
            (RingedSite.Modules (_root_.AlgebraicGeometry.smallEtaleRingedSite B S hS)) 0).obj
              G)))) :
    HasTorAmplitude T E a b := by
  let X := _root_.AlgebraicGeometry.smallEtaleRingedSite B S hS
  let X' := (smallModelRingedTopos B S hS).toRingedSite
  let e : RingedSite.Modules X ≌ RingedSite.Modules X' := modelModulesReindex B S hS
  have : e.functor.Additive := e.functor.additive_of_preserves_binary_products
  let ε : ∀ a b : RingedSite.Modules X,
      e.functor.obj (((Tensor.sheafTensor X.O).obj a).obj b) ≅
        ((Tensor.sheafTensor X'.O).obj (e.functor.obj a)).obj (e.functor.obj b) := fun a b =>
    TensorPower.whiskerTensorSheafIso (J' := smallModelTopology B S hS)
      (commRingStructureSheaf B S hS).obj
      (Tensor.ringSheaf (commRingStructureSheaf B S hS)).property
      (smallModelEquiv B S hS).symm.functor a b
  have hε₁ : ∀ {a a' : RingedSite.Modules X} (f : a ⟶ a') (b : RingedSite.Modules X),
      e.functor.map (((Tensor.sheafTensor X.O).map f).app b) ≫ (ε a' b).hom =
        (ε a b).hom ≫ ((Tensor.sheafTensor X'.O).map (e.functor.map f)).app (e.functor.obj b) :=
    fun f b => SiteEquivalenceDerivedTensor.reindexTensorIso_naturality_left
      (smallModelTopology B S hS) (smallModelEquiv B S hS).symm (commRingStructureSheaf B S hS)
      f b
  have hε₂ : ∀ (a : RingedSite.Modules X) {b b' : RingedSite.Modules X} (g : b ⟶ b'),
      e.functor.map (((Tensor.sheafTensor X.O).obj a).map g) ≫ (ε a b').hom =
        (ε a b).hom ≫ ((Tensor.sheafTensor X'.O).obj (e.functor.obj a)).map (e.functor.map g) :=
    fun a _ _ g => SiteEquivalenceDerivedTensor.reindexTensorIso_naturality_right
      (smallModelTopology B S hS) (smallModelEquiv B S hS).symm (commRingStructureSheaf B S hS)
      a g
  let T' := canonicalDerivedTensorProduct X'
  -- A K-flat representative of `E`.
  obtain ⟨K, pr, hK, hqi⟩ := Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize
    (commRingStructureSheaf B S hS) (DerivedCategory.Q.objPreimage E)
  have _ := hqi
  let eK : DerivedCategory.Q.obj K ≅ E :=
    asIso (DerivedCategory.Q.map pr) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  -- Stacks 071Q: `E ≅ ε^*E₀`.
  let Eq : (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).FullSubcategory := ⟨E, hqc⟩
  let E₀ := (derivedRestrictModuleQcoh B S hS).obj Eq
  let e₀ : (associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E₀.obj ≅ E :=
    (DerivedCategoryB.derivedCategoryB (qcohOnSite B S hS)).ι.mapIso
      (asIso ((derivedAssociatedModuleQcohAdjunction B S hS).counit.app Eq))
  -- On the model, `E` is `Lε^*E₀`.
  let eD : (derivedPullback (toZariskiSmallModelHom B S hS)).obj E₀.obj ≅
      e.functor.mapDerivedCategory.obj E :=
    derivedPullbackModelIso B S hS E₀.obj ≪≫ e.functor.mapDerivedCategory.mapIso e₀
  refine (hasTorAmplitude_iff_of_equivalence e ε hε₁ hε₂ T T' K hK E eK a b).2
    (HasTorAmplitude.of_iso eD ?_)
  refine hasTorAmplitude_derivedPullback_of_quasicoherent_tests B S hS T' E₀.obj a b
    (fun n => E₀.property n) fun F hF i hi => ?_
  exact ((isZero_homology_tensor_single_iff_of_equivalence e ε hε₁ hε₂ T T' K hK E eK
    ((associatedModuleOfSheaf B S hS).obj F) i).1
      (h _ (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS F hF) i hi)).of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso ((T'.tensor.mapIso eD).app _ ≪≫
      (T'.tensor.obj _).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
        ((pullbackToposIsoAssociatedModel B S hS).app F))))

end AlgebraicGeometry.SmallEtale

end
