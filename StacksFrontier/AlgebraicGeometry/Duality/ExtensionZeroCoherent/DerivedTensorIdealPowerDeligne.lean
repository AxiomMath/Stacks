module

public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.CoherentComplexRepresentative
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemOpenRestriction
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemSourcePresentation
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.TruncationDevissage
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DerivedTensorIdealPowerAffine
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DerivedTensorIdealPowerResolution
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DerivedTensorIdealPowerRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ProIsoComplexesCover
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ProSeqIsoOfProInverse

/-!
# `(K ⊗^L 𝓘^n)` is pro-isomorphic to a Deligne system

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and `𝓘 ⊆ 𝒪_X` a quasi-coherent sheaf of
ideals with `V(𝓘) = X ∖ U`. For `K` in `D^b_{Coh}(𝒪_X)`, [Stacks, Tag 0G4U] says that the inverse
system `(K ⊗^L_{𝒪_X} 𝓘^n)_n` is pro-isomorphic to a Deligne system with constant value `K|_U`
over `U`.

The terms `K ⊗^L 𝓘^n` need not lie in `D^b_{Coh}(𝒪_X)` (they are bounded above, but not bounded
below in general), so the pro-isomorphism is one of pro-objects of `D(𝒪_X)`, with the Deligne
system read in `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.proInverse_derivedTensorIdealPowerNatTrans`: the canonical maps
  `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` are a pro-isomorphism, for a bounded complex of coherent modules on a
  Noetherian scheme.
* `AlgebraicGeometry.exists_deligneSystem_proIso_derivedTensorIdealPowerSystem`:
  **[Stacks, Tag 0G4U]**.

## Implementation notes

The Stacks Project argues: by Stacks 0G4T the question is local on `X`, and on an affine scheme
it is the algebra statement Stacks 0G3N. Stacks 0G4T is a statement about systems in
`D^b_{Coh}`, so it does not apply verbatim to `(K ⊗^L 𝓘^n)`; the locality used here is instead
that of a pro-isomorphism of inverse systems of complexes
(`AlgebraicGeometry.proInverse_whiskerRight_Q_of_cover`, through the mapping-cone triangles,
Stacks 0G3C and a ghost-lemma argument on Mayer–Vietoris triangles). Concretely: write
`K ≅ 𝓕^•` for a bounded complex of coherent modules (Stacks 0FDB) and take the Deligne system
`(𝓘^n 𝓕^•)`. The canonical maps
`𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` (`AlgebraicGeometry.derivedTensorIdealPowerNatTrans`) are computed on a
K-flat resolution `𝓟^• ⟶ 𝓕^•` (Stacks 06YS) by maps of complexes
(`AlgebraicGeometry.derivedTensorResolutionIso_hom_comp`), which are compatible with restriction
along open immersions (`AlgebraicGeometry.idealPowerResolutionNatTrans_restrict`). On a member
`Spec R ⟶ X` of the affine open cover they are a pro-isomorphism by the affine case
(`AlgebraicGeometry.proInverse_derivedTensorIdealPowerNatTrans_spec`), which is Stacks 0G3N
transported along `M ↦ M̃`. Hence they are a pro-isomorphism on `X`.

## References

* [Stacks Project, Tag 0G4U](https://stacks.math.columbia.edu/tag/0G4U)
* [Stacks Project, Tag 0G4T](https://stacks.math.columbia.edu/tag/0G4T)
* [Stacks Project, Tag 0G3N](https://stacks.math.columbia.edu/tag/0G3N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.IdealPower

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

universe u

namespace AlgebraicGeometry

variable {U X : Scheme.{u}}

/-- **The canonical maps `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` are a pro-isomorphism** in `D(𝒪_X)`, for a
bounded complex `𝓕^•` of coherent modules on a Noetherian scheme and any quasi-coherent ideal
sheaf `𝓘`: every stage admits an inverse after passing to a later stage. -/
public theorem proInverse_derivedTensorIdealPowerNatTrans [IsNoetherian X] (I : X.IdealSheafData)
    (F : CochainComplex X.Modules ℤ) (hcoh : ∀ i, (F.X i).IsCoherent)
    (hge : ∃ a, F.IsStrictlyGE a) (hle : ∃ b, F.IsStrictlyLE b) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : (Functor.ofOpSequence (idealPowerComplexSystem I F).transition ⋙
          DerivedCategory.Q).obj (op m) ⟶
        (derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F)).obj (op n)),
      (derivedTensorIdealPowerNatTrans I F).app (op m) ≫ s =
          (derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F)).map (homOfLE h).op ∧
        s ≫ (derivedTensorIdealPowerNatTrans I F).app (op n) =
          (Functor.ofOpSequence (idealPowerComplexSystem I F).transition ⋙
            DerivedCategory.Q).map (homOfLE h).op := by
  obtain ⟨P, π, hP, hπ⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso X.sheaf
    (show Stacks.Duality.TensorComplex X from F)
  have : QuasiIso π := hπ
  refine ProSeq.proInverse_of_natIso (derivedTensorIdealPowerNatTrans I F)
    (Functor.whiskerRight (idealPowerResolutionNatTrans I π) DerivedCategory.Q)
    (derivedTensorResolutionIso I hP π) (Iso.refl _) ?_ ?_
  · exact (Category.comp_id _).trans (derivedTensorResolutionIso_hom_comp I hP π)
  have : CompactSpace X := inferInstance
  refine proInverse_whiskerRight_Q_of_cover (idealPowerResolutionNatTrans I π) fun x => ?_
  let 𝒰 := X.affineOpenCover
  let R := 𝒰.X (𝒰.idx x)
  let g : Spec R ⟶ X := 𝒰.f (𝒰.idx x)
  refine ⟨Spec R, g, inferInstance, 𝒰.covers x, ?_⟩
  have : IsLocallyNoetherian (Spec R) := isLocallyNoetherian_of_isOpenImmersion g
  have : IsNoetherianRing R := isLocallyNoetherian_Spec.mp inferInstance
  have hFq : ∀ i, (F.X i).IsQuasicoherent := fun i =>
    have := hcoh i; isQuasicoherent_of_isCoherent _
  let F' := restrictComplex g F
  have hcoh' : ∀ i, (F'.X i).IsCoherent := fun i =>
    have := hcoh i; Stacks.Algebraization.isCoherent_restrict_of_isOpenImmersion g (F.X i)
  have hge' : ∃ a, F'.IsStrictlyGE a := by
    obtain ⟨a, ha⟩ := hge
    exact ⟨a, (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi =>
      (Scheme.Modules.restrictFunctor g).map_isZero (F.isZero_of_isStrictlyGE a i hi)⟩
  have hle' : ∃ b, F'.IsStrictlyLE b := by
    obtain ⟨b, hb⟩ := hle
    exact ⟨b, (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi =>
      (Scheme.Modules.restrictFunctor g).map_isZero (F.isZero_of_isStrictlyLE b i hi)⟩
  let π' := restrictResolution g π
  have := AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor g
  have : (Scheme.Modules.restrictFunctor g).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have hπX : QuasiIso (show (show CochainComplex X.Modules ℤ from P) ⟶ F from π) := hπ
  have : QuasiIso π' :=
    HomologicalComplex.quasiIso_map_of_preservesHomology (F := Scheme.Modules.restrictFunctor g)
      (φ := show (show CochainComplex X.Modules ℤ from P) ⟶ F from π) (hφ := hπX)
  have hP' := kFlatComplex_restrict g hP
  have Hspec := proInverse_derivedTensorIdealPowerNatTrans_spec R (I.comap g) F' hcoh' hge' hle'
  have H1 := ProSeq.proInverse_of_natIso
    (Functor.whiskerRight (idealPowerResolutionNatTrans (I.comap g) π')
      DerivedCategory.Q) (derivedTensorIdealPowerNatTrans (I.comap g) F')
    (derivedTensorResolutionIso (I.comap g) hP' π').symm (Iso.refl _)
    (by
      rw [derivedTensorResolutionIso_hom_comp (I.comap g) hP' π']
      exact (Category.comp_id _).trans (Iso.inv_hom_id_assoc _ _).symm) Hspec
  refine ProSeq.proInverse_of_natIso _ _ (Functor.isoWhiskerRight
      (restrictIdealPowerResolutionSystemIso g I P) DerivedCategory.Q)
    (Functor.isoWhiskerRight (restrictIdealPowerTensorComplexSystemIso g I F hFq)
      DerivedCategory.Q) ?_ H1
  have h := congrArg (fun t => Functor.whiskerRight t DerivedCategory.Q)
    (idealPowerResolutionNatTrans_restrict g I hFq π)
  refine NatTrans.ext (funext fun n => ?_)
  have hn := congrArg (fun t => NatTrans.app t n) h
  simp only [Functor.whiskerRight_comp, NatTrans.comp_app] at hn
  exact hn

/-- **Stacks Project, Tag 0G4U.** Let `j : U ⟶ X` be an open immersion of Noetherian schemes, let
`𝓘 ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals with `V(𝓘) = X ∖ U`, and let `K` be in
`D^b_{Coh}(𝒪_X)`. Then the inverse system `(K ⊗^L_{𝒪_X} 𝓘^n)_n` is pro-isomorphic to a Deligne
system whose restriction to `U` is constant with value `K|_U`.

The derived tensor product is that of [Stacks, Tag 06YU]
(`AlgebraicGeometry.derivedTensorIdealPowerSystem`), and the pro-isomorphism is one of pro-objects
of `D(𝒪_X)`: the terms `K ⊗^L 𝓘^n` are not in `D^b_{Coh}(𝒪_X)` in general. The Deligne system
produced is `(𝓘^n 𝓕^•)` for a bounded complex `𝓕^•` of coherent modules representing `K`, with the
given ideal sheaf `𝓘`. -/
@[stacks 0G4U]
public theorem exists_deligneSystem_proIso_derivedTensorIdealPowerSystem (j : U ⟶ X)
    [IsOpenImmersion j] [IsNoetherian X] (I : X.IdealSheafData)
    (hI : (I.support : Set X) = (Set.range j.base)ᶜ) (K : BoundedCoherentDerived X) :
    ∃ D : DeligneSystem j,
      Nonempty (D.system ⋙ restrictBoundedCoherent j ≅
        (Functor.const ℕᵒᵖ).obj ((restrictBoundedCoherent j).obj K)) ∧
      Nonempty (ProSeq.of (derivedTensorIdealPowerSystem I K.obj) ≅
        ProSeq.of (D.system ⋙ (boundedCoherentDerived X).ι)) := by
  obtain ⟨F, a, b, hcoh, hGE, hLE, ⟨eF⟩⟩ := exists_isCoherent_complex_iso_Q_obj X K
  let D := DeligneTriangle.deligneSystemOfComplex j I hI F ⟨a, hGE⟩ ⟨b, hLE⟩ hcoh
  refine ⟨D, ⟨D.restrictIsoConst ≪≫ (Functor.const ℕᵒᵖ).mapIso
    ((Scheme.Modules.restrictFunctor j).mapDerivedCategory.mapIso eF)⟩, ⟨?_⟩⟩
  let T := Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace
  let Y : ℕ → DerivedCategory X.Modules := fun k =>
    (DerivedCategory.singleFunctor X.Modules 0).obj (idealPowerSheaf I k)
  let t : ∀ n, Y (n + 1) ⟶ Y n := fun n =>
    (DerivedCategory.singleFunctor X.Modules 0).map (idealPowerSheafTransition I n)
  let eSys : derivedTensorIdealPowerSystem I K.obj ≅
      derivedTensorIdealPowerSystem I (DerivedCategory.Q.obj F) :=
    (Stacks.Duality.ofOpSequenceCompIso t (T.tensor.obj K.obj)).symm ≪≫
      Functor.isoWhiskerLeft (Functor.ofOpSequence t) (T.tensor.mapIso eF.symm) ≪≫
      Stacks.Duality.ofOpSequenceCompIso t (T.tensor.obj (DerivedCategory.Q.obj F))
  exact ProSeq.ofIsoOfNatIso eSys ≪≫
    ProSeq.isoOfProInverse (derivedTensorIdealPowerNatTrans I F)
      (proInverse_derivedTensorIdealPowerNatTrans I F hcoh ⟨a, hGE⟩ ⟨b, hLE⟩)

end AlgebraicGeometry

end
