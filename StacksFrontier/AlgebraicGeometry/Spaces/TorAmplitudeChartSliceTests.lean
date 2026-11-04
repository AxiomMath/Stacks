module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalSplitEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.TorAmplitudeQuasiCoherentTests
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.IntervalDescentSliceTests
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.DirectSummands

/-!
# Condition (2) of Stacks 08IL restricts to the slice at an affine chart

Let `X` be a quasi-separated algebraic space and `E` an object of `D(𝒪_X)` satisfying condition
(2) of Stacks 08IL: `Hⁱ(E ⊗^L_{𝒪_X} ℳ[0]) = 0` for `i ∉ [a, b]` and every quasi-coherent
`𝒪_X`-module `ℳ`.  For an étale chart `W` of `X` whose scheme is affine, the restriction `E|_W` to
the slice `X_étale/W` satisfies the same condition on that slice: `Hⁱ(E|_W ⊗^L 𝒢[0]) = 0` for
every quasi-coherent module `𝒢` on the slice, against an arbitrary derived tensor product datum
on the slice.

This is the first paragraph of the source's proof of the converse of Stacks 08IL.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_sliceTensor_of_hasTorAmplitudeOnQuasicoherent`: the
  restriction of condition (2) to the slice at an affine chart.

## Implementation notes

Let `j : W → X` be the chart.  As `X` is quasi-separated and `W` affine, `j` is quasi-compact
(Stacks 073B, `AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace`) and separated
(Stacks 03FZ, `AlgebraicGeometry.Space.isSeparated_of_isEtale_of_scheme_isSeparated`), hence
quasi-separated.  A quasi-coherent module `𝒢` on the slice is, through the comparison of
Stacks 04M0 (`AlgebraicGeometry.Space.chartModuleSliceEquiv`), a quasi-coherent module `𝒢'` on
the chart; `ℳ = j_*𝒢'` is quasi-coherent by Stacks 03M9
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`), so condition (2)
kills `Hⁱ(E ⊗^L ℳ[0])`, and with it the slice test at `ℳ|_W`
(`isZero_homology_tensorModule_restriction_of_isZero_homology` in
`Stacks.SheafOfModules.DerivedTensorProduct`).
Restriction to the slice is `j^*` read through the comparison
(`AlgebraicGeometry.Space.chartModuleRestrictionSliceIso`), and `𝒢'` is a direct summand of
`j^*j_*𝒢'` because the counit splits along a separated étale morphism (Stacks 0HAP,
`AlgebraicGeometry.Space.counitSplitEpiOfSeparatedEtale`).  So `𝒢` is a retract of `ℳ|_W`, and
the functor `𝒢 ↦ Hⁱ(E|_W ⊗^L 𝒢[0])` kills it.

The retraction is built in the chart's module category and pulled back to the slice by the full
faithfulness of the comparison; the two spellings of the slice category (as the slice of
`AlgebraicGeometry.Space.SmallEtale` and as the slice of the ringed site's category) are
definitionally equal, so the identity `s ≫ r = 𝟙` is assembled with `congrArg₂` rather than by
rewriting, whose motive would not typecheck at reducible transparency.

## References

* [Stacks Project, Lemma 75.13.8 (Tag 08IL)](https://stacks.math.columbia.edu/tag/08IL)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 0HAP](https://stacks.math.columbia.edu/tag/0HAP)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules (DerivedTensorProduct)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS}
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O)
      (ComplexShape.up ℤ)]
  [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max (u + 1) u, u, u, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).O).Additive]
  [∀ (U : (smallEtaleRingedSite B S hS X.1 X.2).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max (u + 1) u, u, u, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).O).obj M).Additive]
  [∀ (U : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (K L : CochainComplex
      (RingedSite.Modules.{max (u + 1) u, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{max (u + 1) u, u, u, u, u}
        ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)
      (ComplexShape.up ℤ)]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

variable [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
  [hSliceDerived : ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
    HasDerivedCategory.{d}
      (RingedSite.Modules.{max (u + 1) u, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

/-- **Condition (2) of Stacks 08IL restricts to the slice at an affine chart.**  Let `X` be a
quasi-separated algebraic space, `E` an object of `D(𝒪_X)` with
`Hⁱ(E ⊗^L_T ℳ[0]) = 0` for `i ∉ [a, b]` and every quasi-coherent `𝒪_X`-module `ℳ`, and `W` an
étale chart of `X` with affine scheme.  Then `Hⁱ(E|_W ⊗^L_{T_W} 𝒢[0]) = 0` for `i ∉ [a, b]` and
every quasi-coherent module `𝒢` on the slice `X_étale/W`, for any derived tensor product datum
`T_W` on the slice.

`𝒢` is a retract of the restriction of the quasi-coherent module `j_*𝒢` (Stacks 03M9 and 0HAP,
for the chart `j : W → X`, quasi-compact and separated because `X` is quasi-separated and `W`
affine). -/
theorem isZero_homology_sliceTensor_of_hasTorAmplitudeOnQuasicoherent
    (hZ : B.Contains (⊤_ Scheme.{u})) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : DerivedTensorProduct.{u + 1, u, u, d} (smallEtaleRingedSite B S hS X.1 X.2))
    (E : RingedSite.DerivedModules.{u + 1, u, u, d} (smallEtaleRingedSite B S hS X.1 X.2))
    (a b : ℤ) (h : HasTorAmplitudeOnQuasicoherent B S hS X.2 T E a b)
    (W : (smallEtaleRingedSite B S hS X.1 X.2).C) (hW : IsAffine (chartScheme W))
    (TW : DerivedTensorProduct.{u + 1, u, u, d} ((smallEtaleRingedSite B S hS X.1 X.2).over W))
    (G : RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over W))
    (hG : G.IsQuasicoherentOnSite) (i : ℤ) (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((TW.tensor.obj ((RingedSite.derivedRestriction.{u + 1, u, u, d} _ W).obj E)).obj
        ((DerivedCategory.singleFunctor _ 0).obj G))) := by
  have := smallEtaleRingedSite_essentiallySmall B S hS X.1 X.2
  let j := chartToSpace B S hS X W
  have hjet : IsEtale B S hS j.hom := isEtale_chartToSpace B S hS X W
  have hjsep : IsSeparated B S hS j.hom :=
    isSeparated_of_isEtale_of_scheme_isSeparated B S hS X.1 X.2
      ((SmallEtale.toOver B S hS X.1).obj W) (by
        let : IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((SmallEtale.toOver B S hS X.1).obj W)) := hW
        infer_instance) j.hom hjet
  have hjqc : IsQuasiCompact B S hS j.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hqs
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ hW) j.hom
  let R := chartModuleSliceReindex B S hS X W
  let G' := R.obj G
  let M := (modulePushforward B S hS j).obj G'
  have hM : M.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS j hjqc
      (isQuasiSeparated_of_isSeparated B S hS hjsep) G'
      ((isQuasicoherentOnSite_chartModuleSliceReindex_obj_iff B S hS X W G).2 hG)
  have hMW := DerivedTensorProduct.isZero_homology_tensorModule_restriction_of_isZero_homology
    (smallEtaleRingedSite B S hS X.1 X.2) T W TW E M i (h M hM i hi)
  let e : R.obj ((SheafOfModules.overFunctor (structureRingSheaf B S hS X) W).obj M) ≅
      (modulePullback B S hS j).obj M :=
    ((chartModuleRestrictionSliceIso B S hS X W).app M).symm
  let hR : R.FullyFaithful := (chartModuleSliceEquiv B S hS X W).fullyFaithfulFunctor
  let σ := counitSplitEpiOfSeparatedEtale B S hS j hjet hjsep G'
  let r : (SheafOfModules.overFunctor (structureRingSheaf B S hS X) W).obj M ⟶ G :=
    hR.preimage (e.hom ≫ (modulePullbackAdjunction B S hS j).counit.app G')
  let s : G ⟶ (SheafOfModules.overFunctor (structureRingSheaf B S hS X) W).obj M :=
    hR.preimage (σ.section_ ≫ e.inv)
  have hsr : s ≫ r = 𝟙 G := hR.map_injective (by
    refine (R.map_comp s r).trans ?_
    refine Eq.trans ?_ (R.map_id G).symm
    refine (congrArg₂ (fun x y => x ≫ y) (hR.map_preimage (σ.section_ ≫ e.inv))
      (hR.map_preimage (e.hom ≫ (modulePullbackAdjunction B S hS j).counit.app G'))).trans ?_
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun x => σ.section_ ≫ x) (Iso.inv_hom_id_assoc e _)).trans σ.id))
  exact Stacks.Cohomology.TorAmplitude.isZero_obj_of_retract
    (DerivedCategory.singleFunctor _ 0 ⋙
      TW.tensor.obj ((RingedSite.derivedRestriction.{u + 1, u, u, d} _ W).obj E) ⋙
        DerivedCategory.homologyFunctor _ i) s r hsr hMW

end AlgebraicGeometry.Space

end
