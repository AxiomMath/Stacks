module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingSliceUnit
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.SliceBasicOpenDualAmplitude
public import StacksFrontier.AlgebraicGeometry.InternalHomEvaluation.CoherentEvaluation
public import StacksFrontier.AlgebraicGeometry.InternalHomEvaluation.SliceCoherentTransport
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SmoothBandSplitting
public import
  StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedSheafHomothetyRestrictionMonoidal
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPseudoCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison

/-!
# Evaluation against a dualizing complex is an isomorphism on `D_Coh`

Let `X` be a locally Noetherian scheme, `K` a dualizing complex on `X` ([Stacks, Tag 0A87]) and
`L` an object of `D_Coh(𝒪_X)`. This file proves that the evaluation morphism of
[Stacks, Tag 0A8U]

`R𝓗om_{𝒪_X}(K, K) ⊗^L_{𝒪_X} L ⟶ R𝓗om_{𝒪_X}(R𝓗om_{𝒪_X}(L, K), K)`

is an isomorphism, `Stacks.Duality.isIso_derivedSheafHomEvaluation_of_isDualizingComplex`. With
the homothety `𝒪_X[0] ⟶ R𝓗om_{𝒪_X}(K, K)` of a dualizing complex being invertible
(`Stacks.Duality.isIso_derivedSheafHomothety_of_isDualizingComplex`), this is the invertibility of
the canonical biduality morphism of [Stacks, Tag 0A89].

## Main results

* `Stacks.Duality.isLE_derivedSheafHomSelf_restrict` and
  `Stacks.Duality.isGE_derivedTensor_derivedSheafHomSelf_restrict`: over an affine open `W`,
  `R𝓗om_{𝒪_X|_W}(K|_W, K|_W)` has no cohomology in positive degrees, and tensoring with it keeps a
  bound below.
* `Stacks.Duality.exists_basicOpen_hasSiteApproximation`: a strictly perfect approximation of a
  bounded-above object of `D_Coh(𝒪_X)` on a basic open of a given affine open containing a given
  point.
* `Stacks.Duality.exists_isIso_homologyMap_derivedSheafHomEvaluation_restrict`: the evaluation
  morphism is invertible on `Hⁿ` over a neighbourhood of every point.
* `Stacks.Duality.isIso_derivedSheafHomEvaluation_of_isDualizingComplex`: **the evaluation
  morphism against a dualizing complex is an isomorphism at a source with coherent cohomology.**

## References

* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 0A69](https://stacks.math.columbia.edu/tag/0A69)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A88](https://stacks.math.columbia.edu/tag/0A88)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0A8U](https://stacks.math.columbia.edu/tag/0A8U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated TopologicalSpace Opposite AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

variable {X : Scheme.{u}}

/-! ### The derived internal hom of `K|_W` with itself -/

/-- **`R𝓗om_{𝒪_X|_W}(K|_W, K|_W)` has no cohomology in positive degrees**, for `W ⊆ X` affine
and `K` a dualizing complex on a locally Noetherian scheme `X`. -/
theorem isLE_derivedSheafHomSelf_restrict [IsLocallyNoetherian X] (W : X.Opens)
    (hW : IsAffineOpen W) {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (d : ℤ) (hd : 0 ≤ d) :
    ((((Stacks.SheafOfModules.ringedSite X.sheaf).over W).derivedSheafHomBifunctor.obj
      (op ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K))).obj
        ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K)).IsLE d := by
  let := RingedSite.derivedTensorMonoidal ((Stacks.SheafOfModules.ringedSite X.sheaf).over W)
  have hu : (𝟙_ (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      ((Stacks.SheafOfModules.ringedSite X.sheaf).over W).O)))).IsLE 0 :=
    inferInstanceAs ((DerivedCategory.Q.obj (RingedSite.structureSheafComplex
      ((Stacks.SheafOfModules.ringedSite X.sheaf).over W))).IsLE 0)
  have h0 : ((((Stacks.SheafOfModules.ringedSite X.sheaf).over W).derivedSheafHomBifunctor.obj
        (op ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K))).obj
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K)).IsLE 0 :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (restrictDDerivedSheafHomSelfUnitIso W hW K hK).symm 0
  exact DerivedCategory.TStructure.t.isLE_of_le _ 0 d hd

/-- **Tensoring with `R𝓗om_{𝒪_X|_W}(K|_W, K|_W)` keeps a bound below**, for `W ⊆ X` affine and
`K` a dualizing complex on a locally Noetherian scheme `X`. -/
theorem isGE_derivedTensor_derivedSheafHomSelf_restrict [IsLocallyNoetherian X] (W : X.Opens)
    (hW : IsAffineOpen W) {K : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (Z : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over W).O))) (q : ℤ) (hZ : Z.IsGE q) :
    (((Stacks.SheafOfModules.derivedTensorProductFunctor
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over W)).obj
      ((((Stacks.SheafOfModules.ringedSite X.sheaf).over W).derivedSheafHomBifunctor.obj
        (op ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K))).obj
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K))).obj
            Z).IsGE q := by
  let := RingedSite.derivedTensorMonoidal ((Stacks.SheafOfModules.ringedSite X.sheaf).over W)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (((Stacks.SheafOfModules.derivedTensorProductFunctor
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over W)).mapIso
      (restrictDDerivedSheafHomSelfUnitIso W hW K hK)).app Z ≪≫ λ_ Z).symm q

/-! ### A strictly perfect approximation on a basic open -/

/-- **A bounded-above object of `D_Coh(𝒪_X)` has a strictly perfect approximation on a basic open
of any affine open through a given point.** Let `X` be locally Noetherian, `E` an object of
`D(𝒪_X)` with no cohomology above `b` and all cohomology sheaves coherent, `m` an integer,
`V ⊆ X` an affine open and `x ∈ V`. Then `E` is represented by a complex `NN` admitting, over a
basic open `D(g)` of `V` containing `x`, a strictly perfect complex mapping to `NN|_{D(g)}`
invertibly on cohomology above `m` and epimorphically in degree `m`. -/
theorem exists_basicOpen_hasSiteApproximation [IsLocallyNoetherian X]
    (E : DerivedCategory X.Modules) (b : ℤ) (hE : E.IsLE b)
    (hEcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsCoherent)
    (m : ℤ) (V : X.affineOpens) (x : X) (hxV : x ∈ V.1) :
    ∃ (NN : CochainComplex (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) ℤ) (g : Γ(X, V.1)),
      x ∈ X.basicOpen g ∧ Nonempty (DerivedCategory.Q.obj NN ≅ E) ∧
      AlgebraicGeometry.RingedSpace.PseudoCoherence.HasSiteApproximation X.toRingedSpace NN m
        (X.basicOpen g) := by
  have hpc : AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m :=
    AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_isLE_homology E m b hE
      (fun i _ => AlgebraicGeometry.isPseudoCoherentFrom_singleFunctor_zero_of_isCoherent X _
        (hEcoh i).stacksIsCoherent (m - i))
  obtain ⟨NN, hNN, eNN⟩ := hpc
  obtain ⟨Ux, hxUx, P, hP, α, hiso, hepi⟩ := hNN x
  obtain ⟨g, hgle, hxg⟩ := V.2.exists_basicOpen_le (V := V.1 ⊓ Ux) ⟨x, ⟨hxV, hxUx⟩⟩ hxV
  exact ⟨NN, g, hxg, eNN,
    AlgebraicGeometry.RingedSpace.PseudoCoherence.hasSiteApproximation_mono X.toRingedSpace NN m
      (le_trans hgle inf_le_right)
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.hasSiteApproximation_of_space
        X.toRingedSpace Ux NN m hP α hiso hepi)⟩

/-! ### Invertibility on `Hⁿ` near a point -/

/-- **The evaluation morphism against a dualizing complex is invertible on `Hⁿ` over a
neighbourhood of every point.** Let `X` be a locally Noetherian scheme, `K` a dualizing complex
on `X`, `L` an object of `D(𝒪_X)` with coherent cohomology sheaves, `n` an integer and `x` a
point of `X`. Then `x` has an open neighbourhood `W` over whose slice site `Opens(X)/W` the
evaluation morphism at the restrictions of `L`, `K`, `K` is invertible on `Hⁿ`. -/
theorem exists_isIso_homologyMap_derivedSheafHomEvaluation_restrict [IsLocallyNoetherian X]
    {K L : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (hLcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent)
    (n : ℤ) (x : X) :
    ∃ W : X.Opens, x ∈ W ∧
      IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              ((Stacks.SheafOfModules.ringedSite X.sheaf).over W).O)) n).map
        (RingedSite.derivedSheafHomEvaluation ((Stacks.SheafOfModules.ringedSite X.sheaf).over W)
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct
            ((Stacks.SheafOfModules.ringedSite X.sheaf).over W))
          (RingedSite.derivedInternalHomOfBifunctor
            ((Stacks.SheafOfModules.ringedSite X.sheaf).over W))
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj L)
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K)
          ((SheafOfModules.overFunctor.{u} X.ringCatSheaf W).mapDerivedCategory.obj K))) := by
  have hxtop : x ∈ (⊤ : X.Opens) := trivial
  rw [← AlgebraicGeometry.iSup_affineOpens_eq_top X] at hxtop
  obtain ⟨V, hxV⟩ := Opens.mem_iSup.1 hxtop
  obtain ⟨b', hb'⟩ := exists_forall_basicOpen_isLE_derivedSheafHomSlice V hK
  obtain ⟨a', ha'⟩ := exists_forall_basicOpen_isGE_derivedSheafHomSlice V hK
  obtain ⟨NN, g, hxg, ⟨eNN⟩, happ⟩ :=
    exists_basicOpen_hasSiteApproximation
      ((DerivedCategory.TStructure.t.truncLE (n + max 0 (b' - a'))).obj L)
      (n + max 0 (b' - a')) inferInstance
      (fun i => AlgebraicGeometry.isCoherent_homology_obj_truncLE L hLcoh _ i)
      (n - max 0 (b' - a') - 1) V x hxV
  refine ⟨X.basicOpen g, hxg, ?_⟩
  obtain ⟨P, hP, α₀, hαiso, hαepi⟩ := happ
  have hT := ((SheafOfModules.overFunctor.{u} X.ringCatSheaf
      (X.basicOpen g)).mapDerivedCategory).map_distinguished _
    (DerivedCategory.TStructure.t.triangleLEGE_distinguished (n + max 0 (b' - a'))
      (n + max 0 (b' - a') + 1) rfl L)
  have hc0 : (0 : ℤ) ≤ max 0 (b' - a') := le_max_left _ _
  have hc1 : b' - a' ≤ max 0 (b' - a') := le_max_right _ _
  have hZGE : ((SheafOfModules.overFunctor.{u} X.ringCatSheaf
      (X.basicOpen g)).mapDerivedCategory.obj
        ((DerivedCategory.TStructure.t.truncGE
          (n + max 0 (b' - a') + 1)).obj L)).IsGE (n + max 0 (b' - a') + 1) :=
    CategoryTheory.Functor.isGE_obj_mapDerivedCategory _ _ _
      (DerivedCategory.TStructure.t.isGE_truncGE_obj L _ _ le_rfl)
  have hZcoh := isCoherent_homology_sliceSpecFunctor_restrict (X.basicOpen g) (V.2.basicOpen g)
    ((DerivedCategory.TStructure.t.truncGE (n + max 0 (b' - a') + 1)).obj L)
    (fun i => AlgebraicGeometry.isCoherent_homology_obj_truncGE L hLcoh _ i)
  refine RingedSite.isIso_homologyMap_derivedSheafHomEvaluation_of_triangle
    ((Stacks.SheafOfModules.ringedSite X.sheaf).over (X.basicOpen g)) _ _ _ _ _ _ _ hT n
    ?hK' ?h1 ?h2
  case h1 =>
    exact Or.inr ⟨n + max 0 (b' - a') + 1,
      isGE_derivedTensor_derivedSheafHomSelf_restrict (X.basicOpen g) (V.2.basicOpen g) hK
        _ _ hZGE, by omega⟩
  case h2 =>
    exact Or.inr ⟨a' - (b' - (n + max 0 (b' - a') + 1)), ha' g _ _
      (isCoherent_homology_sliceSpecFunctor_derivedSheafHom (X.basicOpen g) (V.2.basicOpen g)
        hK _ hZcoh)
      (hb' g _ _ hZcoh hZGE), by omega⟩
  case hK' =>
    have hepi : Epi ((DerivedCategory.homologyFunctor _
        (n - max 0 (b' - a') - 1)).map (DerivedCategory.Q.map α₀)) :=
      (DerivedCategory.epi_homologyFunctor_map_Q_map_iff α₀ _).2 hαepi
    have hαiso' : ∀ j : ℤ, n - max 0 (b' - a') - 1 < j →
        IsIso ((DerivedCategory.homologyFunctor _ j).map (DerivedCategory.Q.map α₀)) :=
      fun j hj => (DerivedCategory.isIso_homologyFunctor_map_Q_map_iff α₀ j).2 (hαiso j hj)
    have hcohP := isCoherent_homology_sliceSpecFunctor_Q_of_isStrictlyPerfect
      (X.basicOpen g) (V.2.basicOpen g) hP
    have hcohN : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
        (Spec Γ(X, X.basicOpen g)).Modules i).obj
          ((sliceSpecFunctor (X.basicOpen g) (V.2.basicOpen g)).obj
            (DerivedCategory.Q.obj
              ((Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex NN
                (X.basicOpen g))))).IsCoherent := fun i =>
      AlgebraicGeometry.isCoherent_of_modulesIso
        ((DerivedCategory.homologyFunctor (Spec Γ(X, X.basicOpen g)).Modules i).mapIso
          ((sliceSpecFunctor (X.basicOpen g) (V.2.basicOpen g)).mapIso
            (RingedSite.restrictModelIso (Stacks.SheafOfModules.ringedSite X.sheaf)
              (X.basicOpen g) eNN))).symm
        (isCoherent_homology_sliceSpecFunctor_restrict (X.basicOpen g) (V.2.basicOpen g)
          ((DerivedCategory.TStructure.t.truncLE (n + max 0 (b' - a'))).obj L)
          (fun j => AlgebraicGeometry.isCoherent_homology_obj_truncLE L hLcoh _ j) i)
    have h₀ := RingedSite.isIso_homologyMap_derivedSheafHomEvaluation_of_approximation_of_isLE
      ((Stacks.SheafOfModules.ringedSite X.sheaf).over (X.basicOpen g)) _ _ _ hP
      (DerivedCategory.Q.map α₀) (n - max 0 (b' - a') - 1) hαiso' hepi
      0 (max 0 (b' - a'))
      (isLE_derivedSheafHomSelf_restrict (X.basicOpen g) (V.2.basicOpen g) hK _ (by omega))
      (fun Z gz hz hTz => ?_) n (by omega)
    · exact (RingedSite.isIso_homologyMap_derivedSheafHomEvaluation_iff_of_iso
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over (X.basicOpen g)) _ _
        (RingedSite.restrictModelIso (Stacks.SheafOfModules.ringedSite X.sheaf)
          (X.basicOpen g) eNN) (Iso.refl _) (Iso.refl _) n).1 h₀
    · have hZLE : Z.IsLE (n - max 0 (b' - a') - 1 - 1) :=
        DerivedCategory.triangle_obj₃_isLE_of_approximation _ hTz _ hαiso' hepi
      have hcohZ := isCoherent_homology_sliceSpecFunctor_obj₃_of_distinguished
        (X.basicOpen g) (V.2.basicOpen g)
        (Triangle.mk (DerivedCategory.Q.map α₀) gz hz) hTz hcohP hcohN
      have hGE := ha' g Z (n - max 0 (b' - a') - 1 - 1) hcohZ hZLE
      have hLE := hb' g _ (a' - (n - max 0 (b' - a') - 1 - 1))
        (isCoherent_homology_sliceSpecFunctor_derivedSheafHom (X.basicOpen g)
          (V.2.basicOpen g) hK Z hcohZ) hGE
      rw [DerivedCategory.isLE_iff]
      intro i hi
      exact DerivedCategory.isZero_of_isLE _
        (b' - (a' - (n - max 0 (b' - a') - 1 - 1))) i (by omega)

/-! ### The evaluation isomorphism -/

/-- For `K` a dualizing complex on a locally Noetherian scheme `X` and `L` an object of
`D(𝒪_X)` with coherent cohomology sheaves, every point of `X` has an open neighbourhood `W` with
`RingedSite.IsIsoHomologyMapEvaluationOver` in degree `n`: the evaluation morphism over the slice
site `Opens(X)/W` is invertible on `Hⁿ`. -/
theorem exists_isIsoHomologyMapEvaluationOver_of_isDualizingComplex [IsLocallyNoetherian X]
    {K L : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (hLcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent)
    (n : ℤ) (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ RingedSite.IsIsoHomologyMapEvaluationOver
      (Stacks.SheafOfModules.ringedSite X.sheaf) L K K n W :=
  exists_isIso_homologyMap_derivedSheafHomEvaluation_restrict hK hLcoh n x

/-- **The evaluation morphism against a dualizing complex is an isomorphism on `D_Coh(𝒪_X)`.**
Let `X` be a locally Noetherian scheme, `K` a dualizing complex on `X` ([Stacks, Tag 0A87]) and
`L` an object of `D(𝒪_X)` all of whose cohomology sheaves are coherent. Then the evaluation
morphism of [Stacks, Tag 0A8U]

`R𝓗om_{𝒪_X}(K, K) ⊗^L_{𝒪_X} L ⟶ R𝓗om_{𝒪_X}(R𝓗om_{𝒪_X}(L, K), K)`

is an isomorphism. -/
theorem isIso_derivedSheafHomEvaluation_of_isDualizingComplex [IsLocallyNoetherian X]
    {K L : DerivedCategory X.Modules} (hK : IsDualizingComplex K)
    (hLcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsCoherent) :
    IsIso (Stacks.SheafOfModules.derivedSheafHomEvaluation X.sheaf L K K) := by
  refine RingedSite.isIso_derivedSheafHomEvaluation_of_coversTop_isIsoHomologyMapEvaluationOver
    (Stacks.SheafOfModules.ringedSite X.sheaf) _ _ L K K fun n => ?_
  refine ⟨{ W : X.Opens // RingedSite.IsIsoHomologyMapEvaluationOver
      (Stacks.SheafOfModules.ringedSite X.sheaf) L K K n W }, fun p => p.1, ?_, fun p => p.2⟩
  rw [Opens.coversTop_iff]
  refine TopologicalSpace.IsOpenCover.mk (le_antisymm le_top fun x _ => ?_)
  obtain ⟨W, hxW, hW⟩ := exists_isIsoHomologyMapEvaluationOver_of_isDualizingComplex hK hLcoh n x
  exact Opens.mem_iSup.2 ⟨⟨W, hW⟩, hxW⟩

end Stacks.Duality

end
