module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties

/-!
# `D_ctf` is invariant under a universal homeomorphism which is a closed immersion

Let `i : Z ⟶ X` be a closed immersion of schemes of a big étale site which is a universal
homeomorphism — the inclusion of the reduction `X_red`, or of any closed subscheme with the same
underlying space. The inverse image `i⁻¹` on sheaves of `Λ`-modules on Mathlib's small étale sites
is an equivalence (topological invariance of the étale site, Stacks 04DZ), and an object `K` of
`D(X_étale, Λ)` lies in `D_ctf` exactly when `i⁻¹ K` does. This lets results proved for reduced
schemes, such as the generic local constancy of
`Stacks.EtaleCohomology.exists_isOpenImmersion_isFiniteProjectiveLocallyConstant`, be applied on an
arbitrary scheme.

## Main results

* `Stacks.EtaleCohomology.etaleModuleDirectImage_isEquivalence` and
  `Stacks.EtaleCohomology.etaleModuleInverseImage_isEquivalence`: direct and inverse image along a
  universal homeomorphism are equivalences of the categories of sheaves of `Λ`-modules.
* `Stacks.EtaleCohomology.isCtf_iff_inverseImage`: `K ∈ D_ctf(X_étale, Λ)` if and only if
  `i⁻¹ K ∈ D_ctf(Z_étale, Λ)`.

## Implementation notes

The direction `⟸` is checked after inverse image to a quasi-compact and quasi-separated `W ⟶ X`,
which is how `Stacks.EtaleCohomology.IsCtf` is defined. With `W' = W ×_X Z` and `j : W' ⟶ W` the
base change of `i`, again a closed immersion and a universal homeomorphism, the hypothesis
represents `j⁻¹ (K|_W)` by a bounded complex of constructible flat sheaves; its direct image along
`j`, taken degreewise, represents `K|_W`, because `j⁻¹` is an equivalence with quasi-inverse `j_*`,
and its terms are constructible flat by
`Stacks.EtaleCohomology.IsConstructibleFlatEtaleModule.directImage`, the open complement of `j`
being empty.

## References

* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring
  etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type r) [Ring Λ]

/-- **Direct image along a universal homeomorphism is an equivalence** of the categories of sheaves
of `Λ`-modules on Mathlib's small étale sites (topological invariance of the étale site,
Stacks 04DZ). -/
public instance etaleModuleDirectImage_isEquivalence {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] : (etaleModuleDirectImage.{u, r} Λ f).IsEquivalence := by
  have := isDenseSubsite_of_universalHomeomorphism f
  infer_instance

/-- **Inverse image along a universal homeomorphism is an equivalence** of the categories of
sheaves of `Λ`-modules on Mathlib's small étale sites. -/
public instance etaleModuleInverseImage_isEquivalence {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] : (etaleModuleInverseImage.{u, r} Λ f).IsEquivalence :=
  (etaleModuleInverseImageAdj.{u, r} Λ f).isEquivalence_left_of_isEquivalence_right

variable (B : BigEtaleSite.{u})

/-- The empty scheme belongs to every big étale site. -/
theorem bigEtaleSite_contains_empty : B.Contains (∅ : Scheme.{u}) :=
  lt_of_le_of_lt Scheme.size_empty_le_aleph0 B.aleph0_lt_cutoff

/-- **Representability descends along a closed immersion which is a universal homeomorphism.** Let
`j : W' ⟶ W` be a closed immersion and a universal homeomorphism, `W` quasi-compact and
quasi-separated. If `j⁻¹ L` is represented by a bounded complex of constructible flat sheaves, so
is `L`. -/
theorem IsRepresentedByConstructibleFlatEtaleComplex.of_inverseImage {W W' : B.Scheme}
    [CompactSpace W.obj] [QuasiSeparatedSpace W.obj] (j : W' ⟶ W)
    [IsClosedImmersion (B.inclusion.map j)] [UniversalHomeomorphism (B.inclusion.map j)]
    {L : DerivedCategory (EtaleModules.{u, r} Λ W.obj)}
    (hL : IsRepresentedByConstructibleFlatEtaleComplex B W' Λ
      ((etaleModuleRingDerivedInverseImage.{u, r} Λ (B.inclusion.map j)).obj L)) :
    IsRepresentedByConstructibleFlatEtaleComplex B W Λ L := by
  obtain ⟨C, a, b, ha, hb, hC, ⟨e⟩⟩ := hL
  let F := etaleModuleInverseImage.{u, r} Λ (B.inclusion.map j)
  let G := etaleModuleDirectImage.{u, r} Λ (B.inclusion.map j)
  let adj := etaleModuleInverseImageAdj.{u, r} Λ (B.inclusion.map j)
  have := adj.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits G := PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _
  have : PreservesFiniteColimits G := inferInstance
  let E : B.Scheme := B.obj (∅ : Scheme.{u}) (bigEtaleSite_contains_empty B)
  let o : E ⟶ W := ObjectProperty.homMk (emptyIsInitial.to _)
  have : IsOpenImmersion (B.inclusion.map o) :=
    inferInstanceAs (IsOpenImmersion (emptyIsInitial.to (B.inclusion.obj W)))
  have hrange : Set.range (B.inclusion.map o).base = ∅ :=
    Set.range_eq_empty_iff.2 (inferInstanceAs (IsEmpty (∅ : Scheme.{u})))
  have hjsurj : Set.range (B.inclusion.map j).base = Set.univ :=
    have := Stacks.Etale.surjective_of_universalHomeomorphism' (B.inclusion.map j)
    Set.range_eq_univ.2 (B.inclusion.map j).surjective
  have hoc : Topology.IsConstructible (Set.range (B.inclusion.map o).base) :=
    hrange ▸ Topology.IsConstructible.empty
  have hoj : Set.range (B.inclusion.map o).base = (Set.range (B.inclusion.map j).base)ᶜ := by
    rw [hrange, hjsurj, Set.compl_univ]
  let L₀ := DerivedCategory.Q.objPreimage L
  let e₀ : DerivedCategory.Q.obj L₀ ≅ L := DerivedCategory.Q.objObjPreimageIso L
  let eL₀ : L₀ ≅ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L₀) :=
    HomologicalComplex.Hom.isoOfComponents (fun n => (asIso adj.unit).app (L₀.X n))
      (fun n m _ => (adj.unit.naturality (L₀.d n m)).symm)
  refine ⟨(G.mapHomologicalComplex (ComplexShape.up ℤ)).obj C, a, b,
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff C G a).2 ha,
    (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff C G b).2 hb,
    fun n => IsConstructibleFlatEtaleModule.directImage B Λ o j hoc hoj (hC n), ⟨?_⟩⟩
  exact (G.mapDerivedCategoryFactors.app C).symm ≪≫ G.mapDerivedCategory.mapIso e ≪≫
    G.mapDerivedCategory.mapIso
      ((etaleModuleRingDerivedInverseImage.{u, r} Λ (B.inclusion.map j)).mapIso e₀.symm ≪≫
        F.mapDerivedCategoryFactors.app L₀) ≪≫
    G.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso eL₀.symm ≪≫ e₀

/-- **`D_ctf` is invariant under a universal homeomorphism which is a closed immersion.** Let
`i : Z ⟶ X` be a closed immersion of schemes of the big étale site `B` which is a universal
homeomorphism, for instance the inclusion of the reduction of `X`. An object `K` of `D(X_étale, Λ)`
lies in `D_ctf(X_étale, Λ)` if and only if `i⁻¹ K` lies in `D_ctf(Z_étale, Λ)`. -/
public theorem isCtf_iff_inverseImage {X Z : B.Scheme} (i : Z ⟶ X)
    [IsClosedImmersion (B.inclusion.map i)] [UniversalHomeomorphism (B.inclusion.map i)]
    (K : DerivedCategory (EtaleModules.{u, r} Λ X.obj)) :
    IsCtf B X Λ K ↔
      IsCtf B Z Λ ((etaleModuleRingDerivedInverseImage.{u, r} Λ (B.inclusion.map i)).obj K) := by
  refine ⟨fun hK => hK.pullback B Λ i, fun hK W g hc hq => ?_⟩
  have := hasPullbacks_bigEtaleSite B
  have := preservesPullbacks_bigEtaleSiteInclusion B
  let W' : B.Scheme := pullback g i
  let j : W' ⟶ W := pullback.fst g i
  let g' : W' ⟶ Z := pullback.snd g i
  have hsq : IsPullback (B.inclusion.map j) (B.inclusion.map g') (B.inclusion.map g)
      (B.inclusion.map i) :=
    (IsPullback.of_hasPullback g i).map B.inclusion
  have : IsClosedImmersion (B.inclusion.map j) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip inferInstance
  have : UniversalHomeomorphism (B.inclusion.map j) :=
    Stacks.Etale.universalHomeomorphism_of_isPullback hsq
  have : CompactSpace ↥(B.inclusion.obj W) := inferInstanceAs (CompactSpace W.obj)
  have : QuasiSeparatedSpace ↥(B.inclusion.obj W) := inferInstanceAs (QuasiSeparatedSpace W.obj)
  have : CompactSpace W'.obj := QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map j)
  have : QuasiSeparatedSpace W'.obj := quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map j)
  refine IsRepresentedByConstructibleFlatEtaleComplex.of_inverseImage Λ B j ?_
  have h := hK W' g' inferInstance inferInstance
  refine h.of_iso B W' Λ ?_
  exact ((etaleModuleDerivedInverseImageCompIso B Λ g' i).app K).symm ≪≫
    eqToIso (by rw [pullback.condition]) ≪≫
    (etaleModuleDerivedInverseImageCompIso B Λ j g).app K

end Stacks.EtaleCohomology
