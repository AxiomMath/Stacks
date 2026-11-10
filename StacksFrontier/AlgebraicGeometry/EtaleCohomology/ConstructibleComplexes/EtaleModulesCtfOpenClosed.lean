module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.GlobalStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.NoetherianStratification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle

/-!
# Extension by zero and closed direct image of constructible complexes of finite Tor dimension

Let `X` be a quasi-compact and quasi-separated scheme, `j : U ⟶ X` a quasi-compact open immersion
and `i : Z ⟶ X` the closed immersion of a closed subscheme with complement the image of `j`. For an
arbitrary ring `Λ` this file proves that extension by zero `j_!` and direct image `i_*` carry
constructible flat sheaves of `Λ`-modules to constructible flat sheaves, hence bounded complexes of
them to bounded complexes of them, and `D_ctf` into `D_ctf`.

## Main results

* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_of_isZero`: a zero sheaf is constructible flat.
* `AlgebraicGeometry.isConstructibleFlatModuleSheaf_of_openClosed`: on a quasi-compact and
  quasi-separated scheme, a sheaf whose restrictions to a constructible open and to its closed
  complement are constructible flat is constructible flat.
* `Stacks.EtaleCohomology.IsConstructibleFlatEtaleModule.extensionByZero` and
  `Stacks.EtaleCohomology.IsConstructibleFlatEtaleModule.directImage`: the two functors on sheaves,
  on Mathlib's small étale site.
* `Stacks.EtaleCohomology.IsCtf.extensionByZero` and `Stacks.EtaleCohomology.IsCtf.directImage`:
  for a cochain complex `C` whose class lies in `D_ctf`, the complex obtained by applying `j_!`,
  respectively `i_*`, degreewise has its class in `D_ctf` (part (2) of Tag 0962 for an open
  immersion, and the closed-immersion case of the stability of `D_ctf` under finite direct image).

## Implementation notes

Constructible flatness is tested on the stratification of Tag 09YR built from the two-member cover
of `X` by `U` and `Z`,
`AlgebraicGeometry.exists_stratification_top_of_constructible_immersion_cover`: `j^{-1} j_! G ≅ G`
and `i^{-1} j_! G = 0`, while `i^{-1} i_* G ≅ G` and `j^{-1} i_* G = 0`.

## References

* [Stacks Project, Tag 0962](https://stacks.math.columbia.edu/tag/0962)
* [Stacks Project, Tag 09YR](https://stacks.math.columbia.edu/tag/09YR)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r r'

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- A zero sheaf of `Λ`-modules is locally constant with finite projective values. -/
public theorem isFiniteProjectiveLocallyConstant_of_isZero (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsZero F) :
    Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
      (SmallEtale.topology B X.obj X.property) F := by
  intro U
  refine ⟨PUnit, fun _ => U, fun _ => 𝟙 U, ?_, fun _ => ?_⟩
  · refine (SmallEtale.topology B X.obj X.property).superset_covering ?_
      ((SmallEtale.topology B X.obj X.property).top_mem U)
    intro W g _
    exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨PUnit.unit, g, (Category.comp_id g).symm⟩
  · let E : ModuleCat.{max (u + 1) r} Λ := ModuleCat.of Λ PUnit
    have hE : IsZero E := ModuleCat.isZero_of_subsingleton E
    refine ⟨E, inferInstance, Module.Projective.of_free, ⟨IsZero.iso ?_ ?_⟩⟩
    · exact Functor.map_isZero _ hE
    · exact Functor.map_isZero _ hF

/-- A zero sheaf of `Λ`-modules is constructible flat. -/
public theorem isConstructibleFlatModuleSheaf_of_isZero (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsZero F) :
    IsConstructibleFlatModuleSheaf B X Λ F := fun U =>
  ⟨ConstructibleStratification.singleReduced B X U.1, fun _ =>
    isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ _ F
      (isFiniteProjectiveLocallyConstant_of_isZero B Λ X F hF)⟩

/-- **Constructible flatness from an open subscheme and its closed complement.** On a quasi-compact
and quasi-separated scheme `X`, let `j : U ⟶ X` be an open immersion with constructible image and
`i : Z ⟶ X` an immersion whose image is the complement. A sheaf of `Λ`-modules whose inverse images
to `U` and to `Z` are constructible flat is constructible flat. -/
public theorem isConstructibleFlatModuleSheaf_of_openClosed {X U Z : B.Scheme}
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (j : U ⟶ X) (i : Z ⟶ X)
    (hj : IsImmersion (B.inclusion.map j)) (hi : IsImmersion (B.inclusion.map i))
    (hjc : Topology.IsConstructible (Set.range (B.inclusion.map j).base))
    (hij : Set.range (B.inclusion.map j).base = (Set.range (B.inclusion.map i).base)ᶜ)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} Λ))
    (hU : IsConstructibleFlatModuleSheaf B U Λ (smallEtalePullObj B j F))
    (hZ : IsConstructibleFlatModuleSheaf B Z Λ (smallEtalePullObj B i F)) :
    IsConstructibleFlatModuleSheaf B X Λ F := by
  have hPIso : ∀ (T : B.Scheme)
      {F G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{max (u + 1) r} Λ)},
      (F ≅ G) →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T.obj T.property) F →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T.obj T.property) G := fun T _ _ e h =>
    Stacks.ConstantSheaf.isFiniteProjectiveLocallyConstant_congr Λ _ e h
  have hPPull : ∀ (T' T : B.Scheme) (q : T' ⟶ T)
      (G : Sheaf (SmallEtale.topology B T.obj T.property) (ModuleCat.{max (u + 1) r} Λ)),
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T.obj T.property) G →
      Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant Λ
        (SmallEtale.topology B T'.obj T'.property) (smallEtalePullObj B q G) :=
    fun _ _ q G h => isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ q G h
  let T : Bool → B.Scheme := fun b => match b with | true => U | false => Z
  let k : ∀ b, T b ⟶ X := fun b => match b with | true => j | false => i
  refine isStratifiedSheaf_of_exists_stratification_top B X _ hPIso hPPull F
    (exists_stratification_top_of_constructible_immersion_cover B X _ hPIso hPPull F T k
      (fun b => by cases b <;> assumption) (fun b => ?_) ?_ (fun b => ?_))
  · cases b
    · change Topology.IsConstructible (Set.range (B.inclusion.map i).base)
      rw [← compl_compl (Set.range (B.inclusion.map i).base), ← hij]
      exact hjc.compl
    · exact hjc
  · refine Set.Subset.antisymm (fun x _ => ?_) (fun x _ => Set.mem_univ x)
    by_cases hx : x ∈ Set.range (B.inclusion.map i).base
    · exact Set.mem_iUnion.2 ⟨false, hx⟩
    · rw [← Set.mem_compl_iff, ← hij] at hx
      exact Set.mem_iUnion.2 ⟨true, hx⟩
  · cases b
    · exact hZ
    · exact hU

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ]

/-- A zero sheaf of `Λ`-modules on Mathlib's small étale site is constructible flat. -/
public theorem isConstructibleFlatEtaleModule_of_isZero (X : B.Scheme)
    {F : EtaleModules.{u, r} Λ X.obj} (hF : IsZero F) :
    IsConstructibleFlatEtaleModule B X Λ F :=
  isConstructibleFlatModuleSheaf_of_isZero B Λ X _
    (Functor.map_isZero (etaleModulesToSmallEtale B X Λ) hF)

/-- **Constructible flatness from an open subscheme and its closed complement**, on Mathlib's small
étale site of a quasi-compact and quasi-separated scheme. -/
public theorem IsConstructibleFlatEtaleModule.of_openClosed {X U Z : B.Scheme}
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] (j : U ⟶ X) (i : Z ⟶ X)
    (hj : IsImmersion (B.inclusion.map j)) (hi : IsImmersion (B.inclusion.map i))
    (hjc : Topology.IsConstructible (Set.range (B.inclusion.map j).base))
    (hij : Set.range (B.inclusion.map j).base = (Set.range (B.inclusion.map i).base)ᶜ)
    (F : EtaleModules.{u, r} Λ X.obj)
    (hU : IsConstructibleFlatEtaleModule B U Λ
      ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map j)).obj F))
    (hZ : IsConstructibleFlatEtaleModule B Z Λ
      ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map i)).obj F)) :
    IsConstructibleFlatEtaleModule B X Λ F :=
  isConstructibleFlatModuleSheaf_of_openClosed B Λ j i hj hi hjc hij _
    (isConstructibleFlatModuleSheaf_congr B U Λ (etaleModulesToSmallEtalePullbackIso B Λ j F) hU)
    (isConstructibleFlatModuleSheaf_congr B Z Λ (etaleModulesToSmallEtalePullbackIso B Λ i F) hZ)

/-- **An exact functor preserving constructible flatness preserves condition (2) of Tag 03TT**, in
the form of cochain complexes: if the class of `C` is represented by a bounded complex of
constructible flat sheaves, so is the class of the complex obtained by applying the functor
degreewise. The functor may change the coefficient ring, from `Λ` to `Λ'`. -/
public theorem IsRepresentedByConstructibleFlatEtaleComplex.map {X Y : B.Scheme}
    {Λ' : Type r'} [Ring Λ']
    (Φ : EtaleModules.{u, r} Λ Y.obj ⥤ EtaleModules.{u, r'} Λ' X.obj) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (hΦ : ∀ G, IsConstructibleFlatEtaleModule B Y Λ G →
      IsConstructibleFlatEtaleModule B X Λ' (Φ.obj G))
    {C : CochainComplex (EtaleModules.{u, r} Λ Y.obj) ℤ}
    (hC : IsRepresentedByConstructibleFlatEtaleComplex B Y Λ (DerivedCategory.Q.obj C)) :
    IsRepresentedByConstructibleFlatEtaleComplex B X Λ'
      (DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) := by
  obtain ⟨D, a, b, ha, hb, hD, ⟨e⟩⟩ := hC
  let D' := (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj D
  have ha' : CochainComplex.IsStrictlyGE D' a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => Φ.map_isZero (D.isZero_of_isStrictlyGE a i hi)
  have hb' : CochainComplex.IsStrictlyLE D' b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => Φ.map_isZero (D.isZero_of_isStrictlyLE b i hi)
  exact ⟨D', a, b, ha', hb', fun i => hΦ _ (hD i),
    ⟨(Φ.mapDerivedCategoryFactors.app D).symm ≪≫ Φ.mapDerivedCategory.mapIso e ≪≫
      Φ.mapDerivedCategoryFactors.app C⟩⟩

/-- **An exact functor preserving constructible flatness preserves `D_ctf`** between quasi-compact
and quasi-separated schemes, in the form of cochain complexes. The functor may change the
coefficient ring, from `Λ` to `Λ'`. -/
public theorem IsCtf.map {X Y : B.Scheme} [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    [CompactSpace Y.obj] [QuasiSeparatedSpace Y.obj] {Λ' : Type r'} [Ring Λ']
    (Φ : EtaleModules.{u, r} Λ Y.obj ⥤ EtaleModules.{u, r'} Λ' X.obj) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (hΦ : ∀ G, IsConstructibleFlatEtaleModule B Y Λ G →
      IsConstructibleFlatEtaleModule B X Λ' (Φ.obj G))
    {C : CochainComplex (EtaleModules.{u, r} Λ Y.obj) ℤ}
    (hC : IsCtf B Y Λ (DerivedCategory.Q.obj C)) :
    IsCtf B X Λ' (DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C)) :=
  (isCtf_iff_of_qcqs B Λ' _).2
    (IsRepresentedByConstructibleFlatEtaleComplex.map B Λ Φ hΦ ((isCtf_iff_of_qcqs B Λ _).1 hC))

private instance (X : B.Scheme) [QuasiSeparatedSpace X.obj] :
    QuasiSeparatedSpace ↥(B.inclusion.obj X) :=
  inferInstanceAs (QuasiSeparatedSpace X.obj)

private instance (X : B.Scheme) [CompactSpace X.obj] : CompactSpace ↥(B.inclusion.obj X) :=
  inferInstanceAs (CompactSpace X.obj)

variable {X U Z : B.Scheme} [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
  (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion (B.inclusion.map j)]
  [IsClosedImmersion (B.inclusion.map i)]
  (hjc : Topology.IsConstructible (Set.range (B.inclusion.map j).base))
  (hij : Set.range (B.inclusion.map j).base = (Set.range (B.inclusion.map i).base)ᶜ)

include hjc hij

/-- **Extension by zero along a quasi-compact open immersion preserves constructible flatness.**
For `j : U ⟶ X` an open immersion with constructible image into a quasi-compact and quasi-separated
scheme, and `i : Z ⟶ X` the closed immersion of the complement, `j_! G` is constructible flat when
`G` is. -/
public theorem IsConstructibleFlatEtaleModule.extensionByZero {G : EtaleModules.{u, r} Λ U.obj}
    (hG : IsConstructibleFlatEtaleModule B U Λ G) :
    IsConstructibleFlatEtaleModule B X Λ
      ((etaleModuleExtensionByZero.{u, r} Λ (B.inclusion.map j)).obj G) := by
  refine IsConstructibleFlatEtaleModule.of_openClosed B Λ j i inferInstance inferInstance hjc hij
    _ ?_ (isConstructibleFlatEtaleModule_of_isZero B Λ Z
      (isZero_etaleModuleInverseImage_extensionByZero Λ _ _ hij G))
  refine hG.of_iso B U Λ ?_
  exact (asIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ (B.inclusion.map j)).unit.app G)) ≪≫
    ((etaleModuleInverseImageRestrictionIso.{u, r} Λ (B.inclusion.map j)).app _).symm

/-- **Direct image along a closed immersion preserves constructible flatness.** For `i : Z ⟶ X` a
closed immersion into a quasi-compact and quasi-separated scheme whose open complement is the image
of an open immersion `j` with constructible image, `i_* G` is constructible flat when `G` is. -/
public theorem IsConstructibleFlatEtaleModule.directImage {G : EtaleModules.{u, r} Λ Z.obj}
    (hG : IsConstructibleFlatEtaleModule B Z Λ G) :
    IsConstructibleFlatEtaleModule B X Λ
      ((etaleModuleDirectImage.{u, r} Λ (B.inclusion.map i)).obj G) := by
  let ff := etaleModuleDirectImageFullyFaithful.{u, r} Λ (B.inclusion.map i)
  have := ff.full
  have := ff.faithful
  refine IsConstructibleFlatEtaleModule.of_openClosed B Λ j i inferInstance inferInstance hjc hij
    _ (isConstructibleFlatEtaleModule_of_isZero B Λ U ?_) ?_
  · exact (isZero_etaleModuleRestriction_etaleModuleDirectImage Λ _ _ hij G).of_iso
      ((etaleModuleInverseImageRestrictionIso.{u, r} Λ (B.inclusion.map j)).app _)
  · exact hG.of_iso B Z Λ
      (asIso ((etaleModuleInverseImageAdj.{u, r} Λ (B.inclusion.map i)).counit.app G)).symm

omit [CompactSpace X.obj] [IsClosedImmersion (B.inclusion.map i)] hjc hij in
/-- The image of a quasi-compact open immersion into a quasi-separated scheme is constructible. -/
public theorem isConstructible_range_of_compactSpace [CompactSpace U.obj] :
    Topology.IsConstructible (Set.range (B.inclusion.map j).base) :=
  (IsCompact.isRetrocompact (isCompact_range (B.inclusion.map j).base.hom.continuous)
    (B.inclusion.map j).isOpenEmbedding.isOpen_range).isConstructible
      (B.inclusion.map j).isOpenEmbedding.isOpen_range

omit hjc in
/-- **Tag 0962 (2) for an open immersion, on complexes.** For a quasi-compact open immersion
`j : U ⟶ X` into a quasi-compact and quasi-separated scheme, applying `j_!` degreewise to a complex
whose class lies in `D_ctf(U_étale, Λ)` gives a complex whose class lies in `D_ctf(X_étale, Λ)`. -/
public theorem IsCtf.extensionByZero [CompactSpace U.obj]
    {C : CochainComplex (EtaleModules.{u, r} Λ U.obj) ℤ}
    (hC : IsCtf B U Λ (DerivedCategory.Q.obj C)) :
    IsCtf B X Λ (DerivedCategory.Q.obj
      (((etaleModuleExtensionByZero.{u, r} Λ (B.inclusion.map j)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C)) := by
  have : QuasiSeparatedSpace U.obj :=
    quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map j)
  exact IsCtf.map B Λ _ (fun G hG => hG.extensionByZero B Λ j i
    (isConstructible_range_of_compactSpace B j) hij) hC

/-- **Direct image along a closed immersion preserves `D_ctf`, on complexes.** For a closed
immersion `i : Z ⟶ X` into a quasi-compact and quasi-separated scheme, with open complement the
image of an open immersion `j` with constructible image, applying `i_*` degreewise to a complex
whose class lies in `D_ctf(Z_étale, Λ)` gives a complex whose class lies in `D_ctf(X_étale, Λ)`. -/
public theorem IsCtf.directImage {C : CochainComplex (EtaleModules.{u, r} Λ Z.obj) ℤ}
    (hC : IsCtf B Z Λ (DerivedCategory.Q.obj C)) :
    IsCtf B X Λ (DerivedCategory.Q.obj
      (((etaleModuleDirectImage.{u, r} Λ (B.inclusion.map i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C)) := by
  have : CompactSpace Z.obj := QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map i)
  have : QuasiSeparatedSpace Z.obj :=
    quasiSeparatedSpace_of_quasiSeparated (B.inclusion.map i)
  have := (etaleModuleInverseImageAdj.{u, r} Λ (B.inclusion.map i)).rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (etaleModuleDirectImage.{u, r} Λ (B.inclusion.map i)) :=
    PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _
  exact IsCtf.map B Λ _ (fun G hG => hG.directImage B Λ j i hjc hij) hC

end Stacks.EtaleCohomology

end
