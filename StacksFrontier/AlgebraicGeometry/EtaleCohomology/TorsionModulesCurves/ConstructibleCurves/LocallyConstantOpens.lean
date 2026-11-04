module
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre
public import StacksFrontier.Algebra.Homology.Resolution.NatIntBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Fullness
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsiteFiniteType

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleStability
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.LowerShriekComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DenseSubsite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening

/-!
# Opens on which a constructible sheaf is locally constant

A constructible sheaf of `Λ`-modules is, by definition, locally constant of finite type on the
strata of a stratification of each affine open; the strata are locally closed subschemes, not
opens. This file shows that it is locally constant of finite type on suitable opens: around the
generic point of an irreducible component, on every open lying in that component and in a
neighbourhood of the generic point.

## Main results

* `isFiniteTypeLocallyConstantModuleSheaf_etaleModuleInverseImage` — local constancy of finite
  type survives inverse image along any morphism of schemes, on Mathlib's small étale sites.
* `isFiniteTypeLocallyConstantModuleSheaf_of_etaleModuleInverseImage` — it descends along a
  universal homeomorphism.
* `isFiniteTypeLocallyConstantModuleSheaf_etaleModuleRestriction_of_subset_range` — a sheaf whose
  inverse image along an immersion is locally constant of finite type is locally constant of
  finite type on every open contained in the image of the immersion.
* `exists_isOpen_isFiniteTypeLocallyConstantModuleSheaf_etaleModuleRestriction` — the statement
  about generic points above.

## Implementation notes

An open `W` inside the image of an immersion `i : T ⟶ X` is not an open of `T`: the base change
`W ×_X T ⟶ W` is a surjective closed immersion, a thickening when `T` carries a reduced structure.
Local constancy is carried across it by topological invariance of the small étale site, in the
form that base change along a universal homeomorphism is a fully faithful dense subsite inclusion
(`Stacks.EtaleCohomology.isDenseSubsite_of_universalHomeomorphism`), along which local constancy
of finite type is preserved and reflected
(`Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_iff`).

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03SI](https://stacks.math.columbia.edu/tag/03SI)
* [Stacks Project, Tag 0GJI](https://stacks.math.columbia.edu/tag/0GJI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.ConstantSheaf

universe u r

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace Stacks.EtaleCohomology

attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat moduleCat_hasLimitsOfSize

variable (Λ : Type r) [CommRing Λ]

/-- **Local constancy of finite type survives inverse image along any morphism of schemes**, on
Mathlib's small étale sites. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_etaleModuleInverseImage {T S : Scheme.{u}}
    (g : T ⟶ S) (H : EtaleModules.{u, r} Λ S)
    (hH : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r} S.smallEtaleTopology Λ H) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r} T.smallEtaleTopology Λ
      ((etaleModuleInverseImage.{u, r} Λ g).obj H) := by
  have : Small.{u} ({S, T} : Set Scheme.{u}) := inferInstance
  let B := BigEtaleSite.ofSet ({S, T} : Set Scheme.{u})
  have hS : B.Contains S := BigEtaleSite.contains_ofSet _ (Set.mem_insert _ _)
  have hT : B.Contains T := BigEtaleSite.contains_ofSet _ (Set.mem_insert_of_mem _ rfl)
  refine (isFiniteTypeLocallyConstant_sheafPullback_etaleModuleToBoundedSite_iff Λ B
    (S := B.obj S hS) (T := B.obj T hT) (ObjectProperty.homMk g) H).1 ?_
  exact isFiniteTypeLocallyConstant_smallEtaleSheafPullback B Λ _ _
    ((isFiniteTypeLocallyConstantModuleSheaf_etaleModuleToBoundedSite_iff Λ B hS H).2 hH)

/-- **Local constancy of finite type descends along a universal homeomorphism**, for instance a
surjective closed immersion. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_of_etaleModuleInverseImage {W' W : Scheme.{u}}
    (f : W' ⟶ W) [UniversalHomeomorphism f] (H : EtaleModules.{u, r} Λ W)
    (h : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r} W'.smallEtaleTopology Λ
      ((etaleModuleInverseImage.{u, r} Λ f).obj H)) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r} W.smallEtaleTopology Λ H := by
  have := isDenseSubsite_of_universalHomeomorphism f
  have := smallEtaleBaseChange_full_of_universalHomeomorphism f
  have := smallEtaleBaseChange_faithful_of_universalHomeomorphism f
  have hR := (isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_iff
    W.smallEtaleTopology W'.smallEtaleTopology (smallEtaleBaseChange f) Λ
      ((etaleModuleInverseImage.{u, r} Λ f).obj H)).2 h
  have := isIso_etaleModuleInverseImageAdj_unit_of_universalHomeomorphism.{u, r} Λ f
  exact ObjectProperty.prop_of_iso _
    (asIso ((etaleModuleInverseImageAdj.{u, r} Λ f).unit.app H)).symm hR

/-- **An open inside the image of an immersion on which a sheaf is locally constant.** Let
`i : T ⟶ X` be an immersion along which the inverse image of `ℱ` is locally constant of finite
type, and let `W ⊆ X` be an open contained in the image of `i`. Then `ℱ|_W` is locally constant of
finite type. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_etaleModuleRestriction_of_subset_range
    {T X : Scheme.{u}} (i : T ⟶ X) [IsImmersion i] (F : EtaleModules.{u, r} Λ X)
    (hi : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r} T.smallEtaleTopology Λ
      ((etaleModuleInverseImage.{u, r} Λ i).obj F))
    (W : X.Opens) (hW : (W : Set X) ⊆ Set.range i) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r} W.toScheme.smallEtaleTopology Λ
      ((etaleModuleRestriction.{u, r} Λ W.ι).obj F) := by
  let f := pullback.snd i W.ι
  let g := pullback.fst i W.ι
  have hsurj : Function.Surjective f.base := fun w =>
    show w ∈ Set.range f by rw [Scheme.Pullback.range_snd]; exact hW w.2
  have : IsClosedImmersion f := IsClosedImmersion.of_isPreimmersion f (by
    rw [Set.range_eq_univ.2 hsurj]
    exact isClosed_univ)
  have : UniversalHomeomorphism f :=
    Stacks.Etale.universalHomeomorphism_of_isClosedImmersion_of_surjective f hsurj
  refine isFiniteTypeLocallyConstantModuleSheaf_of_etaleModuleInverseImage Λ f _ ?_
  refine ObjectProperty.prop_of_iso _ ?_
    (isFiniteTypeLocallyConstantModuleSheaf_etaleModuleInverseImage Λ g _ hi)
  exact (etaleModuleInverseImageCompIso.{u, r} Λ g i).symm.app F ≪≫
    eqToIso (congrArg (fun h => (etaleModuleInverseImage.{u, r} Λ h).obj F)
      pullback.condition) ≪≫
    (etaleModuleInverseImageCompIso.{u, r} Λ f W.ι).app F ≪≫
    (etaleModuleInverseImage.{u, r} Λ f).mapIso
      ((etaleModuleInverseImageRestrictionIso.{u, r} Λ W.ι).app F)

/-- **A constructible sheaf is locally constant of finite type on an open neighbourhood of a
generic point, within its irreducible component.** Let `ℱ` be a constructible sheaf of
`Λ`-modules on `X_étale` and let `x` be the generic point of an irreducible component `Z` of `X`.
Then there is an open `O ∋ x` such that `ℱ|_W` is locally constant of finite type for every open
`W ⊆ O ∩ Z`. -/
theorem exists_isOpen_isFiniteTypeLocallyConstantModuleSheaf_etaleModuleRestriction
    {X : Scheme.{u}} (F : EtaleModules.{u, r} Λ X) (hF : IsConstructibleEtaleModule Λ F)
    (x : X) :
    ∃ O : X.Opens, x ∈ O ∧ ∀ W : X.Opens, W ≤ O → (W : Set X) ⊆ closure {x} →
      IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r} W.toScheme.smallEtaleTopology Λ
        ((etaleModuleRestriction.{u, r} Λ W.ι).obj F) := by
  let B := BigEtaleSite.containing X
  let hX : B.Contains X := BigEtaleSite.contains_containing X
  obtain ⟨U, hU⟩ : ∃ U : X.affineOpens, x ∈ (U.1 : Set X) :=
    TopologicalSpace.Opens.mem_iSup.mp (by rw [iSup_affineOpens_eq_top X]; trivial)
  obtain ⟨st, hst⟩ := hF U
  obtain ⟨k, hk⟩ : ∃ k : Fin st.n, x ∈ Set.range (B.inclusion.map (st.inclusion k)).base :=
    Set.mem_iUnion.mp (by rw [← st.covers]; exact hU)
  have := st.isImmersion k
  obtain ⟨O, C, hO, hC, hOC⟩ := (B.inclusion.map (st.inclusion k)).isLocallyClosed_range
  refine ⟨⟨O, hO⟩, (hOC ▸ hk).1, fun W hWO hWZ => ?_⟩
  have hi : IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
      (st.piece k).obj.smallEtaleTopology Λ
      ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map (st.inclusion k))).obj F) :=
    (isFiniteTypeLocallyConstant_sheafPullback_etaleModuleToBoundedSite_iff Λ B
      (S := B.obj X hX) (st.inclusion k) F).1 (hst k)
  refine isFiniteTypeLocallyConstantModuleSheaf_etaleModuleRestriction_of_subset_range Λ
    (B.inclusion.map (st.inclusion k)) F hi W fun w hw => ?_
  rw [hOC]
  exact ⟨hWO hw, closure_minimal (Set.singleton_subset_iff.2 (hOC ▸ hk).2) hC (hWZ hw)⟩

end Stacks.EtaleCohomology

end
