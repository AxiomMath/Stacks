module

public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.NodalChartNormal
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.NodalBlowupFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Quot.StableModelExistence.Acyclic
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.EtaleNodalChart
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.Derived.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.FlatCoverCriteria
public import
  StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StructureSheafIsoNearSpecialFibreTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.ModificationGlobalSections
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpReduction
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import
  StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso.FibreCohomology
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.NodalBlowupChainSpecialFibre

/-!
# One blowup of a nodal family in a singular point is structurally acyclic

Let `R` be a discrete valuation ring, `f : X ⟶ Spec R` at-worst-nodal of relative dimension one
and `x ∈ X` a closed point at which `X` has an étale nodal chart `R'[u, v]/(uv - πⁿ)` with
`n ≥ 2`. The blowup `b : X' ⟶ X` of `X` in `x` satisfies `𝒪_X = b_*𝒪_{X'}` and
`Rⁱb_*𝒪_{X'} = 0` for `i > 0`.

## The argument

Both statements are checked after pulling back along the étale chart `U ⟶ X` and along the
complement of `x`, whose images cover `X`
(`AlgebraicGeometry.DualizingDivisor.isIso_of_isIso_pullback_map_of_cover`,
`AlgebraicGeometry.DualizingDivisor.isZero_of_isZero_pullback_of_cover`). Away from `x` the
blowup is an isomorphism. Over the chart, flat base change ([Stacks, Tag 02KH]) and the fact that
blowing up commutes with flat base change ([Stacks, Tag 0805]) reduce both statements to the
blowup `X'₀ ⟶ X₀` of the local model `X₀ = Spec R'[u, v]/(uv - πⁿ)` in its origin, where:

* `𝒪_{X₀} = b_*𝒪_{X'₀}` because `X'₀ ⟶ X₀` is a modification of the spectrum of a normal domain
  (`Stacks.isIntegrallyClosed_nodalChartRing`, `AlgebraicGeometry.IsModification.isIso_c`);
* `R¹b_*𝒪_{X'₀} = 0` because `H¹(X'₀, 𝒪) = 0`
  (`Stacks.isZero_Hgroup_one_blowUp_nodalModelOriginPoint`) and `X₀` is affine.

The higher `Rⁱ`, `i ≥ 2`, vanish because the fibres of `b` lie in the fibres of `X' ⟶ Spec R`,
which are curves ([Stacks, Tag 0E7D]).

## Main results

* `Stacks.SemistableReduction.isStructurallyAcyclic_blowUpToBase_of_nodalChartAt`.

## References

* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace Stacks.SemistableReduction

open Scheme.IdealSheafData

/-! ### Fibre dimensions -/

/-- **The fibres of `c` lie in the fibres of `c ≫ p`**, so they have dimension at most one when
those do. -/
theorem topologicalKrullDim_fiber_le_one_of_comp {X Y S : Scheme.{u}} (c : X ⟶ Y) (p : Y ⟶ S)
    (h : ∀ s : S, topologicalKrullDim ((c ≫ p).fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞)) (y : Y) :
    topologicalKrullDim (c.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  rcases isEmpty_or_nonempty (c.fiber y) with hE | ⟨⟨x⟩⟩
  · rw [Stacks.Models.SpecialFibreIso.topologicalKrullDim_eq_bot_of_isEmpty]
    exact bot_le
  have hsub : Set.range (c.fiberι y) ⊆ (c ≫ p).base ⁻¹' {p y} := by
    rintro _ ⟨z, rfl⟩
    have hz : c (c.fiberι y z) = y := by
      have hmem : c.fiberι y z ∈ Set.range (c.fiberι y) := ⟨z, rfl⟩
      rwa [c.range_fiberι y] at hmem
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply, hz]
  have hle :=
    Stacks.AlgebraicGeometry.FibreDimension.topologicalKrullDim_le_of_isInducing_of_range_subset
    (c.fiberι y).isEmbedding.isInducing hsub
  rw [← IsHomeomorph.topologicalKrullDim_eq _ ((c ≫ p).fiberHomeo (p y)).isHomeomorph] at hle
  exact hle.trans (h _)

/-- The structure sheaf, as a sheaf of modules, is quasi-coherent. -/
private instance isQuasicoherent_unit_ringCatSheaf (Z : Scheme.{u}) :
    (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent :=
  inferInstanceAs (Scheme.unitModule Z).IsQuasicoherent

/-! ### Flat base change in degree one -/

section BaseChange

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **`R¹f_*𝒪 = 0` is compatible with flat base change** ([Stacks, Tag 02KH]): along a cartesian
square with `g` flat, `R¹f'_*𝒪_{X'} = 0` if and only if the pullback of `R¹f_*𝒪_X` along `g`
vanishes. -/
theorem isZero_firstDirectImage_iff_of_isPullback (H : IsPullback g' f' f g) [Flat g]
    [QuasiCompact f] [QuasiSeparated f] :
    IsZero (firstDirectImageStructureSheaf f') ↔
      IsZero ((Scheme.Modules.pullback g).obj (firstDirectImageStructureSheaf f)) := by
  let := HasDerivedCategory.standard X'.Modules
  let := HasDerivedCategory.standard S'.Modules
  let e : (Scheme.Modules.pullback g).obj (firstDirectImageStructureSheaf f) ≅
      firstDirectImageStructureSheaf f' :=
    Stacks.AlgebraicGeometry.FlatBaseChangeDerived.higherBaseChangeIso H
      (SheafOfModules.unit X.ringCatSheaf) 1 ≪≫
    ((Scheme.Modules.pushforward f').rightDerivedPlus 1).mapIso
      (Scheme.Modules.pullbackUnitIso g')
  exact e.isZero_iff.symm

end BaseChange

/-! ### The local model -/

section Model

variable {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] {π : R'}

/-- For `π ≠ 0`, the standard nodal model `Spec R'[x, y]/(xy - πⁿ)` is integral. -/
instance isIntegral_nodalModel [Fact (π ≠ 0)] (n : ℕ) : IsIntegral (nodalModel R' π n) :=
  haveI := isDomain_nodalChartRing (R := R') (pow_ne_zero n (Fact.out : π ≠ 0))
  inferInstanceAs (IsIntegral (Spec (CommRingCat.of (nodalChartRing R' (π ^ n)))))

/-- The standard nodal model `Spec R'[x, y]/(xy - πⁿ)` is affine. -/
instance isAffine_nodalModel (n : ℕ) : IsAffine (nodalModel R' π n) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (nodalChartRing R' (π ^ n)))))

/-- The standard nodal model `Spec R'[x, y]/(xy - πⁿ)` is locally noetherian. -/
instance isLocallyNoetherian_nodalModel (n : ℕ) : IsLocallyNoetherian (nodalModel R' π n) :=
  haveI : IsNoetherianRing (CommRingCat.of (nodalChartRing R' (π ^ n))) :=
    inferInstanceAs (IsNoetherianRing (nodalChartRing R' (π ^ n)))
  inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of (nodalChartRing R' (π ^ n)))))

/-- The nodal chart ring `R'[x, y]/(xy - a)`, as a commutative ring object, is noetherian. -/
private instance isNoetherianRing_commRingCat_nodalChartRing (a : R') :
    IsNoetherianRing (CommRingCat.of (nodalChartRing R' a)) :=
  inferInstanceAs (IsNoetherianRing (nodalChartRing R' a))

/-- For `π ≠ 0`, the nodal chart ring `R'[x, y]/(xy - πⁿ)` is a normal domain. -/
theorem isNormalDomain_nodalChartRing (hπ : π ≠ 0) (n : ℕ) :
    IsNormalDomain (nodalChartRing R' (π ^ n)) :=
  ⟨isDomain_nodalChartRing (pow_ne_zero n hπ),
    isIntegrallyClosed_nodalChartRing (pow_ne_zero n hπ)⟩

variable (hπ : Irreducible π) {n : ℕ} (hn : 2 ≤ n)

/-- The origin of the local model is not its generic point. -/
theorem vanishingIdeal_nodalModelOriginPoint_ne_bot :
    vanishingIdeal (⟨{nodalModelOriginPoint (isMaximal_span_singleton_of_irreducible hπ)
                        (by omega : 1 ≤ n)}, isClosed_singleton_nodalModelOriginPoint
          (isMaximal_span_singleton_of_irreducible hπ) (by omega : 1 ≤ n)⟩ :
        Closeds (nodalModel R' π n)) ≠ ⊥ := by
  have := isDomain_nodalChartRing (R := R') (pow_ne_zero n hπ.ne_zero)
  have : Fact (π ≠ 0) := ⟨hπ.ne_zero⟩
  refine vanishingIdeal_singleton_ne_bot _ _ (y := ⟨⊥, Ideal.isPrime_bot⟩) fun h => ?_
  have h' : (⊥ : Ideal (nodalChartRing R' (π ^ n))) = nodalModelOrigin R' π n :=
    congrArg PrimeSpectrum.asIdeal h
  have hmem : algebraMap R' (nodalChartRing R' (π ^ n)) π ∈ nodalModelOrigin R' π n :=
    Ideal.subset_span (Set.mem_insert _ _)
  rw [← h', Ideal.mem_bot] at hmem
  exact algebraMap_nodalChartRing_ne_zero _ hπ.ne_zero hmem

include hn in
/-- **`𝒪_{X₀} = b_*𝒪_{X'₀}` for the blowup of the local model in its origin**: it is a
modification of the spectrum of a normal domain. -/
theorem isIso_unitToPushforwardUnit_blowUp_nodalModelOriginPoint :
    IsIso (Scheme.Modules.unitToPushforwardUnit (blowUpToBase (vanishingIdeal
      (⟨{nodalModelOriginPoint (isMaximal_span_singleton_of_irreducible hπ)
          (by omega : 1 ≤ n)}, isClosed_singleton_nodalModelOriginPoint
          (isMaximal_span_singleton_of_irreducible hπ) (by omega : 1 ≤ n)⟩ :
        Closeds (nodalModel R' π n))))) := by
  have := isNormalDomain_nodalChartRing (R' := R') hπ.ne_zero n
  have := isDomain_nodalChartRing (R := R') (pow_ne_zero n hπ.ne_zero)
  have : Fact (π ≠ 0) := ⟨hπ.ne_zero⟩
  have h0 := vanishingIdeal_nodalModelOriginPoint_ne_bot hπ hn
  have hmod : IsModification (blowUpToBase (vanishingIdeal
      (⟨{nodalModelOriginPoint (isMaximal_span_singleton_of_irreducible hπ)
          (by omega : 1 ≤ n)}, isClosed_singleton_nodalModelOriginPoint
          (isMaximal_span_singleton_of_irreducible hπ) (by omega : 1 ≤ n)⟩ :
        Closeds (nodalModel R' π n)))) :=
    ⟨isBirational_blowUpToBase _ h0, inferInstance, isIntegral_blowUp _ h0⟩
  exact (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_isIso_unitToPushforwardObjUnit
    _).1 (IsModification.isIso_c hmod)

include hn in
/-- **`R¹b_*𝒪_{X'₀} = 0` for the blowup of the local model in its origin**: the base is affine
and `H¹(X'₀, 𝒪) = 0`. -/
theorem isZero_firstDirectImage_blowUp_nodalModelOriginPoint :
    IsZero (firstDirectImageStructureSheaf (blowUpToBase (vanishingIdeal
      (⟨{nodalModelOriginPoint (isMaximal_span_singleton_of_irreducible hπ)
          (by omega : 1 ≤ n)}, isClosed_singleton_nodalModelOriginPoint
          (isMaximal_span_singleton_of_irreducible hπ) (by omega : 1 ≤ n)⟩ :
        Closeds (nodalModel R' π n))))) := by
  exact isZero_rightDerivedPlus_pushforward_of_isZero_cohomology _ 1 _
    ((Stacks.Cohomology.AffineBase.isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup
      _ _ 1).2 (isZero_Hgroup_one_blowUp_nodalModelOriginPoint
        (isMaximal_span_singleton_of_irreducible hπ) hn))

end Model

/-! ### One blowup -/

section Step

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **The blowup of a nodal family in a singular point with a chart of exponent `n ≥ 2` is
structurally acyclic**: `𝒪_X = b_*𝒪_{X'}` and `Rⁱb_*𝒪_{X'} = 0` for `i > 0`. -/
theorem isStructurallyAcyclic_blowUpToBase_of_nodalChartAt {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (hf : IsAtWorstNodalOfRelativeDimensionOne f) {x : X}
    (hx : IsClosed ({x} : Set X)) {n : ℕ} (c₀ : NodalChartAt f x n) (hn : 2 ≤ n) :
    (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))).IsStructurallyAcyclic := by
  obtain ⟨c, hcX, hcM⟩ := c₀.exists_preimage_eq_singleton
  have := c.etale_toX
  have := c.etale_toModel
  set M := vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  set b := blowUpToBase M
  have hmax : (Ideal.span {c.π}).IsMaximal := isMaximal_span_singleton_of_irreducible c.irreducible
  have h1 : 1 ≤ n := by omega
  have hoC := isClosed_singleton_nodalModelOriginPoint hmax h1
  have hwo : c.toModel.base c.pt = nodalModelOriginPoint hmax h1 := PrimeSpectrum.ext c.pt_origin
  set Mo := vanishingIdeal (⟨{nodalModelOriginPoint hmax h1}, hoC⟩ :
    Closeds (nodalModel c.R' c.π n))
  have hcomap : M.comap c.toX = Mo.comap c.toModel := by
    rw [comap_vanishingIdeal_of_smooth c.toX _
        ⟨c.toX.base ⁻¹' {x}, hx.preimage c.toX.continuous⟩ rfl,
      comap_vanishingIdeal_of_smooth c.toModel _
        ⟨c.toModel.base ⁻¹' {nodalModelOriginPoint hmax h1}, hoC.preimage c.toModel.continuous⟩
        rfl]
    congr 1
    ext1
    change c.toX.base ⁻¹' {x} = c.toModel.base ⁻¹' {nodalModelOriginPoint hmax h1}
    rw [hcX, ← hwo, hcM]
  obtain ⟨h₁, sq₁⟩ := exists_isPullback_blowUpToBase_comap c.toX M
  obtain ⟨h₂, sq₂⟩ : ∃ h₂ : AlgebraicGeometry.blowUp (M.comap c.toX) ⟶ AlgebraicGeometry.blowUp Mo,
      IsPullback (blowUpToBase (M.comap c.toX)) h₂ c.toModel (blowUpToBase Mo) := by
    rw [hcomap]
    exact exists_isPullback_blowUpToBase_comap c.toModel Mo
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsIso (Scheme.Modules.unitToPushforwardUnit (blowUpToBase Mo)) :=
    isIso_unitToPushforwardUnit_blowUp_nodalModelOriginPoint c.irreducible hn
  let V : X.Opens := ⟨{x}ᶜ, hx.isOpen_compl⟩
  have : IsIso (b ∣_ V) := isIso_blowUpToBase_restrict_of_subset_compl_support _ _ <| by
    rw [coe_support_vanishingIdeal]
    exact fun z hz => hz
  have hcov : ∀ z : X, z ∈ Set.range c.toX.base ∨ z ∈ Set.range V.ι.base := fun z =>
    (eq_or_ne z x).imp (fun hz => ⟨c.pt, c.pt_mem.trans hz.symm⟩) fun hz => ⟨⟨z, hz⟩, rfl⟩
  have sqV := (isPullback_morphismRestrict b V).flip
  have h0 : IsIso (Scheme.Modules.unitToPushforwardUnit b) :=
    AlgebraicGeometry.DualizingDivisor.isIso_of_isIso_pullback_map_of_cover c.toX V.ι hcov _
      ((isIso_unitToPushforwardUnit_iff_of_isPullback sq₁.flip).1
        ((isIso_unitToPushforwardUnit_iff_of_isPullback sq₂.flip).2 inferInstance))
      ((isIso_unitToPushforwardUnit_iff_of_isPullback sqV).1
        (Stacks.Models.SpecialFibreIso.isIso_unitToPushforwardUnit_of_isIso _))
  refine Scheme.Hom.isStructurallyAcyclic_of_isZero_rightDerived_one b
    (topologicalKrullDim_fiber_le_one_of_comp b f
      (topologicalKrullDim_fiber_le_one_of_isAtWorstNodal _ (blowUp_nodalChartAt hx hf c₀ hn).1))
    h0 ((Stacks.Models.SpecialFibreIso.isZero_firstDirectImageStructureSheaf_iff b).1 ?_)
  exact AlgebraicGeometry.DualizingDivisor.isZero_of_isZero_pullback_of_cover c.toX V.ι hcov
    ((isZero_firstDirectImage_iff_of_isPullback sq₁.flip).1
      ((isZero_firstDirectImage_iff_of_isPullback sq₂.flip).2 (Functor.map_isZero _
        (isZero_firstDirectImage_blowUp_nodalModelOriginPoint c.irreducible hn))))
    ((isZero_firstDirectImage_iff_of_isPullback sqV).1
      (Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom (b ∣_ V) _ 1
        one_pos))

end Step

end Stacks.SemistableReduction

end
