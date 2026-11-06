module

public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleLength
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.CohomologyColimitReduction.Basic
public import StacksFrontier.AlgebraicGeometry.DevissageColimit.Basic
public import StacksFrontier.AlgebraicGeometry.LerayAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoretic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.CohomologyVanishingDevissage
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.Peeling
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# Vanishing above the affine stratification number

On a nonempty quasi-compact quasi-separated scheme `X` with affine stratification number `n` the
cohomology `Hᵖ(X, F)` of a quasi-coherent `𝒪_X`-module vanishes for `p > n`. This file carries
out the cohomological dévissage of the source's induction, so that the two conditions the
induction was assembled from in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/AffineStratification/CohomologyVanishingDevissage.lean`
are discharged and the vanishing holds outright.

## Main results

* `AlgebraicGeometry.isZero_hgroup_of_nonempty_affineStratification`: the induction on the length
  of an affine stratification.
* `AlgebraicGeometry.cohomologicalDevissageStep`: the dévissage condition
  `AlgebraicGeometry.CohomologicalDevissageStep`, discharged.
* `AlgebraicGeometry.isZero_cohomology_of_affineStratificationNumber`: **[Stacks, Tag 0F2Y]**,
  with no hypothesis beyond the tag's own.

## Implementation notes

The induction is on the length of an affine stratification rather than on the affine
stratification number, and it has no topological hypothesis: a scheme carrying a finite affine
stratification is quasi-compact and quasi-separated by [Stacks, Tag 0F2U], so the hypotheses the
cohomological steps need are extracted from the stratification itself.

The inductive step runs the source's dévissage for the top stratum `U`, an affine open with
affine inclusion by [Stacks, Tag 06AD]. The unit `η : F ⟶ j_*(F|_U)` of the
restriction-pushforward adjunction has quasi-coherent kernel and cokernel, both supported in the
complement of `U`, and `Hᵖ(X, j_*(F|_U)) = 0` for `p > 0` by [Stacks, Tags 089W and 01XB]; the
four-term exact sequence `0 → K → F → j_*(F|_U) → Q → 0` is split into two short exact sequences
and the long exact cohomology sequence of the δ-functor `Hᵖ(X, -)` reduces the claim to the
vanishing for `K` and `Q`.

For a module supported in the complement of `U` the reduction to the inductive hypothesis is
[Stacks, Tag 01PG] with [Stacks, Tag 01FF] — cohomology commutes with the presentation of a
quasi-coherent module as the filtered colimit of its finite type quasi-coherent submodules — and
then [Stacks, Tag 05JU]: a finite type quasi-coherent submodule is the direct image of a module
on its scheme-theoretic support, a closed subscheme of `X` whose underlying space misses `U` and
which therefore inherits an affine stratification one shorter.

## References

* [Stacks Project, Tag 0F2Y](https://stacks.math.columbia.edu/tag/0F2Y)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 05JU](https://stacks.math.columbia.edu/tag/05JU)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

namespace AlgebraicGeometry

/-! ### Reduction to the finite type quasi-coherent submodules -/

/-- **The reduction of [Stacks, Tag 0F2Y] to modules of finite type.** On a quasi-compact
quasi-separated scheme, if `Hᵖ(X, M) = 0` for every finite type quasi-coherent submodule `M` of a
quasi-coherent module `F`, then `Hᵖ(X, F) = 0`: `F` is the filtered colimit of those submodules by
[Stacks, Tag 01PG] and cohomology commutes with that colimit by [Stacks, Tag 01FF]. -/
theorem isZero_hgroup_of_finiteType_subobjects {X : Scheme.{u}}
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (hsub : ∀ M : X.Modules, M.IsQuasicoherent → M.IsFiniteType →
      ∀ i : M ⟶ F, Mono i → IsZero (Hgroup X.ringCatSheaf ⊤ p M)) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) := by
  obtain ⟨hcol⟩ :=
    Stacks.AlgebraicGeometry.CohomologyColimitReduction.nonempty_isColimit_mapCocone_hfunctor F p
  refine Stacks.DevissageColimit.isZero_of_isColimit (fun j => ?_) hcol
  set M := (equivSmallModel (FiniteTypeQuasicoherentSubobject F)).inverse.obj j
  exact hsub _ M.property.1 M.property.2 M.obj.arrow (Subobject.arrow_mono _)

/-! ### The two cohomological inputs of the dévissage -/

/-- **The positive-degree cohomology of the direct image of a quasi-coherent module from an
affine open with affine inclusion vanishes**, by [Stacks, Tag 089W] and [Stacks, Tag 01XB]. -/
theorem isZero_hgroup_pushforward_isAffineOpen {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) [IsAffineHom U.ι] (G : U.toScheme.Modules) [G.IsQuasicoherent]
    (p : ℕ) (hp : 0 < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p ((Scheme.Modules.pushforward U.ι).obj G)) := by
  have : IsAffine U.toScheme := hU
  exact (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen U.toScheme G ⊤
    (isAffineOpen_top U.toScheme) p hp).of_iso
      (Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp U.ι p G).symm

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **The kernel and the cokernel of the unit `F ⟶ j_*(F|_U)` are supported in the complement of
`U`.** The unit restricts to an isomorphism over `U`, by the triangle identity and the
invertibility of the counit of the restriction-pushforward adjunction, so both its kernel and its
cokernel restrict to zero there. -/
theorem supp_kernel_cokernel_restrictAdjunction_unit {X : Scheme.{u}} (F : X.Modules)
    (U : X.Opens) :
    SheafOfModules.supp (kernel ((Scheme.Modules.restrictAdjunction U.ι).unit.app F)) ⊆
        (U : Set X)ᶜ ∧
      SheafOfModules.supp (cokernel ((Scheme.Modules.restrictAdjunction U.ι).unit.app F)) ⊆
        (U : Set X)ᶜ := by
  have _ : PreservesFiniteLimits (Scheme.Modules.restrictFunctor U.ι) :=
    AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor U.ι
  set φ := (Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app F) with hφ
  have _ : IsIso ((Scheme.Modules.restrictAdjunction U.ι).counit.app
      ((Scheme.Modules.restrictFunctor U.ι).obj F)) :=
    NatIso.isIso_app_of_isIso _ _
  have he : φ = inv ((Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.restrictFunctor U.ι).obj F)) :=
    (cancel_mono ((Scheme.Modules.restrictAdjunction U.ι).counit.app
      ((Scheme.Modules.restrictFunctor U.ι).obj F))).mp
      (by simp [hφ])
  have _ : IsIso φ := by rw [he]; infer_instance
  refine ⟨Stacks.Algebraization.supp_subset_compl_of_isZero_restrict U _ ?_,
    Stacks.Algebraization.supp_subset_compl_of_isZero_restrict U _ ?_⟩
  · exact (isZero_kernel_of_mono _).of_iso
      (PreservesKernel.iso (Scheme.Modules.restrictFunctor U.ι) _)
  · exact (isZero_cokernel_of_epi _).of_iso
      (PreservesCokernel.iso (Scheme.Modules.restrictFunctor U.ι) _)

/-! ### The induction -/

/-- **The inductive step of [Stacks, Tag 0F2Y].** Let `s` be an affine stratification of `Y`
indexed by `Fin (m + 2)`. If the cohomology of every quasi-coherent module vanishes above `m` on
every scheme carrying an affine stratification indexed by `Fin (m + 1)`, then the cohomology of
every quasi-coherent module on `Y` vanishes above `m + 1`. -/
theorem quasicoherentCohomologyVanishesAbove_succ_of_affineStratification (m : ℕ)
    (Y : Scheme.{u}) (s : AffineStratification Y (Fin (m + 2)))
    (ih : ∀ W : Scheme.{u}, Nonempty (AffineStratification W (Fin (m + 1))) →
      QuasicoherentCohomologyVanishesAbove W m) :
    QuasicoherentCohomologyVanishesAbove Y (m + 1) := by
  obtain ⟨hcompact, hqsep⟩ := (hasFiniteAffineStratification_iff.{u, 0} Y).1
    ⟨Fin (m + 2), inferInstance, inferInstance, ⟨s⟩⟩
  have _ : CompactSpace (Y : Type u) := hcompact
  have _ : QuasiSeparatedSpace (Y : Type u) := hqsep
  set U : Y.Opens := ⟨s.strata (Fin.last (m + 1)), s.isOpen_strata_last⟩ with hUdef
  have hUred : IsAffine (reducedInducedScheme (U : Set Y) U.isOpen.isLocallyClosed) :=
    s.isAffine (Fin.last (m + 1))
  have hUaff : IsAffineOpen U :=
    isAffineOpen_of_isAffine_reducedInduced isAffineOfSurjectiveImmersion U hUred
  have _ : IsAffineHom U.ι :=
    isAffineHom_ι_of_isAffineHom_reducedInducedInclusion isAffineOfSurjectiveImmersion U hUred
      (s.isAffineHom (Fin.last (m + 1)))
  -- Modules supported off the top stratum have cohomology vanishing above `m`.
  have supported : ∀ G : Y.Modules, G.IsQuasicoherent →
      SheafOfModules.supp G ⊆ (U : Set Y)ᶜ → ∀ q : ℕ, m < q →
      IsZero (Hgroup Y.ringCatSheaf ⊤ q G) := by
    intro G hG hGsupp q hq
    have _ : G.IsQuasicoherent := hG
    refine isZero_hgroup_of_finiteType_subobjects G q fun M hMqc hMft i hi => ?_
    have _ : M.IsQuasicoherent := hMqc
    have _ : M.IsFiniteType := hMft
    have _ : Mono i := hi
    have hJsupp : ((Scheme.Modules.schemeTheoreticSupport M).support : Set Y) ⊆
        (s.strata (Fin.last (m + 1)))ᶜ := by
      rw [← Scheme.Modules.supp_eq_support_schemeTheoreticSupport M]
      exact (Stacks.Chow.supp_subset_of_mono i).trans hGsupp
    obtain ⟨N, hNqc, hNft, ⟨e⟩⟩ := Scheme.Modules.exists_module_on_schemeTheoreticSupport M
    have _ : N.IsQuasicoherent := hNqc
    refine (ih (Scheme.Modules.schemeTheoreticSupport M).subscheme
      (AffineStratification.nonempty_subscheme s _ hJsupp) N hNqc q hq).of_iso ?_
    exact ((Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp
      (Scheme.Modules.schemeTheoreticSupport M).subschemeι q N) ≪≫
      (Hfunctor Y.ringCatSheaf ⊤ q).mapIso e).symm
  intro F hF p hp
  have _ : F.IsQuasicoherent := hF
  obtain ⟨p, rfl⟩ : ∃ q : ℕ, p = q + 1 := ⟨p - 1, by omega⟩
  have _ : (F.restrict U.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor U.ι F
  have _ : ((Scheme.Modules.pushforward U.ι).obj (F.restrict U.ι)).IsQuasicoherent :=
    inferInstance
  set η : F ⟶ (Scheme.Modules.pushforward U.ι).obj (F.restrict U.ι) :=
    (Scheme.Modules.restrictAdjunction U.ι).unit.app F with hηdef
  have _ : (kernel η).IsQuasicoherent := inferInstance
  have _ : (cokernel η).IsQuasicoherent := inferInstance
  have hsupp := supp_kernel_cokernel_restrictAdjunction_unit F U
  have hS₁ : (ShortComplex.cokernelSequence (kernel.ι η)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := by dsimp [ShortComplex.cokernelSequence]; infer_instance }
  have hS₂ : (ShortComplex.kernelSequence (cokernel.π η)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _
      epi_g := by dsimp [ShortComplex.kernelSequence]; infer_instance }
  have himage := Stacks.AlgebraicGeometry.LerayAffineBase.isZero_obj_X₁_succ
    (Stacks.AlgebraicGeometry.LerayAffineBase.secDelta Y) hS₂ p
    (isZero_hgroup_pushforward_isAffineOpen U hUaff (F.restrict U.ι) (p + 1) (by omega))
    (supported (cokernel η) inferInstance hsupp.2 p (by omega))
  exact Stacks.AlgebraicGeometry.LerayAffineBase.isZero_obj_X₂
    (Stacks.AlgebraicGeometry.LerayAffineBase.secDelta Y) hS₁ (p + 1)
    (supported (kernel η) inferInstance hsupp.1 (p + 1) (by omega))
    (himage.of_iso ((Hfunctor Y.ringCatSheaf ⊤ (p + 1)).mapIso (Abelian.coimageIsoImage η)))

/-- **The induction of [Stacks, Tag 0F2Y].** On a scheme carrying an affine stratification
indexed by `Fin (n + 1)` the cohomology of every quasi-coherent module vanishes above `n`. -/
theorem isZero_hgroup_of_nonempty_affineStratification : ∀ (n : ℕ) (Y : Scheme.{u}),
    Nonempty (AffineStratification Y (Fin (n + 1))) →
    QuasicoherentCohomologyVanishesAbove Y n := by
  intro n
  induction n with
  | zero =>
    rintro Y ⟨t⟩
    have hLC := t.isLocallyFiniteStratification.isStratification.isPartition.locallyClosed 0
    have hsub : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    have hrange : Set.range (reducedInducedInclusion (t.strata 0) hLC).base = Set.univ := by
      refine (range_reducedInducedInclusion (t.strata 0) hLC).trans ?_
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp
        (t.isLocallyFiniteStratification.isStratification.isPartition.cover ▸ Set.mem_univ x)
      exact (Subsingleton.elim j 0) ▸ hxj
    have _ : IsAffine (reducedInducedScheme (t.strata 0) hLC) := t.isAffine 0
    have _ : IsAffine Y := isAffineOfSurjectiveImmersion Y _
      (reducedInducedInclusion (t.strata 0) hLC) inferInstance hrange inferInstance
    exact quasicoherentCohomologyVanishesAbove_zero_of_isAffine Y
  | succ m ih =>
    rintro Y ⟨t⟩
    exact quasicoherentCohomologyVanishesAbove_succ_of_affineStratification m Y t ih

/-! ### The dévissage condition, and the vanishing -/

/-- **[Stacks, Tag 0F2Y], the cohomological dévissage step.** The condition
`AlgebraicGeometry.CohomologicalDevissageStep`, discharged: an affine open `U` with affine
inclusion and an affine stratification indexed by `Fin (m + 1)` of a closed subscheme carrying
the complement of `U` assemble into an affine stratification of the ambient scheme indexed by
`Fin (m + 2)`, and the induction applies to it. -/
theorem cohomologicalDevissageStep : CohomologicalDevissageStep.{u} := by
  intro m Y U hU hUhom V j hj hjrange ht _
  have _ : IsAffineHom U.ι := hUhom
  have _ : IsClosedImmersion j := hj
  exact isZero_hgroup_of_nonempty_affineStratification (m + 1) Y
    (AffineStratification.nonempty_of_isAffineOpen_compl U hU j hjrange ht.some)

/-- **[Stacks, Tag 0F2Y].** Let `X` be a nonempty quasi-compact quasi-separated scheme with
affine stratification number `n`. Then `Hᵖ(X, F) = 0` for every `p > n` and every quasi-coherent
`𝒪_X`-module `F`. -/
@[stacks 0F2Y]
theorem isZero_cohomology_of_affineStratificationNumber (X : Scheme.{u}) [Nonempty X]
    [CompactSpace X] [QuasiSeparatedSpace X] (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (hp : affineStratificationNumber X < p) :
    IsZero (Hgroup X.ringCatSheaf ⊤ p F) :=
  isZero_cohomology_of_affineStratificationNumber_lt isAffineOfSurjectiveImmersion
    cohomologicalDevissageStep X F p hp

end AlgebraicGeometry

end
