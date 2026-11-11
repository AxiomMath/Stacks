module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Isomorphism
public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.TargetCover
public import StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
public import StacksFrontier.AlgebraicGeometry.NodalContraction.GenericFibreField
public import StacksFrontier.AlgebraicGeometry.PicardFibreTrivial.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardLocallyTrivial
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.OverField
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ContractExceptionalCurve
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalCurveLocus
public import StacksFrontier.AlgebraicGeometry.Surfaces.ContractionPicardDecomposition

/-!
# Descent along the contraction of an exceptional curve

Let `b : X ⟶ X'` contract an exceptional curve of the first kind `E ⊆ X`, cut out by the ideal
sheaf `D` and presented by an isomorphism `e : 𝐏¹_k ≅ E`. This file proves the descent step of
[Stacks, Tag 0C5L]: an invertible `𝒪_X`-module `ℒ` whose restriction to `E` is trivial is pulled
back from `X'`, its pushforward `b_*ℒ` is invertible and the counit `b^*b_*ℒ ⟶ ℒ` is an
isomorphism. With it, exactness at `Pic(X)` of the Picard sequence of the contraction holds for
a **general** contraction, and so does the decomposition `Pic(X) = Pic(X') ⊕ ℤ` of
[Stacks, Tag 0C5M].

The descent is proved by discharging the hypotheses of [Stacks, Tag 0E24] at the single
contracted point `z`; away from `z` the contraction is an isomorphism, which produces the
trivializing cover of the target directly.

* **Above `z`.** The fibre `X_z` is the exceptional curve
  (`AlgebraicGeometry.exists_fiberIso_subscheme_comap_vanishingIdeal`), hence `𝐏¹_k`: it has
  dimension one and `H¹(X_z, 𝒪) = 0`, and `ℒ|_{X_z}` is trivial because its class on `𝐏¹_k` has
  degree zero. So `ℒ` is trivial on `b⁻¹(V)` for a neighbourhood `V` of `z`
  (`Stacks.PicardFibreTrivial.exists_restrict_iso_unit_of_fiber`, the theorem on formal
  functions).
* **Away from `z`.** There the fibre of `b` is a single point, `ℒ` is trivial on some open
  neighbourhood `S` of it, and `b` is a closed map, being proper; so `V = X' ∖ b(X ∖ S)` is an
  open neighbourhood with `b⁻¹(V) ⊆ S`.
* **Descent.** `b_*𝒪_X = 𝒪_{X'}` for a contraction
  (`AlgebraicGeometry.IsContractionOfExceptionalCurve.isIso_c`), so the transition functions of
  `ℒ` over such a cover descend
  (`Stacks.PicFinite.exists_isInvertible_modulePullback_iso_of_forall_isIso_app`).

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exists_isInvertible_pullback_iso_of_isContraction` —
  **the descent step**: an invertible module trivial on the exceptional curve is the pullback of
  an invertible module on `X'`.
* `AlgebraicGeometry.Scheme.IdealSheafData.isInvertible_pushforward_of_isContraction` and
  `AlgebraicGeometry.Scheme.IdealSheafData.isIso_counit_app_of_isContraction` — **the descent
  step in the source's two clauses**: `b_*ℒ` is invertible and the counit `b^*b_*ℒ ⟶ ℒ` is an
  isomorphism.
* `AlgebraicGeometry.Scheme.IdealSheafData.contractionPicardExactness_of_isContraction` —
  **exactness at `Pic(X)` for a general contraction**: a class of degree zero on the exceptional
  curve is pulled back along `b`.
* `AlgebraicGeometry.Scheme.IdealSheafData.picardDecomposition_of_isContraction` and
  `AlgebraicGeometry.Scheme.IdealSheafData.contractedPicardHom_of_isContraction` — **the
  decomposition `Pic(X) = Pic(X') ⊕ ℤ` and the homomorphism `ℒ ↦ ℒ'` for a general
  contraction**, together with the source's two characterisations
  `picardDecomposition_of_isContraction_eq_iff` (`ℒ = (b^*ℒ')(-nE)`) and
  `picardDecomposition_of_isContraction_eq_iff_exceptionalTwist` (`ℒ(nE) = b^*ℒ'`), and the
  formula `ℒ' = b_*ℒ(nE)`, both for the actual pushforward of a representative of `ℒ(nE)`
  (`picardDecomposition_of_isContraction_apply_fst_eq_picardClass_pushforward`, with
  `isInvertible_pushforward_exceptionalTwist_of_isContraction` for the invertibility of
  `b_*ℒ(nE)`) and for every pushforward on Picard classes left inverse to `b^*`
  (`picardDecomposition_of_isContraction_apply_fst_pushforward`), all in the same namespace.
* `AlgebraicGeometry.isZero_coh_one_unit_projectiveLineProj` — `H¹(𝐏¹_k, 𝒪) = 0` in the spelling
  of the theorem on formal functions, and
  `AlgebraicGeometry.topologicalKrullDim_eq_one_of_iso_projectiveLineProj` — a scheme isomorphic
  to the projective line has dimension one.

## Implementation notes

The presentation `e : 𝐏¹_k ≅ E` is used only through the scheme it exhibits: the normal-sheaf
clause of `Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind` is not needed for the descent, so
`exists_isInvertible_pullback_iso_of_isContraction` and
`contractionPicardExactness_of_isContraction` ask for `e` alone. The decomposition of Tag 0C5M
does use the full hypothesis, through the degree of `𝒪_X(E)`.

The three spellings of `H¹` — `Stacks.PicardFibreTrivial.coh`,
`Stacks.Cohomology.AffineBase.moduleGlobalSections` and `Stacks.Cohomology.sectionsFunctor _ ⊤`
— are the same functor `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)` right-derived, so the
vanishing on `𝐏¹_k` of `Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_one_of_neg_one_le`
is transported by nothing more than the isomorphism `𝒪(0) ≅ 𝒪`.

## References

* [Stacks Project, Tag 0C5L](https://stacks.math.columbia.edu/tag/0C5L)
* [Stacks Project, Tag 0C5M](https://stacks.math.columbia.edu/tag/0C5M)
* [Stacks Project, Tag 0E24](https://stacks.math.columbia.edu/tag/0E24)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry

/-! ### The projective line: dimension and `H¹` -/

/-- **`H¹(𝐏¹_k, 𝒪) = 0`**, in the spelling of the theorem on formal functions. -/
public theorem isZero_coh_one_unit_projectiveLineProj (k : Type u) [Field k] :
    IsZero ((Stacks.PicardFibreTrivial.coh (projectiveLineProj k) 1).obj
      (SheafOfModules.unit (projectiveLineProj k).ringCatSheaf)) := by
  have h := Stacks.ProjectiveSpace.Cohomology.isZero_lineCohomology_one_of_neg_one_le k
    (d := 0) (by norm_num)
  exact h.of_iso (((Stacks.Cohomology.sectionsFunctor (projectiveLineProj k) ⊤).rightDerived
    1).mapIso
    (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit
      (MvPolynomial.homogeneousSubmodule (Fin 2) k)).symm)

/-- Vanishing of `H¹` of the structure sheaf transports along an isomorphism of schemes. -/
public theorem isZero_coh_one_unit_of_iso {Y Z : Scheme.{u}} (ψ : Y ≅ Z)
    (h : IsZero ((Stacks.PicardFibreTrivial.coh Y 1).obj
      (SheafOfModules.unit Y.ringCatSheaf))) :
    IsZero ((Stacks.PicardFibreTrivial.coh Z 1).obj (SheafOfModules.unit Z.ringCatSheaf)) := by
  have h2 : IsZero ((Stacks.PicardFibreTrivial.coh Z 1).obj
      ((Scheme.Modules.pushforward ψ.hom).obj (SheafOfModules.unit Y.ringCatSheaf))) :=
    (Stacks.PicardFibreTrivial.isZero_coh_pushforward_iff ψ.hom _ 1).2 h
  refine h2.of_iso ((Stacks.PicardFibreTrivial.coh Z 1).mapIso ?_)
  exact Stacks.ClosedImmersion.unitIsoOfIsIso ψ.hom _ ≪≫
    (Scheme.Modules.pushforward ψ.hom).mapIso
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso ψ.hom)

/-- **A scheme isomorphic to the projective line has topological Krull dimension one.** -/
public theorem topologicalKrullDim_eq_one_of_iso_projectiveLineProj {Y : Scheme.{u}}
    (k : Type u) [Field k] (ψ : projectiveLineProj k ≅ Y) :
    topologicalKrullDim Y = 1 := by
  let ε : projectiveSpaceOverRing 1 (CommRingCat.of k) ≅ Y :=
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1).iso ≪≫ ψ
  rw [← IsHomeomorph.topologicalKrullDim_eq _ ε.hom.homeomorph.isHomeomorph,
    topologicalKrullDim_projectiveSpaceOverRing k 1]
  rfl

namespace Scheme.IdealSheafData

variable {X X' : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
  [Stacks.Divisors.IsEffectiveCartierDivisor D] (e : projectiveLineProj k ≅ D.subscheme)
  (b : X ⟶ X')

/-! ### The descent step -/

include e in
/-- **The descent step of Stacks Project, Tag 0C5L.** Let `b : X ⟶ X'` contract the exceptional
curve `E` cut out by `D` and presented as `𝐏¹_k` by `e`, and let `ℒ` be an invertible `𝒪_X`-module
whose restriction to `E` is trivial. Then `ℒ` is the pullback along `b` of an invertible
`𝒪_{X'}`-module. -/
public theorem exists_isInvertible_pullback_iso_of_isContraction
    (hb : IsContractionOfExceptionalCurve D b) (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : Nonempty ((Scheme.Modules.pullback D.subschemeι).obj L ≅
      SheafOfModules.unit D.subscheme.ringCatSheaf)) :
    ∃ N : X'.Modules,
      Stacks.SheafOfModules.IsInvertible X'.presheaf
          (structureSheafRing X'.toRingedSpace).property N ∧
        Nonempty ((Scheme.Modules.pullback b).obj N ≅ L) := by
  classical
  have := hb.isNoetherian
  have : IsProper b := hb.isProper
  have : IsLocallyNoetherian X' := inferInstance
  have := hb.isIso_c
  have hO : ∀ W : X'.Opens, IsIso (b.app W) := fun W =>
    NatIso.isIso_app_of_isIso b.toLRSHom.toHom.c (Opposite.op W)
  obtain ⟨z, hz, -, -, hD, ebl, hebl⟩ := hb.exists_blowUp_iso
  subst hD
  obtain ⟨eE⟩ := hL
  -- the fibre over the contracted point is the exceptional curve, hence the projective line
  obtain ⟨χ, hχ⟩ := exists_fiberIso_subscheme_comap_vanishingIdeal b z hz
  have hdimz : topologicalKrullDim (b.fiber z) ≤ 1 :=
    le_of_eq (topologicalKrullDim_eq_one_of_iso_projectiveLineProj k (e ≪≫ χ.symm))
  have hH1z : IsZero ((Stacks.PicardFibreTrivial.coh (b.fiber z) 1).obj
      (SheafOfModules.unit (b.fiber z).ringCatSheaf)) :=
    isZero_coh_one_unit_of_iso (e ≪≫ χ.symm) (isZero_coh_one_unit_projectiveLineProj k)
  have hfib : (Scheme.Modules.pullback (b.fiberι z)).obj L ≅
      SheafOfModules.unit (b.fiber z).ringCatSheaf :=
    (Scheme.Modules.pullbackCongr hχ.symm).app L ≪≫
      ((Scheme.Modules.pullbackComp χ.hom _).app L).symm ≪≫
      (Scheme.Modules.pullback χ.hom).mapIso eE ≪≫
      Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso χ.hom
  -- `ℒ` is trivial above a neighbourhood of every point of `X'`
  obtain ⟨U, hU, hUiso⟩ := Stacks.Modules.exists_restrict_iso_unit_of_isInvertible L
  have hcov : Stacks.Divisors.HasTrivializingTargetCover b L := by
    intro y
    by_cases hyz : y = z
    · subst hyz
      exact Stacks.PicardFibreTrivial.exists_restrict_iso_unit_of_fiber b y hz hdimz hH1z L hfib
    · have hyW : y ∈ (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens) := hyz
      have hWiso : IsIso (b ∣_ (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens)) :=
        isIso_morphismRestrict_compl_of_blowUp_iso _ z hz
          (Scheme.IdealSheafData.coe_support_vanishingIdeal _) ebl hebl
      obtain ⟨x₀, hx₀⟩ :=
        (b ∣_ (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens)).homeomorph.surjective ⟨y, hyW⟩
      have hbx : b ((b ⁻¹ᵁ (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens)).ι x₀) = y := by
        rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, Scheme.Hom.comp_apply]
        exact congrArg Subtype.val hx₀
      have hsub : (b ⁻¹' {y} : Set X).Subsingleton :=
        Stacks.ResolutionOfSurfaces.subsingleton_fiber_of_isIso_restrict b _ hWiso hyW
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
        (show (b ⁻¹ᵁ (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens)).ι x₀ ∈ ⨆ j, U j from
          hU.symm ▸ Set.mem_univ _)
      refine ⟨⟨(b.base '' ((U i : Set X)ᶜ))ᶜ,
        (b.isClosedMap _ (U i).isOpen.isClosed_compl).isOpen_compl⟩, ?_, ?_⟩
      · rintro ⟨x', hx', hbx'⟩
        have heq : x' = (b ⁻¹ᵁ (⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩ : X'.Opens)).ι x₀ :=
          hsub hbx' hbx
        rw [heq] at hx'
        exact hx' hi
      · exact ⟨Stacks.SheafOfModules.restrictIsoUnitOfLE L
          (fun x' hx' => by by_contra hn; exact hx' ⟨x', hn, rfl⟩) (hUiso i).some⟩
  -- the transition functions descend
  have : DiscreteTopology ((((⊤ : X'.Opens) : Set X')ᶜ : Set X')) :=
    ⟨eq_bot_of_singletons_open fun x => (x.2 (Set.mem_univ x.1)).elim⟩
  exact Stacks.PicFinite.exists_isInvertible_modulePullback_iso_of_forall_isIso_app b ⊤
    (fun W _ => hO W) L hcov

/-- The descent step with the extra information that the unit `N ⟶ b_*b^*N` is an isomorphism. -/
private theorem exists_isInvertible_isIso_unit_app_pullback_iso
    (e : projectiveLineProj k ≅ D.subscheme)
    (hb : IsContractionOfExceptionalCurve D b) (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : Nonempty ((Scheme.Modules.pullback D.subschemeι).obj L ≅
      SheafOfModules.unit D.subscheme.ringCatSheaf)) :
    ∃ N : X'.Modules, ∃ _ : Stacks.SheafOfModules.IsInvertible X'.presheaf
          (structureSheafRing X'.toRingedSpace).property N,
        IsIso ((Stacks.PicardFibreTrivial.unitPP b).app N) ∧
        Nonempty ((Scheme.Modules.pullback b).obj N ≅ L) := by
  have := hb.isIso_c
  obtain ⟨N, hN, h⟩ := D.exists_isInvertible_pullback_iso_of_isContraction k e b hb L hL
  exact ⟨N, hN, Stacks.PicardFibreTrivial.isIso_unit_app_of_isInvertible b
    (fun W => NatIso.isIso_app_of_isIso b.toLRSHom.toHom.c (Opposite.op W)) N, h⟩

include e in
/-- **Stacks Project, Tag 0C5L: `b_*ℒ` is invertible.** Let `b : X ⟶ X'` contract the exceptional
curve `E` cut out by `D` and presented as `𝐏¹_k` by `e`, and let `ℒ` be an invertible `𝒪_X`-module
whose restriction to `E` is trivial. Then `b_*ℒ` is invertible. -/
public theorem isInvertible_pushforward_of_isContraction
    (hb : IsContractionOfExceptionalCurve D b) (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : Nonempty ((Scheme.Modules.pullback D.subschemeι).obj L ≅
      SheafOfModules.unit D.subscheme.ringCatSheaf)) :
    Stacks.SheafOfModules.IsInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property
      ((Scheme.Modules.pushforward b).obj L) := by
  obtain ⟨N, hN, _, ⟨eN⟩⟩ := D.exists_isInvertible_isIso_unit_app_pullback_iso k b e hb L hL
  exact Stacks.Picard.isInvertible_of_iso
    (asIso ((Stacks.PicardFibreTrivial.unitPP b).app N) ≪≫
      (Scheme.Modules.pushforward b).mapIso eN) hN

include e in
/-- **Stacks Project, Tag 0C5L: the counit `b^*b_*ℒ ⟶ ℒ` is an isomorphism.** Let `b : X ⟶ X'`
contract the exceptional curve `E` cut out by `D` and presented as `𝐏¹_k` by `e`, and let `ℒ` be an
invertible `𝒪_X`-module whose restriction to `E` is trivial. Then the counit `b^*b_*ℒ ⟶ ℒ` is an
isomorphism. -/
public theorem isIso_counit_app_of_isContraction
    (hb : IsContractionOfExceptionalCurve D b) (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hL : Nonempty ((Scheme.Modules.pullback D.subschemeι).obj L ≅
      SheafOfModules.unit D.subscheme.ringCatSheaf)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction b).counit.app L) := by
  obtain ⟨N, hN, hu, ⟨eN⟩⟩ := D.exists_isInvertible_isIso_unit_app_pullback_iso k b e hb L hL
  have hcounit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction b).counit.app
      ((Scheme.Modules.pullback b).obj N)) := by
    rw [← (Scheme.Modules.pullbackPushforwardAdjunction b).inv_map_unit]
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso
    (Scheme.Modules.pullbackPushforwardAdjunction b).counit eN.symm).mpr hcounit

/-! ### Exactness at `Pic(X)` -/

omit [Stacks.Divisors.IsEffectiveCartierDivisor D] in
/-- A Picard class of degree zero on the exceptional curve has a trivial restriction to it. -/
private theorem nonempty_pullback_subschemeι_iso_unit_of_exceptionalDegree_eq_zero
    (L : Stacks.Picard.ofScheme X) (hL : D.exceptionalDegree k e L = 0) :
    Nonempty ((Scheme.Modules.pullback D.subschemeι).obj
        (Stacks.Picard.picardRepresentative X.toRingedSpace L).obj ≅
      SheafOfModules.unit D.subscheme.ringCatSheaf) := by
  refine (Stacks.Picard.schemePullbackClass_eq_zero_iff_nonempty_iso_unit _ L).1 ?_
  have h2 : (projectiveLinePicardAddEquiv k).symm
      (Stacks.Picard.schemePullbackClass e.hom
        (Stacks.Picard.schemePullbackClass D.subschemeι L)) = 0 := hL
  have h1 := (map_eq_zero_iff _ (projectiveLinePicardAddEquiv k).symm.injective).1 h2
  have hinj : Function.Injective
      (Stacks.Picard.schemePullbackClass (X := projectiveLineProj k) e.hom) := by
    intro a c hac
    have h4 := congrArg (Stacks.Picard.schemePullbackClass e.inv) hac
    rwa [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
      e.inv_hom_id, Stacks.Picard.schemePullbackClass_id,
      Stacks.Picard.schemePullbackClass_id] at h4
  exact hinj (h1.trans (map_zero (Stacks.Picard.schemePullbackClassHom e.hom)).symm)

/-- Let `b : X ⟶ X'` contract the exceptional curve of the first kind cut out by `D`, presented as
`𝐏¹_k` by `e`. Then every Picard class of `X` of degree zero on the exceptional curve is pulled
back along `b`. -/
@[stacks 0C5L "exactness at Pic(X), the inclusion of the kernel of the degree in the image of \
b^*, for a general contraction of an exceptional curve of the first kind: with nothing assumed \
beyond the contraction"]
public theorem contractionPicardExactness_of_isContraction
    (hb : IsContractionOfExceptionalCurve D b) :
    D.ContractionPicardExactness k e b := by
  intro L hL
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Stacks.Picard.picardRepresentative X.toRingedSpace L).obj :=
    (Stacks.Picard.picardRepresentative X.toRingedSpace L).property
  obtain ⟨N, hN, ⟨eN⟩⟩ := D.exists_isInvertible_pullback_iso_of_isContraction k e b hb _
    (D.nonempty_pullback_subschemeι_iso_unit_of_exceptionalDegree_eq_zero k e L hL)
  refine ⟨Stacks.SheafOfModules.picardClass X'.presheaf
    (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace) N hN, ?_⟩
  refine (Stacks.Picard.pullbackClass_classOf b.toLRSHom.toShHom N hN).trans ?_
  refine Eq.trans ?_ (Stacks.Picard.classOf_picardRepresentative X.toRingedSpace L)
  exact (Stacks.SheafOfModules.picardClass_eq_iff X.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) _ _ _ _).2 ⟨eN⟩

/-! ### The decomposition `Pic(X) = Pic(X') ⊕ ℤ` -/

/-- The identification `Pic(X) = Pic(X') ⊕ ℤ` for `b : X ⟶ X'` the contraction of an exceptional
curve of the first kind `E ⊆ X`: a class `ℒ` on `X` corresponds to the pair `(ℒ', n)` with `n` the
degree of `ℒ` on `E`, and a pair `(ℒ', n)` to the class of `(b^*ℒ')(-nE)`. -/
@[stacks 0C5M "the identification Pic(X) = Pic(X') ⊕ Z for a general contraction of an \
exceptional curve of the first kind: with nothing assumed beyond the contraction, exactness at \
Pic(X) discharged"]
public def picardDecomposition_of_isContraction
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) :
    Stacks.Picard.ofScheme X ≃+ Stacks.Picard.ofScheme X' × ℤ :=
  D.picardDecompositionOfExactness k e b hb
    (D.contractionPicardExactness_of_isContraction k e b hb) hE

/-- The homomorphism `ℒ ↦ ℒ'` of the contraction `b : X ⟶ X'` of an exceptional curve of the first
kind. It sends a Picard class `ℒ` of `X` to the unique class `ℒ'` on `X'` with `ℒ(nE) = b^*ℒ'`,
where `n` is the degree of `ℒ` on the exceptional curve. -/
@[stacks 0C5M "the assignment L ↦ L' is a group homomorphism, for a general contraction of an \
exceptional curve of the first kind: with nothing assumed beyond the contraction, exactness at \
Pic(X) discharged"]
public def contractedPicardHom_of_isContraction
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) :
    Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X' :=
  D.contractedPicardHomOfExactness k e b hb
    (D.contractionPicardExactness_of_isContraction k e b hb) hE

/-- The `Pic(X')`-component of the decomposition of a general contraction is the homomorphism
`ℒ ↦ ℒ'`. -/
public theorem picardDecomposition_of_isContraction_apply_fst
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X) :
    (D.picardDecomposition_of_isContraction k e b hb hE L).1 =
      D.contractedPicardHom_of_isContraction k e b hb hE L :=
  rfl

/-- The integer component of the decomposition of a general contraction is the degree of `ℒ` on
the exceptional curve. -/
public theorem picardDecomposition_of_isContraction_apply_snd
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X) :
    (D.picardDecomposition_of_isContraction k e b hb hE L).2 = D.exceptionalDegree k e L :=
  rfl

/-- For the contraction of an exceptional curve of the first kind, a class `ℒ` corresponds under
the decomposition to the pair `(ℒ', n)` if and only if `ℒ = (b^*ℒ')(-nE)`. -/
@[stacks 0C5M "the characterisation: L corresponds to the pair (L', n) if and only if \
L = (b^*L')(-nE), for a general contraction of an exceptional curve of the first kind: with \
nothing assumed beyond the contraction"]
public theorem picardDecomposition_of_isContraction_eq_iff
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X)
    (L' : Stacks.Picard.ofScheme X') (n : ℤ) :
    D.picardDecomposition_of_isContraction k e b hb hE L = (L', n) ↔
      L = Stacks.Picard.schemePullbackClassHom b L' + negativeExceptionalMultipleHom D n :=
  D.picardDecompositionOfExactness_eq_iff k e b hb
    (D.contractionPicardExactness_of_isContraction k e b hb) hE L L' n

/-- For the contraction of an exceptional curve of the first kind, a class `ℒ` corresponds under
the decomposition to the pair `(ℒ', n)` if and only if `ℒ(nE)` is the pullback of `ℒ'` along
`b`. -/
@[stacks 0C5M "the characterisation in the source's second form: L corresponds to (L', n) if \
and only if L(nE) = b^*L', for a general contraction of an exceptional curve of the first kind: \
with nothing assumed beyond the contraction"]
public theorem picardDecomposition_of_isContraction_eq_iff_exceptionalTwist
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X)
    (L' : Stacks.Picard.ofScheme X') (n : ℤ) :
    D.picardDecomposition_of_isContraction k e b hb hE L = (L', n) ↔
      D.exceptionalTwist n L = Stacks.Picard.schemePullbackClassHom b L' :=
  D.picardDecompositionOfExactness_eq_iff_exceptionalTwist k e b hb
    (D.contractionPicardExactness_of_isContraction k e b hb) hE L L' n

/-- The homomorphism `ℒ ↦ ℒ'` of a general contraction is left inverse to `b^*`. -/
public theorem contractedPicardHom_of_isContraction_schemePullbackClassHom
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L' : Stacks.Picard.ofScheme X') :
    D.contractedPicardHom_of_isContraction k e b hb hE
        (Stacks.Picard.schemePullbackClassHom b L') = L' :=
  D.contractedPicardHomOfExactness_schemePullbackClassHom k e b hb
    (D.contractionPicardExactness_of_isContraction k e b hb) hE L'

/-- For the contraction of an exceptional curve of the first kind, the `Pic(X')`-component of the
decomposition is `p(ℒ(nE))`, with `n` the degree of `ℒ` on the exceptional curve, for every
pushforward `p` on Picard classes left inverse to `b^*`. -/
@[stacks 0C5M "the formula L' = b_*L(nE) read off the proof of Tag 0C5L, stated for every \
pushforward on Picard classes left inverse to b^*, for a general contraction of an exceptional \
curve of the first kind: with nothing assumed beyond the contraction, exactness at Pic(X) \
discharged and such a pushforward exhibited"]
public theorem picardDecomposition_of_isContraction_apply_fst_pushforward
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    (p : Stacks.Picard.ofScheme X →+ Stacks.Picard.ofScheme X')
    (hp : ∀ L' : Stacks.Picard.ofScheme X',
      p (Stacks.Picard.schemePullbackClassHom b L') = L')
    (L : Stacks.Picard.ofScheme X) :
    (D.picardDecomposition_of_isContraction k e b hb hE L).1 =
      p (D.exceptionalTwist (D.exceptionalDegree k e L) L) :=
  D.picardDecompositionOfExactness_apply_fst k e b hb
    (D.contractionPicardExactness_of_isContraction k e b hb) hE p hp L

/-- For the contraction of an exceptional curve of the first kind, `b_*ℒ(nE)` is invertible, where
`ℒ(nE)` is represented by `Stacks.Picard.picardRepresentative` and `n` is the degree of `ℒ` on the
exceptional curve. -/
public theorem isInvertible_pushforward_exceptionalTwist_of_isContraction
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X) :
    Stacks.SheafOfModules.IsInvertible X'.presheaf
      (structureSheafRing X'.toRingedSpace).property
      ((Scheme.Modules.pushforward b).obj (Stacks.Picard.picardRepresentative X.toRingedSpace
        (D.exceptionalTwist (D.exceptionalDegree k e L) L)).obj) := by
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Stacks.Picard.picardRepresentative X.toRingedSpace
        (D.exceptionalTwist (D.exceptionalDegree k e L) L)).obj :=
    (Stacks.Picard.picardRepresentative X.toRingedSpace _).property
  exact D.isInvertible_pushforward_of_isContraction k e b hb _
    (D.nonempty_pullback_subschemeι_iso_unit_of_exceptionalDegree_eq_zero k e _
      (D.exceptionalDegree_exceptionalTwist_self k e hE L))

/-- **`ℒ' = b_*ℒ(nE)`.** For the contraction `b : X ⟶ X'` of an exceptional curve of the first
kind, the `Pic(X')`-component `ℒ'` of the decomposition of a class `ℒ` is the class of the
invertible module `b_*ℒ(nE)`, the pushforward along `b` of a representative of `ℒ(nE)`, where `n`
is the degree of `ℒ` on the exceptional curve. -/
@[stacks 0C5M "the formula L' = b_*L(nE): the Pic(X')-component of the class L is the class of \
the pushforward along b of a representative of L(nE), for a general contraction of an \
exceptional curve of the first kind"]
public theorem picardDecomposition_of_isContraction_apply_fst_eq_picardClass_pushforward
    (hb : IsContractionOfExceptionalCurve D b)
    (hE : D.IsExceptionalCurveOfFirstKind k e) (L : Stacks.Picard.ofScheme X) :
    (D.picardDecomposition_of_isContraction k e b hb hE L).1 =
      Stacks.SheafOfModules.picardClass X'.presheaf
        (Stacks.RingedSpace.structureIsSheaf X'.toRingedSpace)
        ((Scheme.Modules.pushforward b).obj (Stacks.Picard.picardRepresentative X.toRingedSpace
          (D.exceptionalTwist (D.exceptionalDegree k e L) L)).obj)
        (D.isInvertible_pushforward_exceptionalTwist_of_isContraction k e b hb hE L) := by
  have : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property
      (Stacks.Picard.picardRepresentative X.toRingedSpace
        (D.exceptionalTwist (D.exceptionalDegree k e L) L)).obj :=
    (Stacks.Picard.picardRepresentative X.toRingedSpace _).property
  have hc := D.isIso_counit_app_of_isContraction k e b hb
    (Stacks.Picard.picardRepresentative X.toRingedSpace
      (D.exceptionalTwist (D.exceptionalDegree k e L) L)).obj
    (D.nonempty_pullback_subschemeι_iso_unit_of_exceptionalDegree_eq_zero k e _
      (D.exceptionalDegree_exceptionalTwist_self k e hE L))
  refine injective_schemePullbackClassHom_of_isContraction (D := D) (b := b) (hb := hb) ?_
  rw [picardDecomposition_of_isContraction_apply_fst, contractedPicardHom_of_isContraction,
    contractedPicardHomOfExactness_apply, D.schemePullbackClassHom_contractedClass k e b]
  symm
  refine (Stacks.Picard.pullbackClass_classOf b.toLRSHom.toShHom _ _).trans ?_
  refine Eq.trans ?_ (Stacks.Picard.classOf_picardRepresentative X.toRingedSpace _)
  exact (Stacks.SheafOfModules.picardClass_eq_iff X.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) _ _ _ _).2
    ⟨@asIso _ _ _ _ _ hc⟩

end Scheme.IdealSheafData

end AlgebraicGeometry

end
