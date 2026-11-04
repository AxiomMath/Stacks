module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreLineAtInfinity
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreModification
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LargerClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedComposite
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.BijectiveOfChernFormula
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.ChernCharacterFundamentalClass
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPullback09US
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackRightExact

/-!
# The deformation of `i_*𝒪_Z` to the normal cone, as an input of Stacks 0FE8

Let `i : Z ⟶ X` be a closed immersion, `ℐ = ker i`, and let `b : W ⟶ 𝐏¹_X` be the blowup of
`𝐏¹_X` in `∞(Z)` (Stacks 0FBG), read as a modification of `X ×_S 𝐏¹_S`, with fibre at infinity
`W_∞`, exceptional divisor `E` and strict transform `X'`, and let `i' : 𝐏¹_Z ⟶ W` be the closed
immersion of Stacks 0FE9. The proof of Stacks 0FEG feeds `F = i_*𝒪_Z` and `Q = i'_*𝒪_{𝐏¹_Z}` into
Stacks 0F9K and 0FE8, with `T = X' ⊆ W_∞`. This file verifies the hypotheses on `T` the source
calls "immediately verified":

* `X'` is a closed subscheme of `W_∞` containing every point of `W_∞` lying over `X ∖ Z`, because
  `W_∞ = E + X'` (assertion (4) of Stacks 0FBG) and `E` lies over `Z`;
* `Q|_{X'}` is zero, because `𝐏¹_Z` misses `X'` (the proof of Stacks 0FE9);
* `Q|_{b⁻¹(𝐀¹_X)}` is the pullback of `F`, because `b` is an isomorphism over `𝐀¹_X` and
  `𝐏¹_Z ⟶ 𝐏¹_X` is the base change of `i`.

## Main definitions

* `Stacks.Chow.strictTransformToFibreAtInfinity` — the closed immersion `X' ⟶ W_∞`.

## Main results

* `Stacks.Chow.mem_range_strictTransformToFibreAtInfinity` — every point of `W_∞` over `X ∖ Z`
  lies on `X'`.
* `Stacks.Chow.isZero_derivedPullback_pushforward_unit_of_disjoint` — the derived pullback of
  `j_*𝒪` along a morphism missing the image of the closed immersion `j` is zero.
* `Stacks.Chow.isZero_derivedPullback_strictTransform_lineToBlowupAtInfinity` — `Q|_{X'} = 0`.
* `Stacks.Chow.isPullback_lineToBlowupAtInfinity_affineChart` —
  `𝐏¹_Z ∩ b⁻¹(𝐀¹_X) = Z ×_X b⁻¹(𝐀¹_X)`.
* `Stacks.Chow.derivedPullbackAffineChartLineIso` — `Q|_{b⁻¹(𝐀¹_X)} ≅` the pullback of `F`.
* `Stacks.Chow.localizedChernFiniteness_blowupAtInfinity` — condition (3) of 0GUJ on `W`.

## References

* [Stacks Project, Tag 0FEG](https://stacks.math.columbia.edu/tag/0FEG)
* [Stacks Project, Tag 0FE8](https://stacks.math.columbia.edu/tag/0FE8)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0FE9](https://stacks.math.columbia.edu/tag/0FE9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### A pushforward of the structure sheaf vanishes off its support -/

section Support

variable {W P V : Scheme.{u}} (j : P ⟶ W) [IsClosedImmersion j] (k : V ⟶ W)

/-- **`j_*𝒪_P` restricts to zero along a morphism missing `j(P)`**: for a closed immersion
`j : P ⟶ W` and `k : V ⟶ W` whose image misses that of `j`, the derived pullback of
`j_*𝒪_P[0]` along `k` is zero. The morphism `k` factors through the open complement of `j(P)`,
on which `j_*𝒪_P[0]` vanishes. -/
theorem isZero_derivedPullback_pushforward_unit_of_disjoint
    (hk : Disjoint (Set.range k.base) (Set.range j.base)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      k.toLRSHom.toShHom).obj ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit P.ringCatSheaf)))) := by
  let U : W.Opens := ⟨(Set.range j.base)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      U.ι.toLRSHom.toShHom).obj ((DerivedCategory.singleFunctor W.Modules 0).obj
        ((Scheme.Modules.pushforward j).obj (SheafOfModules.unit P.ringCatSheaf)))) :=
    isZero_derivedPullback_ofRestrict_compl _ _ j.isClosedEmbedding.isClosed_range
      (supp_pushforwardStructureSheaf j).subset _ (Iso.refl _)
  exact isZero_derivedPullback_of_factors (IsOpenImmersion.lift_fac U.ι k (by
    rw [Scheme.Opens.range_ι]
    exact fun _ hx => Set.disjoint_left.1 hk hx)) hU

end Support

/-! ### The strict transform inside the fibre at infinity -/

section StrictTransform

variable {X S Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- The fibre at infinity is contained in the strict transform: `W_∞ = E + X'`. -/
theorem fibreIdealAtInfinity_le_strictTransformIdealAtInfinity :
    fibreIdealAtInfinity i.ker ≤ strictTransformIdealAtInfinity i.ker := by
  rw [fibreIdealAtInfinity_eq_mul_strictTransformIdealAtInfinity]
  exact Scheme.IdealSheafData.mul_le_right _ _

/-- **The strict transform `X' ⟶ W_∞` as a closed subscheme of the fibre at infinity** of the
blowup at infinity, read as a modification of `X ×_S 𝐏¹_S`. -/
def strictTransformToFibreAtInfinity :
    (strictTransformIdealAtInfinity i.ker).subscheme ⟶
      modificationFibreAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) :=
  Scheme.IdealSheafData.inclusion (fibreIdealAtInfinity_le_strictTransformIdealAtInfinity i) ≫
    (modificationFibreAtInfinityIso i.ker f).inv

/-- The strict transform `X' ⟶ W_∞` is a closed immersion. -/
instance isClosedImmersion_strictTransformToFibreAtInfinity :
    IsClosedImmersion (strictTransformToFibreAtInfinity f i) := by
  unfold strictTransformToFibreAtInfinity
  infer_instance

omit [IsClosedImmersion i] in
/-- The composite of `X' ⟶ W_∞` with the inclusion `W_∞ ⟶ W` is the closed immersion of the
strict transform `X'` into `W`. -/
@[reassoc (attr := simp)]
theorem strictTransformToFibreAtInfinity_inclusion :
    strictTransformToFibreAtInfinity f i ≫
        modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) =
      (strictTransformIdealAtInfinity i.ker).subschemeι := by
  rw [strictTransformToFibreAtInfinity, Category.assoc,
    modificationFibreAtInfinityIso_inv_inclusion, Scheme.IdealSheafData.inclusion_subschemeι]

/-- **The exceptional divisor lies over `Z`**: a point of `E ⊆ W` maps into `Z` under
`W ⟶ X`. -/
theorem blowupAtInfinityToBase_mem_range_of_mem_support (w : blowupAtInfinity i.ker)
    (hw : w ∈ (exceptionalIdealAtInfinity i.ker).support) :
    blowupAtInfinityToBase i.ker w ∈ Set.range i := by
  have h1 : w ∈ ((infinityCentreIdeal i.ker).comap (blowupAtInfinityToLine i.ker)).support := hw
  rw [Scheme.IdealSheafData.support_comap, infinityCentreIdeal_eq_sup,
    Scheme.IdealSheafData.support_sup] at h1
  obtain ⟨h2, -⟩ := h1
  change blowupAtInfinityToLine i.ker w ∈
    ((Scheme.Hom.ker i).comap (relativeProjectiveLine X ↘ X)).support at h2
  rw [Scheme.IdealSheafData.support_comap] at h2
  have h3 : (relativeProjectiveLine X ↘ X) (blowupAtInfinityToLine i.ker w) ∈
      ((Scheme.Hom.ker i).support : Set X) := h2
  rwa [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq] at h3

/-- **Every point of `W_∞` over `X ∖ Z` lies on the strict transform `X'`**: `W_∞ = E ∪ X'` and
`E` lies over `Z`. This is the condition on `T = X'` in Stacks 0F9K. -/
theorem mem_range_strictTransformToFibreAtInfinity
    (w : modificationFibreAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f))
    (hw : modificationProjectionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) w ∉
      Set.range i) :
    w ∈ Set.range (strictTransformToFibreAtInfinity f i) := by
  have hp : modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) w ∈
      ((fibreIdealAtInfinity i.ker).support : Set (blowupAtInfinity i.ker)) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨(modificationFibreAtInfinityIso i.ker f).hom w, by
      rw [← Scheme.Hom.comp_apply, modificationFibreAtInfinityIso_hom_subschemeι]⟩
  rw [fibreIdealAtInfinity_eq_mul_strictTransformIdealAtInfinity,
    Scheme.IdealSheafData.support_mul] at hp
  rcases hp with hE | hX
  · refine absurd ?_ hw
    have := blowupAtInfinityToBase_mem_range_of_mem_support i _ hE
    rwa [modificationProjectionAtInfinity, Scheme.Hom.comp_apply,
      modificationProjection_blowupAtInfinityToProjectiveLineProduct]
  · rw [← Scheme.IdealSheafData.range_subschemeι] at hX
    obtain ⟨q, hq⟩ := hX
    refine ⟨q, (modificationInclusionAtInfinity f
      (blowupAtInfinityToProjectiveLineProduct i.ker f)).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, strictTransformToFibreAtInfinity_inclusion, hq]

omit [IsClosedImmersion i] in
/-- **`Q|_{X'}` is zero**: the derived pullback of `i'_*𝒪_{𝐏¹_Z}[0]` along the strict transform
`X' ⟶ W_∞ ⟶ W` vanishes, `𝐏¹_Z` missing `X'`
(`comap_strictTransformIdealAtInfinity_lineToBlowupAtInfinity`). -/
theorem isZero_derivedPullback_strictTransform_lineToBlowupAtInfinity :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (strictTransformToFibreAtInfinity f i ≫ modificationInclusionAtInfinity f
        (blowupAtInfinityToProjectiveLineProduct i.ker f)).toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((Scheme.Modules.pushforward
        (lineToBlowupAtInfinity i.ker)).obj (SheafOfModules.unit _)))) := by
  refine isZero_derivedPullback_pushforward_unit_of_disjoint _ _ ?_
  rw [strictTransformToFibreAtInfinity_inclusion, Scheme.IdealSheafData.range_subschemeι,
    Set.disjoint_iff]
  rintro _ ⟨hx, y, rfl⟩
  have hy : y ∈ ((strictTransformIdealAtInfinity i.ker).comap
      (lineToBlowupAtInfinity i.ker)).support := by
    rwa [Scheme.IdealSheafData.support_comap]
  rwa [congrArg Scheme.IdealSheafData.support
    (comap_strictTransformIdealAtInfinity_lineToBlowupAtInfinity i.ker)] at hy

end StrictTransform

/-! ### `Q` over the affine chart is the pullback of `F` -/

section AffineChart

variable {X S Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- `b⁻¹(𝐀¹_X) ⟶ X`, the restriction of `W ⟶ X` to the part of the blowup at infinity over the
affine chart, is flat: it is the isomorphism `b⁻¹(𝐀¹_X) ≅ 𝐀¹_X` followed by `𝐀¹_X ⟶ X`. -/
theorem flat_affineChartRestriction_blowupAtInfinity :
    Flat (pullback.fst (blowupAtInfinityToProjectiveLineProduct i.ker f)
        (projectiveLineAffineChart f) ≫
      modificationProjection f (blowupAtInfinityToProjectiveLineProduct i.ker f)) := by
  have := isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker f
  have h : pullback.fst (blowupAtInfinityToProjectiveLineProduct i.ker f)
        (projectiveLineAffineChart f) ≫
      modificationProjection f (blowupAtInfinityToProjectiveLineProduct i.ker f) =
      pullback.snd (blowupAtInfinityToProjectiveLineProduct i.ker f)
        (projectiveLineAffineChart f) ≫
      pullback.fst (terminal.from X) (terminal.from (Spec (.of (Polynomial (ULift.{u} ℤ))))) := by
    rw [modificationProjection, pullback.condition_assoc, projectiveLineAffineChart_fst]
  rw [h]
  infer_instance

/-- **`𝐏¹_Z` over the affine chart is `𝐀¹_Z`**: the square
`𝐏¹_Z ×_W b⁻¹(𝐀¹_X) ⟶ Z`, `b⁻¹(𝐀¹_X) ⟶ X` over `i : Z ⟶ X` is cartesian, because `b` is an
isomorphism over `𝐀¹_X` and `𝐏¹_Z ⟶ 𝐏¹_X` is the base change of `i`. -/
theorem isPullback_lineToBlowupAtInfinity_affineChart :
    IsPullback
      (pullback.fst (lineToBlowupAtInfinity i.ker)
          (pullback.fst (blowupAtInfinityToProjectiveLineProduct i.ker f)
            (projectiveLineAffineChart f)) ≫
        (relativeProjectiveLine i.ker.subscheme ↘ i.ker.subscheme) ≫ inv i.toImage)
      (pullback.snd (lineToBlowupAtInfinity i.ker)
        (pullback.fst (blowupAtInfinityToProjectiveLineProduct i.ker f)
          (projectiveLineAffineChart f)))
      i
      (pullback.fst (blowupAtInfinityToProjectiveLineProduct i.ker f)
          (projectiveLineAffineChart f) ≫
        modificationProjection f (blowupAtInfinityToProjectiveLineProduct i.ker f)) := by
  set b := blowupAtInfinityToProjectiveLineProduct i.ker f
  set c := projectiveLineAffineChart f
  set e := relativeProjectiveLineIsoProjectiveLineProduct f
  have := isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct i.ker f
  have hA := (IsPullback.of_hasPullback (lineToBlowupAtInfinity i.ker)
    (pullback.fst b c)).paste_vert (IsPullback.of_hasPullback b c)
  have hb : lineToBlowupAtInfinity i.ker ≫ b =
      projectiveLineBaseChange i.ker.subschemeι ≫ e.hom := by
    rw [show b = blowupAtInfinityToLine i.ker ≫ e.hom from rfl, ← Category.assoc,
      lineToBlowupAtInfinity_comp]
  rw [hb] at hA
  have hB : IsPullback (relativeProjectiveLine i.ker.subscheme ↘ i.ker.subscheme)
      (projectiveLineBaseChange i.ker.subschemeι ≫ e.hom) i.ker.subschemeι
      (pullback.fst f (relativeProjectiveLine S ↘ S)) := by
    simpa using (isPullback_projectiveLineBaseChange i.ker.subschemeι).paste_vert
      (IsPullback.of_vert_isIso (f := 𝟙 X) (snd := e.hom)
        (fst := relativeProjectiveLine X ↘ X) (g := pullback.fst f (relativeProjectiveLine S ↘ S))
        ⟨by rw [Category.comp_id, relativeProjectiveLineIsoProjectiveLineProduct_hom_fst]⟩)
  refine (hA.paste_horiz hB).of_iso (Iso.refl _) (asIso i.toImage).symm
    (asIso (pullback.snd b c)).symm (Iso.refl _) (by simp) (by simp) (by simp) ?_
  rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp,
    modificationProjection, ← pullback.condition_assoc]

/-- **`Q|_{b⁻¹(𝐀¹_X)}` is the pullback of `F`** (the first condition on `F` and `Q` in
Stacks 0FE8): for `Q = i'_*𝒪_{𝐏¹_Z}[0]` on the blowup at infinity and `F = i_*𝒪_Z[0]` on `X`,
the derived pullback of `Q` to `b⁻¹(𝐀¹_X)` is isomorphic to the derived pullback of `F` along
`b⁻¹(𝐀¹_X) ⟶ W ⟶ X`. Both are the pushforward of the structure sheaf of `𝐏¹_Z ×_W b⁻¹(𝐀¹_X)`:
the first because `b⁻¹(𝐀¹_X) ⟶ W` is an open immersion, the second because `b⁻¹(𝐀¹_X) ⟶ X` is
flat and the square of `Stacks.Chow.isPullback_lineToBlowupAtInfinity_affineChart` is cartesian.
-/
def derivedPullbackAffineChartLineIso :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst (blowupAtInfinityToProjectiveLineProduct i.ker f)
          (projectiveLineAffineChart f)).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((Scheme.Modules.pushforward
          (lineToBlowupAtInfinity i.ker)).obj (SheafOfModules.unit _))) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (pullback.fst (blowupAtInfinityToProjectiveLineProduct i.ker f)
            (projectiveLineAffineChart f) ≫
          modificationProjection f
            (blowupAtInfinityToProjectiveLineProduct i.ker f)).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) := by
  set g := pullback.fst (blowupAtInfinityToProjectiveLineProduct i.ker f)
      (projectiveLineAffineChart f) ≫
    modificationProjection f (blowupAtInfinityToProjectiveLineProduct i.ker f)
  have sq := isPullback_lineToBlowupAtInfinity_affineChart f i
  haveI := flat_affineChartRestriction_blowupAtInfinity f i
  letI : PreservesFiniteLimits (modulePullback g.toLRSHom.toShHom) :=
    preservesFiniteLimits_pullback_of_flat g
  letI : PreservesFiniteColimits (modulePullback g.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback _
  letI : (modulePullback g.toLRSHom.toShHom).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  refine derivedPullbackSinglePushforwardUnitIso _ _ ≪≫ ?_
  refine ?_ ≪≫ (AlgebraicGeometry.derivedPullbackSingleIsoOfPreservesHomology
    g.toLRSHom.toShHom _).symm
  refine (DerivedCategory.singleFunctor _ 0).mapIso ?_
  refine ?_ ≪≫ ((AlgebraicGeometry.baseChangeIsoOfKernelAnnihilates sq.w.symm
    (AlgebraicGeometry.kernelAnnihilatesPullbackPushforward_of_isPullback sq.flip)).app
      (SheafOfModules.unit Z.ringCatSheaf)).symm
  exact (Scheme.Modules.pushforward _).mapIso
    (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso _).symm

end AffineChart

/-! ### Condition (3) of Situation 0GUJ on the blowup at infinity -/

section Finiteness

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [IsClosedImmersion i]

omit [IsClosedImmersion i] in
/-- **Condition (3) of Situation 0GUJ holds on the blowup at infinity** for every object, as
soon as `X` is quasi-compact or has quasi-compact irreducible components: `W ⟶ X` is proper, so
`W` is quasi-compact, resp. has quasi-compact irreducible components. -/
theorem localizedChernFiniteness_blowupAtInfinity
    (hX : CompactSpace X ∨ ∀ T ∈ irreducibleComponents X, IsCompact T)
    (Q : DerivedCategory (blowupAtInfinity i.ker).Modules) :
    LocalizedChernFiniteness C
      (modificationProjection sX (blowupAtInfinityToProjectiveLineProduct i.ker sX) ≫ sX) Q := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hp := (modificationProjection sX
    (blowupAtInfinityToProjectiveLineProduct i.ker sX)).isProperMap
  rcases hX with hX | hX
  · exact Or.inl ⟨by simpa using hp.isCompact_preimage (isCompact_univ (X := X))⟩
  · exact Or.inr (Or.inl (isCompact_of_mem_irreducibleComponents_of_isProperMap hp hX))

end Finiteness

end Stacks.Chow

end
