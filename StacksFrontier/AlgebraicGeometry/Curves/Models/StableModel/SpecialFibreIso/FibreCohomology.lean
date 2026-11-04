module

public import
  StacksFrontier.AlgebraicGeometry.Curves.Models.StableModel.SpecialFibreIso.BaseChangeSquares
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GorensteinGeometry
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequenceGenericFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentProperCurve
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimensionAux
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreFirstCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ProperFibreDimensionVanishing
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing

/-!
# The fibres of the contraction have dimension at most one and no first cohomology

In the situation of [Stacks, Tag 0C61] let `c : X ⟶ Y` be a proper morphism over `Spec R` which
is an isomorphism on generic fibres and whose special fibre is `c_k = c₀ ≫ h`, with `c₀` a stable
contraction ([Stacks, Tag 0E7Q]) and `h` finite. Every fibre `X_y` of `c` has dimension at most
one, being contained in a fibre of `X ⟶ Spec R`, and `H¹(X_y, 𝒪) = 0`. The point `y` lies on
`Y_K` or on `Y_k`, and by [Stacks, Tag 0E7F] part (2) it suffices that `R¹` of the structure
sheaf vanishes along the base change of `c` to that fibre, which is `c_K` respectively `c_k` up to
isomorphism:

* `c_K` is an isomorphism, hence affine, so its higher direct images vanish;
* `R¹(c₀ ≫ h)_*𝒪 ≅ R¹h_*𝒪_{Y₀}` because `𝒪_{Y₀} = c₀_*𝒪_{X_k}` and `Rⁱc₀_*𝒪_{X_k} = 0` for
  `i > 0` (for `i = 1` by hypothesis, for `i ≥ 2` because the fibres of `c₀` are curves), and
  `R¹h_*𝒪_{Y₀} = 0` as `h` is affine.

## Main results

* `Stacks.Models.RegularProperModelSituation.topologicalKrullDim_fiber_le_one`.
* `Stacks.Models.RegularProperModelSituation.isZero_firstDirectImage_specialFiberMap`:
  `R¹c_{k*}𝒪_{X_k} = 0`.
* `Stacks.Models.RegularProperModelSituation.isZero_firstCohomologyStructureSheaf_fiber`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace Stacks.Models.SpecialFibreIso

/-- `R¹ f_* 𝒪_X = 0` in the `ℤ`-indexed spelling `firstDirectImageStructureSheaf` is the same as
in Mathlib's `ℕ`-indexed spelling. -/
theorem isZero_firstDirectImageStructureSheaf_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsZero (firstDirectImageStructureSheaf f) ↔
      IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) := by
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard Y.Modules
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).symm

/-- **The higher direct images of the structure sheaf along an affine morphism vanish.** -/
theorem isZero_rightDerived_unit_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj
      (SheafOfModules.unit X.ringCatSheaf)) :=
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    inferInstanceAs (Scheme.unitModule X).IsQuasicoherent
  Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward f _ n hn

/-- **Higher direct images vanish above the fibre dimension**, in Mathlib's `ℕ`-indexing: for `f`
proper with fibres of dimension at most one, `Rⁱf_*𝒪_X = 0` for `i ≥ 2`. -/
theorem isZero_rightDerived_unit_of_fiber_dim_le_one {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) (n : ℕ)
    (hn : 1 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    inferInstanceAs (Scheme.unitModule X).IsQuasicoherent
  let := HasDerivedCategory.standard X.Modules
  let := HasDerivedCategory.standard Y.Modules
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ n _).2
    (isZero_rightDerivedPlus_pushforward_of_forall_fiber_dim_le f hdim _ n
      (by exact_mod_cast hn))

/-- A topological space with no points has dimension `⊥`. -/
theorem topologicalKrullDim_eq_bot_of_isEmpty (T : Type*) [TopologicalSpace T] [IsEmpty T] :
    topologicalKrullDim T = ⊥ := by
  have : IsEmpty (TopologicalSpace.IrreducibleCloseds T) :=
    ⟨fun Z => Z.isIrreducible.nonempty.elim fun x _ => isEmptyElim x⟩
  exact Order.krullDim_eq_bot

end Stacks.Models.SpecialFibreIso

namespace Stacks.Models.RegularProperModelSituation

open Stacks.Models.SpecialFibreIso

variable (S : RegularProperModelSituation.{u})

/-- **Every fibre of a morphism of models out of `X` has dimension at most one**: it lies in a
fibre of `X ⟶ Spec R`, which is a curve or empty (Tag 0C60 part (1)). -/
theorem topologicalKrullDim_fiber_le_one {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of S.R))
    (c : S.X ⟶ Y) (hc : c ≫ pY = S.X_to_R) (y : Y) :
    topologicalKrullDim (c.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  rcases isEmpty_or_nonempty (c.fiber y) with hE | ⟨⟨x⟩⟩
  · rw [topologicalKrullDim_eq_bot_of_isEmpty]
    exact bot_le
  have hsub : Set.range (c.fiberι y) ⊆ S.X_to_R ⁻¹' {pY y} := by
    rintro _ ⟨z, rfl⟩
    have hz : c (c.fiberι y z) = y := by
      have hmem : c.fiberι y z ∈ Set.range (c.fiberι y) := ⟨z, rfl⟩
      rw [c.range_fiberι y] at hmem
      exact hmem
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hc, Scheme.Hom.comp_apply, hz]
  have hle :=
    Stacks.AlgebraicGeometry.FibreDimension.topologicalKrullDim_le_of_isInducing_of_range_subset
      (c.fiberι y).isEmbedding.isInducing hsub
  rw [← IsHomeomorph.topologicalKrullDim_eq _ (S.X_to_R.fiberHomeo (pY y)).isHomeomorph] at hle
  refine hle.trans (S.toRegularModelSituation.relativeDimension_model (pY y)
    ⟨(S.X_to_R.fiberHomeo (pY y)).symm ⟨c.fiberι y x, hsub ⟨x, rfl⟩⟩⟩).2.le

variable {Y₀ : Scheme.{u}} {g₀ : Y₀ ⟶ Spec (.of S.k)} {c₀ : S.specialFiber ⟶ Y₀}

/-- The special fibre contraction of a stable contraction is proper. -/
private theorem isProper_of_isStableContraction
    (hc₀ : Stacks.Curves.StableModel.IsStableContraction S.specialFiberToSpec g₀ c₀) :
    IsProper c₀ := by
  have : IsProper g₀ := hc₀.isProper
  have : IsProper (c₀ ≫ g₀) := by rw [hc₀.comp_eq]; infer_instance
  exact IsProper.of_comp c₀ g₀

/-- **A stable contraction of the special fibre is acyclic**: `Rⁱc₀_*𝒪_{X_k} = 0` for `i > 0`, for
`i = 1` by definition and for `i ≥ 2` because the fibres of `c₀` lie in the curve `X_k`. -/
theorem isZero_rightDerived_unit_of_isStableContraction
    (hc₀ : Stacks.Curves.StableModel.IsStableContraction S.specialFiberToSpec g₀ c₀) (i : ℕ)
    (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward c₀).rightDerived i).obj
      (SheafOfModules.unit S.specialFiber.ringCatSheaf)) := by
  have : IsProper c₀ := S.isProper_of_isStableContraction hc₀
  rcases (show i = 1 ∨ 1 < i by omega) with rfl | h
  · exact hc₀.isZero_rightDerived_one
  · refine isZero_rightDerived_unit_of_fiber_dim_le_one c₀ (fun y => ?_) i h
    -- the fibre embeds into the source
    exact ((c₀.fiberι y).isEmbedding.isInducing.topologicalKrullDim_le).trans
      (S.toRegularModelSituation.topologicalKrullDim_specialFiber S.nonempty_specialFiber).le

/-- **`R¹(c₀ ≫ h)_*𝒪_{X_k} = 0` for a stable contraction `c₀` followed by a finite `h`**: by Leray
for the acyclic first factor `R¹(c₀ ≫ h)_*𝒪 ≅ R¹h_*𝒪_{Y₀}`, which vanishes as `h` is affine. -/
theorem isZero_rightDerived_one_comp_of_isStableContraction
    (hc₀ : Stacks.Curves.StableModel.IsStableContraction S.specialFiberToSpec g₀ c₀)
    {T : Scheme.{u}} (h : Y₀ ⟶ T) [IsAffineHom h] :
    IsZero (((Scheme.Modules.pushforward (c₀ ≫ h)).rightDerived 1).obj
      (SheafOfModules.unit S.specialFiber.ringCatSheaf)) := by
  have : IsProper g₀ := hc₀.isProper
  have : IsProper c₀ := S.isProper_of_isStableContraction hc₀
  have : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace g₀
  exact (isZero_rightDerived_unit_of_isAffineHom h 1 one_pos).of_iso
    (Stacks.Curves.StableModel.rightDerivedCompUnitIso c₀ h hc₀.isIso_unitToPushforwardObjUnit
      (S.isZero_rightDerived_unit_of_isStableContraction hc₀) 1)

/-- **The fibres of the contraction have no first cohomology.** -/
theorem isZero_firstCohomologyStructureSheaf_fiber
    (hc₀ : Stacks.Curves.StableModel.IsStableContraction S.specialFiberToSpec g₀ c₀)
    {Y : Scheme.{u}} (pY : Y ⟶ Spec (.of S.R)) (c : S.X ⟶ Y)
    (hc : c ≫ pY = S.X_to_R) [IsProper c]
    (h : Y₀ ⟶ pullback pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))) [IsFinite h]
    (hh : c₀ ≫ h = S.specialFiberMap pY c hc)
    (hgen : IsIso (S.genericFiberMap pY c hc)) (y : Y) :
    IsZero (firstCohomologyStructureSheaf (c.fiber y)) := by
  have hdim := S.topologicalKrullDim_fiber_le_one pY c hc y
  have hy : pY y ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) ∨
      pY y ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))) := by
    by_cases hmem : pY y ∈ (((Spec (.of S.R)).basicOpen ((Scheme.ΓSpecIso (.of S.R)).inv S.π) :
        (Spec (.of S.R)).Opens) : Set ↥(Spec (.of S.R)))
    · left
      rw [← S.toRegularModelSituation.coe_basicOpen_spec_eq_range S.uniformizer]
      exact hmem
    · right
      rw [← S.toRegularModelSituation.compl_coe_basicOpen_spec_eq_range S.uniformizer]
      exact hmem
  rcases hy with hy | hy
  · have sq : IsPullback (pullback.fst S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))))
        (S.genericFiberMap pY c hc) c
        (pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))) :=
      isPullback_pullbackMap _ _ _ hc _ (by rw [Category.comp_id, hc]) (by simp)
    have := hgen
    have : IsIso (pullback.snd c
        (pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))))) := by
      rw [← sq.isoPullback_inv_snd]
      infer_instance
    refine isZero_firstCohomologyStructureSheaf_fiber_of_isZero_firstDirectImage_baseChange c y
      hdim (pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))) ?_
      ((isZero_firstDirectImageStructureSheaf_iff _).2
        (isZero_rightDerived_unit_of_isAffineHom _ 1 one_pos))
    rw [Scheme.Pullback.range_fst]
    exact hy
  · have sq : IsPullback S.specialFiberι (S.specialFiberMap pY c hc) c
        (pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))) :=
      isPullback_pullbackMap _ _ _ hc _ (by rw [Category.comp_id, hc]) (by simp)
    refine isZero_firstCohomologyStructureSheaf_fiber_of_isZero_firstDirectImage_baseChange c y
      hdim (pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))) ?_
      ((isZero_firstDirectImageStructureSheaf_iff _).2 ?_)
    · rw [Scheme.Pullback.range_fst]
      exact hy
    · have heq : pullback.snd c
          (pullback.fst pY (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))) =
          sq.isoPullback.inv ≫ c₀ ≫ h := by rw [hh, sq.isoPullback_inv_snd]
      rw [heq]
      exact isZero_rightDerived_unit_iso_comp _ _ 1
        (S.isZero_rightDerived_one_comp_of_isStableContraction hc₀ h)

end Stacks.Models.RegularProperModelSituation

end
