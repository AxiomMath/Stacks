module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionOpenPart
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionRigEtale

/-!
# The comparison morphism `X'' ⟶ X'` over `U'` and on completions

In the situation of **Stacks 0GHC** let `h : X'' ⟶ X` be the algebraization over `X` of
`X_{/T} ×_{a, W, g} X'_{/T'} ⟶ X_{/T}` and `x'' : X'' ⟶ X'` the comparison morphism
(`AlgebraicGeometry.Artin.ContractionSituation.modificationHom`). This file proves the three
properties of `x''` that Stacks 0GDR over `X'` needs in order to invert it:

* `|x''|⁻¹ T' = |h|⁻¹ T`;
* `x''` is an isomorphism over `U'`;
* the completion of `x''` along `T'` is the isomorphism
  `X''_{/T''} ≅ X_{/T} ×_W X'_{/T'} ≅ X'_{/T'}`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.preimage_T'_modificationHom`.
* `AlgebraicGeometry.Artin.ContractionSituation.isIso_pullback_snd_modificationHom`.

## References

* [Stacks Project, Tag 0GDR](https://stacks.math.columbia.edu/tag/0GDR)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ContractionSolutionModificationIso
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_ContractionSolutionModificationIso
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_ContractionSolutionModificationIso.has_limit _

/-- Pullbacks of fppf sheaves in `Type (u + 1)` on `BigFppfOver B S hS`: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_sheaf_ContractionSolutionModificationIso
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks (Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) := by
  set_option synthInstance.maxHeartbeats 400000 in infer_instance

local instance (priority := high) hasLimit_cospan_sheaf_ContractionSolutionModificationIso
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)
    {hX : IsAlgebraicSpace B S hS X}
    {hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)}
    (A : Algebraization c α hX hft)

/-- **`|x''|⁻¹ T' = |h|⁻¹ T`.** Tested at a field-valued point `ξ : Spec K ⟶ X''`: if `ξ ∘ h` meets
`T`, the closed subset of its triple is all of `Spec K` and `x'' ∘ ξ` lands in `T'` by the
completion property of `x''`; otherwise that closed subset is empty and `x'' ∘ ξ` lands in `U'`
by the restriction property. -/
theorem preimage_T'_modificationHom :
    Space.pointsMap B S hS A.Y (modificationHom c α A) ⁻¹' c.T' =
      Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α := by
  ext p
  induction p using Quot.ind with | _ q =>
  let V := q.locallyNoetherianObject B S hS
  let ξ : yoneda.obj V.obj ⟶ A.Y := yonedaEquiv.symm q.value
  let w : Space.points B S hS (yoneda.obj V.obj) :=
    (Space.FieldValuedPoint.tautological B S hS q).class B S hS (yoneda.obj q.siteObject)
  have hq : q.class B S hS A.Y = Space.pointsMap B S hS _ ξ w :=
    (Space.FieldValuedPoint.pointsMap_class_tautological B S hS q).symm
  show Space.pointsMap B S hS A.Y (modificationHom c α A) (q.class B S hS A.Y) ∈ c.T' ↔
    Space.pointsMap B S hS A.Y A.h (q.class B S hS A.Y) ∈ contractedLocus c α
  have e1 : Space.pointsMap B S hS A.Y (modificationHom c α A)
      (Space.pointsMap B S hS _ ξ w) =
        Space.pointsMap B S hS _ (modificationMor c α A V ξ) w := by
    rw [← comp_modificationHom c α A V ξ, Space.pointsMap_comp]; rfl
  have e2 : Space.pointsMap B S hS A.Y A.h (Space.pointsMap B S hS _ ξ w) =
      Space.pointsMap B S hS _ (ξ ≫ A.h) w := by
    rw [Space.pointsMap_comp]; rfl
  rw [hq, e1, e2]
  have hZ : (tripleOfMor c α V (ξ ≫ A.h)).Z =
      Space.pointsMap B S hS _ (ξ ≫ A.h) ⁻¹' contractedLocus c α :=
    (preimage_contractedLocus c α V (ξ ≫ A.h)).symm
  constructor
  · intro hy
    by_contra hw
    have hwZ : w ∈ (tripleOfMor c α V (ξ ≫ A.h)).Zᶜ := by rwa [hZ]
    obtain ⟨w', hw'⟩ : w ∈ Set.range (Space.pointsMap B S hS _
        (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj)
          (tripleOfMor c α V (ξ ≫ A.h)).Zᶜ).ι) := by
      rwa [Space.range_pointsMap_ι_openSubspaceOfPoints]
    have hT : Space.pointsMap B S hS _ (modificationMor c α A V ξ) w ∈ c.T'ᶜ := by
      have e3 : Space.pointsMap B S hS _ (modificationMor c α A V ξ) w =
          Space.pointsMap B S hS _ c.U'.ι (Space.pointsMap B S hS _
            (tripleOfMor c α V (ξ ≫ A.h)).u w') := by
        rw [← hw']
        simpa only [Space.pointsMap_comp, Function.comp_apply] using
          congrArg (fun m => Space.pointsMap B S hS _ m w') (modificationMor_restrict c α A V ξ)
      rw [e3, ← c.range_pointsMap_ι_U']
      exact ⟨_, rfl⟩
    exact hT hy
  · intro hw
    have hwZ : w ∈ (tripleOfMor c α V (ξ ≫ A.h)).Z := by rwa [hZ]
    exact image_subset_of_completion_comp_eq c.isAlgebraicSpace_X' _ _
      (modificationMor_completion c α A V ξ) ⟨w, hwZ, rfl⟩

/-- The section of `X` matched by `α` with the triple of a section is that section. -/
theorem eq_of_tripleOfMor_eq (V : LocallyNoetherianOver B S hS) (ζ : yoneda.obj V.obj ⟶ X)
    (t : Triple c V.obj) (h : tripleOfMor c α V ζ = t) :
    ζ = yonedaEquiv.symm (α.hom.app (op V) t).down := by
  rw [← h, Equiv.eq_symm_apply]
  unfold tripleOfMor
  have h2 := ConcreteCategory.congr_hom (α.inv_hom_id_app (op V))
    (show (morOnLocallyNoetherian B S hS X).obj (op V) from ULift.up (yonedaEquiv ζ))
  exact (congrArg ULift.down h2).symm

/-- The open part `X'' ∖ |x''|⁻¹ T'` of `X''`. -/
noncomputable abbrev modificationOpen : Subfunctor A.Y :=
  Space.openSubspaceOfPoints B S hS A.Y
    (Space.pointsMap B S hS A.Y (modificationHom c α A) ⁻¹' c.T'ᶜ)

/-- The open part `X'' ∖ |h|⁻¹ T` of `X''`. -/
noncomputable abbrev modificationOpenH : Subfunctor A.Y :=
  Space.openSubspaceOfPoints B S hS A.Y (Space.pointsMap B S hS A.Y A.h ⁻¹' (contractedLocus c α)ᶜ)

/-- The points of `X''` outside `|x''|⁻¹ T'` lie outside `|h|⁻¹ T`. -/
theorem modificationOpen_subset :
    Space.pointsMap B S hS A.Y (modificationHom c α A) ⁻¹' c.T'ᶜ ⊆
      Space.pointsMap B S hS A.Y (𝟙 _) ⁻¹'
        (Space.pointsMap B S hS A.Y A.h ⁻¹' (contractedLocus c α)ᶜ) := by
  rw [Space.pointsMap_id, Set.preimage_id, Set.preimage_compl, Set.preimage_compl,
    preimage_T'_modificationHom]

/-- The points of `X''` outside `|h|⁻¹ T` lie outside `|x''|⁻¹ T'`. -/
theorem modificationOpenH_subset :
    Space.pointsMap B S hS A.Y A.h ⁻¹' (contractedLocus c α)ᶜ ⊆
      Space.pointsMap B S hS A.Y (𝟙 _) ⁻¹'
        (Space.pointsMap B S hS A.Y (modificationHom c α A) ⁻¹' c.T'ᶜ) := by
  rw [Space.pointsMap_id, Set.preimage_id, Set.preimage_compl, Set.preimage_compl,
    preimage_T'_modificationHom]

/-- The candidate inverse `U' ⟶ X'' ∖ |x''|⁻¹ T'` of the restriction of `x''`: the morphism
`U' ⟶ X ∖ T` of the empty triples followed by the inverse of `X'' ∖ |h|⁻¹ T ≅ X ∖ T`. -/
noncomputable def modificationOpenInv :
    c.U'.toFunctor ⟶ (modificationOpen c α A).toFunctor :=
  haveI := Space.isIso_openComplementRestriction B S hS A.h (contractedLocus c α)
    A.isIso_pullback_snd_h
  openPartHom c α hX hft ≫ inv (Space.openComplementRestriction B S hS A.h (contractedLocus c α)) ≫
    Space.openSubspaceOfPointsRestrict B S hS (𝟙 _) _ _ (modificationOpenH_subset c α A)

/-- The restriction `X'' ∖ |h|⁻¹ T ≅ X ∖ T` of `h` is an isomorphism. -/
private theorem isIso_openComplementRestriction_h :
    IsIso (Space.openComplementRestriction B S hS A.h (contractedLocus c α)) :=
  Space.isIso_openComplementRestriction B S hS A.h (contractedLocus c α) A.isIso_pullback_snd_h

/-- `X'' ∖ |h|⁻¹ T ⟶ X'' ⟶ X` is `X'' ∖ |h|⁻¹ T ⟶ X ∖ T ⟶ X`. -/
private theorem modificationOpenH_ι_h :
    (modificationOpenH c α A).ι ≫ A.h =
      Space.openComplementRestriction B S hS A.h (contractedLocus c α) ≫
        (Space.openSubspaceOfPoints B S hS X (contractedLocus c α)ᶜ).ι :=
  (Space.isPullback_openComplementRestriction B S hS A.h (contractedLocus c α)).w

/-- The composite `U' ⟶ X'' ∖ T'' ⟶ X` is `u ↦ α(∅, u, ∅ ⟶ W)`. -/
theorem modificationOpenInv_ι_h (V : LocallyNoetherianOver B S hS)
    (u : yoneda.obj V.obj ⟶ c.U'.toFunctor) :
    u ≫ modificationOpenInv c α A ≫ (modificationOpen c α A).ι ≫ A.h =
      yonedaEquiv.symm (α.hom.app (op V) (c.emptyTriple V.obj u)).down := by
  have := isIso_openComplementRestriction_h c α A
  rw [← comp_openPartHom_ι c α hX hft V u]
  simp only [modificationOpenInv, Category.assoc]
  congr 2
  rw [← Category.assoc (Space.openSubspaceOfPointsRestrict B S hS (𝟙 _) _ _ _),
    Space.openSubspaceOfPointsRestrict_comp_ι, Category.comp_id, modificationOpenH_ι_h,
    IsIso.inv_hom_id_assoc]

/-- The section `ξ ≫ f` of the Yoneda embedding of `ξ = yonedaEquiv.symm x` evaluated at the
identity is `f x`. -/
private theorem yonedaEquiv_symm_comp_app_id {V : LocallyNoetherianOver B S hS}
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : F.obj (op V.obj)) (f : F ⟶ G) :
    (yonedaEquiv.symm x ≫ f).app (op V.obj) (𝟙 V.obj) = f.app _ x := by
  rw [← yonedaEquiv_apply, yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- `X'' ∖ |x''|⁻¹ T'` is an open subspace of `X''`. -/
theorem isOpenSubspace_modificationOpen :
    Space.IsOpenSubspace B S hS (modificationOpen c α A) :=
  Space.isOpenSubspace_openSubspaceOfPoints B S hS A.isAlgebraicSpace_Y _
    (c.isClosed_T'.isOpen_compl.preimage (Space.continuous_pointsMap B S hS _))

/-- The restriction `X'' ∖ |x''|⁻¹T' ⟶ U'` of `x''`. -/
noncomputable abbrev modificationOpenRestr :
    (modificationOpen c α A).toFunctor ⟶ c.U'.toFunctor :=
  Space.openComplementRestriction B S hS (modificationHom c α A) c.T'

/-- The restriction of `x''` followed by `U' ⟶ X'` is the inclusion of `X'' ∖ |x''|⁻¹ T'`
followed by `x''`. -/
theorem modificationOpenRestr_ι :
    modificationOpenRestr c α A ≫ c.U'.ι = (modificationOpen c α A).ι ≫ modificationHom c α A :=
  (Space.isPullback_openComplementRestriction B S hS (modificationHom c α A) c.T').w.symm

/-- On a morphism `u : V ⟶ U'` from a locally Noetherian scheme, the triple of
`u ∘ (U' ⟶ X'') ∘ h` is the empty triple of `u`. -/
theorem tripleOfMor_modificationOpenInv (V : LocallyNoetherianOver B S hS)
    (u : yoneda.obj V.obj ⟶ c.U'.toFunctor) (ξ : yoneda.obj V.obj ⟶ A.Y)
    (hξ : u ≫ modificationOpenInv c α A ≫ (modificationOpen c α A).ι = ξ) :
    tripleOfMor c α V (ξ ≫ A.h) = c.emptyTriple V.obj u := by
  rw [← hξ, Category.assoc, Category.assoc, modificationOpenInv_ι_h,
    tripleOfMor_yonedaEquiv_symm_hom_app]

/-- `U' ⟶ X'' ∖ T'' ⟶ U'` is the identity. -/
theorem modificationOpenInv_restr :
    modificationOpenInv c α A ≫ modificationOpenRestr c α A = 𝟙 _ := by
  rw [← cancel_mono c.U'.ι, Category.assoc, modificationOpenRestr_ι, Category.id_comp]
  refine hom_ext_of_locallyNoetherian c c.isOpenSubspace_U'.1
    (isLocallyOfFiniteType_terminal_of_isOpenSubspace c.isAlgebraicSpace_X'
      c.isLocallyOfFiniteType_X' c.isOpenSubspace_U')
    c.isAlgebraicSpace_X' c.isLocallyOfFiniteType_X' (fun V u => ?_)
  obtain ⟨ξ, hξ⟩ : ∃ ξ, u ≫ modificationOpenInv c α A ≫ (modificationOpen c α A).ι = ξ :=
    ⟨_, rfl⟩
  rw [← Category.assoc (modificationOpenInv c α A), ← Category.assoc, hξ,
    comp_modificationHom]
  have htr := tripleOfMor_modificationOpenInv c α A V u ξ hξ
  have h1 := modificationMor_restrict c α A V ξ
  rw [htr] at h1
  have := epi_ι_openSubspaceOfPoints_of_eq_univ
    ((c.emptyTriple V.obj u).Z)ᶜ (by rw [emptyTriple_Z, Set.compl_empty])
  rw [← cancel_epi (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj)
    (c.emptyTriple V.obj u).Zᶜ).ι, h1]
  exact Category.assoc _ _ _

/-- `X'' ∖ T'' ⟶ U' ⟶ X'' ∖ T''` is the identity. -/
theorem modificationOpenRestr_inv :
    modificationOpenRestr c α A ≫ modificationOpenInv c α A = 𝟙 _ := by
  have := isIso_openComplementRestriction_h c α A
  rw [← cancel_mono (modificationOpen c α A).ι, Category.id_comp]
  refine hom_ext_of_locallyNoetherian c (isOpenSubspace_modificationOpen c α A).1
    (isLocallyOfFiniteType_terminal_of_isOpenSubspace A.isAlgebraicSpace_Y
      A.isLocallyOfFiniteType_Y (isOpenSubspace_modificationOpen c α A))
    A.isAlgebraicSpace_Y A.isLocallyOfFiniteType_Y (fun V o => ?_)
  set u := o ≫ modificationOpenRestr c α A with hu
  set ξ := o ≫ (modificationOpen c α A).ι with hξdef
  have hZ : (tripleOfMor c α V (ξ ≫ A.h)).Z = ∅ := by
    rw [← preimage_contractedLocus]
    ext z
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro hz
    have hmem : Space.pointsMap B S hS _ ξ z ∈
        Space.pointsMap B S hS A.Y (modificationHom c α A) ⁻¹' c.T'ᶜ := by
      rw [hξdef, Space.pointsMap_comp, Function.comp_apply,
        ← Space.range_pointsMap_ι_openSubspaceOfPoints B S hS
          (Space.pointsMap B S hS A.Y (modificationHom c α A) ⁻¹' c.T'ᶜ)]
      exact ⟨_, rfl⟩
    rw [Set.preimage_compl, preimage_T'_modificationHom] at hmem
    rw [Space.pointsMap_comp, Function.comp_apply] at hz
    exact hmem hz
  have hu' : (Space.openSubspaceOfPoints B S hS (yoneda.obj V.obj)
      (tripleOfMor c α V (ξ ≫ A.h)).Zᶜ).ι ≫ u = (tripleOfMor c α V (ξ ≫ A.h)).u := by
    rw [← cancel_mono c.U'.ι, ← modificationMor_restrict c α A V ξ, ← comp_modificationHom,
      hu, hξdef]
    simp only [Category.assoc, modificationOpenRestr_ι]
  have htr := Triple.eq_emptyTriple c _ u hZ hu'
  have hh : (o ≫ modificationOpenRestr c α A ≫ modificationOpenInv c α A ≫
      (modificationOpen c α A).ι) ≫ A.h = (o ≫ (modificationOpen c α A).ι) ≫ A.h := by
    rw [Category.assoc, Category.assoc, Category.assoc, ← Category.assoc o,
      modificationOpenInv_ι_h c α A V u]
    rw [← htr, ← eq_of_tripleOfMor_eq c α V (ξ ≫ A.h) _ rfl]
  have e1 : (modificationOpen c α A).ι = Space.openSubspaceOfPointsRestrict B S hS (𝟙 _) _ _
      (modificationOpen_subset c α A) ≫ (modificationOpenH c α A).ι := by
    rw [Space.openSubspaceOfPointsRestrict_comp_ι, Category.comp_id]
  rw [e1] at hh
  simp only [Category.assoc, modificationOpenH_ι_h] at hh
  have : IsIso (Space.openComplementRestriction B S hS A.h (contractedLocus c α)) :=
    isIso_openComplementRestriction_h c α A
  simp only [← Category.assoc] at hh
  replace hh := (IsIso.mono_of_iso
    (Space.openComplementRestriction B S hS A.h (contractedLocus c α))).right_cancellation _ _
    ((Subfunctor.instMonoFunctorTypeι _).right_cancellation _ _ hh)
  rw [e1, ← Category.assoc, ← Category.assoc, ← Category.assoc, hh, Category.assoc, ← e1,
    hξdef]

/-- **`x''` is an isomorphism over `U'`.** -/
theorem isIso_pullback_snd_modificationHom :
    IsIso (pullback.snd (modificationHom c α A)
      (Space.openSubspaceOfPoints B S hS c.X' c.T'ᶜ).ι) := by
  have hsq := Space.isPullback_openComplementRestriction B S hS (modificationHom c α A) c.T'
  have : IsIso (modificationOpenRestr c α A) :=
    ⟨⟨modificationOpenInv c α A, modificationOpenRestr_inv c α A,
      modificationOpenInv_restr c α A⟩⟩
  have e : pullback.snd (modificationHom c α A)
      (Space.openSubspaceOfPoints B S hS c.X' c.T'ᶜ).ι =
        hsq.isoPullback.inv ≫ modificationOpenRestr c α A :=
    ((Iso.inv_comp_eq _).mpr hsq.isoPullback_hom_snd.symm).symm
  have h' : IsIso (C := (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (X := (modificationOpen c α A).toFunctor)
      (Y := (Space.openSubspaceOfPoints B S hS c.X' c.T'ᶜ).toFunctor)
      (modificationOpenRestr c α A) := this
  rw [e]
  exact IsIso.comp_isIso' inferInstance h'

/-- `|h|⁻¹ T` is contained in `|x''|⁻¹ T'`. -/
theorem contractedLocus_preimage_subset :
    Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α ⊆
      Space.pointsMap B S hS A.Y (modificationHom c α A) ⁻¹' c.T' := by
  rw [preimage_T'_modificationHom]

/-- **The completion of `x''` along `T'` is
`X''_{/T''} ≅ X_{/T} ×_{a, W, g} X'_{/T'} ⟶ X'_{/T'}`.**
Both sides are morphisms between limit preserving fppf sheaves, so they may be compared on
locally Noetherian schemes `N` (Stacks 0GE3); there a section of `X''_{/T''}` is a morphism
`ξ : N ⟶ X''` with image in `T''`, and both sides send it to `x'' ∘ ξ`, by the completion
property of `x''` read at the identity of `N`. -/
theorem completionSheafRestrict_modificationHom :
    Space.completionSheafRestrict B S hS (modificationHom c α A)
        (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α) c.T'
        (contractedLocus_preimage_subset c α A) =
      A.eLeft ≫ pullback.fst c.g (completionSheafIsoWExt c α hX hft).hom := by
  have := c.isLocallyNoetherian_base
  have hT'' : IsClosed (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α) :=
    (isClosed_contractedLocus c α hX hft).preimage (Space.continuous_pointsMap B S hS _)
  obtain ⟨_, _, hu⟩ := ExtendingFunctors.existsUnique_hom_whiskerLeft_eq_bigFppfOver B hS
    (Space.completionSheaf B S hS A.Y _).property
    (Space.limitPreserving_completionSheaf B S hS A.isAlgebraicSpace_Y A.isLocallyOfFiniteType_Y
      hT'')
    (Space.completionSheaf B S hS c.X' c.T').property
    (Space.limitPreserving_completionSheaf B S hS c.isAlgebraicSpace_X' c.isLocallyOfFiniteType_X'
      c.isClosed_T')
    (Functor.whiskerLeft (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op
      (Space.completionSheafRestrict B S hS (modificationHom c α A)
        (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α) c.T'
        (contractedLocus_preimage_subset c α A)).hom)
  apply Sheaf.hom_ext
  refine ((hu _ rfl).trans (hu _ ?_).symm)
  ext N z
  let e := Space.completionSheafIsoSubfunctor B S hS A.isAlgebraicSpace_Y.isSheaf
    (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α)
  have hw : FormalSpace.presheafSection B S hS (e.hom.app (op N.unop.obj) z).1.down
      (e.hom.app (op N.unop.obj) z).2 = z :=
    congrArg (fun φ => φ.app (op N.unop.obj) z) e.hom_inv_id
  show (A.eLeft ≫ pullback.fst c.g (completionSheafIsoWExt c α hX hft).hom).hom.app
      (op N.unop.obj) z =
    (Space.completionSheafRestrict B S hS (modificationHom c α A) _ c.T' _).hom.app
      (op N.unop.obj) z
  have core : ∀ (x : A.Y.obj (op N.unop.obj)) (hx : Space.HasImageIn B S hS A.Y
      (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α) N.unop.obj x),
      (A.eLeft ≫ pullback.fst c.g (completionSheafIsoWExt c α hX hft).hom).hom.app
          (op N.unop.obj) (FormalSpace.presheafSection B S hS x hx) =
        (Space.completionSheafRestrict B S hS (modificationHom c α A) _ c.T'
          (contractedLocus_preimage_subset c α A)).hom.app (op N.unop.obj)
          (FormalSpace.presheafSection B S hS x hx) := by
    intro x hx
    have hx' : Space.HasImageIn B S hS c.X' c.T' N.unop.obj ((modificationHom c α A).app _ x) :=
      (FormalSpace.hasImageIn_preimage_pointsMap_iff B S hS _ _ _ x).1
        (fun p => contractedLocus_preimage_subset c α A (hx p))
    rw [FormalSpace.completionSheafRestrict_presheafSection B S hS _ _ _ _ _ hx hx']
    apply FormalSpace.injective_completionSheafInclusion_app B S hS c.T' N.unop.obj
    rw [FormalSpace.inclusion_presheafSection]
    let V : LocallyNoetherianOver B S hS := N.unop
    let ξ : yoneda.obj V.obj ⟶ A.Y := yonedaEquiv.symm x
    have hid : Space.HasImageIn B S hS (yoneda.obj V.obj) (tripleOfMor c α V (ξ ≫ A.h)).Z V.obj
        (𝟙 V.obj) := by
      rw [← preimage_contractedLocus]
      refine (FormalSpace.hasImageIn_preimage_pointsMap_iff B S hS _ _ _ _).2 ?_
      rw [yonedaEquiv_symm_comp_app_id]
      exact (FormalSpace.hasImageIn_preimage_pointsMap_iff B S hS _ _ _ x).1 hx
    have key := completionSheafInclusion_app_eq_of_comp_eq (modificationMor c α A V ξ) _
      (modificationMor_completion c α A V ξ) (𝟙 V.obj) hid
    have hy : (modificationMor c α A V ξ).app (op V.obj) (𝟙 V.obj) =
        (modificationHom c α A).app _ x := by
      rw [← comp_modificationHom c α A V ξ, yonedaEquiv_symm_comp_app_id]
    rw [hy] at key
    refine Eq.trans ?_ key
    have hξx : ξ.app (op V.obj) (𝟙 V.obj) = x := Equiv.apply_symm_apply yonedaEquiv x
    have pc : ∀ (a b : A.Y.obj (op V.obj)) (_ : a = b)
        (ha : Space.HasImageIn B S hS A.Y (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α)
          V.obj a)
        (hb : Space.HasImageIn B S hS A.Y (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α)
          V.obj b),
        FormalSpace.presheafSection B S hS a ha = FormalSpace.presheafSection B S hS b hb := by
      intro a b h _ _; subst h; rfl
    have hs : (modificationCompletion c α A V ξ).hom.app (op V.obj)
        (FormalSpace.presheafSection B S hS (𝟙 V.obj) hid) =
          (A.eLeft ≫ pullback.fst c.g (completionSheafIsoWExt c α hX hft).hom).hom.app (op V.obj)
            (FormalSpace.presheafSection B S hS x hx) := by
      have hx2 : Space.HasImageIn B S hS A.Y
          (Space.pointsMap B S hS A.Y A.h ⁻¹' contractedLocus c α) V.obj
          (ξ.app (op V.obj) (𝟙 V.obj)) := by rwa [hξx]
      show (A.eLeft ≫ pullback.fst c.g _).hom.app _
        ((Space.completionSheafRestrict B S hS ξ _ _ (tripleOfMor_Z_subset c α A V ξ)).hom.app _
          (FormalSpace.presheafSection B S hS (𝟙 V.obj) hid)) = _
      rw [FormalSpace.completionSheafRestrict_presheafSection B S hS _ _ _ _ _ hid hx2,
        pc _ _ hξx hx2 hx]
    rw [← hs]
  rw [← hw]
  exact core _ _

end AlgebraicGeometry.Artin.ContractionSituation

end
