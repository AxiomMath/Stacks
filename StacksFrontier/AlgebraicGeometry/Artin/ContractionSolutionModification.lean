module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionClosed
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionHomExtNoetherian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChangeAdic

/-!
# The algebraization over `X` of the contraction's formal modification

In the situation of Stacks 0GH8, recorded by
`AlgebraicGeometry.Artin.ContractionSituation`, let `X` be an algebraic space locally of finite
type over `S` carrying a functorial bijection `α : F(V) = Mor_S(V, X)` on locally Noetherian
schemes, as in Stacks 0GHC, and let `T ⊆ |X|` and `a : X_{/T} ≅ W` be the closed subset
`AlgebraicGeometry.Artin.ContractionSituation.contractedLocus` and the isomorphism
`AlgebraicGeometry.Artin.ContractionSituation.completionSheafIsoWExt`. The base change
`X_{/T} ×_{a, W, g} X'_{/T'} ⟶ X_{/T}` of `g` along `a` is a formal modification (Stacks 0GDN),
so by Stacks 0GDU there is an algebraic space `X''` with a proper morphism `h : X'' ⟶ X` which is
an isomorphism over `X ∖ T` and whose completion along `T` is that formal modification. For a
morphism `ξ : V ⟶ X` from a locally Noetherian scheme, the third component of the triple matching
`ξ` is the completion of `ξ` along `|ξ|⁻¹T` followed by `a`.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.contractionModification`: the formal
  modification `X_{/T} ×_{a, W, g} X'_{/T'} ⟶ X_{/T}`.
* `AlgebraicGeometry.Artin.ContractionSituation.Algebraization`: the data `(X'', h, e)` of
  Stacks 0GDU for that formal modification.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.isLocallyNoetherian_of_isLocallyOfFiniteType_base`:
  `X` is locally Noetherian.
* `AlgebraicGeometry.Artin.ContractionSituation.isFormalModification_contractionModification`:
  the base change of `g` along `a` is a formal modification.
* `AlgebraicGeometry.Artin.ContractionSituation.nonempty_algebraization`: the formal modification
  `X_{/T} ×_{a, W, g} X'_{/T'} ⟶ X_{/T}` has an algebraization.
* `AlgebraicGeometry.Artin.ContractionSituation.tripleOfMor_xhat`: the third component of the
  triple matching `ξ : V ⟶ X` is the completion of `ξ` followed by `a`.

## References

* [Stacks Project, Tag 0GDN](https://stacks.math.columbia.edu/tag/0GDN)
* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_ContractionSolutionModification
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_ContractionSolutionModification
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_ContractionSolutionModification.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` instance search for fppf sheaves of types on `BigFppfOver B S hS`
/-- Pullbacks of fppf sheaves in `Type (u + 1)` on `BigFppfOver B S hS`: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_sheaf_ContractionSolutionModification
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks (Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) := by
  infer_instance

local instance (priority := high) hasLimit_cospan_sheaf_ContractionSolutionModification
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)

include c in
/-- An algebraic space locally of finite type over the locally Noetherian base `S` of the
situation is locally Noetherian. -/
theorem isLocallyNoetherian_of_isLocallyOfFiniteType_base
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    Space.IsLocallyNoetherian B S hS X :=
  fun V q hq => by
    have := c.isLocallyNoetherian_base
    have h := hq V (yoneda.map (𝟙 V)) (Space.presheaf_yoneda_map_id_etale B S hS _)
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact Space.isLocallyNoetherian_of_presheafEtale B S hS hft V q h

/-- The formal modification `X_{/T} ×_{a, W, g} X'_{/T'} ⟶ X_{/T}`: the base change of `g` along
the isomorphism `a : X_{/T} ≅ W`. -/
noncomputable def contractionModification (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    pullback c.g (completionSheafIsoWExt c α hX hft).hom ⟶
      Space.completionSheaf B S hS X (contractedLocus c α) :=
  pullback.snd c.g (completionSheafIsoWExt c α hX hft).hom

/-- The base change of the formal modification `g` along the isomorphism `a : X_{/T} ≅ W` is a
formal modification. -/
theorem isFormalModification_contractionModification (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    FormalSpace.IsFormalModification B S hS (contractionModification c α hX hft) :=
  FormalSpace.isFormalModification_pullback_snd_of_isAdicMorphism B S hS _ _
    (FormalSpace.isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hX
      (isLocallyNoetherian_of_isLocallyOfFiniteType_base c hft) _
      (isClosed_contractedLocus c α hX hft))
    (FormalSpace.isAdicMorphism_of_isIso B S hS _) c.isFormalModification_g

/-- An algebraization of the formal modification `X_{/T} ×_{a, W, g} X'_{/T'} ⟶ X_{/T}`, as in
Stacks 0GDU: an algebraic space `X''`, a proper morphism
`h : X'' ⟶ X` which is an isomorphism over `X ∖ T`, and an isomorphism over `X_{/T}` between
the completion of `h` along `T` and that formal modification. -/
structure Algebraization (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) where
  /-- The algebraic space `X''`. -/
  Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- `X''` is an algebraic space. -/
  isAlgebraicSpace_Y : IsAlgebraicSpace B S hS Y
  /-- The morphism `h : X'' ⟶ X`. -/
  h : Y ⟶ X
  /-- `h` is proper. -/
  isProper_h : Space.IsProper B S hS h
  /-- `h` is an isomorphism over `X ∖ T`. -/
  isIso_pullback_snd_h :
    IsIso (pullback.snd h (Space.openSubspaceOfPoints B S hS X (contractedLocus c α)ᶜ).ι)
  /-- The completion of `h` along `T` is the formal modification
  `X_{/T} ×_{a, W, g} X'_{/T'} ⟶ X_{/T}`. -/
  e : (Space.completionOverFunctor B S hS (contractedLocus c α)).obj (Over.mk h) ≅
    Over.mk (contractionModification c α hX hft)

/-- The formal modification `X_{/T} ×_{a, W, g} X'_{/T'} ⟶ X_{/T}` has an algebraization: an
algebraic space `X''` with a proper morphism `h : X'' ⟶ X` which is an isomorphism over `X ∖ T`
and whose completion along `T` is that formal modification. -/
theorem nonempty_algebraization (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    Nonempty (Algebraization c α hX hft) := by
  obtain ⟨Y, hY, h, hp, hU, ⟨e⟩⟩ :=
    FormalSpace.exists_isProper_completion_iso_of_isFormalModification hX
      (isLocallyNoetherian_of_isLocallyOfFiniteType_base c hft) _
      (isClosed_contractedLocus c α hX hft)
      (isFormalModification_contractionModification c α hX hft)
  exact ⟨⟨Y, hY, h, hp, hU, e⟩⟩

/-! ### The third component of the triple of a section of `X` -/

/-- The third component of the triple matching `ξ : V ⟶ X` is the completion of `ξ` along
`Z = |ξ|⁻¹T` followed by `a : X_{/T} ≅ W`. -/
theorem tripleOfMor_xhat (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (V : LocallyNoetherianOver B S hS) (ξ : yoneda.obj V.obj ⟶ X) :
    (tripleOfMor c α V ξ).xhat =
      Space.completionSheafRestrict B S hS ξ (tripleOfMor c α V ξ).Z (contractedLocus c α)
        (preimage_contractedLocus c α V ξ).symm.subset ≫
        (completionSheafIsoWExt c α hX hft).hom := by
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V.obj) := V.property
  refine FormalSpace.completionSheaf_yoneda_hom_ext_of_isLocallyNoetherian B S hS
    (tripleOfMor c α V ξ).isClosed_Z (fun N hN x hx => ?_)
  let t := tripleOfMor c α V ξ
  let N' : LocallyNoetherianOver B S hS := ⟨N, hN⟩
  let φ : N' ⟶ V := ObjectProperty.homMk x
  have hyx : yonedaEquiv.symm x = yoneda.map x := by
    rw [Equiv.symm_apply_eq, yonedaEquiv_yoneda_map]
  have h := (Space.hasImageIn_iff_range_subset B S hS t.Z N x).mp hx
  rw [hyx] at h
  have hZ1 : (mapTriple c x t).Z = Set.univ := by
    rw [mapTriple_Z_eq_preimage, Set.eq_univ_iff_forall]
    exact fun w => h ⟨w, rfl⟩
  have hy : Space.HasImageIn B S hS X (contractedLocus c α) N (ξ.app (op N) x) := by
    have hxi : yonedaEquiv.symm (ξ.app (op N) x) = yoneda.map x ≫ ξ := by
      rw [Equiv.symm_apply_eq, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    rw [Space.hasImageIn_iff_range_subset, hxi]
    rintro _ ⟨w, rfl⟩
    rw [Space.pointsMap_comp, Function.comp_apply]
    have hw := h ⟨w, rfl⟩
    rwa [← preimage_contractedLocus c α V ξ] at hw
  have hL : t.xhat.hom.app (op N) (FormalSpace.presheafSection B S hS x hx) =
      wSection c (mapTriple c x t) hZ1 := by
    have hid : Space.HasImageIn B S hS (yoneda.obj N) (mapTriple c x t).Z N (𝟙 N) := by
      rw [hZ1]; exact Space.hasImageIn_univ B S hS (yoneda.obj N) N (𝟙 N)
    have hx' : Space.HasImageIn B S hS (yoneda.obj V.obj) t.Z N
        ((yoneda.map x).app (op N) (𝟙 N)) := by
      simpa using hx
    change _ = t.xhat.hom.app (op N) ((Space.completionSheafRestrict B S hS (yoneda.map x)
      (mapTriple c x t).Z t.Z (mapTriple_Z_eq_preimage c x t).subset).hom.app (op N)
        (FormalSpace.presheafSection B S hS (𝟙 N) hid))
    rw [FormalSpace.completionSheafRestrict_presheafSection B S hS _ _ _ _ _ hid hx']
    congr 2
  have hR : (completionSheafIsoWExt c α hX hft).hom.hom.app (op N)
      (FormalSpace.presheafSection B S hS (ξ.app (op N) x) hy) =
        completionSectionToW c α N' (ξ.app (op N) x) hy := by
    have h := congrArg (fun e => e.hom.app (op N') (FormalSpace.presheafSection B S hS
      (ξ.app (op N) x) hy)) (isoWhiskerLeft_completionSheafIsoWExt c α hX hft)
    refine h.trans ?_
    change (completionToW c α).app (op N') ((Space.completionSheafIsoSubfunctor B S hS hX.isSheaf
      (contractedLocus c α)).hom.app (op N) (FormalSpace.presheafSection B S hS _ hy)) = _
    have hsub : (Space.completionSheafIsoSubfunctor B S hS hX.isSheaf
        (contractedLocus c α)).hom.app (op N) (FormalSpace.presheafSection B S hS _ hy) =
          ⟨ULift.up (ξ.app (op N) x), hy⟩ := by
      have hP := Space.isSheaf_completionSubfunctor B S hS hX.isSheaf (contractedLocus c α)
      change (((BigFppfOver.topology B S hS).isoSheafify hP).hom ≫
        ((BigFppfOver.topology B S hS).isoSheafify hP).inv).app (op N)
          ⟨ULift.up (ξ.app (op N) x), hy⟩ = _
      rw [Iso.hom_inv_id]
      rfl
    rw [hsub]
    rfl
  have htr : tripleOfMor c α N' (yonedaEquiv.symm (ξ.app (op N) x)) = mapTriple c x t := by
    have h' := tripleOfMor_map c α φ (yonedaEquiv ξ)
    rwa [Equiv.symm_apply_apply,
      show X.map φ.hom.op (yonedaEquiv ξ) = ξ.app (op N) x from map_yonedaEquiv ξ x] at h'
  rw [hL]
  change _ = (completionSheafIsoWExt c α hX hft).hom.hom.app (op N)
    ((Space.completionSheafRestrict B S hS ξ t.Z (contractedLocus c α) _).hom.app (op N)
      (FormalSpace.presheafSection B S hS x hx))
  rw [FormalSpace.completionSheafRestrict_presheafSection B S hS _ _ _ _ _ hx hy, hR]
  exact wSection_congr c htr.symm _ _

end AlgebraicGeometry.Artin.ContractionSituation

end
