module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Conditions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic

/-!
# An algebraic space locally quasi-finite over a field is decent

Let `X` be an algebraic space over a scheme `S` isomorphic to the spectrum of a field, and assume
`X ⟶ S` is locally quasi-finite. Then `X` is decent: an affine étale chart `U` of `X` is a
scheme locally quasi-finite and quasi-compact over a one-point scheme, so it has finitely many
points, and so does `U ×_S U`, into which the self-intersection `U ×_X U` embeds. This is
condition `(γ)` of Stacks 03JX at every point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)

attribute [local instance] pointTopology

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this). -/
local instance hasPullbacks_presheaf_LocallyQuasiFiniteOverField :
    HasPullbacks ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_LocallyQuasiFiniteOverField
    {X Y Z : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site
/-- Binary products of presheaves on the big fppf site. -/
local instance hasBinaryProducts_presheaf_LocallyQuasiFiniteOverField :
    HasBinaryProducts ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site
/-- Small discrete limits of presheaves on the big fppf site. -/
local instance hasLimitsOfShape_discrete_presheaf_LocallyQuasiFiniteOverField (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver C S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- The source of a quasi-compact, locally quasi-finite morphism to a finite scheme is finite. -/
private theorem finite_of_quasiCompact_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [LocallyQuasiFinite f] [Finite Y] : Finite X := by
  have h := f.finite_preimage (Set.finite_univ (α := Y))
  rwa [Set.preimage_univ, Set.finite_univ_iff] at h

/-- An object of the big fppf site whose underlying scheme is affine and locally quasi-finite
over the spectrum of a field has finitely many points. -/
theorem finite_of_locallyQuasiFinite_of_isAffine {k : Type u} [Field k]
    (e : S ≅ Spec (.of k)) (U : BigFppfOver C S hS)
    [IsAffine ((BigFppfOver.toScheme C S hS).obj U)]
    (hU : LocallyQuasiFinite ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from U))) :
    Finite ((BigFppfOver.toScheme C S hS).obj U) := by
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : Finite (Spec (.of k)) := inferInstance
  exact finite_of_quasiCompact_of_locallyQuasiFinite
    ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from U) ≫ e.hom)

/-- **An algebraic space locally quasi-finite over a field is decent.** -/
theorem isDecentSpace_of_isLocallyQuasiFinite {k : Type u} [Field k] (e : S ≅ Spec (.of k))
    {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace C S hS X)
    (hlqf : IsLocallyQuasiFinite C S hS ((isTerminal_yoneda_obj_base C S hS).from X)) :
    IsDecentSpace C S hS X := by
  classical
  rw [isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint C S hS X hX]
  intro x U hU φ hφ
  have hUlqf : LocallyQuasiFinite ((BigFppfOver.toScheme C S hS).map (Over.mkIdTerminal.from U)) :=
    (hlqf U (Over.mk (𝟙 (C.obj hS))) φ (𝟙 _) (Over.mkIdTerminal.from U) hφ
      (presheaf_yoneda_map_id_etale C S hS _)
      ((isTerminal_yoneda_obj_base C S hS).hom_ext _ _)).2
  have : IsAffine ((BigFppfOver.toScheme C S hS).obj U) := hU
  have hUfin := finite_of_locallyQuasiFinite_of_isAffine C S hS e U hUlqf
  have hptsU : Finite (points C S hS (yoneda.obj U)) :=
    Finite.of_equiv _ (schemePointsHomeomorph C S hS U).toEquiv.symm
  refine ⟨Set.toFinite _, ?_⟩
  -- the product `h_U × h_U` is represented by an object with finitely many points
  have hrep := relativelyRepresentable_prod_snd U (yoneda.obj U)
  let W := hrep.pullback (𝟙 (yoneda.obj U))
  have sq := hrep.isPullback (𝟙 (yoneda.obj U))
  have : IsIso (hrep.fst (𝟙 (yoneda.obj U))) := sq.isIso_fst_of_isIso
  have : IsAffine S := IsAffine.of_isIso e.hom
  have hqc : (MorphismProperty.inverseImage (@QuasiCompact.{u})
      (BigFppfOver.toScheme C S hS)).presheaf (prod.snd : yoneda.obj U ⨯ yoneda.obj U ⟶ _) :=
    presheaf_prod_snd inferInstance U (yoneda.obj U) (by infer_instance)
  have hlqf' : (MorphismProperty.inverseImage (@LocallyQuasiFinite.{u})
      (BigFppfOver.toScheme C S hS)).presheaf (prod.snd : yoneda.obj U ⨯ yoneda.obj U ⟶ _) :=
    presheaf_prod_snd inferInstance U (yoneda.obj U) hUlqf
  have : QuasiCompact ((BigFppfOver.toScheme C S hS).map (hrep.snd (𝟙 (yoneda.obj U)))) :=
    hqc.property _ _ _ sq
  have : LocallyQuasiFinite ((BigFppfOver.toScheme C S hS).map (hrep.snd (𝟙 (yoneda.obj U)))) :=
    hlqf'.property _ _ _ sq
  have hWfin : Finite ((BigFppfOver.toScheme C S hS).obj W) :=
    finite_of_quasiCompact_of_locallyQuasiFinite
      ((BigFppfOver.toScheme C S hS).map (hrep.snd (𝟙 (yoneda.obj U))))
  have hprod : Finite (points C S hS (yoneda.obj U ⨯ yoneda.obj U)) :=
    Finite.of_equiv _ ((schemePointsHomeomorph C S hS W).toEquiv.symm.trans
      (pointsHomeomorphOfIso C S hS (asIso (hrep.fst (𝟙 (yoneda.obj U))))).toEquiv)
  -- the self-intersection embeds into the product
  let m : pullback φ φ ⟶ yoneda.obj U ⨯ yoneda.obj U :=
    prod.lift (pullback.fst φ φ) (pullback.snd φ φ)
  have : Mono m := ⟨fun a b hab => pullback.hom_ext
    (by simpa [m] using congrArg (· ≫ prod.fst) hab)
    (by simpa [m] using congrArg (· ≫ prod.snd) hab)⟩
  have : Finite (points C S hS (pullback φ φ)) :=
    Finite.of_injective _ (pointsMap_injective_of_mono C S hS m)
  exact Set.toFinite _

end AlgebraicGeometry.Space
