module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal

/-!
# Faithfulness of base change on the spaces-étale sites of a surjective morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is surjective on points.
Base change `V ↦ V_X = X ×_Y V` is then a *faithful* functor from the spaces-étale site of `Y` to
that of `X`. In particular this holds for `f` integral, universally injective and surjective, the
setting of Stacks 05ZH.

## Main results

* `AlgebraicGeometry.Space.eq_of_isSurjective_of_isEtale`: two morphisms over `Y` into an
  algebraic space étale over `Y` which agree after precomposition with a surjective morphism
  are equal.
* `AlgebraicGeometry.Space.faithful_functor_of_isSurjective`: base change along a surjective
  morphism is faithful on spaces-étale sites.
* `AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isIntegralHom_of_universallyInjective`:
  base change along an integral, universally injective and surjective morphism is faithful on
  spaces-étale sites.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_spacesEtaleFaithful :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_spacesEtaleFaithful
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance (priority := high) hasLimitsOfShape_discrete_presheaf_spacesEtaleFaithful
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-! ### The equalizer of two morphisms into an étale algebraic space -/

section Equalizer

variable {𝒴 𝒱 𝒱' 𝒲 : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- In a cartesian square of presheaves over `S`, the base change of an open immersion of
algebraic spaces is an open immersion. -/
private theorem isOpenImmersion_of_isPullback_presheaf
    {F G H P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ H} {g : G ⟶ H} {fst : P ⟶ F}
    {snd : P ⟶ G} (sq : IsPullback fst snd f g) (hf : IsOpenImmersion B S hS f) :
    IsOpenImmersion B S hS snd :=
  (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback sq hf

/-- Let `v : 𝒱 ⟶ 𝒴` be étale, let `α, β : 𝒱' ⟶ 𝒱` be two morphisms over `𝒴`, and let `p : 𝒲 ⟶ 𝒱'`
be surjective on points with `p ≫ α = p ≫ β`. Then `α = β`. -/
theorem eq_of_isSurjective_of_isEtale (h𝒴 : IsAlgebraicSpace B S hS 𝒴)
    (h𝒱 : IsAlgebraicSpace B S hS 𝒱) (h𝒱' : IsAlgebraicSpace B S hS 𝒱')
    (_h𝒲 : IsAlgebraicSpace B S hS 𝒲) (v : 𝒱 ⟶ 𝒴) (hv : IsEtale B S hS v)
    {α β : 𝒱' ⟶ 𝒱} (hv' : α ≫ v = β ≫ v) {p : 𝒲 ⟶ 𝒱'} (hp : IsSurjective B S hS p)
    (hpαβ : p ≫ α = p ≫ β) :
    α = β := by
  have hsq : IsPullback (pullback.fst (pullback.diagonal v) (pullback.lift α β hv'))
      (pullback.snd (pullback.diagonal v) (pullback.lift α β hv')) (pullback.diagonal v)
      (pullback.lift α β hv') :=
    IsPullback.of_hasPullback _ _
  have hα : pullback.snd (pullback.diagonal v) (pullback.lift α β hv') ≫ α =
      pullback.fst (pullback.diagonal v) (pullback.lift α β hv') := by
    simpa [pullback.lift_fst] using (congrArg (· ≫ pullback.fst v v) hsq.w).symm
  have hβ : pullback.snd (pullback.diagonal v) (pullback.lift α β hv') ≫ β =
      pullback.fst (pullback.diagonal v) (pullback.lift α β hv') := by
    simpa [pullback.lift_snd] using (congrArg (· ≫ pullback.snd v v) hsq.w).symm
  have hE : IsAlgebraicSpace B S hS
      (pullback (pullback.diagonal v) (pullback.lift α β hv')) :=
    isAlgebraicSpace_pullback B S hS _ _ h𝒱 h𝒱'
      (isAlgebraicSpace_pullback B S hS v v h𝒱 h𝒱 h𝒴)
  have hincl : IsOpenImmersion B S hS
      (pullback.snd (pullback.diagonal v) (pullback.lift α β hv')) :=
    isOpenImmersion_of_isPullback_presheaf B S hS hsq
      (isOpenImmersion_diagonal_of_isUnramified B S hS h𝒱 h𝒴 v
        (isUnramified_of_isEtale B S hS hv))
  have hfactor : (p ≫ α) ≫ pullback.diagonal v = p ≫ pullback.lift α β hv' :=
    pullback.hom_ext (by simp [pullback.lift_fst]) (by simpa [pullback.lift_snd] using hpαβ)
  have hsurj : IsSurjective B S hS
      (pullback.snd (pullback.diagonal v) (pullback.lift α β hv')) := by
    intro x
    obtain ⟨w, rfl⟩ := hp x
    exact ⟨pointsMap B S hS 𝒲 (hsq.lift (p ≫ α) p hfactor) w,
      by rw [← pointsMap_comp_apply B S hS, hsq.lift_snd]⟩
  have hiso : IsIso (pullback.snd (pullback.diagonal v) (pullback.lift α β hv')) :=
    isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS hE h𝒱' _
      (isEtale_of_isOpenImmersion B S hS hincl)
      (fun _ hZ g ↦ injective_pointsMap_of_isImmersion B S hS hZ _
        (isImmersion_of_isOpenImmersion B S hS
          (isOpenImmersion_of_isPullback_presheaf B S hS
            (IsPullback.of_hasPullback g _).flip hincl)))
      hsurj
  exact (@cancel_epi _ _ _ _ _ _ (IsIso.epi_of_iso _) _ _).mp (hα.trans hβ.symm)

end Equalizer

/-! ### Faithfulness of base change along a surjective morphism -/

variable {X Y : AlgebraicSpaces B S hS}

/-- Base change along a morphism of algebraic spaces which is surjective on points is faithful on
spaces-étale sites. -/
theorem faithful_functor_of_isSurjective (f : X ⟶ Y) (hf : IsSurjective B S hS f.hom)
    (D : SpacesBaseChange B S hS f) :
    D.functor.Faithful where
  map_injective {V' V} {a b} hab := by
    have key : ∀ c : V' ⟶ V,
        (D.projection.app V').hom ≫ c.hom.left.hom =
          (D.functor.map c).hom.left.hom ≫ (D.projection.app V).hom :=
      fun c ↦ (congrArg (fun k ↦ k.hom) (D.projection.naturality c)).symm
    have hw : ∀ c : V' ⟶ V, c.hom.left.hom ≫ V.1.hom.hom = V'.1.hom.hom :=
      fun c ↦ congrArg (fun k ↦ k.hom) (Over.w c.hom)
    have hproj : IsSurjective B S hS (D.projection.app V').hom :=
      isSurjective_of_isPullback B S hS (D.isPullback V').flip hf
    exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _
      (eq_of_isSurjective_of_isEtale B S hS Y.property V.1.left.property
        V'.1.left.property (D.functor.obj V').1.left.property V.1.hom.hom V.property
        ((hw a).trans (hw b).symm) hproj (by rw [key a, key b, hab]))))

/-- Let `f : X ⟶ Y` be an integral, universally injective and surjective morphism of algebraic
spaces over `S`. The base-change functor `V ↦ V_X = X ×_Y V` from the spaces-étale site of `Y` to
that of `X` is faithful. -/
theorem faithful_spacesBaseChange_of_isIntegralHom_of_universallyInjective (f : X ⟶ Y)
    (_hint : IsIntegralHom B S hS f.hom) (_hui : UniversallyInjective B S hS f.hom)
    (hsurj : IsSurjective B S hS f.hom) :
    (spacesBaseChange B S hS f).functor.Faithful :=
  faithful_functor_of_isSurjective B S hS f hsurj (spacesBaseChange B S hS f)

end AlgebraicGeometry.Space

end
