module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.RationalMapCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.RationalMapBlowupChart
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.BlowupEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SchemeChartLift

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Resolving a rational map to projective space on an algebraic space by a blowup

Let `X` be an algebraic space with an affine surjective étale atlas `φ : V ⟶ X` whose relation
is affine, carrying a rational map `[g₀ : ⋯ : gₘ]` to projective space on an open `U ⊆ V` given by
data compatible on the relation, with centre `𝒥` on `V`. Let `τ : T ⟶ X` be a morphism from a
scheme whose base change `T_V = T ×_X V ⟶ V` is an isomorphism over `U` and comes with a closed
immersion into `V × ℙᵐ` over `V` whose second component is the rational map over `U`; this is
the situation of the closure of the graph of the rational map.

Then the centre descends to a closed subspace `Z ⊆ X`
(`AlgebraicGeometry.Space.C1573.exists_closedSubspace_preimage_eq_centreSheaf`) and the blowup
`W ⟶ T` of the scheme `T` in the inverse image of `Z`, composed with `τ`, is the blowup of `X` in
`Z`. On the chart `V` this is
`AlgebraicGeometry.Space.C1573.isBlowupAlong_comp_of_centreSheaf`, and being a blowup is étale
local on the target (`AlgebraicGeometry.Space.C1573.isBlowupAlong_of_isBlowupAlong_pullbackSnd`).

## Main results

* `AlgebraicGeometry.Space.C1573.exists_isBlowupAlong_comp_of_rationalMap`: the statement above.

## References

* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

open Stacks.ProjectiveExtension Stacks.SectionsToProjectiveSpace
  _root_.Stacks.ProjectiveExtension.C1573 in
/-- **Resolving a rational map to projective space on an algebraic space by a blowup.**
In the situation of the module docstring, there is a closed subspace `Z ⊆ X` whose preimage on the
chart `V` is the centre `centreSheaf U₀ I₀ g₀`, and a blowup `π : W ⟶ T₀` of `T₀` in an ideal
sheaf `JT` cutting out the inverse image of `Z` under `τ`, such that `π ≫ τ` is the blowup of `X`
along `Z`. -/
theorem C1573.exists_isBlowupAlong_comp_of_rationalMap (X : AlgebraicSpaces B S hS)
    {V T₀ TV : BigFppfOver B S hS} {φ : yoneda.obj V ⟶ X.1}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs))]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T₀)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj TV)]
    (U₀ : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {m : ℕ}
    (g₀ : Fin (m + 1) → Γ((BigFppfOver.toScheme B S hS).obj V, U₀))
    (hU : IsCompact (U₀ : Set ((BigFppfOver.toScheme B S hS).obj V)))
    (hU' : _root_.IsQuasiSeparated (U₀ : Set ((BigFppfOver.toScheme B S hS).obj V)))
    (hIle : ∀ f ∈ I₀, ((BigFppfOver.toScheme B S hS).obj V).basicOpen f ≤ U₀)
    (hIU : ∀ x ∈ U₀, ∃ f ∈ I₀, x ∈ ((BigFppfOver.toScheme B S hS).obj V).basicOpen f)
    (hg : Ideal.span (Set.range g₀) = ⊤)
    (hgU : Ideal.span (Set.range fun j => U₀.topIso.inv (g₀ j)) = ⊤)
    (hpq : (BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs) ⁻¹ᵁ U₀ =
      (BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs) ⁻¹ᵁ U₀)
    (hI : I₀.map ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).appTop.hom =
      I₀.map ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).appTop.hom)
    (hgR : ∀ l, ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs)).presheaf.map
        (eqToHom hpq.symm).op
        (((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).app U₀ (g₀ l)) =
      ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).app U₀ (g₀ l))
    (τ : yoneda.obj T₀ ⟶ X.1) (pT : TV ⟶ T₀) (tV : TV ⟶ V)
    (hsq : IsPullback (yoneda.map pT) (yoneda.map tV) τ φ)
    (c : (BigFppfOver.toScheme B S hS).obj TV ⟶
      pullback (terminal.from ((BigFppfOver.toScheme B S hS).obj V))
        (terminal.from (projectiveSpaceAtUniverse.{u} m)))
    [_root_.AlgebraicGeometry.IsClosedImmersion c]
    (hct : c ≫ pullback.fst _ _ = (BigFppfOver.toScheme B S hS).map tV)
    [IsIso ((BigFppfOver.toScheme B S hS).map tV ∣_ U₀)]
    (hcg : ((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀).ι ≫ c ≫ pullback.snd _ _ =
      ((BigFppfOver.toScheme B S hS).map tV ∣_ U₀) ≫
        toProjectiveSpaceAtUniverse (fun j => U₀.topIso.inv (g₀ j)) hgU) :
    ∃ Z : ClosedSubspaces B S hS X.1,
      Z.1.preimage φ = subschemePoints B S hS (Subobject.mk (centreSheaf U₀ I₀ g₀).subschemeι) ∧
      ∃ (W : BigFppfOver B S hS) (π : W ⟶ T₀)
        (JT : ((BigFppfOver.toScheme B S hS).obj T₀).IdealSheafData)
        (eW : (BigFppfOver.toScheme B S hS).obj W ≅ AlgebraicGeometry.blowUp JT),
        eW.hom ≫ AlgebraicGeometry.blowUpToBase JT = (BigFppfOver.toScheme B S hS).map π ∧
        (preimageClosedSubspace (ObjectProperty.homMk τ : schemeSpace T₀ ⟶ X) Z).1 =
          subschemePoints B S hS (Subobject.mk JT.subschemeι) ∧
        IsBlowupAlong B S hS Z
          (schemeSpaceMap π ≫ (ObjectProperty.homMk τ : schemeSpace T₀ ⟶ X)) := by
  obtain ⟨Z, hZ⟩ := exists_closedSubspace_preimage_eq_centreSheaf hs he U₀ I₀ g₀ X.2 hU hU' hpq
    hI hgR
  refine ⟨Z, hZ, ?_⟩
  set τ' : schemeSpace T₀ ⟶ X := ObjectProperty.homMk τ with hτ'
  set φ' : schemeSpace V ⟶ X := ObjectProperty.homMk φ with hφ'
  obtain ⟨JT, hJT⟩ := exists_idealSheafData_subschemePoints_eq T₀ (preimageClosedSubspace τ' Z)
  obtain ⟨W, π, eW, heW, hπ⟩ := exists_isBlowupAlong_blowUp T₀ JT _ hJT
  refine ⟨W, π, JT, eW, heW, hJT, ?_⟩
  -- the inverse image of `Z` on the blowup of `T` is an effective Cartier divisor
  have hb : IsPullbackDefined B S hS (schemeSpaceMap π ≫ τ') Z :=
    isEffectiveCartierDivisor_of_subfunctor_eq rfl hπ.isPullbackDefined
  -- the chart
  have het : IsEtale B S hS φ := isEtale_of_presheaf_etale B S hS he
  have hsurj : IsSurjective B S hS φ :=
    isSurjective_of_presheafSurjective B S hS φ hs
  have hsq' : IsPullback (schemeSpaceMap pT) (schemeSpaceMap tV) τ' φ' :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS T))
      hsq
  have hpTet : IsEtale B S hS (yoneda.map pT) :=
    isEtale_of_isPullback_presheaf B S hS (isAlgebraicSpace_yoneda B S hS TV)
      (isAlgebraicSpace_yoneda B S hS V) X.2 (isAlgebraicSpace_yoneda B S hS T₀) hsq.flip het
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj
      (bundledAtlasPresentation X φ hs he).U) :=
    inferInstanceAs (IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V))
  refine isBlowupAlong_of_isBlowupAlong_pullbackSnd (bundledAtlasPresentation X φ hs he) Z _ hb φ'
    hsurj het ?_
  have hQ := IsPullback.of_hasPullback (schemeSpaceMap π) (schemeSpaceMap pT)
  have hfstet : IsEtale B S hS (pullback.fst (schemeSpaceMap π) (schemeSpaceMap pT)).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ hQ.flip hpTet
  have hQV : IsBlowupAlong B S hS
      (preimageClosedSubspace (schemeSpaceMap tV) (preimageClosedSubspace φ' Z))
      (pullback.snd (schemeSpaceMap π) (schemeSpaceMap pT)) := by
    refine IsBlowupAlong.of_isPullback_of_isFlat hQ.flip (isFlat_of_isEtale B S hS hfstet)
      (preimageClosedSubspace τ' Z) _ ?_ hπ
    change Z.1.preimage (yoneda.map tV ≫ φ) = Z.1.preimage (yoneda.map pT ≫ τ)
    rw [hsq.w]
  have hVV := isBlowupAlong_comp_of_centreSheaf U₀ I₀ g₀ hU hU' hIle hIU hg hgU tV c hct hcg
    (preimageClosedSubspace φ' Z) hZ _ hQV
  have hpaste := hQ.paste_vert hsq'
  have h := hVV.of_iso_over hpaste.isoPullback.symm
  rwa [Iso.symm_hom, IsPullback.isoPullback_inv_snd] at h

end AlgebraicGeometry.Space

end
