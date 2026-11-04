module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.RationalMapAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.RationalMapBlowup
public import StacksFrontier.AlgebraicGeometry.C1573Port.SectionsToProjectiveSpace.DenseOpen
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart

namespace Ideal.C1573
end Ideal.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Resolving the rational map of a flattened graph closure by a blowup

Let `τ : h_{T₀} ⟶ X` be a morphism from a scheme which is an isomorphism over a dense open
`u : h_D ⟶ X`, given with an open immersion `T₀ ⟶ Z₂` into a scheme projective over `S` and a
chart `TV = T₀ ×_X V` closed in `V ×_S Z₂`; this is the output of
`AlgebraicGeometry.Space.C1573.exists_flattenedGraphClosure`. The rational map `X ⇢ Z₂ ⊆ ℙᵐ` is
defined by sections on a dense open `U' ⊆ D`, and the blowup of `X` in its centre factors through
`T₀` as the blowup of `T₀` in the pulled back centre. The centre avoids `U'`.

## Main results

* `AlgebraicGeometry.Space.C1573.exists_isBlowupAlong_resolution`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
  _root_.CategoryTheory.Limits.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The image of a family generating the unit ideal under a ring map generates the unit ideal. -/
theorem _root_.Ideal.C1573.span_range_comp_eq_top {R R' : Type*} [CommRing R] [CommRing R']
    (f : R →+* R') {ι : Type*} (a : ι → R) (h : Ideal.span (Set.range a) = ⊤) :
    Ideal.span (Set.range fun i => f (a i)) = ⊤ := by
  rw [show (Set.range fun i => f (a i)) = f '' Set.range a from (Set.range_comp f a),
    ← Ideal.map_span, h, Ideal.map_top]

open Stacks.ProjectiveExtension Stacks.SectionsToProjectiveSpace
  _root_.Stacks.ProjectiveExtension.C1573 _root_.Stacks.SectionsToProjectiveSpace.C1573 in
/-- **The rational map to the flattened graph closure is resolved by a blowup of `X`.** -/
theorem C1573.exists_isBlowupAlong_resolution (X : AlgebraicSpaces B S hS)
    {D V T₀ TV Z₂ : BigFppfOver B S hS} (u : yoneda.obj D ⟶ X.1) (hu : IsOpenImmersion B S hS u)
    {φ : yoneda.obj V ⟶ X.1}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs))]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T₀)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj TV)]
    [Finite (irreducibleComponents ((BigFppfOver.toScheme B S hS).obj D))]
    (τ : yoneda.obj T₀ ⟶ X.1) (σ : D ⟶ T₀) (hσ : IsPullback (yoneda.map σ) (𝟙 _) τ u)
    (pT : TV ⟶ T₀) (tV : TV ⟶ V) (hsq : IsPullback (yoneda.map pT) (yoneda.map tV) τ φ)
    (o : T₀ ⟶ Z₂) {m : ℕ} (i : (BigFppfOver.toScheme B S hS).obj Z₂ ⟶ projectiveSpaceOver m S)
    [_root_.AlgebraicGeometry.IsClosedImmersion i]
    (hi : i ≫ pullback.fst _ _ = B.inclusion.map Z₂.hom)
    (cS : (BigFppfOver.toScheme B S hS).obj TV ⟶
      pullback (B.inclusion.map V.hom) (B.inclusion.map Z₂.hom))
    [_root_.AlgebraicGeometry.IsClosedImmersion cS]
    (hc1 : cS ≫ pullback.fst _ _ = (BigFppfOver.toScheme B S hS).map tV)
    (hc2 : cS ≫ pullback.snd _ _ = (BigFppfOver.toScheme B S hS).map (pT ≫ o)) :
    ∃ (U' : ((BigFppfOver.toScheme B S hS).obj D).Opens),
      Dense (U' : Set ((BigFppfOver.toScheme B S hS).obj D)) ∧
      ∃ Z : ClosedSubspaces B S hS X.1,
        Disjoint (Set.range (pointsMap B S hS _ (yoneda.map (openSubHom D U') ≫ u)))
          (subspacePointSet B S hS X.1 Z.1) ∧
        ∃ (W : BigFppfOver B S hS) (π : W ⟶ T₀)
          (JT : ((BigFppfOver.toScheme B S hS).obj T₀).IdealSheafData)
          (eW : (BigFppfOver.toScheme B S hS).obj W ≅ AlgebraicGeometry.blowUp JT),
          eW.hom ≫ AlgebraicGeometry.blowUpToBase JT = (BigFppfOver.toScheme B S hS).map π ∧
          IsBlowupAlong B S hS Z
            (schemeSpaceMap π ≫ (ObjectProperty.homMk τ : schemeSpace T₀ ⟶ X)) := by
  set e₂ : (BigFppfOver.toScheme B S hS).obj Z₂ ⟶ projectiveSpaceAtUniverse.{u} m :=
    i ≫ pullback.snd _ _ with he₂
  obtain ⟨U', s, hs', hdense, hG⟩ :=
    exists_dense_eq_toProjectiveSpaceAtUniverse ((BigFppfOver.toScheme B S hS).map (σ ≫ o) ≫ e₂)
  have hu' : IsOpenImmersion B S hS (yoneda.map (openSubHom D U') ≫ u) :=
    isOpenImmersion_comp B S hS _ _ (isOpenImmersion_yoneda_map_openSubHom D U') hu
  have : Mono (yoneda.map (openSubHom D U') ≫ u) := mono_of_presheaf_isOpenImmersion hu'
  obtain ⟨U₀, ψ, hψpb, hU₀⟩ := exists_openSub_isPullback X.1 _ hu' φ
  have hψ : yoneda.map ψ ≫ yoneda.map (openSubHom D U') ≫ u =
      yoneda.map (openSubHom V U₀) ≫ φ := hψpb.w
  have hψ' : yoneda.map (ψ ≫ openSubHom D U') ≫ u = yoneda.map (openSubHom V U₀) ≫ φ := by
    rw [yoneda.map_comp, Category.assoc, hψ]
  have hpq := preimage_atlasRelationTarget_eq_of_eq_atlasPointSet hs U₀ _ hU₀
  set t : Fin (m + 1) → Γ((BigFppfOver.toScheme B S hS).obj (openSub V U₀), ⊤) := fun l =>
    ((BigFppfOver.toScheme B S hS).map ψ).appTop (U'.topIso.inv (s l)) with ht
  set g₀ : Fin (m + 1) → Γ((BigFppfOver.toScheme B S hS).obj V, U₀) :=
    fun l => U₀.topIso.hom (t l) with hg₀
  have ht' : Ideal.span (Set.range t) = ⊤ :=
    Ideal.C1573.span_range_comp_eq_top ((BigFppfOver.toScheme B S hS).map ψ).appTop.hom _ hs'
  have hfun : (fun j => U₀.topIso.inv (g₀ j)) = t := funext fun j => Iso.hom_inv_id_apply _ _
  have hgU : Ideal.span (Set.range fun j => U₀.topIso.inv (g₀ j)) = ⊤ := by
    rw [hfun]
    exact ht'
  have hg : Ideal.span (Set.range g₀) = ⊤ :=
    Ideal.C1573.span_range_comp_eq_top U₀.topIso.hom.hom _ ht'
  set J := Scheme.IdealSheafData.vanishingIdeal
    ⟨((U₀ : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
      Set ((BigFppfOver.toScheme B S hS).obj V))ᶜ, U₀.isOpen.isClosed_compl⟩ with hJ
  have hJs : (J.support : Set ((BigFppfOver.toScheme B S hS).obj V)) =
      (U₀ : Set ((BigFppfOver.toScheme B S hS).obj V))ᶜ :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  set I₀ := J.ideal ⟨⊤, isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj V)⟩ with hI₀
  have hIle := Scheme.IdealSheafData.C1573.basicOpen_le_of_mem_ideal_top J U₀ hJs
  have hIU := Scheme.IdealSheafData.C1573.exists_mem_ideal_top J U₀ hJs
  have := etale_atlasRelationTarget B S hS hs he
  have := etale_atlasRelationSource B S hS hs he
  have hI :
      I₀.map ((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).appTop.hom =
      I₀.map ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).appTop.hom :=
    Scheme.IdealSheafData.C1573.map_ideal_top_vanishingIdeal_eq U₀ _ _ hpq
  have hgR : ∀ l, ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hs)).presheaf.map
      (eqToHom hpq.symm).op
      (((BigFppfOver.toScheme B S hS).map (atlasRelationTarget B S hS hs)).app U₀ (g₀ l)) =
      ((BigFppfOver.toScheme B S hS).map (atlasRelationSource B S hS hs)).app U₀ (g₀ l) := fun l =>
    atlasRelation_presheaf_map_app_eq hs _ U₀ ψ hψ hpq (U'.topIso.inv (s l))
  have : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj V) := {}
  have hU : IsCompact (U₀ : Set ((BigFppfOver.toScheme B S hS).obj V)) :=
    NoetherianSpace.isCompact _
  have hU' : _root_.IsQuasiSeparated (U₀ : Set ((BigFppfOver.toScheme B S hS).obj V)) :=
    fun _ _ _ _ _ _ _ _ => NoetherianSpace.isCompact _
  set L : pullback (B.inclusion.map V.hom) (B.inclusion.map Z₂.hom) ⟶
      pullback (terminal.from ((BigFppfOver.toScheme B S hS).obj V))
        (terminal.from (projectiveSpaceAtUniverse.{u} m)) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e₂) (terminal.hom_ext _ _) with hL
  have : _root_.AlgebraicGeometry.IsClosedImmersion L :=
    isClosedImmersion_lift_comp_snd _ _ i hi
  set c := cS ≫ L with hc
  have hct : c ≫ pullback.fst _ _ = (BigFppfOver.toScheme B S hS).map tV := by
    rw [hc, Category.assoc, hL, pullback.lift_fst, hc1]
  have hsnd : c ≫ pullback.snd _ _ = (BigFppfOver.toScheme B S hS).map (pT ≫ o) ≫ e₂ := by
    rw [hc, Category.assoc, hL, pullback.lift_snd, ← Category.assoc, hc2]
  obtain ⟨hiso, hfac⟩ := isIso_morphismRestrict_of_isPullback_section τ pT tV φ hsq σ u hσ U₀
    (ψ ≫ openSubHom D U') hψ'
  have hnat : (BigFppfOver.toScheme B S hS).map ψ ≫
      toProjectiveSpaceAtUniverse (fun l => U'.topIso.inv (s l)) hs' =
      toProjectiveSpaceAtUniverse t ht' :=
    Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality ((BigFppfOver.toScheme B S hS).map ψ) _
      hs' ht'
  have hcg : (((BigFppfOver.toScheme B S hS).map tV) ⁻¹ᵁ U₀).ι ≫ c ≫ pullback.snd _ _ =
      ((BigFppfOver.toScheme B S hS).map tV ∣_ U₀) ≫
        toProjectiveSpaceAtUniverse (fun j => U₀.topIso.inv (g₀ j)) hgU := by
    have key : toProjectiveSpaceAtUniverse (fun j => U₀.topIso.inv (g₀ j)) hgU =
        (BigFppfOver.toScheme B S hS).map ψ ≫
          toProjectiveSpaceAtUniverse (fun l => U'.topIso.inv (s l)) hs' :=
      (toProjectiveSpaceAtUniverse_congr hfun hgU ht').trans hnat.symm
    have hG' : (BigFppfOver.toScheme B S hS).map (openSubHom D U') ≫
        (BigFppfOver.toScheme B S hS).map (σ ≫ o) ≫ e₂ =
        toProjectiveSpaceAtUniverse (X := (BigFppfOver.toScheme B S hS).obj (openSub D U'))
          (fun l => U'.topIso.inv (s l)) hs' := by
      rwa [toScheme_map_openSubHom]
    rw [key, ← hG', hsnd]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [← Category.assoc (((BigFppfOver.toScheme B S hS).map tV ⁻¹ᵁ U₀).ι), hfac,
      CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    rfl
  obtain ⟨Z, hZ, W, π, JT, eW, heW, -, hb⟩ := exists_isBlowupAlong_comp_of_rationalMap X hs he
    U₀ I₀ g₀ hU hU' hIle hIU hg hgU hpq hI hgR τ pT tV hsq c hct hcg
  refine ⟨U', hdense, Z, ?_, W, π, JT, eW, heW, hb⟩
  refine disjoint_subspacePointSet_of_preimage_eq X (isSurjective_of_presheafSurjective B S hS φ hs)
    Z _ hZ _ fun v hv hsupp => ?_
  rw [← hU₀] at hv
  exact (mem_support_centreSheaf_iff U₀ I₀ g₀ hU hU' hIle hIU hg v).1 hsupp hv

end AlgebraicGeometry.Space

end
