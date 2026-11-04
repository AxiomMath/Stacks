module

public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductChartDesc
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeLocalCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePointwiseCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace

/-!
# Étale charts out of a disjoint union

Let `T` be an object of the big fppf site of `S` whose scheme is the disjoint union of the
schemes of a family `T' a`. A morphism `h_T ⟶ X` into an algebraic space whose restrictions to
the summands are étale is étale. In particular an affine étale chart `h_U ⟶ X` and a surjective
affine étale chart `h_W ⟶ X` glue to a surjective affine étale chart `h_{U ⊔ W} ⟶ X` in which
`U` is the nonvanishing locus of a global function.

## Main results

* `AlgebraicGeometry.Space.isEtale_of_iso_sigma`: étaleness out of a disjoint union is checked
  on the summands.
* `AlgebraicGeometry.Space.exists_isAffine_atlas_of_chart`: an affine étale chart is a basic
  open of a surjective affine étale chart.
* `AlgebraicGeometry.Space.exists_isPullback_basicOpen_of_isClosedImmersion`: such a basic open
  of a closed subscheme of an affine object is cut out by a basic open of the ambient object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {σ : Type u}
  (T' : σ → BigFppfOver B S hS) (T : BigFppfOver B S hS) (c : ∀ a, T' a ⟶ T)
  (e : (∐ fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) ≅ (BigFppfOver.toScheme B S hS).obj T)

/-- **Étaleness out of a disjoint union is checked on the summands.** A morphism from the
representable sheaf of a disjoint union to an algebraic space is étale as soon as its
restrictions to the summands are. -/
theorem isEtale_of_iso_sigma
    (he : ∀ a, Sigma.ι (fun a ↦ (BigFppfOver.toScheme B S hS).obj (T' a)) a ≫ e.hom =
      (BigFppfOver.toScheme B S hS).map (c a))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (p : yoneda.obj T ⟶ X) (hp : ∀ a, IsEtale B S hS (yoneda.map (c a) ≫ p)) :
    IsEtale B S hS p := by
  obtain ⟨hopen, hcov, -⟩ := isOpenImmersion_cover_disjoint_of_iso_sigma e he
  refine isEtale_of_forall_isEtaleAt B S hS (isAlgebraicSpace_yoneda B S hS T) hX p fun t => ?_
  obtain ⟨a, w, hw⟩ := hcov (pointsToScheme B S hS T t)
  obtain ⟨z, hz⟩ := surjective_pointsToScheme B S hS (T' a) w
  have hg := isOpenImmersion_yoneda_map B S hS (c a) (hopen a)
  let g := yoneda.map (c a)
  refine ⟨Subfunctor.range g, isOpenSubspace_range_of_isOpenImmersion (T' a) g hg,
    pointsMap B S hS _ (Subfunctor.toRange g) z, ?_, ?_⟩
  · rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]
    refine injective_pointsToScheme B S hS T ?_
    rw [pointsToScheme_pointsMap_yoneda, hz, hw]
  · let i := rangeIsoOfIsOpenImmersion (T' a) g hg
    have hfac : (Subfunctor.range g).ι = i.inv ≫ g := by
      rw [Iso.eq_inv_comp]
      exact Subfunctor.toRange_ι g
    rw [hfac, Category.assoc]
    exact isEtale_comp B S hS (isEtale_of_isIso B S hS i.inv) (hp a)

/-- **An affine étale chart is a basic open of a surjective affine étale chart.** Let
`b : h_U ⟶ X` be an étale chart and `c : h_W ⟶ X` a surjective étale chart of an algebraic
space, with `U` and `W` affine. Then there is a surjective étale chart `p : h_T ⟶ X` with `T`
affine and an open immersion `U ⟶ T` through which `b` factors, whose image is the
nonvanishing locus of a global function on `T`: `T` is the disjoint union of `U` and `W`. -/
theorem exists_isAffine_atlas_of_chart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {U W : BigFppfOver B S hS}
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (b : yoneda.obj U ⟶ X) (c : yoneda.obj W ⟶ X)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hce : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (hcs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c) :
    ∃ (T : BigFppfOver B S hS) (cU : U ⟶ T) (p : yoneda.obj T ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧ yoneda.map cU ≫ p = b ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf p ∧
      ∃ _ : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map cU),
      ∃ s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤),
        ((BigFppfOver.toScheme B S hS).obj T).basicOpen s =
          ((BigFppfOver.toScheme B S hS).map cU).opensRange := by
  let T' : ULift.{u} Bool → BigFppfOver B S hS := fun a => cond a.down U W
  obtain ⟨T, ι, e, he, -⟩ := BigFppfOver.exists_coproduct_of_mk_le_aleph0 (B := B) (S := S)
    (hS := hS) (σ := ULift.{u} Bool) Cardinal.mk_le_aleph0 T'
  let f : ∀ a, yoneda.obj (T' a) ⟶ X := fun a => match a with
    | ⟨true⟩ => b
    | ⟨false⟩ => c
  obtain ⟨p, hp⟩ := exists_desc_yoneda_of_iso_sigma B S hS T' T ι e he hX.isSheaf f
  have hTa : ∀ a, IsAffine ((BigFppfOver.toScheme B S hS).obj (T' a)) := fun a =>
    match a with
    | ⟨true⟩ => hU
    | ⟨false⟩ => hW
  have hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := IsAffine.of_isIso e.inv
  have hpe : IsEtale B S hS p := by
    refine isEtale_of_iso_sigma B S hS T' T ι e he hX p fun a => ?_
    rw [hp a]
    exact (isEtale_iff_presheaf_of_yoneda B S hS _).2 (match a with
      | ⟨true⟩ => hb
      | ⟨false⟩ => hce)
  have hpe' := (isEtale_iff_presheaf_of_yoneda B S hS p).1 hpe
  obtain ⟨hopen, hcov, hdisj⟩ := isOpenImmersion_cover_disjoint_of_iso_sigma e he
  refine ⟨T, ι ⟨true⟩, p, hTaff, hp ⟨true⟩, hpe', ?_, hopen ⟨true⟩, ?_⟩
  · refine presheafSurjective_of_isSurjective B S hS p hpe'.rep fun x => ?_
    obtain ⟨y, rfl⟩ := isSurjective_of_presheafSurjective B S hS c hcs x
    refine ⟨pointsMap B S hS _ (yoneda.map (ι ⟨false⟩)) y, ?_⟩
    rw [← pointsMap_comp_apply, hp ⟨false⟩]
    rfl
  · have hcl : IsClosed (((BigFppfOver.toScheme B S hS).map (ι ⟨true⟩)).opensRange :
        Set ((BigFppfOver.toScheme B S hS).obj T)) := by
      have heq : (((BigFppfOver.toScheme B S hS).map (ι ⟨true⟩)).opensRange :
          Set ((BigFppfOver.toScheme B S hS).obj T)) =
            (Set.range ((BigFppfOver.toScheme B S hS).map (ι ⟨false⟩)))ᶜ := by
        ext x
        refine ⟨fun hx hx' => Set.disjoint_left.1 (hdisj (by decide)) hx hx', fun hx => ?_⟩
        obtain ⟨⟨a⟩, ha⟩ := hcov x
        cases a
        · exact absurd ha hx
        · exact ha
      rw [heq, isClosed_compl_iff]
      exact ((BigFppfOver.toScheme B S hS).map (ι ⟨false⟩)).isOpenEmbedding.isOpen_range
    obtain ⟨s, -, hs⟩ := exists_isIdempotentElem_basicOpen_eq _ _ hcl
    exact ⟨s, hs⟩

/-- **A clopen part of a closed subscheme of an affine object is cut out by a basic open.** Let
`jT : T ⟶ AS` be a closed immersion into an affine object of the site and `cU : U ⟶ T` an open
immersion whose image is the nonvanishing locus of a global function on `T`. Then there is a
basic open `V₀ ⊂ AS`, again an affine object of the site, such that `U` is the part of `T` over
`V₀`: the square `U ⟶ V₀ ⟶ AS`, `U ⟶ T ⟶ AS` is a pullback and `U ⟶ V₀` is a closed
immersion. -/
theorem exists_isPullback_basicOpen_of_isClosedImmersion {U T AS : BigFppfOver B S hS}
    (cU : U ⟶ T) (jT : T ⟶ AS)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map cU)]
    [_root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map jT)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj AS)]
    (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (hs : ((BigFppfOver.toScheme B S hS).obj T).basicOpen s =
      ((BigFppfOver.toScheme B S hS).map cU).opensRange) :
    ∃ (V₀ : BigFppfOver B S hS) (o : V₀ ⟶ AS) (gU : U ⟶ V₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₀) ∧
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map o) ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map gU) ∧
        IsPullback gU cU o jT := by
  let Q := BigFppfOver.toScheme B S hS
  obtain ⟨-, hsurj⟩ :=
    _root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine (Q.map jT)
  obtain ⟨f, hf⟩ := hsurj s
  let V₀ := openSubobject B S hS AS ((Q.obj AS).basicOpen f).ι inferInstance
  let o := openSubobjectHom B S hS AS ((Q.obj AS).basicOpen f).ι inferInstance
  have ho : Q.map o = ((Q.obj AS).basicOpen f).ι :=
    toScheme_map_openSubobjectHom B S hS AS _ inferInstance
  have : _root_.AlgebraicGeometry.IsOpenImmersion (Q.map o) := by
    rw [ho]
    exact inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι _))
  have hR : (Q.map o).opensRange = (Q.obj AS).basicOpen f := by
    refine TopologicalSpace.Opens.ext ?_
    rw [Scheme.Hom.coe_opensRange, ho]
    exact Scheme.Opens.range_ι _
  have H' : Q.map jT ⁻¹ᵁ (Q.map o).opensRange = (Q.map cU).opensRange := by
    rw [hR, Scheme.preimage_basicOpen_top, hf, hs]
  have hrange : Set.range (Q.map (cU ≫ jT)) ⊆ Set.range (Q.map o) := by
    rintro _ ⟨y, rfl⟩
    have hy : Q.map cU y ∈ Q.map jT ⁻¹ᵁ (Q.map o).opensRange := by
      rw [H']; exact ⟨y, rfl⟩
    rw [Functor.map_comp, Scheme.Hom.comp_apply]
    exact hy
  obtain ⟨gU, hgU, -⟩ := BigFppfOver.existsUnique_lift_of_isOpenImmersion o
    inferInstance (cU ≫ jT) hrange
  have H : Q.map cU ≫ Q.map jT = Q.map gU ≫ Q.map o := by
    rw [← Functor.map_comp, ← Functor.map_comp, hgU]
  have hsq := IsOpenImmersion.isPullback (Q.map gU) (Q.map cU) (Q.map o) (Q.map jT) H H'
  let := B.hasPullbacks_schemes
  refine ⟨V₀, o, gU, ?_, inferInstance, ?_, IsPullback.of_map_of_faithful Q hsq⟩
  · exact (isAffineOpen_top (Q.obj AS)).basicOpen f
  · exact MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsClosedImmersion)
      hsq.flip inferInstance

end AlgebraicGeometry.Space

end
