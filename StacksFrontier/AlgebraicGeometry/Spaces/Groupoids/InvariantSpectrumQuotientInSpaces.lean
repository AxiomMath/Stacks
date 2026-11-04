module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSpectrumSiteCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC

/-!
# The invariant spectrum is a categorical quotient in the category of algebraic spaces

Let `G = (U, R, s, t, c)` be a groupoid scheme over `S` with `U` and `R` affine and `s, t` finite
locally free, whose object scheme, arrow scheme and invariant spectrum `M = Spec C` lie in the big
fppf site of `S`. This file proves the heart of **Stacks 0DUR**: every morphism `ψ : U ⟶ Y` to an
algebraic space which is invariant under `s` and `t` factors uniquely through `φ : U ⟶ M`
(`AlgebraicGeometry.Space.existsUnique_comp_quotientSite`).

Uniqueness is `AlgebraicGeometry.Space.IsSiteCategoricalQuotient.hom_ext`. Existence is the
source's argument: for every point `p` of `M` there is an étale chart `W ⟶ M` through `p` on which
`ψ` is read off a morphism `W ⟶ Y`; it is constructed from an affine open `V` of an étale atlas of
`Y` around the image of a point of `U ×_Y (atlas)` over `p`, by
`AlgebraicGeometry.Space.exists_siteChart`. The morphisms on the charts agree on the fibre products
of two charts by `AlgebraicGeometry.Space.eq_of_twistedToAux_comp_eq`, so they glue to a morphism
`M ⟶ Y` because `Y` is a sheaf; that it restricts to `ψ` is checked on the étale covering of `U`
by the base changes of the charts.

## Main results

* `AlgebraicGeometry.Space.existsUnique_comp_quotientSite`: the categorical quotient property in
  algebraic spaces.

## References

* [Stacks Project, Tag 0DUR](https://stacks.math.columbia.edu/tag/0DUR)
-/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids Stacks.Morphisms
open AlgebraicGeometry.GroupoidScheme

noncomputable section

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} (hS : B.Contains S)
  {G : GroupoidScheme S} [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
  (σ : Spec (.of (invariantRing G)) ⟶ S) (hσ : objectsToInvariantSpectrum G ≫ σ = G.objects.hom)
  (hM : B.Contains (Spec (.of (invariantRing G))))
  {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
  (ψ : yoneda.obj (schemeSiteObject B hS hU) ⟶ Y)

omit [IsAffine G.objects.left] [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
  [IsFiniteLocallyFree G.target.left] in
/-- **A morphism from the base change of a chart factors as required.** Given a chart `W ⟶ M`
with `U'' = W ×_M U` on which `ψ` is read off `h_W : W ⟶ Y`, any two morphisms `x₁ : X ⟶ U` and
`x₂ : X ⟶ W` over `M` satisfy `x₂ ≫ h_W = x₁ ≫ ψ`: the pair factors through `U''`. -/
theorem chart_comp_eq {W U'' : BigFppfOver B S hS} (e : W ⟶ invariantSpectrumSite hS G σ hM)
    (a : U'' ⟶ schemeSiteObject B hS hU) (b : U'' ⟶ W) (hW : yoneda.obj W ⟶ Y)
    (hpb : IsPullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
      ((BigFppfOver.toScheme B S hS).map (quotientSite hS G hU σ hσ hM))
      ((BigFppfOver.toScheme B S hS).map e))
    (hbW : yoneda.map b ≫ hW = yoneda.map a ≫ ψ) {X : BigFppfOver B S hS}
    (x₁ : X ⟶ schemeSiteObject B hS hU) (x₂ : X ⟶ W)
    (hx : x₁ ≫ quotientSite hS G hU σ hσ hM = x₂ ≫ e) :
    yoneda.map x₂ ≫ hW = yoneda.map x₁ ≫ ψ := by
  have hx' := congrArg (BigFppfOver.toScheme B S hS).map hx
  rw [Functor.map_comp, Functor.map_comp] at hx'
  let c₀ := hpb.lift ((BigFppfOver.toScheme B S hS).map x₁)
    ((BigFppfOver.toScheme B S hS).map x₂) hx'
  have hc₀ : c₀ ≫ B.inclusion.map U''.hom = B.inclusion.map X.hom := by
    have hw : ∀ {T T' : BigFppfOver B S hS} (f : T ⟶ T'),
        (BigFppfOver.toScheme B S hS).map f ≫ B.inclusion.map T'.hom =
          B.inclusion.map T.hom := fun f => by
      change B.inclusion.map f.left ≫ _ = _
      rw [← Functor.map_comp, Over.w f]
    rw [← hw a, ← Category.assoc, hpb.lift_fst, hw x₁]
  let c : X ⟶ U'' := BigFppfOver.homOfCompEq B S hS c₀ hc₀
  have hca : c ≫ a = x₁ := (BigFppfOver.toScheme B S hS).map_injective <| by
    rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq]
    exact hpb.lift_fst _ _ _
  have hcb : c ≫ b = x₂ := (BigFppfOver.toScheme B S hS).map_injective <| by
    rw [Functor.map_comp, BigFppfOver.toScheme_map_homOfCompEq]
    exact hpb.lift_snd _ _ _
  rw [← hca, ← hcb, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hbW]

/-- The data of an étale chart of `M` on which `ψ` is read off a morphism to `Y`. -/
def ChartAt (p : (BigFppfOver.toScheme B S hS).obj (invariantSpectrumSite hS G σ hM)) : Prop :=
  ∃ (W U'' R'' : BigFppfOver B S hS) (e : W ⟶ invariantSpectrumSite hS G σ hM)
    (a : U'' ⟶ schemeSiteObject B hS hU) (b : U'' ⟶ W) (s'' t'' : R'' ⟶ U'')
    (hW : yoneda.obj W ⟶ Y),
    Etale ((BigFppfOver.toScheme B S hS).map e) ∧
      IsPullback ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map b)
        ((BigFppfOver.toScheme B S hS).map (quotientSite hS G hU σ hσ hM))
        ((BigFppfOver.toScheme B S hS).map e) ∧
      yoneda.map b ≫ hW = yoneda.map a ≫ ψ ∧ IsSiteCategoricalQuotient s'' t'' b ∧
      p ∈ Set.range ((BigFppfOver.toScheme B S hS).map e).base

/-- **Every point of an object of the site lies in an affine open subobject.** -/
private theorem exists_affine_open_mem_range (W₀ : BigFppfOver B S hS)
    (w₀ : (BigFppfOver.toScheme B S hS).obj W₀) :
    ∃ (Vs : BigFppfOver B S hS) (ιV : Vs ⟶ W₀), IsAffine ((siteToOver B hS).obj Vs).left ∧
      _root_.AlgebraicGeometry.IsSeparated ((siteToOver B hS).obj Vs).hom ∧
      Etale ((BigFppfOver.toScheme B S hS).map ιV) ∧
      w₀ ∈ Set.range ((BigFppfOver.toScheme B S hS).map ιV).base := by
  obtain ⟨_, ⟨V₀', hV₀, rfl⟩, hwV₀, -⟩ :=
    ((BigFppfOver.toScheme B S hS).obj W₀).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ w₀) isOpen_univ
  let V₀ : ((BigFppfOver.toScheme B S hS).obj W₀).Opens := V₀'
  have hcV : B.Contains V₀.toScheme := BigFppfSite.contains_of_isOpenImmersion B V₀.ι W₀.left.2
  let Vs : BigFppfOver B S hS :=
    schemeSiteObject B hS (X := Over.mk (V₀.ι ≫ ((siteToOver B hS).obj W₀).hom)) hcV
  let ιV : Vs ⟶ W₀ := BigFppfOver.homOfCompEq B S hS (T := Vs) (W := W₀) V₀.ι rfl
  have hιV : (BigFppfOver.toScheme B S hS).map ιV = V₀.ι :=
    BigFppfOver.toScheme_map_homOfCompEq B S hS (T := Vs) (W := W₀) V₀.ι rfl
  have hVa : IsAffine ((siteToOver B hS).obj Vs).left := hV₀
  refine ⟨Vs, ιV, hVa, ?_, by rw [hιV]; exact (inferInstance : Etale V₀.ι), ⟨(⟨_, hwV₀⟩ : V₀), ?_⟩⟩
  · have : _root_.AlgebraicGeometry.IsSeparated
        (((siteToOver B hS).obj Vs).hom ≫ terminal.from S) := by
      rw [Subsingleton.elim (((siteToOver B hS).obj Vs).hom ≫ terminal.from S)
        (terminal.from _)]
      infer_instance
    exact _root_.AlgebraicGeometry.IsSeparated.of_comp _ (terminal.from S)
  · rw [hιV]
    rfl

include hR hY in
/-- **Every point of `M` lies in an étale chart on which `ψ` is read off a morphism to `Y`.** -/
theorem chartAt
    (hψ : yoneda.map (sourceSite hS G hU hR) ≫ ψ = yoneda.map (targetSite hS G hU hR) ≫ ψ)
    (p : (BigFppfOver.toScheme B S hS).obj (invariantSpectrumSite hS G σ hM)) :
    ChartAt hS hU σ hσ hM ψ p := by
  classical
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  obtain ⟨u, hu⟩ := surjective_objectsToInvariantSpectrum G p
  obtain ⟨W₀, b₀, hsurj₀, het₀⟩ := hY.exists_atlas
  set hv₀ := Functor.relativelyRepresentable.of_diag hY.diagonal_representable b₀
  -- a point of `U ×_Y W₀` over `u`
  have hsurj₁ : Surjective ((BigFppfOver.toScheme B S hS).map (hv₀.snd ψ)) :=
    MorphismProperty.relative.property_snd hsurj₀ ψ
  obtain ⟨u₁, hu₁⟩ := hsurj₁.surj u
  -- an affine open of `W₀` around its image
  obtain ⟨Vs, ιV, _, _, hιe, w, hw⟩ := exists_affine_open_mem_range hS W₀
    (((BigFppfOver.toScheme B S hS).map (hv₀.fst' ψ)).base u₁)
  let v : yoneda.obj Vs ⟶ Y := yoneda.map ιV ≫ b₀
  have hv : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) v :=
    (isEtale_iff_presheaf_of_yoneda B S hS v).1 (isEtale_comp B S hS
      (isEtale_of_presheaf_etale B S hS
        ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ιV).2 hιe))
      ((isEtale_iff_presheaf_of_yoneda B S hS b₀).2 het₀))
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback u₁ w hw.symm
  have hpbV := (IsPullback.of_hasPullback (hv₀.fst' ψ) ιV).map (BigFppfOver.toScheme B S hS)
  have hx₀ : ((BigFppfOver.toScheme B S hS).map (pullback.fst (hv₀.fst' ψ) ιV)).base
      (hpbV.isoPullback.inv.base z) = u₁ := by
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz]
  have hcond : yoneda.map (pullback.snd (hv₀.fst' ψ) ιV) ≫ v =
      yoneda.map (pullback.fst (hv₀.fst' ψ) ιV ≫ hv₀.snd ψ) ≫ ψ := by
    rw [← Category.assoc, ← Functor.map_comp, ← pullback.condition, Functor.map_comp,
      Category.assoc, (hv₀.isPullback' ψ).w, Functor.map_comp, Category.assoc]
  let ℓ := (Functor.relativelyRepresentable.of_diag hY.diagonal_representable v).lift' _ _ hcond
  have hℓ : ℓ ≫ twistedProj hU hY ψ v = pullback.fst (hv₀.fst' ψ) ιV ≫ hv₀.snd ψ :=
    Functor.relativelyRepresentable.lift'_snd _ _ _ _
  have hu' : ((BigFppfOver.toScheme B S hS).map (twistedProj hU hY ψ v)).base
      (((BigFppfOver.toScheme B S hS).map ℓ).base (hpbV.isoPullback.inv.base z)) = u := by
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hℓ, Functor.map_comp,
      Scheme.Hom.comp_apply, hx₀, hu₁]
  -- the chart
  obtain ⟨W, U'', R'', e, k, a, b, j, s'', t'', he, hpb, hja, hbk, hq, hrange⟩ :=
    exists_siteChart hU hR σ hσ hM hY ψ hψ v hv
      (((BigFppfOver.toScheme B S hS).map ℓ).base (hpbV.isoPullback.inv.base z))
  refine ⟨W, U'', R'', e, a, b, s'', t'', yoneda.map k ≫ v, he, hpb, ?_, hq, ?_⟩
  · rw [← Category.assoc, ← Functor.map_comp, hbk, Functor.map_comp, Category.assoc,
      twisted_w, ← Category.assoc, ← Functor.map_comp, hja]
  · obtain ⟨x, hx⟩ := hrange
    refine ⟨((BigFppfOver.toScheme B S hS).map b).base x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hpb.w, Scheme.Hom.comp_apply, ← hja, Functor.map_comp,
      Scheme.Hom.comp_apply, hx, hu']
    exact hu

include hR hY in
/-- **`φ : U ⟶ M` is a categorical quotient in the category of algebraic spaces**, in the form of
Stacks 0DUR: every morphism from `U` to an algebraic space which coequalizes the source and the
target factors uniquely through `M`. -/
theorem existsUnique_comp_quotientSite
    (hψ : yoneda.map (sourceSite hS G hU hR) ≫ ψ = yoneda.map (targetSite hS G hU hR) ≫ ψ) :
    ∃! h : yoneda.obj (invariantSpectrumSite hS G σ hM) ⟶ Y,
      yoneda.map (quotientSite hS G hU σ hσ hM) ≫ h = ψ := by
  classical
  refine existsUnique_of_exists_of_unique ?_ fun h₁ h₂ e₁ e₂ =>
    (isSiteCategoricalQuotient_quotientSite hS G hU hR σ hσ hM).hom_ext hY (e₁.trans e₂.symm)
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  choose W U'' R'' e a b s'' t'' hW he hpb hbW hqW hrange using
    fun p => chartAt hS hU hR σ hσ hM hY ψ hψ p
  -- the sheaf condition for the étale covering of `M` by the charts
  have hcover : Sieve.generate (Presieve.ofArrows W e) ∈
      BigFppfOver.topology B S hS (invariantSpectrumSite hS G σ hM) :=
    generate_ofArrows_mem_topology_of_etale W e he fun p => ⟨p, hrange p⟩
  have hsf : Presieve.IsSheafFor Y (Presieve.ofArrows W e) :=
    (Presieve.isSheafFor_iff_generate (P := Y) _).mpr
      (((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) Y).mp hY.isSheaf) _ hcover)
  obtain ⟨t, ht, -⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks Y e).mp hsf)
    (fun p => yonedaEquiv (hW p)) fun p q => by
      rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
      congr 1
      -- agreement on `W_p ×_M W_q`, checked on an affine étale cover
      obtain ⟨I, Z, π, hZ, hπ, hZc⟩ := BigFppfOver.exists_affine_etale_cover B S hS
        (pullback (e p) (e q))
      refine hom_ext_of_cover B S hS hY.isSheaf _ Z π hZc fun i => ?_
      have := hZ i
      have hπe : Etale ((BigFppfOver.toScheme B S hS).map (π i)) :=
        (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (π i)).1
          ((isEtale_iff_presheaf_of_yoneda B S hS _).1 (hπ i))
      have hpbpq := (IsPullback.of_hasPullback (e p) (e q)).map (BigFppfOver.toScheme B S hS)
      have hfst : Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst (e p) (e q))) :=
        MorphismProperty.of_isPullback hpbpq.flip (he q)
      let ζ := π i ≫ pullback.fst (e p) (e q) ≫ e p
      have hζ : Etale ((BigFppfOver.toScheme B S hS).map ζ) := by
        have := he p
        simp only [ζ, Functor.map_comp]
        infer_instance
      set hYM := isAlgebraicSpace_invariantSpectrumSite hS σ hM
      set A := twistedToAux hU hYM (yoneda.map (quotientSite hS G hU σ hσ hM)) (yoneda.map ζ)
      set Pj := twistedProj hU hYM (yoneda.map (quotientSite hS G hU σ hσ hM)) (yoneda.map ζ)
      have hw := twisted_w hU hYM (yoneda.map (quotientSite hS G hU σ hσ hM)) (yoneda.map ζ)
      rw [← Functor.map_comp, ← Functor.map_comp] at hw
      have hw' : A ≫ ζ = Pj ≫ quotientSite hS G hU σ hσ hM := yoneda.map_injective hw
      have h₁ := chart_comp_eq hS hU σ hσ hM ψ (e p) (a p) (b p) (hW p) (hpb p) (hbW p) Pj
        (A ≫ π i ≫ pullback.fst (e p) (e q)) (by rw [← hw']; simp only [ζ, Category.assoc])
      have h₂ := chart_comp_eq hS hU σ hσ hM ψ (e q) (a q) (b q) (hW q) (hpb q) (hbW q) Pj
        (A ≫ π i ≫ pullback.snd (e p) (e q))
        (by rw [← hw']; simp only [ζ, Category.assoc, pullback.condition])
      have key : yoneda.map (π i ≫ pullback.fst (e p) (e q)) ≫ hW p =
          yoneda.map (π i ≫ pullback.snd (e p) (e q)) ≫ hW q := by
        refine eq_of_twistedToAux_comp_eq hS hU hR σ hσ hM (Z i) ζ hζ hY _ _ ?_
        simpa only [Functor.map_comp, Category.assoc] using h₁.trans h₂.symm
      simpa only [Functor.map_comp, Category.assoc] using key
  let h : yoneda.obj (invariantSpectrumSite hS G σ hM) ⟶ Y := yonedaEquiv.symm t
  have hh : ∀ p, yoneda.map (e p) ≫ h = hW p := fun p => yonedaEquiv.injective <| by
    rw [← yonedaEquiv_naturality, Equiv.apply_symm_apply]
    exact ht p
  refine ⟨h, ?_⟩
  -- `φ ≫ h = ψ` on the étale covering of `U` by the base changes of the charts
  have hacover : Sieve.generate (Presieve.ofArrows U'' a) ∈
      BigFppfOver.topology B S hS (schemeSiteObject B hS hU) := by
    refine generate_ofArrows_mem_topology_of_etale U'' a
      (fun p => MorphismProperty.of_isPullback (hpb p).flip (he p)) fun x => ?_
    let p := ((BigFppfOver.toScheme B S hS).map (quotientSite hS G hU σ hσ hM)).base x
    obtain ⟨w, hw⟩ := hrange p
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x w hw.symm
    refine ⟨p, ((hpb p).isoPullback.inv).base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz]
  refine hom_ext_of_cover B S hS hY.isSheaf _ U'' a hacover fun p => ?_
  have hab : a p ≫ quotientSite hS G hU σ hσ hM = b p ≫ e p :=
    (BigFppfOver.toScheme B S hS).map_injective (by simpa only [Functor.map_comp] using (hpb p).w)
  rw [← Category.assoc, ← Functor.map_comp, hab, Functor.map_comp, Category.assoc, hh p, hbW p]

end AlgebraicGeometry.Space

end

end
