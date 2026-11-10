module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Contains

/-!
# The chart sections of a pullback of a quasi-coherent module are uniformly bounded

Let `a : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, and let `ℳ` be a quasi-coherent `𝒪_X`-module whose sections over every étale chart of `X`
are fewer than the cutoff of `B`.  This file proves that for every étale chart `W` of `Y` a single
cardinal below the cutoff bounds the sections of `a^*ℳ` over the étale charts cut out by *all*
the Zariski opens of the scheme of `W`.

This is `AlgebraicGeometry.Space.exists_mk_modulePullback_sections_le` — which is the case of a
scheme point `T ⟶ X` and its identity chart — with the scheme point replaced by an arbitrary
morphism of algebraic spaces and an arbitrary étale chart of the source, and the argument is the
same.  Choose a surjective étale chart `U ⟶ X` whose scheme is a disjoint union of affine schemes
(Stacks 03FX) and let `P = W ×_X U`, an étale chart of `Y` mapping to `W` surjectively.  For an
open `Ω` of the scheme of `W` the sections of `a^*ℳ` over `Ω` inject into its sections over the
preimage of `Ω` in `P`, by the sheaf property for that étale covering; those are sections of the
Zariski restriction of `a^*ℳ` to `P`, which is the scheme-level pullback along `P ⟶ U` of the
Zariski restriction of `ℳ` to `U`
(`AlgebraicGeometry.Space.nonempty_chartRestrictionBaseChange`); and the sections of such a
pullback over any open of `P` are bounded in terms of the size of `P` and of the sections of `ℳ`
over the affine components of `U`, which are quotients of the sections of `ℳ` over `U` itself
(`AlgebraicGeometry.Scheme.Modules.mk_sections_pullback_le`).

## Main results

* `AlgebraicGeometry.Space.exists_mk_modulePullback_openChart_sections_le`: the uniform bound.

## References

* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 000I](https://stacks.math.columbia.edu/tag/000I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The sections of the pullback of a quasi-coherent module over the Zariski opens of an étale
chart of the source are uniformly bounded below the cutoff.**  Let `a : Y ⟶ X` be a morphism of
algebraic spaces and `ℳ` a quasi-coherent `𝒪_X`-module whose sections over every étale chart of
`X` are fewer than `B.cutoff`.  Then for every étale chart `W` of `Y` a single cardinal below
`B.cutoff` bounds the sections of `a^*ℳ` over the étale charts cut out by all the Zariski opens
of the scheme of `W`. -/
theorem exists_mk_modulePullback_openChart_sections_le {X Y : AlgebraicSpaces B S hS}
    (a : Y ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite)
    (hbound : ∀ U : (SmallEtale B S hS X.1)ᵒᵖ, HasCardinalLT (M.val.obj U) B.cutoff)
    (Wc : SmallEtale B S hS Y.1) :
    ∃ c < B.cutoff, ∀ Ω : (chartScheme Wc).Opens,
      #(((modulePullback B S hS a).obj M).val.obj
        (op ((openChartFunctor B S hS Y.1 Wc).obj Ω))) ≤ c := by
  obtain ⟨U, u, I, W, j, e, hsurj, het, hWaff, hje, hjimm, -, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS X.1 X.2
  let T : BigFppfOver B S hS := Wc.obj.left
  let f : yoneda.obj T ⟶ X.1 := Wc.obj.hom ≫ a.hom
  let hf := het.rep
  let P' := hf.pullback f
  let snd : P' ⟶ T := hf.snd f
  let fst' : P' ⟶ U := hf.fst' f
  have hsndSurj : Surjective ((BigFppfOver.toScheme B S hS).map snd) := hsurj.property_snd f
  let V0 : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk u, het⟩
  let W0 : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk (yoneda.map snd ≫ Wc.obj.hom),
    etale_comp_of_scheme B S hS snd Wc.obj.hom (het.property_snd f) Wc.property⟩
  have hw' : yoneda.map fst' ≫ V0.obj.hom = W0.obj.hom ≫ a.hom := by
    change yoneda.map fst' ≫ u = (yoneda.map snd ≫ Wc.obj.hom) ≫ a.hom
    rw [(hf.isPullback' f).w, Category.assoc]
  obtain ⟨ebc⟩ := nonempty_chartRestrictionBaseChange B S hS a M hM V0 W0 fst' hw'
  let P0 := restrictToChart B S hS X.2 M V0
  have : P0.IsQuasicoherent := isQuasicoherent_restrictToChart_viaIdEtaleChart B S hS X M hM V0
  set c := #Γ(P0, ⊤) with hc
  have : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (j i)) := hjimm
  let O : I → (chartScheme V0).Opens := fun i =>
    ((BigFppfOver.toScheme B S hS).map (j i)).opensRange
  have hOaff : ∀ i, IsAffineOpen (O i) := fun i => have := hWaff i; isAffineOpen_opensRange _
  have hcov : ⨆ i, O i = ⊤ :=
    iSup_opensRange_eq_top_of_sigma_iso (fun i => (BigFppfOver.toScheme B S hS).map (j i)) e hje
  have hcO : ∀ i, #Γ(P0, O i) ≤ c := by
    intro i
    have hbot : O i ⊓ (⨆ k : {k // k ≠ i}, O k) = ⊥ := by
      rw [inf_iSup_eq]
      exact iSup_eq_bot.2 fun k => disjoint_iff.1
        (disjoint_opensRange_of_sigma_iso (fun i => (BigFppfOver.toScheme B S hS).map (j i)) e
          hje (Ne.symm k.2))
    have htop : O i ⊔ (⨆ k : {k // k ≠ i}, O k) = ⊤ := by
      rw [eq_top_iff, ← hcov]
      refine iSup_le fun k => ?_
      by_cases hk : k = i
      · subst hk
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup (fun k : {k // k ≠ i} => O k) ⟨k, hk⟩)
    have h := Scheme.Modules.mk_sections_le_of_inf_eq_bot P0 hbot
    rwa [htop] at h
  have hclt : c < B.cutoff := by
    rw [hc, mk_restrictToChart_sections]
    exact (hasCardinalLT_iff_cardinal_mk_lt _ _).1 (hbound _)
  set Yp := (BigFppfOver.toScheme B S hS).obj P'
  have hY : Yp.size < B.cutoff := P'.left.property
  refine ⟨max Yp.size c ^ Yp.size, power_lt_of_isStrongPrelimit B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit (max_lt hY hclt) hY, fun Ω => ?_⟩
  let M' := (modulePullback B S hS a).obj M
  let g : W0 ⟶ Wc := ObjectProperty.homMk (CostructuredArrow.homMk snd rfl)
  let cΩ := openChartRestrict B S hS Y.1 g Ω
  have hcΩ : Surjective ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS Y.1).map cΩ)) :=
    IsZariskiLocalAtTarget.restrict hsndSurj Ω
  have hinj : Function.Injective (M'.val.map cΩ.op) := by
    intro s t hst
    have hsep := Stacks.SheafOfModules.isSeparated_presheaf M' _
      (sieve_generate_singleton_chart_mem_topology B S hS Y.1 cΩ hcΩ)
    exact (Presieve.isSeparatedFor_iff_generate.mpr hsep).ext fun _ _ hg => by
      cases hg
      exact hst
  calc #(M'.val.obj (op ((openChartFunctor B S hS Y.1 Wc).obj Ω)))
      ≤ #(M'.val.obj (op ((openChartFunctor B S hS Y.1 W0).obj
          (chartSchemeMap g ⁻¹ᵁ Ω)))) := Cardinal.mk_le_of_injective hinj
    _ = #Γ(restrictToChart B S hS Y.2 M' W0, chartSchemeMap g ⁻¹ᵁ Ω) :=
        (mk_restrictToChart_sections Y M' W0 _).symm
    _ = #Γ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map fst')).obj P0,
          chartSchemeMap g ⁻¹ᵁ Ω) :=
        (Cardinal.mk_congr ((SheafOfModules.evaluation _ (op (chartSchemeMap g ⁻¹ᵁ Ω)) ⋙
          forget₂ _ AddCommGrpCat).mapIso ebc).addCommGroupIsoToAddEquiv.toEquiv).symm
    _ ≤ max Yp.size c ^ Yp.size :=
        Scheme.Modules.mk_sections_pullback_le _ P0 O hOaff hcov hcO _

end AlgebraicGeometry.Space

end
