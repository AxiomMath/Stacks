module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGluing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleOverLimit
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverEnlargement.Basic
public import StacksFrontier.AlgebraicGeometry.Gluing.Punctured
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Preimage

/-!
# Extending a finite étale cover across a point of the base

Let `f : X ⟶ S` be quasi-compact and quasi-separated with `X` locally Noetherian, `U ⊆ S` an
open and `s` a point of `S`. Write `X_s = X ×_S Spec 𝒪_{S, s}`. Suppose a finite étale cover `Y`
of `f⁻¹(U)` and a finite étale cover `Y_s` of `X_s` agree over the part of `X_s` lying over `U`.
Then `Y` extends to a finite étale cover of `f⁻¹(U ∪ W)` for some open neighbourhood `W` of `s`.

This is the gluing step of the proof of [Stacks, Tag 0EYJ], where the source uses
[Stacks, Tag 0BQ5] and [Stacks, Tag 0EY3]. Here the same descent is done directly on finite étale
covers: `X_s` is the limit of the `f⁻¹(W)` (`AlgebraicGeometry.isLimitPreimageSpecStalkCone`),
so by [Stacks, Tag 0BTV] (`AlgebraicGeometry.exists_finiteEtale_model`,
`AlgebraicGeometry.exists_finiteEtale_hom_model`) and [Stacks, Tag 081E] `Y_s` and the
comparison over `U` come from some affine `W`, and the two covers glue along `f⁻¹(U ∩ W)` by
`AlgebraicGeometry.FiniteEtaleGluing.exists_extension`.

## Main results

* `AlgebraicGeometry.exists_finiteEtale_extension_of_stalk`: the extension across `s`.
* `AlgebraicGeometry.exists_affineOpenNhds_finiteEtale_model_of_stalk`: the descent to an affine
  neighbourhood `W` of `s`.

## References

* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
* [Stacks Project, Tag 0BTV](https://stacks.math.columbia.edu/tag/0BTV)
* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- **Descending a finite étale cover of `X ×_S Spec 𝒪_{S, s}` together with its identification
over `U`** to an affine open neighbourhood `W` of `s`: there are a finite étale cover `F` of
`f⁻¹(W)` and an identification of its part over `f⁻¹(U)` with the restriction of `Y`. -/
theorem exists_affineOpenNhds_finiteEtale_model_of_stalk [IsLocallyNoetherian X] [QuasiCompact f]
    [QuasiSeparated f] (s : S) (U : S.Opens) (Y : FiniteEtaleOver (f ⁻¹ᵁ U).toScheme)
    (YO : FiniteEtaleOver (pullback f (S.fromSpecStalk s)))
    (θ : (finiteEtaleBaseChange
        (pullback.fst f (S.fromSpecStalk s) ⁻¹ᵁ (f ⁻¹ᵁ U)).ι).obj YO ≅
      (finiteEtaleBaseChange (pullback.fst f (S.fromSpecStalk s) ∣_ (f ⁻¹ᵁ U))).obj Y) :
    ∃ (W : AffineOpenNhds S s) (Ω : (f ⁻¹ᵁ W.opens).toScheme.Opens)
      (κ : Ω.toScheme ⟶ (f ⁻¹ᵁ U).toScheme) (F : FiniteEtaleOver (f ⁻¹ᵁ W.opens).toScheme),
      (Ω : Set (f ⁻¹ᵁ W.opens).toScheme) = (f ⁻¹ᵁ W.opens).ι ⁻¹' (f ⁻¹ᵁ U) ∧
      κ ≫ (f ⁻¹ᵁ U).ι = Ω.ι ≫ (f ⁻¹ᵁ W.opens).ι ∧
      Nonempty ((finiteEtaleBaseChange Ω.ι).obj F ≅ (finiteEtaleBaseChange κ).obj Y) := by
  let D := preimageAffineOpenNhdsDiagram f s
  let c := preimageSpecStalkCone f s
  have hc : IsLimit c := isLimitPreimageSpecStalkCone f s
  obtain ⟨W₁, F₁, ⟨ε₁⟩⟩ := exists_finiteEtale_model D c hc YO
  let Ω₁ : (D.obj W₁).Opens := (f ⁻¹ᵁ W₁.opens).ι ⁻¹ᵁ (f ⁻¹ᵁ U)
  have hΩ₁ : IsCompact (Ω₁ : Set (D.obj W₁)) := by
    have : IsLocallyNoetherian (D.obj W₁) :=
      inferInstanceAs (IsLocallyNoetherian (f ⁻¹ᵁ W₁.opens).toScheme)
    have : IsNoetherian (D.obj W₁) := ⟨⟩
    exact TopologicalSpace.NoetherianSpace.isCompact _
  let Dop := opensDiagram D W₁ Ω₁
  let cop := opensCone D c W₁ Ω₁
  have hcop : IsLimit cop := isLimitOpensCone D c hc W₁ Ω₁
  have (j : Over W₁) : CompactSpace (Dop.obj j) :=
    compactSpace_opensDiagram_obj_of_isCompact D W₁ Ω₁ hΩ₁ j
  have (j : Over W₁) : QuasiSeparatedSpace (Dop.obj j) :=
    quasiSeparatedSpace_opensDiagram_obj D W₁ Ω₁ j
  -- the maps from the stages of the restricted system to `f⁻¹(U)`
  have hrange (j : Over W₁) : Set.range ((D.map j.hom ⁻¹ᵁ Ω₁).ι ≫ (f ⁻¹ᵁ j.left.opens).ι) ⊆
      Set.range (f ⁻¹ᵁ U).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hx := x.2
    change (D.map j.hom ≫ (f ⁻¹ᵁ W₁.opens).ι) x.1 ∈ f ⁻¹ᵁ U at hx
    rw [preimageAffineOpenNhdsDiagram_map_ι] at hx
    exact hx
  let κ (j : Over W₁) : (D.map j.hom ⁻¹ᵁ Ω₁).toScheme ⟶ (f ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.lift (f ⁻¹ᵁ U).ι _ (hrange j)
  have hκ (j : Over W₁) : κ j ≫ (f ⁻¹ᵁ U).ι =
      (D.map j.hom ⁻¹ᵁ Ω₁).ι ≫ (f ⁻¹ᵁ j.left.opens).ι :=
    IsOpenImmersion.lift_fac _ _ _
  -- the comparison over the limit
  let j₀ : Over W₁ := Over.mk (𝟙 W₁)
  let Ω₀ : (f ⁻¹ᵁ W₁.opens).toScheme.Opens := D.map j₀.hom ⁻¹ᵁ Ω₁
  -- `κ j₀` followed by `f⁻¹(U) ⟶ X` is computed through any square over `f⁻¹(W₁)`
  have hκ₀ {Z V : Scheme.{u}} (a : Z ⟶ Ω₀.toScheme) (b : Z ⟶ V) (q : V ⟶ (f ⁻¹ᵁ W₁.opens).toScheme)
      (ιV : V ⟶ X) (hq : q ≫ (f ⁻¹ᵁ W₁.opens).ι = ιV) (h : a ≫ Ω₀.ι = b ≫ q) :
      (a ≫ κ j₀) ≫ (f ⁻¹ᵁ U).ι = b ≫ ιV :=
    (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (hκ j₀)).trans
      (by erw [← Category.assoc, h, Category.assoc, hq]))
  let A : FiniteEtaleOver Ω₀.toScheme := (finiteEtaleBaseChange Ω₀.ι).obj F₁
  let B : FiniteEtaleOver Ω₀.toScheme := (finiteEtaleBaseChange (κ j₀)).obj Y
  let XP := pullback.fst f (S.fromSpecStalk s) ⁻¹ᵁ (f ⁻¹ᵁ U)
  let k := pullback.fst f (S.fromSpecStalk s) ∣_ (f ⁻¹ᵁ U)
  let leg : pullback f (S.fromSpecStalk s) ⟶ (f ⁻¹ᵁ W₁.opens).toScheme := c.π.app W₁
  have hleg : leg ≫ (f ⁻¹ᵁ W₁.opens).ι = pullback.fst f (S.fromSpecStalk s) :=
    preimageSpecStalkLeg_ι f s W₁
  let T : (pullback f (S.fromSpecStalk s)).Opens := leg ⁻¹ᵁ Ω₁
  have hTX : T ≤ XP := by
    intro x hx
    change (leg ≫ (f ⁻¹ᵁ W₁.opens).ι) x ∈ f ⁻¹ᵁ U at hx
    rw [hleg] at hx
    exact hx
  let m := (pullback f (S.fromSpecStalk s)).homOfLE hTX
  let π₀ : T.toScheme ⟶ Ω₀.toScheme := cop.π.app j₀
  have e1 : T.ι ≫ leg = π₀ ≫ Ω₀.ι := (Scheme.Hom.resLE_comp_ι _ _).symm
  have e2 : π₀ ≫ κ j₀ = m ≫ k := by
    apply (cancel_mono (f ⁻¹ᵁ U).ι).1
    have h1 : (π₀ ≫ κ j₀) ≫ (f ⁻¹ᵁ U).ι = T.ι ≫ pullback.fst f (S.fromSpecStalk s) :=
      hκ₀ _ _ leg _ hleg e1.symm
    have h2 : (m ≫ k) ≫ (f ⁻¹ᵁ U).ι = T.ι ≫ pullback.fst f (S.fromSpecStalk s) := by
      rw [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
    exact h1.trans h2.symm
  let ψ : (finiteEtaleBaseChange π₀).obj A ≅ (finiteEtaleBaseChange π₀).obj B :=
    (finiteEtaleBaseChangeComp π₀ Ω₀.ι (T.ι ≫ leg) e1).symm.app F₁ ≪≫
    (finiteEtaleBaseChangeComp T.ι leg _ rfl).app F₁ ≪≫
    (finiteEtaleBaseChange T.ι).mapIso ε₁.symm ≪≫
    (finiteEtaleBaseChangeComp m XP.ι T.ι (Scheme.homOfLE_ι _ _).symm).app YO ≪≫
    (finiteEtaleBaseChange m).mapIso θ ≪≫
    (finiteEtaleBaseChangeComp m k (π₀ ≫ κ j₀) e2).symm.app Y ≪≫
    (finiteEtaleBaseChangeComp π₀ (κ j₀) _ rfl).app Y
  obtain ⟨j, e, χ, hχ⟩ := exists_finiteEtale_hom_model Dop cop hcop j₀ A B ψ.hom
  -- `χ` becomes an isomorphism at a later stage
  have hχiso : IsIso ((finiteEtaleBaseChange (cop.π.app j)).map χ) := by
    let cA := (finiteEtaleLimitCompIso Dop cop e).app A
    let cB := (finiteEtaleLimitCompIso Dop cop e).app B
    have h0 : cA.hom ≫ (finiteEtaleBaseChange (cop.π.app j)).map χ ≫ cB.inv = ψ.hom := hχ.symm
    have h : (finiteEtaleBaseChange (cop.π.app j)).map χ = (cA.inv ≫ ψ.hom) ≫ cB.hom :=
      (Iso.comp_inv_eq cB).1 ((Iso.eq_inv_comp cA).2 h0)
    rw [h]
    exact Iso.isIso_hom ((cA.symm ≪≫ ψ) ≪≫ cB)
  let A' := (finiteEtaleBaseChange (Dop.map e)).obj A
  let B' := (finiteEtaleBaseChange (Dop.map e)).obj B
  let χo : Over.mk A'.hom ⟶ Over.mk B'.hom := Over.homMk χ.left (MorphismProperty.Over.w χ)
  have : IsIso ((Over.pullback (cop.π.app j)).map χo).left :=
    (inferInstance : IsIso ((MorphismProperty.Over.forget finiteEtale ⊤ _ ⋙ Over.forget _).map
      ((finiteEtaleBaseChange (cop.π.app j)).map χ)))
  have hAB (P : FiniteEtaleOver (Dop.obj j)) :
      CompactSpace (Over.mk P.hom).left ∧ QuasiSeparatedSpace (Over.mk P.hom).left := by
    have : IsFinite P.hom := P.prop.1
    have : Etale P.hom := P.prop.2
    exact ⟨@QuasiCompact.compactSpace_of_compactSpace _ (Dop.obj j) P.hom _ inferInstance,
      @quasiSeparatedSpace_of_quasiSeparated _ (Dop.obj j) P.hom inferInstance _⟩
  have : Etale A'.hom := A'.prop.2
  have : Etale B'.hom := B'.prop.2
  obtain ⟨_, _⟩ := hAB A'
  obtain ⟨_, _⟩ := hAB B'
  have : Etale χo.left := MorphismProperty.of_postcomp @Etale (W' := @Etale) χ.left B'.hom
    inferInstance (by rw [MorphismProperty.Over.w χ]; infer_instance)
  obtain ⟨kk, g, hk⟩ := exists_isIso_baseChange_of_isIso_limitBaseChange Dop cop hcop j
    (Over.mk A'.hom) (Over.mk B'.hom) χo
  have : IsIso ((finiteEtaleBaseChange (Dop.map g)).map χ).left := hk
  let Φ : (finiteEtaleBaseChange (Dop.map g)).obj A' ≅ (finiteEtaleBaseChange (Dop.map g)).obj B' :=
    MorphismProperty.Over.isoMk (asIso ((finiteEtaleBaseChange (Dop.map g)).map χ).left)
      (MorphismProperty.Over.w _)
  -- back to `f⁻¹(W)` for the final stage `W`
  let Ω : (f ⁻¹ᵁ kk.left.opens).toScheme.Opens := D.map kk.hom ⁻¹ᵁ Ω₁
  have hleft : D.map (g ≫ e).left = D.map kk.hom :=
    congrArg D.map ((Category.comp_id _).symm.trans (Over.w (g ≫ e)))
  have h1 : Dop.map (g ≫ e) ≫ Ω₀.ι = Ω.ι ≫ D.map kk.hom :=
    (Scheme.Hom.resLE_comp_ι _ _).trans (congrArg (Ω.ι ≫ ·) hleft)
  have h2 : κ kk = Dop.map (g ≫ e) ≫ κ j₀ := by
    apply (cancel_mono (f ⁻¹ᵁ U).ι).1
    exact (hκ kk).trans (hκ₀ _ _ _ _ (preimageAffineOpenNhdsDiagram_map_ι f s kk.hom) h1).symm
  refine ⟨kk.left, Ω, κ kk, (finiteEtaleBaseChange (D.map kk.hom)).obj F₁, ?_, hκ kk, ⟨?_⟩⟩
  · ext x
    change (D.map kk.hom ≫ (f ⁻¹ᵁ W₁.opens).ι) x ∈ f ⁻¹ᵁ U ↔ _
    rw [preimageAffineOpenNhdsDiagram_map_ι]
    rfl
  · exact (finiteEtaleBaseChangeComp Ω.ι (D.map kk.hom) _ h1).symm.app F₁ ≪≫
      (finiteEtaleBaseChangeComp (Dop.map (g ≫ e)) Ω₀.ι _ rfl).app F₁ ≪≫
      (finiteEtaleBaseChangeComp (Dop.map g) (Dop.map e) (Dop.map (g ≫ e))
        (Dop.map_comp g e)).app A ≪≫ Φ ≪≫
      (finiteEtaleBaseChangeComp (Dop.map g) (Dop.map e) (Dop.map (g ≫ e))
        (Dop.map_comp g e)).symm.app B ≪≫
      (finiteEtaleBaseChangeComp (Dop.map (g ≫ e)) (κ j₀) (κ kk) h2).symm.app Y

/-- **Extending a finite étale cover across a point of the base.** Let `f : X ⟶ S` be flat,
quasi-compact and quasi-separated, from a normal locally Noetherian scheme to an integral scheme,
and let `U ⊆ S` be an open containing the generic point. If a finite étale cover `Y` of `f⁻¹(U)`
agrees over `U` with a finite étale cover of `X ×_S Spec 𝒪_{S, s}`, then `Y` extends to a finite
étale cover of `f⁻¹(U ∪ W)` for some open neighbourhood `W` of `s`. -/
theorem exists_finiteEtale_extension_of_stalk [IsIntegral S] [IsLocallyNoetherian X] [IsNormal X]
    [Flat f] [QuasiCompact f] [QuasiSeparated f] (s : S) (U : S.Opens)
    (hη : genericPoint S ∈ U) (Y : FiniteEtaleOver (f ⁻¹ᵁ U).toScheme)
    (YO : FiniteEtaleOver (pullback f (S.fromSpecStalk s)))
    (θ : (finiteEtaleBaseChange
        (pullback.fst f (S.fromSpecStalk s) ⁻¹ᵁ (f ⁻¹ᵁ U)).ι).obj YO ≅
      (finiteEtaleBaseChange (pullback.fst f (S.fromSpecStalk s) ∣_ (f ⁻¹ᵁ U))).obj Y) :
    ∃ W : S.Opens, s ∈ W ∧ ∃ F : FiniteEtaleOver (f ⁻¹ᵁ (U ⊔ W)).toScheme,
      Nonempty ((finiteEtaleBaseChange (X.homOfLE (f.preimage_mono
        (le_sup_left : U ≤ U ⊔ W)))).obj F ≅ Y) := by
  obtain ⟨W, Ω, κ, F₂, hΩ, hκ, ⟨Φ₂⟩⟩ :=
    exists_affineOpenNhds_finiteEtale_model_of_stalk f s U Y YO θ
  refine ⟨W.opens, W.mem_opens, ?_⟩
  let U' := U ⊔ W.opens
  let X' := (f ⁻¹ᵁ U').toScheme
  let OU : X'.Opens := (f ⁻¹ᵁ U').ι ⁻¹ᵁ (f ⁻¹ᵁ U)
  let OW : X'.Opens := (f ⁻¹ᵁ U').ι ⁻¹ᵁ (f ⁻¹ᵁ W.opens)
  let r : OU.toScheme ⟶ (f ⁻¹ᵁ U).toScheme := (f ⁻¹ᵁ U').ι ∣_ (f ⁻¹ᵁ U)
  let E : FiniteEtaleOver OU.toScheme := (finiteEtaleBaseChange r).obj Y
  -- restriction to the part over `U` is fully faithful on every open of `f⁻¹(U')`
  have hff : ∀ W' : X'.Opens,
      Nonempty (finiteEtaleBaseChange (FiniteEtaleGluing.part OU W').ι).FullyFaithful := by
    intro W'
    refine nonempty_fullyFaithful_finiteEtaleBaseChange_of_isNormal _ fun w ↦ ?_
    obtain ⟨x', hx'w, hfx'⟩ := Flat.generalizingMap f (genericPoint_specializes (f w.1.1))
    have hx'U' : x' ∈ f ⁻¹ᵁ U' := hx'w.mem_open (f ⁻¹ᵁ U').isOpen w.1.2
    have h1 : (⟨x', hx'U'⟩ : X') ⤳ w.1 :=
      (Topology.IsInducing.subtypeVal.specializes_iff).mp hx'w
    have hx'W' : (⟨x', hx'U'⟩ : X') ∈ W' := h1.mem_open W'.isOpen w.2
    have h2 : (⟨⟨x', hx'U'⟩, hx'W'⟩ : W'.toScheme) ⤳ w :=
      (Topology.IsInducing.subtypeVal.specializes_iff).mp h1
    refine h2.mem_closed isClosed_closure (subset_closure ?_)
    change f x' ∈ U
    rw [hfx']
    exact hη
  -- every point has a neighbourhood over which `E` extends
  have hloc : ∀ x : X', ∃ W' : X'.Opens, x ∈ W' ∧ Nonempty (FiniteEtaleGluing.Ext OU E W') := by
    intro x
    rcases x.2 with hxU | hxW
    · exact ⟨OU, hxU, ⟨FiniteEtaleGluing.Ext.self E⟩⟩
    refine ⟨OW, hxW, ⟨?_⟩⟩
    let ρ : OW.toScheme ⟶ (f ⁻¹ᵁ W.opens).toScheme := (f ⁻¹ᵁ U').ι ∣_ (f ⁻¹ᵁ W.opens)
    let P := FiniteEtaleGluing.part OU OW
    have hPΩ : P ≤ ρ ⁻¹ᵁ Ω := by
      intro v hv
      change ρ v ∈ (Ω : Set (f ⁻¹ᵁ W.opens).toScheme)
      rw [hΩ]
      change (ρ ≫ (f ⁻¹ᵁ W.opens).ι) v ∈ f ⁻¹ᵁ U
      rw [morphismRestrict_ι]
      exact hv
    let τ : P.toScheme ⟶ Ω.toScheme := ρ.resLE Ω P hPΩ
    have hτ : τ ≫ Ω.ι = P.ι ≫ ρ := Scheme.Hom.resLE_comp_ι _ _
    have hlam : (OW.ι ∣_ OU) ≫ r = τ ≫ κ := by
      apply (cancel_mono (f ⁻¹ᵁ U).ι).1
      rw [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, Category.assoc, hκ,
        ← Category.assoc τ, hτ, Category.assoc, morphismRestrict_ι]
    let F : FiniteEtaleOver OW.toScheme := (finiteEtaleBaseChange ρ).obj F₂
    have sqa : IsPullback (pullback.fst F.hom P.ι ≫ pullback.fst F₂.hom ρ)
        (pullback.snd F.hom P.ι) F₂.hom (P.ι ≫ ρ) :=
      (IsPullback.of_hasPullback F.hom P.ι).paste_horiz (IsPullback.of_hasPullback F₂.hom ρ)
    let Φ₂L : pullback F₂.hom Ω.ι ≅ pullback Y.hom κ :=
      (MorphismProperty.Over.forget finiteEtale ⊤ _ ⋙ Over.forget _).mapIso Φ₂
    have hΦ₂ : Φ₂L.hom ≫ pullback.snd Y.hom κ = pullback.snd F₂.hom Ω.ι :=
      MorphismProperty.Over.w Φ₂.hom
    have sqb : IsPullback (Φ₂L.hom ≫ pullback.fst Y.hom κ) (pullback.snd F₂.hom Ω.ι)
        Y.hom κ :=
      IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition,
        ← Category.assoc, hΦ₂]⟩ Φ₂L rfl hΦ₂
    let l : pullback F.hom P.ι ⟶ pullback F₂.hom Ω.ι :=
      pullback.lift (pullback.fst F.hom P.ι ≫ pullback.fst F₂.hom ρ)
        (pullback.snd F.hom P.ι ≫ τ) (by rw [sqa.w, Category.assoc, hτ])
    have sqc : IsPullback l (pullback.snd F.hom P.ι) (pullback.snd F₂.hom Ω.ι) τ := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
        (IsPullback.of_hasPullback F₂.hom Ω.ι)
      rw [pullback.lift_fst, hτ]
      exact sqa
    have sqd := sqc.paste_horiz sqb
    rw [← hlam] at sqd
    let Θ := l ≫ Φ₂L.hom ≫ pullback.fst Y.hom κ
    let θ' : pullback F.hom P.ι ⟶ pullback Y.hom r :=
      pullback.lift Θ (pullback.snd F.hom P.ι ≫ (OW.ι ∣_ OU))
        (by rw [sqd.w, Category.assoc])
    refine ⟨F, θ', ?_⟩
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback Y.hom r)
    convert sqd using 1
    exact pullback.lift_fst _ _ _
  obtain ⟨Fg, ⟨eg⟩⟩ := FiniteEtaleGluing.exists_extension (U := OU) (E := E) hff hloc
  let j := X.homOfLE (f.preimage_mono (le_sup_left : U ≤ U'))
  have hj : Set.range j ⊆ Set.range OU.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ((X.homOfLE _) ≫ (f ⁻¹ᵁ U').ι) x ∈ f ⁻¹ᵁ U
    rw [Scheme.homOfLE_ι]
    exact x.2
  let rinv : (f ⁻¹ᵁ U).toScheme ⟶ OU.toScheme := IsOpenImmersion.lift OU.ι j hj
  have hrinv : rinv ≫ OU.ι = j := IsOpenImmersion.lift_fac _ _ _
  have hrr : rinv ≫ r = 𝟙 _ := by
    rw [← cancel_mono (f ⁻¹ᵁ U).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hrinv,
      Scheme.homOfLE_ι, Category.id_comp]
  refine ⟨Fg, ⟨(finiteEtaleBaseChangeComp rinv OU.ι j hrinv.symm).app Fg ≪≫
    (finiteEtaleBaseChange rinv).mapIso eg ≪≫
    (finiteEtaleBaseChangeComp rinv r (𝟙 _) hrr.symm).symm.app Y ≪≫
    finiteEtaleBaseChangeId.app Y⟩⟩

end AlgebraicGeometry
