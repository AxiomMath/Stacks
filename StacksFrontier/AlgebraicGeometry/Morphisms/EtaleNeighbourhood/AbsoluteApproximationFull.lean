module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.AffineShrinkCommonNeighborhood
public import StacksFrontier.AlgebraicGeometry.Limits.SliceEtalePairAssembly
public import StacksFrontier.AlgebraicGeometry.Limits.SmoothLimitPresentationLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CommonNeighborhoodCompletedStalkBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkClosedPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.CompletedStalkHelpers
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteTypeBaseApproximation

/-!
# Absolute approximation of a formal neighbourhood by an elementary étale neighbourhood

Let `fX : X ⟶ S` be locally of finite type over a locally Noetherian base, let `gY : Y ⟶ T` be
locally of finite type with `T` of finite type over `ℤ`, let `x ∈ X` lie over `s ∈ S` with
`𝒪_{S, s}` a G-ring, and let `σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a local homomorphism. Given a point
`yσ` of `Y ×_T Spec 𝒪^∧_{S, s}` over `y ∈ Y` and the closed point, and an isomorphism
`φ : 𝒪^∧_{X, x} ≅ 𝒪^∧_{Y ×_T Spec 𝒪^∧_{S, s}, yσ}` of `𝒪_{S, s}`-algebras, this file assembles
clauses (1)–(4) of Stacks Tag 0GDX: an elementary étale neighbourhood `V` of `(S, s)`, a morphism
`τ : V ⟶ T` carrying the marked point to `t`, a point `yτ` of `Y ×_{T, τ} V` over `y` and the
marked point, and an elementary étale neighbourhood `W` of `(Y ×_{T, τ} V, yτ)` which is étale
over `X`, trivial on residue fields over `x`, and compatible with the structure morphisms.

The composition chains the smooth limit presentation of `Spec 𝒪^∧_{S, s}` over `S`, the two
computations at the closed point of that spectrum, the base-change comparison of completed local
rings, the common étale neighbourhood produced by Artin approximation over a complete base, the
reduction to affine opens, and the descent of the whole diagram to a slice of the limit.

## Main results

* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_absoluteApproximation_full_section`:
  clauses (1)–(4) of Stacks Tag 0GDX, with the two morphisms `Spec κ(s) ⟶ T` identified.
* `AlgebraicGeometry.exists_elementaryEtaleNeighborhood_absoluteApproximation_full`: the same,
  with that identification dropped.

## Implementation notes

The cone produced by `AlgebraicGeometry`'s
`exists_cofiltered_smooth_limit_presentation_specCompletedStalk_of_isLocallyNoetherian`
has an abstract vertex together with an isomorphism from `Spec 𝒪^∧_{S, s}`; it is normalized by
`CategoryTheory.Limits.Cone.extend` along that isomorphism, so that the vertex becomes
`Spec 𝒪^∧_{S, s}` on the nose and the two computations at the closed point apply verbatim. The
morphisms `Spec 𝒪^∧_{S, s} ⟶ S` and `Spec 𝒪^∧_{S, s} ⟶ T` are almost never written out: they are
pinned by the hypotheses that mention them, so the arguments naming them are left to unification.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing StacksDraft.ArtinApproximation

universe u

namespace AlgebraicGeometry

/-- **Stacks Tag 0GDX, clauses (1)–(4), with the two morphisms `Spec κ(s) ⟶ T` identified.**
Let `fX : X ⟶ S` be locally of finite type with `S`
locally Noetherian, let `gY : Y ⟶ T` be locally of finite type with `T` of finite type over `ℤ`,
let `x ∈ X` lie over `s ∈ S` with `𝒪_{S, s}` a G-ring, and let
`σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a local homomorphism. Let `yσ` be a point of
`Y ×_T Spec 𝒪^∧_{S, s}` lying over `y ∈ Y` and over the closed point, and let
`φ : 𝒪^∧_{X, x} ≅ 𝒪^∧_{Y ×_T Spec 𝒪^∧_{S, s}, yσ}` be an isomorphism of `𝒪_{S, s}`-algebras.
Then there are an elementary étale neighbourhood `V` of `(S, s)`, a morphism `τ : V ⟶ T` carrying
the marked point to `t`, a point `yτ` of `Y ×_{T, τ} V` over `y` and over the marked point of
`V`, and an elementary étale neighbourhood `W` of `(Y ×_{T, τ} V, yτ)` together with a morphism
`F : W ⟶ X` carrying the marked point to `x` which is étale, trivial on residue fields, and
compatible with the structure morphisms to `S`; moreover the canonical section
`Spec κ(s) ⟶ Spec 𝒪^∧_{S, s}` followed by `Spec 𝒪^∧_{S, s} ⟶ T` agrees with the canonical
section `Spec κ(s) ⟶ V` followed by `τ`. -/
@[stacks 0GDX "clauses (1), (2), (3) and (4) of the conclusion, together with the commutativity \
of the source's diagram: (1) the elementary étale neighbourhood `(V, v)` of `(S, s)`; (2) the \
morphism `F : W ⟶ X` with `F(w) = x`, étale and trivial on residue fields at `w`, i.e. an \
elementary étale neighbourhood `(W, w) → (X, x)`; (3) `τ(v) = t`; and (4) the elementary étale \
neighbourhood `(W, w) → (Y ×_{T, τ} V, y_τ)`. HOW `y_τ` IS SPECIFIED -- the one part of the \
source's sentence that is NOT proved: the source takes for `y_τ` the point corresponding to \
`y_σ` under the identification `(Y_σ)_s = (Y ×_T V)_v`. Here `y_τ` is specified by lying over \
`y` and over `v`, together with the equality of the two morphisms `Spec κ(s) ⟶ T` -- one \
through `Spec 𝒪^∧_{S, s}` and `σ`, one through `V` and `τ` -- which IS that identification of \
the two fibres as one and the same scheme. That `y_τ` and `y_σ` are the same point OF that \
common fibre is not established. NO hypothesis beyond the source's is carried: Theorem 07QZ in \
particular is not, being proved as \
`StacksDraft.ArtinApproximation.localApproximationProperty`, so Tags 0CAU, 0CAV, \
07GC, 07PS, 01ZC, 01ZM, 07RP and 057G that this rests on are unconditional. Two of the source's \
hypotheses are WEAKENED, so what is proved is stronger there: `T` of finite type over \
`Spec ℤ` is only required to be LOCALLY of finite type, and `φ` is only required to be a map of \
`𝒪_{S, s}`-algebras rather than of `𝒪^∧_{S, s}`-algebras"]
public theorem exists_elementaryEtaleNeighborhood_absoluteApproximation_full_section
    {S T X Y : Scheme.{u}} [IsLocallyNoetherian S]
    (fX : X ⟶ S) (gY : Y ⟶ T) [LocallyOfFiniteType fX] [LocallyOfFiniteType gY]
    (hT : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from T))
    (x : X) (s : S) (hfx : fX x = s) (t : T) (y : Y)
    (hG : IsGRing (S.presheaf.stalk s))
    (σ : T.presheaf.stalk t →+* AdicCompletion (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s))
    (hσ : IsLocalHom σ)
    (yσ : ↥(pullback gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t)))
    (hyσ₁ : pullback.fst gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) yσ = y)
    (hyσ₂ : pullback.snd gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) yσ =
      closedPoint _)
    (φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      AdicCompletion (maximalIdeal ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
          T.fromSpecStalk t)).presheaf.stalk yσ))
        ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t)).presheaf.stalk yσ))
    (hbase : (pullback.snd gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
      S.fromSpecStalk s) yσ = s)
    (hφ : φ.toRingHom.comp ((algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (fX.stalkHomAt hfx)) =
      (algebraMap ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
            T.fromSpecStalk t)).presheaf.stalk yσ)
          (AdicCompletion (maximalIdeal ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
              T.fromSpecStalk t)).presheaf.stalk yσ))
            ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
              T.fromSpecStalk t)).presheaf.stalk yσ))).comp
        ((pullback.snd gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
            (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
          S.fromSpecStalk s).stalkHomAt hbase)) :
    ∃ V : EtaleNeighborhood S s, ∃ hVel : V.IsElementary,
      ∃ (τ : V.scheme ⟶ T) (_ : τ V.point = t),
        specResidueFieldSection (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
              (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
            S.fromSpecStalk s) (specCompletedStalkToBase_closedPoint s)
            (isIso_residueFieldMap_specCompletedStalkToBase s) ≫
            (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) =
          specResidueFieldSection V.toBase V.map_point
            ((EtaleNeighborhood.isElementary_iff V).mp hVel) ≫ τ ∧
        ∃ yτ : ↥(pullback gY τ),
          pullback.fst gY τ yτ = y ∧ pullback.snd gY τ yτ = V.point ∧
          ∃ W : EtaleNeighborhood (pullback gY τ) yτ, W.IsElementary ∧
            ∃ (F : W.scheme ⟶ X) (_ : F W.point = x),
              Etale F ∧ IsIso (F.residueFieldMap W.point) ∧
                F ≫ fX = W.toBase ≫ pullback.snd gY τ ≫ V.toBase := by
  have := hT
  have : IsLocalHom (CommRingCat.ofHom σ).hom := hσ
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.{u}.from T)
  have : IsNoetherian (Spec (CommRingCat.of (AdicCompletion
      (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) :=
    isNoetherian_Spec.mpr inferInstance
  -- (a) the smooth limit presentation, normalized so that its vertex is `Spec 𝒪^∧_{S, s}`
  obtain ⟨I, hI, hIcof, D, p, c₀, hc₀, e, haff, hsm, hcomp⟩ :=
    exists_cofiltered_smooth_limit_presentation_specCompletedStalk_of_isLocallyNoetherian s hG
  have := haff
  have hc : IsLimit (c₀.extend e.hom) := IsLimit.extendIso e.hom hc₀
  have hm := fun i => (Category.assoc e.hom (c₀.π.app i) (p.app i)).trans (hcomp i)
  -- (b) the data at the closed point of `Spec 𝒪^∧_{S, s}`
  have hz := specCompletedStalkToBase_closedPoint s
  have hzres := isIso_residueFieldMap_specCompletedStalkToBase s
  have hbT := specMap_fromSpecStalk_closedPoint (X := T) (x := t) (CommRingCat.ofHom σ)
  -- (c) the point of the base change and the common elementary étale neighbourhood
  obtain ⟨xσ, hxσ, hxσ', hbij⟩ :=
    exists_point_bijective_completionMapAt_pullback_fst fX x s hfx _ rfl
  obtain ⟨U, q, hqEt, hq, hUel, hUalong, hover⟩ :=
    exists_common_neighborhood_of_bijective_completionMapAt fX gY x s hfx t σ hσ yσ hyσ₂
      xσ hxσ hxσ' hbij 1 le_rfl φ hbase hφ
  -- (d) shrinking `X`, `Y` and the neighbourhood to affine opens
  have hqres : IsIso (q.residueFieldMap U.point) :=
    (EtaleNeighborhood.isElementary_iff (U.along q hqEt hq)).mp hUalong
  have hUres : IsIso (U.toBase.residueFieldMap U.point) :=
    (EtaleNeighborhood.isElementary_iff U).mp hUel
  obtain ⟨X', Y', jX, jY, hjX, hjY, hfpX, hfpY, U', u', jU, hjU, hjUu, al', be',
      hal'e, hbe'e, hal'res, hbe'res, hU'fp, hcomm', hal'fac, hbe'fac⟩ :=
    exists_affine_shrink_common_neighborhood fX gY _ _ U.scheme U.point q U.toBase hqEt
      inferInstance hover hqres hUres
  have := hjX
  have := hjY
  have := hjU
  -- (e) descending the whole diagram to a slice of the limit
  obtain ⟨V, v, pV, tau, hpVe, hpVres, hpVs, htau, hsec, W, w, FX', FY',
      hFXe, hFYe, hFXres, hFYres, hFsnd, hFXsndv, hFXfstx, hFYfst⟩ :=
    exists_slice_etale_pair_of_common_neighborhood_section (jX ≫ fX) (jY ≫ gY) hfpX hfpY hT _ s t
      D p (c₀.extend e.hom) hc hsm _ hm _ hz hzres _ hbT U' _ hU'fp u'
      (by
        have e2 : al' ≫ pullback.snd (jX ≫ fX) _ = jU ≫ q ≫ pullback.snd fX _ := by
          rw [← pullbackMapOver_snd fX (jX ≫ fX) jX rfl _, ← Category.assoc, hal'fac,
            Category.assoc]
        refine (congrArg (fun g : U' ⟶ _ => g u') e2).trans ?_
        change pullback.snd fX _ (q (jU u')) = _
        rw [hjUu, hq]
        exact hxσ')
      al' be' hal'e hbe'e rfl hcomm'.symm hal'res hbe'res rfl
  -- (f) packaging the result
  have := hpVe
  have := hFXe
  have := hFYe
  have : IsOpenImmersion (pullbackMapOver fX (jX ≫ fX) jX rfl pV) :=
    isOpenImmersion_pullbackMapOver fX (jX ≫ fX) jX rfl pV
  have : IsOpenImmersion (pullbackMapOver gY (jY ≫ gY) jY rfl tau) :=
    isOpenImmersion_pullbackMapOver gY (jY ≫ gY) jY rfl tau
  refine ⟨{ scheme := V, point := v, toBase := pV, etale_toBase := hpVe, map_point := hpVs },
    (EtaleNeighborhood.isElementary_iff _).mpr hpVres, tau, htau, hsec,
    (FY' ≫ pullbackMapOver gY (jY ≫ gY) jY rfl tau) w, ?_, ?_,
    { scheme := W, point := w, toBase := FY' ≫ pullbackMapOver gY (jY ≫ gY) jY rfl tau,
      etale_toBase := inferInstance, map_point := rfl },
    (EtaleNeighborhood.isElementary_iff _).mpr
      (isIso_residueFieldMap_comp_isOpenImmersion FY' _ w hFYres),
    FX' ≫ pullbackMapOver fX (jX ≫ fX) jX rfl pV ≫ pullback.fst fX pV, ?_, inferInstance,
    ?_, ?_⟩
  · -- the point of `Y ×_{T, τ} V` lies over `y`
    have hpt : pullbackMapOver gY (jY ≫ gY) jY rfl
        (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) (be' u') = yσ := by
      change (be' ≫ pullbackMapOver gY (jY ≫ gY) jY rfl _) u' = yσ
      rw [hbe'fac, Scheme.Hom.comp_apply, hjUu]
      exact U.map_point
    have hy : jY (pullback.fst (jY ≫ gY)
        (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) (be' u')) = y := by
      have e1 : pullbackMapOver gY (jY ≫ gY) jY rfl
            (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) ≫
          pullback.fst gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) =
          pullback.fst (jY ≫ gY) (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) ≫ jY :=
        pullbackMapOver_fst ..
      refine (congrArg (fun g : pullback (jY ≫ gY) _ ⟶ Y => g (be' u')) e1).symm.trans ?_
      change pullback.fst gY _ (pullbackMapOver gY (jY ≫ gY) jY rfl _ (be' u')) = y
      rw [hpt]
      exact hyσ₁
    have e2 : (FY' ≫ pullbackMapOver gY (jY ≫ gY) jY rfl tau) ≫ pullback.fst gY tau =
        FY' ≫ pullback.fst (jY ≫ gY) tau ≫ jY := by
      rw [Category.assoc, pullbackMapOver_fst]
    refine (congrArg (fun g : W ⟶ Y => g w) e2).trans ?_
    change jY (pullback.fst (jY ≫ gY) tau (FY' w)) = y
    rw [hFYfst]
    exact hy
  · -- the point of `Y ×_{T, τ} V` lies over the marked point of `V`
    have e2 : (FY' ≫ pullbackMapOver gY (jY ≫ gY) jY rfl tau) ≫ pullback.snd gY tau =
        FY' ≫ pullback.snd (jY ≫ gY) tau := by
      rw [Category.assoc, pullbackMapOver_snd]
    refine (congrArg (fun g : W ⟶ V => g w) e2).trans ?_
    rw [← hFsnd]
    exact hFXsndv
  · -- the morphism to `X` carries the marked point to `x`
    have e1 : FX' ≫ pullbackMapOver fX (jX ≫ fX) jX rfl pV ≫ pullback.fst fX pV =
        FX' ≫ pullback.fst (jX ≫ fX) pV ≫ jX := by rw [pullbackMapOver_fst]
    have e3 : al' ≫ pullback.fst (jX ≫ fX) _ ≫ jX = jU ≫ q ≫ pullback.fst fX _ := by
      rw [← pullbackMapOver_fst fX (jX ≫ fX) jX rfl _, ← Category.assoc, ← Category.assoc,
        hal'fac]
    refine (congrArg (fun g : W ⟶ X => g w) e1).trans ?_
    change jX (pullback.fst (jX ≫ fX) pV (FX' w)) = x
    rw [hFXfstx]
    refine (congrArg (fun g : U' ⟶ X => g u') e3).trans ?_
    change pullback.fst fX _ (q (jU u')) = x
    rw [hjUu, hq]
    exact hxσ
  · -- the morphism to `X` is trivial on residue fields at the marked point
    have hpt : pullback.snd fX pV (pullbackMapOver fX (jX ≫ fX) jX rfl pV (FX' w)) = v := by
      have e4 : pullbackMapOver fX (jX ≫ fX) jX rfl pV ≫ pullback.snd fX pV =
          pullback.snd (jX ≫ fX) pV := pullbackMapOver_snd ..
      exact (congrArg (fun g : pullback (jX ≫ fX) pV ⟶ V => g (FX' w)) e4).trans hFXsndv
    have hfstres : IsIso ((pullback.fst fX pV).residueFieldMap
        (pullbackMapOver fX (jX ≫ fX) jX rfl pV (FX' w))) :=
      Scheme.Pullback.isIso_residueFieldMap_fst_of_isIso_residueFieldMap fX pV _ v hpVres _
        rfl hpt
    rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso' (IsIso.comp_isIso' hfstres inferInstance) hFXres
  · -- the two structure morphisms to `S` agree
    have hlhs : (FX' ≫ pullbackMapOver fX (jX ≫ fX) jX rfl pV ≫ pullback.fst fX pV) ≫ fX =
        FX' ≫ pullback.snd (jX ≫ fX) pV ≫ pV := by
      simp only [Category.assoc, pullback.condition]
      rw [← Category.assoc (pullbackMapOver fX (jX ≫ fX) jX rfl pV), pullbackMapOver_snd]
    have hrhs : (FY' ≫ pullbackMapOver gY (jY ≫ gY) jY rfl tau) ≫
        pullback.snd gY tau ≫ pV = FY' ≫ pullback.snd (jY ≫ gY) tau ≫ pV := by
      simp only [Category.assoc]
      rw [← Category.assoc (pullbackMapOver gY (jY ≫ gY) jY rfl tau), pullbackMapOver_snd]
    rw [hlhs, hrhs, ← Category.assoc, ← Category.assoc, hFsnd]

/-- **Stacks Tag 0GDX, clauses (1)–(4).** Let `fX : X ⟶ S` be locally of finite type with `S`
locally Noetherian, let `gY : Y ⟶ T` be locally of finite type with `T` of finite type over `ℤ`,
let `x ∈ X` lie over `s ∈ S` with `𝒪_{S, s}` a G-ring, and let
`σ : 𝒪_{T, t} → 𝒪^∧_{S, s}` be a local homomorphism. Let `yσ` be a point of
`Y ×_T Spec 𝒪^∧_{S, s}` lying over `y ∈ Y` and over the closed point, and let
`φ : 𝒪^∧_{X, x} ≅ 𝒪^∧_{Y ×_T Spec 𝒪^∧_{S, s}, yσ}` be an isomorphism of `𝒪_{S, s}`-algebras.
Then there are an elementary étale neighbourhood `V` of `(S, s)`, a morphism `τ : V ⟶ T` carrying
the marked point to `t`, a point `yτ` of `Y ×_{T, τ} V` over `y` and over the marked point of
`V`, and an elementary étale neighbourhood `W` of `(Y ×_{T, τ} V, yτ)` together with a morphism
`F : W ⟶ X` carrying the marked point to `x` which is étale, trivial on residue fields, and
compatible with the structure morphisms to `S`.

This is
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_absoluteApproximation_full_section` with
the identity of the two morphisms `Spec κ(s) ⟶ T` dropped. -/
public theorem exists_elementaryEtaleNeighborhood_absoluteApproximation_full
    {S T X Y : Scheme.{u}} [IsLocallyNoetherian S]
    (fX : X ⟶ S) (gY : Y ⟶ T) [LocallyOfFiniteType fX] [LocallyOfFiniteType gY]
    (hT : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from T))
    (x : X) (s : S) (hfx : fX x = s) (t : T) (y : Y)
    (hG : IsGRing (S.presheaf.stalk s))
    (σ : T.presheaf.stalk t →+* AdicCompletion (maximalIdeal (S.presheaf.stalk s))
      (S.presheaf.stalk s))
    (hσ : IsLocalHom σ)
    (yσ : ↥(pullback gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t)))
    (hyσ₁ : pullback.fst gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) yσ = y)
    (hyσ₂ : pullback.snd gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) yσ =
      closedPoint _)
    (φ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+*
      AdicCompletion (maximalIdeal ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
          T.fromSpecStalk t)).presheaf.stalk yσ))
        ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t)).presheaf.stalk yσ))
    (hbase : (pullback.snd gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
      S.fromSpecStalk s) yσ = s)
    (hφ : φ.toRingHom.comp ((algebraMap (X.presheaf.stalk x)
        (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))).comp
          (fX.stalkHomAt hfx)) =
      (algebraMap ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
            T.fromSpecStalk t)).presheaf.stalk yσ)
          (AdicCompletion (maximalIdeal ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
              T.fromSpecStalk t)).presheaf.stalk yσ))
            ((pullback gY (Spec.map (CommRingCat.ofHom σ) ≫
              T.fromSpecStalk t)).presheaf.stalk yσ))).comp
        ((pullback.snd gY (Spec.map (CommRingCat.ofHom σ) ≫ T.fromSpecStalk t) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s)
            (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))) ≫
          S.fromSpecStalk s).stalkHomAt hbase)) :
    ∃ V : EtaleNeighborhood S s, V.IsElementary ∧
      ∃ (τ : V.scheme ⟶ T) (_ : τ V.point = t),
        ∃ yτ : ↥(pullback gY τ),
          pullback.fst gY τ yτ = y ∧ pullback.snd gY τ yτ = V.point ∧
          ∃ W : EtaleNeighborhood (pullback gY τ) yτ, W.IsElementary ∧
            ∃ (F : W.scheme ⟶ X) (_ : F W.point = x),
              Etale F ∧ IsIso (F.residueFieldMap W.point) ∧
                F ≫ fX = W.toBase ≫ pullback.snd gY τ ≫ V.toBase := by
  obtain ⟨V, hVel, τ, hτ, -, yτ, hy₁, hy₂, W, hWel, F, hF, hFet, hFres, hFcomp⟩ :=
    exists_elementaryEtaleNeighborhood_absoluteApproximation_full_section fX gY hT x s hfx t y
      hG σ hσ yσ hyσ₁ hyσ₂ φ hbase hφ
  exact ⟨V, hVel, τ, hτ, yτ, hy₁, hy₂, W, hWel, F, hF, hFet, hFres, hFcomp⟩


end AlgebraicGeometry

end
