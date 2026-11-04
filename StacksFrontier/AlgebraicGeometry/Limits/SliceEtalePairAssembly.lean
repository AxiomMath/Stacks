module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtalePairBare
public import StacksFrontier.AlgebraicGeometry.Limits.EtalePairOnSlice
public import StacksFrontier.AlgebraicGeometry.Limits.SliceStageOfSmoothLimit
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.SpecResidueFieldSection

/-!
# The slice and the common étale neighbourhood on it

This file assembles the proof of Stacks Tag 0GDX out of the three steps that precede it. The
input is

* a smooth limit presentation of `Spec(𝒪^∧_{S,s})`: a cofiltered diagram `D` of affine schemes
  smooth over a locally Noetherian `S`, with limit cone `c`, induced morphism `m : c.pt ⟶ S` and
  a point `z` over `s` at which `m` is trivial on residue fields;
* a morphism `bT : c.pt ⟶ T` carrying `z` to `t`, with `T` locally of finite type over `Spec ℤ`;
* a *common étale neighbourhood over the limit*: a scheme `Usch` of finite presentation over
  `c.pt` with a point `u` over `z` and two étale morphisms `al : Usch ⟶ X ×_S c.pt` and
  `be : Usch ⟶ Y ×_T c.pt`, both over `c.pt` and both trivial on residue fields at `u`, with
  `al u` lying over the prescribed point `x` of `X`.

The output is clauses (1)–(4) of the tag: an elementary étale neighbourhood `(V, v)` of `(S, s)`,
a morphism `tau : V ⟶ T` with `tau v = t`, and a scheme `W` with a point `w` carrying two étale
morphisms, trivial on residue fields at `w`, into `X ×_S V` and `Y ×_T V` which agree on `V`.

## Main results

* `AlgebraicGeometry.exists_slice_etale_pair_of_common_neighborhood_section`: clauses (1)–(4)
  together with the identity of the two morphisms `Spec κ(s) ⟶ T` — one through the limit and
  `bT`, one through the slice and `tau`. That identity makes the fibres `(Y_{bT})_s` and
  `(Y ×_{T,tau} V)_v` literally the same scheme, which is the identification the source uses to
  pin down its point.
* `AlgebraicGeometry.exists_slice_etale_pair_of_common_neighborhood`: clauses (1)–(4) alone,
  obtained from it by forgetting that identity.

## Implementation notes

The assembly is: descend `bT` to a stage `j`
(`AlgebraicGeometry.exists_stage_morphism_of_locallyOfFiniteTypeOverZ_apply`), descend the étale
pair to a later stage `j'` (`AlgebraicGeometry.exists_stage_etale_pair_bare`), cut the slice
`i : V ⟶ D.obj j'` through the image of `z`
(`AlgebraicGeometry.exists_slice_at_stage`) and take for `W` the inverse image `U' ×_{D.obj j'} V`
of the slice in the descended neighbourhood, as in
`AlgebraicGeometry.exists_point_etale_pair_on_slice`. The scheme `W` and the two morphisms are
spelled out here rather than taken from that lemma because the two *first* projections are needed
as well, to identify the images of `w` in `X` and in `Y`, and those are not part of its
conclusion.

The only step with content beyond bookkeeping is the triviality of the residue field extensions
of the descended pair at the descended point. It is handled uniformly on both sides by
`AlgebraicGeometry.pullbackFactorComparison`, the comparison `X ×_T C ⟶ X ×_T D` attached to a
factorization `C ⟶ D ⟶ T` presented as an equation of morphisms rather than as a composite, so
that no type has to be rewritten: the comparison is the base change of `C ⟶ D` along
`X ×_T D ⟶ D`, hence trivial on residue fields above any point of `C` at which `C ⟶ D` is
(`AlgebraicGeometry.isIso_residueFieldMap_pullbackFactorComparison`), and the descended morphism
composed with the morphism to the later stage *is* the given morphism composed with the
comparison.

For the `Y`-side this detour is not optional: the residue field extension `κ(t) → κ(z)` of `bT` is
in general nontrivial, so the first projection `Y ×_T c.pt ⟶ Y` is not trivial on residue fields
at `be u`, while the projection `c.pt ⟶ D.obj j'` to a stage is trivial on residue fields at `z`
because `m` is.

The hypothesis `pU u = z` — the point of the common neighbourhood lies over the distinguished
point of the limit — is needed twice: to place `pullback.snd fX m (al u)` and
`pullback.snd gY bT (be u)` at `z`, which is where the residue field of `m` is known to be
trivial, and to place the image of `u` in `D.obj j'` on the slice.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section FactorComparison

variable {Y T Dj C : Scheme.{u}} (f : Y ⟶ T) (q : Dj ⟶ T) (k : C ⟶ Dj) (n : C ⟶ T)
  (hn : k ≫ q = n)

/-- The comparison morphism `Y ×_T C ⟶ Y ×_T Dj` attached to a factorization of `n : C ⟶ T` as
`k : C ⟶ Dj` followed by `q : Dj ⟶ T`. Unlike
`AlgebraicGeometry.pullbackComparison` the factorization is given as an equation of morphisms, so
that the source is the fibre product along `n` on the nose. -/
public def pullbackFactorComparison : pullback f n ⟶ pullback f q :=
  pullback.lift (pullback.fst f n) (pullback.snd f n ≫ k)
    (by rw [Category.assoc, hn]; exact pullback.condition)

/-- The comparison morphism read through the first projections. -/
@[reassoc (attr := simp)]
public lemma pullbackFactorComparison_fst :
    pullbackFactorComparison f q k n hn ≫ pullback.fst f q = pullback.fst f n :=
  pullback.lift_fst _ _ _

/-- The comparison morphism read through the second projections. -/
@[reassoc (attr := simp)]
public lemma pullbackFactorComparison_snd :
    pullbackFactorComparison f q k n hn ≫ pullback.snd f q = pullback.snd f n ≫ k :=
  pullback.lift_snd _ _ _

/-- The comparison morphism is the base change of `k : C ⟶ Dj` along `Y ×_T Dj ⟶ Dj`, read
through `AlgebraicGeometry.pullbackSndPullbackIso`. -/
public theorem pullbackFactorComparison_eq :
    pullbackFactorComparison f q k n hn =
      (pullbackSndPullbackIso f q k n hn).inv ≫ pullback.fst (pullback.snd f q) k := by
  refine pullback.hom_ext ?_ ?_
  · rw [pullbackFactorComparison_fst, Category.assoc, pullbackSndPullbackIso_inv_fst]
  · rw [pullbackFactorComparison_snd, Category.assoc,
      pullback.condition (f := pullback.snd f q) (g := k),
      pullbackSndPullbackIso_inv_snd_assoc]

/-- **The comparison morphism is trivial on residue fields above a point of `C` at which the
factor `k` is.** -/
public theorem isIso_residueFieldMap_pullbackFactorComparison (w : ↥(pullback f n)) (ζ : C)
    (hw : pullback.snd f n w = ζ) (hk : IsIso (k.residueFieldMap ζ)) :
    IsIso ((pullbackFactorComparison f q k n hn).residueFieldMap w) := by
  set ee := (pullbackSndPullbackIso f q k n hn).inv with hee
  have hpt : pullback.snd (pullback.snd f q) k (ee w) = ζ := by
    have h1 : pullback.snd (pullback.snd f q) k (ee w) =
        (ee ≫ pullback.snd (pullback.snd f q) k) w := rfl
    rw [h1, hee, pullbackSndPullbackIso_inv_snd]
    exact hw
  have hmain : IsIso ((pullback.fst (pullback.snd f q) k).residueFieldMap (ee w)) :=
    Scheme.Pullback.isIso_residueFieldMap_fst_of_isIso_residueFieldMap (pullback.snd f q) k _ ζ
      hk (ee w) rfl hpt
  have hee' : IsIso (ee.residueFieldMap w) := by rw [hee]; infer_instance
  rw [pullbackFactorComparison_eq, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' hmain hee'

include hn in
/-- **Triviality of the residue field extension descends along the comparison morphism.** If
`al : U ⟶ Y ×_T C` and `a' : U' ⟶ Y ×_T Dj` are morphisms over `C` and `Dj` and `psi : U ⟶ U'`
makes them agree on the projections to `Y` and to the bases, then triviality of the residue field
extension of `al` at a point `uu` of `U` over a point `ζ` of `C` at which `k` is trivial on
residue fields implies triviality of the residue field extension of `a'` at `psi uu`. -/
public theorem isIso_residueFieldMap_of_pullbackFactorComparison_eq {U U' : Scheme.{u}}
    (pU : U ⟶ C) (pU' : U' ⟶ Dj) (al : U ⟶ pullback f n) (a' : U' ⟶ pullback f q) (psi : U ⟶ U')
    (hal : al ≫ pullback.snd f n = pU) (ha' : a' ≫ pullback.snd f q = pU')
    (hpsiU : psi ≫ pU' = pU ≫ k)
    (hpsia : psi ≫ a' ≫ pullback.fst f q = al ≫ pullback.fst f n)
    (uu : U) (ζ : C) (hpU : pU uu = ζ) (hk : IsIso (k.residueFieldMap ζ))
    (hres : IsIso (al.residueFieldMap uu)) :
    IsIso (a'.residueFieldMap (psi uu)) := by
  have hsnd : pullback.snd f n (al uu) = ζ := by
    have h1 : pullback.snd f n (al uu) = (al ≫ pullback.snd f n) uu := rfl
    rw [h1, hal, hpU]
  have hcmp : IsIso ((pullbackFactorComparison f q k n hn).residueFieldMap (al uu)) :=
    isIso_residueFieldMap_pullbackFactorComparison f q k n hn (al uu) ζ hsnd hk
  have heq : psi ≫ a' = al ≫ pullbackFactorComparison f q k n hn := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, pullbackFactorComparison_fst]
      exact hpsia
    · rw [Category.assoc, Category.assoc, pullbackFactorComparison_snd, ha', hpsiU,
        ← Category.assoc, hal]
  refine isIso_residueFieldMap_of_isIso_residueFieldMap_comp psi a' uu ?_
  rw [heq, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' hcmp hres

end FactorComparison

/-- Base change of a descended étale morphism `a' : U' ⟶ Y ×_B Dj` over `Dj` along a slice
`i : V ⟶ Dj` is an étale morphism `U' ×_Dj V ⟶ Y ×_B V` that is trivial on residue fields above
points where `a'` is. -/
private theorem exists_etale_pullback_slice_morphism {Y B Dj U' V : Scheme.{u}} (f : Y ⟶ B)
    (q : Dj ⟶ B) (pU' : U' ⟶ Dj) (a' : U' ⟶ pullback f q) (he : Etale a')
    (ha : a' ≫ pullback.snd f q = pU') (i : V ⟶ Dj) (uu : U') (w : ↥(pullback pU' i))
    (hw : pullback.fst pU' i w = uu) (hres : IsIso (a'.residueFieldMap uu)) :
    ∃ F : pullback pU' i ⟶ pullback f (i ≫ q), Etale F ∧ IsIso (F.residueFieldMap w) ∧
      F ≫ pullback.snd f (i ≫ q) = pullback.snd pU' i ∧
      pullback.fst f (i ≫ q) (F w) = pullback.fst f q (a' uu) := by
  refine ⟨pullbackMapOver (pullback.snd f q) pU' a' ha i ≫
    (pullbackLeftPullbackSndIso f q i).hom, ?_, ?_, ?_, ?_⟩
  · have := etale_pullbackMapOver (pullback.snd f q) pU' a' ha i
    infer_instance
  · exact isIso_residueFieldMap_comp_isOpenImmersion _ _ w
      (isIso_residueFieldMap_pullbackMapOver (pullback.snd f q) pU' a' ha i uu w hw hres)
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullbackMapOver_snd]
  · rw [← Scheme.Hom.comp_apply, Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      ← Category.assoc, pullbackMapOver_fst, Category.assoc, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, hw]

/-- **Tag 0GDX, clauses (1)–(4), with the two morphisms `Spec κ(s) ⟶ T` identified.** From a
smooth limit presentation of `Spec(𝒪^∧_{S,s})` over `S` and a common étale neighbourhood over that
limit, the slice `V`, the morphism `tau : V ⟶ T` and the scheme `W` with its point, together with
the identity of the composite of the canonical section `Spec κ(s) ⟶ c.pt` with `bT` and of the
canonical section `Spec κ(s) ⟶ V` with `tau`. -/
public theorem exists_slice_etale_pair_of_common_neighborhood_section
    {S T X Y : Scheme.{u}} [IsLocallyNoetherian S]
    (fX : X ⟶ S) (gY : Y ⟶ T) [LocallyOfFiniteType fX] [LocallyOfFiniteType gY]
    (hfp : FinitePresentation fX) (hgp : FinitePresentation gY)
    (hT : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from T))
    (x : X) (s : S) (t : T)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)]
    (hsm : ∀ i, Smooth (p.app i))
    (m : c.pt ⟶ S) (hm : ∀ i, c.π.app i ≫ p.app i = m)
    (z : c.pt) (hz : m z = s) (hzres : IsIso (m.residueFieldMap z))
    (bT : c.pt ⟶ T) (hbT : bT z = t)
    (Usch : Scheme.{u}) (pU : Usch ⟶ c.pt) (hUfp : FinitePresentation pU) (u : Usch)
    (hpUz : pU u = z)
    (al : Usch ⟶ pullback fX m) (be : Usch ⟶ pullback gY bT)
    (hale : Etale al) (hbee : Etale be)
    (hal : al ≫ pullback.snd fX m = pU) (hbe : be ≫ pullback.snd gY bT = pU)
    (halres : IsIso (al.residueFieldMap u)) (hberes : IsIso (be.residueFieldMap u))
    (halx : pullback.fst fX m (al u) = x) :
    ∃ (V : Scheme.{u}) (v : V) (pV : V ⟶ S) (tau : V ⟶ T)
      (hpVe : Etale pV) (hpVres : IsIso (pV.residueFieldMap v)) (hpVs : pV v = s),
      tau v = t ∧
      specResidueFieldSection m hz hzres ≫ bT =
        specResidueFieldSection pV hpVs hpVres ≫ tau ∧
      ∃ (W : Scheme.{u}) (w : W) (FX : W ⟶ pullback fX pV) (FY : W ⟶ pullback gY tau),
        Etale FX ∧ Etale FY ∧
          IsIso (FX.residueFieldMap w) ∧ IsIso (FY.residueFieldMap w) ∧
            FX ≫ pullback.snd fX pV = FY ≫ pullback.snd gY tau ∧
              pullback.snd fX pV (FX w) = v ∧
                pullback.fst fX pV (FX w) = x ∧
                  pullback.fst gY tau (FY w) = pullback.fst gY bT (be u) := by
  -- The projection from the limit to any stage is trivial on residue fields at `z`.
  have hkz : ∀ i : I, IsIso ((c.π.app i).residueFieldMap z) := fun i =>
    isIso_residueFieldMap_left_of_isIso_residueFieldMap_comp (c.π.app i) (p.app i) z
      (by rw [hm i]; exact hzres)
  -- Step 1: descend `bT` to a stage.
  obtain ⟨j, tj, htj, htjz⟩ :=
    exists_stage_morphism_of_locallyOfFiniteTypeOverZ_apply D p c hc m hm
      (fun i => inferInstance) hT bT z
  -- Step 2: descend the étale pair to a later stage.
  obtain ⟨j', e, U', pU', a', b', ha'e, hb'e, ha'sn, hb'sn, psi, hpsia, hpsib, hpsiU⟩ :=
    exists_stage_etale_pair_bare fX gY hfp hgp D p c hc m hm j tj bT htj Usch pU hUfp al be
      hal hbe hale hbee
  have hbTfac : c.π.app j' ≫ D.map e ≫ tj = bT := by
    rw [← Category.assoc, c.w e]; exact htj
  -- Step 3: the descended point and its residue fields.
  have hpU'u : pU' (psi u) = c.π.app j' z := by
    have h1 : pU' (psi u) = (psi ≫ pU') u := rfl
    rw [h1, hpsiU, Scheme.Hom.comp_apply, hpUz]
  have ha'res : IsIso (a'.residueFieldMap (psi u)) :=
    isIso_residueFieldMap_of_pullbackFactorComparison_eq fX (p.app j') (c.π.app j') m (hm j')
      pU pU' al a' psi hal ha'sn hpsiU hpsia u z hpUz (hkz j') halres
  have hb'res : IsIso (b'.residueFieldMap (psi u)) :=
    isIso_residueFieldMap_of_pullbackFactorComparison_eq gY (D.map e ≫ tj) (c.π.app j') bT
      hbTfac pU pU' be b' psi hbe hb'sn hpsiU hpsib u z hpUz (hkz j') hberes
  -- Step 4: the slice.
  obtain ⟨V, i, v, himm, hiv, het, hresv, hvs⟩ :=
    exists_slice_at_stage D p c m hm hsm j' z s hz hzres
  have hires : IsIso (i.residueFieldMap v) :=
    isIso_residueFieldMap_left_of_isIso_residueFieldMap_comp i (p.app j') v hresv
  have htauv : (i ≫ D.map e ≫ tj) v = t := by
    have h1 : (i ≫ D.map e ≫ tj) v = (D.map e ≫ tj) (c.π.app j' z) := by rw [← hiv]; rfl
    have h2 : (D.map e ≫ tj) (c.π.app j' z) = (c.π.app j' ≫ D.map e ≫ tj) z := rfl
    rw [h1, h2, hbTfac]; exact hbT
  -- Step 5: the point `w` of the inverse image of the slice, and the two morphisms.
  obtain ⟨w, ⟨hw₁, hw₂⟩, -⟩ :=
    Scheme.Pullback.exists_unique_point_of_isIso_residueFieldMap pU' i (psi u) v
      (hpU'u.trans hiv.symm) hires
  obtain ⟨FX, hFXe, hFXres, hFXsn, hFXx⟩ :=
    exists_etale_pullback_slice_morphism fX (p.app j') pU' a' ha'e ha'sn i (psi u) w hw₁ ha'res
  obtain ⟨FY, hFYe, hFYres, hFYsn, hFYx⟩ :=
    exists_etale_pullback_slice_morphism gY (D.map e ≫ tj) pU' b' hb'e hb'sn i (psi u) w hw₁
      hb'res
  -- Step 7: the two morphisms out of `Spec κ(s)` agree.
  have hsec : specResidueFieldSection m hz hzres ≫ bT =
      specResidueFieldSection (i ≫ p.app j') hvs hresv ≫ (i ≫ D.map e ≫ tj) := by
    have hα : (c.π.app j' ≫ p.app j') z = s := by rw [hm j']; exact hz
    have hα' : IsIso ((c.π.app j' ≫ p.app j').residueFieldMap z) := by
      rw [hm j']; exact hzres
    have key := specResidueFieldSection_comp_eq_comp (c.π.app j') i (p.app j') hiv.symm hα hvs
      hα' hresv
    have h2 : specResidueFieldSection (c.π.app j' ≫ p.app j') hα hα' ≫
          (c.π.app j' ≫ D.map e ≫ tj) =
        specResidueFieldSection (i ≫ p.app j') hvs hresv ≫ (i ≫ D.map e ≫ tj) := by
      rw [← Category.assoc _ (c.π.app j') (D.map e ≫ tj),
        ← Category.assoc _ i (D.map e ≫ tj), key]
    rw [specResidueFieldSection_congr_hom (hm j') hα hz hα' hzres, hbTfac] at h2
    exact h2
  refine ⟨V, v, i ≫ p.app j', i ≫ D.map e ≫ tj, het, hresv, hvs, htauv, hsec,
    pullback pU' i, w, FX, FY, hFXe, hFYe, hFXres, hFYres, hFXsn.trans hFYsn.symm, ?_,
    (hFXx.trans (congrArg (· u) hpsia)).trans halx, hFYx.trans (congrArg (· u) hpsib)⟩
  have h1 : pullback.snd fX (i ≫ p.app j') (FX w) =
      (FX ≫ pullback.snd fX (i ≫ p.app j')) w := rfl
  rw [h1, hFXsn]
  exact hw₂

/-- **Tag 0GDX, clauses (1)–(4).** From a smooth limit presentation of `Spec(𝒪^∧_{S,s})` over `S`
and a common étale neighbourhood over that limit, the slice `V`, the morphism `tau : V ⟶ T` and
the scheme `W` with its point.

This is `AlgebraicGeometry.exists_slice_etale_pair_of_common_neighborhood_section` with the
identity of the two morphisms `Spec κ(s) ⟶ T` dropped. -/
public theorem exists_slice_etale_pair_of_common_neighborhood
    {S T X Y : Scheme.{u}} [IsLocallyNoetherian S]
    (fX : X ⟶ S) (gY : Y ⟶ T) [LocallyOfFiniteType fX] [LocallyOfFiniteType gY]
    (hfp : FinitePresentation fX) (hgp : FinitePresentation gY)
    (hT : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from T))
    (x : X) (s : S) (t : T)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) [∀ i, IsAffine (D.obj i)]
    (hsm : ∀ i, Smooth (p.app i))
    (m : c.pt ⟶ S) (hm : ∀ i, c.π.app i ≫ p.app i = m)
    (z : c.pt) (hz : m z = s) (hzres : IsIso (m.residueFieldMap z))
    (bT : c.pt ⟶ T) (hbT : bT z = t)
    (Usch : Scheme.{u}) (pU : Usch ⟶ c.pt) (hUfp : FinitePresentation pU) (u : Usch)
    (hpUz : pU u = z)
    (al : Usch ⟶ pullback fX m) (be : Usch ⟶ pullback gY bT)
    (hale : Etale al) (hbee : Etale be)
    (hal : al ≫ pullback.snd fX m = pU) (hbe : be ≫ pullback.snd gY bT = pU)
    (halres : IsIso (al.residueFieldMap u)) (hberes : IsIso (be.residueFieldMap u))
    (halx : pullback.fst fX m (al u) = x) :
    ∃ (V : Scheme.{u}) (v : V) (pV : V ⟶ S) (tau : V ⟶ T),
      Etale pV ∧ IsIso (pV.residueFieldMap v) ∧ pV v = s ∧ tau v = t ∧
      ∃ (W : Scheme.{u}) (w : W) (FX : W ⟶ pullback fX pV) (FY : W ⟶ pullback gY tau),
        Etale FX ∧ Etale FY ∧
          IsIso (FX.residueFieldMap w) ∧ IsIso (FY.residueFieldMap w) ∧
            FX ≫ pullback.snd fX pV = FY ≫ pullback.snd gY tau ∧
              pullback.snd fX pV (FX w) = v ∧
                pullback.fst fX pV (FX w) = x ∧
                  pullback.fst gY tau (FY w) = pullback.fst gY bT (be u) := by
  obtain ⟨V, v, pV, tau, hpVe, hpVres, hpVs, htauv, -, W, w, FX, FY, hrest⟩ :=
    exists_slice_etale_pair_of_common_neighborhood_section fX gY hfp hgp hT x s t D p c hc hsm
      m hm z hz hzres bT hbT Usch pU hUfp u hpUz al be hale hbee hal hbe halres hberes halx
  exact ⟨V, v, pV, tau, hpVe, hpVres, hpVs, htauv, W, w, FX, FY, hrest⟩

end AlgebraicGeometry

end
