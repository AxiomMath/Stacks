module

public import StacksFrontier.AlgebraicGeometry.Quot.EtaleLocallyProjectiveCurvesChartPiece
public import StacksFrontier.AlgebraicGeometry.Divisors.ClopenPieceSubschemeOnOpen

/-!
# The finite piece of a chart divisor as an effective Cartier divisor on an open

Let `g : W ⟶ S` be flat and locally of finite presentation and `Z ⊆ W` a closed subscheme which
is principal near `w`, whose fibre over `s = g(w)` is an effective Cartier divisor near `w`, and
which is quasi-finite over `S` at `w`. By
`Stacks.Divisors.exists_elementaryEtaleNeighborhood_finite_piece` there are an affine open
`V ∋ w` on which `Z` is a relative effective Cartier divisor (Stacks 062Y) and an elementary étale
neighbourhood `(U, u)` of `(S, s)` over which `(Z ∩ V) ×_S U` has an open and closed piece `P`,
finite over `U`, with a single point over `u`, lying over `w` (Stacks 02LN).

This file shows that the piece is itself an effective Cartier divisor on an open `N` of
`V ×_S U`: it is `Z_U ∩ N` for the pullback `Z_U` of `Z ∩ V` to `V ×_S U`, which is an effective
Cartier divisor because `V ×_S U ⟶ V` is étale. This is the local principal data of the divisor
used in the proof that families of curves are étale locally schemes (Stacks 0E6F).

## Main results

* `Stacks.Divisors.exists_elementaryEtaleNeighborhood_cartier_piece`.
* `AlgebraicGeometry.Space.exists_etale_cartier_piece_of_chart`: the same in the big fppf site,
  over an affine étale `U ⟶ S₀`, with the open of `V ×_S U` replaced by a scheme `N` of the site
  étale over `W ×_{S₀} U`, in the form taken by
  `AlgebraicGeometry.Space.exists_isOpen_isClosedImmersion_of_elementaryChart` and
  `AlgebraicGeometry.Space.isEffectiveCartierDivisor_range_of_etaleChart_of_ideal`.

## References

* [Stacks Project, Tag 01WR](https://stacks.math.columbia.edu/tag/01WR)
* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 02LN](https://stacks.math.columbia.edu/tag/02LN)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

variable {W S : Scheme.{u}}

/-- **The finite piece of a chart divisor is an effective Cartier divisor on an open.** Let
`g : W ⟶ S` be flat and locally of finite presentation and `Z` a closed subscheme of `W`,
principal near `w`, with effective Cartier fibre near `w`, and quasi-finite over `S` at a point
`z` of `Z` over `w`. Then there are an affine open `V ∋ w` of `W`, an elementary étale
neighbourhood `U` of `(S, g w)` and an open `N` of `V ×_S U` such that the pullback `J` to `N` of
`Z ∩ V` is an effective Cartier divisor on `N`, finite and flat over `U`, whose only point `v` over
the point of `U` lies over `w`. -/
theorem exists_elementaryEtaleNeighborhood_cartier_piece (g : W ⟶ S) [Flat g]
    [LocallyOfFinitePresentation g] (Z : W.IdealSheafData) (w : W) (hw : w ∈ Z.support)
    (hprin : ∃ V : W.affineOpens, w ∈ (V : W.Opens) ∧ (Z.ideal V).IsPrincipal)
    (hfib : ∃ V : (g.fiber (g w)).Opens, g.asFiber w ∈ V ∧
      IsEffectiveCartierDivisor ((Z.comap (g.fiberι (g w))).comap V.ι))
    (z : Z.subscheme) (hz : Z.subschemeι z = w) (hqf : (Z.subschemeι ≫ g).QuasiFiniteAt z) :
    ∃ V : W.Opens, w ∈ V ∧ IsAffineOpen V ∧
      ∃ (U : EtaleNeighborhood S (g w)) (_ : U.IsElementary)
        (N : (pullback (V.ι ≫ g) U.toBase).Opens) (J : N.toScheme.IdealSheafData),
        J = ((Z.comap V.ι).comap (pullback.fst (V.ι ≫ g) U.toBase)).comap N.ι ∧
        IsEffectiveCartierDivisor J ∧
        IsFinite (J.subschemeι ≫ N.ι ≫ pullback.snd (V.ι ≫ g) U.toBase) ∧
        Flat (J.subschemeι ≫ N.ι ≫ pullback.snd (V.ι ≫ g) U.toBase) ∧
        ∃ v : J.subscheme, (J.subschemeι ≫ N.ι ≫ pullback.fst (V.ι ≫ g) U.toBase ≫ V.ι) v = w ∧
          {y | (J.subschemeι ≫ N.ι ≫ pullback.snd (V.ι ≫ g) U.toBase) y = U.point} = {v} := by
  obtain ⟨V, hwV, hV, hrel, Ue, hUe, P₀, j₀, v₀, hjo, hjc, hfin, hv₀, hfibre⟩ :=
    exists_elementaryEtaleNeighborhood_finite_piece g Z w hw hprin hfib z hz hqf
  refine ⟨V, hwV, hV, Ue, hUe, ?_⟩
  let Z₀ := Z.comap V.ι
  let pr₁ := pullback.fst (V.ι ≫ g) Ue.toBase
  let pr₂ := pullback.snd (V.ι ≫ g) Ue.toBase
  let Z' := Z₀.comap pr₁
  -- the pullback of `Z ∩ V` to `V ×_S U` is an effective Cartier divisor
  have hZ' : IsEffectiveCartierDivisor Z' := isPullbackDefined_of_flat pr₁ Z₀ hrel.1
  -- `(Z ∩ V) ×_S U` is the closed subscheme `Z'`
  let Φ : pullback (Z₀.subschemeι ≫ V.ι ≫ g) Ue.toBase ≅ Z'.subscheme :=
    (pullbackRightPullbackFstIso (V.ι ≫ g) Ue.toBase Z₀.subschemeι).symm ≪≫
      pullbackSymmetry _ _ ≪≫ (Z₀.comapIso pr₁).symm
  have hΦ : Φ.hom ≫ Z'.subschemeι =
      (pullbackRightPullbackFstIso (V.ι ≫ g) Ue.toBase Z₀.subschemeι).inv ≫
        pullback.snd Z₀.subschemeι pr₁ := by
    simp only [Φ, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← Scheme.IdealSheafData.comapIso_hom_fst Z₀ pr₁, Iso.inv_hom_id_assoc,
      pullbackSymmetry_hom_comp_fst]
  have hΦ₂ : Φ.hom ≫ Z'.subschemeι ≫ pr₂ = pullback.snd (Z₀.subschemeι ≫ V.ι ≫ g) Ue.toBase := by
    rw [reassoc_of% hΦ]
    exact pullbackRightPullbackFstIso_inv_snd_snd _ _ _
  have hΦ₁ : Φ.hom ≫ Z'.subschemeι ≫ pr₁ =
      pullback.fst (Z₀.subschemeι ≫ V.ι ≫ g) Ue.toBase ≫ Z₀.subschemeι := by
    rw [reassoc_of% hΦ]
    exact pullbackRightPullbackFstIso_inv_snd_fst _ _ _
  -- the piece as an open and closed piece of `Z'`
  have : IsOpenImmersion j₀ := hjo
  have : IsClosedImmersion j₀ := hjc
  let c := j₀ ≫ Φ.hom
  obtain ⟨N, -, -, hcart, e, he⟩ := exists_opens_iso_comap_subscheme_of_isOpenImmersion Z' ⊤
    (isPullbackDefined_of_flat _ Z' hZ') c (fun _ _ => trivial)
  have hmor : (Z'.comap N.ι).subschemeι ≫ N.ι = e.inv ≫ j₀ ≫ Φ.hom ≫ Z'.subschemeι := by
    rw [(Iso.eq_inv_comp e).2 he]
    simp only [c, Category.assoc]
  let q₀ := j₀ ≫ pullback.snd (Z₀.subschemeι ≫ V.ι ≫ g) Ue.toBase
  have hq : (Z'.comap N.ι).subschemeι ≫ N.ι ≫ pr₂ = e.inv ≫ q₀ := by
    rw [← Category.assoc, hmor]
    simp only [Category.assoc, q₀, hΦ₂]
  have : IsFinite q₀ := hfin
  have hfflat : Flat (Z₀.subschemeι ≫ V.ι ≫ g) := hrel.2
  have : Flat q₀ := by
    simp only [q₀]
    infer_instance
  refine ⟨N, Z'.comap N.ι, rfl, hcart, ?_, ?_, e.hom v₀, ?_, ?_⟩
  · rw [hq]
    infer_instance
  · rw [hq]
    infer_instance
  · have h1 : (Z'.comap N.ι).subschemeι ≫ N.ι ≫ pr₁ ≫ V.ι =
        e.inv ≫ j₀ ≫ pullback.fst (Z₀.subschemeι ≫ V.ι ≫ g) Ue.toBase ≫ Z₀.subschemeι ≫ V.ι := by
      rw [← Category.assoc, hmor]
      simp only [Category.assoc]
      rw [reassoc_of% hΦ₁]
    rw [h1, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    exact hv₀
  · rw [hq]
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    have hy : q₀ (e.inv y) = Ue.point ↔ e.inv y = v₀ := Set.ext_iff.1 hfibre (e.inv y)
    rw [Scheme.Hom.comp_apply, hy]
    exact ⟨fun h => by simp [← h], by rintro rfl; simp⟩

end Stacks.Divisors

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

open Stacks.Divisors in
/-- **The finite piece of a chart divisor in the big fppf site, with its Cartier data.** Let
`gW : W ⟶ S₀` be a morphism of the site, flat and locally of finite presentation, with `W`
affine, and `Z` a closed subscheme of `W` principal near `w`, with effective Cartier fibre near
`w` and quasi-finite over `S₀` at a point `z` over `w`. Then there are an affine scheme `U` of
the site with an étale morphism `φ : U ⟶ S₀` through `g(w)`, a scheme `N` of the site with an
étale morphism `ι : N ⟶ W ×_{S₀} U`, and an effective Cartier divisor `J` on `N` whose closed
subscheme `P` (a scheme of the site) is finite and flat over `U`, maps to `W ×_{S₀} U` by a closed
immersion, and has all its points over the point `u` of `U` lying over `w`, and at least one
such point. The neighbourhood is elementary: the residue field map of `φ` at `u` is an
isomorphism. -/
theorem exists_etale_cartier_piece_of_chart {S₀ W : BigFppfOver B S hS} (gW : W ⟶ S₀)
    [Flat ((𝒯).map gW)] [LocallyOfFinitePresentation ((𝒯).map gW)] [IsAffine ((𝒯).obj W)]
    (Z : ((𝒯).obj W).IdealSheafData) (w : (𝒯).obj W) (hw : w ∈ Z.support)
    (hprin : ∃ V : ((𝒯).obj W).affineOpens, w ∈ (V : ((𝒯).obj W).Opens) ∧ (Z.ideal V).IsPrincipal)
    (hfib : ∃ V : (((𝒯).map gW).fiber ((𝒯).map gW w)).Opens, ((𝒯).map gW).asFiber w ∈ V ∧
      IsEffectiveCartierDivisor ((Z.comap (((𝒯).map gW).fiberι ((𝒯).map gW w))).comap V.ι))
    (z : Z.subscheme) (hz : Z.subschemeι z = w)
    (hqf : (Z.subschemeι ≫ (𝒯).map gW).QuasiFiniteAt z) :
    ∃ (U N P : BigFppfOver B S hS) (φ : U ⟶ S₀) (u : (𝒯).obj U) (ι : N ⟶ pullback gW φ)
      (j : P ⟶ N),
      Etale ((𝒯).map φ) ∧ IsAffine ((𝒯).obj U) ∧ (𝒯).map φ u = (𝒯).map gW w ∧
      IsIso (((𝒯).map φ).residueFieldMap u) ∧ Etale ((𝒯).map ι) ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map (j ≫ ι)) ∧
      _root_.AlgebraicGeometry.IsFinite ((𝒯).map (j ≫ ι ≫ pullback.snd gW φ)) ∧
      Flat ((𝒯).map (j ≫ ι ≫ pullback.snd gW φ)) ∧
      (∀ v, (𝒯).map (j ≫ ι ≫ pullback.snd gW φ) v = u →
        (𝒯).map (j ≫ ι ≫ pullback.fst gW φ) v = w) ∧
      (∃ v, (𝒯).map (j ≫ ι ≫ pullback.snd gW φ) v = u) ∧
      ∃ J : ((𝒯).obj N).IdealSheafData, IsEffectiveCartierDivisor J ∧
        ∃ ε : (𝒯).obj P ≅ J.subscheme, (𝒯).map j = ε.hom ≫ J.subschemeι := by
  obtain ⟨V, hwV, hV, Ue, hUe, N, J, -, hJ, hfin, hflat, v₀, hv₀, hfibre⟩ :=
    exists_elementaryEtaleNeighborhood_cartier_piece ((𝒯).map gW) Z w hw hprin hfib z hz hqf
  let pr₁ := pullback.fst (V.ι ≫ (𝒯).map gW) Ue.toBase
  let pr₂ := pullback.snd (V.ι ≫ (𝒯).map gW) Ue.toBase
  -- an affine open of the étale neighbourhood, as a scheme of the site
  obtain ⟨U₁, hU₁, hpt, -⟩ := exists_isAffineOpen_mem_and_subset (X := Ue.scheme) (x := Ue.point)
    (U := ⊤) trivial
  have : IsAffine (U₁ : Scheme.{u}) := hU₁
  have hcU : B.Contains (U₁ : Scheme.{u}) :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B (U₁.ι ≫ Ue.toBase) S₀.left.property
  let U : BigFppfOver B S hS := BigFppfOver.siteObjectOver B S hS S₀ hcU (U₁.ι ≫ Ue.toBase)
  let φ : U ⟶ S₀ := BigFppfOver.siteMapOver B S hS S₀ hcU (U₁.ι ≫ Ue.toBase)
  let u : (𝒯).obj U := (⟨Ue.point, hpt⟩ : (U₁ : Scheme.{u}))
  -- the part `N₁` of `N` over `U₁`, as a scheme of the site étale over `W ×_{S₀} U`
  let N₁ : N.toScheme.Opens := (N.ι ≫ pr₂) ⁻¹ᵁ U₁
  let a : N₁.toScheme ⟶ (𝒯).obj W := N₁.ι ≫ N.ι ≫ pr₁ ≫ V.ι
  let b : N₁.toScheme ⟶ (U₁ : Scheme.{u}) := (N.ι ≫ pr₂) ∣_ U₁
  have hb : b ≫ U₁.ι = N₁.ι ≫ N.ι ≫ pr₂ := morphismRestrict_ι _ _
  have hP := (IsPullback.of_hasPullback gW φ).map (𝒯)
  have hab : a ≫ (𝒯).map gW = b ≫ (𝒯).map φ := by
    show a ≫ (𝒯).map gW = b ≫ U₁.ι ≫ Ue.toBase
    rw [reassoc_of% hb]
    simp only [a, Category.assoc]
    rw [pullback.condition]
  let m : N₁.toScheme ⟶ (𝒯).obj (pullback gW φ) := hP.lift a b hab
  have hm₁ : m ≫ (𝒯).map (pullback.fst gW φ) = a := hP.lift_fst _ _ _
  have hm₂ : m ≫ (𝒯).map (pullback.snd gW φ) = b := hP.lift_snd _ _ _
  -- `m` is an étale monomorphism
  have hφet : Etale ((𝒯).map φ) := by
    show Etale (U₁.ι ≫ Ue.toBase)
    infer_instance
  have : Etale ((𝒯).map (pullback.fst gW φ)) := MorphismProperty.of_isPullback hP.flip hφet
  have : Etale (m ≫ (𝒯).map (pullback.fst gW φ)) := by
    rw [hm₁]
    simp only [a]
    infer_instance
  have hetm : Etale m := Etale.of_comp m ((𝒯).map (pullback.fst gW φ))
  have : Mono m := ⟨fun {T} x₁ x₂ hx => by
    have ha : x₁ ≫ a = x₂ ≫ a := by
      simpa only [Category.assoc, hm₁] using hx =≫ (𝒯).map (pullback.fst gW φ)
    have hb' : x₁ ≫ b = x₂ ≫ b := by
      have := hx =≫ (𝒯).map (pullback.snd gW φ)
      rw [Category.assoc, Category.assoc, hm₂] at this
      exact this
    have h1 : x₁ ≫ N₁.ι ≫ N.ι = x₂ ≫ N₁.ι ≫ N.ι := by
      apply pullback.hom_ext
      · rw [← cancel_mono V.ι]
        simpa only [a, Category.assoc] using ha
      · simpa only [Category.assoc, hb] using hb' =≫ U₁.ι
    exact (cancel_mono N₁.ι).1 ((cancel_mono N.ι).1 (by simpa only [Category.assoc] using h1))⟩
  have hcN : B.Contains N₁.toScheme :=
    Scheme.size_lt_of_mono_locallyOfFinitePresentation m (pullback gW φ).left.property
  let Nsite : BigFppfOver B S hS := BigFppfOver.siteObjectOver B S hS (pullback gW φ) hcN m
  let ι : Nsite ⟶ pullback gW φ := BigFppfOver.siteMapOver B S hS (pullback gW φ) hcN m
  have hιm : (𝒯).map ι = m := rfl
  -- the divisor on `N₁` and its closed subscheme, the part of `J` over `N₁`
  let J₁ := J.comap N₁.ι
  have hJ₁ : IsEffectiveCartierDivisor J₁ := isPullbackDefined_of_flat N₁.ι J hJ
  let q := J.subschemeι ≫ N.ι ≫ pr₂
  have : IsFinite q := hfin
  have : Flat q := hflat
  let Q : J.subscheme.Opens := J.subschemeι ⁻¹ᵁ N₁
  have hQ : Q = q ⁻¹ᵁ U₁ := by
    ext y
    rfl
  let ε₀ : Q.toScheme ≅ J₁.subscheme :=
    (pullbackRestrictIsoRestrict J.subschemeι N₁).symm ≪≫ pullbackSymmetry _ _ ≪≫
      (J.comapIso N₁.ι).symm
  have hε₀ : ε₀.hom ≫ J₁.subschemeι ≫ N₁.ι = Q.ι ≫ J.subschemeι := by
    simp only [ε₀, J₁, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [← Scheme.IdealSheafData.comapIso_hom_fst J N₁.ι, Category.assoc, Iso.inv_hom_id_assoc,
      pullback.condition, pullbackSymmetry_hom_comp_snd_assoc,
      pullbackRestrictIsoRestrict_inv_fst_assoc]
  let bQ : Q.toScheme ⟶ (U₁ : Scheme.{u}) := (J.subscheme.isoOfEq hQ).hom ≫ q ∣_ U₁
  have hbQ : ε₀.hom ≫ J₁.subschemeι ≫ b = bQ := by
    rw [← cancel_mono U₁.ι, Category.assoc, Category.assoc, hb]
    simp only [bQ, Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
    rw [← Category.assoc J₁.subschemeι, ← Category.assoc, hε₀]
    simp only [q, Category.assoc]
  have hbQι : bQ ≫ U₁.ι = Q.ι ≫ q := by
    simp only [bQ, Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
  have hbQx : ∀ x, U₁.ι (bQ x) = q (Q.ι x) := fun x => by
    have h : (bQ ≫ U₁.ι) x = (Q.ι ≫ q) x := by rw [hbQι]
    exact h
  have hfinQ : IsFinite bQ := by
    show IsFinite ((J.subscheme.isoOfEq hQ).hom ≫ q ∣_ U₁)
    infer_instance
  have hflatQ : Flat bQ := by
    show Flat ((J.subscheme.isoOfEq hQ).hom ≫ q ∣_ U₁)
    infer_instance
  have hcP : B.Contains Q.toScheme := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact bQ hcU
  let Psite : BigFppfOver B S hS :=
    BigFppfOver.siteObjectOver B S hS Nsite hcP (ε₀.hom ≫ J₁.subschemeι)
  let jsite : Psite ⟶ Nsite := BigFppfOver.siteMapOver B S hS Nsite hcP (ε₀.hom ≫ J₁.subschemeι)
  have hjm : (𝒯).map jsite = ε₀.hom ≫ J₁.subschemeι := rfl
  have hjs : (𝒯).map (jsite ≫ ι ≫ pullback.snd gW φ) = bQ := by
    show (ε₀.hom ≫ J₁.subschemeι) ≫ m ≫ (𝒯).map (pullback.snd gW φ) = bQ
    rw [hm₂]
    exact (Category.assoc _ _ _).trans hbQ
  have hjf :
      (𝒯).map (jsite ≫ ι ≫ pullback.fst gW φ) = Q.ι ≫ J.subschemeι ≫ N.ι ≫ pr₁ ≫ V.ι := by
    show (ε₀.hom ≫ J₁.subschemeι) ≫ m ≫ (𝒯).map (pullback.fst gW φ) = _
    rw [hm₁, Category.assoc]
    simp only [a]
    rw [← Category.assoc J₁.subschemeι, ← Category.assoc, hε₀]
    simp only [Category.assoc]
  have hq₀ : q v₀ = Ue.point := (Set.ext_iff.1 hfibre v₀).2 (Set.mem_singleton v₀)
  have hres : IsIso (((𝒯).map φ).residueFieldMap u) := by
    let u₁ : (U₁ : Scheme.{u}) := ⟨Ue.point, hpt⟩
    have h1 : IsIso (Ue.toBase.residueFieldMap (U₁.ι u₁)) :=
      (EtaleNeighborhood.isElementary_iff Ue).1 hUe
    have h2 : IsIso (U₁.ι.residueFieldMap u₁) :=
      (IsLocalRing.ResidueField.mapEquiv
        (asIso (U₁.ι.stalkMap u₁)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
    have e := Scheme.residueFieldMap_comp U₁.ι Ue.toBase u₁
    have h3 : IsIso (Ue.toBase.residueFieldMap (U₁.ι u₁) ≫ U₁.ι.residueFieldMap u₁) :=
      IsIso.comp_isIso
    exact e ▸ h3
  refine ⟨U, Nsite, Psite, φ, u, ι, jsite, hφet, hU₁, Ue.map_point, hres, hetm, ?_, ?_, ?_, ?_,
    ?_, J₁, hJ₁, ε₀, hjm⟩
  · show _root_.AlgebraicGeometry.IsClosedImmersion ((ε₀.hom ≫ J₁.subschemeι) ≫ m)
    refine (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono _).2 ⟨?_, ?_⟩
    · have : _root_.AlgebraicGeometry.IsSeparated ((𝒯).map (pullback.snd gW φ)) :=
        MorphismProperty.of_isPullback hP
          (inferInstance : _root_.AlgebraicGeometry.IsSeparated ((𝒯).map gW))
      have : _root_.AlgebraicGeometry.IsProper
          (((ε₀.hom ≫ J₁.subschemeι) ≫ m) ≫ (𝒯).map (pullback.snd gW φ)) := by
        have e : ((ε₀.hom ≫ J₁.subschemeι) ≫ m) ≫ (𝒯).map (pullback.snd gW φ) = bQ := hjs
        rw [e]
        have := hfinQ
        exact (inferInstance : _root_.AlgebraicGeometry.IsProper bQ)
      exact _root_.AlgebraicGeometry.IsProper.of_comp _ ((𝒯).map (pullback.snd gW φ))
    · infer_instance
  · rw [hjs]
    exact hfinQ
  · rw [hjs]
    exact hflatQ
  · intro v hv
    rw [hjs] at hv
    rw [hjf]
    let v' : Q.toScheme := v
    have hv' : bQ v' = ⟨Ue.point, hpt⟩ := hv
    have h1 : q (Q.ι v') = Ue.point := by
      rw [← hbQx, hv']
      rfl
    have h2 : Q.ι v' = v₀ := by
      have : Q.ι v' ∈ {y | q y = Ue.point} := h1
      rw [hfibre] at this
      exact this
    show (Q.ι ≫ J.subschemeι ≫ N.ι ≫ pr₁ ≫ V.ι) v' = w
    have e : (Q.ι ≫ J.subschemeι ≫ N.ι ≫ pr₁ ≫ V.ι) v' =
        (J.subschemeι ≫ N.ι ≫ pr₁ ≫ V.ι) (Q.ι v') := rfl
    rw [e, h2]
    exact hv₀
  · have hv₀Q : v₀ ∈ Q := by
      show q v₀ ∈ U₁
      rw [hq₀]
      exact hpt
    refine ⟨(⟨v₀, hv₀Q⟩ : Q.toScheme), ?_⟩
    rw [hjs]
    apply U₁.ι.isOpenEmbedding.injective
    exact (hbQx ⟨v₀, hv₀Q⟩).trans hq₀

end AlgebraicGeometry.Space

end
