module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.LocallyPrincipalFibre
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.Decomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.ProductSubscheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Etale.UniversallyInjectiveUnramified.ClosedImmersion

/-!
# A finite piece of a relative divisor on a chart, after an elementary étale base change

Let `g : W ⟶ S` be flat and locally of finite presentation, and let `Z ⊆ W` be a closed
subscheme which is principal near a point `w`, whose fibre over `s = g(w)` is an effective
Cartier divisor near `w`, and which is quasi-finite over `S` at `w`. Then there is an affine open
`V ∋ w` on which `Z` is a relative effective Cartier divisor over `S` (Stacks 062Y), and an
elementary étale neighbourhood `(U, u)` of `(S, s)` over which the base change of `Z ∩ V` has an
open and closed piece `P`, finite over `U`, with a single point `v` over `u`, lying over `w`
(Stacks 02LN).

This is the scheme part of the proof that families of curves are étale locally schemes
(Stacks 0E6F): on an étale chart `W` of the family, the divisor cut out by a lift of a local
equation of a divisor of the special fibre is made finite over an étale neighbourhood of the
base point.

## Main results

* `Stacks.Divisors.exists_elementaryEtaleNeighborhood_finite_piece`.

## References

* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 02LN](https://stacks.math.columbia.edu/tag/02LN)
* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Divisors

variable {W S : Scheme.{u}}

/-- **A finite piece of a relative divisor on a chart.** Let `g : W ⟶ S` be flat and locally of
finite presentation and `Z` a closed subscheme of `W`, principal near `w`, with effective Cartier
fibre near `w`, and quasi-finite over `S` at a point `z` of `Z` over `w`. Then on an affine open
`V ∋ w` the closed subscheme `Z ∩ V` is a relative effective Cartier divisor over `S`, and there
are an elementary étale neighbourhood `U` of `(S, g w)` and an open and closed piece `P` of
`(Z ∩ V) ×_S U`, finite over `U`, whose only point over the point of `U` lies over `w`. -/
theorem exists_elementaryEtaleNeighborhood_finite_piece (g : W ⟶ S) [Flat g]
    [LocallyOfFinitePresentation g] (Z : W.IdealSheafData) (w : W) (hw : w ∈ Z.support)
    (hprin : ∃ V : W.affineOpens, w ∈ (V : W.Opens) ∧ (Z.ideal V).IsPrincipal)
    (hfib : ∃ V : (g.fiber (g w)).Opens, g.asFiber w ∈ V ∧
      IsEffectiveCartierDivisor ((Z.comap (g.fiberι (g w))).comap V.ι))
    (z : Z.subscheme) (hz : Z.subschemeι z = w) (hqf : (Z.subschemeι ≫ g).QuasiFiniteAt z) :
    ∃ V : W.Opens, w ∈ V ∧ IsAffineOpen V ∧
      IsRelativeEffectiveCartierDivisor (V.ι ≫ g) (Z.comap V.ι) ∧
      ∃ (U : EtaleNeighborhood S (g w)) (_ : U.IsElementary) (P : Scheme.{u})
        (j : P ⟶ pullback ((Z.comap V.ι).subschemeι ≫ V.ι ≫ g) U.toBase) (v : P),
        IsOpenImmersion j ∧ IsClosedImmersion j ∧
        IsFinite (j ≫ pullback.snd ((Z.comap V.ι).subschemeι ≫ V.ι ≫ g) U.toBase) ∧
        (j ≫ pullback.fst _ _ ≫ (Z.comap V.ι).subschemeι ≫ V.ι) v = w ∧
        {y | (j ≫ pullback.snd ((Z.comap V.ι).subschemeι ≫ V.ι ≫ g) U.toBase) y = U.point} =
          {v} := by
  obtain ⟨V, hwV, hV, hrel⟩ :=
    exists_isRelativeEffectiveCartierDivisor_of_ideal_isPrincipal g Z w hw hprin hfib
  refine ⟨V, hwV, hV, hrel, ?_⟩
  set Z₀ := Z.comap V.ι
  have hsq := Scheme.IdealSheafData.isPullback_comap_subschemeι Z V.ι
  -- the point of `Z ∩ V` over `z`
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : Z₀.subscheme,
      Z₀.subschemeι z₀ = (⟨w, hwV⟩ : V.toScheme) ∧
        Scheme.IdealSheafData.subschemeMap Z₀ Z V.ι (Z.le_map_comap V.ι) z₀ = z := by
    obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.ι)
      (g := Z.subschemeι) (⟨w, hwV⟩ : V.toScheme) z (by rw [hz]; rfl)
    refine ⟨hsq.isoPullback.inv p, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hp₁]
    · rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hp₂]
  have hopen : IsOpenImmersion (Scheme.IdealSheafData.subschemeMap Z₀ Z V.ι (Z.le_map_comap V.ι)) :=
    MorphismProperty.of_isPullback hsq inferInstance
  set f := Z₀.subschemeι ≫ V.ι ≫ g
  have hf :
      f = Scheme.IdealSheafData.subschemeMap Z₀ Z V.ι (Z.le_map_comap V.ι) ≫ Z.subschemeι ≫ g := by
    simp only [f, ← Category.assoc]
    rw [hsq.w]
  have hqf₀ : f.QuasiFiniteAt z₀ := by
    rw [hf, Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, hz₀.2]
    exact hqf
  have hiso : IsOpen {f.asFiber z₀} := Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hqf₀
  have hfz : f z₀ = g w := by
    simp only [f, Scheme.Hom.comp_apply, hz₀.1]
    rfl
  have : IsAffine V.toScheme := hV
  have : IsSeparated f := by
    simp only [f]
    infer_instance
  obtain ⟨U, hU, P, j, hjo, hjc, hiP, v, hfin, hvx, hfibre, hres, hnone⟩ :=
    exists_elementaryEtaleNeighborhood_decomposition f (g w) 1 ![z₀]
      (fun i => by fin_cases i; exact hfz) (Function.injective_of_subsingleton _)
      (fun i => by fin_cases i; exact hiso)
  refine ⟨U, hU, P (some 0), j (some 0), v 0, hjo _, hjc _, hfin 0, ?_, hfibre 0⟩
  have h := hvx 0
  simp only [Matrix.cons_val_fin_one] at h
  simp only [Scheme.Hom.comp_apply] at h ⊢
  rw [h, hz₀.1]
  rfl

end Stacks.Divisors

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

open Stacks.Divisors in
/-- **A finite piece of a relative divisor on a chart, in the big fppf site.** Let
`gW : W ⟶ S₀` be a morphism of the site, flat and locally of finite presentation, with `W`
affine, and `Z` a closed subscheme of `W` principal near `w`, with effective Cartier fibre near `w`
and quasi-finite over `S₀` at a point `z` over `w`. Then there are an affine scheme `U` of the site
with an étale morphism `φ : U ⟶ S₀` through `g(w)`, and a scheme `P` of the site with a closed
immersion `j : P ⟶ W ×_{S₀} U`, finite and flat over `U`, whose points over the point `u` of `U`
all lie over `w`. -/
theorem exists_etale_finite_piece_of_chart {S₀ W : BigFppfOver B S hS} (gW : W ⟶ S₀)
    [Flat ((𝒯).map gW)] [LocallyOfFinitePresentation ((𝒯).map gW)] [IsAffine ((𝒯).obj W)]
    (Z : ((𝒯).obj W).IdealSheafData) (w : (𝒯).obj W) (hw : w ∈ Z.support)
    (hprin : ∃ V : ((𝒯).obj W).affineOpens, w ∈ (V : ((𝒯).obj W).Opens) ∧ (Z.ideal V).IsPrincipal)
    (hfib : ∃ V : (((𝒯).map gW).fiber ((𝒯).map gW w)).Opens, ((𝒯).map gW).asFiber w ∈ V ∧
      IsEffectiveCartierDivisor ((Z.comap (((𝒯).map gW).fiberι ((𝒯).map gW w))).comap V.ι))
    (z : Z.subscheme) (hz : Z.subschemeι z = w)
    (hqf : (Z.subschemeι ≫ (𝒯).map gW).QuasiFiniteAt z) :
    ∃ (U P : BigFppfOver B S hS) (φ : U ⟶ S₀) (u : (𝒯).obj U) (j : P ⟶ pullback gW φ),
      Etale ((𝒯).map φ) ∧ IsAffine ((𝒯).obj U) ∧ (𝒯).map φ u = (𝒯).map gW w ∧
      _root_.AlgebraicGeometry.IsClosedImmersion ((𝒯).map j) ∧
      _root_.AlgebraicGeometry.IsFinite ((𝒯).map (j ≫ pullback.snd gW φ)) ∧
      Flat ((𝒯).map (j ≫ pullback.snd gW φ)) ∧
      ∀ v, (𝒯).map (j ≫ pullback.snd gW φ) v = u → (𝒯).map (j ≫ pullback.fst gW φ) v = w := by
  obtain ⟨V, hwV, hV, hrel, Ue, hUe, P₀, j₀, v₀, hjo, hjc, hfin, hv₀, hfibre⟩ :=
    exists_elementaryEtaleNeighborhood_finite_piece ((𝒯).map gW) Z w hw hprin hfib z hz hqf
  let Z₀ := Z.comap V.ι
  let f := Z₀.subschemeι ≫ V.ι ≫ (𝒯).map gW
  -- an affine open of the étale neighbourhood, as a scheme of the site
  obtain ⟨U₁, hU₁, hpt, -⟩ := exists_isAffineOpen_mem_and_subset (X := Ue.scheme) (x := Ue.point)
    (U := ⊤) trivial
  have : IsAffine (U₁ : Scheme.{u}) := hU₁
  have hcU : B.Contains (U₁ : Scheme.{u}) :=
    BigFppfSite.contains_of_locallyOfFinitePresentation B (U₁.ι ≫ Ue.toBase) S₀.left.property
  let U : BigFppfOver B S hS := BigFppfOver.siteObjectOver B S hS S₀ hcU (U₁.ι ≫ Ue.toBase)
  let φ : U ⟶ S₀ := BigFppfOver.siteMapOver B S hS S₀ hcU (U₁.ι ≫ Ue.toBase)
  let u : (𝒯).obj U := (⟨Ue.point, hpt⟩ : (U₁ : Scheme.{u}))
  -- the piece over `U₁`
  let q₀ : P₀ ⟶ Ue.scheme := j₀ ≫ pullback.snd f Ue.toBase
  have : _root_.AlgebraicGeometry.IsFinite q₀ := hfin
  have hfflat : Flat f := hrel.2
  have : _root_.AlgebraicGeometry.IsOpenImmersion j₀ := hjo
  have : Flat q₀ := inferInstance
  let b : (q₀ ⁻¹ᵁ U₁ : Scheme.{u}) ⟶ (U₁ : Scheme.{u}) := q₀ ∣_ U₁
  have hcP : B.Contains (q₀ ⁻¹ᵁ U₁ : Scheme.{u}) :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact b hcU
  let a : (q₀ ⁻¹ᵁ U₁ : Scheme.{u}) ⟶ (𝒯).obj W :=
    (q₀ ⁻¹ᵁ U₁).ι ≫ j₀ ≫ pullback.fst f Ue.toBase ≫ Z₀.subschemeι ≫ V.ι
  have hP := (IsPullback.of_hasPullback gW φ).map (𝒯)
  have hab : a ≫ (𝒯).map gW = b ≫ (𝒯).map φ := by
    change a ≫ (𝒯).map gW = b ≫ U₁.ι ≫ Ue.toBase
    rw [← Category.assoc b, morphismRestrict_ι]
    simp only [a, q₀, f, Category.assoc]
    rw [pullback.condition]
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m : (q₀ ⁻¹ᵁ U₁ : Scheme.{u}) ⟶ (𝒯).obj (pullback gW φ),
      m ≫ (𝒯).map (pullback.fst gW φ) = a ∧ m ≫ (𝒯).map (pullback.snd gW φ) = b :=
    ⟨hP.lift a b hab, hP.lift_fst _ _ _, hP.lift_snd _ _ _⟩
  let P : BigFppfOver B S hS := BigFppfOver.siteObjectOver B S hS (pullback gW φ) hcP m
  let j : P ⟶ pullback gW φ := BigFppfOver.siteMapOver B S hS (pullback gW φ) hcP m
  have hjm : (𝒯).map j = m := rfl
  have hjs : (𝒯).map (j ≫ pullback.snd gW φ) = b := (Functor.map_comp _ _ _).trans hm₂
  have hjf : (𝒯).map (j ≫ pullback.fst gW φ) = a := (Functor.map_comp _ _ _).trans hm₁
  refine ⟨U, P, φ, u, j, ?_, hU₁, ?_, ?_, ?_, ?_, ?_⟩
  · change Etale (U₁.ι ≫ Ue.toBase); infer_instance
  · exact Ue.map_point
  · rw [hjm]
    refine (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono m).2 ⟨?_, ?_⟩
    · have : _root_.AlgebraicGeometry.IsSeparated ((𝒯).map (pullback.snd gW φ)) :=
        MorphismProperty.of_isPullback hP
          (inferInstance : _root_.AlgebraicGeometry.IsSeparated ((𝒯).map gW))
      have : _root_.AlgebraicGeometry.IsProper (m ≫ (𝒯).map (pullback.snd gW φ)) := by
        rw [hm₂]; change _root_.AlgebraicGeometry.IsProper (q₀ ∣_ U₁); infer_instance
      exact _root_.AlgebraicGeometry.IsProper.of_comp m ((𝒯).map (pullback.snd gW φ))
    · refine ⟨fun {T} x₁ x₂ hx => ?_⟩
      have key : ∀ {Y : Scheme.{u}} (k : (𝒯).obj (pullback gW φ) ⟶ Y) (c), m ≫ k = c →
          x₁ ≫ c = x₂ ≫ c :=
        fun k c hc => by simpa only [Category.assoc, hc] using hx =≫ k
      refine (cancel_mono (q₀ ⁻¹ᵁ U₁).ι).1 ((cancel_mono j₀).1 ?_)
      simp only [Category.assoc]
      apply pullback.hom_ext
      · rw [← cancel_mono (Z₀.subschemeι ≫ V.ι)]
        simpa only [a, Category.assoc] using key _ _ hm₁
      · have : x₁ ≫ b = x₂ ≫ b := key _ _ hm₂
        have := this =≫ U₁.ι
        simp only [Category.assoc, b, morphismRestrict_ι] at this
        simpa only [q₀, Category.assoc] using this
  · rw [hjs]; change _root_.AlgebraicGeometry.IsFinite (q₀ ∣_ U₁); infer_instance
  · rw [hjs]; change Flat (q₀ ∣_ U₁); infer_instance
  · intro v hv
    rw [hjs] at hv
    rw [hjf]
    have hv' : (q₀ ∣_ U₁) v = ⟨Ue.point, hpt⟩ := hv
    have h : (q₀ ∣_ U₁ ≫ U₁.ι) v = ((q₀ ⁻¹ᵁ U₁).ι ≫ q₀) v := by rw [morphismRestrict_ι]
    have h1 : q₀ ((q₀ ⁻¹ᵁ U₁).ι v) = Ue.point := by
      have h' : U₁.ι ((q₀ ∣_ U₁) v) = q₀ ((q₀ ⁻¹ᵁ U₁).ι v) := h
      rw [← h', hv']
      rfl
    have h2 : (q₀ ⁻¹ᵁ U₁).ι v = v₀ := by
      have : (q₀ ⁻¹ᵁ U₁).ι v ∈ {y | (j₀ ≫ pullback.snd f Ue.toBase) y = Ue.point} := h1
      rw [hfibre] at this
      exact this
    have e : ∀ y : (q₀ ⁻¹ᵁ U₁ : Scheme.{u}),
        ((q₀ ⁻¹ᵁ U₁).ι ≫ (j₀ ≫ pullback.fst f Ue.toBase ≫ Z₀.subschemeι ≫ V.ι)) y =
          (j₀ ≫ pullback.fst f Ue.toBase ≫ Z₀.subschemeι ≫ V.ι) ((q₀ ⁻¹ᵁ U₁).ι y) := fun y => rfl
    exact (e v).trans (by rw [h2]; exact hv₀)

end AlgebraicGeometry.Space

end
