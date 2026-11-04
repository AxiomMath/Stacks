module

public import StacksCore.Topology.Compact.Image
public import StacksFrontier.AlgebraicGeometry.Descent.AffineSourceEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.CandidateEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.ClosedImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.ImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineHullDescent
public import StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent of quasi-affine morphisms along a surjective étale chart

Quasi-affine morphisms descend effectively along the surjective étale morphisms of the big fppf
site of `S`, which is Stacks 0247 in the shape
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`. Over an affine base object with
an affine chart, the descended object is an open subscheme of `Spec C`, for `C` the ring to which
the datum descends on global sections. As a consequence, effective descent along a surjective
étale chart holds unconditionally for the property of Stacks 02W8.

## Main results

* `AlgebraicGeometry.Scheme.size_Spec_lt_of_injective_sections`: a ring which injects into the
  global sections of an object of `Sch_κ` has its spectrum in `Sch_κ`.
* `AlgebraicGeometry.Space.exists_candidate_object_of_isPushout`: **the candidate object.** From
  the descended ring of a quasi-affine datum over an affine base, an object `T` of the site over
  `a` with `T = Spec C`, a morphism `v ⟶ T` invariant under the datum, and the Cartesian square
  presenting `Spec Γ(v, ⊤)` as `c ×_a T`.
* `AlgebraicGeometry.Space.presheaf_pullback_snd_isQuasiAffineHom_of_affineBase`: Stacks 0247
  over an affine base with an affine chart: the body of
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` at
  `AlgebraicGeometry.IsQuasiAffineHom`, for a datum whose base object and chart source are
  affine.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom`: Stacks 0247
  in the surjective-étale shape, for an arbitrary base object.
* `isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_locallyQuasiFinite_inf_lft`: effective
  descent along a surjective étale chart at the property of Stacks 02W8, unconditionally.

## References

* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry

/-! ### The spectrum of a ring of sections is an object of the site -/

/-- If `κ` is an uncountable strong prelimit cardinal, `V` is a scheme of size less than `κ` and a
ring `C` injects into `Γ(V, ⊤)`, then `Spec C` has size less than `κ`. -/
theorem Scheme.size_Spec_lt_of_injective_sections {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (hsl : Cardinal.IsStrongPrelimit κ) {C : CommRingCat.{u}} {V : Scheme.{u}}
    {p : C ⟶ Γ(V, ⊤)} (hp : Function.Injective p.hom) (hV : V.size < κ) :
    (Spec C).size < κ := by
  rw [Scheme.size_Spec]
  refine max_lt hκ (lt_of_le_of_lt ?_ (hsl hV))
  exact (Cardinal.mk_le_of_injective hp).trans (V.mk_sections_le_two_pow_size ⊤)

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The candidate object -/

/-- **The candidate for the descended object of a quasi-affine datum.** Let `w : v ⟶ c` and
`q : c ⟶ a` be morphisms of the big fppf site of `S` with `a` and `c` affine, let `s, ρ₂` be two
morphisms `P₂ ⟶ v`, and suppose `Γ(v, ⊤)` is the pushout of `Γ(c, ⊤) ← Γ(a, ⊤) → C` along a ring
map `C ⟶ Γ(v, ⊤)` which is injective and equalizes `s` and `ρ₂` on sections. Then `Spec C` is an
object `T` of the site over `a`, the canonical morphism `v ⟶ Spec Γ(v, ⊤) ⟶ T` is a morphism
`kT : v ⟶ T` of the site over `a` on which `s` and `ρ₂` agree, and `Spec Γ(v, ⊤)` is the fibre
product `c ×_a T`. -/
theorem exists_candidate_object_of_isPushout {v c a P₂ : BigFppfOver B S hS} (w : v ⟶ c)
    (q : c ⟶ a) (s ρ₂ : P₂ ⟶ v) (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c)) {C : CommRingCat.{u}}
    {kR : Γ((BigFppfOver.toScheme B S hS).obj a, ⊤) ⟶ C}
    {pR : C ⟶ Γ((BigFppfOver.toScheme B S hS).obj v, ⊤)} (hpinj : Function.Injective pR.hom)
    (po : IsPushout ((BigFppfOver.toScheme B S hS).map q).appTop kR
      ((BigFppfOver.toScheme B S hS).map w).appTop pR)
    (hinvR : pR ≫ ((BigFppfOver.toScheme B S hS).map s).appTop
      = pR ≫ ((BigFppfOver.toScheme B S hS).map ρ₂).appTop) :
    ∃ (T : BigFppfOver B S hS) (i : T ⟶ a) (kT : v ⟶ T)
      (p : Spec Γ((BigFppfOver.toScheme B S hS).obj v, ⊤) ⟶
        (BigFppfOver.toScheme B S hS).obj T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧ kT ≫ i = w ≫ q ∧
        s ≫ kT = ρ₂ ≫ kT ∧
        (BigFppfOver.toScheme B S hS).map kT
          = ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ p ∧
        IsPullback (Spec.map ((BigFppfOver.toScheme B S hS).map w).appTop
            ≫ ((BigFppfOver.toScheme B S hS).obj c).isoSpec.inv) p
          ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map i) := by
  have _ha := ha
  have _hc := hc
  have hCmem : B.Contains (Spec C) :=
    Scheme.size_Spec_lt_of_injective_sections B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
      hpinj v.left.property
  have hpow : Spec.map pR ≫ Spec.map kR
      = Spec.map ((BigFppfOver.toScheme B S hS).map w).appTop
        ≫ Spec.map ((BigFppfOver.toScheme B S hS).map q).appTop := by
    rw [← Spec.map_comp, ← Spec.map_comp, po.w]
  have hkvi : (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map pR)
      ≫ Spec.map kR ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv
      = (BigFppfOver.toScheme B S hS).map (w ≫ q) := by
    calc (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map pR)
          ≫ Spec.map kR ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv
        = ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ (Spec.map pR ≫ Spec.map kR)
            ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv := by
          simp only [Category.assoc]
      _ = ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ
            ≫ (Spec.map ((BigFppfOver.toScheme B S hS).map w).appTop
              ≫ Spec.map ((BigFppfOver.toScheme B S hS).map q).appTop)
            ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv := by rw [hpow]
      _ = (BigFppfOver.toScheme B S hS).map w ≫ (BigFppfOver.toScheme B S hS).map q := by
          simp only [Category.assoc]
          rw [← Scheme.toSpecΓ_naturality_assoc, ← Scheme.toSpecΓ_naturality_assoc,
            Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
      _ = (BigFppfOver.toScheme B S hS).map (w ≫ q) :=
          ((BigFppfOver.toScheme B S hS).map_comp w q).symm
  have hstr : (BigFppfOver.toScheme B S hS).map (w ≫ q) ≫ B.inclusion.map a.hom
      = B.inclusion.map v.hom := by
    have h0 := congrArg B.inclusion.map (Over.w (w ≫ q))
    rw [Functor.map_comp] at h0
    exact h0
  have htri : (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map pR)
      ≫ (Spec.map kR ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv)
        ≫ B.inclusion.map a.hom = B.inclusion.map v.hom := by
    have h1 : (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map pR)
        ≫ (Spec.map kR ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv)
          ≫ B.inclusion.map a.hom
        = (BigFppfOver.toScheme B S hS).map (w ≫ q) ≫ B.inclusion.map a.hom := by
      rw [← hkvi]
      simp only [Category.assoc]
    rw [h1]
    exact hstr
  refine ⟨BigFppfOver.mk B S hS hCmem ((Spec.map kR
      ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv) ≫ B.inclusion.map a.hom),
    Over.homMk (ObjectProperty.homMk (Spec.map kR
      ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv))
      (by apply ObjectProperty.hom_ext; rfl),
    BigFppfOver.homMk B S hS hCmem _
      (((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map pR) ?_,
    Spec.map pR, inferInstanceAs (IsAffine (Spec C)), ?_, ?_, rfl, ?_⟩
  · exact htri
  · refine (BigFppfOver.toScheme B S hS).map_injective ?_
    simp only [Functor.map_comp]
    exact hkvi
  · refine (BigFppfOver.toScheme B S hS).map_injective ?_
    simp only [Functor.map_comp]
    have key : ∀ g : P₂ ⟶ v, (BigFppfOver.toScheme B S hS).map g
          ≫ ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ ≫ Spec.map pR
        = ((BigFppfOver.toScheme B S hS).obj P₂).toSpecΓ
          ≫ Spec.map (pR ≫ ((BigFppfOver.toScheme B S hS).map g).appTop) := by
      intro g
      rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp]
    refine (key s).trans ?_
    rw [hinvR, ← key ρ₂, BigFppfOver.toScheme_map_homMk]
    rfl
  · have HS : IsPullback (Spec.map ((BigFppfOver.toScheme B S hS).map w).appTop)
        (Spec.map pR) (Spec.map ((BigFppfOver.toScheme B S hS).map q).appTop) (Spec.map kR) :=
      (po.op.map Scheme.Spec).flip
    show IsPullback (Spec.map ((BigFppfOver.toScheme B S hS).map w).appTop
        ≫ ((BigFppfOver.toScheme B S hS).obj c).isoSpec.inv) (Spec.map pR)
      ((BigFppfOver.toScheme B S hS).map q)
      (Spec.map kR ≫ ((BigFppfOver.toScheme B S hS).obj a).isoSpec.inv)
    refine HS.of_iso (Iso.refl _) ((BigFppfOver.toScheme B S hS).obj c).isoSpec.symm
      (Iso.refl _) ((BigFppfOver.toScheme B S hS).obj a).isoSpec.symm ?_ ?_ ?_ ?_
    · rw [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    · rw [Iso.symm_hom, Iso.symm_hom]
      exact Scheme.isoSpec_inv_naturality _
    · rw [Iso.refl_hom, Iso.symm_hom, Category.id_comp]

/-! ### Quasi-affine descent over an affine base -/

/-- A property respecting isomorphisms holds for the second projection of any pullback square
once it holds for the second projection of another pullback square on the same cospan. -/
private theorem respectsIso_snd_of_isPullback {C : Type*} [Category C] {P : MorphismProperty C}
    [P.RespectsIso] {W₁ W₂ X Y Z : C} {fst₁ : W₁ ⟶ X} {snd₁ : W₁ ⟶ Y} {fst₂ : W₂ ⟶ X}
    {snd₂ : W₂ ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h₁ : IsPullback fst₁ snd₁ f g)
    (h₂ : IsPullback fst₂ snd₂ f g) (hP : P snd₂) : P snd₁ := by
  rw [← h₁.isoIsPullback_hom_snd _ _ h₂]
  exact MorphismProperty.RespectsIso.precomp _ _ _ hP

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    {a c : BigFppfOver B S hS} {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {m : A ⟶ X} {r : A ⟶ yoneda.obj c}

/-- **Effective descent of quasi-affine morphisms over an affine base with an affine chart.** Let
`f : X ⟶ Y` be a morphism of sheaves on the big fppf site of `S`, let `h : yoneda.obj a ⟶ Y` with
`a` affine, let `q : c ⟶ a` be a surjective étale morphism of the site with `c` affine, and let
`(m, r)` present `A` as the base change of `f` along `yoneda.map q ≫ h`, with `r` representable by
quasi-affine morphisms. Then `X ×[Y] yoneda.obj a ⟶ yoneda.obj a` is representable by
quasi-affine morphisms: the quasi-affine descent datum is effective. -/
theorem presheaf_pullback_snd_isQuasiAffineHom_of_affineBase
    (hXs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hYs : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf r) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  have _ha := ha
  have _hc := hc
  have _hqe := hqe
  have hqf : Flat ((BigFppfOver.toScheme B S hS).map q) := inferInstance
  have _hrioi : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (BigFppfOver.toScheme B S hS))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  obtain ⟨v, w, e, hwqa, hew, P₂, ρ₁, ρ₂, s, sq₂, hs₁, hs₂, Cr, kR, pR, hpinj, po, hinvR⟩ :=
    exists_descentHullPushout_of_isPullback sq hr ha hc hqs hqf
  have vsq : IsPullback (e.inv ≫ m) (yoneda.map w) f (yoneda.map q ≫ h) := by
    refine sq.of_iso e (Iso.refl X) (Iso.refl (yoneda.obj c)) (Iso.refl Y) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, hew]
    · simp
    · simp
  have hvqa : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj v) :=
    (isQuasiAffineHom_iff_isQuasiAffine ((BigFppfOver.toScheme B S hS).map w)).1 hwqa
  have _hvc : CompactSpace ((BigFppfOver.toScheme B S hS).obj v) := inferInstance
  obtain ⟨hvoi, hvqc⟩ :=
    (isQuasiAffineHom_iff_toSpecΓ ((BigFppfOver.toScheme B S hS).map w)).1 hwqa
  obtain ⟨T, i, kT, pT, hTaff, hki, hsk, hFkT, hspec⟩ :=
    exists_candidate_object_of_isPushout w q s ρ₂ ha hc hpinj po hinvR
  have _hTaff := hTaff
  have hinv : ∀ ⦃W : BigFppfOver B S hS⦄ (ζ₁ ζ₂ : W ⟶ v),
      yoneda.map ζ₁ ≫ e.inv ≫ m = yoneda.map ζ₂ ≫ e.inv ≫ m →
      ζ₁ ≫ w ≫ q = ζ₂ ≫ w ≫ q → ζ₁ ≫ kT = ζ₂ ≫ kT := by
    intro W ζ₁ ζ₂ hmζ hqζ
    have cond : (ζ₁ ≫ w) ≫ q = ζ₂ ≫ w ≫ q := by rw [Category.assoc]; exact hqζ
    have hu₁ : sq₂.lift (ζ₁ ≫ w) ζ₂ cond ≫ ρ₁ = ζ₁ ≫ w := sq₂.lift_fst _ _ cond
    have hu₂ : sq₂.lift (ζ₁ ≫ w) ζ₂ cond ≫ ρ₂ = ζ₂ := sq₂.lift_snd _ _ cond
    have hus : sq₂.lift (ζ₁ ≫ w) ζ₂ cond ≫ s = ζ₁ := by
      refine descentAction_unique vsq ?_ ?_
      · rw [Category.assoc, hs₁, hu₁]
      · rw [Functor.map_comp, Category.assoc, hs₂, ← Category.assoc, ← Functor.map_comp, hu₂,
          hmζ]
    rw [← hus, Category.assoc, hsk, ← Category.assoc, hu₂]
  obtain ⟨κ, hκ1, hκ2, sqκ, hκls⟩ : ∃ κ : A ⟶ pullback f h, κ ≫ pullback.fst f h = m ∧
      κ ≫ pullback.snd f h = r ≫ yoneda.map q ∧
      IsPullback κ r (pullback.snd f h) (yoneda.map q) ∧
      Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) κ :=
    ⟨_, (IsPullback.of_hasPullback f h).lift_fst m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]),
      (IsPullback.of_hasPullback f h).lift_snd m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]),
      sq.of_right' (IsPullback.of_hasPullback f h),
      isLocallySurjective_datumToPullback sq hqs hqe⟩
  obtain ⟨g, hgκ, hgfac⟩ := exists_comparison_of_invariant hκ1 hκ2 hκls hki e hew hinv
  have csq : IsPullback (pullback.fst q i) (pullback.snd q i) q i := IsPullback.of_hasPullback q i
  have hq's : Surjective ((BigFppfOver.toScheme B S hS).map (pullback.snd q i)) :=
    MorphismProperty.of_isPullback (csq.map (BigFppfOver.toScheme B S hS)) hqs
  have hq'e : Etale ((BigFppfOver.toScheme B S hS).map (pullback.snd q i)) :=
    MorphismProperty.of_isPullback (csq.map (BigFppfOver.toScheme B S hS)) hqe
  obtain ⟨θ, hθ₁, hθ₂⟩ : ∃ θ : v ⟶ pullback q i, θ ≫ pullback.fst q i = w ∧
      θ ≫ pullback.snd q i = kT :=
    ⟨csq.lift w kT hki.symm, csq.lift_fst _ _ hki.symm, csq.lift_snd _ _ hki.symm⟩
  have sq' : IsPullback κ (e.hom ≫ yoneda.map θ) g (yoneda.map (pullback.snd q i)) := by
    refine IsPullback.of_bot ?_ ?_ ((csq.map yoneda).flip)
    · rw [Category.assoc, ← Functor.map_comp, hθ₁, hew, hgfac]
      exact sqκ
    · rw [hgκ, Category.assoc, ← Functor.map_comp, hθ₂]
  have hθoi : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map θ) := by
    have hcomp : (BigFppfOver.toScheme B S hS).map θ
        = ((BigFppfOver.toScheme B S hS).obj v).toSpecΓ
          ≫ (hspec.isoIsPullback _ _ (csq.map (BigFppfOver.toScheme B S hS))).hom := by
      refine (csq.map (BigFppfOver.toScheme B S hS)).hom_ext ?_ ?_
      · rw [← Functor.map_comp, hθ₁, Category.assoc, hspec.isoIsPullback_hom_fst,
          ← Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
      · rw [← Functor.map_comp, hθ₂, Category.assoc, hspec.isoIsPullback_hom_snd, hFkT]
    rw [hcomp]
    have _ := hvoi
    exact inferInstance
  have hr'oi : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (BigFppfOver.toScheme B S hS)))
      (e.hom ≫ yoneda.map θ) :=
    MorphismProperty.RespectsIso.precomp _ e.hom _
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ θ).2 hθoi)
  have hgp : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (BigFppfOver.toScheme B S hS))) g := by
    have hpred := isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion B S hS g
      (BigFppfOver.isSheaf_pullback_yoneda_obj f h hXs hYs)
      (BigFppfOver.isSheaf_yoneda_obj B S hS T) (𝟙 (yoneda.obj T)) (pullback.snd q i)
      hq's hq'e κ (e.hom ≫ yoneda.map θ) (by rw [Category.comp_id]; exact sq') hr'oi
    exact respectsIso_snd_of_isPullback (IsPullback.id_horiz g)
      (IsPullback.of_hasPullback g (𝟙 (yoneda.obj T))) hpred
  obtain ⟨b, i₀, hi₀oi, j, hj⟩ : ∃ (b : BigFppfOver B S hS) (i₀ : b ⟶ T),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i₀) ∧
      ∃ j : pullback f h ≅ yoneda.obj b, j.hom ≫ yoneda.map i₀ = g :=
    ⟨_, _, hgp.property_snd (𝟙 (yoneda.obj T)), descentObjIso hgp.rep,
      descentObjIso_hom_comp hgp.rep⟩
  obtain ⟨ψ, hψ⟩ := yoneda.map_surjective (e.inv ≫ κ ≫ j.hom)
  have sqψ : IsPullback (yoneda.map ψ) (yoneda.map θ) (yoneda.map i₀)
      (yoneda.map (pullback.snd q i)) := by
    refine sq'.of_iso e j (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · rw [hψ, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id]
    · rw [Iso.refl_hom, Category.comp_id, hj]
    · simp
  have hψs : Surjective ((BigFppfOver.toScheme B S hS).map ψ) :=
    MorphismProperty.of_isPullback
      (((IsPullback.of_map_of_faithful yoneda sqψ).map
        (BigFppfOver.toScheme B S hS)).flip) hq's
  have _hbc : CompactSpace ((BigFppfOver.toScheme B S hS).obj b) := by
    refine ⟨?_⟩
    rw [← Set.range_eq_univ.2 hψs.surj]
    exact isCompact_range (Scheme.Hom.continuous _)
  have _hi₀ := hi₀oi
  have hbqa : Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj b) :=
    Scheme.IsQuasiAffine.of_isImmersion ((BigFppfOver.toScheme B S hS).map i₀)
  have hfinqa : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map (i₀ ≫ i)) :=
    isQuasiAffineHom_of_isQuasiAffine _ hbqa ha
  have sqfin : IsPullback (j.inv ≫ pullback.fst f h) (yoneda.map (i₀ ≫ i)) f h := by
    refine (IsPullback.of_hasPullback f h).of_iso j (Iso.refl X)
      (Iso.refl (yoneda.obj a)) (Iso.refl Y) ?_ ?_ ?_ ?_
    · rw [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · rw [Iso.refl_hom, Category.comp_id, Functor.map_comp, ← Category.assoc, hj, hgfac]
    · simp
    · simp
  exact presheaf_pullback_snd_of_isPullback sqfin hfinqa


/-! ### Quasi-affine descent -/

/-- **Quasi-affine morphisms descend effectively along the surjective étale morphisms of the big
fppf site of `S`.** If the base change of a morphism of sheaves `f : X ⟶ Y` along a surjective
étale chart `q : c ⟶ a` of a representable `yoneda.obj a ⟶ Y` is representable by quasi-affine
morphisms, then so is `X ×[Y] yoneda.obj a ⟶ yoneda.obj a`. -/
@[stacks 0247 "effective descent along a surjective étale chart of the site",
  sga "1 VIII 7.9" "surjective étale cover"]
theorem isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u}) := by
  have _hqari := isQuasiAffineHom_respectsIso.{u}
  intro X Y f hX hY a c h q hqs hqe A m r sq hr
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hstable := MorphismProperty.relative_isStableUnderBaseChange (F := yoneda)
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
  have _hripre := hstable.respectsIso
  choose V u hu hurange hVaff using fun U => BigFppfOver.exists_affineOpen_restrict B S hS a U
  have hucov : ∀ y : (BigFppfOver.toScheme B S hS).obj a,
      ∃ U, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (u U)) := by
    intro y
    have hy : y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj a).Opens) := trivial
    rw [← iSup_affineOpens_eq_top] at hy
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    exact ⟨U, by rw [hurange U]; exact hU⟩
  have key : ∀ U, ∃ (W : BigFppfOver B S hS) (pr : W ⟶ V U)
      (k : yoneda.obj W ⟶ pullback f h),
      _root_.AlgebraicGeometry.IsQuasiAffineHom ((BigFppfOver.toScheme B S hS).map pr) ∧
      IsPullback k (yoneda.map pr) (pullback.snd f h) (yoneda.map (u U)) := by
    intro U
    have hsqsch : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst q (u U)))
        ((BigFppfOver.toScheme B S hS).map (pullback.snd q (u U)))
        ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map (u U)) :=
      (IsPullback.of_hasPullback q (u U)).map (BigFppfOver.toScheme B S hS)
    have hbc : IsPullback (pullback.fst r (yoneda.map (pullback.fst q (u U))))
        (pullback.snd r (yoneda.map (pullback.fst q (u U)))) r
        (yoneda.map (pullback.fst q (u U))) := IsPullback.of_hasPullback _ _
    have heq : yoneda.map (pullback.fst q (u U)) ≫ yoneda.map q ≫ h =
        yoneda.map (pullback.snd q (u U)) ≫ yoneda.map (u U) ≫ h := by
      rw [← Category.assoc, ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp,
        pullback.condition]
    have hdat : IsPullback (pullback.fst r (yoneda.map (pullback.fst q (u U))) ≫ m)
        (pullback.snd r (yoneda.map (pullback.fst q (u U)))) f
        (yoneda.map (pullback.snd q (u U)) ≫ yoneda.map (u U) ≫ h) := by
      rw [← heq]
      exact hbc.paste_horiz sq
    have hr₁ := MorphismProperty.of_isPullback hbc hr
    obtain ⟨c₁, p, hc₁aff, hps, hpe, hpqc⟩ :=
      BigFppfOver.exists_affine_surjective_etale_refinement (hVaff U) (pullback.snd q (u U))
        (MorphismProperty.of_isPullback hsqsch hqs) (MorphismProperty.of_isPullback hsqsch hqe)
    have hbc₂ : IsPullback
        (pullback.fst (pullback.snd r (yoneda.map (pullback.fst q (u U)))) (yoneda.map p))
        (pullback.snd (pullback.snd r (yoneda.map (pullback.fst q (u U)))) (yoneda.map p))
        (pullback.snd r (yoneda.map (pullback.fst q (u U)))) (yoneda.map p) :=
      IsPullback.of_hasPullback _ _
    have hdat₂ : IsPullback
        (pullback.fst (pullback.snd r (yoneda.map (pullback.fst q (u U)))) (yoneda.map p)
          ≫ pullback.fst r (yoneda.map (pullback.fst q (u U))) ≫ m)
        (pullback.snd (pullback.snd r (yoneda.map (pullback.fst q (u U)))) (yoneda.map p)) f
        (yoneda.map (p ≫ pullback.snd q (u U)) ≫ yoneda.map (u U) ≫ h) := by
      have hh := hbc₂.paste_horiz hdat
      simpa only [Functor.map_comp, Category.assoc] using hh
    have hH := presheaf_pullback_snd_isQuasiAffineHom_of_affineBase hX hY (hVaff U) hc₁aff
      hps hpe hdat₂ (MorphismProperty.of_isPullback hbc₂ hr₁)
    have _ : (pullback f (yoneda.map (u U) ≫ h)).IsRepresentable :=
      Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable
        (pullback.snd f (yoneda.map (u U) ≫ h)) hH.rep
    have hsqR := (IsPullback.of_hasPullback f (yoneda.map (u U) ≫ h)).of_right'
      (IsPullback.of_hasPullback f h)
    refine ⟨_, yoneda.preimage ((pullback f (yoneda.map (u U) ≫ h)).reprW.hom
        ≫ pullback.snd f (yoneda.map (u U) ≫ h)),
      (pullback f (yoneda.map (u U) ≫ h)).reprW.hom ≫ (IsPullback.of_hasPullback f h).lift
        (pullback.fst f (yoneda.map (u U) ≫ h))
        (pullback.snd f (yoneda.map (u U) ≫ h) ≫ yoneda.map (u U))
        (by rw [(IsPullback.of_hasPullback f (yoneda.map (u U) ≫ h)).w, Category.assoc]),
      ?_, ?_⟩
    · refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).1 ?_
      rw [Functor.map_preimage]
      exact MorphismProperty.RespectsIso.precomp _ _ _ hH
    · rw [Functor.map_preimage]
      exact hsqR.of_iso' (pullback f (yoneda.map (u U) ≫ h)).reprW (Iso.refl _) (Iso.refl _)
        (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  choose W pr k hprP hpb using key
  obtain ⟨μ, hμ, hbound⟩ := exists_size_bound_of_descentDatum f h q hqs hqe m r sq hr.rep
  have hoi : ∀ U, IsOpenImmersion B S hS (k U) := fun U =>
    isOpenImmersion_of_isPullback_yoneda_map B S hS (hu U) (hpb U)
  have hrepF : (pullback f h).IsRepresentable :=
    isRepresentable_of_zariskiCover_of_size_le B S hS
      (BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY)
      (((BigFppfOver.toScheme B S hS).obj a).mk_affineOpens_le_size.trans_lt a.left.property)
      hμ W (fun U => hbound (W U) (k U) (hoi U)) k hoi
      (isLocallySurjective_sigmaDesc_of_openCover B S hS hu hucov hpb)
  obtain ⟨i, hmapi⟩ := yoneda.map_surjective ((pullback f h).reprW.hom ≫ pullback.snd f h)
  have hfac : pullback.snd f h = (pullback f h).reprW.inv ≫ yoneda.map i := by
    rw [hmapi, Iso.inv_hom_id_assoc]
  rw [hfac]
  refine MorphismProperty.RespectsIso.precomp _ _ _
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ i).2 ?_)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : ((BigFppfOver.toScheme B S hS).obj a).affineOpens =>
      (U.1 : ((BigFppfOver.toScheme B S hS).obj a).Opens))
    (iSup_affineOpens_eq_top _) fun U => ?_
  have _ := hu U
  have hopens : ((BigFppfOver.toScheme B S hS).map (u U)).opensRange
      = (U.1 : ((BigFppfOver.toScheme B S hS).obj a).Opens) :=
    TopologicalSpace.Opens.ext (hurange U)
  rw [← hopens]
  refine (MorphismProperty.arrow_mk_iso_iff
    (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
    (morphismRestrictOpensRange ((BigFppfOver.toScheme B S hS).map i)
      ((BigFppfOver.toScheme B S hS).map (u U)))).mpr ?_
  obtain ⟨ψ, hψ⟩ := yoneda.map_surjective (k U ≫ (pullback f h).reprW.inv)
  have sqψ : IsPullback (yoneda.map ψ) (yoneda.map (pr U)) (yoneda.map i)
      (yoneda.map (u U)) := by
    refine (hpb U).of_iso (Iso.refl _) (pullback f h).reprW.symm (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · rw [hψ, Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, ← hfac]
    · rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  have sqS := (IsPullback.of_map_of_faithful yoneda sqψ).map (BigFppfOver.toScheme B S hS)
  exact respectsIso_snd_of_isPullback (IsPullback.of_hasPullback _ _) sqS (hprP U)


/-! ### Separated locally quasi-finite morphisms -/

/-- Effective descent along the surjective étale morphisms of the big fppf site of `S` for the
separated, locally quasi-finite morphisms which are locally of finite type. -/
@[stacks 02W8 "effective descent along a surjective étale chart of the site"]
theorem isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_locallyQuasiFinite_inf_lft
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) :=
  isEffectiveDescentAlongSurjectiveEtale_isSeparated_locallyQuasiFinite_locallyOfFiniteType
    (isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom B S hS)

end Space

end AlgebraicGeometry

end
