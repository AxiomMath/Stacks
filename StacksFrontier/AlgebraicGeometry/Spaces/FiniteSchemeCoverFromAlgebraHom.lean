module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverFinitenessCertificate
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentationAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeOpenChartCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralPushforwardSupport

/-!
# A finite and finitely presented cover from a finite algebra reaching the integral cover

Let `π : h_Y ⟶ X` be a surjective integral morphism from a scheme to a quasi-compact and
quasi-separated algebraic space, finite étale over a quasi-compact dense open `U ⊆ X`, which
factors Zariski locally on `Y` through an étale `p : h_V ⟶ X` with `V` affine. There are an
étale chart `V_s` (the chart `p` itself) and an affine étale chart `U_s` of `U` and finitely many
sections `s` of `π_* 𝒪_Y` over `V_s` and `s'` over `U_s` such that every finite and finitely
presented quasi-coherent `𝒪_X`-algebra `𝒞` with a morphism `φ : 𝒞 ⟶ π_* 𝒪_Y` reaching them
gives a cover as in Stacks 0GUN.

## The argument

Let `P = \underline{Spec}_X(𝒞)`, finite and of finite presentation over `X`, and `g : Y ⟶ P` the
morphism over `X` of `φ`. Over the chart `V` the cover `W = Y ×_X V` is affine, and the graphs of
the local factorizations of `π` through `p` contain finitely many basic opens `D(q_k) ⊆ W`
mapping isomorphically onto opens of `Y` covering it
(`AlgebraicGeometry.Space.exists_basicOpens_mono_of_factorsZariskiLocallyThrough`); `s` is the
`q_k`. If `φ` reaches them, `q_k` is the pullback of a function `b_k` on `Z = P ×_X V`, so that
`D(q_k)` is the base change of `D(b_k)` along `g`, and the charts `D(b_k) ⟶ P` become
monomorphisms over `Y`, hence over the scheme-theoretic image `C` of `g`, whose points are those of
`g(Y)` since `g` is integral
(`AlgebraicGeometry.Space.preimage_le_range_diagonal_of_mono_pullback_snd`). Over the chart `U_s`
the sections `s'` generate `π_* 𝒪_Y`, so `g` is a closed immersion there, and `C` is finite étale
over `U` because its base change to `U_s` is that of `Y`
(`AlgebraicGeometry.Space.isFinite_isEtale_pullback_fst_of_preimage_eq_range`, through Stacks
082Z (3)). Then `AlgebraicGeometry.Space.exists_finiteSchemeCover_of_isEtaleSectionClosed`
applies.

## Main results

* `AlgebraicGeometry.Space.isFinite_of_isFinite_pushforwardAlgebra`.
* `AlgebraicGeometry.Space.exists_finiteSchemeCover_of_algebraHom`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- The base change of an affine morphism of algebraic spaces to an affine chart is affine. -/
private theorem isAffine_pullback_of_isAffineHom {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hf : IsAffineHom B S hS f) (hr : yoneda.relativelyRepresentable f) {V : BigFppfOver B S hS}
    (p : yoneda.obj V ⟶ G) (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (hr.pullback p)) := by
  have hf' := ((isAffineHom_tfae_of_isAlgebraicSpace B S hS f hF hG).out 2 1).mp hf
  exact @isAffine_of_isAffineHom _ _ ((BigFppfOver.toScheme B S hS).map (hr.snd p))
    (hf'.2.property p (hr.fst p) (hr.snd p) (hr.isPullback p)) hV

/-- **A space affine over a quasi-compact base whose direct-image algebra is finite on the affine
étale charts is finite over the base.** -/
theorem isFinite_of_isFinite_pushforwardAlgebra {X : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (Z : AffineOver B S hS X)
    (hfin : (pushforwardAlgebra B S hS Z.obj).IsFinite) :
    IsFinite B S hS Z.obj.hom.hom := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨U, hUaff, husurj⟩ := exists_smallEtale_isAffine_surjective B S hS hXqc
  have : IsAffine (T.obj U.1.left) := hUaff
  have hZ : yoneda.relativelyRepresentable Z.obj.hom.hom :=
    relativelyRepresentable_of_isAffineHom B S hS Z.obj.hom Z.property
  have : IsAffine (T.obj (hZ.pullback U.1.hom)) :=
    isAffine_pullback_of_isAffineHom B S hS _ Z.obj.left.2 X.2 Z.property hZ _ hUaff
  have happ : RingHom.Finite (T.map (hZ.snd U.1.hom)).appTop.hom := by
    rw [← fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS Z.obj hZ U]
    have h1 : RingHom.Finite
        ((smallEtaleRingedToposHom B S hS Z.obj.hom).fSharp.hom.app (op U)).hom := hfin U hUaff
    have h2 : RingHom.Finite
        (CommRingCat.Hom.hom (pushforwardAlgebraSectionsIso B S hS Z.obj hZ U).hom) :=
      RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact h2.comp h1
  have hfinZ : _root_.AlgebraicGeometry.IsFinite (T.map (hZ.snd U.1.hom)) := by
    have : MorphismProperty.RespectsIso
        (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff _
      (arrowIsoSpecΓOfIsAffine (T.map (hZ.snd U.1.hom)))).2 ((IsFinite.SpecMap_iff _).2 happ)
  refine isFinite_of_surjectiveEtaleChart B S hS Z.obj.left.2 X.2 _
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 _ U.1.hom).1 husurj)
    (isEtale_of_presheaf_etale B S hS U.2) ?_
  rw [← (hZ.isPullback U.1.hom).isoPullback_inv_snd]
  exact isFinite_comp B S hS (isFinite_of_isIso B S hS _)
    ((isFinite_yoneda_map_iff B S hS _).2 hfinZ)

/-- A function on the base change of `Y` to a chart `W` whose image under `σY.inv` comes from the
direct-image map of `g` comes from the base-change map `Y ×_X W ⟶ Z ×_X W`. -/
private theorem mem_range_appTop_smallBaseChangeOverMap {X : AlgebraicSpaces B S hS}
    {Y Z : Over X} (g : Y ⟶ Z) (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (W : SmallEtale B S hS X.1)
    {x : Γ((BigFppfOver.toScheme B S hS).obj (hY.pullback W.obj.hom), ⊤)}
    (hx : (pushforwardAlgebraSectionsIso B S hS Y hY W).inv x ∈
      Set.range ((pushforwardRingMap B S hS g).hom.app (op W))) :
    x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
      (smallBaseChangeOverMap B S hS g hY hZ W)).appTop.hom := by
  obtain ⟨c, hc⟩ := hx
  refine ⟨(pushforwardAlgebraSectionsIso B S hS Z hZ W).hom c, ?_⟩
  rw [← pushforwardRingMap_app_eq B S hS g hY hZ W]
  change (pushforwardAlgebraSectionsIso B S hS Y hY W).hom
    ((pushforwardRingMap B S hS g).hom.app (op W) ((pushforwardAlgebraSectionsIso B S hS Z hZ W).inv
      ((pushforwardAlgebraSectionsIso B S hS Z hZ W).hom c))) = x
  rw [Iso.hom_inv_id_apply, hc]
  exact Iso.inv_hom_id_apply _ x

/-- **The base change of a morphism over `X` to an affine chart is surjective on functions as soon
as the direct-image map reaches generators.** -/
theorem surjective_appTop_smallBaseChangeOverMap {X : AlgebraicSpaces B S hS} {Y Z : Over X}
    (g : Y ⟶ Z) (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (W : SmallEtale B S hS X.1)
    (t : Finset Γ((BigFppfOver.toScheme B S hS).obj (hY.pullback W.obj.hom), ⊤))
    (hgen : ∀ R' : Subring Γ((BigFppfOver.toScheme B S hS).obj (hY.pullback W.obj.hom), ⊤),
      Set.range ((BigFppfOver.toScheme B S hS).map (hY.snd W.obj.hom)).appTop.hom ⊆
        SetLike.coe R' → (∀ x ∈ t, x ∈ R') → R' = ⊤)
    (ht : ∀ x ∈ t, (pushforwardAlgebraSectionsIso B S hS Y hY W).inv x ∈
      Set.range ((pushforwardRingMap B S hS g).hom.app (op W))) :
    Function.Surjective
      ((BigFppfOver.toScheme B S hS).map (smallBaseChangeOverMap B S hS g hY hZ W)).appTop.hom := by
  let T := BigFppfOver.toScheme B S hS
  let m := smallBaseChangeOverMap B S hS g hY hZ W
  have hms_snd : T.map m ≫ T.map (hZ.snd W.obj.hom) = T.map (hY.snd W.obj.hom) := by
    rw [← Functor.map_comp]
    exact congrArg T.map (smallBaseChangeOverMap_snd B S hS g hY hZ W)
  have hsub₁ : Set.range (T.map (hY.snd W.obj.hom)).appTop.hom ⊆
      SetLike.coe (T.map m).appTop.hom.range := by
    rintro _ ⟨r, rfl⟩
    refine ⟨(T.map (hZ.snd W.obj.hom)).appTop r, ?_⟩
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply] using congrArg (fun f => f.appTop.hom r) hms_snd
  exact RingHom.range_eq_top.1 (hgen _ hsub₁ fun x hx =>
    mem_range_appTop_smallBaseChangeOverMap B S hS g hY hZ W (ht x hx))

/-- The first projection of the base change of a representable morphism along an étale morphism
from an object of the site is étale. -/
private theorem isEtale_fst_of_isEtale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hr : yoneda.relativelyRepresentable f) {V : BigFppfOver B S hS} (p : yoneda.obj V ⟶ G)
    (hp : IsEtale B S hS p) : IsEtale B S hS (hr.fst p) :=
  isEtale_of_isPullback_of_isAlgebraicSpace B S hS (hr.isPullback p)
    (isAlgebraicSpace_yoneda B S hS _) hF (isAlgebraicSpace_yoneda B S hS V) hG hp

/-- The range of the second projection of a pullback is that of any cartesian square. -/
theorem range_pullback_snd_eq_of_isPullback {F G H K : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {fst : K ⟶ F} {snd : K ⟶ G} {f : F ⟶ H} {g : G ⟶ H} (sq : IsPullback fst snd f g) :
    Subfunctor.range (pullback.snd f g) = Subfunctor.range snd := by
  rw [← sq.isoPullback_inv_snd, Subfunctor.range_comp,
    @Subfunctor.range_eq_top _ _ _ _ _ (IsIso.epi_of_iso _), Subfunctor.image_top]

/-- The preimage of the scheme-theoretic image of a quasi-compact morphism under an étale morphism
is the scheme-theoretic image of any morphism with the same range as the base change. -/
private theorem preimage_schemeTheoreticImageSubfunctor_eq
    {F G V W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : V ⟶ G) (m : W ⟶ V)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hV : IsAlgebraicSpace B S hS V) (hf : IsQuasiCompact B S hS f) (hg : IsEtale B S hS g)
    (h : Subfunctor.range (pullback.snd f g) = Subfunctor.range m) :
    (schemeTheoreticImageSubfunctor B S hS f).preimage g =
      schemeTheoreticImageSubfunctor B S hS m := by
  rw [← schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS f g hF hG
    hV hf hg, schemeTheoreticImageSubfunctor_congr_range' B S hS _ m hV h]

/-- **Monic equations for generators.** If `f : R →+* A` is of finite type and `h : A →+* B`
makes `B` integral over `R`, then monic equations over `R` for generators of `A`, read in `A`,
generate an ideal of finite type killed by `h` with finite quotient over `R`. -/
theorem exists_ideal_fg_finite_le_ker_of_isIntegral {R A C : Type u} [CommRing R] [CommRing A]
    [CommRing C] (f : R →+* A) (hf : f.FiniteType) (h : A →+* C) (hint : (h.comp f).IsIntegral) :
    ∃ I : Ideal A, I.FG ∧ RingHom.Finite ((Ideal.Quotient.mk I).comp f) ∧
      I ≤ RingHom.ker h := by
  classical
  let := f.toAlgebra
  obtain ⟨zs, hzs⟩ := hf.out
  choose P hPmonic hPeval using fun z : A => hint (h z)
  refine ⟨Ideal.span ((fun z => Polynomial.eval₂ f z (P z)) '' (zs : Set A)), ?_,
    finite_comp_quotient_span_eval₂ f zs hzs P fun z _ => hPmonic z, ?_⟩
  · exact ⟨zs.image fun z => Polynomial.eval₂ f z (P z), by rw [Finset.coe_image]⟩
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨z, -, rfl⟩
    change h (Polynomial.eval₂ f z (P z)) = 0
    rw [Polynomial.hom_eval₂]
    exact hPeval z

/-- **Monic equations on a chart.** Let `g : Y ⟶ Z` be a morphism over `X` of spaces with
representable structure morphisms and `W` an étale chart of `X`, with the direct-image algebra of
`Z` of finite type over `W` and `Y ×_X W ⟶ W` integral on functions. Then an ideal `I` of finite
type of the functions on `Z ×_X W`, killed on `Y ×_X W`, makes the quotient finite over `W`. -/
theorem exists_ideal_finite_le_ker_smallBaseChangeOverMap {X : AlgebraicSpaces B S hS}
    {Y Z : Over X} (g : Y ⟶ Z) (hY : yoneda.relativelyRepresentable Y.hom.hom)
    (hZ : yoneda.relativelyRepresentable Z.hom.hom) (W : SmallEtale B S hS X.1)
    (hft : RingHom.FiniteType ((pushforwardAlgebra B S hS Z).algebraMap (op W)))
    (hint : RingHom.IsIntegral
      ((BigFppfOver.toScheme B S hS).map (hY.snd W.obj.hom)).appTop.hom) :
    ∃ I : Ideal Γ((BigFppfOver.toScheme B S hS).obj (hZ.pullback W.obj.hom), ⊤), I.FG ∧
      RingHom.Finite ((Ideal.Quotient.mk I).comp
        ((BigFppfOver.toScheme B S hS).map (hZ.snd W.obj.hom)).appTop.hom) ∧
      I ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map
        (smallBaseChangeOverMap B S hS g hY hZ W)).appTop.hom := by
  have hf₀ : ((BigFppfOver.toScheme B S hS).map (hZ.snd W.obj.hom)).appTop.hom =
      (pushforwardAlgebraSectionsIso B S hS Z hZ W).hom.hom.comp
        ((pushforwardAlgebra B S hS Z).algebraMap (op W)) :=
    (congrArg CommRingCat.Hom.hom
      (fSharp_app_comp_pushforwardAlgebraSectionsIso B S hS Z hZ W)).symm
  have hft₀ : RingHom.FiniteType
      ((BigFppfOver.toScheme B S hS).map (hZ.snd W.obj.hom)).appTop.hom := by
    rw [hf₀]
    exact hft.comp_surjective
      (ConcreteCategory.bijective_of_isIso (pushforwardAlgebraSectionsIso B S hS Z hZ W).hom).2
  have hm_snd : ((BigFppfOver.toScheme B S hS).map
      (smallBaseChangeOverMap B S hS g hY hZ W)).appTop.hom.comp
        ((BigFppfOver.toScheme B S hS).map (hZ.snd W.obj.hom)).appTop.hom =
      ((BigFppfOver.toScheme B S hS).map (hY.snd W.obj.hom)).appTop.hom := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ← Functor.map_comp,
      smallBaseChangeOverMap_snd]
  exact exists_ideal_fg_finite_le_ker_of_isIntegral _ hft₀ _ (hm_snd ▸ hint)

/-- **Monic equations on a chart cut a finite cover out of a closed subspace.** Let `g : Y ⟶ Z` be
a morphism over `X`, with `Y` integral and `Z` affine of finite presentation over `X`, the
direct-image algebra of `Z` of finite type on an affine surjective étale chart `V` of `X`. If the
scheme-theoretic image `C` of `g` is a closed subspace on which étale charts `Γ k ⟶ Z` over `V` are
monomorphisms covering it, surjective over `X` and finite étale over a quasi-compact dense open
`U`, then there is a finite and finitely presented scheme cover of `X`, finite étale over `U`,
factoring Zariski locally through `V`. -/
theorem exists_finiteSchemeCover_of_monicEquations (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) {Yo Zo : Over X} (g : Yo ⟶ Zo)
    (hY : yoneda.relativelyRepresentable Yo.hom.hom)
    (hZr : yoneda.relativelyRepresentable Zo.hom.hom) (hYint : IsIntegralHom B S hS Yo.hom.hom)
    (hZa : IsAffineHom B S hS Zo.hom.hom) (hZfp : IsFinitePresentation B S hS Zo.hom.hom)
    (Vs : SmallEtale B S hS X.1) [IsAffine ((BigFppfOver.toScheme B S hS).obj Vs.obj.left)]
    (hpsurj : IsSurjective B S hS Vs.obj.hom) (hp : IsEtale B S hS Vs.obj.hom)
    (hft : RingHom.FiniteType ((pushforwardAlgebra B S hS Zo).algebraMap (op Vs)))
    {n : ℕ} {Γ : Fin n → BigFppfOver B S hS}
    (hΓ : ∀ k, CompactSpace ((BigFppfOver.toScheme B S hS).obj (Γ k)))
    (gk : ∀ k, yoneda.obj (Γ k) ⟶ Zo.left.1) (hgk : ∀ k, IsEtale B S hS (gk k))
    (hk : ∀ k, yoneda.obj (Γ k) ⟶ yoneda.obj Vs.obj.left)
    (hgh : ∀ k, gk k ≫ Zo.hom.hom = hk k ≫ Vs.obj.hom)
    (C : ClosedSubspaces B S hS Zo.left.1) (hC : IsEtaleSectionClosed B S hS gk C.1)
    (hCsurj : IsSurjective B S hS (C.1.ι ≫ Zo.hom.hom))
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hUdense : Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)))
    (hCUfin : IsFinite B S hS (pullback.fst U.ι (C.1.ι ≫ Zo.hom.hom)))
    (hCUet : IsEtale B S hS (pullback.fst U.ι (C.1.ι ≫ Zo.hom.hom)))
    (hgqc : IsQuasiCompact B S hS g.left.hom)
    (hCimg : C.1 = schemeTheoreticImageSubfunctor B S hS g.left.hom) :
    ∃ (Y' : BigFppfOver B S hS) (f : yoneda.obj Y' ⟶ X.1),
      IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS Y' f U ∧
        FactorsZariskiLocallyThrough B S hS Vs.obj.hom Y' f := by
  let T := BigFppfOver.toScheme B S hS
  let p := Vs.obj.hom
  have : IsAffine (T.obj (hZr.pullback p)) :=
    isAffine_pullback_of_isAffineHom B S hS _ Zo.left.2 X.2 hZa hZr p inferInstance
  -- `Y ×_X V ⟶ V` is integral.
  have hsch : _root_.AlgebraicGeometry.IsIntegralHom (T.map (hY.snd p)) :=
    (presheaf_isIntegralHom_of_isIntegralHom Yo.hom.hom hY hYint).property p (hY.fst p)
      (hY.snd p) (hY.isPullback p)
  have : IsAffine (T.obj (hY.pullback p)) := isAffine_of_isAffineHom (T.map (hY.snd p))
  have hWint : RingHom.IsIntegral (T.map (hY.snd p)).appTop.hom := by
    have : MorphismProperty.RespectsIso
        (@_root_.AlgebraicGeometry.IsIntegralHom.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (IsIntegralHom.SpecMap_iff).1 ((MorphismProperty.arrow_mk_iso_iff _
      (arrowIsoSpecΓOfIsAffine (T.map (hY.snd p)))).1 hsch)
  obtain ⟨I, hIfg, hI, hIker⟩ :=
    exists_ideal_finite_le_ker_smallBaseChangeOverMap B S hS g hY hZr Vs hft hWint
  let m := smallBaseChangeOverMap B S hS g hY hZr Vs
  have sqV : IsPullback (hY.fst p) (yoneda.map m) g.left.hom (hZr.fst p) :=
    isPullback_fst_smallBaseChangeOverMap B S hS g hY hZr Vs
  have hPfst : IsEtale B S hS (hZr.fst p) := isEtale_fst_of_isEtale B S hS _ Zo.left.2 X.2 hZr p hp
  have hle : Scheme.IdealSheafData.ofIdealTop I ≤ (T.map m).ker := by
    rw [Scheme.ker_of_isAffine]
    exact (map_le_map_iff (Scheme.IdealSheafData.equivOfIsAffine
      (X := T.obj (hZr.pullback p))).symm).2 hIker
  have hJtC : Scheme.IdealSheafData.ofIdealTop I ≤ chartKer B S hS Zo.left C (hZr.fst p) := by
    have hrV : Subfunctor.range (pullback.snd g.left.hom (hZr.fst p)) =
        Subfunctor.range (yoneda.map m) := range_pullback_snd_eq_of_isPullback B S hS sqV
    rw [le_chartKer_iff, hCimg, preimage_schemeTheoreticImageSubfunctor_eq B S hS _ _ (yoneda.map m)
      Yo.left.2 Zo.left.2 (isAlgebraicSpace_yoneda B S hS _) hgqc hPfst hrV]
    exact schemeTheoreticImageSubfunctor_le B S hS _ (isClosedSubspace_idealPoints _)
      (range_yoneda_map_le_idealPoints B S hS m _ hle)
  have hJt : (Scheme.IdealSheafData.ofIdealTop I).IsFiniteType := fun W => by
    rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    exact hIfg.map _
  exact exists_finiteSchemeCover_of_isEtaleSectionClosed B S hS hZ X.2 hXqc hXqs Zo.left
    Zo.hom.hom hZa hZfp p hΓ gk hgk hk hgh C hC hCsurj U hU hUqc hUdense hCUfin hCUet (hZr.fst p)
    ((isEtale_iff_presheaf_of_yoneda B S hS _).1 hPfst) _ hJt hJtC
    (fun Tc hT => isFinite_ι_comp_of_ofIdealTop_le_chartKer B S hS X.2 Zo.left Zo.hom.hom p hpsurj
      hp (hZr.fst p) (hZr.snd p) (hZr.isPullback p) I hI Tc hT)

/-- **A finite and finitely presented cover from a finite algebra reaching the integral cover.**
See the module documentation. -/
theorem exists_finiteSchemeCover_of_algebraHom (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {Y : BigFppfOver B S hS} (π : yoneda.obj Y ⟶ X.1) (hπint : IsIntegralHom B S hS π)
    (hπsurj : IsSurjective B S hS π) (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hUdense : Dense (Set.range (pointsMap B S hS U.toFunctor U.ι)))
    (hπUfin : IsFinite B S hS (pullback.fst U.ι π)) (hπUet : IsEtale B S hS (pullback.fst U.ι π))
    {V : BigFppfOver B S hS} (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (p : yoneda.obj V ⟶ X.1) (hp : IsEtale B S hS p) (hpsurj : IsSurjective B S hS p)
    (hfac : FactorsZariskiLocallyThrough B S hS p Y π) :
    ∃ (Vs Us : SmallEtale B S hS X.1) (_ : IsAffine (chartScheme Vs))
      (_ : IsAffine (chartScheme Us))
      (s : Finset ((pushforwardAlgebra B S hS (Over.mk (ObjectProperty.homMk π :
        (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ :
          AlgebraicSpaces B S hS) ⟶ X))).right.obj.obj
          (op Vs)))
      (s' : Finset ((pushforwardAlgebra B S hS (Over.mk (ObjectProperty.homMk π :
        (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ :
          AlgebraicSpaces B S hS) ⟶ X))).right.obj.obj
          (op Us))),
      ∀ (C : QuasicoherentAlgebra B S hS X) (_ : AlgebraSheaf.SectionsBelowCutoff B S hS C.obj),
        C.obj.IsFinitePresentation →
        ∀ φ : C.obj ⟶ pushforwardAlgebra B S hS (Over.mk (ObjectProperty.homMk π :
          (⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩ : AlgebraicSpaces B S hS) ⟶ X)),
          (s : Set _) ⊆ Set.range (φ.right.hom.app (op Vs)) →
          (s' : Set _) ⊆ Set.range (φ.right.hom.app (op Us)) →
          ∃ (Y' : BigFppfOver B S hS) (f : yoneda.obj Y' ⟶ X.1),
            IsFiniteSchemeCoverFiniteEtaleOverDenseOpen B S hS Y' f U ∧
              FactorsZariskiLocallyThrough B S hS p Y' f := by
  classical
  let T := BigFppfOver.toScheme B S hS
  let Ya : AlgebraicSpaces B S hS := ⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩
  let Yo : Over X := Over.mk (ObjectProperty.homMk π : Ya ⟶ X)
  have hπaff : IsAffineHom B S hS π := isAffineHom_of_isIntegralHom π hπint
  have hYrep : yoneda.relativelyRepresentable π :=
    relativelyRepresentable_of_isAffineHom B S hS (ObjectProperty.homMk π : Ya ⟶ X) hπaff
  -- The chart `V`.
  let Vs : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk p, (isEtale_iff_presheaf_of_yoneda B S hS p).1 hp⟩
  have : IsAffine (T.obj V) := hV
  have hWaff : IsAffine (T.obj (hYrep.pullback p)) :=
    isAffine_pullback_of_isAffineHom B S hS π Ya.2 X.2 hπaff hYrep p hV
  have hYqc : CompactSpace (T.obj Y) :=
    compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
      (isQuasiCompactSpace_source_of_isQuasiCompact B S hS X.2 hXqc
        (isQuasiCompact_of_isIntegralHom π Ya.2 X.2 hπint))
  obtain ⟨n, q, hqmono, hqcov⟩ := exists_basicOpens_mono_of_factorsZariskiLocallyThrough B S hS
    X.2 π hYrep hYqc p hp hWaff hfac
  -- The chart `U₀` of `U`, over which `π` is finite étale.
  obtain ⟨U₀, u₀, hU₀aff, hu₀s, hu₀e⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS U.toFunctor hU.1).1 hUqc
  have hu₀U : IsEtale B S hS (u₀ ≫ U.ι) := isEtale_comp B S hS hu₀e (isEtale_ι_of_isOpenSubspace hU)
  let Us : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (u₀ ≫ U.ι), (isEtale_iff_presheaf_of_yoneda B S hS _).1 hu₀U⟩
  have : IsAffine (T.obj U₀) := hU₀aff
  have hWsaff : IsAffine (T.obj (hYrep.pullback (u₀ ≫ U.ι))) :=
    isAffine_pullback_of_isAffineHom B S hS π Ya.2 X.2 hπaff hYrep _ hU₀aff
  have hsqU := isPullback_lift_pullback_fst B S hS π U u₀ (hYrep.fst (u₀ ≫ U.ι))
    (yoneda.map (hYrep.snd (u₀ ≫ U.ι))) (hYrep.isPullback (u₀ ≫ U.ι))
  have hWsfin : _root_.AlgebraicGeometry.IsFinite (T.map (hYrep.snd (u₀ ≫ U.ι))) :=
    (presheaf_yoneda_map_iff B S hS (P := @_root_.AlgebraicGeometry.IsFinite.{u}) inferInstance _).1
      (presheaf_isFinite_of_isFinite _ (Functor.relativelyRepresentable.map yoneda _)
        (isFinite_of_isPullback B S hS hsqU hπUfin))
  have hWset : Etale (T.map (hYrep.snd (u₀ ≫ U.ι))) :=
    etale_of_isEtale_yoneda_map B S hS (isEtale_of_isPullback_of_isAlgebraicSpace B S hS hsqU.flip
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS U₀)
      (isAlgebraicSpace_pullback B S hS _ _ hU.1 Ya.2 X.2) hU.1 hπUet)
  -- Finitely many generators of the sections of `π_* 𝒪_Y` over `U₀`.
  obtain ⟨t, ht⟩ : ∃ t : Finset Γ(T.obj (hYrep.pullback (u₀ ≫ U.ι)), ⊤),
      ∀ R' : Subring Γ(T.obj (hYrep.pullback (u₀ ≫ U.ι)), ⊤),
        Set.range (T.map (hYrep.snd (u₀ ≫ U.ι))).appTop.hom ⊆ SetLike.coe R' →
          (∀ x ∈ t, x ∈ R') → R' = ⊤ := by
    let := (T.map (hYrep.snd (u₀ ≫ U.ι))).appTop.hom.toAlgebra
    obtain ⟨t, ht⟩ := (Scheme.Hom.finite_appTop (T.map (hYrep.snd (u₀ ≫ U.ι)))).finiteType.out
    refine ⟨t, fun R' hR' htR' => ?_⟩
    let R'' : Subalgebra Γ(T.obj U₀, ⊤) Γ(T.obj (hYrep.pullback (u₀ ≫ U.ι)), ⊤) :=
      { R' with algebraMap_mem' := fun r => hR' ⟨r, rfl⟩ }
    have hle : Algebra.adjoin Γ(T.obj U₀, ⊤) (t : Set _) ≤ R'' :=
      Algebra.adjoin_le fun x hx => htR' x hx
    rw [ht] at hle
    exact eq_top_iff.2 fun x _ => hle Algebra.mem_top
  -- The finitely many sections.
  let σV := pushforwardAlgebraSectionsIso B S hS Yo hYrep Vs
  let σU := pushforwardAlgebraSectionsIso B S hS Yo hYrep Us
  refine ⟨Vs, Us, hV, hU₀aff, Finset.univ.image fun k => σV.inv (q k),
    t.image fun x => σU.inv x, ?_⟩
  intro 𝒞 h𝒞 hCfp φ hs hs'
  -- The relative spectrum `P` of `𝒞`, and the morphism `g : Y ⟶ P` of `φ`.
  let P := boundedRelativeSpec B S hS 𝒞 h𝒞
  let e := pushforwardAlgebraBoundedRelativeSpecIso B S hS 𝒞 h𝒞
  let g : Yo ⟶ P.obj := (overHomEquivPushforwardAlgebraHom B S hS Yo P).symm (e.hom ≫ φ)
  have hgalg : pushforwardAlgebraMap B S hS g = e.hom ≫ φ :=
    pushforwardAlgebraMap_overHomEquivPushforwardAlgebraHom_symm B S hS Yo P _
  have hinvhom : ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ) (c : 𝒞.obj.right.obj.obj W),
      (e.hom.right.hom.app W) ((e.inv.right.hom.app W) c) = c := fun W c =>
    congrArg (fun k : 𝒞.obj ⟶ 𝒞.obj => (k.right.hom.app W) c) e.inv_hom_id
  have hhominv : ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ)
      (c : (pushforwardAlgebra B S hS P.obj).right.obj.obj W),
      (e.inv.right.hom.app W) ((e.hom.right.hom.app W) c) = c := fun W c =>
    congrArg (fun k : pushforwardAlgebra B S hS P.obj ⟶ pushforwardAlgebra B S hS P.obj =>
      (k.right.hom.app W) c) e.hom_inv_id
  -- the image of `φ` lies in the image of the ring map of `g`
  have hrange : ∀ (W : (SmallEtale B S hS X.1)ᵒᵖ)
      (x : (pushforwardAlgebra B S hS Yo).right.obj.obj W), x ∈ Set.range (φ.right.hom.app W) →
        x ∈ Set.range ((pushforwardRingMap B S hS g).hom.app W) := by
    rintro W _ ⟨c, rfl⟩
    refine ⟨(e.inv.right.hom.app W) c, ?_⟩
    rw [← pushforwardAlgebraMap_right, hgalg]
    change (φ.right.hom.app W) ((e.hom.right.hom.app W) ((e.inv.right.hom.app W) c)) = _
    rw [hinvhom]
  have hPalgfp : (pushforwardAlgebra B S hS P.obj).IsFinitePresentation := by
    intro W hW
    have hbij : Function.Bijective (e.inv.right.hom.app (op W)).hom :=
      Function.bijective_iff_has_inverse.2 ⟨e.hom.right.hom.app (op W),
        hinvhom (op W), hhominv (op W)⟩
    rw [← AlgebraSheaf.comp_algebraMap e.inv (op W)]
    exact (RingEquiv.finitePresentation (RingEquiv.ofBijective _ hbij)).comp (hCfp W hW)
  have hPfp : IsFinitePresentation B S hS P.obj.hom.hom :=
    isFinitePresentation_of_isFinitePresentation_pushforwardAlgebra B S hS hXqc P hPalgfp
  -- `P` and `g` over the chart `V`.
  let qP : P.obj.left.1 ⟶ X.1 := P.obj.hom.hom
  let gY : yoneda.obj Y ⟶ P.obj.left.1 := g.left.hom
  have hgq : gY ≫ qP = π := by
    rw [← ObjectProperty.FullSubcategory.comp_hom]
    exact congrArg (fun m : Yo.left ⟶ X => m.hom) (Over.w g)
  have hPrep : yoneda.relativelyRepresentable qP :=
    relativelyRepresentable_of_isAffineHom B S hS P.obj.hom P.property
  have hZaff : IsAffine (T.obj (hPrep.pullback p)) :=
    isAffine_pullback_of_isAffineHom B S hS qP P.obj.left.2 X.2 P.property hPrep p hV
  let m := smallBaseChangeOverMap B S hS g hYrep hPrep Vs
  have sqV : IsPullback (hYrep.fst p) (yoneda.map m) gY (hPrep.fst p) :=
    isPullback_fst_smallBaseChangeOverMap B S hS g hYrep hPrep Vs
  -- The functions `b k` on `Z = P ×_X V` pulling back to the `q k`.
  have hb : ∀ k, ∃ b : Γ(T.obj (hPrep.pullback p), ⊤), (T.map m).appTop b = q k := by
    intro k
    exact mem_range_appTop_smallBaseChangeOverMap B S hS g hYrep hPrep Vs (x := q k)
      (hrange _ _ (hs (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ k)))))
  choose b hb using hb
  -- The charts `D(b k) ⟶ P`.
  let O : Fin n → (T.obj (hPrep.pullback p)).Opens := fun k =>
    (T.obj (hPrep.pullback p)).basicOpen (b k)
  have hO : ∀ k, T.map m ⁻¹ᵁ O k = (T.obj (hYrep.pullback p)).basicOpen (q k) := by
    intro k
    rw [← hb k]
    exact Scheme.preimage_basicOpen_top (T.map m) (b k)
  have hPfst : IsEtale B S hS (hPrep.fst p) :=
    isEtale_fst_of_isEtale B S hS _ P.obj.left.2 X.2 hPrep p hp
  let gk : ∀ k, yoneda.obj (openSub _ (O k)) ⟶ P.obj.left.1 := fun k =>
    yoneda.map (openSubHom _ (O k)) ≫ hPrep.fst p
  let hk : ∀ k, yoneda.obj (openSub _ (O k)) ⟶ yoneda.obj V := fun k =>
    yoneda.map (openSubHom _ (O k) ≫ hPrep.snd p)
  have hgh : ∀ k, gk k ≫ qP = hk k ≫ p := by
    intro k
    simp only [gk, hk, Category.assoc, Functor.map_comp, (hPrep.isPullback p).w]
  have hgk : ∀ k, IsEtale B S hS (gk k) := fun k =>
    isEtale_comp B S hS (isEtale_of_isOpenImmersion B S hS
      (isOpenImmersion_yoneda_map_openSubHom _ _)) hPfst
  have hΓ' : ∀ k, CompactSpace (T.obj (openSub (hPrep.pullback p) (O k))) := by
    intro k
    have : IsAffine (T.obj (openSub (hPrep.pullback p) (O k))) :=
      (isAffineOpen_top (T.obj (hPrep.pullback p))).basicOpen (b k)
    infer_instance
  have hmono : ∀ k, Mono (pullback.snd (gk k) gY) := by
    intro k
    have sq := ((isPullback_openSubHomOfRestrict m (O k)).map yoneda).flip.paste_vert sqV.flip
    have : Mono (yoneda.map (openSubHom _ (T.map m ⁻¹ᵁ O k)) ≫ hYrep.fst p) :=
      hqmono k _ (le_of_eq (hO k))
    have hsnd : pullback.snd (gk k) gY = sq.isoPullback.inv ≫
        (yoneda.map (openSubHom _ (T.map m ⁻¹ᵁ O k)) ≫ hYrep.fst p) := sq.isoPullback_inv_snd.symm
    rw [hsnd]
    exact @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso _) _ this
  -- The scheme-theoretic image `C` of `g`, whose points are those of `g(Y)`.
  have hgint : IsIntegralHom B S hS gY :=
    isIntegralHom_of_comp_of_isSeparated B S hS gY qP (by rwa [hgq])
      (isSeparated_of_isAffineHom B S hS qP P.obj.left.2 X.2 P.property)
  have hgqc : IsQuasiCompact B S hS gY := isQuasiCompact_of_isIntegralHom gY Ya.2 P.obj.left.2 hgint
  let C : ClosedSubspaces B S hS P.obj.left.1 := schemeTheoreticImage B S hS gY P.obj.left.2
  have hCpts : Set.range (pointsMap B S hS C.1.toFunctor C.1.ι) =
      Set.range (pointsMap B S hS _ gY) := by
    change Set.range (pointsMap B S hS (schemeTheoreticImageSubfunctor B S hS gY).toFunctor
      (schemeTheoreticImageSubfunctor B S hS gY).ι) = _
    rw [range_pointsMap_ι_schemeTheoreticImage_eq_closure_of_isQuasiCompact B S hS gY Ya.2
      P.obj.left.2 hgqc]
    exact (isClosed_range_pointsMap_of_isIntegralHom B S hS
      (ObjectProperty.homMk gY : Ya ⟶ P.obj.left) hgint).closure_eq
  have hC : IsEtaleSectionClosed B S hS gk C.1 := by
    refine ⟨fun k => preimage_le_range_diagonal_of_mono_pullback_snd B S hS P.obj.left.2
      (isAlgebraicSpace_yoneda B S hS _) (gk k) (hgk k) gY (hmono k) C.1 (le_of_eq hCpts), ?_⟩
    intro c hc
    rw [hCpts] at hc
    obtain ⟨y, rfl⟩ := hc
    obtain ⟨k, w, hwk, hwy⟩ := hqcov y
    have hmw : (T.map m).base w ∈ O k := by
      change w ∈ T.map m ⁻¹ᵁ O k
      rwa [hO k]
    obtain ⟨z, hz⟩ := exists_points_openSub_of_mem B S hS _ (O k) hmw
    refine Set.mem_iUnion.2 ⟨k, z, ?_⟩
    change pointsMap B S hS _ (yoneda.map (openSubHom _ (O k)) ≫ hPrep.fst p) z = _
    rw [pointsMap_comp_apply, hz, ← schemePointsHomeomorph_symm_naturality,
      ← pointsMap_comp_apply, ← sqV.w, pointsMap_comp_apply]
    exact congrArg _ hwy
  have hCsurj : IsSurjective B S hS (C.1.ι ≫ qP) := by
    intro x
    obtain ⟨y, rfl⟩ := hπsurj x
    obtain ⟨c, hc⟩ : pointsMap B S hS _ gY y ∈ Set.range (pointsMap B S hS C.1.toFunctor C.1.ι) :=
      hCpts ▸ Set.mem_range_self y
    refine ⟨c, ?_⟩
    rw [pointsMap_comp_apply, hc, ← pointsMap_comp_apply, hgq]
  -- Over the chart `U₀` of `U`, `g` is a closed immersion.
  let ms := smallBaseChangeOverMap B S hS g hYrep hPrep Us
  have sqU : IsPullback (hYrep.fst (u₀ ≫ U.ι)) (yoneda.map ms) gY (hPrep.fst (u₀ ≫ U.ι)) :=
    isPullback_fst_smallBaseChangeOverMap B S hS g hYrep hPrep Us
  have : IsAffine (T.obj (hPrep.pullback (u₀ ≫ U.ι))) :=
    isAffine_pullback_of_isAffineHom B S hS qP P.obj.left.2 X.2 P.property hPrep _ hU₀aff
  have hmsurj : Function.Surjective (T.map ms).appTop.hom :=
    surjective_appTop_smallBaseChangeOverMap B S hS g hYrep hPrep Us t ht fun x hx => by
      exact hrange _ _ (hs' (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun x => σU.inv x) hx)))
  have hmscl : _root_.AlgebraicGeometry.IsClosedImmersion (T.map ms) := by
    have : IsAffine (T.obj (hYrep.pullback Us.obj.hom)) := hWsaff
    have : IsAffine (T.obj (hPrep.pullback Us.obj.hom)) :=
      inferInstanceAs (IsAffine (T.obj (hPrep.pullback (u₀ ≫ U.ι))))
    exact IsClosedImmersion.of_surjective_of_isAffine _ hmsurj
  have hmscl' : IsClosedImmersion B S hS (yoneda.map ms) := by
    let : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
      inverseImage_isStableUnderBaseChange B S hS inferInstance
    exact MorphismProperty.relative_map hmscl
  have hφs : IsEtale B S hS (hPrep.fst (u₀ ≫ U.ι)) :=
    isEtale_fst_of_isEtale B S hS _ P.obj.left.2 X.2 hPrep _ hu₀U
  have hCU : C.1.preimage (hPrep.fst (u₀ ≫ U.ι)) = Subfunctor.range (yoneda.map ms) := by
    change (schemeTheoreticImageSubfunctor B S hS gY).preimage _ = _
    rw [preimage_schemeTheoreticImageSubfunctor_eq B S hS gY _ (yoneda.map ms) Ya.2 P.obj.left.2
      (isAlgebraicSpace_yoneda B S hS _) hgqc hφs (range_pullback_snd_eq_of_isPullback B S hS sqU)]
    exact schemeTheoreticImageSubfunctor_eq_range_of_isClosedImmersion B S hS _
      (isAlgebraicSpace_yoneda B S hS _) hmscl'
  have hms_snd : ms ≫ hPrep.snd (u₀ ≫ U.ι) = hYrep.snd (u₀ ≫ U.ι) :=
    smallBaseChangeOverMap_snd B S hS g hYrep hPrep Us
  obtain ⟨hCUfin, hCUet⟩ := isFinite_isEtale_pullback_fst_of_preimage_eq_range B S hS X.2
    P.obj.left qP U hU u₀ (isSurjective_of_presheafSurjective B S hS u₀ hu₀s) hu₀e
    (hPrep.fst _) (hPrep.snd _) (hPrep.isPullback _) C ms
    (mono_of_isClosedImmersion B S hS _ hmscl') hCU (by rwa [hms_snd])
    (by rwa [hms_snd])
  have : IsAffine (T.obj Vs.obj.left) := hV
  exact exists_finiteSchemeCover_of_monicEquations B S hS hZ X hXqc hXqs g hYrep hPrep hπint
    P.property hPfp Vs hpsurj hp (RingHom.FiniteType.of_finitePresentation (hPalgfp Vs hV)) hΓ' gk
    hgk hk hgh C hC hCsurj U hU hUqc hUdense hCUfin hCUet hgqc rfl

end AlgebraicGeometry.Space

end
