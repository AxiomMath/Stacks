module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Dominance
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# Invariant closed subobjects of an étale equivalence relation

Let `S` be a scheme contained in a big fppf site `B`, let `f : Y ⟶ X` be a representable étale
morphism of presheaves of `Type (u + 1)` on the big fppf site of `S`, and let `z : h_Z ⟶ Y` be a
representable closed immersion from a scheme of the site. If `Z` receives a scheme-theoretically
dominant quasi-compact morphism from a base change of `f`, compatibly with `z`, then the
restriction of the étale equivalence relation `Y ×_X Y` to `Z` is representable by a scheme of the
site. No hypothesis is placed on `Y`.

## Main results

* `CategoryTheory.mono_of_relative_monomorphisms_uliftYoneda`: a morphism of presheaves of
  `Type (max u w)` all of whose represented base changes are monomorphisms of the site is a
  monomorphism, where "represented" is taken along the universe-lifted Yoneda embedding.
* `CategoryTheory.isPullback_of_comp_fst_mono`: a monomorphism can be cancelled out of the first
  leg of a cartesian square.
* `AlgebraicGeometry.Space.mono_of_relative_isClosedImmersion`: a representable closed immersion
  of presheaves of `Type (u + 1)` is a monomorphism.
* `AlgebraicGeometry.Space.exists_factor_of_isSchemeTheoreticallyDominant`: a
  scheme-theoretically dominant morphism `g : U ⟶ V` of the site lifts a factorisation of
  `g ≫ a` through a representable closed immersion `z` to a factorisation of `a` itself.
* `AlgebraicGeometry.Space.isSchemeTheoreticallyDominant_of_factor_schemeImage`: a factorisation
  of a quasi-compact morphism with affine target through its scheme-theoretic image is
  scheme-theoretically dominant.
* `AlgebraicGeometry.Space.exists_invariantImage_relation`: the restricted relation is
  representable by a scheme of the site, cartesian over the inclusion of `Z`, and étale on the
  second projection.
* `AlgebraicGeometry.Space.relative_isThickening_of_factor`: a representable closed immersion
  through which a representable thickening factors is itself a representable thickening.

## References

* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 0AJE](https://stacks.math.columbia.edu/tag/0AJE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/-- A morphism into the apex of a pullback square of presheaves with a representable apex and a
representable second leg is determined by a morphism of the site lifting both legs. -/
private theorem exists_lift_of_isPullback_uliftYoneda {C : Type v} [Category.{u} C]
    {F G : Cᵒᵖ ⥤ Type (max u w)} {W P U : C} {p : (uliftYoneda.{w}).obj P ⟶ F} {q : P ⟶ U}
    {f : F ⟶ G} {g : (uliftYoneda.{w}).obj U ⟶ G}
    (hp : IsPullback p (uliftYoneda.map q) f g) (a : (uliftYoneda.{w}).obj W ⟶ F) (h : W ⟶ U)
    (hah : a ≫ f = uliftYoneda.map h ≫ g) :
    ∃ c : W ⟶ P, uliftYoneda.map c ≫ p = a ∧ c ≫ q = h := by
  let ff := ULiftYoneda.fullyFaithful (C := C)
  refine ⟨ff.preimage (hp.lift a (uliftYoneda.map h) hah),
    by rw [ff.map_preimage, hp.lift_fst], ff.map_injective ?_⟩
  rw [Functor.map_comp, ff.map_preimage, hp.lift_snd]

/-- A morphism of presheaves all of whose base changes along the universe-lifted Yoneda embedding
are represented by monomorphisms is a monomorphism. -/
theorem mono_of_relative_monomorphisms_uliftYoneda {C : Type v} [Category.{u} C]
    {F G : Cᵒᵖ ⥤ Type (max u w)} (f : F ⟶ G)
    (hf : (MorphismProperty.monomorphisms C).relative (uliftYoneda.{w}) f) :
    Mono f := by
  suffices ∀ {U : C} {a b : (uliftYoneda.{w}).obj U ⟶ F}, a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_uliftYoneda (fun _ _ ↦ this (by simp only [Category.assoc, h]))⟩
  intro U a b hab
  obtain ⟨V, q, p, hp⟩ := hf.rep (a ≫ f)
  obtain ⟨l, hlp, hlq⟩ := exists_lift_of_isPullback_uliftYoneda hp a (𝟙 _) (by simp)
  obtain ⟨r, hrp, hrq⟩ := exists_lift_of_isPullback_uliftYoneda hp b (𝟙 _) (by simpa using hab.symm)
  have : Mono q := hf.property _ _ _ hp
  rw [← hlp, ← hrp, (cancel_mono q).mp (hlq.trans hrq.symm)]

/-- If `t ≫ z` and `r` exhibit `R` as the fibre product of `f` and `g`, and `z` is a monomorphism,
then `t` and `r` exhibit `R` as the fibre product of `z ≫ f` and `g`. -/
theorem isPullback_of_comp_fst_mono {C : Type v} [Category.{u} C] {R U V Y X : C}
    {t : R ⟶ U} {r : R ⟶ V} {z : U ⟶ Y} [Mono z] {f : Y ⟶ X} {g : V ⟶ X}
    (hp : IsPullback (t ≫ z) r f g) : IsPullback t r (z ≫ f) g := by
  apply IsPullback.mk' (by simpa only [Category.assoc] using hp.w)
  · intro T a b ht hr
    apply hp.hom_ext _ hr
    simpa only [← Category.assoc] using congrArg (fun k ↦ k ≫ z) ht
  · intro T a b hab
    refine ⟨hp.lift (a ≫ z) b (by simpa only [Category.assoc] using hab), ?_,
      hp.lift_snd _ _ _⟩
    apply (cancel_mono z).mp
    simpa only [Category.assoc] using hp.lift_fst (a ≫ z) b _

end CategoryTheory

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A representable closed immersion of presheaves on the big fppf site of `S` is a
monomorphism. -/
theorem mono_of_relative_isClosedImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) f) :
    Mono f := by
  refine mono_of_relative_monomorphisms_uliftYoneda f
    (show (MorphismProperty.monomorphisms _).relative (uliftYoneda.{u + 1}) f from ?_)
  apply MorphismProperty.relative_monotone (P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)) _ _ hf
  intro U V g hg
  have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g) := hg
  exact (BigFppfOver.toScheme B S hS).mono_of_mono_map (f := g) inferInstance

/-- Let `z : h_Z ⟶ Y` be a representable closed immersion and let `g : U ⟶ V` be
scheme-theoretically dominant. If `a : h_V ⟶ Y` becomes, after restriction along `g`, a morphism
through `z`, then `a` itself factors through `z`. -/
theorem exists_factor_of_isSchemeTheoreticallyDominant
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {U V Z : BigFppfOver B S hS}
    (z : (uliftYoneda.{u + 1}).obj Z ⟶ Y)
    (hz : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) z)
    (g : U ⟶ V)
    (hg : IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map g))
    (a : (uliftYoneda.{u + 1}).obj V ⟶ Y) (b : U ⟶ Z)
    (hab : uliftYoneda.map g ≫ a = uliftYoneda.map b ≫ z) :
    ∃ c : V ⟶ Z, uliftYoneda.map c ≫ z = a := by
  let F := BigFppfOver.toScheme B S hS
  let ff := ULiftYoneda.fullyFaithful (C := BigFppfOver B S hS)
  obtain ⟨T, q, p, hp⟩ := hz.rep a
  obtain ⟨l, -, hlq⟩ :=
    exists_lift_of_isPullback_uliftYoneda hp (uliftYoneda.map b) g hab.symm
  have : AlgebraicGeometry.IsClosedImmersion (F.map q) := hz.property a p q hp
  have : IsIso (F.map q) := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr <| le_bot_iff.mp <|
    (Scheme.Hom.le_ker_comp _ _).trans_eq (by rw [← F.map_comp, hlq, hg.ker_eq_bot])
  have : IsIso q := isIso_of_reflects_iso q F
  refine ⟨ff.preimage (uliftYoneda.map (inv q) ≫ p), ?_⟩
  rw [ff.map_preimage, Category.assoc, hp.w, ← Functor.map_comp_assoc, IsIso.inv_hom_id]
  simp

/-- If `a : W ⟶ V` is a quasi-compact morphism of the site with affine target, `Z` is an object of
the site identified with the scheme-theoretic image of `a` compatibly with the inclusion, and `a`
factors as `l ≫ q` through `Z`, then `l` is scheme-theoretically dominant. -/
theorem isSchemeTheoreticallyDominant_of_factor_schemeImage
    {W V Z : BigFppfOver B S hS} (a : W ⟶ V) (q : Z ⟶ V) (l : W ⟶ Z)
    (e : (BigFppfOver.toScheme B S hS).obj Z ≅
      ((BigFppfOver.toScheme B S hS).map a).image)
    (hq : (BigFppfOver.toScheme B S hS).map q =
      e.hom ≫ ((BigFppfOver.toScheme B S hS).map a).imageι)
    (hl : l ≫ q = a)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (ha : QuasiCompact ((BigFppfOver.toScheme B S hS).map a)) :
    IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map l) := by
  let F := BigFppfOver.toScheme B S hS
  have hcomp : F.map l ≫ e.hom = (F.map a).toImage := by
    apply (cancel_mono (F.map a).imageι).mp
    rw [Category.assoc, ← hq, ← F.map_comp, hl, Scheme.Hom.toImage_imageι]
  have heq : F.map l = (F.map a).toImage ≫ e.inv := e.eq_comp_inv.mpr hcomp
  have : IsAffine (F.obj V) := hV
  have : QuasiCompact (F.map a) := ha
  have : IsSchemeTheoreticallyDominant (F.map a).toImage :=
    isSchemeTheoreticallyDominant_toImage _
  rw [heq]
  infer_instance

/-- Let `f : Y ⟶ X` be a representable étale morphism of presheaves on the big fppf site of `S`,
let `s : h_U ⟶ Y` be a morphism with `p : h_W ⟶ Y` the base change of `f` along `s ≫ f`, and let
`z : h_Z ⟶ Y` be a representable closed immersion receiving a scheme-theoretically dominant,
quasi-compact `l : W ⟶ Z` with `l ≫ z = p`. Then the restriction of the relation to `Z` is
representable by an object `R` of the site, with projections `t, r : R ⟶ Z` forming a kernel pair
of `z ≫ f`, and `r` is étale. -/
theorem exists_invariantImage_relation
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (f : Y ⟶ X)
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) f)
    {U W Z : BigFppfOver B S hS}
    (s : (uliftYoneda.{u + 1}).obj U ⟶ Y)
    (p : (uliftYoneda.{u + 1}).obj W ⟶ Y) (q : W ⟶ U)
    (hp : IsPullback p (uliftYoneda.map q) f (s ≫ f))
    (z : (uliftYoneda.{u + 1}).obj Z ⟶ Y)
    (hz : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) z)
    (l : W ⟶ Z)
    (hl : IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map l))
    (hlqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map l))
    (hlz : uliftYoneda.map l ≫ z = p) :
    ∃ (R : BigFppfOver B S hS) (t r : R ⟶ Z),
      IsPullback (uliftYoneda.map t ≫ z) (uliftYoneda.map r) f (z ≫ f) ∧
      IsPullback (uliftYoneda.map t) (uliftYoneda.map r) (z ≫ f) (z ≫ f) ∧
      AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map r) := by
  let F := BigFppfOver.toScheme B S hS
  let H := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  obtain ⟨R, r, y, hR⟩ := hf.rep (z ≫ f)
  let : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have : AlgebraicGeometry.Etale (F.map r) := hf.property _ _ _ hR
  let K := pullback l r
  let a : K ⟶ W := pullback.fst l r
  let b : K ⟶ R := pullback.snd l r
  have hk : IsPullback (F.map a) (F.map b) (F.map l) (F.map r) :=
    (IsPullback.of_hasPullback l r).map F
  have : IsSchemeTheoreticallyDominant (F.map l) := hl
  have : QuasiCompact (F.map l) := hlqc
  have hb : IsSchemeTheoreticallyDominant (F.map b) :=
    IsSchemeTheoreticallyDominant.of_isPullback hk
  have hw : (H.map b ≫ y) ≫ f = H.map (a ≫ q) ≫ s ≫ f := by
    calc
      (H.map b ≫ y) ≫ f = H.map b ≫ H.map r ≫ z ≫ f := by
        rw [Category.assoc, hR.w]
      _ = H.map a ≫ H.map l ≫ z ≫ f := by
        rw [← H.map_comp_assoc, ← pullback.condition, H.map_comp_assoc]
      _ = H.map (a ≫ q) ≫ s ≫ f := by
        rw [reassoc_of% hlz, hp.w]
        simp only [H.map_comp, Category.assoc]
        rfl
  obtain ⟨d, hd, -⟩ := exists_lift_of_isPullback_uliftYoneda hp (H.map b ≫ y) (a ≫ q) hw
  obtain ⟨t, ht⟩ := exists_factor_of_isSchemeTheoreticallyDominant B S hS z hz b hb y (d ≫ l) (by
    simpa only [H.map_comp, Functor.map_comp, Category.assoc, hlz] using hd.symm)
  have hR' : IsPullback (H.map t ≫ z) (H.map r) f (z ≫ f) := ht ▸ hR
  have : Mono z := mono_of_relative_isClosedImmersion B S hS z hz
  exact ⟨R, t, r, hR', isPullback_of_comp_fst_mono hR', inferInstance⟩

/-- If the representable thickening `s : h_U ⟶ Y` factors as `a ≫ z` through the representable
closed immersion `z : h_Z ⟶ Y`, then `z` is itself a representable thickening. -/
theorem relative_isThickening_of_factor
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {U Z : BigFppfOver B S hS}
    (s : (uliftYoneda.{u + 1}).obj U ⟶ Y)
    (hs : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) s)
    (z : (uliftYoneda.{u + 1}).obj Z ⟶ Y)
    (hz : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) z)
    (a : U ⟶ Z) (ha : uliftYoneda.map a ≫ z = s) :
    (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) z := by
  let F := BigFppfOver.toScheme B S hS
  let H := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  refine ⟨hz.rep, fun T R g p q hp ↦ ⟨hz.property g p q hp, ?_⟩⟩
  obtain ⟨W, v, w, hw⟩ := hs.rep g
  have hv := (hs.property g w v hw).2
  obtain ⟨c, -, hc⟩ := exists_lift_of_isPullback_uliftYoneda hp (w ≫ H.map a) v (by
    simpa only [H, Category.assoc, ha] using hw.w)
  have hcF : F.map c ≫ F.map q = F.map v := by rw [← F.map_comp, hc]
  intro x
  obtain ⟨y, hy⟩ := hv x
  exact ⟨F.map c y, (congrArg (fun k : F.obj W ⟶ F.obj T ↦ k y) hcF).trans hy⟩

end Space

end AlgebraicGeometry

end
