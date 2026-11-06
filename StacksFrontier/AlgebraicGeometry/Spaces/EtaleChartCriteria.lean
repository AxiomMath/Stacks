module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The étale-chart criteria for a property with no cancellation

Let `P` be a property of morphisms of schemes which is étale local on the source and target,
stable under base change and Zariski local at the target. This file proves the eight
equivalent characterisations of the condition of Stacks 03MJ that `P` hold on every commuting
square of étale charts of a morphism of algebraic spaces over a scheme `S`.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae_of_isLocalAtTarget`: eight criteria,
  tested on every base change to a scheme in the site, on every base change to an affine
  scheme, on one surjective étale chart of the target, on one surjective étale chart of the
  source, on every — or on one surjective — commuting square of étale charts, or over a pair
  of Zariski coverings.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 04RF](https://stacks.math.columbia.edu/tag/04RF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_etaleChartCriteria :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_etaleChartCriteria
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Small products of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance (priority := high) hasLimitsOfShape_discrete_etaleChartCriteria (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- The chart condition of Stacks 03MJ transports along an isomorphism of arrows: if `P` holds
on every étale chart of `f` and `g` becomes `f` after the isomorphisms `eX` of the sources and
`eY` of the targets, then `P` holds on every étale chart of `g`. -/
private theorem holdsOnEveryEtaleChart_of_arrowIso
    {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (eX : X' ≅ X) (eY : Y' ≅ Y) (hcomm : g ≫ eY.hom = eX.hom ≫ f)
    (hf : HoldsOnEveryEtaleChart B S hS P f) :
    HoldsOnEveryEtaleChart B S hS P g := by
  intro U V a b h ha hb hh
  let Q := MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))
  have : Q.RespectsIso := inferInstance
  have ha' : Q (a ≫ eX.hom) := MorphismProperty.RespectsIso.postcomp Q eX.hom a ha
  have hb' : Q (b ≫ eY.hom) := MorphismProperty.RespectsIso.postcomp Q eY.hom b hb
  have hh' : yoneda.map h ≫ (b ≫ eY.hom) = (a ≫ eX.hom) ≫ f := by
    simp only [← Category.assoc, hh]
    rw [Category.assoc, hcomm, ← Category.assoc]
  exact hf U V (a ≫ eX.hom) (b ≫ eY.hom) h ha' hb' hh'


/-- A chart of an algebraic space `F`: a surjective étale morphism from a representable. -/
private theorem exists_isSurjective_isEtale_of_isAlgebraicSpace
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F),
      IsSurjective B S hS a ∧ IsEtale B S hS a := by
  obtain ⟨U, a, hs, he⟩ := hF.exists_atlas
  exact ⟨U, a, (surjective_iff_surjective_pointsMap B S hS F hF U a).mp hs,
    (isEtale_iff_presheaf_of_yoneda B S hS a).2 he⟩

/-- If `P` holds on every étale chart of `g` and `a` is étale, then `P` holds on any morphism of
the site whose image under Yoneda is `a ≫ g`. -/
private theorem map_of_holdsOnEveryEtaleChart_of_isEtale {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : BigFppfOver B S hS} {g : X ⟶ yoneda.obj V}
    (hg : HoldsOnEveryEtaleChart B S hS P g) {a : yoneda.obj U ⟶ X} (ha : IsEtale B S hS a)
    {h : U ⟶ V} (hh : yoneda.map h = a ≫ g) : P ((BigFppfOver.toScheme B S hS).map h) :=
  hg U V a (𝟙 _) h ((isEtale_iff_presheaf_of_yoneda B S hS a).1 ha)
    ((isEtale_iff_presheaf_of_yoneda B S hS _).1 fun _ _ hφ => by simpa using hφ)
    (by simpa using hh)

/-- A cartesian square of algebraic-space presheaves is cartesian in `AlgebraicSpaces`. -/
private theorem isPullback_homMk_of_isAlgebraicSpace
    {P Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {p : P ⟶ Z} {q : P ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f) :
    IsPullback (ObjectProperty.homMk p : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk q : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq

/-- Condition (3) of Stacks 03MM implies condition (4): if `P` holds on every étale chart of
every base change of `f` to an affine scheme in the site, then it holds on every étale chart
of the base change of `f` along some surjective étale chart of its target. -/
private theorem exists_surjectiveEtaleChart_of_affine_baseChange
    (hP : IsEtaleLocalOnSourceAndTarget P) [P.IsLocalAtTarget Scheme.zariskiPrecoverage]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h₃ : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
        HoldsOnEveryEtaleChart B S hS P (pullback.snd f g)) :
    ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
      IsSurjective B S hS g ∧ IsEtale B S hS g ∧
        HoldsOnEveryEtaleChart B S hS P (pullback.snd f g) := by
  classical
  set T := BigFppfOver.toScheme B S hS with hT
  obtain ⟨V, g, hgSurj, hgEtale⟩ := exists_isSurjective_isEtale_of_isAlgebraicSpace B S hS hY
  refine ⟨V, g, hgSurj, hgEtale, ?_⟩
  have hV := isAlgebraicSpace_yoneda B S hS V
  have hPB : IsAlgebraicSpace B S hS (pullback f g) :=
    isAlgebraicSpace_pullback B S hS f g hX hV hY
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hPB hV
    (pullback.snd f g)).2 ?_
  obtain ⟨W, a, haSurjRaw, haEtaleRaw⟩ := hPB.exists_atlas
  have haEtale : IsEtale B S hS a := (isEtale_iff_presheaf_of_yoneda B S hS a).2 haEtaleRaw
  obtain ⟨q, hq⟩ := yoneda.map_surjective (a ≫ pullback.snd f g)
  refine ⟨W, V, a, 𝟙 (yoneda.obj V), q, haEtaleRaw,
    (isEtale_iff_presheaf_of_yoneda B S hS _).1 fun _ _ hφ => by simpa using hφ, haSurjRaw,
    by simpa using hq, ?_⟩
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := P) (f := T.map q)
    (T.obj V).affineCover).2 ?_
  intro i
  have hcont : B.Contains ((T.obj V).affineCover.X i) :=
    Scheme.size_lt_of_isOpenImmersion ((T.obj V).affineCover.f i) V.left.property
  let Zi : BigFppfOver B S hS :=
    Over.mk (Y := B.obj hcont)
      (ObjectProperty.homMk ((T.obj V).affineCover.f i ≫ V.hom.hom))
  let vi : Zi ⟶ V := Over.homMk (ObjectProperty.homMk ((T.obj V).affineCover.f i))
  have hvi : T.map vi = (T.obj V).affineCover.f i := rfl
  have hZiAff : IsAffine (T.obj Zi) := by
    show IsAffine ((T.obj V).affineCover.X i)
    infer_instance
  have hZi := isAlgebraicSpace_yoneda B S hS Zi
  have hPBi : HoldsOnEveryEtaleChart B S hS P (pullback.snd f (yoneda.map vi ≫ g)) :=
    h₃ Zi (yoneda.map vi ≫ g) hZiAff
  have hAltSq : IsPullback (pullback.fst (pullback.snd f g) (yoneda.map vi))
      (pullback.snd (pullback.snd f g) (yoneda.map vi)) (pullback.snd f g)
      (yoneda.map vi) := IsPullback.of_hasPullback _ _
  have hPasted := IsPullback.of_right' (IsPullback.of_hasPullback f (yoneda.map vi ≫ g))
    (IsPullback.of_hasPullback f g)
  have hAlt : HoldsOnEveryEtaleChart B S hS P
      (pullback.snd (pullback.snd f g) (yoneda.map vi)) :=
    holdsOnEveryEtaleChart_of_arrowIso B S hS P
      (hAltSq.isoIsPullback _ _ hPasted) (Iso.refl (yoneda.obj Zi))
      (by simp) hPBi
  have hw : yoneda.map (pullback.snd q vi) ≫ yoneda.map vi =
      (yoneda.map (pullback.fst q vi) ≫ a) ≫ pullback.snd f g := by
    rw [← Functor.map_comp, ← pullback.condition, Functor.map_comp, hq, Category.assoc]
  have hsplit : IsPullback (yoneda.map (pullback.snd q vi)) (yoneda.map (pullback.fst q vi))
      (yoneda.map vi) (a ≫ pullback.snd f g) := by
    rw [← hq]
    exact ((IsPullback.of_hasPullback q vi).map yoneda).flip
  obtain ⟨ai, haiSnd, hsqai⟩ :
      ∃ ai : yoneda.obj (pullback q vi) ⟶ pullback (pullback.snd f g) (yoneda.map vi),
        ai ≫ pullback.snd (pullback.snd f g) (yoneda.map vi) =
            yoneda.map (pullback.snd q vi) ∧
          IsPullback (yoneda.map (pullback.fst q vi)) ai a
            (pullback.fst (pullback.snd f g) (yoneda.map vi)) :=
    ⟨hAltSq.flip.lift (yoneda.map (pullback.snd q vi))
        (yoneda.map (pullback.fst q vi) ≫ a) hw,
      hAltSq.flip.lift_fst _ _ _, (IsPullback.of_right' hsplit hAltSq.flip).flip⟩
  have hPBalt : IsAlgebraicSpace B S hS (pullback (pullback.snd f g) (yoneda.map vi)) :=
    isAlgebraicSpace_pullback B S hS (pullback.snd f g) (yoneda.map vi) hPB hZi hV
  have haiEtale : IsEtale B S hS ai := by
    exact isEtale_of_isPullback B S hS _ _ _ _ (isPullback_homMk_of_isAlgebraicSpace B S hS
      (isAlgebraicSpace_yoneda B S hS (pullback q vi)) (isAlgebraicSpace_yoneda B S hS W)
      hPBalt hPB hsqai) haEtale
  have hPrZ : P (T.map (pullback.snd q vi)) :=
    map_of_holdsOnEveryEtaleChart_of_isEtale B S hS P hAlt haiEtale haiSnd.symm
  have hMapped : IsPullback (T.map (pullback.fst q vi)) (T.map (pullback.snd q vi)) (T.map q)
      ((T.obj V).affineCover.f i) := by
    rw [← hvi]
    exact (IsPullback.of_hasPullback q vi).map T
  have hStd := IsPullback.of_hasPullback (T.map q) ((T.obj V).affineCover.f i)
  have heStd : (hMapped.isoIsPullback _ _ hStd).hom ≫
      pullback.snd (T.map q) ((T.obj V).affineCover.f i) =
      T.map (pullback.snd q vi) ≫ (Iso.refl ((T.obj Zi))).hom := by
    rw [Iso.refl_hom, Category.comp_id]
    exact hMapped.isoIsPullback_hom_snd _ _ hStd
  exact (P.arrow_mk_iso_iff (Arrow.isoMk (hMapped.isoIsPullback _ _ hStd)
    (Iso.refl ((T.obj Zi))) heStd)).mp hPrZ

set_option synthInstance.maxHeartbeats 400000 in
/-- **Eight étale-chart criteria for a property with no cancellation.** Let `P` be a property
of morphisms of schemes which is étale local on the source and target, stable under base
change and Zariski local at the target. Then, for a morphism `f` of algebraic spaces over `S`,
the condition of Stacks 03MJ that `P` hold on every étale chart of `f` can equivalently be
tested after base change to every scheme or to every affine scheme or to one surjective étale
chart of the target, on the composite with one surjective étale chart of the source, in
every — or in one surjective — commuting square of étale charts, or over a pair of Zariski
coverings. -/
theorem holdsOnEveryEtaleChart_tfae_of_isLocalAtTarget
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P)
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.zariskiPrecoverage]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      HoldsOnEveryEtaleChart B S hS P f,
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        HoldsOnEveryEtaleChart B S hS P (pullback.snd f g),
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          HoldsOnEveryEtaleChart B S hS P (pullback.snd f g),
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧
          HoldsOnEveryEtaleChart B S hS P (pullback.snd f g),
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧
          HoldsOnEveryEtaleChart B S hS P (p ≫ f),
      ∀ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p → IsEtale B S hS q → p ≫ f = yoneda.map a ≫ q →
          P ((BigFppfOver.toScheme B S hS).map a),
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧ P ((BigFppfOver.toScheme B S hS).map a),
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, HoldsOnEveryEtaleChart B S hS P
            ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)
    ] := by
  classical
  have hmulEtale := isMultiplicative_presheaf_etale B S hS
  tfae_have 1 ↔ 6 := by
    constructor
    · intro hf U V p q a hp hq hcomm
      exact hf U V p q a ((isEtale_iff_presheaf_of_yoneda B S hS p).1 hp)
        ((isEtale_iff_presheaf_of_yoneda B S hS q).1 hq) hcomm.symm
    · intro h U V p q a hp hq hcomm
      exact h U V p q a ((isEtale_iff_presheaf_of_yoneda B S hS p).2 hp)
        ((isEtale_iff_presheaf_of_yoneda B S hS q).2 hq) hcomm.symm
  tfae_have 1 ↔ 7 := by
    rw [holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hX hY f]
    constructor
    · rintro ⟨U, V, p, q, a, hp, hq, hs, hcomm, hPa⟩
      exact ⟨U, V, p, q, a, (isEtale_iff_presheaf_of_yoneda B S hS p).2 hp,
        (isEtale_iff_presheaf_of_yoneda B S hS q).2 hq,
        (surjective_iff_surjective_pointsMap B S hS X hX U p).mp hs, hcomm.symm, hPa⟩
    · rintro ⟨U, V, p, q, a, hp, hq, hs, hcomm, hPa⟩
      exact ⟨U, V, p, q, a, (isEtale_iff_presheaf_of_yoneda B S hS p).1 hp,
        (isEtale_iff_presheaf_of_yoneda B S hS q).1 hq,
        (surjective_iff_surjective_pointsMap B S hS X hX U p).mpr hs, hcomm.symm, hPa⟩
  tfae_have 1 → 2 := fun hf Z g =>
    holdsOnEveryEtaleChart_pullback_snd_of_isAlgebraicSpace B S hS P hP inferInstance hX hY
      (isAlgebraicSpace_yoneda B S hS Z) f g hf
  tfae_have 2 → 3 := fun h Z g _ => h Z g
  tfae_have 3 → 4 := fun h₃ =>
    exists_surjectiveEtaleChart_of_affine_baseChange B S hS P hP hX hY f h₃
  tfae_have 4 → 7 := by
    rintro ⟨V, g, hgSurj, hgEtale, hbase⟩
    have hV := isAlgebraicSpace_yoneda B S hS V
    have hPB : IsAlgebraicSpace B S hS (pullback f g) :=
      isAlgebraicSpace_pullback B S hS f g hX hV hY
    have hsq := (isPullback_homMk_of_isAlgebraicSpace B S hS hPB hX hV hY
      (IsPullback.of_hasPullback f g)).flip
    obtain ⟨U, a, haSurj, haEtale⟩ := exists_isSurjective_isEtale_of_isAlgebraicSpace B S hS hPB
    obtain ⟨h, hh⟩ := yoneda.map_surjective (a ≫ pullback.snd f g)
    refine ⟨U, V, a ≫ pullback.fst f g, g, h,
      isEtale_comp B S hS haEtale (isEtale_of_isPullback B S hS _ _ _ _ hsq hgEtale), hgEtale,
      isSurjective_comp B S hS haSurj (isSurjective_of_isPullback B S hS hsq hgSurj), ?_,
      map_of_holdsOnEveryEtaleChart_of_isEtale B S hS P hbase haEtale hh⟩
    rw [hh, Category.assoc, Category.assoc, pullback.condition]
  tfae_have 1 → 5 := by
    intro hf
    obtain ⟨U, p, hpSurj, hpEtale⟩ := exists_isSurjective_isEtale_of_isAlgebraicSpace B S hS hX
    refine ⟨U, p, hpSurj, hpEtale, ?_⟩
    intro U' V' a' b' h' ha' hb' hcomm
    have haComp : IsEtale B S hS (a' ≫ p) :=
      isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS a').2 ha') hpEtale
    exact hf U' V' (a' ≫ p) b' h'
      ((isEtale_iff_presheaf_of_yoneda B S hS (a' ≫ p)).1 haComp) hb'
      (by rw [hcomm, Category.assoc])
  tfae_have 5 → 1 := by
    rintro ⟨U, p, hpSurj, hpEtale, hpf⟩
    exact holdsOnEveryEtaleChart_of_surjectiveEtale_source B S hS P hP hX hY f p
      ((surjective_iff_surjective_pointsMap B S hS X hX U p).mpr hpSurj)
      ((isEtale_iff_presheaf_of_yoneda B S hS p).1 hpEtale) hpf
  tfae_have 1 → 8 := by
    intro hf
    have hYtop : IsAlgebraicSpace B S hS (⊤ : Subfunctor Y).toFunctor :=
      (isOpenSubspace_top (B := B) (S := S) (hS := hS) (F := Y) hY).1
    have hZ : IsAlgebraicSpace B S hS (pullback f (⊤ : Subfunctor Y).ι) :=
      isAlgebraicSpace_pullback B S hS f (⊤ : Subfunctor Y).ι hX hYtop hY
    have hIsoFst : IsIso (pullback.fst f (⊤ : Subfunctor Y).ι) :=
      (IsPullback.of_hasPullback f (⊤ : Subfunctor Y).ι).isIso_fst_of_isIso
    refine ⟨PUnit.{u + 1}, fun _ => ⊤, fun _ => PUnit.{u + 1}, fun _ _ => ⊤,
      isZariskiCover_top hY, fun _ => isZariskiCover_top hZ, fun _ _ => ?_⟩
    refine holdsOnEveryEtaleChart_of_arrowIso B S hS P
      ((asIso (Subfunctor.ι (⊤ : Subfunctor (pullback f (⊤ : Subfunctor Y).ι)))).trans
        (asIso (pullback.fst f (⊤ : Subfunctor Y).ι)))
      (asIso (Subfunctor.ι (⊤ : Subfunctor Y))) ?_ hf
    simp only [Iso.trans_hom, asIso_hom, Category.assoc, ← pullback.condition]
  tfae_have 8 → 1 := by
    rintro ⟨I, Yopen, J, Xopen, hYcov, hXcov, hlocal⟩
    have hYpoints : (⋃ i, Set.range (pointsMap B S hS (Yopen i).toFunctor (Yopen i).ι))
        = Set.univ :=
      (isZariskiCover_iff_iUnion_points B S hS Y hY I Yopen hYcov.1).mp hYcov
    have hQcomp := MorphismProperty.relative_isStableUnderComposition
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
    have hQbc := MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
    have hmOpen : ∀ (i : I) (j : J i),
        IsOpenImmersion B S hS ((Xopen i j).ι ≫ pullback.fst f (Yopen i).ι) := by
      intro i j
      have hfstOpen : IsOpenImmersion B S hS (pullback.fst f (Yopen i).ι) :=
        hQbc.of_isPullback (IsPullback.of_hasPullback f (Yopen i).ι).flip (hYcov.1 i).2
      exact MorphismProperty.comp_mem _ _ _ ((hXcov i).1 j).2 hfstOpen
    have hrangeOpen : ∀ (i : I) (j : J i), IsOpenSubspace B S hS
        (Subfunctor.range ((Xopen i j).ι ≫ pullback.fst f (Yopen i).ι)) := fun i j =>
      isOpenSubspace_subfunctorRange B S hS ((hXcov i).1 j).1 (hmOpen i j)
    have hrangeChart : ∀ (i : I) (j : J i), HoldsOnEveryEtaleChart B S hS P
        ((Subfunctor.range ((Xopen i j).ι ≫ pullback.fst f (Yopen i).ι)).ι ≫ f) := by
      intro i j
      set m := (Xopen i j).ι ≫ pullback.fst f (Yopen i).ι with hm
      set Wsub := Subfunctor.range m with hWsub
      have : Mono m := mono_of_presheaf_isOpenImmersion (hmOpen i j)
      have heInv : (asIso (Subfunctor.toRange m)).inv ≫ m = Wsub.ι :=
        (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι m).symm
      have hmf : ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι) ≫ (Yopen i).ι = m ≫ f := by
        rw [hm, Category.assoc, Category.assoc, pullback.condition]
      have hg₀Chart : HoldsOnEveryEtaleChart B S hS P
          ((asIso (Subfunctor.toRange m)).inv ≫
            ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)) :=
        holdsOnEveryEtaleChart_of_arrowIso B S hS P (asIso (Subfunctor.toRange m)).symm
          (Iso.refl _) (by simp) (hlocal i j)
      have hg₀Comp : ((asIso (Subfunctor.toRange m)).inv ≫
          ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)) ≫ (Yopen i).ι = Wsub.ι ≫ f := by
        rw [Category.assoc, hmf, ← Category.assoc, heInv]
      obtain ⟨U₀, V₀, a₀, b₀, h₀, ha₀Raw, hb₀Raw, ha₀SurjRaw, hcomm₀, htop₀⟩ :=
        (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP (hrangeOpen i j).1
          (hYcov.1 i).1 _).mp hg₀Chart
      have hbYEtaleRaw := MorphismProperty.comp_mem _ b₀ (Yopen i).ι hb₀Raw
        (presheaf_etale_of_isOpenImmersion B S hS (hYcov.1 i).2)
      refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP (hrangeOpen i j).1 hY
        (Wsub.ι ≫ f)).2 ⟨U₀, V₀, a₀, b₀ ≫ (Yopen i).ι, h₀, ha₀Raw, hbYEtaleRaw,
          ha₀SurjRaw, ?_, htop₀⟩
      rw [← hg₀Comp]
      simp only [← Category.assoc, hcomm₀]
    refine (holdsOnEveryEtaleChart_iff_forall_atPoint B S hS P hP hX hY f).2 fun x => ?_
    refine (holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS P hP hX hY f x).2 ?_
    obtain ⟨i, yi, hyi⟩ : ∃ (i : I) (yi : points B S hS (Yopen i).toFunctor),
        pointsMap B S hS (Yopen i).toFunctor (Yopen i).ι yi = pointsMap B S hS X f x := by
      have hmem : pointsMap B S hS X f x ∈
          ⋃ i, Set.range (pointsMap B S hS (Yopen i).toFunctor (Yopen i).ι) := by
        rw [hYpoints]; trivial
      simpa only [Set.mem_iUnion, Set.mem_range] using hmem
    have hYi : IsAlgebraicSpace B S hS (Yopen i).toFunctor := (hYcov.1 i).1
    have hZi : IsAlgebraicSpace B S hS (pullback f (Yopen i).ι) :=
      isAlgebraicSpace_pullback B S hS f (Yopen i).ι hX hYi hY
    obtain ⟨z, hzFst, -⟩ := exists_point_of_isPullback B S hS
      (isPullback_homMk_of_isAlgebraicSpace B S hS hZi hX hYi hY
        (IsPullback.of_hasPullback f (Yopen i).ι)) x yi hyi.symm
    have hXipoints : (⋃ j, Set.range (pointsMap B S hS (Xopen i j).toFunctor (Xopen i j).ι))
        = Set.univ :=
      (isZariskiCover_iff_iUnion_points B S hS (pullback f (Yopen i).ι) hZi (J i) (Xopen i)
        (hXcov i).1).mp (hXcov i)
    obtain ⟨j, w, hw⟩ : ∃ (j : J i) (w : points B S hS (Xopen i j).toFunctor),
        pointsMap B S hS (Xopen i j).toFunctor (Xopen i j).ι w = z := by
      have hmem : z ∈ ⋃ j, Set.range (pointsMap B S hS (Xopen i j).toFunctor
          (Xopen i j).ι) := by
        rw [hXipoints]; trivial
      simpa only [Set.mem_iUnion, Set.mem_range] using hmem
    refine ⟨Subfunctor.range ((Xopen i j).ι ≫ pullback.fst f (Yopen i).ι), hrangeOpen i j,
      ⟨pointsMap B S hS (Xopen i j).toFunctor
        (Subfunctor.toRange ((Xopen i j).ι ≫ pullback.fst f (Yopen i).ι)) w, ?_⟩,
      hrangeChart i j⟩
    calc pointsMap B S hS
            (Subfunctor.range ((Xopen i j).ι ≫ pullback.fst f (Yopen i).ι)).toFunctor
            (Subfunctor.range ((Xopen i j).ι ≫ pullback.fst f (Yopen i).ι)).ι
            (pointsMap B S hS (Xopen i j).toFunctor
              (Subfunctor.toRange ((Xopen i j).ι ≫ pullback.fst f (Yopen i).ι)) w)
        = pointsMap B S hS (Xopen i j).toFunctor
            (Subfunctor.toRange ((Xopen i j).ι ≫ pullback.fst f (Yopen i).ι) ≫
              (Subfunctor.range ((Xopen i j).ι ≫ pullback.fst f (Yopen i).ι)).ι) w := by
          rw [pointsMap_comp]; rfl
      _ = pointsMap B S hS (Xopen i j).toFunctor
            ((Xopen i j).ι ≫ pullback.fst f (Yopen i).ι) w := by
          rw [Subfunctor.toRange_ι]
      _ = pointsMap B S hS (pullback f (Yopen i).ι) (pullback.fst f (Yopen i).ι)
            (pointsMap B S hS (Xopen i j).toFunctor (Xopen i j).ι w) := by
          rw [pointsMap_comp]; rfl
      _ = x := by rw [hw]; exact hzFst
  tfae_finish

end AlgebraicGeometry.Space

end
