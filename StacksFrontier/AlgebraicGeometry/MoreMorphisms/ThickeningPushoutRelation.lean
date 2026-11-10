module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutPrescribed
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutUnconditionalSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningAffineFlatPushout

/-!
# The pushed-out relation of a thickening-and-affine span is an étale equivalence relation

Let `k : U ⟶ U'` be a thickening of schemes and `g : U ⟶ V` an affine morphism, with pushout
`P = U' ⨿_U V`.  Let `t', s' : R' ⇉ U'` and `tY, sY : T ⇉ V` be étale equivalence relations,
and let `R₀` carry a thickening `kR : R₀ ⟶ R'` and an affine morphism `gR : R₀ ⟶ T` such that
both projections of `R₀` to `U` exhibit `R₀` as the restriction of `R'` along `k` and of `T`
along `g`.  Then the pushout `Rel = R' ⨿_{R₀} T`, with the two morphisms `t, s : Rel ⇉ P`
induced by the projections, is again an étale equivalence relation.

This is the step of the proof of [Stacks Project, Tag 07VX] that the source states as
"`j'` is an equivalence relation ... (details omitted)": the relation `Rel ⇉ P` of the chart
of the pushout `Y ⨿_X X'` of algebraic spaces.

## Main results

* `Stacks.Pushout.eq_of_comp_etale_of_eq_on_surjective`: two morphisms into an étale (indeed
  unramified, locally of finite type) scheme over a common base which agree after composing with a
  surjection are equal.
* `CategoryTheory.Limits.isPullback_pullbackCone_map`: two cartesian squares over the two legs of
  a pair of morphisms induce a cartesian square of the fibre products.
* `Stacks.Pushout.etale_of_isPushout_relation`: the two induced morphisms are étale.
* `Stacks.Pushout.equivalenceRelation_of_isPushout`: the two induced morphisms form an
  equivalence relation.

## Implementation notes

The two morphisms are étale by the étale clause of [Stacks Project, Tag 07RX] on prescribed
squares.  Joint monicity is checked after restriction to the thickening `Z ×_P V` of a test
scheme `Z`, where both test morphisms land in `T`, using that the diagonal of the étale `s` is an
open immersion.  Reflexivity and symmetry are induced on the pushout from the corresponding
morphisms of `R'` and `T`.  Transitivity uses the counit assertion of Tag 07RX on prescribed
squares: `Rel ×_{s, P, t} Rel` is étale, hence flat, over `P`, so it is the pushout of its base
changes, which are the composable pairs of `R'`, of `T` and of `R₀`.

## References

* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
* [Stacks Project, Tag 07VX](https://stacks.math.columbia.edu/tag/07VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Thickenings

universe u

namespace CategoryTheory.Limits

variable {C : Type*} [Category C]

/-- The two legs of a pullback cone of `s', t'` composed with `α` form a commutative square over
`s, t`, when `α` is compatible with `s, t` and `s', t'` over a common morphism `a`. -/
private theorem comp_condition_of_cone {R R' P U' : C} {s t : R ⟶ P} {s' t' : R' ⟶ U'}
    {α : R' ⟶ R} {a : U' ⟶ P} (hs : α ≫ s = s' ≫ a) (ht : α ≫ t = t' ≫ a)
    (c' : PullbackCone s' t') : (c'.fst ≫ α) ≫ s = (c'.snd ≫ α) ≫ t := by
  rw [Category.assoc, Category.assoc, hs, ht, ← Category.assoc, ← Category.assoc, c'.condition]

/-- Two cartesian squares `R' = R ×_{s, P} U'` and `R' = R ×_{t, P} U'` over the two legs of a
pair `s, t : R ⇉ P`, sharing the morphism `aR : R' ⟶ R`, induce a cartesian square exhibiting the
fibre product `R' ×_{s', U', t'} R'` as the base change of `R ×_{s, P, t} R` along `a : U' ⟶ P`. -/
theorem isPullback_pullbackCone_map {R R' P U' : C} {s t : R ⟶ P} {s' t' : R' ⟶ U'}
    {aR : R' ⟶ R} {a : U' ⟶ P} (hs : IsPullback aR s' s a) (ht : IsPullback aR t' t a)
    {c : PullbackCone s t} (hc : IsLimit c) {c' : PullbackCone s' t'} (hc' : IsLimit c') :
    IsPullback (PullbackCone.IsLimit.lift hc (c'.fst ≫ aR) (c'.snd ≫ aR)
        (by rw [Category.assoc, Category.assoc, hs.w, ht.w, ← Category.assoc,
          ← Category.assoc, c'.condition]))
      (c'.fst ≫ s') (c.fst ≫ s) a := by
  set L := PullbackCone.IsLimit.lift hc (c'.fst ≫ aR) (c'.snd ≫ aR)
    (comp_condition_of_cone hs.w ht.w c') with hLdef
  have hL1 : L ≫ c.fst = c'.fst ≫ aR := PullbackCone.IsLimit.lift_fst _ _ _ _
  have hL2 : L ≫ c.snd = c'.snd ≫ aR := PullbackCone.IsLimit.lift_snd _ _ _ _
  have hw : L ≫ c.fst ≫ s = (c'.fst ≫ s') ≫ a := by
    rw [← Category.assoc, hL1, Category.assoc, hs.w, Category.assoc]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw (fun l => ?_) (fun l => ?_) (fun l => ?_)
    (fun l m h₁ h₂ => ?_)⟩⟩
  · exact PullbackCone.IsLimit.lift hc'
      (hs.lift (l.fst ≫ c.fst) l.snd (by rw [Category.assoc, l.condition]))
      (ht.lift (l.fst ≫ c.snd) l.snd (by rw [Category.assoc, ← c.condition, l.condition]))
      (by rw [hs.lift_snd, ht.lift_snd])
  · apply PullbackCone.IsLimit.hom_ext hc
    · rw [Category.assoc, hL1, ← Category.assoc, PullbackCone.IsLimit.lift_fst, hs.lift_fst]
    · rw [Category.assoc, hL2, ← Category.assoc, PullbackCone.IsLimit.lift_snd, ht.lift_fst]
  · rw [← Category.assoc, PullbackCone.IsLimit.lift_fst, hs.lift_snd]
  · apply PullbackCone.IsLimit.hom_ext hc'
    · apply hs.hom_ext
      · rw [PullbackCone.IsLimit.lift_fst, hs.lift_fst, Category.assoc, ← hL1,
          ← Category.assoc, h₁]
      · rw [PullbackCone.IsLimit.lift_fst, hs.lift_snd, ← h₂, Category.assoc]
    · apply ht.hom_ext
      · rw [PullbackCone.IsLimit.lift_snd, ht.lift_fst, Category.assoc, ← hL2,
          ← Category.assoc, h₁]
      · rw [PullbackCone.IsLimit.lift_snd, ht.lift_snd, Category.assoc, ← c'.condition]
        exact h₂

end CategoryTheory.Limits

namespace Stacks.Pushout

/-- Two morphisms `x, y : Z ⟶ R` over a common morphism `Z ⟶ P` through an unramified morphism
`s : R ⟶ P` locally of finite type, which agree after precomposition with a surjective morphism
`ι : Z₀ ⟶ Z`, are equal: the diagonal of `s` is an open immersion, and the pair `(x, y)` lands in
it because it does so on the image of `ι`. -/
theorem eq_of_comp_etale_of_eq_on_surjective {R P Z Z₀ : Scheme.{u}} (s : R ⟶ P)
    [FormallyUnramified s] [LocallyOfFiniteType s] {x y : Z ⟶ R} (hxy : x ≫ s = y ≫ s)
    (ι : Z₀ ⟶ Z) [Surjective ι] (h : ι ≫ x = ι ≫ y) : x = y := by
  let φ : Z ⟶ pullback s s := pullback.lift x y hxy
  have hrange : Set.range φ ⊆ Set.range (pullback.diagonal s) := by
    have hιφ : ι ≫ φ = (ι ≫ x) ≫ pullback.diagonal s := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
          Category.comp_id]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
          Category.comp_id, h]
    rintro _ ⟨z, rfl⟩
    obtain ⟨z₀, rfl⟩ := ι.surjective z
    refine ⟨(ι ≫ x) z₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hιφ, Scheme.Hom.comp_apply]
  have hfac := IsOpenImmersion.lift_fac (pullback.diagonal s) φ hrange
  have hx : x = IsOpenImmersion.lift (pullback.diagonal s) φ hrange := by
    have := congrArg (fun m => m ≫ pullback.fst s s) hfac
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, φ,
      pullback.lift_fst] at this
    exact this.symm
  have hy : y = IsOpenImmersion.lift (pullback.diagonal s) φ hrange := by
    have := congrArg (fun m => m ≫ pullback.snd s s) hfac
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, φ,
      pullback.lift_snd] at this
    exact this.symm
  rw [hx, hy]

section relation

variable {U U' V P : Scheme.{u}} {k : U ⟶ U'} {g : U ⟶ V} {a : U' ⟶ P} {b : V ⟶ P}
  (hP : IsPushout k g a b) (hk : IsThickening k) [IsAffineHom g]
  {R₀ R' T Rel : Scheme.{u}} {kR : R₀ ⟶ R'} {gR : R₀ ⟶ T} {aR : R' ⟶ Rel} {bR : T ⟶ Rel}
  (hR : IsPushout kR gR aR bR)
  {s' t' : R' ⟶ U'} {sY tY : T ⟶ V} {s₀ t₀ : R₀ ⟶ U}
  (hsi : IsPullback kR s₀ s' k) (hsf : IsPullback gR s₀ sY g)
  (hti : IsPullback kR t₀ t' k) (htf : IsPullback gR t₀ tY g)
  {s t : Rel ⟶ P} (hsa : aR ≫ s = s' ≫ a) (hsb : bR ≫ s = sY ≫ b)
  (hta : aR ≫ t = t' ≫ a) (htb : bR ≫ t = tY ≫ b)

include hP hk hR hsi hsf hsa hsb in
/-- The morphism `s : R' ⨿_{R₀} T ⟶ U' ⨿_U V` induced by étale morphisms `s' : R' ⟶ U'` and
`sY : T ⟶ V` is étale: the étale clause of [Stacks Project, Tag 07RX] on prescribed squares. -/
theorem etale_of_isPushout_relation [Etale s'] [Etale sY] : Etale s :=
  (AlgebraicGeometry.ThickeningAffineGluing.etale_induced_iff_of_isPushout hk hP hR hsi hsf
    hsa hsb).2 ⟨inferInstance, inferInstance⟩

include hP hk hR hsi hsf hti htf hsa hsb hta htb in
/-- **The pushed-out relation is an equivalence relation.**  Let `P = U' ⨿_U V` be the pushout
of a thickening `k` and an affine morphism `g`, let `t', s' : R' ⇉ U'` and `tY, sY : T ⇉ V` be
equivalence relations with étale projections, and let `Rel = R' ⨿_{R₀} T` be the pushout of a
thickening `kR` and an affine morphism `gR` whose two projections to `U` restrict both relations
compatibly.  Then the induced pair `t, s : Rel ⇉ P` is an equivalence relation. -/
theorem nonempty_equivalenceRelation_of_isPushout [Etale s'] [Etale t'] [Etale sY] [Etale tY]
    (e' : EquivalenceRelation t' s') (eY : EquivalenceRelation tY sY) :
    Nonempty (EquivalenceRelation t s) := by
  have : IsClosedImmersion k := hk.1
  have : IsClosedImmersion b := (isThickening_of_isPushout_of_isThickening hP hk).1
  have : Mono k := inferInstance
  have hbmono : Mono b := inferInstance
  have : Etale s := etale_of_isPushout_relation hP hk hR hsi hsf hsa hsb
  have : Etale t := etale_of_isPushout_relation hP hk hR hti htf hta htb
  have hjY : ∀ {W : Scheme.{u}} (x y : W ⟶ T), x ≫ tY = y ≫ tY → x ≫ sY = y ≫ sY → x = y :=
    fun x y h₁ h₂ => eY.right_cancellation x y h₁ h₂
  -- the two cartesian squares of the `V`-side and of the `U'`-side
  obtain ⟨hsbY, hsaX⟩ :=
    AlgebraicGeometry.ThickeningAffinePushoutSituation.isPullback_of_isPushout_of_isPullback
      hP hk hR hsi hsf hsa hsb
  obtain ⟨htbY, htaX⟩ :=
    AlgebraicGeometry.ThickeningAffinePushoutSituation.isPullback_of_isPushout_of_isPullback
      hP hk hR hti htf hta htb
  -- joint monicity, tested on the thickening `Z ×_P V` of a test scheme
  have hmono : ∀ {Z : Scheme.{u}} (x y : Z ⟶ Rel), x ≫ t = y ≫ t → x ≫ s = y ≫ s → x = y := by
    intro Z x y h₁ h₂
    have : Surjective (pullback.fst (x ≫ s) b) := by
      have : Surjective b := ⟨(isThickening_of_isPushout_of_isThickening hP hk).2⟩
      infer_instance
    refine eq_of_comp_etale_of_eq_on_surjective s h₂ (pullback.fst (x ≫ s) b) ?_
    let x₀ : pullback (x ≫ s) b ⟶ T := hsbY.lift (pullback.fst _ _ ≫ x) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition])
    let y₀ : pullback (x ≫ s) b ⟶ T := hsbY.lift (pullback.fst _ _ ≫ y) (pullback.snd _ _)
      (by rw [Category.assoc, ← h₂, pullback.condition])
    have hx₀ : x₀ ≫ bR = pullback.fst _ _ ≫ x := hsbY.lift_fst _ _ _
    have hy₀ : y₀ ≫ bR = pullback.fst _ _ ≫ y := hsbY.lift_fst _ _ _
    have : x₀ = y₀ := by
      refine hjY _ _ ?_ ?_
      · rw [← cancel_mono b, Category.assoc, Category.assoc, ← htb, ← Category.assoc, hx₀,
          ← Category.assoc, hy₀, Category.assoc, Category.assoc, h₁]
      · simp only [x₀, y₀, IsPullback.lift_snd]
    rw [← hx₀, ← hy₀, this]
  -- reflexivity
  let r₀ : U ⟶ R₀ := hsi.lift (k ≫ e'.r) (𝟙 U) (by simp)
  have hr₀t : r₀ ≫ t₀ = 𝟙 U := by
    rw [← cancel_mono k, Category.assoc, ← hti.w, ← Category.assoc, hsi.lift_fst]
    simp
  have hr₀ : k ≫ e'.r ≫ aR = g ≫ eY.r ≫ bR := by
    have h1 : r₀ ≫ gR = g ≫ eY.r := by
      refine hjY _ _ ?_ ?_
      · rw [Category.assoc, htf.w, ← Category.assoc, hr₀t]
        simp
      · rw [Category.assoc, hsf.w, ← Category.assoc, hsi.lift_snd]
        simp
    rw [← Category.assoc, ← hsi.lift_fst (k ≫ e'.r) (𝟙 U) (by simp), Category.assoc, hR.w,
      ← Category.assoc]
    change (r₀ ≫ gR) ≫ bR = _
    rw [h1, Category.assoc]
  let r : P ⟶ Rel := hP.desc (e'.r ≫ aR) (eY.r ≫ bR) hr₀
  have hr₁ : r ≫ t = 𝟙 P := by
    refine hP.hom_ext ?_ ?_
    · rw [← Category.assoc, hP.inl_desc, Category.assoc, hta, ← Category.assoc, e'.reflexivity₁]
      simp
    · rw [← Category.assoc, hP.inr_desc, Category.assoc, htb, ← Category.assoc, eY.reflexivity₁]
      simp
  have hr₂ : r ≫ s = 𝟙 P := by
    refine hP.hom_ext ?_ ?_
    · rw [← Category.assoc, hP.inl_desc, Category.assoc, hsa, ← Category.assoc, e'.reflexivity₂]
      simp
    · rw [← Category.assoc, hP.inr_desc, Category.assoc, hsb, ← Category.assoc, eY.reflexivity₂]
      simp
  -- symmetry
  let σ₀ : R₀ ⟶ R₀ := hsi.lift (kR ≫ e'.s) t₀ (by rw [Category.assoc, e'.symmetry₂, hti.w])
  have hσ₀t : σ₀ ≫ t₀ = s₀ := by
    rw [← cancel_mono k, Category.assoc, ← hti.w, ← Category.assoc, hsi.lift_fst, Category.assoc,
      e'.symmetry₁, hsi.w]
  have hσ : kR ≫ e'.s ≫ aR = gR ≫ eY.s ≫ bR := by
    have h1 : σ₀ ≫ gR = gR ≫ eY.s := by
      refine hjY _ _ ?_ ?_
      · rw [Category.assoc, htf.w, ← Category.assoc, hσ₀t, Category.assoc, eY.symmetry₁,
          hsf.w]
      · rw [Category.assoc, hsf.w, ← Category.assoc, hsi.lift_snd, Category.assoc,
          eY.symmetry₂, htf.w]
    rw [← Category.assoc, ← hsi.lift_fst (kR ≫ e'.s) t₀
      (by rw [Category.assoc, e'.symmetry₂, hti.w]), Category.assoc, hR.w, ← Category.assoc]
    change (σ₀ ≫ gR) ≫ bR = _
    rw [h1, Category.assoc]
  let σ : Rel ⟶ Rel := hR.desc (e'.s ≫ aR) (eY.s ≫ bR) hσ
  have hσ₁ : σ ≫ t = s := by
    refine hR.hom_ext ?_ ?_
    · rw [← Category.assoc, hR.inl_desc, Category.assoc, hta, ← Category.assoc, e'.symmetry₁, hsa]
    · rw [← Category.assoc, hR.inr_desc, Category.assoc, htb, ← Category.assoc, eY.symmetry₁, hsb]
  have hσ₂ : σ ≫ s = t := by
    refine hR.hom_ext ?_ ?_
    · rw [← Category.assoc, hR.inl_desc, Category.assoc, hsa, ← Category.assoc, e'.symmetry₂, hta]
    · rw [← Category.assoc, hR.inr_desc, Category.assoc, hsb, ← Category.assoc, eY.symmetry₂, htb]
  -- transitivity: the composable pairs, as a pushout of the composable pairs of the pieces
  let c : PullbackCone s t := PullbackCone.mk (pullback.fst s t) (pullback.snd s t)
    pullback.condition
  have hc : IsLimit c := pullbackIsPullback s t
  let c₀ : PullbackCone s₀ t₀ := PullbackCone.mk (pullback.fst s₀ t₀) (pullback.snd s₀ t₀)
    pullback.condition
  have hc₀ : IsLimit c₀ := pullbackIsPullback s₀ t₀
  have hV := isPullback_pullbackCone_map hsbY htbY hc eY.isLimit
  have hU' := isPullback_pullbackCone_map hsaX htaX hc e'.isLimit
  have hjV := isPullback_pullbackCone_map hsf htf eY.isLimit hc₀
  let cV := PullbackCone.IsLimit.lift hc (eY.c.fst ≫ bR) (eY.c.snd ≫ bR)
    (comp_condition_of_cone hsbY.w htbY.w eY.c)
  let cU' := PullbackCone.IsLimit.lift hc (e'.c.fst ≫ aR) (e'.c.snd ≫ aR)
    (comp_condition_of_cone hsaX.w htaX.w e'.c)
  let jV := PullbackCone.IsLimit.lift eY.isLimit (c₀.fst ≫ gR) (c₀.snd ≫ gR)
    (comp_condition_of_cone hsf.w htf.w c₀)
  let jU' := PullbackCone.IsLimit.lift e'.isLimit (c₀.fst ≫ kR) (c₀.snd ≫ kR)
    (comp_condition_of_cone hsi.w hti.w c₀)
  have hjU' : jU' ≫ e'.c.fst ≫ s' = (c₀.fst ≫ s₀) ≫ k := by
    rw [← Category.assoc, PullbackCone.IsLimit.lift_fst, Category.assoc, hsi.w,
      Category.assoc]
  have hcomm : jV ≫ cV = jU' ≫ cU' := by
    apply PullbackCone.IsLimit.hom_ext hc
    · simp only [Category.assoc, cV, cU', PullbackCone.IsLimit.lift_fst]
      rw [← Category.assoc, PullbackCone.IsLimit.lift_fst, ← Category.assoc,
        PullbackCone.IsLimit.lift_fst, Category.assoc, Category.assoc, hR.w]
    · simp only [Category.assoc, cV, cU', PullbackCone.IsLimit.lift_snd]
      rw [← Category.assoc, PullbackCone.IsLimit.lift_snd, ← Category.assoc,
        PullbackCone.IsLimit.lift_snd, Category.assoc, Category.assoc, hR.w]
  have hflat : Flat (c.fst ≫ s) := by
    have : Etale (pullback.fst s t) := inferInstance
    change Flat (pullback.fst s t ≫ s)
    infer_instance
  have hpush : IsPushout jV jU' cV cU' :=
    isPushout_of_flat_of_isPullback_of_isPushout hk hP (c.fst ≫ s) hflat hV hU' hjV hjU' hcomm
  -- the composition morphism of `R₀`
  let τ₀ : c₀.pt ⟶ R₀ := hsi.lift (jU' ≫ e'.t) (c₀.snd ≫ s₀) (by
    rw [Category.assoc, e'.transitivity₂, ← Category.assoc, PullbackCone.IsLimit.lift_snd,
      Category.assoc, hsi.w, Category.assoc])
  have hτ₀t : τ₀ ≫ t₀ = c₀.fst ≫ t₀ := by
    rw [← cancel_mono k, Category.assoc, ← hti.w, ← Category.assoc, hsi.lift_fst, Category.assoc,
      e'.transitivity₁, ← Category.assoc, PullbackCone.IsLimit.lift_fst, Category.assoc,
      hti.w, Category.assoc]
  have hτ : jV ≫ eY.t ≫ bR = jU' ≫ e'.t ≫ aR := by
    have h1 : τ₀ ≫ gR = jV ≫ eY.t := by
      refine hjY _ _ ?_ ?_
      · rw [Category.assoc, htf.w, ← Category.assoc, hτ₀t, Category.assoc, Category.assoc,
          eY.transitivity₁, ← Category.assoc jV, PullbackCone.IsLimit.lift_fst,
          Category.assoc, htf.w]
      · rw [Category.assoc, hsf.w, ← Category.assoc, hsi.lift_snd, Category.assoc,
          Category.assoc, eY.transitivity₂, ← Category.assoc jV, PullbackCone.IsLimit.lift_snd,
          Category.assoc, hsf.w]
    rw [← Category.assoc, ← h1, Category.assoc, ← hR.w, ← Category.assoc, hsi.lift_fst,
      Category.assoc]
  let τ : c.pt ⟶ Rel := hpush.desc (eY.t ≫ bR) (e'.t ≫ aR) hτ
  have hτ₁ : τ ≫ t = c.fst ≫ t := by
    refine hpush.hom_ext ?_ ?_
    · rw [← Category.assoc, hpush.inl_desc, Category.assoc, htb, ← Category.assoc, eY.transitivity₁,
        ← Category.assoc cV, PullbackCone.IsLimit.lift_fst, Category.assoc, Category.assoc,
        htb]
    · rw [← Category.assoc, hpush.inr_desc, Category.assoc, hta, ← Category.assoc, e'.transitivity₁,
        ← Category.assoc cU', PullbackCone.IsLimit.lift_fst, Category.assoc, Category.assoc,
        hta]
  have hτ₂ : τ ≫ s = c.snd ≫ s := by
    refine hpush.hom_ext ?_ ?_
    · rw [← Category.assoc, hpush.inl_desc, Category.assoc, hsb, ← Category.assoc, eY.transitivity₂,
        ← Category.assoc cV, PullbackCone.IsLimit.lift_snd, Category.assoc, Category.assoc,
        hsb]
    · rw [← Category.assoc, hpush.inr_desc, Category.assoc, hsa, ← Category.assoc, e'.transitivity₂,
        ← Category.assoc cU', PullbackCone.IsLimit.lift_snd, Category.assoc, Category.assoc,
        hsa]
  exact ⟨{ right_cancellation := fun _ x y h₁ h₂ => hmono x y h₁ h₂
           r := r
           reflexivity₁ := hr₁
           reflexivity₂ := hr₂
           s := σ
           symmetry₁ := hσ₁
           symmetry₂ := hσ₂
           c := c
           isLimit := hc
           t := τ
           transitivity₁ := hτ₁
           transitivity₂ := hτ₂ }⟩

end relation

end Stacks.Pushout

end
