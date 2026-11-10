module

public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquarePushout
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FppfSourceLocalityFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SeparatedFromElementarySquare
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite

/-!
# Glueing two algebraic spaces along a common open subspace

Let `X₁₂ ⟶ X₁` and `X₁₂ ⟶ X₂` be open immersions of algebraic spaces over a scheme `S`.  The
pushout `W = X₁ ⊔_{X₁₂} X₂` in the category of algebraic spaces over `S` is the space obtained
by glueing `X₁` and `X₂` along `X₁₂`.  It is the special case of Stacks 0DVJ in which the
separated étale morphism `V' ⟶ U` is an open immersion.

This file records what the glueing is: both `X₁ ⟶ W` and `X₂ ⟶ W` are open immersions, and
the two form an elementary distinguished square.  The first is not part of Stacks 0DVJ, which
only asserts that `X₁ ⟶ W` is étale; it follows by applying Stacks 0DVJ a second time, with the
roles of `X₁` and `X₂` exchanged, and comparing the two pushouts.

If moreover `X₁` and `X₂` are separated over an algebraic space `Y`, the glued space is
separated over `Y` as soon as `X₁₂ ⟶ X₁ ×_Y X₂` is a closed immersion and `X₁₂` contains a
scheme-theoretically dense open subspace of `X₁`.  Under these hypotheses `X₁₂` is exactly the
intersection `X₁ ×_W X₂`, and the diagonal of `W` over `Y` can be checked on the four pieces
`X_i ×_Y X_j` of `W ×_Y W`, by Stacks 0F45.  The glued space is of finite type over `Y` when
`X₁` and `X₂` are and `Y` is quasi-separated.

## Main results

* `AlgebraicGeometry.Space.exists_isPushout_isOpenImmersion_of_isOpenImmersion`: the glueing of
  two algebraic spaces along a common open subspace, with open immersions into it.
* `AlgebraicGeometry.Space.isPullback_of_isClosedImmersion_lift`: over a base `Y` for which
  `X₁₂ ⟶ X₁ ×_Y X₂` is a closed immersion, and with `X₁₂` containing a scheme-theoretically
  dense open of `X₁`, the overlap of the glueing is `X₁₂`.
* `AlgebraicGeometry.Space.isSeparated_of_isPullback_of_isClosedImmersion_lift`: the glueing is
  then separated over `Y`.
* `AlgebraicGeometry.Space.isFiniteType_of_isElementaryDistinguishedSquare`: a space covered by
  an elementary distinguished square of finite type pieces over a quasi-compact and
  quasi-separated base is of finite type over it.

## Implementation notes

The glueing is Stacks 0DVJ,
`AlgebraicGeometry.Space.exists_pushout_isElementaryDistinguishedSquare`, applied to the open
subspace `e₁(X₁₂) ⊆ X₁` and the open immersion `e₁(X₁₂) ≅ X₁₂ ⟶ X₂`.

## References

* [Stacks Project, Tag 0DVJ](https://stacks.math.columbia.edu/tag/0DVJ)
* [Stacks Project, Tag 0DVI](https://stacks.math.columbia.edu/tag/0DVI)
* [Stacks Project, Tag 0F45](https://stacks.math.columbia.edu/tag/0F45)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- For a monomorphism `p` the inverse of the isomorphism onto its range, followed by `p`, is
the inclusion of the range. -/
@[reassoc (attr := simp)]
theorem CategoryTheory.Subfunctor.inv_toRange_comp_of_mono {C : Type*} [Category C]
    {F F' : C ⥤ Type u} (p : F' ⟶ F) [Mono p] :
    inv (Subfunctor.toRange p) ≫ p = (Subfunctor.range p).ι := by
  rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **One application of Stacks 0DVJ to two open immersions.**  For open immersions
`e₁ : X₁₂ ⟶ X₁` and `e₂ : X₁₂ ⟶ X₂` there are an algebraic space `W`, a morphism
`i₁ : X₁ ⟶ W` and an open subspace `Uw ⊆ W` isomorphic to `X₂` such that `(Uw ⊆ W, i₁)` is an
elementary distinguished square and `W` is the pushout of `X₁ ← X₁₂ → X₂`.

Stacks 0DVJ is applied to the open subspace `e₁(X₁₂) ⊆ X₁` and to the open immersion
`e₁(X₁₂) ≅ X₁₂ ⟶ X₂`, which is separated and étale. -/
theorem exists_isPushout_isElementaryDistinguishedSquare_of_isOpenImmersion
    {X₁₂ X₁ X₂ : AlgebraicSpaces B S hS} (e₁ : X₁₂ ⟶ X₁) (e₂ : X₁₂ ⟶ X₂)
    (he₁ : IsOpenImmersion B S hS e₁.hom) (he₂ : IsOpenImmersion B S hS e₂.hom) :
    ∃ (W : AlgebraicSpaces B S hS) (i₁ : X₁ ⟶ W) (Uw : Subfunctor W.obj)
      (ε : X₂.obj ≅ Uw.toFunctor),
      IsElementaryDistinguishedSquare B S hS W.property Uw i₁.hom ∧
        IsPushout e₁ e₂ i₁ (ObjectProperty.homMk (ε.hom ≫ Uw.ι)) := by
  have : Mono e₁.hom := mono_of_isOpenImmersion B S hS _ he₁
  have hV' : IsOpenSubspace B S hS (Subfunctor.range e₁.hom) :=
    isOpenSubspace_range_of_open B S hS e₁.hom X₁₂.2 he₁
  let t : X₁₂.obj ≅ (Subfunctor.range e₁.hom).toFunctor := asIso (Subfunctor.toRange e₁.hom)
  have hf' : IsOpenImmersion B S hS (t.inv ≫ e₂.hom) :=
    isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _) he₂
  obtain ⟨W, Uw, ε, f, hsq, hpo⟩ := exists_pushout_isElementaryDistinguishedSquare B S hS X₂ X₁
    (Subfunctor.range e₁.hom) hV' (t.inv ≫ e₂.hom)
    (isEtale_of_isOpenImmersion B S hS hf')
    (isSeparated_of_mono B S hS _ (mono_of_isOpenImmersion B S hS _ hf'))
  refine ⟨W, f, Uw, ε, hsq, ?_⟩
  refine hpo.of_iso' (ObjectProperty.isoMk _ t) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext : 1
    simp [t]
  · ext : 1
    simp
  · simp
  · simp

/-- **Glueing two algebraic spaces along a common open subspace**, over Stacks 0DVJ.  Let
`e₁ : X₁₂ ⟶ X₁` and `e₂ : X₁₂ ⟶ X₂` be open immersions of algebraic spaces over `S`.  There is
a pushout square `X₁ ⟶ W ⟵ X₂` of `X₁ ← X₁₂ → X₂` in the category of algebraic spaces over
`S` in which **both** `i₁ : X₁ ⟶ W` and `i₂ : X₂ ⟶ W` are open immersions; moreover `i₂` is the
inclusion of an open subspace `Uw ⊆ W` read through an isomorphism `X₂ ≅ Uw`, and
`(Uw ⊆ W, i₁)` is an elementary distinguished square.

Stacks 0DVJ makes `i₂` an open immersion and `i₁` étale.  Applying it once more with `X₁` and
`X₂` exchanged gives a second pushout of the same span in which the morphism out of `X₁` is an
open immersion; the two pushouts are isomorphic compatibly with the morphisms out of `X₁`, so
`i₁` is an open immersion as well. -/
theorem exists_isPushout_isOpenImmersion_of_isOpenImmersion
    {X₁₂ X₁ X₂ : AlgebraicSpaces B S hS} (e₁ : X₁₂ ⟶ X₁) (e₂ : X₁₂ ⟶ X₂)
    (he₁ : IsOpenImmersion B S hS e₁.hom) (he₂ : IsOpenImmersion B S hS e₂.hom) :
    ∃ (W : AlgebraicSpaces B S hS) (i₁ : X₁ ⟶ W) (i₂ : X₂ ⟶ W),
      IsPushout e₁ e₂ i₁ i₂ ∧ IsOpenImmersion B S hS i₁.hom ∧ IsOpenImmersion B S hS i₂.hom ∧
        ∃ (Uw : Subfunctor W.obj) (ε : X₂.obj ≅ Uw.toFunctor), i₂.hom = ε.hom ≫ Uw.ι ∧
          IsElementaryDistinguishedSquare B S hS W.property Uw i₁.hom := by
  obtain ⟨W, i₁, Uw, ε, hsq, hpo⟩ :=
    exists_isPushout_isElementaryDistinguishedSquare_of_isOpenImmersion e₁ e₂ he₁ he₂
  obtain ⟨W', i₂', Uw', ε', hsq', hpo'⟩ :=
    exists_isPushout_isElementaryDistinguishedSquare_of_isOpenImmersion e₂ e₁ he₂ he₁
  let φ := hpo.isoIsPushout _ _ hpo'.flip
  have hφ : i₁ = ObjectProperty.homMk (ε'.hom ≫ Uw'.ι) ≫ φ.inv := by
    rw [Iso.eq_comp_inv]
    exact hpo.inl_isoIsPushout_hom _ _ hpo'.flip
  refine ⟨W, i₁, ObjectProperty.homMk (ε.hom ≫ Uw.ι), hpo, ?_, ?_, Uw, ε, rfl, hsq⟩
  · rw [hφ]
    change IsOpenImmersion B S hS ((ε'.hom ≫ Uw'.ι) ≫ φ.inv.hom)
    exact isOpenImmersion_comp B S hS _ _
      (isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _)
        hsq'.isOpenSubspace.2)
      (isOpenImmersion_of_isIso B S hS _)
  · exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _)
      hsq.isOpenSubspace.2

/-- **Over a separated base, the overlap of a glueing is the given open subspace.**  Let
`e₁ : X₁₂ ⟶ X₁` and `e₂ : X₁₂ ⟶ X₂` be open immersions and let `i₁ : X₁ ⟶ W` and
`i₂ : X₂ ⟶ W` be open immersions with `e₁ ≫ i₁ = e₂ ≫ i₂`.  Let `g : W ⟶ Y` and put
`g₁ = i₁ ≫ g`, `g₂ = i₂ ≫ g`.  If `(e₁, e₂) : X₁₂ ⟶ X₁ ×_Y X₂` is a closed immersion and
`e₁(X₁₂)` contains a scheme-theoretically dense open subspace `D` of `X₁`, then the square
`X₁₂ ⟶ X₁, X₂ ⟶ W` is cartesian: `X₁₂` is the intersection of `X₁` and `X₂` in `W`. -/
theorem isPullback_of_isClosedImmersion_lift
    {X₁₂ X₁ X₂ W Y : AlgebraicSpaces B S hS} {e₁ : X₁₂ ⟶ X₁} {e₂ : X₁₂ ⟶ X₂}
    {i₁ : X₁ ⟶ W} {i₂ : X₂ ⟶ W} (hw : e₁ ≫ i₁ = e₂ ≫ i₂)
    (he₁ : IsOpenImmersion B S hS e₁.hom) (_hi₁ : IsOpenImmersion B S hS i₁.hom)
    (hi₂ : IsOpenImmersion B S hS i₂.hom) (g : W ⟶ Y) {g₁ : X₁ ⟶ Y} {g₂ : X₂ ⟶ Y}
    (h₁ : i₁ ≫ g = g₁) (h₂ : i₂ ≫ g = g₂) (hg : e₁.hom ≫ g₁.hom = e₂.hom ≫ g₂.hom)
    (hc : IsClosedImmersion B S hS (pullback.lift e₁.hom e₂.hom hg))
    (D : Subfunctor X₁.obj) (hD : IsSchemeTheoreticallyDense B S hS D)
    (hDe : D ≤ Subfunctor.range e₁.hom) :
    IsPullback e₁.hom e₂.hom i₁.hom i₂.hom := by
  subst h₁ h₂
  have hw' : e₁.hom ≫ i₁.hom = e₂.hom ≫ i₂.hom := congrArg (fun k => k.hom) hw
  have : Mono e₁.hom := mono_of_isOpenImmersion B S hS _ he₁
  have : Mono i₂.hom := mono_of_isOpenImmersion B S hS _ hi₂
  set R := Subfunctor.range i₂.hom with hRdef
  have hR : IsOpenSubspace B S hS R := isOpenSubspace_range_of_open B S hS i₂.hom X₂.2 hi₂
  set N := R.preimage i₁.hom with hNdef
  have hN : IsOpenSubspace B S hS N := isOpenSubspace_preimage B S hS i₁.hom R W.2 X₁.2 hR
  have hRι : inv (Subfunctor.toRange i₂.hom) ≫ i₂.hom = R.ι :=
    Subfunctor.inv_toRange_comp_of_mono i₂.hom
  let γ : N.toFunctor ⟶ X₂.obj := R.fromPreimage i₁.hom ≫ inv (Subfunctor.toRange i₂.hom)
  have hγ : γ ≫ i₂.hom = N.ι ≫ i₁.hom := by
    simpa only [γ, Category.assoc, hRι] using Subfunctor.fromPreimage_ι R i₁.hom
  have hγg : N.ι ≫ i₁.hom ≫ g.hom = γ ≫ i₂.hom ≫ g.hom := by
    rw [← Category.assoc, ← hγ, Category.assoc]
  let Γ : N.toFunctor ⟶ pullback (i₁.hom ≫ g.hom) (i₂.hom ≫ g.hom) := pullback.lift N.ι γ hγg
  set c := (pullback.lift e₁.hom e₂.hom hg :
        X₁₂.obj ⟶ pullback (i₁.hom ≫ g.hom) (i₂.hom ≫ g.hom)) with hcdef
  have hP : IsAlgebraicSpace B S hS (pullback (i₁.hom ≫ g.hom) (i₂.hom ≫ g.hom)) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS _ _ X₁.2 X₂.2 Y.2
  have hcR : IsClosedSubspace B S hS (Subfunctor.range c) :=
    isClosedSubspace_range_of_isClosedImmersion B S hS c X₁₂.2 hc
  have hC : IsClosedSubspace B S hS ((Subfunctor.range c).preimage Γ) :=
    isClosedSubspace_preimage B S hS Γ _ hP hN.1 hcR
  set D' := D.preimage N.ι with hD'def
  have hD'le : Subfunctor.range (D'.ι ≫ N.ι) ≤ Subfunctor.range e₁.hom := by
    rw [← Subfunctor.fromPreimage_ι D N.ι]
    exact (Subfunctor.range_comp_le _ _).trans ((Subfunctor.range_ι D).le.trans hDe)
  let κ : D'.toFunctor ⟶ X₁₂.obj :=
    Subfunctor.lift (D'.ι ≫ N.ι) hD'le ≫ inv (Subfunctor.toRange e₁.hom)
  have hκ : κ ≫ e₁.hom = D'.ι ≫ N.ι := by
    simp only [κ, Category.assoc, Subfunctor.inv_toRange_comp_of_mono, Subfunctor.lift_ι]
  have hD'Γ : D'.ι ≫ Γ = κ ≫ c := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, Γ, c, pullback.lift_fst, hκ]
    · simp only [Category.assoc, Γ, c, pullback.lift_snd]
      refine (cancel_mono i₂.hom).1 ?_
      rw [Category.assoc, hγ, Category.assoc, ← hw', ← Category.assoc κ, hκ, Category.assoc]
  have hDN : D' ≤ (Subfunctor.range c).preimage Γ := by
    rw [← Subfunctor.image_le_iff]
    calc D'.image Γ = Subfunctor.range (D'.ι ≫ Γ) := by
          rw [Subfunctor.range_comp, Subfunctor.range_ι]
      _ = Subfunctor.range (κ ≫ c) := by rw [hD'Γ]
      _ ≤ Subfunctor.range c := Subfunctor.range_comp_le _ _
  have hcl : schemeTheoreticClosure B S hS D' = ⊤ :=
    hD hN.1 N.ι (isEtale_of_isOpenImmersion B S hS hN.2)
  have hCtop : (Subfunctor.range c).preimage Γ = ⊤ := by
    refine top_unique ?_
    rw [← hcl]
    exact schemeTheoreticImageSubfunctor_le B S hS _ hC (by rw [Subfunctor.range_ι]; exact hDN)
  have hrange : Subfunctor.range Γ ≤ Subfunctor.range c :=
    (Subfunctor.preimage_eq_top_iff _ _).1 hCtop
  have : Mono c := mono_of_isClosedImmersion B S hS c hc
  let Γ' : N.toFunctor ⟶ X₁₂.obj :=
    Subfunctor.lift Γ hrange ≫ inv (Subfunctor.toRange c)
  have hΓ' : Γ' ≫ c = Γ := by
    simp only [Γ', Category.assoc, Subfunctor.inv_toRange_comp_of_mono, Subfunctor.lift_ι]
  have hΓ'e : Γ' ≫ e₁.hom = N.ι := by
    have h1 : Γ' ≫ c ≫ pullback.fst _ _ = Γ ≫ pullback.fst _ _ := by
      rw [← Category.assoc, hΓ']
    rwa [pullback.lift_fst, pullback.lift_fst] at h1
  have hNe : N ≤ Subfunctor.range e₁.hom := by
    rw [← Subfunctor.range_ι N, ← hΓ'e]
    exact Subfunctor.range_comp_le _ _
  have hinv := Subfunctor.inv_toRange_comp_of_mono e₁.hom
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw' (fun s => ?_) ?_ ?_ ?_)
  · have hs : Subfunctor.range s.fst ≤ N := by
      rw [hNdef, ← Subfunctor.image_le_iff, ← Subfunctor.range_comp, s.condition]
      exact Subfunctor.range_comp_le _ _
    exact Subfunctor.lift s.fst hs ≫ Subfunctor.homOfLe hNe ≫ inv (Subfunctor.toRange e₁.hom)
  · intro s
    simp only [Category.assoc, hinv, Subfunctor.homOfLe_ι, Subfunctor.lift_ι]
  · intro s
    refine (cancel_mono i₂.hom).1 ?_
    rw [Category.assoc, ← hw', Category.assoc, Category.assoc, reassoc_of% hinv,
      Subfunctor.homOfLe_ι_assoc, Subfunctor.lift_ι_assoc, s.condition]
  · intro s m hm₁ _
    refine (cancel_mono e₁.hom).1 ?_
    rw [hm₁]
    simp only [Category.assoc, hinv, Subfunctor.homOfLe_ι, Subfunctor.lift_ι]

section ClosedLift

variable {P X X' Y Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If `P` is the fibre product `X ×_Z Y`, then the comparison
`X ×_Z Y ⟶ X ×_T Y` along `g : Z ⟶ T` is a closed immersion as soon as `P ⟶ X ×_T Y` is. -/
theorem isClosedImmersion_mapDesc_of_isPullback {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z}
    {h : Y ⟶ Z} (hpb : IsPullback a b f h) (g : Z ⟶ T)
    (hc : IsClosedImmersion B S hS (pullback.lift a b
      (by rw [← Category.assoc, hpb.w, Category.assoc]) : P ⟶ pullback (f ≫ g) (h ≫ g))) :
    IsClosedImmersion B S hS (pullback.mapDesc f h g) := by
  have h1 : pullback.mapDesc f h g ≫ pullback.fst _ _ = pullback.fst f h :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have h2 : pullback.mapDesc f h g ≫ pullback.snd _ _ = pullback.snd f h :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have heq : pullback.mapDesc f h g = hpb.isoPullback.inv ≫ pullback.lift a b
      (by rw [← Category.assoc, hpb.w, Category.assoc]) := by
    rw [Iso.eq_inv_comp]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, h1, IsPullback.isoPullback_hom_fst, pullback.lift_fst]
    · rw [Category.assoc, h2, IsPullback.isoPullback_hom_snd, pullback.lift_snd]
  rw [heq]
  exact isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS _) hc

/-- The morphism `(b, a) : P ⟶ Y ×_T X` is a closed immersion when `(a, b) : P ⟶ X ×_T Y`
is. -/
theorem isClosedImmersion_lift_swap {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ T} {h : Y ⟶ T}
    (w : a ≫ f = b ≫ h) (hc : IsClosedImmersion B S hS (pullback.lift a b w)) :
    IsClosedImmersion B S hS (pullback.lift b a w.symm) := by
  have heq : pullback.lift b a w.symm = pullback.lift a b w ≫ (pullbackSymmetry f h).hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullbackSymmetry_hom_comp_fst, pullback.lift_snd]
    · rw [pullback.lift_snd, Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.lift_fst]
  rw [heq]
  exact isClosedImmersion_comp B S hS _ _ hc (isClosedImmersion_of_isIso B S hS _)

/-- The morphism `(a, b) : P ⟶ X ×_T Y` stays a closed immersion when `X` is replaced by an
isomorphic `X'` over `T`. -/
theorem isClosedImmersion_lift_of_iso {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ T} {h : Y ⟶ T}
    (w : a ≫ f = b ≫ h) (hc : IsClosedImmersion B S hS (pullback.lift a b w))
    (φ : X ≅ X') {f' : X' ⟶ T} (hf : f = φ.hom ≫ f') :
    IsClosedImmersion B S hS (pullback.lift (f := f') (g := h) (a ≫ φ.hom) b
      (by rw [Category.assoc, ← hf, w])) := by
  let m : pullback f h ⟶ pullback f' h :=
    pullback.lift (pullback.fst f h ≫ φ.hom) (pullback.snd f h)
      (by rw [Category.assoc, ← hf, pullback.condition])
  let m' : pullback f' h ⟶ pullback f h :=
    pullback.lift (pullback.fst f' h ≫ φ.inv) (pullback.snd f' h)
      (by rw [Category.assoc, hf, Iso.inv_hom_id_assoc, pullback.condition])
  have hm : IsIso m := by
    refine ⟨m', ?_, ?_⟩
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc,
          Iso.hom_inv_id, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc,
          Iso.inv_hom_id, Category.comp_id, Category.id_comp]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  have heq : pullback.lift (f := f') (g := h) (a ≫ φ.hom) b (by rw [Category.assoc, ← hf, w]) =
      pullback.lift a b w ≫ m := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  rw [heq]
  exact isClosedImmersion_comp B S hS _ _ hc (isClosedImmersion_of_isIso B S hS _)

end ClosedLift

/-- **A glueing along a closed overlap is separated**, Stacks 0F45.  Let `i₁ : X₁ ⟶ W` and
`i₂ : X₂ ⟶ W` be open immersions which are pulled back from each other along open immersions
`e₁ : X₁₂ ⟶ X₁` and `e₂ : X₁₂ ⟶ X₂`, with `i₂` the inclusion of an open subspace `Uw ⊆ W` read
through an isomorphism and `(Uw ⊆ W, i₁)` an elementary distinguished square.  Let
`g : W ⟶ Y` be such that `X₁ ⟶ Y` and `X₂ ⟶ Y` are separated and
`(e₁, e₂) : X₁₂ ⟶ X₁ ×_Y X₂` is a closed immersion.  Then `g` is separated. -/
theorem isSeparated_of_isPullback_of_isClosedImmersion_lift
    {X₁₂ X₁ X₂ W Y : AlgebraicSpaces B S hS} {e₁ : X₁₂ ⟶ X₁} {e₂ : X₁₂ ⟶ X₂}
    {i₁ : X₁ ⟶ W} {i₂ : X₂ ⟶ W} (hpb : IsPullback e₁.hom e₂.hom i₁.hom i₂.hom)
    (hi₁ : IsOpenImmersion B S hS i₁.hom) {Uw : Subfunctor W.obj} (ε : X₂.obj ≅ Uw.toFunctor)
    (hi₂ : i₂.hom = ε.hom ≫ Uw.ι)
    (hsq : IsElementaryDistinguishedSquare B S hS W.property Uw i₁.hom) (g : W ⟶ Y)
    {g₁ : X₁ ⟶ Y} {g₂ : X₂ ⟶ Y} (h₁ : i₁ ≫ g = g₁) (h₂ : i₂ ≫ g = g₂)
    (hs₁ : IsSeparated B S hS g₁.hom) (hs₂ : IsSeparated B S hS g₂.hom)
    (hg : e₁.hom ≫ g₁.hom = e₂.hom ≫ g₂.hom)
    (hc : IsClosedImmersion B S hS (pullback.lift e₁.hom e₂.hom hg)) :
    IsSeparated B S hS g.hom := by
  subst h₁ h₂
  have hg₁ : IsSeparated B S hS (i₁.hom ≫ g.hom) := hs₁
  have hg₂ : IsSeparated B S hS (i₂.hom ≫ g.hom) := hs₂
  have hUwg : Uw.ι ≫ g.hom = ε.inv ≫ i₂.hom ≫ g.hom := by
    rw [hi₂, Category.assoc, Iso.inv_hom_id_assoc]
  have hP : ∀ {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ Y.obj) (b : G ⟶ Y.obj),
      IsAlgebraicSpace B S hS F → IsAlgebraicSpace B S hS G →
        IsAlgebraicSpace B S hS (pullback a b) := fun a b hF hG =>
    AlgebraicGeometry.isAlgebraicSpace_pullback B S hS a b hF hG Y.2
  refine isSeparated_of_elementaryDistinguishedSquare B S hS W.2 Y.2 g.hom Uw i₁.hom hsq ?_ hg₁
    ?_ ?_
  · rw [hUwg]
    exact isSeparated_comp B S hS _ _ (isSeparated_of_isIso B S hS _) hg₂
  · have hpb' : IsPullback (e₂.hom ≫ ε.hom) e₁.hom Uw.ι i₁.hom := by
      refine hpb.flip.of_iso (Iso.refl _) ε (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp
      · rw [hi₂]; simp
      · simp
    refine isClosedMorphism_of_isClosedImmersion B S hS
      (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS _ _ hsq.isOpenSubspace.1
        hsq.isAlgebraicSpace W.2) (hP _ _ hsq.isOpenSubspace.1 hsq.isAlgebraicSpace) _ ?_
    refine isClosedImmersion_mapDesc_of_isPullback hpb' g.hom ?_
    exact isClosedImmersion_lift_of_iso _ (isClosedImmersion_lift_swap _ hc) ε
      (by rw [hUwg, Iso.hom_inv_id_assoc]; rfl)
  · have : Mono i₁.hom := mono_of_isOpenImmersion B S hS _ hi₁
    have heq : pullback.mapDesc i₁.hom i₁.hom g.hom =
        pullback.fst i₁.hom i₁.hom ≫ pullback.diagonal (i₁.hom ≫ g.hom) := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.diagonal_fst, pullback.lift_fst, Category.comp_id]
      · rw [Category.assoc, pullback.diagonal_snd, pullback.lift_snd, Category.comp_id,
          Category.comp_id, fst_eq_snd_of_mono_eq]
    rw [heq]
    refine isClosedMorphism_of_isClosedImmersion B S hS
      (AlgebraicGeometry.isAlgebraicSpace_pullback B S hS _ _ hsq.isAlgebraicSpace
        hsq.isAlgebraicSpace W.2) (hP _ _ hsq.isAlgebraicSpace hsq.isAlgebraicSpace) _ ?_
    exact isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS _) hg₁

/-- **A space covered by an elementary distinguished square of finite type pieces is of finite
type.**  Let `(Uw ⊆ W, f : V ⟶ W)` be an elementary distinguished square and let `g : W ⟶ Y`
be a morphism to a quasi-compact and quasi-separated algebraic space.  If `Uw ⟶ Y` and
`V ⟶ Y` are of finite type then so is `g`.

Being locally of finite type is local on the source for the fppf topology (Stacks 06EW), and
`{Uw ⊆ W, V ⟶ W}` is an étale covering.  The space `W` is quasi-compact, being covered by the
quasi-compact `Uw` and `V`, and a morphism from a quasi-compact space to a quasi-separated one
is quasi-compact. -/
theorem isFiniteType_of_isElementaryDistinguishedSquare (hZ : B.Contains (⊤_ Scheme.{u}))
    {V W Y : AlgebraicSpaces B S hS} {Uw : Subfunctor W.obj} {f : V ⟶ W}
    (hsq : IsElementaryDistinguishedSquare B S hS W.property Uw f.hom) (g : W ⟶ Y)
    (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hU : IsFiniteType B S hS (Uw.ι ≫ g.hom)) (hV : IsFiniteType B S hS (f.hom ≫ g.hom)) :
    IsFiniteType B S hS g.hom := by
  have hcov := isEtaleCovering_of_isElementaryDistinguishedSquare B S hS W.2 Uw f.hom hsq
  let Q : Bool → AlgebraicSpaces B S hS := fun
    | false => ⟨Uw.toFunctor, hsq.isOpenSubspace.1⟩
    | true => V
  let q : ∀ j, Q j ⟶ W := fun
    | false => ObjectProperty.homMk Uw.ι
    | true => f
  have hft : ∀ j, IsFiniteType B S hS ((q j).hom ≫ g.hom) := fun
    | false => hU
    | true => hV
  have hQqc : ∀ j, IsQuasiCompactSpace B S hS (Q j).obj := fun j =>
    IsQuasiCompactSpace.of_iso B S hS ((hft j).2 Y.1 Y.2 hYqc (𝟙 Y.1))
      (asIso (pullback.snd (𝟙 Y.1) ((q j).hom ≫ g.hom)))
  have hsurj : (⋃ j, Set.range (pointsMap B S hS (Q j).obj (q j).hom)) = Set.univ := by
    refine Set.eq_univ_iff_forall.2 fun x => ?_
    obtain ⟨j, hx⟩ := Set.mem_iUnion.1 (Set.eq_univ_iff_forall.1 hcov.jointly_surjective x)
    exact Set.mem_iUnion.2 ⟨j, by cases j <;> exact hx⟩
  have hWqc : IsQuasiCompactSpace B S hS W.obj := by
    refine isQuasiCompactSpace_of_finite_jointly_surjective B S hS (fun j => (Q j).2) W.2
      (fun j => (q j).hom) ?_ hQqc
    exact hsurj
  refine ⟨?_, isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hWqc g.hom⟩
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => IsLocallyOfFiniteType B S hS k.hom
  have hR : Presieve.ofArrows Q q ∈ Topology.precoverage.{u, 0} .fppf B S hS W := by
    refine ⟨Bool, _, _, rfl, W.2, fun j => (Q j).2, ?_⟩
    have hf := isFppfCovering_of_isEtaleCovering B S hS hcov
    refine ⟨W.2, fun j => (Q j).2, fun j => ?_, fun j => ?_, ?_⟩
    · cases j
      · exact hf.flat false
      · exact hf.flat true
    · cases j
      · exact hf.locallyOfFinitePresentation false
      · exact hf.locallyOfFinitePresentation true
    · exact hsurj
  refine MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) hR ?_
  rintro T k ⟨j⟩
  exact (hft j).1

end AlgebraicGeometry.Space

end
