module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CoordinateAxes
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelationFromInvolution

/-!
# The coordinate-axes étale equivalence relation

Over a field, the disjoint union of the coordinate axes with their punctured complement maps
to the fibre square of the coordinate axes by the diagonal on the first summand and by the
graph of the coordinate-swap involution on the second. This is an étale equivalence relation
on the coordinate axes.

## Main definitions

* `AlgebraicGeometry.Space.EtaleRelation.axesOver` and
  `AlgebraicGeometry.Space.EtaleRelation.relationOver` are the coordinate axes and the
  two-component relation scheme, viewed as schemes over the ground field.
* `AlgebraicGeometry.Space.EtaleRelation.relationPreRelation` packages the map to the fibre
  square as a pre-relation of schemes over the ground field.

## Main results

* `AlgebraicGeometry.Space.EtaleRelation.isEtaleEquivalenceRelation` states that this
  pre-relation is an étale equivalence relation.

## Implementation notes

The relation is the one constructed on the coordinate axes, not an arbitrary relation on
that scheme, and the two projections are the specified maps from its two-component relation
scheme. Transitivity is produced by descending along the coproduct decomposition of the
relation scheme: the pullbacks of a morphism into a binary coproduct again form a binary
coproduct, by van Kampen descent in the finitary extensive category of schemes, so a
morphism out of such a pullback may be defined summand by summand. Étaleness of the two
projections is checked on each summand, where the projection is either an isomorphism or an
open immersion followed by the coordinate swap.

The equivalence-relation data are built first for the two bare maps of schemes and then
transported to the slice over the ground field, where the pre-relation lives.

## References

* [Stacks Project, Tag 0ENU](https://stacks.math.columbia.edu/tag/0ENU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedChangeOfRings

universe u

namespace AlgebraicGeometry.Space.EtaleRelation

/-- The pullbacks of a morphism into a binary coproduct of schemes along the two inclusions
form a binary coproduct. -/
alias splitCoproduct := AlgebraicGeometry.nonempty_isColimit_binaryCofan_pullback_fst

/-- Evaluation at the origin is unchanged by the coordinate swap. -/
private lemma origin_comp_swap (S : CoordinateAxesQuotientSetup.{u}) :
    (originRingMap S).comp (swapRingEquiv S).toRingEquiv.toRingHom =
      originRingMap S := by
  apply RingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  simp [originRingMap, swapRingEquiv, swapPolynomialEquiv, originPolynomialMap]

/-- The coordinate swap fixes the origin. -/
private lemma coordinateSwap_fixes_origin (S : CoordinateAxesQuotientSetup.{u}) :
    coordinateSwap S (origin S) = origin S := by
  apply PrimeSpectrum.ext
  change Ideal.comap ((swapRingEquiv S).toRingEquiv) (origin S).asIdeal =
    (origin S).asIdeal
  change Ideal.comap ((swapRingEquiv S).toRingEquiv.toRingHom)
      (RingHom.ker (originRingMap S)) = RingHom.ker (originRingMap S)
  ext a
  change (originRingMap S) ((swapRingEquiv S).toRingEquiv a) = 0 ↔
    (originRingMap S) a = 0
  have h := congrArg (fun f : NodalRing S.k →+* S.k => f a) (origin_comp_swap S)
  simpa [RingHom.comp_apply] using congrArg (fun x => x = (0 : S.k)) h

/-- The ring automorphism interchanging the two coordinates is an involution. -/
private lemma swapRing_symm_involutive (S : CoordinateAxesQuotientSetup.{u}) :
    (((swapRingEquiv S).toRingEquiv.symm.toRingHom).comp
      (swapRingEquiv S).toRingEquiv.symm.toRingHom) = RingHom.id _ := by
  apply RingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hp : (MvPolynomial.rename (fun x : Bool ↦ x)) p = p :=
    MvPolynomial.rename_id_apply p
  simp [swapRingEquiv, swapPolynomialEquiv, MvPolynomial.rename_rename,
    Function.comp_def, Equiv.swap_apply_self, hp]

/-- The coordinate swap is an involution. -/
private lemma coordinateSwap_comp_self (S : CoordinateAxesQuotientSetup.{u}) :
    coordinateSwap S ≫ coordinateSwap S = 𝟙 _ := by
  dsimp [coordinateSwap, coordinateSwapIso]
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_injective.eq_iff]
  exact CommRingCat.hom_ext (swapRing_symm_involutive S)

/-- The coordinate swap is an involution on points. -/
private lemma coordinateSwap_involutive (S : CoordinateAxesQuotientSetup.{u})
    (p : coordinateAxes S) : coordinateSwap S (coordinateSwap S p) = p := by
  have h := congrArg (fun f : coordinateAxes S ⟶ coordinateAxes S => f p)
    (coordinateSwap_comp_self S)
  simpa [Scheme.Hom.comp_apply] using h

/-- The coordinate swap preserves the complement of the origin. -/
private lemma coordinateSwap_ne_origin_of_ne_origin (S : CoordinateAxesQuotientSetup.{u})
    (p : coordinateAxes S) (hp : p ≠ origin S) :
    coordinateSwap S p ≠ origin S := by
  intro h
  have h' := congrArg (coordinateSwap S) h
  rw [coordinateSwap_involutive S, coordinateSwap_fixes_origin S] at h'
  exact hp h'

/-- The restriction of the coordinate swap to the punctured coordinate axes. -/
private def swapPunctured (S : CoordinateAxesQuotientSetup.{u}) :
    (↑(puncturedCoordinateAxes S) : Scheme) ⟶
      (↑(puncturedCoordinateAxes S) : Scheme) :=
  IsOpenImmersion.lift (puncturedCoordinateAxes S).ι
    ((puncturedCoordinateAxes S).ι ≫ coordinateSwap S) (by
      rintro y ⟨x, rfl⟩
      apply (Scheme.Hom.mem_opensRange (f := (puncturedCoordinateAxes S).ι)).2
      refine ⟨⟨coordinateSwap S ((puncturedCoordinateAxes S).ι x), ?_⟩, rfl⟩
      have hx : ((puncturedCoordinateAxes S).ι x : coordinateAxes S) ≠ origin S := by
        have hm : ((puncturedCoordinateAxes S).ι x : coordinateAxes S) ∈
            ({origin S}ᶜ : Set (coordinateAxes S)) := by
          rw [← coe_puncturedCoordinateAxes S]
          exact x.2
        simpa using hm
      change coordinateSwap S ((puncturedCoordinateAxes S).ι x) ∈
        (puncturedCoordinateAxes S : Set (coordinateAxes S))
      rw [coe_puncturedCoordinateAxes S]
      exact coordinateSwap_ne_origin_of_ne_origin S _ hx)

/-- The restricted coordinate swap is compatible with the open inclusion. -/
private lemma swapPunctured_comp_ι (S : CoordinateAxesQuotientSetup.{u}) :
    swapPunctured S ≫ (puncturedCoordinateAxes S).ι =
      (puncturedCoordinateAxes S).ι ≫ coordinateSwap S :=
  IsOpenImmersion.lift_fac _ _ _

/-- The two projections of the relation form an equivalence relation of schemes. -/
private theorem relation_maps_equivalence (S : CoordinateAxesQuotientSetup.{u}) :
    IsEquivalenceRelation (relationLeft S) (relationRight S) := by
  have : Mono (relationMap S) := relationMap_mono S
  let r : coordinateAxes S ⟶ relationScheme S := coprod.inl
  let s : relationScheme S ⟶ relationScheme S :=
    coprod.desc coprod.inl (swapPunctured S ≫ coprod.inr)
  let P := pullback (relationRight S) (relationLeft S)
  let a : P ⟶ relationScheme S := pullback.fst _ _
  let b : P ⟶ relationScheme S := pullback.snd _ _
  let c : PullbackCone (relationRight S) (relationLeft S) := pullback.cone _ _
  let hc : IsLimit c := pullback.isLimit _ _
  let t₀ : pullback a coprod.inl ⟶ relationScheme S :=
    pullback.fst a coprod.inl ≫ b
  let d := pullback a coprod.inr
  let dπ : d ⟶ P := pullback.fst a coprod.inr
  let dι : d ⟶ (↑(puncturedCoordinateAxes S) : Scheme) :=
    pullback.snd a coprod.inr
  let q := dπ ≫ b
  let e₀ := pullback q coprod.inl
  let e₁ := pullback q coprod.inr
  let c₀ : BinaryCofan e₀ e₁ :=
    BinaryCofan.mk (pullback.fst q coprod.inl) (pullback.fst q coprod.inr)
  let hc₀ : IsColimit c₀ := Classical.choice (splitCoproduct q)
  let u₀ : e₀ ⟶ relationScheme S :=
    pullback.fst q coprod.inl ≫ dι ≫ coprod.inr
  let u₁ : e₁ ⟶ relationScheme S :=
    pullback.fst q coprod.inr ≫ dι ≫ (puncturedCoordinateAxes S).ι ≫ coprod.inl
  let t₁ : d ⟶ relationScheme S :=
    hc₀.desc (BinaryCofan.mk u₀ u₁)
  have ht₁_fac₀ : pullback.fst q coprod.inl ≫ t₁ = u₀ :=
    BinaryCofan.IsColimit.inl_desc hc₀ u₀ u₁
  have ht₁_fac₁ : pullback.fst q coprod.inr ≫ t₁ = u₁ :=
    BinaryCofan.IsColimit.inr_desc hc₀ u₀ u₁
  let c₁ : BinaryCofan (pullback a coprod.inl) d :=
    BinaryCofan.mk (pullback.fst a coprod.inl) (pullback.fst a coprod.inr)
  let hc₁ : IsColimit c₁ := Classical.choice (splitCoproduct a)
  let t : P ⟶ relationScheme S :=
    hc₁.desc (BinaryCofan.mk t₀ t₁)
  have ht_fac₀ : pullback.fst a coprod.inl ≫ t = t₀ :=
    BinaryCofan.IsColimit.inl_desc hc₁ t₀ t₁
  have ht_fac₁ : pullback.fst a coprod.inr ≫ t = t₁ :=
    BinaryCofan.IsColimit.inr_desc hc₁ t₀ t₁
  have ht₀_left : t₀ ≫ relationLeft S =
      pullback.fst a coprod.inl ≫ a ≫ relationLeft S := by
    dsimp [t₀]
    calc
      pullback.fst a coprod.inl ≫ b ≫ relationLeft S =
          pullback.fst a coprod.inl ≫ a ≫ relationRight S :=
        (congrArg (fun f => pullback.fst a coprod.inl ≫ f)
          (pullback.condition : a ≫ relationRight S = b ≫ relationLeft S)).symm
      _ = pullback.snd a coprod.inl ≫ coprod.inl ≫ relationRight S := by
        simpa only [Category.assoc] using congrArg (fun f => f ≫ relationRight S)
          (pullback.condition : pullback.fst a coprod.inl ≫ a =
            pullback.snd a coprod.inl ≫ coprod.inl)
      _ = pullback.snd a coprod.inl := by
        simp [relationRight_inl']
      _ = pullback.snd a coprod.inl ≫ coprod.inl ≫ relationLeft S := by
        simp [relationLeft_inl']
      _ = pullback.fst a coprod.inl ≫ a ≫ relationLeft S := by
        simpa only [Category.assoc] using (congrArg (fun f => f ≫ relationLeft S)
          (pullback.condition : pullback.fst a coprod.inl ≫ a =
            pullback.snd a coprod.inl ≫ coprod.inl)).symm
  have ht₀_right : t₀ ≫ relationRight S =
      pullback.fst a coprod.inl ≫ b ≫ relationRight S :=
    rfl
  have hd_left : dπ ≫ a ≫ relationLeft S = dι ≫ (puncturedCoordinateAxes S).ι := by
    rw [← Category.assoc, pullback.condition, Category.assoc, relationLeft_inr']
  have hd_right : dπ ≫ a ≫ relationRight S =
      dι ≫ (puncturedCoordinateAxes S).ι ≫ coordinateSwap S := by
    rw [← Category.assoc, pullback.condition, Category.assoc, relationRight_inr']
  have hd_mid : dπ ≫ b ≫ relationLeft S =
      dι ≫ (puncturedCoordinateAxes S).ι ≫ coordinateSwap S :=
    (congrArg (fun f => dπ ≫ f)
      (pullback.condition : a ≫ relationRight S = b ≫ relationLeft S)).symm.trans hd_right
  have ht₁_left : t₁ ≫ relationLeft S = dπ ≫ a ≫ relationLeft S := by
    apply BinaryCofan.IsColimit.hom_ext hc₀
    · change (pullback.fst q coprod.inl ≫ t₁) ≫ relationLeft S =
        (pullback.fst q coprod.inl ≫ dπ ≫ a) ≫ relationLeft S
      rw [ht₁_fac₀]
      calc
        pullback.fst q coprod.inl ≫ dι ≫ coprod.inr ≫ relationLeft S =
            pullback.fst q coprod.inl ≫ dι ≫ (puncturedCoordinateAxes S).ι := by
          simp [relationLeft_inr']
        _ = pullback.fst q coprod.inl ≫ dπ ≫ a ≫ relationLeft S := by
          simpa only [Category.assoc] using congrArg
            (fun f => pullback.fst q coprod.inl ≫ f) hd_left.symm
    · change (pullback.fst q coprod.inr ≫ t₁) ≫ relationLeft S =
        (pullback.fst q coprod.inr ≫ dπ ≫ a) ≫ relationLeft S
      rw [ht₁_fac₁]
      calc
        pullback.fst q coprod.inr ≫ dι ≫ (puncturedCoordinateAxes S).ι ≫ coprod.inl ≫
            relationLeft S = pullback.fst q coprod.inr ≫ dι ≫
              (puncturedCoordinateAxes S).ι := by
          simp [relationLeft_inl']
        _ = pullback.fst q coprod.inr ≫ dπ ≫ a ≫ relationLeft S := by
          simpa only [Category.assoc] using congrArg
            (fun f => pullback.fst q coprod.inr ≫ f) hd_left.symm
  have ht₁_right : t₁ ≫ relationRight S = dπ ≫ b ≫ relationRight S := by
    apply BinaryCofan.IsColimit.hom_ext hc₀
    · change (pullback.fst q coprod.inl ≫ t₁) ≫ relationRight S =
        (pullback.fst q coprod.inl ≫ dπ ≫ b) ≫ relationRight S
      rw [ht₁_fac₀]
      let m := pullback.fst q coprod.inl
      let n := pullback.snd q coprod.inl
      have hq : m ≫ (dπ ≫ b) = n ≫ coprod.inl := by
        dsimp [m, n, q]
        exact pullback.condition
      change (m ≫ dι ≫ coprod.inr) ≫ relationRight S =
        (m ≫ dπ ≫ b) ≫ relationRight S
      calc
        (m ≫ dι ≫ coprod.inr) ≫ relationRight S =
            m ≫ dι ≫ (puncturedCoordinateAxes S).ι ≫ coordinateSwap S := by
          simp [relationRight_inr', Category.assoc]
        _ = m ≫ dπ ≫ b ≫ relationLeft S := by
          simpa only [Category.assoc] using congrArg (fun f => m ≫ f) hd_mid.symm
        _ = n ≫ coprod.inl ≫ relationLeft S := by
          simpa only [Category.assoc] using congrArg (fun f => f ≫ relationLeft S) hq
        _ = n := by simp [relationLeft_inl']
        _ = n ≫ coprod.inl ≫ relationRight S := by simp [relationRight_inl']
        _ = m ≫ dπ ≫ b ≫ relationRight S := by
          simpa only [Category.assoc] using
            (congrArg (fun f => f ≫ relationRight S) hq).symm
    · change (pullback.fst q coprod.inr ≫ t₁) ≫ relationRight S =
        (pullback.fst q coprod.inr ≫ dπ ≫ b) ≫ relationRight S
      rw [ht₁_fac₁]
      let m := pullback.fst q coprod.inr
      let n := pullback.snd q coprod.inr
      have hq : m ≫ (dπ ≫ b) = n ≫ coprod.inr := by
        dsimp [m, n, q]
        exact pullback.condition
      change (m ≫ dι ≫ (puncturedCoordinateAxes S).ι ≫ coprod.inl) ≫
          relationRight S = (m ≫ dπ ≫ b) ≫ relationRight S
      calc
        (m ≫ dι ≫ (puncturedCoordinateAxes S).ι ≫ coprod.inl) ≫ relationRight S =
            m ≫ dι ≫ (puncturedCoordinateAxes S).ι := by simp [relationRight_inl']
        _ = m ≫ dι ≫ (puncturedCoordinateAxes S).ι ≫
            coordinateSwap S ≫ coordinateSwap S := by
          simpa only [Category.assoc, Category.comp_id] using
            (congrArg (fun f => (m ≫ dι ≫ (puncturedCoordinateAxes S).ι) ≫ f)
              (coordinateSwap_comp_self S)).symm
        _ = m ≫ dπ ≫ b ≫ relationLeft S ≫ coordinateSwap S := by
          simpa only [Category.assoc] using congrArg (fun f => m ≫ f ≫ coordinateSwap S)
            hd_mid.symm
        _ = n ≫ coprod.inr ≫ relationLeft S ≫ coordinateSwap S := by
          simpa only [Category.assoc] using
            congrArg (fun f => f ≫ relationLeft S ≫ coordinateSwap S) hq
        _ = n ≫ (puncturedCoordinateAxes S).ι ≫ coordinateSwap S := by
          simpa only [Category.assoc] using congrArg
            (fun f => n ≫ f ≫ coordinateSwap S) (relationLeft_inr' S)
        _ = n ≫ coprod.inr ≫ relationRight S := by
          simpa only [Category.assoc] using congrArg (fun f => n ≫ f)
            (relationRight_inr' S).symm
        _ = m ≫ dπ ≫ b ≫ relationRight S := by
          simpa only [Category.assoc] using
            (congrArg (fun f => f ≫ relationRight S) hq).symm
  have ht_left : t ≫ relationLeft S = c.fst ≫ relationLeft S := by
    change t ≫ relationLeft S = a ≫ relationLeft S
    apply BinaryCofan.IsColimit.hom_ext hc₁
    · change (pullback.fst a coprod.inl ≫ t) ≫ relationLeft S =
        (pullback.fst a coprod.inl ≫ a) ≫ relationLeft S
      rw [ht_fac₀]
      exact ht₀_left
    · change (pullback.fst a coprod.inr ≫ t) ≫ relationLeft S =
        (pullback.fst a coprod.inr ≫ a) ≫ relationLeft S
      rw [ht_fac₁]
      exact ht₁_left
  have ht_right : t ≫ relationRight S = c.snd ≫ relationRight S := by
    change t ≫ relationRight S = b ≫ relationRight S
    apply BinaryCofan.IsColimit.hom_ext hc₁
    · change (pullback.fst a coprod.inl ≫ t) ≫ relationRight S =
        (pullback.fst a coprod.inl ≫ b) ≫ relationRight S
      rw [ht_fac₀]
    · change (pullback.fst a coprod.inr ≫ t) ≫ relationRight S =
        (pullback.fst a coprod.inr ≫ b) ≫ relationRight S
      rw [ht_fac₁]
      exact ht₁_right
  have hsym₁ : s ≫ relationLeft S = relationRight S := by
    apply coprod.hom_ext
    · dsimp [s]
      rw [← Category.assoc, coprod.inl_desc, relationLeft_inl', relationRight_inl']
    · dsimp [s]
      rw [← Category.assoc, coprod.inr_desc]
      change swapPunctured S ≫ ((coprod.inr : _ ⟶ relationScheme S) ≫ relationLeft S) =
        (coprod.inr : _ ⟶ relationScheme S) ≫ relationRight S
      rw [relationLeft_inr', swapPunctured_comp_ι, relationRight_inr']
  have hsym₂ : s ≫ relationRight S = relationLeft S := by
    apply coprod.hom_ext
    · dsimp [s]
      rw [← Category.assoc, coprod.inl_desc, relationRight_inl', relationLeft_inl']
    · dsimp [s]
      rw [← Category.assoc, coprod.inr_desc]
      change swapPunctured S ≫ ((coprod.inr : _ ⟶ relationScheme S) ≫ relationRight S) =
        (coprod.inr : _ ⟶ relationScheme S) ≫ relationLeft S
      rw [relationRight_inr']
      calc
        swapPunctured S ≫ ((puncturedCoordinateAxes S).ι ≫ coordinateSwap S) =
            (swapPunctured S ≫ (puncturedCoordinateAxes S).ι) ≫ coordinateSwap S :=
          (Category.assoc _ _ _).symm
        _ = ((puncturedCoordinateAxes S).ι ≫ coordinateSwap S) ≫ coordinateSwap S :=
          congrArg (fun f => f ≫ coordinateSwap S) (swapPunctured_comp_ι S)
        _ = (puncturedCoordinateAxes S).ι := by
          calc
            ((puncturedCoordinateAxes S).ι ≫ coordinateSwap S) ≫ coordinateSwap S =
                (puncturedCoordinateAxes S).ι ≫
                  (coordinateSwap S ≫ coordinateSwap S) := Category.assoc _ _ _
            _ = (puncturedCoordinateAxes S).ι := by
              rw [coordinateSwap_comp_self, Category.comp_id]
        _ = (coprod.inr : _ ⟶ relationScheme S) ≫ relationLeft S :=
          (relationLeft_inr' S).symm
  exact EquivalenceRelation.isEquivalenceRelation
    { right_cancellation := fun _ _ _ h₁ h₂ => (cancel_mono (relationMap S)).1 <| by
        apply pullback.hom_ext
        · simpa only [relationLeft, Scheme.Hom.comp_apply, Category.assoc] using h₁
        · simpa only [relationRight, Scheme.Hom.comp_apply, Category.assoc] using h₂
      r := r
      reflexivity₁ := by simpa [r] using relationLeft_inl' S
      reflexivity₂ := by simpa [r] using relationRight_inl' S
      s := s
      symmetry₁ := hsym₁
      symmetry₂ := hsym₂
      c := c
      isLimit := hc
      t := t
      transitivity₁ := ht_left
      transitivity₂ := ht_right }

/-- The coordinate axes as a scheme over the ground field. -/
abbrev axesOver (S : CoordinateAxesQuotientSetup.{u}) :
    Over (Spec (.of S.k)) := Over.mk (baseMap S)

/-- The two-component relation scheme over the ground field. -/
abbrev relationOver (S : CoordinateAxesQuotientSetup.{u}) :
    Over (Spec (.of S.k)) := Over.mk (relationLeft S ≫ baseMap S)

/-- The diagonal and twisted diagonal give a pre-relation on the coordinate axes. -/
def relationPreRelation (S : CoordinateAxesQuotientSetup.{u}) :
    Stacks.Groupoids.PreRelation (relationOver S) (axesOver S) :=
  prod.lift (Over.homMk (relationLeft S))
    (Over.homMk (relationRight S) (by
      dsimp [relationRight, relationLeft]
      rw [Category.assoc, Category.assoc, pullback.condition]))

/-- Both projections of the relation have the same composite with the structure map. -/
private lemma relationRight_comp_baseMap (S : CoordinateAxesQuotientSetup.{u}) :
    relationRight S ≫ baseMap S = relationLeft S ≫ baseMap S := by
  change relationMap S ≫ (pullback.snd _ _ ≫ baseMap S) =
    relationMap S ≫ (pullback.fst _ _ ≫ baseMap S)
  exact congrArg (fun f => relationMap S ≫ f) pullback.condition.symm

/-- The first projection as a morphism of schemes over the ground field. -/
private noncomputable def relationLeftOver (S : CoordinateAxesQuotientSetup.{u}) :
    relationOver S ⟶ axesOver S := Over.homMk (relationLeft S) (by rfl)

/-- The second projection as a morphism of schemes over the ground field. -/
private noncomputable def relationRightOver (S : CoordinateAxesQuotientSetup.{u}) :
    relationOver S ⟶ axesOver S := Over.homMk (relationRight S) (relationRight_comp_baseMap S)

/-- The target map of the pre-relation is the first projection. -/
private lemma relationPreRelation_target_eq (S : CoordinateAxesQuotientSetup.{u}) :
    (relationPreRelation S).target = relationLeftOver S := by
  ext
  simp [Stacks.Groupoids.PreRelation.target, relationPreRelation, relationLeftOver,
    relationLeft]

/-- The source map of the pre-relation is the second projection. -/
private lemma relationPreRelation_source_eq (S : CoordinateAxesQuotientSetup.{u}) :
    (relationPreRelation S).source = relationRightOver S := by
  ext
  simp [Stacks.Groupoids.PreRelation.source, relationPreRelation, relationRightOver,
    relationRight]

/-- The two projections form an equivalence relation in the slice over the ground field. -/
private theorem relationOver_maps_equivalence (S : CoordinateAxesQuotientSetup.{u}) :
    IsEquivalenceRelation (relationLeftOver S) (relationRightOver S) := by
  let e : EquivalenceRelation (relationLeft S) (relationRight S) :=
    Classical.choice (relation_maps_equivalence S).nonempty_equivalenceRelation
  let p₁ := relationLeftOver S
  let p₂ := relationRightOver S
  let c : PullbackCone p₂ p₁ := pullback.cone p₂ p₁
  let hc : IsLimit c := pullback.isLimit p₂ p₁
  have hcond : c.fst.left ≫ relationRight S = c.snd.left ≫ relationLeft S := by
    have hh := congrArg Over.Hom.left (PullbackCone.condition c)
    simpa [p₁, p₂, relationLeftOver, relationRightOver, Category.assoc] using hh
  let q : c.pt.left ⟶ e.c.pt :=
    PullbackCone.IsLimit.lift e.isLimit c.fst.left c.snd.left hcond
  have hq₁ : q ≫ e.c.fst = c.fst.left :=
    PullbackCone.IsLimit.lift_fst e.isLimit c.fst.left c.snd.left hcond
  have hq₂ : q ≫ e.c.snd = c.snd.left :=
    PullbackCone.IsLimit.lift_snd e.isLimit c.fst.left c.snd.left hcond
  have ht₁ : q ≫ e.t ≫ relationLeft S = c.fst.left ≫ relationLeft S := by
    rw [e.transitivity₁, ← Category.assoc, hq₁]
  have ht₂ : q ≫ e.t ≫ relationRight S = c.snd.left ≫ relationRight S := by
    rw [e.transitivity₂, ← Category.assoc, hq₂]
  have htOver : q ≫ e.t ≫ (relationLeft S ≫ baseMap S) = c.pt.hom := by
    rw [← Category.assoc e.t, ← Category.assoc, ht₁, Category.assoc]
    exact Over.w c.fst
  exact EquivalenceRelation.isEquivalenceRelation
    { right_cancellation := fun _ _ _ h₁ h₂ => by
        ext
        exact e.right_cancellation _ _
          (by simpa [p₁, relationLeftOver, Category.assoc] using
            congrArg Over.Hom.left h₁)
          (by simpa [p₂, relationRightOver, Category.assoc] using
            congrArg Over.Hom.left h₂)
      r := Over.homMk e.r (by
        change e.r ≫ (relationLeft S ≫ baseMap S) = baseMap S
        rw [← Category.assoc, e.reflexivity₁, Category.id_comp])
      reflexivity₁ := by
        ext
        simp [relationLeftOver]
      reflexivity₂ := by
        ext
        simp [relationRightOver]
      s := Over.homMk e.s (by
        change e.s ≫ (relationLeft S ≫ baseMap S) = relationLeft S ≫ baseMap S
        rw [← Category.assoc, e.symmetry₁]
        exact relationRight_comp_baseMap S)
      symmetry₁ := by
        ext
        simpa [p₁, p₂, relationLeftOver, relationRightOver] using e.symmetry₁
      symmetry₂ := by
        ext
        simpa [p₁, p₂, relationLeftOver, relationRightOver] using e.symmetry₂
      c := c
      isLimit := hc
      t := Over.homMk (q ≫ e.t) htOver
      transitivity₁ := by
        ext
        change (q ≫ e.t) ≫ relationLeft S = c.fst.left ≫ relationLeft S
        exact ht₁
      transitivity₂ := by
        ext
        change (q ≫ e.t) ≫ relationRight S = c.snd.left ≫ relationRight S
        exact ht₂ }

/-- A morphism out of a binary coproduct is étale when both components are; this is
`AlgebraicGeometry.etale_coprod`. -/
private alias etale_coprod := AlgebraicGeometry.etale_coprod

/-- A projection of the relation is étale when its restrictions to both summands are. -/
private lemma etale_relationMap_comp (S : CoordinateAxesQuotientSetup.{u})
    (g : pullback (baseMap S) (baseMap S) ⟶ coordinateAxes S)
    (h₁ : Etale (diagonal S ≫ g))
    (h₂ : Etale ((puncturedCoordinateAxes S).ι ≫ twistedDiagonal S ≫ g)) :
    Etale (relationMap S ≫ g) := by
  dsimp only [relationMap]
  rw [coprod.desc_comp]
  exact etale_coprod _ _ h₁ (by simpa using h₂)

/-- The specified relation is an étale equivalence relation on the coordinate axes. -/
@[stacks 0ENU "etale_relation"]
theorem isEtaleEquivalenceRelation (S : CoordinateAxesQuotientSetup.{u}) :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (relationPreRelation S) := by
  have : Etale (relationLeft S) := by
    refine etale_relationMap_comp S _ ?_ ?_
    · have h : diagonal S ≫ pullback.fst (baseMap S) (baseMap S) = 𝟙 _ := by
        simp [diagonal]
      rw [h]
      infer_instance
    · rw [twistedDiagonal, pullback.lift_fst, Category.comp_id]
      infer_instance
  have : Etale (relationRight S) := by
    refine etale_relationMap_comp S _ ?_ ?_
    · have h : diagonal S ≫ pullback.snd (baseMap S) (baseMap S) = 𝟙 _ := by
        simp [diagonal]
      rw [h]
      infer_instance
    · rw [twistedDiagonal, pullback.lift_snd]
      infer_instance
  have : IsEquivalenceRelation (relationPreRelation S).target
      (relationPreRelation S).source := by
    rw [relationPreRelation_target_eq, relationPreRelation_source_eq]
    exact relationOver_maps_equivalence S
  refine { etale_source := ?_, etale_target := ?_ }
  · rw [relationPreRelation_source_eq]
    simpa [relationRightOver] using (inferInstance : Etale (relationRight S))
  · rw [relationPreRelation_target_eq]
    simpa [relationLeftOver] using (inferInstance : Etale (relationLeft S))

attribute [instance] isEtaleEquivalenceRelation

end AlgebraicGeometry.Space.EtaleRelation

end
