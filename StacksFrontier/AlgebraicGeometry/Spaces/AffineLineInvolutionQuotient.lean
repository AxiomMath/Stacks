module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolution
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineFlatChartDescent
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CoordinateAxesEtaleRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.Extension
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
import StacksFrontier.AlgebraicGeometry.Groupoids.EquivalenceRelation.Slice

/-!
# The involution relation on the affine line is an étale equivalence relation

Over a field in which two is invertible, the relation `R = Δ ⨿ Γ` on the affine line — the
diagonal together with the graph of negation on the punctured line — is an equivalence
relation, and both its projections are étale. This is what makes the quotient
`AlgebraicGeometry.AffineLineInvolution.involutionQuotient` of Stacks 02Z1 an algebraic
space.

## Main results

* `AlgebraicGeometry.AffineLineInvolution.isEtaleEquivalenceRelation`: the involution
  relation is an étale equivalence relation when two is nonzero in the ground field.

## Implementation notes

The relation scheme is a coproduct taken in the slice category over `Spec k`, while the
equivalence-relation argument is carried out on the coproduct of the underlying schemes;
`AlgebraicGeometry.AffineLineInvolution.overCoprodIso` is the comparison isomorphism between
the two, and `AlgebraicGeometry.coprodComparison_comp_left_coprod_desc` identifies the two
projections across it. The equivalence relation is therefore first established for the two
maps `relationLeftSum` and `relationRightSum` out of the coproduct of schemes, and then
transported to the slice by `isEquivalenceRelation_over_of_iso`.

Injectivity of `R ⟶ U ×_k U` is where the characteristic enters: the two summands are
disjoint precisely because a punctured point equal to its own negative would force `2` to
vanish. Disjointness is turned into a monomorphism statement by
`mono_coprod_desc_of_disjoint`, whose proof tests a pair of morphisms out of a scheme on the
two parts of the induced decomposition of the source — the decomposition supplied by
`Space.EtaleRelation.splitCoproduct`, which is the van Kampen property of the coproduct of schemes.

Symmetry of the relation is negation on the punctured line, which is the lift of negation
through the open immersion, and transitivity is assembled summand by summand from the same
decomposition.

## References

* [Stacks Project, Tag 02Z1](https://stacks.math.columbia.edu/tag/02Z1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The comparison isomorphism between the coproduct of the underlying schemes of two objects
of a slice category and the underlying scheme of their coproduct in the slice. -/
noncomputable def overCoprodIso {S : Scheme.{u}} (A B : Over S) :
    A.left ⨿ B.left ≅ (A ⨿ B).left :=
  haveI : IsIso (coprodComparison (Over.forget S) A B) :=
    (PreservesColimitPair.iso (Over.forget S) A B).isIso_hom
  asIso (coprodComparison (Over.forget S) A B)

@[simp]
theorem overCoprodIso_hom {S : Scheme.{u}} (A B : Over S) :
    (overCoprodIso A B).hom = coprodComparison (Over.forget S) A B := rfl

namespace AffineLineInvolution

variable (k : Type u) [Field k]

/-- Negating the coordinate twice is the identity, on underlying schemes. -/
private lemma affineLineNeg_left_comp_left :
    (affineLineNeg k).left ≫ (affineLineNeg k).left = 𝟙 (affineLine k).left := by
  rw [← Over.comp_left, affineLineNeg_comp_affineLineNeg, Over.id_left]

private lemma affineLineNeg_preimage_puncture :
    (affineLineNeg k).left ⁻¹ᵁ puncturedAffineLineOpen k = puncturedAffineLineOpen k := by
  rw [Scheme.preimage_basicOpen_top]
  change (affineLine k).left.basicOpen
      ((AffineSpace.homOfVector (affineLine k).hom
        (fun _ : PUnit.{u + 1} => -AffineSpace.coord (Spec (.of k)) PUnit.unit)).appTop
        (AffineSpace.coord (Spec (.of k)) PUnit.unit)) = _
  rw [AffineSpace.homOfVector_appTop_coord]
  change (AffineSpace PUnit.{u + 1} (Spec (.of k))).basicOpen
      (-(AffineSpace.coord (Spec (.of k)) PUnit.unit)) = _
  rw [show -(AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      (-1 : Γ(AffineSpace PUnit.{u + 1} (Spec (.of k)), ⊤)) *
        AffineSpace.coord (Spec (.of k)) PUnit.unit by ring,
    Scheme.basicOpen_mul]
  rw [Scheme.basicOpen_of_isUnit (X := AffineSpace PUnit.{u + 1} (Spec (.of k)))
    (U := ⊤) (isUnit_neg_one : IsUnit
      (-1 : Γ(AffineSpace PUnit.{u + 1} (Spec (.of k)), ⊤)))]
  simp only [top_inf_eq]
  rfl

private noncomputable def puncturedAffineLineNeg :
    (puncturedAffineLine k).left ⟶ (puncturedAffineLine k).left := by
  apply IsOpenImmersion.lift (puncturedAffineLineOpen k).ι
    ((puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left)
  intro y hy
  rcases hy with ⟨x, rfl⟩
  refine ⟨⟨(affineLineNeg k).left ((puncturedAffineLineOpen k).ι x), ?_⟩, rfl⟩
  change (puncturedAffineLineOpen k).ι x ∈
    (affineLineNeg k).left ⁻¹ᵁ puncturedAffineLineOpen k
  rw [affineLineNeg_preimage_puncture]
  exact x.2

private lemma puncturedAffineLineNeg_fac :
    puncturedAffineLineNeg k ≫ (puncturedAffineLineOpen k).ι =
      (puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left :=
  IsOpenImmersion.lift_fac _ _ _

private noncomputable abbrev relationSum (k : Type u) [Field k] :=
  (affineLine k).left ⨿ (puncturedAffineLine k).left

private noncomputable def relationLeftSum (k : Type u) [Field k] :
    relationSum k ⟶ (affineLine k).left :=
  coprod.desc (𝟙 (affineLine k).left) (puncturedAffineLineInclusion k).left

private noncomputable def relationRightSum (k : Type u) [Field k] :
    relationSum k ⟶ (affineLine k).left :=
  coprod.desc (𝟙 (affineLine k).left)
    ((puncturedAffineLineInclusion k).left ≫ (affineLineNeg k).left)

private noncomputable def relationMapSum (k : Type u) [Field k] :
    relationSum k ⟶ (affineLine k).left ⨯ (affineLine k).left :=
  prod.lift (relationLeftSum k) (relationRightSum k)

private lemma relationLeftSum_inl (k : Type u) [Field k] :
    (coprod.inl : (affineLine k).left ⟶ relationSum k) ≫ relationLeftSum k =
      𝟙 (affineLine k).left := by
  change coprod.inl ≫ coprod.desc (𝟙 (affineLine k).left)
    (puncturedAffineLineInclusion k).left = 𝟙 _
  exact coprod.inl_desc _ _

private lemma relationRightSum_inl (k : Type u) [Field k] :
    (coprod.inl : (affineLine k).left ⟶ relationSum k) ≫ relationRightSum k =
      𝟙 (affineLine k).left := by
  change coprod.inl ≫ coprod.desc (𝟙 (affineLine k).left)
    ((puncturedAffineLineInclusion k).left ≫ (affineLineNeg k).left) = 𝟙 _
  exact coprod.inl_desc _ _

private lemma relationLeftSum_inr (k : Type u) [Field k] :
    (coprod.inr : (puncturedAffineLine k).left ⟶ relationSum k) ≫ relationLeftSum k =
      (puncturedAffineLineOpen k).ι := by
  change coprod.inr ≫ coprod.desc (𝟙 (affineLine k).left)
    (puncturedAffineLineInclusion k).left = _
  rw [coprod.inr_desc]
  rfl

private lemma relationRightSum_inr (k : Type u) [Field k] :
    (coprod.inr : (puncturedAffineLine k).left ⟶ relationSum k) ≫ relationRightSum k =
      (puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left := by
  change coprod.inr ≫ coprod.desc (𝟙 (affineLine k).left)
    ((puncturedAffineLineInclusion k).left ≫ (affineLineNeg k).left) = _
  rw [coprod.inr_desc]
  rfl

/-- Two maps out of `X` agree if they agree on both pullbacks of a map `X ⟶ A ⨿ B` along the
coproduct inclusions. -/
private lemma hom_ext_of_pullback_coproduct {X A B Y : Scheme.{u}} (q : X ⟶ A ⨿ B)
    (f g : X ⟶ Y) (hl : pullback.fst q coprod.inl ≫ f = pullback.fst q coprod.inl ≫ g)
    (hr : pullback.fst q coprod.inr ≫ f = pullback.fst q coprod.inr ≫ g) : f = g := by
  apply (Classical.choice (Space.EtaleRelation.splitCoproduct q)).hom_ext
  rintro ⟨j⟩
  cases j with
  | left => exact hl
  | right => exact hr

private lemma hom_ext_of_coproduct_pullbacks {X A B Y : Scheme.{u}}
    (q : X ⟶ A ⨿ B) (f g : X ⟶ Y)
    (hl : ∀ {T : Scheme.{u}} (a : T ⟶ X) (b : T ⟶ A),
      a ≫ q = b ≫ coprod.inl → a ≫ f = a ≫ g)
    (hr : ∀ {T : Scheme.{u}} (a : T ⟶ X) (b : T ⟶ B),
      a ≫ q = b ≫ coprod.inr → a ≫ f = a ≫ g) : f = g :=
  hom_ext_of_pullback_coproduct q f g (hl _ _ pullback.condition) (hr _ _ pullback.condition)

private lemma mono_coprod_desc_of_disjoint {A B Y : Scheme.{u}}
    (f : A ⟶ Y) (g : B ⟶ Y) [Mono f] [Mono g]
    (hd : ∀ {T : Scheme.{u}} (a : T ⟶ A) (b : T ⟶ B),
      a ≫ f = b ≫ g → IsEmpty T) : Mono (coprod.desc f g) := by
  constructor
  intro X a b h
  apply hom_ext_of_coproduct_pullbacks a a b
  · intro T i x hi
    apply hom_ext_of_coproduct_pullbacks (i ≫ b) (i ≫ a) (i ≫ b)
    · intro T' j y hj
      have hh := congrArg (fun v => j ≫ i ≫ v) h
      have he : (j ≫ x) ≫ f = y ≫ f := by
        simpa only [Category.assoc, reassoc_of% hi, reassoc_of% hj,
          coprod.inl_desc, Category.comp_id] using hh
      calc
        j ≫ i ≫ a = (j ≫ x) ≫ coprod.inl := by rw [hi, Category.assoc]
        _ = y ≫ coprod.inl := congrArg (fun v => v ≫ coprod.inl) ((cancel_mono f).1 he)
        _ = j ≫ i ≫ b := hj.symm
    · intro T' j y hj
      have hh := congrArg (fun v => j ≫ i ≫ v) h
      have he : (j ≫ x) ≫ f = y ≫ g := by
        simpa only [Category.assoc, reassoc_of% hi, reassoc_of% hj,
          coprod.inl_desc, coprod.inr_desc] using hh
      have := hd (j ≫ x) y he
      exact isInitialOfIsEmpty.hom_ext _ _
  · intro T i x hi
    apply hom_ext_of_coproduct_pullbacks (i ≫ b) (i ≫ a) (i ≫ b)
    · intro T' j y hj
      have hh := congrArg (fun v => j ≫ i ≫ v) h
      have he : y ≫ f = (j ≫ x) ≫ g := by
        symm
        simpa only [Category.assoc, reassoc_of% hi, reassoc_of% hj,
          coprod.inl_desc, coprod.inr_desc] using hh
      have := hd y (j ≫ x) he
      exact isInitialOfIsEmpty.hom_ext _ _
    · intro T' j y hj
      have hh := congrArg (fun v => j ≫ i ≫ v) h
      have he : (j ≫ x) ≫ g = y ≫ g := by
        simpa only [Category.assoc, reassoc_of% hi, reassoc_of% hj,
          coprod.inl_desc, coprod.inr_desc] using hh
      calc
        j ≫ i ≫ a = (j ≫ x) ≫ coprod.inr := by rw [hi, Category.assoc]
        _ = y ≫ coprod.inr := congrArg (fun v => v ≫ coprod.inr) ((cancel_mono g).1 he)
        _ = j ≫ i ≫ b := hj.symm

private lemma isEmpty_of_punctured_fixed [NeZero (2 : k)] {X : Scheme.{u}}
    (f : X ⟶ (puncturedAffineLine k).left)
    (h : f ≫ (puncturedAffineLineOpen k).ι =
      f ≫ (puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left) : IsEmpty X := by
  let a := f ≫ (puncturedAffineLineOpen k).ι
  let z := AffineSpace.coord (Spec (.of k)) (PUnit.unit : PUnit.{u + 1})
  have hz : a.appTop z = -a.appTop z := by
    have hh := congrArg (fun v : X ⟶ (affineLine k).left => v.appTop z) h
    change a.appTop z = a.appTop ((affineLineNeg k).left.appTop z) at hh
    simpa [affineLineNeg, z] using hh
  let φ : k →+* Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (a ≫ (affineLine k).hom).appTop).hom
  have htwo : IsUnit (2 : Γ(X, ⊤)) := by
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (NeZero.ne (2 : k))).map φ
  have hz0 : a.appTop z = 0 := by
    apply htwo.mul_left_cancel
    rw [mul_zero, two_mul]
    exact eq_neg_iff_add_eq_zero.mp hz
  constructor
  intro x
  have hx : x ∈ a ⁻¹ᵁ puncturedAffineLineOpen k := (f x).2
  rw [Scheme.preimage_basicOpen_top, hz0, Scheme.basicOpen_zero] at hx
  exact hx

private lemma relationMap_mono (k : Type u) [Field k] [NeZero (2 : k)] :
    Mono (relationMapSum k) := by
  let i := (puncturedAffineLineOpen k).ι
  let n := (affineLineNeg k).left
  let d : (affineLine k).left ⟶ (affineLine k).left ⨯ (affineLine k).left :=
    prod.lift (𝟙 _) (𝟙 _)
  let v : (puncturedAffineLine k).left ⟶
      (affineLine k).left ⨯ (affineLine k).left := prod.lift i (i ≫ n)
  have hd : d ≫ prod.fst = 𝟙 _ := by simp [d]
  have hv : v ≫ prod.fst = i := by simp [v]
  have : Mono (d ≫ prod.fst) := by rw [hd]; infer_instance
  have : Mono d := mono_of_mono d prod.fst
  have : Mono (v ≫ prod.fst) := by rw [hv]; dsimp [i]; infer_instance
  have : Mono v := mono_of_mono v prod.fst
  have hm : relationMapSum k = coprod.desc d v := by
    apply coprod.hom_ext <;> apply prod.hom_ext <;>
      simp [relationMapSum, relationLeftSum, relationRightSum, d, v, i, n,
        puncturedAffineLineInclusion]
  rw [hm]
  apply mono_coprod_desc_of_disjoint
  intro T a b hab
  have h₁ := congrArg (fun f => f ≫ prod.fst) hab
  have h₂ := congrArg (fun f => f ≫ prod.snd) hab
  simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
    Category.comp_id, d, v] at h₁ h₂
  exact isEmpty_of_punctured_fixed k b (h₁.symm.trans h₂)

private theorem involution_relation_maps_equivalence (k : Type u) [Field k] [NeZero (2 : k)] :
    IsEquivalenceRelation (relationLeftSum k) (relationRightSum k) := by
  let relationLeft := relationLeftSum k
  let relationRight := relationRightSum k
  have hjm : JointlyMono₂ relationLeft relationRight := by
    have := relationMap_mono k
    constructor
    intro T f g h₁ h₂
    apply (cancel_mono (relationMapSum k)).1
    apply prod.hom_ext
    · simpa [Category.assoc, relationMapSum] using h₁
    · simpa [Category.assoc, relationMapSum] using h₂
  let r : (affineLine k).left ⟶ relationSum k :=
    coprod.inl
  let s : relationSum k ⟶ relationSum k :=
    coprod.desc coprod.inl (puncturedAffineLineNeg k ≫ coprod.inr)
  let P := pullback (relationRight) (relationLeft)
  let a : P ⟶ relationSum k := pullback.fst _ _
  let b : P ⟶ relationSum k := pullback.snd _ _
  let c : PullbackCone (relationRight) (relationLeft) := pullback.cone _ _
  let hc : IsLimit c := pullback.isLimit _ _
  let t₀ : pullback a coprod.inl ⟶ relationSum k :=
    pullback.fst a coprod.inl ≫ b
  let d := pullback a coprod.inr
  let dπ : d ⟶ P := pullback.fst a coprod.inr
  let dι : d ⟶ (↑((puncturedAffineLine k).left) : Scheme) :=
    pullback.snd a coprod.inr
  let q := dπ ≫ b
  let e₀ := pullback q coprod.inl
  let e₁ := pullback q coprod.inr
  let c₀ : BinaryCofan e₀ e₁ :=
    BinaryCofan.mk (pullback.fst q coprod.inl) (pullback.fst q coprod.inr)
  let hc₀ : IsColimit c₀ := Classical.choice (Space.EtaleRelation.splitCoproduct q)
  let u₀ : e₀ ⟶ relationSum k :=
    pullback.fst q coprod.inl ≫ dι ≫ coprod.inr
  let u₁ : e₁ ⟶ relationSum k :=
    pullback.fst q coprod.inr ≫ dι ≫ (puncturedAffineLineOpen k).ι ≫ coprod.inl
  let t₁ : d ⟶ relationSum k :=
    hc₀.desc (BinaryCofan.mk u₀ u₁)
  have ht₁_fac₀ : pullback.fst q coprod.inl ≫ t₁ = pullback.fst q coprod.inl ≫ dι ≫ coprod.inr :=
    BinaryCofan.IsColimit.inl_desc hc₀ u₀ u₁
  have ht₁_fac₁ : pullback.fst q coprod.inr ≫ t₁ =
      pullback.fst q coprod.inr ≫ dι ≫ (puncturedAffineLineOpen k).ι ≫ coprod.inl :=
    BinaryCofan.IsColimit.inr_desc hc₀ u₀ u₁
  let c₁ : BinaryCofan (pullback a coprod.inl) d :=
    BinaryCofan.mk (pullback.fst a coprod.inl) (pullback.fst a coprod.inr)
  let hc₁ : IsColimit c₁ := Classical.choice (Space.EtaleRelation.splitCoproduct a)
  let t : P ⟶ relationSum k :=
    hc₁.desc (BinaryCofan.mk t₀ t₁)
  have ht_fac₀ : pullback.fst a coprod.inl ≫ t = pullback.fst a coprod.inl ≫ b :=
    BinaryCofan.IsColimit.inl_desc hc₁ t₀ t₁
  have ht_fac₁ : pullback.fst a coprod.inr ≫ t = t₁ := BinaryCofan.IsColimit.inr_desc hc₁ t₀ t₁
  have lInl : (coprod.inl : (affineLine k).left ⟶ relationSum k) ≫ relationLeft = 𝟙 _ :=
    relationLeftSum_inl k
  have rInl : (coprod.inl : (affineLine k).left ⟶ relationSum k) ≫ relationRight = 𝟙 _ :=
    relationRightSum_inl k
  have lInr : (coprod.inr : (puncturedAffineLine k).left ⟶ relationSum k) ≫ relationLeft =
      (puncturedAffineLineOpen k).ι := relationLeftSum_inr k
  have rInr : (coprod.inr : (puncturedAffineLine k).left ⟶ relationSum k) ≫ relationRight =
      (puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left := relationRightSum_inr k
  have hab : a ≫ relationRight = b ≫ relationLeft := pullback.condition
  have hI : pullback.fst a coprod.inl ≫ a = pullback.snd a coprod.inl ≫ coprod.inl :=
    pullback.condition
  have ht₀_left : pullback.fst a coprod.inl ≫ b ≫ relationLeft =
      pullback.fst a coprod.inl ≫ a ≫ relationLeft := by
    simp only [← hab, reassoc_of% hI, rInl, lInl]
  have hd_left : dπ ≫ a ≫ relationLeft = dι ≫ (puncturedAffineLineOpen k).ι := by
    rw [← Category.assoc, pullback.condition, Category.assoc, lInr]
  have hd_mid : dπ ≫ b ≫ relationLeft =
      dι ≫ (puncturedAffineLineOpen k).ι ≫ (affineLineNeg k).left := by
    rw [← hab, ← Category.assoc, pullback.condition, Category.assoc, rInr]
  have ht₁_left : t₁ ≫ relationLeft = dπ ≫ a ≫ relationLeft := by
    refine hom_ext_of_pullback_coproduct q _ _ ?_ ?_
    · simp only [reassoc_of% ht₁_fac₀, lInr, hd_left]
    · simp only [reassoc_of% ht₁_fac₁, lInl, hd_left, Category.comp_id]
  have ht₁_right : t₁ ≫ relationRight = dπ ≫ b ≫ relationRight := by
    refine hom_ext_of_pullback_coproduct q _ _ ?_ ?_
    · have hq : pullback.fst q coprod.inl ≫ dπ ≫ b = pullback.snd q coprod.inl ≫ coprod.inl :=
        pullback.condition
      simp only [reassoc_of% ht₁_fac₀, rInr, ← hd_mid, reassoc_of% hq, lInl,
        rInl, Category.comp_id]
    · have hq : pullback.fst q coprod.inr ≫ dπ ≫ b = pullback.snd q coprod.inr ≫ coprod.inr :=
        pullback.condition
      have h2 : pullback.snd q coprod.inr ≫ (puncturedAffineLineOpen k).ι =
          pullback.fst q coprod.inr ≫ dι ≫ (puncturedAffineLineOpen k).ι ≫
            (affineLineNeg k).left := by
        conv_lhs => rw [← lInr]
        rw [← reassoc_of% hq, hd_mid]
      simp only [reassoc_of% ht₁_fac₁, rInl, Category.comp_id,
        reassoc_of% hq, rInr, reassoc_of% h2, affineLineNeg_left_comp_left]
  have ht_left : t ≫ relationLeft = a ≫ relationLeft := by
    refine hom_ext_of_pullback_coproduct a _ _ ?_ ?_
    · rw [reassoc_of% ht_fac₀, ht₀_left]
    · rw [reassoc_of% ht_fac₁, ht₁_left]
  have ht_right : t ≫ relationRight = b ≫ relationRight := by
    refine hom_ext_of_pullback_coproduct a _ _ ?_ ?_
    · simp only [reassoc_of% ht_fac₀]
    · rw [reassoc_of% ht_fac₁, ht₁_right]
  have hsym₁ : s ≫ relationLeft = relationRight := by
    apply coprod.hom_ext
    · simp only [s, coprod.inl_desc_assoc, lInl, rInl]
    · simp only [s, coprod.inr_desc_assoc, Category.assoc, lInr, rInr,
        puncturedAffineLineNeg_fac]
  have hsym₂ : s ≫ relationRight = relationLeft := by
    apply coprod.hom_ext
    · simp only [s, coprod.inl_desc_assoc, lInl, rInl]
    · simp only [s, coprod.inr_desc_assoc, Category.assoc, lInr, rInr,
        reassoc_of% puncturedAffineLineNeg_fac k, affineLineNeg_left_comp_left,
        Category.comp_id]
  exact EquivalenceRelation.isEquivalenceRelation
    { right_cancellation := hjm.right_cancellation
      r := r
      reflexivity₁ := by simpa [r] using relationLeftSum_inl k
      reflexivity₂ := by simpa [r] using relationRightSum_inl k
      s := s
      symmetry₁ := hsym₁
      symmetry₂ := hsym₂
      c := c
      isLimit := hc
      t := t
      transitivity₁ := ht_left
      transitivity₂ := ht_right }

private alias equivalence_on_hom := Stacks.Groupoids.equivalence_of_equivalenceRelation_hom

private lemma isEquivalenceRelation_over_of_iso {S : Scheme.{u}} {R U : Over S}
    (j : Stacks.Groupoids.PreRelation R U) {R' : Scheme.{u}} (i : R' ≅ R.left)
    (p q : R' ⟶ U.left) (hp : i.hom ≫ j.target.left = p)
    (hq : i.hom ≫ j.source.left = q) (h : IsEquivalenceRelation p q) :
    IsEquivalenceRelation j.target j.source := by
  obtain ⟨e⟩ := h.nonempty_equivalenceRelation
  have hl {T : Over S} (f : T ⟶ R) :
      f.left ≫ i.inv ≫ p = (f ≫ j.target).left := by
    rw [← hp]
    simp
  have hr {T : Over S} (f : T ⟶ R) :
      f.left ≫ i.inv ≫ q = (f ≫ j.source).left := by
    rw [← hq]
    simp
  apply (Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation j).mpr
  constructor
  · constructor
    intro T f g hfg
    apply Over.OverMorphism.ext
    apply (cancel_mono i.inv).mp
    apply e.right_cancellation
    · simp only [Category.assoc, hl]
      exact congrArg Over.Hom.left
        (show f ≫ j.target = g ≫ j.target by
          simpa [Stacks.Groupoids.PreRelation.target, Category.assoc] using
            congrArg (fun v => v ≫ prod.fst) hfg)
    · simp only [Category.assoc, hr]
      exact congrArg Over.Hom.left
        (show f ≫ j.source = g ≫ j.source by
          simpa [Stacks.Groupoids.PreRelation.source, Category.assoc] using
            congrArg (fun v => v ≫ prod.snd) hfg)
  · intro T
    have hrel (x y : T ⟶ U) : j.Rel x y ↔
        ∃ r : T.left ⟶ R', r ≫ p = x.left ∧ r ≫ q = y.left := by
      constructor
      · rintro ⟨r, h₁, h₂⟩
        refine ⟨r.left ≫ i.inv, ?_, ?_⟩
        · simpa only [Category.assoc, hl] using congrArg Over.Hom.left h₁
        · simpa only [Category.assoc, hr] using congrArg Over.Hom.left h₂
      · rintro ⟨r, h₁, h₂⟩
        have ht : (r ≫ i.hom) ≫ j.target.left = x.left := by
          simpa only [Category.assoc, hp] using h₁
        have hs : (r ≫ i.hom) ≫ j.source.left = y.left := by
          simpa only [Category.assoc, hq] using h₂
        have hw : (r ≫ i.hom) ≫ R.hom = T.hom := by
          calc
            (r ≫ i.hom) ≫ R.hom =
                ((r ≫ i.hom) ≫ j.target.left) ≫ U.hom := by simp
            _ = T.hom := by rw [ht, Over.w]
        refine ⟨Over.homMk (r ≫ i.hom) hw, ?_, ?_⟩
        · apply Over.OverMorphism.ext
          exact ht
        · apply Over.OverMorphism.ext
          exact hs
    have he := equivalence_on_hom e T.left
    constructor
    · intro x
      exact (hrel x x).mpr (he.refl x.left)
    · intro x y hxy
      exact (hrel y x).mpr (he.symm ((hrel x y).mp hxy))
    · intro x y z hxy hyz
      exact (hrel x z).mpr (he.trans ((hrel x y).mp hxy) ((hrel y z).mp hyz))

/-- **Stacks 02Z1.** Away from characteristic two, the involution relation on the affine
line is an étale equivalence relation. -/
@[stacks 02Z1 "etale_relation"]
theorem isEtaleEquivalenceRelation [NeZero (2 : k)] :
    Stacks.Groupoids.IsEtaleEquivalenceRelation (involutionRelation k) := by
  refine {
    isEquivalenceRelation := ?_
    etale_source := etale_source k
    etale_target := etale_target k }
  apply isEquivalenceRelation_over_of_iso (involutionRelation k)
    (overCoprodIso (affineLine k) (puncturedAffineLine k))
    (relationLeftSum k) (relationRightSum k)
  · rw [involutionRelation_target]
    exact coprodComparison_comp_left_coprod_desc _ _
  · rw [involutionRelation_source]
    exact coprodComparison_comp_left_coprod_desc _ _
  · exact involution_relation_maps_equivalence k

attribute [instance] isEtaleEquivalenceRelation
/-! ### The quotient is a smooth algebraic space -/

/-- An isomorphism of presheaves on the big fppf site is étale after every representable base
change. -/
private theorem presheafEtale_of_isIso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) e.hom := by
  have := etale_scheme_respectsIso.{u}
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda e.hom, ?_⟩
  intro A A' g fst snd hpb
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
  have : IsIso ((BigFppfOver.toScheme B S hS).map snd) := Functor.map_isIso _ snd
  change Etale ((BigFppfOver.toScheme B S hS).map snd)
  have hmult : MorphismProperty.IsMultiplicative (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities
  have : MorphismProperty.ContainsIdentities (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    hmult.toContainsIdentities
  exact MorphismProperty.isomorphisms_le_of_containsIdentities
    (@Etale.{u} : MorphismProperty Scheme.{u}) _ inferInstance

/-- The affine line is smooth over the ground field. -/
private theorem smooth_affineLine : Smooth (affineLine k).hom := by
  change Smooth (AffineSpace PUnit.{u + 1} (Spec (.of k)) ↘ Spec (.of k))
  let e := AffineSpace.SpecIso PUnit.{u + 1} (.of k)
  have hpoly : RingHom.Smooth
      (MvPolynomial.C : k →+* MvPolynomial PUnit.{u + 1} k) := by
    simpa only [MvPolynomial.algebraMap_eq] using
      (RingHom.smooth_algebraMap.mpr
        (show Algebra.Smooth k (MvPolynomial PUnit.{u + 1} k) from
          ⟨inferInstance, inferInstance⟩))
  have hspec : Smooth (Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : k →+* MvPolynomial PUnit.{u + 1} k))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).2 hpoly
  have he := AffineSpace.SpecIso_inv_over (n := PUnit.{u + 1}) (.of k)
  have hcomp : Smooth (e.hom ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : k →+* MvPolynomial PUnit.{u + 1} k))) := inferInstance
  rw [← he] at hcomp
  rw [← Category.assoc, e.hom_inv_id, Category.id_comp] at hcomp
  exact hcomp

/-- The affine line, as an object of a big fppf site containing `Spec k`. It belongs to the
site because it is of finite type and quasi-compact over the base. -/
noncomputable def affineLineChart (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k))) : BigFppfOver B (Spec (.of k)) hS :=
  letI : Finite PUnit.{u + 1} := inferInstance
  haveI : LocallyOfFinitePresentation (affineLine k).hom := by
    change LocallyOfFinitePresentation
      (AffineSpace PUnit.{u + 1} (Spec (.of k)) ↘ Spec (.of k))
    infer_instance
  letI : IsLocallyNoetherian (Spec (.of k)) := inferInstance
  letI : LocallyOfFiniteType (affineLine k).hom :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mp ‹_›
  letI : QuasiCompact (affineLine k).hom := inferInstance
  Over.mk (ObjectProperty.homMk (affineLine k).hom :
    B.obj (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (affineLine k).hom hS) ⟶
      B.obj hS)

@[simp]
theorem affineLineChart_post (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k))) :
    (Over.post B.inclusion).obj (affineLineChart k B hS) = affineLine k := rfl

instance isAffine_affineLineChart (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k))) :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hS).obj (affineLineChart k B hS)) := by
  change IsAffine (affineLine k).left
  infer_instance

/-- **Stacks 02Z1.** Away from characteristic two, the quotient of the affine line by the
punctured graph of negation is an algebraic space over the ground field.

The chart `affineLineChart` is affine, so the two descent hypotheses of Stacks 0265 are
discharged unconditionally by
`AlgebraicGeometry.Space.isAlgebraicSpace_quotientSheaf_of_affineBase_unconditional`. -/
@[stacks 02Z1 "algebraic_space"]
theorem isAlgebraicSpace_involutionQuotient (hchar : (2 : k) ≠ 0) (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    IsAlgebraicSpace B (Spec (.of k)) hS (involutionQuotient k B hS).obj := by
  have : NeZero (2 : k) := ⟨hchar⟩
  have : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (R := relationScheme k)
      (U := (Over.post B.inclusion).obj (affineLineChart k B hS))
      (involutionRelation k) := isEtaleEquivalenceRelation k
  exact Space.isAlgebraicSpace_quotientSheaf_of_affineBase_unconditional B (Spec (.of k)) hS
    (affineLineChart k B hS) (involutionRelation k)

/-- **Stacks 0ENT.** Away from characteristic two, the quotient of the affine line by the
punctured graph of negation is smooth over the ground field.

Smoothness is tested on the quotient chart, which is a surjective étale chart of the
quotient by Stacks 0265, and on the affine line itself, which is smooth over the base. -/
@[stacks 0ENT "smoothness"]
theorem isSmooth_involutionQuotient (hchar : (2 : k) ≠ 0) (B : BigFppfSite.{u})
    (hS : B.Contains (Spec (.of k)))
    [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)] :
    Space.IsSmooth B (Spec (.of k)) hS
      (terminal.from (involutionQuotient k B hS).obj) := by
  have : NeZero (2 : k) := ⟨hchar⟩
  have : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (R := relationScheme k)
      (U := (Over.post B.inclusion).obj (affineLineChart k B hS))
      (involutionRelation k) := isEtaleEquivalenceRelation k
  let U := affineLineChart k B hS
  let V : BigFppfOver B (Spec (.of k)) hS := Over.mk (𝟙 (B.obj hS))
  have hX := isAlgebraicSpace_involutionQuotient k hchar B hS
  have hVspace := isAlgebraicSpace_yoneda B (Spec (.of k)) hS V
  have hVterminal : IsTerminal (yoneda.obj V) :=
    (Over.mkIdTerminal : IsTerminal V).isTerminalObj yoneda _
  let eV : yoneda.obj V ≅ ⊤_ ((BigFppfOver B (Spec (.of k)) hS)ᵒᵖ ⥤ Type u) :=
    hVterminal.uniqueUpToIso terminalIsTerminal
  have hY := isAlgebraicSpace_of_iso B (Spec (.of k)) hS eV.symm hVspace
  let qmap := yonedaEquiv.symm
    ((Stacks.Groupoids.toQuotientSheaf
      (BigFppfOver.topology B (Spec (.of k)) hS)
      (Over.post B.inclusion) (involutionRelation k)).app
      (Opposite.op U) (𝟙 ((Over.post B.inclusion).obj U)))
  have hqSurj := Space.surjective_toQuotientSheaf_of_affineBase_unconditional
    B (Spec (.of k)) hS U (involutionRelation k)
  have hqEtale := Space.etale_toQuotientSheaf_of_affineBase_unconditional
    B (Spec (.of k)) hS U (involutionRelation k)
  let h : U ⟶ V := Over.homMk U.hom (by simp [V])
  have hscheme : Smooth ((BigFppfOver.toScheme B (Spec (.of k)) hS).map h) :=
    smooth_affineLine k
  have hsurjChart : Space.HoldsOnSurjectiveEtaleChart B (Spec (.of k)) hS
      (@Smooth.{u} : MorphismProperty Scheme.{u})
      (terminal.from (involutionQuotient k B hS).obj) :=
    ⟨U, V, qmap, eV.hom, h, hqEtale, presheafEtale_of_isIso B (Spec (.of k)) hS eV, hqSurj,
      terminalIsTerminal.hom_ext _ _, hscheme⟩
  exact ((Space.isSmooth_tfae B (Spec (.of k)) hS hX hY
    (terminal.from (involutionQuotient k B hS).obj)).out 1 8).mpr hsurjChart

end AffineLineInvolution

end AlgebraicGeometry

end
