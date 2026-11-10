module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.EquivalenceRelation

/-!
# The diagonal together with the graph of an involution is an equivalence relation

Let `U` be a scheme, let `τ : U ⟶ U` be an involution, let `ι : D ⟶ U` be a scheme over `U`
which `τ` preserves, in the sense that `τ` restricts to a morphism `τD : D ⟶ D` over it, and
let `p₁, p₂ : U ⨿ D ⟶ U` be the identity on the first summand and, on the second summand,
`ι` and `ι ≫ τ` respectively.  Then `p₁, p₂` is an internal equivalence relation on `U` as
soon as it is jointly monic: the first summand is the diagonal and the second is the part of
the graph of `τ` lying over `D`.

## Main results

* `AlgebraicGeometry.nonempty_isColimit_binaryCofan_pullback_fst`: the pullbacks of a
  morphism into a binary coproduct of schemes along the two coprojections again form a binary
  coproduct.
* `AlgebraicGeometry.isEquivalenceRelation_of_coprod_involution`: the diagonal together with
  the part of the graph of an involution lying over `D` is an equivalence relation.

## Implementation notes

The hypotheses are the four composites of `p₁` and `p₂` with the two coprojections rather
than the two maps written as `CategoryTheory.Limits.coprod.desc`.  Nothing is assumed of `ι`
beyond the existence of the restricted involution `τD`; in particular it need not be a
monomorphism, and `D` need not be an open subscheme.

## References

* [Stacks Project, Tag 022P](https://stacks.math.columbia.edu/tag/022P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The pullbacks of a morphism into a binary coproduct of schemes along the two coprojections
again form a binary coproduct. -/
theorem nonempty_isColimit_binaryCofan_pullback_fst {X A B : Scheme.{u}} (g : X ⟶ A ⨿ B) :
    Nonempty (IsColimit
      (BinaryCofan.mk (pullback.fst g coprod.inl) (pullback.fst g coprod.inr))) := by
  let F' : Discrete WalkingPair ⥤ Scheme :=
    pair (pullback g coprod.inl) (pullback g coprod.inr)
  let α : F' ⟶ pair A B := Discrete.natTrans fun i =>
    match i with
    | ⟨WalkingPair.left⟩ => pullback.snd g coprod.inl
    | ⟨WalkingPair.right⟩ => pullback.snd g coprod.inr
  let c : BinaryCofan A B := BinaryCofan.mk coprod.inl coprod.inr
  let c' : BinaryCofan (pullback g coprod.inl) (pullback g coprod.inr) :=
    BinaryCofan.mk (pullback.fst g coprod.inl) (pullback.fst g coprod.inr)
  have h : α ≫ c.ι = c'.ι ≫ (Functor.const (Discrete WalkingPair)).map g := by
    ext i
    match i with
    | ⟨WalkingPair.left⟩ =>
        change pullback.snd g coprod.inl ≫ coprod.inl = pullback.fst g coprod.inl ≫ g
        exact pullback.condition.symm
    | ⟨WalkingPair.right⟩ =>
        change pullback.snd g coprod.inr ≫ coprod.inr = pullback.fst g coprod.inr ≫ g
        exact pullback.condition.symm
  exact ⟨Classical.choice
    ((FinitaryExtensive.vanKampen c (coprodIsCoprod A B)).isUniversal c' α g h
      (NatTrans.Equifibered.of_discrete α) fun i =>
      match i with
      | ⟨WalkingPair.left⟩ => IsPullback.of_hasPullback g coprod.inl
      | ⟨WalkingPair.right⟩ => IsPullback.of_hasPullback g coprod.inr)⟩

variable {U D : Scheme.{u}} (ι : D ⟶ U) (τ : U ⟶ U) (τD : D ⟶ D) (p₁ p₂ : U ⨿ D ⟶ U)

/-- A jointly monic pair of morphisms `U ⨿ D ⟶ U` which is the identity on the first summand
and is `ι`, respectively `ι ≫ τ`, on the second is an equivalence relation on `U`, as soon as
`τ` is an involution restricting to a morphism `τD` of `D` over `ι`.  The first summand is the
diagonal and the second is the part of the graph of `τ` lying over `D`. -/
theorem isEquivalenceRelation_of_coprod_involution
    (h₁l : (coprod.inl : U ⟶ U ⨿ D) ≫ p₁ = 𝟙 U)
    (h₁r : (coprod.inr : D ⟶ U ⨿ D) ≫ p₁ = ι)
    (h₂l : (coprod.inl : U ⟶ U ⨿ D) ≫ p₂ = 𝟙 U)
    (h₂r : (coprod.inr : D ⟶ U ⨿ D) ≫ p₂ = ι ≫ τ)
    (hτD : τD ≫ ι = ι ≫ τ) (hτ : τ ≫ τ = 𝟙 U)
    [JointlyMono₂ p₁ p₂] :
    IsEquivalenceRelation p₁ p₂ := by
  have h₁rτ : (coprod.inr : D ⟶ U ⨿ D) ≫ p₁ ≫ τ = ι ≫ τ := by
    rw [← Category.assoc, h₁r]
  let s : U ⨿ D ⟶ U ⨿ D := coprod.desc coprod.inl (τD ≫ coprod.inr)
  have hs_inl : (coprod.inl : U ⟶ U ⨿ D) ≫ s = coprod.inl := coprod.inl_desc _ _
  have hs_inr : (coprod.inr : D ⟶ U ⨿ D) ≫ s = τD ≫ coprod.inr := coprod.inr_desc _ _
  let c : PullbackCone p₂ p₁ := pullback.cone p₂ p₁
  let a : c.pt ⟶ U ⨿ D := pullback.fst p₂ p₁
  let b : c.pt ⟶ U ⨿ D := pullback.snd p₂ p₁
  have hab : a ≫ p₂ = b ≫ p₁ := pullback.condition
  let t₀ : pullback a coprod.inl ⟶ U ⨿ D := pullback.fst a coprod.inl ≫ b
  let d := pullback a coprod.inr
  let dπ : d ⟶ c.pt := pullback.fst a coprod.inr
  let dι : d ⟶ D := pullback.snd a coprod.inr
  let q := dπ ≫ b
  let c₀ : BinaryCofan (pullback q coprod.inl) (pullback q coprod.inr) :=
    BinaryCofan.mk (pullback.fst q coprod.inl) (pullback.fst q coprod.inr)
  have hc₀ : IsColimit c₀ := Classical.choice (nonempty_isColimit_binaryCofan_pullback_fst q)
  let u₀ : pullback q coprod.inl ⟶ U ⨿ D :=
    pullback.fst q coprod.inl ≫ dι ≫ coprod.inr
  let u₁ : pullback q coprod.inr ⟶ U ⨿ D :=
    pullback.fst q coprod.inr ≫ dι ≫ ι ≫ coprod.inl
  let t₁ : d ⟶ U ⨿ D := hc₀.desc (BinaryCofan.mk u₀ u₁)
  have ht₁_fac₀ : pullback.fst q coprod.inl ≫ t₁ = u₀ :=
    BinaryCofan.IsColimit.inl_desc hc₀ u₀ u₁
  have ht₁_fac₁ : pullback.fst q coprod.inr ≫ t₁ = u₁ :=
    BinaryCofan.IsColimit.inr_desc hc₀ u₀ u₁
  let c₁ : BinaryCofan (pullback a coprod.inl) d :=
    BinaryCofan.mk (pullback.fst a coprod.inl) (pullback.fst a coprod.inr)
  have hc₁ : IsColimit c₁ := Classical.choice (nonempty_isColimit_binaryCofan_pullback_fst a)
  let t : c.pt ⟶ U ⨿ D := hc₁.desc (BinaryCofan.mk t₀ t₁)
  have ht_fac₀ : pullback.fst a coprod.inl ≫ t = t₀ :=
    BinaryCofan.IsColimit.inl_desc hc₁ t₀ t₁
  have ht_fac₁ : pullback.fst a coprod.inr ≫ t = t₁ :=
    BinaryCofan.IsColimit.inr_desc hc₁ t₀ t₁
  have hqa : pullback.fst a coprod.inl ≫ a = pullback.snd a coprod.inl ≫ coprod.inl :=
    pullback.condition
  have hdπ : dπ ≫ a = dι ≫ coprod.inr := pullback.condition
  have ht₀_left : t₀ ≫ p₁ = pullback.fst a coprod.inl ≫ a ≫ p₁ := by
    simp [t₀, ← hab, reassoc_of% hqa, h₁l, h₂l]
  have hd_left : dπ ≫ a ≫ p₁ = dι ≫ ι := by
    rw [← Category.assoc, hdπ, Category.assoc, h₁r]
  have hd_right : dπ ≫ a ≫ p₂ = dι ≫ ι ≫ τ := by
    rw [← Category.assoc, hdπ, Category.assoc, h₂r]
  have hd_mid : dπ ≫ b ≫ p₁ = dι ≫ ι ≫ τ := by rw [← hab, hd_right]
  have hd_mid2 : dπ ≫ b ≫ p₁ ≫ τ = dι ≫ ι := by simpa [hτ] using hd_mid =≫ τ
  have ht₁_left : t₁ ≫ p₁ = dπ ≫ a ≫ p₁ := by
    refine hc₀.hom_ext fun j => ?_
    match j with
    | ⟨WalkingPair.left⟩ =>
        change (pullback.fst q coprod.inl ≫ t₁) ≫ p₁ =
          (pullback.fst q coprod.inl ≫ dπ ≫ a) ≫ p₁
        rw [ht₁_fac₀]
        simp only [u₀, Category.assoc, h₁r, hd_left]
    | ⟨WalkingPair.right⟩ =>
        change (pullback.fst q coprod.inr ≫ t₁) ≫ p₁ =
          (pullback.fst q coprod.inr ≫ dπ ≫ a) ≫ p₁
        rw [ht₁_fac₁]
        simp only [u₁, Category.assoc, h₁l, Category.comp_id, hd_left]
  have ht₁_right : t₁ ≫ p₂ = dπ ≫ b ≫ p₂ := by
    refine hc₀.hom_ext fun j => ?_
    match j with
    | ⟨WalkingPair.left⟩ =>
        have hq : pullback.fst q coprod.inl ≫ q = pullback.snd q coprod.inl ≫ coprod.inl :=
          pullback.condition
        change (pullback.fst q coprod.inl ≫ t₁) ≫ p₂ = (pullback.fst q coprod.inl ≫ q) ≫ p₂
        rw [ht₁_fac₀, hq]
        calc u₀ ≫ p₂ = pullback.fst q coprod.inl ≫ dπ ≫ b ≫ p₁ := by
              simp only [u₀, Category.assoc, h₂r, hd_mid]
          _ = (pullback.fst q coprod.inl ≫ q) ≫ p₁ := by simp only [q, Category.assoc]
          _ = (pullback.snd q coprod.inl ≫ coprod.inl) ≫ p₁ := by rw [hq]
          _ = (pullback.snd q coprod.inl ≫ coprod.inl) ≫ p₂ := by
              simp only [Category.assoc, h₁l, h₂l]
    | ⟨WalkingPair.right⟩ =>
        have hq : pullback.fst q coprod.inr ≫ q = pullback.snd q coprod.inr ≫ coprod.inr :=
          pullback.condition
        change (pullback.fst q coprod.inr ≫ t₁) ≫ p₂ = (pullback.fst q coprod.inr ≫ q) ≫ p₂
        rw [ht₁_fac₁, hq]
        calc u₁ ≫ p₂ = pullback.fst q coprod.inr ≫ dπ ≫ b ≫ p₁ ≫ τ := by
              simp only [u₁, Category.assoc, h₂l, Category.comp_id, hd_mid2]
          _ = (pullback.fst q coprod.inr ≫ q) ≫ p₁ ≫ τ := by simp only [q, Category.assoc]
          _ = (pullback.snd q coprod.inr ≫ coprod.inr) ≫ p₁ ≫ τ := by rw [hq]
          _ = (pullback.snd q coprod.inr ≫ coprod.inr) ≫ p₂ := by
              simp only [Category.assoc, h₁rτ, h₂r]
  have ht_left : t ≫ p₁ = c.fst ≫ p₁ := by
    change t ≫ p₁ = a ≫ p₁
    refine hc₁.hom_ext fun j => ?_
    match j with
    | ⟨WalkingPair.left⟩ =>
        change (pullback.fst a coprod.inl ≫ t) ≫ p₁ = (pullback.fst a coprod.inl ≫ a) ≫ p₁
        rw [ht_fac₀, Category.assoc]
        exact ht₀_left
    | ⟨WalkingPair.right⟩ =>
        change (pullback.fst a coprod.inr ≫ t) ≫ p₁ = (pullback.fst a coprod.inr ≫ a) ≫ p₁
        rw [ht_fac₁, Category.assoc]
        exact ht₁_left
  have ht_right : t ≫ p₂ = c.snd ≫ p₂ := by
    change t ≫ p₂ = b ≫ p₂
    refine hc₁.hom_ext fun j => ?_
    match j with
    | ⟨WalkingPair.left⟩ =>
        change (pullback.fst a coprod.inl ≫ t) ≫ p₂ = (pullback.fst a coprod.inl ≫ b) ≫ p₂
        rw [ht_fac₀, Category.assoc]
    | ⟨WalkingPair.right⟩ =>
        change (pullback.fst a coprod.inr ≫ t) ≫ p₂ = (pullback.fst a coprod.inr ≫ b) ≫ p₂
        rw [ht_fac₁, Category.assoc]
        exact ht₁_right
  have hsym₁ : s ≫ p₁ = p₂ := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, hs_inl, h₁l, h₂l]
    · rw [← Category.assoc, hs_inr, Category.assoc, h₁r, hτD, h₂r]
  have hsym₂ : s ≫ p₂ = p₁ := by
    refine coprod.hom_ext ?_ ?_
    · rw [← Category.assoc, hs_inl, h₂l, h₁l]
    · rw [← Category.assoc, hs_inr, Category.assoc, h₂r, ← Category.assoc, hτD,
        Category.assoc, hτ, Category.comp_id, h₁r]
  exact EquivalenceRelation.isEquivalenceRelation
    { __ := (inferInstance : JointlyMono₂ p₁ p₂)
      r := coprod.inl
      reflexivity₁ := h₁l
      reflexivity₂ := h₂l
      s := s
      symmetry₁ := hsym₁
      symmetry₂ := hsym₂
      c := c
      isLimit := pullback.isLimit p₂ p₁
      t := t
      transitivity₁ := ht_left
      transitivity₂ := ht_right }

end AlgebraicGeometry

end
