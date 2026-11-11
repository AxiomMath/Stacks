module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentTransport

/-!
# The descent datum of an involution along an étale double cover

Let `π : Y ⟶ S` be a morphism of schemes and `σ : Y ⟶ Y` an involution such that
`Y ×_S Y` is the disjoint union of the diagonal and the graph of `σ`, that is, the square
formed by `coprod.desc (𝟙 Y) (𝟙 Y)` and `coprod.desc (𝟙 Y) σ` from `Y ⨿ Y` to `Y` over `S` is
a pullback square. Let `X ⊆ Y` be open, let `p : W ⟶ X` be a morphism of schemes, and let `ρ`
be an involution of the part `W_O` of `W` lying over the overlap `O = X ∩ σ⁻¹ X`, covering `σ`.

A point of `W ×_S X` is a pair `(w, x)` with `p w` and `x` either equal or exchanged by `σ`;
in the second case `w` lies in `W_O`. Sending `(w, x)` to `w` in the first case and to `ρ w`
in the second is a descent transport for `W` relative to `X ⟶ S`, hence a descent datum. If
that datum is effective, then `W` is the base change of a scheme `U` over `S`, and the
projection `W ⟶ U` is invariant under `ρ`.

## Main definitions

* `AlgebraicGeometry.involutionOverlap` is the open subscheme `W_O` of `W`.
* `AlgebraicGeometry.involutionMove` is the operation on generalized points described above.
* `AlgebraicGeometry.involutionTransport` is that operation as a descent transport, and
  `AlgebraicGeometry.involutionDatum` is the descent datum it determines.

## Main results

* `AlgebraicGeometry.hom_ext_of_isPullback_coprodDesc`: two morphisms out of a scheme carrying
  two maps `u v` to `Y` which agree over `S` are equal as soon as they agree on every test
  object over which `u = v` and on every test object over which `u ≫ σ = v`.
* `AlgebraicGeometry.involutionDatum_obj`: the scheme of the datum is `W` over `X`.
* `AlgebraicGeometry.exists_isPullback_of_isEffective_involutionDatum`: if the datum is
  effective, `W` is a base change `U ×_S X` and the projection `W ⟶ U` is `ρ`-invariant.

## Implementation notes

The decomposition of `W ×_S X` is obtained by pulling back the coproduct decomposition of
`Y ⨿ Y` along the map `W ×_S X ⟶ Y ⨿ Y` given by the pullback square; coproducts of schemes
are universal (`CategoryTheory.FinitaryExtensive`). The gluing map is defined on the two
pieces separately, and all laws are verified on generalized points after splitting the test
object in the same way.

## References

* [Stacks Project, Tag 08KF](https://stacks.math.columbia.edu/tag/08KF)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-! ### Splitting a scheme over a coproduct -/

/-- A scheme `T` with a morphism `t : T ⟶ A ⨿ B` is the disjoint union of the pullbacks of the
two summands. -/
def isColimitPullbackCoprod {T A B : Scheme.{u}} (t : T ⟶ A ⨿ B) :
    IsColimit (BinaryCofan.mk (pullback.fst t (coprod.inl : A ⟶ A ⨿ B))
      (pullback.fst t (coprod.inr : B ⟶ A ⨿ B))) :=
  Classical.choice <| ((BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.van_kampen' _ (coprodIsCoprod A B))
    (BinaryCofan.mk (pullback.fst t (coprod.inl : A ⟶ A ⨿ B))
      (pullback.fst t (coprod.inr : B ⟶ A ⨿ B)))
    (pullback.snd _ _) (pullback.snd _ _) t pullback.condition.symm
    pullback.condition.symm).mpr
    ⟨IsPullback.of_hasPullback _ _, IsPullback.of_hasPullback _ _⟩

/-- On the pullback of the first summand of `Y ⨿ Y`, the two maps `coprod.desc (𝟙 Y) (𝟙 Y)`
and `coprod.desc (𝟙 Y) σ` agree. -/
lemma pullback_fst_inl_comp_coprodDesc {T Y : Scheme.{u}} (σ : Y ⟶ Y) (t : T ⟶ Y ⨿ Y) :
    pullback.fst t (coprod.inl : Y ⟶ Y ⨿ Y) ≫ t ≫ coprod.desc (𝟙 Y) (𝟙 Y) =
      pullback.fst t (coprod.inl : Y ⟶ Y ⨿ Y) ≫ t ≫ coprod.desc (𝟙 Y) σ := by
  simp only [pullback.condition_assoc, coprod.inl_desc]

/-- On the pullback of the second summand of `Y ⨿ Y`, `coprod.desc (𝟙 Y) (𝟙 Y)` followed by
`σ` is `coprod.desc (𝟙 Y) σ`. -/
lemma pullback_fst_inr_comp_coprodDesc {T Y : Scheme.{u}} (σ : Y ⟶ Y) (t : T ⟶ Y ⨿ Y) :
    pullback.fst t (coprod.inr : Y ⟶ Y ⨿ Y) ≫ t ≫ coprod.desc (𝟙 Y) (𝟙 Y) ≫ σ =
      pullback.fst t (coprod.inr : Y ⟶ Y ⨿ Y) ≫ t ≫ coprod.desc (𝟙 Y) σ := by
  simp only [pullback.condition_assoc, coprod.inr_desc, coprod.inr_desc_assoc, Category.id_comp]

/-- **Splitting along the decomposition `Y ×_S Y = Δ ⨿ Γ_σ`.** If `Y ⨿ Y ≅ Y ×_S Y` through
`(𝟙, 𝟙)` and `(𝟙, σ)`, then two morphisms out of a scheme carrying maps `u v : T ⟶ Y` which
agree over `S` are equal as soon as they agree after every base change on which `u = v` and
after every base change on which `u ≫ σ = v`. -/
lemma hom_ext_of_isPullback_coprodDesc {Y S : Scheme.{u}} {π : Y ⟶ S} {σ : Y ⟶ Y}
    (hπ : IsPullback (coprod.desc (𝟙 Y) (𝟙 Y)) (coprod.desc (𝟙 Y) σ) π π)
    {T Z : Scheme.{u}} (u v : T ⟶ Y) (huv : u ≫ π = v ≫ π) {f g : T ⟶ Z}
    (h₁ : ∀ ⦃T' : Scheme.{u}⦄ (k : T' ⟶ T), k ≫ u = k ≫ v → k ≫ f = k ≫ g)
    (h₂ : ∀ ⦃T' : Scheme.{u}⦄ (k : T' ⟶ T), k ≫ u ≫ σ = k ≫ v → k ≫ f = k ≫ g) :
    f = g := by
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : T ⟶ Y ⨿ Y,
      t ≫ coprod.desc (𝟙 Y) (𝟙 Y) = u ∧ t ≫ coprod.desc (𝟙 Y) σ = v :=
    ⟨hπ.lift u v huv, hπ.lift_fst _ _ _, hπ.lift_snd _ _ _⟩
  refine BinaryCofan.IsColimit.hom_ext (isColimitPullbackCoprod t) (h₁ _ ?_) (h₂ _ ?_)
  · rw [← ht₁, ← ht₂]
    exact pullback_fst_inl_comp_coprodDesc σ t
  · rw [← ht₁, ← ht₂]
    exact pullback_fst_inr_comp_coprodDesc σ t

/-! ### The overlap -/

/-- The open subscheme of `W` lying over `X ∩ σ⁻¹ X`, for `p : W ⟶ X` with `X ⊆ Y` open. -/
abbrev involutionOverlap {Y : Scheme.{u}} (σ : Y ⟶ Y) (X : Y.Opens) {W : Scheme.{u}}
    (p : W ⟶ X.toScheme) : W.Opens :=
  p ⁻¹ᵁ (X.ι ⁻¹ᵁ (σ ⁻¹ᵁ X))

/-- A generalized point `a` of `W` whose image under `σ` lies in `X` factors through the
overlap. -/
def liftInvolutionOverlap {Y : Scheme.{u}} {σ : Y ⟶ Y} {X : Y.Opens} {W : Scheme.{u}}
    {p : W ⟶ X.toScheme} {T : Scheme.{u}} (a : T ⟶ W) (c : T ⟶ X.toScheme)
    (h : a ≫ p ≫ X.ι ≫ σ = c ≫ X.ι) : T ⟶ (involutionOverlap σ X p).toScheme :=
  (isPullback_morphismRestrict (p ≫ X.ι ≫ σ) X).lift c a h.symm

/-- The lift of a generalized point through the overlap recovers the point. -/
@[reassoc (attr := simp)]
lemma liftInvolutionOverlap_ι {Y : Scheme.{u}} {σ : Y ⟶ Y} {X : Y.Opens} {W : Scheme.{u}}
    {p : W ⟶ X.toScheme} {T : Scheme.{u}} (a : T ⟶ W) (c : T ⟶ X.toScheme)
    (h : a ≫ p ≫ X.ι ≫ σ = c ≫ X.ι) :
    liftInvolutionOverlap a c h ≫ (involutionOverlap σ X p).ι = a :=
  (isPullback_morphismRestrict (p ≫ X.ι ≫ σ) X).lift_snd _ _ _

/-! ### The gluing map -/

section Gluing

variable {Y S : Scheme.{u}} {π : Y ⟶ S} {σ : Y ⟶ Y}
  (hπ : IsPullback (coprod.desc (𝟙 Y) (𝟙 Y)) (coprod.desc (𝟙 Y) σ) π π)
  {X : Y.Opens} {W : Scheme.{u}} {p : W ⟶ X.toScheme}
  (ρ : (involutionOverlap σ X p).toScheme ⟶ (involutionOverlap σ X p).toScheme)

/-- The map `W ×_S X ⟶ Y ⨿ Y` recording in which piece of `Y ×_S Y` a point lies. -/
def involutionSplit : pullback (p ≫ X.ι ≫ π) (X.ι ≫ π) ⟶ Y ⨿ Y :=
  hπ.lift (pullback.fst _ _ ≫ p ≫ X.ι) (pullback.snd _ _ ≫ X.ι) (by
    simp only [Category.assoc]
    exact pullback.condition)

/-- The first component of `AlgebraicGeometry.involutionSplit` is the point of `W`, in `Y`. -/
@[reassoc]
lemma involutionSplit_desc_id :
    involutionSplit (p := p) hπ ≫ coprod.desc (𝟙 Y) (𝟙 Y) = pullback.fst _ _ ≫ p ≫ X.ι :=
  hπ.lift_fst _ _ _

/-- The second component of `AlgebraicGeometry.involutionSplit` is the point of `X`, in `Y`. -/
@[reassoc]
lemma involutionSplit_desc_sigma :
    involutionSplit (p := p) hπ ≫ coprod.desc (𝟙 Y) σ = pullback.snd _ _ ≫ X.ι :=
  hπ.lift_snd _ _ _

/-- On the exchanged piece of `W ×_S X`, the point of `W` lies over `σ⁻¹ X`. -/
lemma involutionSplit_inr :
    (pullback.fst (involutionSplit (p := p) hπ) (coprod.inr : Y ⟶ Y ⨿ Y) ≫
        pullback.fst _ _) ≫ p ≫ X.ι ≫ σ =
      (pullback.fst (involutionSplit (p := p) hπ) (coprod.inr : Y ⟶ Y ⨿ Y) ≫
        pullback.snd _ _) ≫ X.ι := by
  have h := pullback_fst_inr_comp_coprodDesc σ (involutionSplit (p := p) hπ)
  rw [involutionSplit_desc_id_assoc, involutionSplit_desc_sigma] at h
  simpa only [Category.assoc] using h

/-- The gluing map `W ×_S X ⟶ W`: the first projection on the diagonal piece, and `ρ` on the
piece where the two points of `Y` are exchanged by `σ`. -/
def involutionGluingMap : pullback (p ≫ X.ι ≫ π) (X.ι ≫ π) ⟶ W :=
  (BinaryCofan.IsColimit.desc' (isColimitPullbackCoprod (involutionSplit (p := p) hπ))
    (pullback.fst _ (coprod.inl : Y ⟶ Y ⨿ Y) ≫ pullback.fst _ _)
    (liftInvolutionOverlap _ _ (involutionSplit_inr hπ) ≫
      ρ ≫ (involutionOverlap σ X p).ι)).1

/-- The gluing map on the diagonal piece. -/
lemma involutionGluingMap_inl :
    pullback.fst _ (coprod.inl : Y ⟶ Y ⨿ Y) ≫ involutionGluingMap hπ ρ =
      pullback.fst (involutionSplit (p := p) hπ) (coprod.inl : Y ⟶ Y ⨿ Y) ≫
        pullback.fst _ _ :=
  (BinaryCofan.IsColimit.desc' (isColimitPullbackCoprod (involutionSplit (p := p) hπ)) _ _).2.1

/-- The gluing map on the exchanged piece. -/
lemma involutionGluingMap_inr :
    pullback.fst _ (coprod.inr : Y ⟶ Y ⨿ Y) ≫ involutionGluingMap hπ ρ =
      liftInvolutionOverlap _ _ (involutionSplit_inr hπ) ≫ ρ ≫ (involutionOverlap σ X p).ι :=
  (BinaryCofan.IsColimit.desc' (isColimitPullbackCoprod (involutionSplit (p := p) hπ)) _ _).2.2

/-- The operation on generalized points: a point `a` of `W` and a point `b` of `X` lying over
the same point of `S` give the point of `W` over `b` obtained by the gluing map. -/
def involutionMove {T : Scheme.{u}} (a : T ⟶ W) (b : T ⟶ X.toScheme)
    (h : a ≫ p ≫ X.ι ≫ π = b ≫ X.ι ≫ π) : T ⟶ W :=
  pullback.lift a b h ≫ involutionGluingMap hπ ρ

variable {hπ ρ}

/-- `involutionMove` depends only on its two points. -/
lemma involutionMove_congr {T : Scheme.{u}} {a a' : T ⟶ W} {b b' : T ⟶ X.toScheme}
    {h : a ≫ p ≫ X.ι ≫ π = b ≫ X.ι ≫ π} {h' : a' ≫ p ≫ X.ι ≫ π = b' ≫ X.ι ≫ π}
    (ha : a = a') (hb : b = b') :
    involutionMove hπ ρ a b h = involutionMove hπ ρ a' b' h' := by
  subst ha hb
  rfl

/-- `involutionMove` commutes with change of test object. -/
@[reassoc]
lemma comp_involutionMove {T T' : Scheme.{u}} (k : T' ⟶ T) (a : T ⟶ W)
    (b : T ⟶ X.toScheme) (h : a ≫ p ≫ X.ι ≫ π = b ≫ X.ι ≫ π) :
    k ≫ involutionMove hπ ρ a b h =
      involutionMove hπ ρ (k ≫ a) (k ≫ b) (by simp only [Category.assoc, h]) := by
  simp only [involutionMove, ← Category.assoc]
  congr 1
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

/-- On the diagonal piece the operation returns the given point of `W`. -/
lemma involutionMove_eq_self {T : Scheme.{u}} (a : T ⟶ W) (b : T ⟶ X.toScheme)
    (h : a ≫ p ≫ X.ι ≫ π = b ≫ X.ι ≫ π) (hab : a ≫ p ≫ X.ι = b ≫ X.ι) :
    involutionMove hπ ρ a b h = a := by
  have hm : pullback.lift a b h ≫ involutionSplit hπ =
      (a ≫ p ≫ X.ι) ≫ (coprod.inl : Y ⟶ Y ⨿ Y) := by
    apply hπ.hom_ext
    · simp only [Category.assoc, involutionSplit_desc_id, pullback.lift_fst_assoc,
        coprod.inl_desc, Category.comp_id]
    · simp only [Category.assoc, involutionSplit_desc_sigma, pullback.lift_snd_assoc,
        coprod.inl_desc, Category.comp_id, hab]
  have hg : pullback.lift a b h =
      pullback.lift (pullback.lift a b h) (a ≫ p ≫ X.ι) hm ≫ pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).symm
  rw [involutionMove, hg, Category.assoc, involutionGluingMap_inl, ← Category.assoc,
    ← hg, pullback.lift_fst]

/-- On the exchanged piece the operation is `ρ`. -/
lemma involutionMove_eq_rho {T : Scheme.{u}} (a : T ⟶ W) (b : T ⟶ X.toScheme)
    (h : a ≫ p ≫ X.ι ≫ π = b ≫ X.ι ≫ π) (hab : a ≫ p ≫ X.ι ≫ σ = b ≫ X.ι)
    (l : T ⟶ (involutionOverlap σ X p).toScheme) (hl : l ≫ (involutionOverlap σ X p).ι = a) :
    involutionMove hπ ρ a b h = l ≫ ρ ≫ (involutionOverlap σ X p).ι := by
  have hm : pullback.lift a b h ≫ involutionSplit hπ =
      (a ≫ p ≫ X.ι) ≫ (coprod.inr : Y ⟶ Y ⨿ Y) := by
    apply hπ.hom_ext
    · simp only [Category.assoc, involutionSplit_desc_id, pullback.lift_fst_assoc,
        coprod.inr_desc, Category.comp_id]
    · simp only [Category.assoc, involutionSplit_desc_sigma, pullback.lift_snd_assoc,
        coprod.inr_desc, hab]
  have hg : pullback.lift a b h =
      pullback.lift (pullback.lift a b h) (a ≫ p ≫ X.ι) hm ≫ pullback.fst _ _ :=
    (pullback.lift_fst _ _ _).symm
  have key : pullback.lift (pullback.lift a b h) (a ≫ p ≫ X.ι) hm ≫
      liftInvolutionOverlap _ _ (involutionSplit_inr hπ) = l := by
    rw [← cancel_mono (involutionOverlap σ X p).ι, Category.assoc, liftInvolutionOverlap_ι, hl,
      ← Category.assoc, ← hg, pullback.lift_fst]
  rw [involutionMove, hg, Category.assoc, involutionGluingMap_inr, ← Category.assoc, key]

/-- The moved point lies over the given point of `X`. -/
@[reassoc]
lemma involutionMove_comp {T : Scheme.{u}} (a : T ⟶ W) (b : T ⟶ X.toScheme)
    (h : a ≫ p ≫ X.ι ≫ π = b ≫ X.ι ≫ π)
    (hρ : ρ ≫ (involutionOverlap σ X p).ι ≫ p ≫ X.ι =
      (involutionOverlap σ X p).ι ≫ p ≫ X.ι ≫ σ) :
    involutionMove hπ ρ a b h ≫ p = b := by
  refine hom_ext_of_isPullback_coprodDesc hπ (a ≫ p ≫ X.ι) (b ≫ X.ι)
    (by simpa only [Category.assoc] using h) (fun T' k hk ↦ ?_) (fun T' k hk ↦ ?_)
  · have hk' : (k ≫ a) ≫ p ≫ X.ι = (k ≫ b) ≫ X.ι := by
      simpa only [Category.assoc] using hk
    rw [comp_involutionMove_assoc, involutionMove_eq_self (k ≫ a) (k ≫ b) _ hk',
      ← cancel_mono X.ι]
    simpa only [Category.assoc] using hk'
  · have hk' : (k ≫ a) ≫ p ≫ X.ι ≫ σ = (k ≫ b) ≫ X.ι := by
      simpa only [Category.assoc] using hk
    rw [comp_involutionMove_assoc, involutionMove_eq_rho (k ≫ a) (k ≫ b) _ hk'
      (liftInvolutionOverlap _ _ hk') (liftInvolutionOverlap_ι _ _ hk'), ← cancel_mono X.ι]
    simp only [Category.assoc, hρ, liftInvolutionOverlap_ι_assoc]
    simpa only [Category.assoc] using hk'

/-- **The operation is invariant under `ρ`**: moving `ρ w` and moving `w` give the same
point. -/
lemma involutionMove_rho {T : Scheme.{u}} (l : T ⟶ (involutionOverlap σ X p).toScheme)
    (c : T ⟶ X.toScheme)
    (h₁ : (l ≫ ρ ≫ (involutionOverlap σ X p).ι) ≫ p ≫ X.ι ≫ π = c ≫ X.ι ≫ π)
    (h₂ : (l ≫ (involutionOverlap σ X p).ι) ≫ p ≫ X.ι ≫ π = c ≫ X.ι ≫ π)
    (hσ : σ ≫ σ = 𝟙 Y)
    (hρ : ρ ≫ (involutionOverlap σ X p).ι ≫ p ≫ X.ι =
      (involutionOverlap σ X p).ι ≫ p ≫ X.ι ≫ σ) (hρρ : ρ ≫ ρ = 𝟙 _) :
    involutionMove hπ ρ (l ≫ ρ ≫ (involutionOverlap σ X p).ι) c h₁ =
      involutionMove hπ ρ (l ≫ (involutionOverlap σ X p).ι) c h₂ := by
  refine hom_ext_of_isPullback_coprodDesc hπ
    (l ≫ (involutionOverlap σ X p).ι ≫ p ≫ X.ι) (c ≫ X.ι)
    (by simpa only [Category.assoc] using h₂) (fun T' k hk ↦ ?_) (fun T' k hk ↦ ?_)
  · have hk₁ : (k ≫ l ≫ (involutionOverlap σ X p).ι) ≫ p ≫ X.ι = (k ≫ c) ≫ X.ι := by
      simpa only [Category.assoc] using hk
    have hk₂ : (k ≫ l ≫ ρ ≫ (involutionOverlap σ X p).ι) ≫ p ≫ X.ι ≫ σ =
        (k ≫ c) ≫ X.ι := by
      simp only [Category.assoc, reassoc_of% hρ, hσ, Category.comp_id]
      simpa only [Category.assoc] using hk
    rw [comp_involutionMove, comp_involutionMove,
      involutionMove_eq_self (k ≫ l ≫ (involutionOverlap σ X p).ι) (k ≫ c) _ hk₁,
      involutionMove_eq_rho (k ≫ l ≫ ρ ≫ (involutionOverlap σ X p).ι) (k ≫ c) _ hk₂
        (k ≫ l ≫ ρ) (by simp only [Category.assoc])]
    simp only [Category.assoc, reassoc_of% hρρ]
  · have hk₁ : (k ≫ l ≫ (involutionOverlap σ X p).ι) ≫ p ≫ X.ι ≫ σ = (k ≫ c) ≫ X.ι := by
      simpa only [Category.assoc] using hk
    have hk₂ : (k ≫ l ≫ ρ ≫ (involutionOverlap σ X p).ι) ≫ p ≫ X.ι = (k ≫ c) ≫ X.ι := by
      simp only [Category.assoc, hρ]
      simpa only [Category.assoc] using hk
    rw [comp_involutionMove, comp_involutionMove,
      involutionMove_eq_rho (k ≫ l ≫ (involutionOverlap σ X p).ι) (k ≫ c) _ hk₁
        (k ≫ l) (by simp only [Category.assoc]),
      involutionMove_eq_self (k ≫ l ≫ ρ ≫ (involutionOverlap σ X p).ι) (k ≫ c) _ hk₂]
    simp only [Category.assoc]

/-- **Moving twice is moving once.** -/
lemma involutionMove_involutionMove {T : Scheme.{u}} (a : T ⟶ W) (b c : T ⟶ X.toScheme)
    (h : a ≫ p ≫ X.ι ≫ π = b ≫ X.ι ≫ π)
    (h' : involutionMove hπ ρ a b h ≫ p ≫ X.ι ≫ π = c ≫ X.ι ≫ π)
    (h'' : a ≫ p ≫ X.ι ≫ π = c ≫ X.ι ≫ π)
    (hσ : σ ≫ σ = 𝟙 Y)
    (hρ : ρ ≫ (involutionOverlap σ X p).ι ≫ p ≫ X.ι =
      (involutionOverlap σ X p).ι ≫ p ≫ X.ι ≫ σ) (hρρ : ρ ≫ ρ = 𝟙 _) :
    involutionMove hπ ρ (involutionMove hπ ρ a b h) c h' = involutionMove hπ ρ a c h'' := by
  refine hom_ext_of_isPullback_coprodDesc hπ (a ≫ p ≫ X.ι) (b ≫ X.ι)
    (by simpa only [Category.assoc] using h) (fun T' k hk ↦ ?_) (fun T' k hk ↦ ?_)
  · have hk' : (k ≫ a) ≫ p ≫ X.ι = (k ≫ b) ≫ X.ι := by
      simpa only [Category.assoc] using hk
    rw [comp_involutionMove k (involutionMove hπ ρ a b h) c, comp_involutionMove k a c]
    refine involutionMove_congr ?_ rfl
    rw [comp_involutionMove, involutionMove_eq_self (k ≫ a) (k ≫ b) _ hk']
  · have hk' : (k ≫ a) ≫ p ≫ X.ι ≫ σ = (k ≫ b) ≫ X.ι := by
      simpa only [Category.assoc] using hk
    let L := liftInvolutionOverlap _ _ hk'
    have hL : L ≫ (involutionOverlap σ X p).ι = k ≫ a := liftInvolutionOverlap_ι _ _ hk'
    have e : k ≫ involutionMove hπ ρ a b h = L ≫ ρ ≫ (involutionOverlap σ X p).ι :=
      (comp_involutionMove k a b h).trans (involutionMove_eq_rho _ _ _ hk' L hL)
    have h₁ : (L ≫ ρ ≫ (involutionOverlap σ X p).ι) ≫ p ≫ X.ι ≫ π = (k ≫ c) ≫ X.ι ≫ π := by
      rw [← e]
      simp only [Category.assoc, h']
    have h₂ : (L ≫ (involutionOverlap σ X p).ι) ≫ p ≫ X.ι ≫ π = (k ≫ c) ≫ X.ι ≫ π := by
      rw [hL]
      simp only [Category.assoc, h'']
    rw [comp_involutionMove k (involutionMove hπ ρ a b h) c, comp_involutionMove k a c]
    exact (involutionMove_congr (h' := h₁) e rfl).trans
      ((involutionMove_rho L (k ≫ c) h₁ h₂ hσ hρ hρρ).trans (involutionMove_congr hL rfl))

end Gluing

/-! ### The descent datum -/

section Datum

variable {Y S : Scheme.{u}} (π : Y ⟶ S) (σ : Y ⟶ Y) (hσ : σ ≫ σ = 𝟙 Y)
  (hπ : IsPullback (coprod.desc (𝟙 Y) (𝟙 Y)) (coprod.desc (𝟙 Y) σ) π π)
  (X : Y.Opens) {W : Scheme.{u}} (p : W ⟶ X.toScheme)
  (ρ : (involutionOverlap σ X p).toScheme ⟶ (involutionOverlap σ X p).toScheme)
  (hρ : ρ ≫ (involutionOverlap σ X p).ι ≫ p ≫ X.ι =
    (involutionOverlap σ X p).ι ≫ p ≫ X.ι ≫ σ)
  (hρρ : ρ ≫ ρ = 𝟙 _)

/-- The descent transport for `W` relative to `X ⟶ S` determined by the involution `ρ`: a
point `(w, x)` of `W ×_S X` goes to `w` when `p w = x` and to `ρ w` when `σ (p w) = x`. -/
def involutionTransport : DescentTransport (structureMap (X.ι ≫ π) (Over.mk p)) where
  move {T} a b := Over.homMk
    (involutionMove hπ ρ a.left b.left ((Over.w a).trans (Over.w b).symm)) (by
      change involutionMove hπ ρ a.left b.left _ ≫ p ≫ X.ι ≫ π = T.hom
      rw [involutionMove_comp_assoc _ _ _ hρ]
      exact Over.w b)
  base a b := Over.OverMorphism.ext (involutionMove_comp _ _ _ hρ)
  refl a := Over.OverMorphism.ext (involutionMove_eq_self _ _ _ (by
    rw [Over.comp_left, Category.assoc]
    rfl))
  trans a b c := Over.OverMorphism.ext (involutionMove_involutionMove _ _ _ _ _ _ hσ hρ hρρ)
  naturality f a b := Over.OverMorphism.ext (by
    rw [Over.comp_left]
    exact (comp_involutionMove _ _ _ _).trans
      (involutionMove_congr (by rw [Over.comp_left]) (by rw [Over.comp_left])))

/-- **The descent datum of an involution.** The descent datum for `W` relative to
`X ⟶ Y ⟶ S` whose gluing sends `(w, x)` to `(x, w)` when `p w = x`, and to `(x, ρ w)` when
`σ (p w) = x`. -/
def involutionDatum :
    DescentData (S := S) (X := fun _ : Unit ↦ X.toScheme) (fun _ ↦ X.ι ≫ π) :=
  transportDescentData (X.ι ≫ π) (Over.mk p) (involutionTransport π σ hσ hπ X p ρ hρ hρρ)

/-- The scheme of `AlgebraicGeometry.involutionDatum` is `W` over `X`. -/
@[simp]
lemma involutionDatum_obj : (involutionDatum π σ hσ hπ X p ρ hρ hρρ).obj () = Over.mk p :=
  rfl

/-- **Effectivity of the involution datum.** If `AlgebraicGeometry.involutionDatum` is
effective, then `W` is the base change along `X ⟶ S` of a scheme `U` over `S`, and the
projection `W ⟶ U` is invariant under `ρ` on the overlap. -/
theorem exists_isPullback_of_isEffective_involutionDatum
    (hD : (involutionDatum π σ hσ hπ X p ρ hρ hρρ).IsEffective) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (Φ : W ⟶ U), IsPullback Φ p g (X.ι ≫ π) ∧
      (involutionOverlap σ X p).ι ≫ Φ = ρ ≫ (involutionOverlap σ X p).ι ≫ Φ := by
  obtain ⟨Q⟩ := DescentDatum.nonempty_descended_of_isEffective hD
  refine ⟨Q.base.left, Q.base.hom, Q.proj, Q.isPullback.flip, ?_⟩
  have hσπ : σ ≫ π = π := by
    have h := coprod.inr ≫= hπ.w
    simp only [coprod.inr_desc_assoc, Category.id_comp] at h
    exact h.symm
  let v : Over.mk ((involutionOverlap σ X p).ι ≫ p ≫ X.ι ≫ π) ⟶
      (Over.map (X.ι ≫ π)).obj (Over.mk p) := Over.homMk (involutionOverlap σ X p).ι rfl
  let x : Over.mk ((involutionOverlap σ X p).ι ≫ p ≫ X.ι ≫ π) ⟶ Over.mk (X.ι ≫ π) :=
    Over.homMk (ρ ≫ (involutionOverlap σ X p).ι ≫ p) (by
      simp only [Over.mk_hom, Category.assoc, reassoc_of% hρ, hσπ])
  have h := Q.proj_act v x
  have hact : DescentDatum.act (involutionDatum π σ hσ hπ X p ρ hρ hρρ) v x =
      (involutionTransport π σ hσ hπ X p ρ hρ hρρ).move v x :=
    transportDescentData_act _ _ _ v x
  have hm : ((involutionTransport π σ hσ hπ X p ρ hρ hρρ).move v x).left =
      ρ ≫ (involutionOverlap σ X p).ι :=
    (involutionMove_eq_rho (involutionOverlap σ X p).ι (ρ ≫ (involutionOverlap σ X p).ι ≫ p)
      _ (by simp only [Category.assoc, hρ]) (𝟙 _) (Category.id_comp _)).trans
      (Category.id_comp _)
  rw [hact, hm] at h
  exact ((Category.assoc ρ (involutionOverlap σ X p).ι Q.proj).symm.trans h).symm

end Datum

end AlgebraicGeometry

end
