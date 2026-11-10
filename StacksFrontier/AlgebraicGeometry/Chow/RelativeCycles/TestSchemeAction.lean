module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionPushPull
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeRelative
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CompositionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CompositionPushPull

/-!
# The operation `g^*α ∩ -` of a family of cycles on every test scheme

Let `(S, δ)` be a Chow situation, let `p : X ⟶ Y` be a morphism of schemes locally of finite type
over `S`, let `r ≥ 0` and let `α` be a family of `r`-cycles on the fibres of `X/Y`. For every
morphism `g : Y' ⟶ Y` locally of finite type and every `k ∈ ℤ` Stacks 0H6F considers the operation

  `g^*α ∩ - : Z_k(Y') ⟶ Z_{r + k}(X')`,   `X' = Y' ×_Y X`,

where `g^*α` is the base change of `α` along `g` (Section 0H4N) and `∩` is the action of
Section 0H65. This file defines that operation, read on the chosen fibre product `pullback p g`
with structure morphism `pullback.fst p g ≫ p ≫ sY` — the spelling in which
`Stacks.Chow.BivariantClass` states its cap operations — and proves that it commutes with proper
pushforward and with flat pullback along morphisms of test schemes, on cycles.

## Main definitions

* `Stacks.Chow.relativeCycleCap` — the operation `g^*α ∩ -` on the cycles of a test scheme.

## Main results

* `Stacks.Chow.relativeCycleCap_apply` — its coefficients are those of the action of
  Section 0H65.
* `Stacks.Chow.relativeCycleCap_comp_apply` — on a test scheme `T' ⟶ T ⟶ Y` the operation is the
  action of the base change of the family over `T`, read through the pasting isomorphism.
* `Stacks.Chow.properPushforward_relativeCycleCap` — the operation commutes with proper pushforward
  along a proper morphism of test schemes (Stacks 0H6B).
* `Stacks.Chow.relativeCycleCap_flatPullback_apply` — the operation commutes with flat pullback
  along a flat morphism of test schemes (Stacks 0H68).

## References

* [Stacks Project, Tag 0H6F](https://stacks.math.columbia.edu/tag/0H6F)
* [Stacks Project, Tag 0H6B](https://stacks.math.columbia.edu/tag/0H6B)
* [Stacks Project, Tag 0H68](https://stacks.math.columbia.edu/tag/0H68)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Membership in a cycle group depends on the structure morphism and the degree only through
their values. -/
theorem mem_cyclesOfDimension_congr (C : ChowSituation.{u}) {X : Scheme.{u}} {f f' : X ⟶ C.S}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (hf : f = f') {k k' : ℤ} (hk : k = k')
    (c : AlgebraicCycle X ℤ) :
    c ∈ cyclesOfDimension C f k ↔ c ∈ cyclesOfDimension C f' k' := by
  subst hf hk
  rfl

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ) (α : FamilyOfCycles p r)

/-- **Stacks 0H6F, the operation on cycles.** For a test scheme `g : T ⟶ Y` locally of finite type
and `k ∈ ℤ`, the operation `g^*α ∩ - : Z_k(T) ⟶ Z_{r + k}(T ×_Y X)`: the action of the base change
`g^*α` (`Stacks.Chow.baseChangeFamily`) on cycles of `T` (`Stacks.Chow.cap`), read on the chosen
fibre product `pullback p g` over the base through `pullback.fst p g ≫ p ≫ sY`. -/
def relativeCycleCap {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) :
    CycleGroup C (g ≫ sY) k →+ CycleGroup C (pullback.fst p g ≫ p ≫ sY) ((r : ℤ) + k) where
  toFun β := ⟨(cap C (g ≫ sY) (pullback.snd p g) (baseChangeFamily p g r α) β).1,
    (mem_cyclesOfDimension_congr C (pullbackFst_comp_eq g rfl).symm rfl _).1
      (cap C (g ≫ sY) (pullback.snd p g) (baseChangeFamily p g r α) β).2⟩
  map_zero' := by
    apply Subtype.ext
    have h := congrArg Subtype.val (cap_zero_right C (g ≫ sY) (pullback.snd p g) r k
      (baseChangeFamily p g r α))
    exact h
  map_add' β₁ β₂ := by
    apply Subtype.ext
    have h := congrArg Subtype.val (cap_add_right C (g ≫ sY) (pullback.snd p g)
      (baseChangeFamily p g r α) β₁ β₂)
    exact h

/-- The underlying cycle of `g^*α ∩ β` is the action of Section 0H65. -/
theorem relativeCycleCap_val {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (β : CycleGroup C (g ≫ sY) k) :
    (relativeCycleCap C sY p r α g k β).1 =
      (cap C (g ≫ sY) (pullback.snd p g) (baseChangeFamily p g r α) β).1 :=
  rfl

/-- The coefficients of `g^*α ∩ β`. -/
theorem relativeCycleCap_apply {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (β : CycleGroup C (g ≫ sY) k) (x : ↥(pullback p g)) :
    (relativeCycleCap C sY p r α g k β).1 x =
      capCoeff (pullback.snd p g) (baseChangeFamily p g r α) β.1 x :=
  rfl

/-- The operation is additive in the family. -/
theorem relativeCycleCap_add_family {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (α₁ α₂ : FamilyOfCycles p r) (β : CycleGroup C (g ≫ sY) k) :
    relativeCycleCap C sY p r (α₁ + α₂) g k β =
      relativeCycleCap C sY p r α₁ g k β + relativeCycleCap C sY p r α₂ g k β := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  change capCoeff (pullback.snd p g) (baseChangeFamily p g r (α₁ + α₂)) β.1 x =
    capCoeff (pullback.snd p g) (baseChangeFamily p g r α₁) β.1 x +
      capCoeff (pullback.snd p g) (baseChangeFamily p g r α₂) β.1 x
  rw [baseChangeFamily_add]
  simp [capCoeff, mul_add]

/-! ### Composite test schemes -/

/-- On a composite test scheme `T' ⟶ T ⟶ Y` the coefficients of the operation are those of the
action of the base change over `T` of `g^*α`, read through the pasting isomorphism
`pullback p (h ≫ g) ≅ pullback (pullback.snd p g) h`. -/
theorem relativeCycleCap_comp_apply {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (h : T' ⟶ T) [LocallyOfFiniteType h] (k : ℤ) (β : CycleGroup C ((h ≫ g) ≫ sY) k)
    (x : ↥(pullback p (h ≫ g))) :
    (relativeCycleCap C sY p r α (h ≫ g) k β).1 x =
      capCoeff (pullback.snd (pullback.snd p g) h)
        (baseChangeFamily (pullback.snd p g) h r (baseChangeFamily p g r α)) β.1
        ((pullbackLeftPullbackSndIso p g h).inv x) :=
  capCoeff_baseChangeFamily_comp' p g h r α
    (fun t ↦ baseChangeFamily_baseChangeFamily_of_locallyOfFiniteType p g h r α t) β.1 x

omit [LocallyOfFiniteType p] in
/-- The comparison morphism `pullback p (h ≫ g) ⟶ pullback p g` of a cartesian square of test
schemes is the pasting isomorphism followed by the first projection. -/
theorem pullbackLeftPullbackSndIso_inv_fst_eq {T T' : Scheme.{u}} (g : T ⟶ Y) (h : T' ⟶ T)
    (h' : pullback p (h ≫ g) ⟶ pullback p g)
    (sq : IsPullback (pullback.snd p (h ≫ g)) h' h (pullback.snd p g))
    (hfst : h' ≫ pullback.fst p g = pullback.fst p (h ≫ g)) :
    (pullbackLeftPullbackSndIso p g h).inv ≫ pullback.fst (pullback.snd p g) h = h' := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst, hfst]
  · rw [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd, sq.w]

/-! ### Proper pushforward -/

/-- **Stacks 0H6B for the operation on test schemes.** Let `h : T' ⟶ T` be a proper morphism of
test schemes over `g : T ⟶ Y` and let `h' : T' ×_Y X ⟶ T ×_Y X` be the base change of `h`. Then
`h'_*((h ≫ g)^*α ∩ β) = g^*α ∩ h_*β` for every cycle `β` on `T'`. -/
theorem properPushforward_relativeCycleCap {T T' : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (h' : pullback p (h ≫ g) ⟶ pullback p g)
    [IsProper h'] (sq : IsPullback (pullback.snd p (h ≫ g)) h' h (pullback.snd p g))
    (hfst : h' ≫ pullback.fst p g = pullback.fst p (h ≫ g)) (k : ℤ)
    (β : CycleGroup C ((h ≫ g) ≫ sY) k) :
    properPushforward C (pullback.fst p (h ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY) h'
        (by rw [← Category.assoc, hfst]) ((r : ℤ) + k)
        (relativeCycleCap C sY p r α (h ≫ g) k β) =
      relativeCycleCap C sY p r α g k
        (properPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) k β) := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have h6B := properPushforward_cap_baseChangeFamily C (pullback.snd p g ≫ g ≫ sY) (g ≫ sY)
    ((h ≫ g) ≫ sY) (pullback.snd p g) h rfl (by simp [Category.assoc]) r k
    (baseChangeFamily p g r α) β
  have hy := congrArg (fun z : CycleGroup C (pullback.snd p g ≫ g ≫ sY) ((r : ℤ) + k) ↦ z.1 y)
    h6B
  simp only at hy
  have hg : h ≫ g ≫ sY = (h ≫ g) ≫ sY := by simp [Category.assoc]
  refine (properPushforward_congr_iso C _ _ (pullback.snd (pullback.snd p g) h ≫ (h ≫ g) ≫ sY)
    (pullback.snd p g ≫ g ≫ sY) h' (pullback.fst (pullback.snd p g) h)
    (by rw [← Category.assoc, hfst]) (pullbackFst_comp_eq_of_base h rfl hg)
    (pullbackLeftPullbackSndIso p g h).symm (Iso.refl _) ?_ ?_ ?_ ((r : ℤ) + k) ((r : ℤ) + k)
    (relativeCycleCap C sY p r α (h ≫ g) k β)
    (cap C ((h ≫ g) ≫ sY) (pullback.snd (pullback.snd p g) h)
      (baseChangeFamily (pullback.snd p g) h r (baseChangeFamily p g r α)) β) ?_ y).trans ?_
  · rw [Iso.symm_hom, ← Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
    exact (pullbackFst_comp_eq (h ≫ g) rfl).symm
  · rw [Iso.refl_hom, Category.id_comp]
    exact pullbackFst_comp_eq g rfl |>.symm
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
    exact (pullbackLeftPullbackSndIso_inv_fst_eq p g h h' sq hfst).symm
  · intro x
    exact relativeCycleCap_comp_apply C sY p r α g h k β x
  · exact hy

/-! ### Flat pullback -/

/-- Flat pullback of cycles depends on the structure morphism of the source only through its
value. -/
theorem flatPullback_val_congr_source (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA'] (hsA : sA = sA')
    (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (w : A ⟶ B) [LocallyOfFiniteType w] [Flat w]
    (hw : w ≫ sB = sA) (hw' : w ≫ sB = sA') (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension w d)
    (k : ℤ) (c : CycleGroup C sB k) :
    (flatPullback C sA sB w hw d hd k c).1 = (flatPullback C sA' sB w hw' d hd k c).1 := by
  subst hsA
  rfl

/-- **Stacks 0H68 for the operation on test schemes.** Let `h : T' ⟶ T` be a flat morphism of test
schemes over `g : T ⟶ Y`, of relative dimension `d`, and let `h' : T' ×_Y X ⟶ T ×_Y X` be its base
change. Then `(h ≫ g)^*α ∩ h^*β = h'^*(g^*α ∩ β)` for every cycle `β` on `T`, coefficientwise. -/
theorem relativeCycleCap_flatPullback_apply {T T' : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension h d) (h' : pullback p (h ≫ g) ⟶ pullback p g)
    [LocallyOfFiniteType h'] [Flat h'] (hd' : AlgebraicGeometry.RelativeDimension h' d)
    (sq : IsPullback (pullback.snd p (h ≫ g)) h' h (pullback.snd p g))
    (hfst : h' ≫ pullback.fst p g = pullback.fst p (h ≫ g)) (k : ℤ)
    (β : CycleGroup C (g ≫ sY) k) (x : ↥(pullback p (h ≫ g))) :
    (relativeCycleCap C sY p r α (h ≫ g) (k + (d : ℤ))
        (flatPullback C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) d hd k β)).1 x =
      (flatPullback C (pullback.fst p (h ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY) h'
        (by rw [← Category.assoc, hfst]) d hd' ((r : ℤ) + k) (relativeCycleCap C sY p r α g k β)).1
        x := by
  set i := (pullbackLeftPullbackSndIso p g h).inv with hi
  have hhi : i ≫ pullback.fst (pullback.snd p g) h = h' :=
    pullbackLeftPullbackSndIso_inv_fst_eq p g h h' sq hfst
  have h68 := congrArg (fun z : AlgebraicCycle (pullback (pullback.snd p g) h : Scheme.{u}) ℤ ↦
      z (i x))
    (cap_flatPullback C (g ≫ sY) (pullback.snd p g) h d hd r k (baseChangeFamily p g r α) β)
  simp only at h68
  rw [relativeCycleCap_comp_apply,
    flatPullback_val_congr_source C (Category.assoc h g sY) (g ≫ sY) h _ rfl d hd k β]
  refine h68.trans ?_
  rw [flatPullback_apply, flatPullback_apply]
  have hpt : (pullback.fst (pullback.snd p g) h).base (i.base x) = h'.base x := by
    rw [← hhi]
    rfl
  rw [hpt, flatPullbackWeight_eq_of_isIso C (pullback.fst p (h ≫ g) ≫ p ≫ sY)
    (pullback.snd (pullback.snd p g) h ≫ h ≫ g ≫ sY) (𝟙 _) i ?_ h'
    (pullback.fst (pullback.snd p g) h) (by rw [Category.comp_id, hhi]) _ x]
  · rfl
  · rw [hi, ← Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
    exact (pullbackFst_comp_eq (h ≫ g) rfl).symm

end Stacks.Chow

end
