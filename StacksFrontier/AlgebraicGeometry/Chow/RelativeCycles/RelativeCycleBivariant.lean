module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VeryWeakBivariantCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GysinAction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.TestSchemeAction

/-!
# The operation of a relative cycle on Chow groups

Let `(S, δ)` be as in Section 0H65, let `p : X ⟶ Y` be a morphism of schemes locally of finite
type over `S`, let `r ≥ 0` and let `α ∈ z(X/Y, r)` be a relative `r`-cycle. Stacks 0H6F says that
the rule `g ↦ g^*α ∩ -` on the cycles of the test schemes `g : Y' ⟶ Y` factors through rational
equivalence. The source's proof is Stacks 0H6E together with Stacks 0B7A: the operation commutes
with the Gysin map of every divisor whose invertible module is trivial on it, and an operation on
cycles with that property kills rational equivalences. This file carries out that step and proves
that the descended operation commutes with proper pushforward and with flat pullback.

## Main definitions

* `Stacks.Chow.relativeCycleCapRule` — the rule `g ↦ g^*α ∩ -` as a very weak cap rule of degree
  `-r` (Stacks 0B7A).
* `Stacks.Chow.relativeCycleCapChow` — the descended operation `A_k(Y') ⟶ A_{k+r}(X')`.

## Main results

* `Stacks.Chow.relativeCycleCap_gysinCycleMapPushforward` — Stacks 0H6E on a test scheme, read in
  `X'`: `g^*α ∩ i_* i^* β = j_* j^*(g^*α ∩ β)` for a divisor with trivial invertible module.
* `Stacks.Chow.isCycleGysinNatural_relativeCycleCapRule` — condition (3) of Stacks 0B76 for
  divisors with trivial invertible module, the hypothesis of Stacks 0B7A.
* `Stacks.Chow.relativeCycleCapChow_mk` — the descended operation on the class of a cycle.
* `Stacks.Chow.relativeCycleCapChow_properPushforward`,
  `Stacks.Chow.relativeCycleCapChow_flatPullbackChow` — conditions (1) and (2) of Stacks 0B76.

## References

* [Stacks Project, Tag 0H6F](https://stacks.math.columbia.edu/tag/0H6F)
* [Stacks Project, Tag 0H6E](https://stacks.math.columbia.edu/tag/0H6E)
* [Stacks Project, Tag 0B7A](https://stacks.math.columbia.edu/tag/0B7A)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Transporting the class of a cycle along an equality of degrees is the class of the transported
cycle. -/
theorem eqMp_chowGroup_mk (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
    [LocallyOfFiniteType q] {m n : ℤ} (h : m = n) (z : CycleGroup C q m) :
    Eq.mp (congrArg (chowGroup C q) h) (QuotientAddGroup.mk' (rationalEquivalences C q m) z) =
      QuotientAddGroup.mk' (rationalEquivalences C q n) (cycleGroupCongr C q h z) := by
  subst h
  rfl

/-- The composite `i_* ∘ i^*` does not see how the degree is written. -/
theorem gysinCycleMapPushforward_val_congr_degree (C : ChowSituation.{u}) {X : Scheme.{u}}
    (q : X ⟶ C.S) [LocallyOfFiniteType q] {k k' : ℤ} (hk : k = k') (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))
    (β : CycleGroup C q (k + 1)) (β' : CycleGroup C q (k' + 1)) (h : β.1 = β'.1) :
    (gysinCycleMapPushforward C q k L s htriv β).1 =
      (gysinCycleMapPushforward C q k' L s htriv β').1 := by
  subst hk
  rw [Subtype.ext h]

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ) (α : FamilyOfCycles p r)

/-! ### Stacks 0H6E on a test scheme -/

/-- **Stacks 0H6E on a test scheme, read in `X' = T ×_Y X`.** Let `g : T ⟶ Y` be a test scheme, let
`L` be an invertible module on `T` and `s` a global section whose zero scheme `D` carries a trivial
restriction of `L`, and let `E` be the zero scheme of the pulled-back section on `X'`. Then
`g^*α ∩ i_* i^* β = j_* j^*(g^*α ∩ β)` for every `β ∈ Z_{k+1}(T)`. -/
theorem relativeCycleCap_gysinCycleMapPushforward
    (hα : letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      IsRelativeCycle p r α)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme T L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L s).subschemeι).obj L))
    (k : ℤ) (β : CycleGroup C (g ≫ sY) (k + 1)) :
    relativeCycleCap C sY p r α g k (gysinCycleMapPushforward C (g ≫ sY) k L s htriv β) =
      gysinCycleMapPushforward C (pullback.fst p g ≫ p ≫ sY) ((r : ℤ) + k)
        (bivariantPullbackModule p g L) (bivariantPullbackSection p g L s)
        (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
          (pullback.snd p g) L s htriv)
        (cycleGroupCongr C _ (by ring) (relativeCycleCap C sY p r α g (k + 1) β)) := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
  have hαT := isRelativeCycle_baseChangeFamily p g r hα
  have h := capCommutesWithGysin_of_isRelativeCycle C (g ≫ sY) (pullback.snd p g) r k L s htriv
    (bivariantPullbackModule p g L) (bivariantPullbackSection p g L s)
    (Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections
      (pullback.snd p g) L s htriv)
    (Stacks.Divisors.zeroScheme_pullback (pullback.snd p g) L s) (baseChangeFamily p g r α)
    hαT β
  apply Subtype.ext
  refine (congrArg Subtype.val h).trans ?_
  exact gysinCycleMapPushforward_congr C _ _ _ _ _ _ (pullbackFst_comp_eq g rfl).symm _ _ rfl

/-! ### The rule of Stacks 0B7A -/

/-- **Stacks 0H6F, the rule.** The operation `g ↦ g^*α ∩ -` followed by the passage to Chow groups,
as a very weak cap rule of degree `-r` for `p` in the sense of Stacks 0B7A. -/
def relativeCycleCapRule : VeryWeakCapRule C (p ≫ sY) sY p rfl (-(r : ℤ)) where
  cap := fun g _ k ↦ (QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst p g ≫ p ≫ sY)
      (k - -(r : ℤ)))).comp
    ((cycleGroupCongr C _ (by ring)).toAddMonoidHom.comp (relativeCycleCap C sY p r α g k))

/-- The cap of `relativeCycleCapRule` on a cycle `β` on `T` is the class modulo rational
equivalence of `g^*α ∩ β`. -/
theorem relativeCycleCapRule_cap {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (β : CycleGroup C (g ≫ sY) k) :
    (relativeCycleCapRule C sY p r α).cap g k β =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst p g ≫ p ≫ sY) (k - -(r : ℤ)))
        (cycleGroupCongr C _ (by ring) (relativeCycleCap C sY p r α g k β)) :=
  rfl

/-- The pushforward along a closed immersion `i` presenting the zero scheme of `s` of the Gysin map
read along `i` is the pushforward of the canonical Gysin map. -/
theorem properPushforward_gysinCycleMapAlong_eq {T D : Scheme.{u}} (q : T ⟶ C.S)
    [LocallyOfFiniteType q] (k : ℤ) (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (s : Γ(L, ⊤))
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme T L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme T L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme T L s).subschemeι).obj L))
    (i : D ⟶ T) [IsClosedImmersion i] (qD : D ⟶ C.S) [LocallyOfFiniteType qD] (hq : i ≫ q = qD)
    (hker : i.ker = Stacks.Divisors.zeroScheme T L s) (β : CycleGroup C q (k + 1)) :
    properPushforward C qD q i hq k (gysinCycleMapAlong C q qD k L s i htriv hq hker β) =
      gysinCycleMapPushforward C q k L s htriv β := by
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_ker_eq i _ hker
  rw [gysinCycleMapPushforward_apply, ← properPushforward_gysinCycleMapAlong C q k L s htriv qD i
    hq hker e he β]
  have h := congrFun (properPushforward_comp C qD
    ((Stacks.Divisors.zeroScheme T L s).subschemeι ≫ q) q e.hom
    (Stacks.Divisors.zeroScheme T L s).subschemeι (by rw [← Category.assoc, he, hq]) rfl k)
    (gysinCycleMapAlong C q qD k L s i htriv hq hker β)
  simp only [Function.comp_apply] at h
  rw [h]
  congr 1
  exact he.symm

/-- **Condition (3) of Stacks 0B76 for divisors with trivial invertible module**, the hypothesis
of Stacks 0B7A, for the rule `g ↦ g^*α ∩ -` of a relative cycle. This is Stacks 0H6E. -/
theorem isCycleGysinNatural_relativeCycleCapRule
    (hα : letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
      IsRelativeCycle p r α) :
    (relativeCycleCapRule C sY p r α).IsCycleGysinNatural := by
  intro T g _ k β
  refine ⟨cycleGroupCongr C _ (by ring) (relativeCycleCap C sY p r α g (k + 1) β), ?_, ?_⟩
  · rw [relativeCycleCapRule_cap, eqMp_chowGroup_mk C _ (by omega)]
    rfl
  intro D L _ s htriv i _ hker gZ _ hgZ φ he₁ he₂ hfac
  subst hgZ
  rw [relativeCycleCapRule_cap, properChowPushforward_mk]
  congr 1
  apply properPushforward_injective_of_isClosedImmersion C _ (pullback.fst p g ≫ p ≫ sY)
    (bivariantPullbackZeroScheme p g L s).subschemeι rfl
  have hmap : φ.hom ≫ (bivariantPullbackZeroScheme p g L s).subschemeι =
      bivariantBaseChangeMap p g i := he₁
  have hpush := congrFun (properPushforward_comp C (pullback.fst p (i ≫ g) ≫ p ≫ sY)
    ((bivariantPullbackZeroScheme p g L s).subschemeι ≫ pullback.fst p g ≫ p ≫ sY)
    (pullback.fst p g ≫ p ≫ sY) φ.hom (bivariantPullbackZeroScheme p g L s).subschemeι
    he₂ rfl (k - -(r : ℤ)))
    (cycleGroupCongr C _ (by ring) (relativeCycleCap C sY p r α (i ≫ g) k
      (gysinCycleMapAlong C (g ≫ sY) ((i ≫ g) ≫ sY) k L s i htriv
        (by rw [← Category.assoc]) hker β)))
  simp only [Function.comp_apply] at hpush
  rw [hpush]
  apply Subtype.ext
  rw [properPushforward_congr C _ _ _ _ hmap _ (by rw [← hmap]; exact he₂)]
  have hprop := properPushforward_relativeCycleCap C sY p r α g i (bivariantBaseChangeMap p g i)
    (isPullback_bivariantBaseChangeMap p g i) (by simp) k
    (gysinCycleMapAlong C (g ≫ sY) ((i ≫ g) ≫ sY) k L s i htriv (by rw [← Category.assoc]) hker β)
  rw [properPushforward_gysinCycleMapAlong_eq,
    relativeCycleCap_gysinCycleMapPushforward C sY p r α hα g L s htriv k β] at hprop
  refine (congrArg Subtype.val hprop).trans ?_
  exact gysinCycleMapPushforward_val_congr_degree C _ (by ring) _ _ _ _ _ rfl

/-! ### The operation on Chow groups -/

section Chow

variable (hα : letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  IsRelativeCycle p r α)

/-- **Stacks 0H6F, the descent.** The operation `g^*α ∩ -` of a relative `r`-cycle factors
through rational equivalence: it is the operation `A_k(T) ⟶ A_{k+r}(T ×_Y X)` on Chow groups,
written in the degree `k - (-r)` of a bivariant class of degree `-r`. -/
def relativeCycleCapChow {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) :
    chowGroup C (g ≫ sY) k →+ chowGroup C (pullback.fst p g ≫ p ≫ sY) (k - -(r : ℤ)) :=
  VeryWeakCapRule.capChowOfCycleGysin C (p ≫ sY) sY p rfl (-(r : ℤ))
    (relativeCycleCapRule C sY p r α) (isCycleGysinNatural_relativeCycleCapRule C sY p r α hα) g k

/-- The descended operation on the class of a cycle. -/
theorem relativeCycleCapChow_mk {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (β : CycleGroup C (g ≫ sY) k) :
    relativeCycleCapChow C sY p r α hα g k (QuotientAddGroup.mk' (rationalEquivalences C _ k) β) =
      QuotientAddGroup.mk' (rationalEquivalences C (pullback.fst p g ≫ p ≫ sY) (k - -(r : ℤ)))
        (cycleGroupCongr C _ (by ring) (relativeCycleCap C sY p r α g k β)) :=
  rfl

/-- **Condition (1) of Stacks 0B76** for the descended operation: it commutes with proper
pushforward along a proper morphism of test schemes. -/
theorem relativeCycleCapChow_properPushforward {T T' : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [IsProper h] (h' : pullback p (h ≫ g) ⟶ pullback p g)
    [IsProper h'] (sq : IsPullback (pullback.snd p (h ≫ g)) h' h (pullback.snd p g))
    (hfst : h' ≫ pullback.fst p g = pullback.fst p (h ≫ g)) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sY) (g ≫ sY) h
      (by simp [Category.assoc]) k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C
      (pullback.fst p (h ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY) h'
      (by rw [← Category.assoc, hfst]) (k - -(r : ℤ)))
    (β : chowGroup C ((h ≫ g) ≫ sY) k) :
    relativeCycleCapChow C sY p r α hα g k
        (properChowPushforward C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) k hfac β) =
      properChowPushforward C (pullback.fst p (h ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY) h'
        (by rw [← Category.assoc, hfst]) (k - -(r : ℤ)) hfac'
        (relativeCycleCapChow C sY p r α hα (h ≫ g) k β) := by
  induction β using QuotientAddGroup.induction_on with
  | H b =>
    change relativeCycleCapChow C sY p r α hα g k (properChowPushforward C _ _ h _ k hfac
        (QuotientAddGroup.mk' (rationalEquivalences C _ k) b)) =
      properChowPushforward C _ _ h' _ _ hfac'
        (relativeCycleCapChow C sY p r α hα (h ≫ g) k
          (QuotientAddGroup.mk' (rationalEquivalences C _ k) b))
    rw [properChowPushforward_mk, relativeCycleCapChow_mk, relativeCycleCapChow_mk,
      properChowPushforward_mk]
    congr 1
    apply Subtype.ext
    exact (congrArg Subtype.val
      (properPushforward_relativeCycleCap C sY p r α g h h' sq hfst k b)).symm

/-- Flat pullback of cycles does not see how the degree is written. -/
theorem flatPullback_val_congr_degree (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (w : A ⟶ B) [LocallyOfFiniteType w] [Flat w] (hw : w ≫ sB = sA) (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension w d) {k k' : ℤ} (hk : k = k')
    (c : CycleGroup C sB k) (c' : CycleGroup C sB k') (hc : c.1 = c'.1) :
    (flatPullback C sA sB w hw d hd k c).1 = (flatPullback C sA sB w hw d hd k' c').1 := by
  subst hk
  rw [Subtype.ext hc]

/-- **Condition (2) of Stacks 0B76** for the descended operation: it commutes with flat pullback
along a flat morphism of test schemes of fixed relative dimension. -/
theorem relativeCycleCapChow_flatPullbackChow {T T' : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension h d) (h' : pullback p (h ≫ g) ⟶ pullback p g)
    [LocallyOfFiniteType h'] [Flat h'] (hd' : AlgebraicGeometry.RelativeDimension h' d)
    (sq : IsPullback (pullback.snd p (h ≫ g)) h' h (pullback.snd p g))
    (hfst : h' ≫ pullback.fst p g = pullback.fst p (h ≫ g)) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sY) (g ≫ sY) h
      (by simp [Category.assoc]) d hd k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C
      (pullback.fst p (h ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY) h'
      (by rw [← Category.assoc, hfst]) d hd' (k - -(r : ℤ)))
    (β : chowGroup C (g ≫ sY) k) :
    relativeCycleCapChow C sY p r α hα (h ≫ g) (k + (d : ℤ))
        (flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) d hd k hfac β) ≍
      flatPullbackChow C (pullback.fst p (h ≫ g) ≫ p ≫ sY) (pullback.fst p g ≫ p ≫ sY) h'
        (by rw [← Category.assoc, hfst]) d hd' (k - -(r : ℤ)) hfac'
        (relativeCycleCapChow C sY p r α hα g k β) := by
  induction β using QuotientAddGroup.induction_on with
  | H b =>
    change relativeCycleCapChow C sY p r α hα (h ≫ g) (k + (d : ℤ)) (flatPullbackChow C _ _ h _ d hd
        k hfac (QuotientAddGroup.mk' (rationalEquivalences C _ k) b)) ≍
      flatPullbackChow C _ _ h' _ d hd' _ hfac'
        (relativeCycleCapChow C sY p r α hα g k
          (QuotientAddGroup.mk' (rationalEquivalences C _ k) b))
    rw [flatPullbackChow_mk, relativeCycleCapChow_mk, relativeCycleCapChow_mk, flatPullbackChow_mk]
    have key : ∀ (m n : ℤ) (hmn : m = n) (a : CycleGroup C (pullback.fst p (h ≫ g) ≫ p ≫ sY) m)
        (b : CycleGroup C (pullback.fst p (h ≫ g) ≫ p ≫ sY) n), a.1 = b.1 →
        (QuotientAddGroup.mk' (rationalEquivalences C _ m) a : chowGroup C _ m) ≍
          (QuotientAddGroup.mk' (rationalEquivalences C _ n) b : chowGroup C _ n) := by
      intro m n hmn a b hab
      subst hmn
      rw [Subtype.ext hab]
    refine key _ _ (by ring) _ _ ?_
    refine Function.locallyFinsuppWithin.ext fun x ↦ ?_
    change (relativeCycleCap C sY p r α (h ≫ g) (k + (d : ℤ)) _).1 x = _
    rw [relativeCycleCap_flatPullback_apply C sY p r α g h d hd h' hd' sq hfst k b x]
    exact congrArg (fun z : AlgebraicCycle _ ℤ ↦ z x)
      (flatPullback_val_congr_degree C _ _ h' _ d hd' (by ring) _ _ rfl)

end Chow

end Stacks.Chow

end
