module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Commuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldSurjective

/-!
# Bivariant classes towards a point commute with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, and let `c ∈ A^p(X ⟶ S)` be a bivariant class for the structure
morphism of `X` — a class *towards the point*, in the language of **Stacks 0FBW**. Let
`f : Y ⟶ Z` be a morphism of schemes locally of finite type over `S` and let
`c' ∈ A^q(Y ⟶ Z)` be an arbitrary bivariant class. **Stacks 0FBX** says that `c` and `c'`
commute.

The two classes acquire a common target only after `c` is base changed: `c` lives over the base
and `c'` over `Z`, so what commutes, in the sense of `Stacks.Chow.BivariantCommute` of Stacks
0FA2, is the pair consisting of the base change `res(c) ∈ A^p(X ×_S Z ⟶ Z)` of Stacks 0F9Z and
`c'` itself. Their composites both live in `A^{p+q}(X ×_S Y ⟶ Z)`, which is the group the tag
names.

The reason is the one the source gives: by Stacks 0FBW a class towards the point is a
`ℤ`-combination of classes `g_* ∘ (flat pullback)`, and `c'` commutes with proper pushforward and
with flat pullback by two of the three laws of Stacks 0B76. This file carries the two steps of
that argument which are statements about commuting classes, namely that commuting is preserved by
`ℤ`-combinations and by proper pushforward in the first argument.

## Main definitions

* `Stacks.Chow.bivariantClassCongrBase` — transport of bivariant classes along equalities of the
  structure morphisms of the source and of the target. The base change of a class towards the
  point is indexed by `pullback.fst sX sZ ≫ sX` and by `sZ ≫ 𝟙 S`, while
  `Stacks.Chow.BivariantCommute` consumes a class indexed by `pullback.snd sX sZ ≫ sZ` and by
  `sZ`; these are the same morphisms and not the same terms.
* `Stacks.Chow.commutingWith` — the classes commuting with a fixed `c₂`, as a subgroup.

## Main results

* `Stacks.Chow.bivariantCommute_zero_left`, `Stacks.Chow.bivariantCommute_add_left`,
  `Stacks.Chow.bivariantCommute_neg_left` — commuting with a fixed class is preserved by the group
  operations in the other argument, because every cap operation in sight is additive.
* `Stacks.Chow.bivariantCommute_of_isBivariantProperPushforward` — **the proper-pushforward step
  of the proof of Stacks 0FBX**: if `c₁ ∈ A^{p₁}(Z₁' ⟶ X)` commutes with `c₂ ∈ A^{p₂}(Z₂ ⟶ X)`
  and `h : Z₁' ⟶ Z₁` is proper, then the proper pushforward `h_* ∘ c₁ ∈ A^{p₁}(Z₁ ⟶ X)` of
  Stacks 0EPK commutes with `c₂` as well.

## Implementation notes

### No parallel datum

Commuting is `Stacks.Chow.BivariantCommute` throughout, the predicate of Stacks 0FA2 recorded in
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Commuting`; nothing here introduces a second notion
of two classes commuting, and nothing here assumes that any pair of classes commutes. The
hypothesis of `Stacks.Chow.bivariantCommute_of_isBivariantProperPushforward` is that `c₁`
commutes with `c₂` and its conclusion is that `h_* ∘ c₁` does; these are commuting statements for
two different pairs.

### Why the proper-pushforward step is an argument about test schemes

The base change `Z₁' ×_X T ⟶ Z₁ ×_X T` of `h` along a test scheme `t : T ⟶ X` is proper, so it
is a *morphism of test schemes* over `X`, and the proper-pushforward law of Stacks 0B76 for
`c₂` applies to it. That law turns `c₂ ∩ (h_* ∘ c₁) ∩ α` into a pushforward of
`c₂ ∩ c₁ ∩ α`, which the commuting hypothesis identifies with `c₁ ∩ c₂ ∩ α`; the two
pushforwards that result traverse the same square of fibre products, which is what
`Stacks.Chow.properChowPushforward_comp_eq` consumes. The comparison of the two iterated fibre
products that Stacks 0FA2 suppresses is `Stacks.Chow.commuteComparisonHom`, and the identity
between the two ways around that square is the only geometric input.

### The hypotheses carried

Stacks 02S2, the descent of proper pushforward to Chow groups, is a `Prop` and is quantified
rather than parameterized, as everywhere in this part of the library; it is carried as `hpp`.
Stacks 0EPK is carried in characterized form: the pushed-forward class is a named argument `d₁`
together with `Stacks.Chow.IsBivariantProperPushforward`, exactly as in
`Stacks.Chow.bivariantToBaseEval_flatPullbackProperPushforward`.

## References

* [Stacks Project, Tag 0FBX](https://stacks.math.columbia.edu/tag/0FBX)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0FBW](https://stacks.math.columbia.edu/tag/0FBW)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0EPK](https://stacks.math.columbia.edu/tag/0EPK)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport along equalities of the structure morphisms -/

section CongrBase

variable (C : ChowSituation.{u}) (G : GysinSystem C) {A W : Scheme.{u}}
  {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
  {sW sW' : W ⟶ C.S} [LocallyOfFiniteType sW] [LocallyOfFiniteType sW']
  (v : A ⟶ W) [LocallyOfFiniteType v]

/-- Bivariant classes for two equal structure morphisms of the source and two equal structure
morphisms of the target form the same group. -/
def bivariantClassCongrBase (hsA : sA = sA') (hsW : sW = sW')
    {hv : v ≫ sW = sA} {hv' : v ≫ sW' = sA'} (p : ℤ) :
    BivariantClass C G sA sW v hv p ≃+ BivariantClass C G sA' sW' v hv' p := by
  subst hsA
  subst hsW
  exact AddEquiv.refl _

/-- The transport of a bivariant class along equalities of the structure morphisms caps the way
the class does. The two values live in the Chow groups of two equal structure morphisms of the
same scheme, so the comparison is a heterogeneous equality. -/
theorem bivariantClassCongrBase_cap (hsA : sA = sA') (hsW : sW = sW')
    {hv : v ≫ sW = sA} {hv' : v ≫ sW' = sA'} (p : ℤ)
    (c : BivariantClass C G sA sW v hv p) {T : Scheme.{u}} (t : T ⟶ W)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sW) k)
    (α' : chowGroup C (t ≫ sW') k) (hα : α ≍ α') :
    (bivariantClassCongrBase C G v hsA hsW (hv := hv) (hv' := hv') p c).cap t k α' ≍
      c.cap t k α := by
  subst hsA
  subst hsW
  obtain rfl := eq_of_heq hα
  rfl

end CongrBase

/-! ### Commuting is preserved by the group operations -/

section Additive

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Z₁ Z₂ : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁] (f₂ : Z₂ ⟶ X)
  [LocallyOfFiniteType f₂] (p₁ p₂ : ℤ)
  (c₂ : BivariantClass C G (f₂ ≫ sX) sX f₂ rfl p₂)

/-- The zero class commutes with every bivariant class: both iterated cap operations vanish. -/
theorem bivariantCommute_zero_left : BivariantCommute C G sX f₁ f₂ p₁ p₂ 0 c₂ := by
  intro T t _ k α
  simp only [bivariantIteratedCap_apply, BivariantClass.zero_cap, map_zero]

/-- A sum of two classes commuting with `c₂` commutes with `c₂`. -/
theorem bivariantCommute_add_left {c₁ d₁ : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁}
    (hc : BivariantCommute C G sX f₁ f₂ p₁ p₂ c₁ c₂)
    (hd : BivariantCommute C G sX f₁ f₂ p₁ p₂ d₁ c₂) :
    BivariantCommute C G sX f₁ f₂ p₁ p₂ (c₁ + d₁) c₂ := by
  intro T t _ k α
  have h1 := hc t k α
  have h2 := hd t k α
  simp only [bivariantIteratedCap_apply, BivariantClass.add_cap, map_add] at h1 h2 ⊢
  rw [h1, h2]

/-- The negative of a class commuting with `c₂` commutes with `c₂`. -/
theorem bivariantCommute_neg_left {c₁ : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁}
    (hc : BivariantCommute C G sX f₁ f₂ p₁ p₂ c₁ c₂) :
    BivariantCommute C G sX f₁ f₂ p₁ p₂ (-c₁) c₂ := by
  intro T t _ k α
  have h1 := hc t k α
  simp only [bivariantIteratedCap_apply, BivariantClass.neg_cap, map_neg] at h1 ⊢
  rw [h1]

/-- The bivariant classes of degree `p₁` for `f₁` that commute with `c₂`, as a subgroup of
`A^{p₁}(Z₁ ⟶ X)`. -/
def commutingWith : AddSubgroup (BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁) where
  carrier := {c₁ | BivariantCommute C G sX f₁ f₂ p₁ p₂ c₁ c₂}
  zero_mem' := bivariantCommute_zero_left C G sX f₁ f₂ p₁ p₂ c₂
  add_mem' hc hd := bivariantCommute_add_left C G sX f₁ f₂ p₁ p₂ c₂ hc hd
  neg_mem' hc := bivariantCommute_neg_left C G sX f₁ f₂ p₁ p₂ c₂ hc

/-- Membership in `Stacks.Chow.commutingWith` is commuting with `c₂`. -/
@[simp]
theorem mem_commutingWith {c₁ : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁} :
    c₁ ∈ commutingWith C G sX f₁ f₂ p₁ p₂ c₂ ↔
      BivariantCommute C G sX f₁ f₂ p₁ p₂ c₁ c₂ :=
  Iff.rfl

end Additive

/-! ### Commuting is preserved by proper pushforward -/

section ProperPushforward

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Z₁ Z₁' Z₂ : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f₁ : Z₁ ⟶ X) [LocallyOfFiniteType f₁]
  (h : Z₁' ⟶ Z₁) [IsProper h] [LocallyOfFiniteType (h ≫ f₁)]
  (f₂ : Z₂ ⟶ X) [LocallyOfFiniteType f₂]
  (hpp : ProperPushforwardDescends C) (p₁ p₂ : ℤ)
  (c₁ : BivariantClass C G ((h ≫ f₁) ≫ sX) sX (h ≫ f₁) rfl p₁)
  (c₂ : BivariantClass C G (f₂ ≫ sX) sX f₂ rfl p₂)
  (d₁ : BivariantClass C G (f₁ ≫ sX) sX f₁ rfl p₁)

/-- **The proper-pushforward step of the proof of Stacks 0FBX.** Let `h : Z₁' ⟶ Z₁` be a proper
morphism of schemes over `X`, let `c₁ ∈ A^{p₁}(Z₁' ⟶ X)` and let `d₁ ∈ A^{p₁}(Z₁ ⟶ X)` be the
proper pushforward `h_* ∘ c₁` of Stacks 0EPK. If `c₁` commutes with `c₂ ∈ A^{p₂}(Z₂ ⟶ X)` then so
does `d₁`.

The base change of `h` along a test scheme is a proper morphism of test schemes, so the
proper-pushforward law of Stacks 0B76 for `c₂` moves `c₂` past it; the two resulting
pushforwards traverse one square of fibre products, and the commuting hypothesis identifies what
is pushed. Stacks 02S2 is carried as `hpp` and Stacks 0EPK in characterized form as `hd`; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.PointClassCommuting`. -/
theorem bivariantCommute_of_isBivariantProperPushforward
    (hd : IsBivariantProperPushforward C G ((h ≫ f₁) ≫ sX) (f₁ ≫ sX) sX h f₁
        (Category.assoc h f₁ sX).symm rfl hpp p₁ c₁ d₁)
    (hc : BivariantCommute C G sX (h ≫ f₁) f₂ p₁ p₂ c₁ c₂) :
    BivariantCommute C G sX f₁ f₂ p₁ p₂ d₁ c₂ := by
  intro T t _ k α
  have e : bivariantPushforwardBaseChange h f₁ t ≫ (pullback.fst f₁ t ≫ f₁) =
      pullback.fst (h ≫ f₁) t ≫ (h ≫ f₁) := by
    rw [← Category.assoc, bivariantPushforwardBaseChange_fst, Category.assoc]
  obtain ⟨z, hz_fst, hz_snd⟩ :
      ∃ z : pullback f₂ (pullback.fst (h ≫ f₁) t ≫ (h ≫ f₁)) ⟶
          pullback f₂ (pullback.fst f₁ t ≫ f₁),
        z ≫ pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) =
            pullback.fst f₂ (pullback.fst (h ≫ f₁) t ≫ (h ≫ f₁)) ∧
          z ≫ pullback.snd f₂ (pullback.fst f₁ t ≫ f₁) =
            pullback.snd f₂ (pullback.fst (h ≫ f₁) t ≫ (h ≫ f₁)) ≫
              bivariantPushforwardBaseChange h f₁ t :=
    ⟨pullback.map f₂ (pullback.fst (h ≫ f₁) t ≫ (h ≫ f₁)) f₂ (pullback.fst f₁ t ≫ f₁) (𝟙 Z₂)
        (bivariantPushforwardBaseChange h f₁ t) (𝟙 X) (by simp) (by simp), by simp, by simp⟩
  have hbcm : (pullback.congrHom (rfl : f₂ = f₂) e).hom ≫ z =
      bivariantBaseChangeMap f₂ (pullback.fst f₁ t ≫ f₁)
        (bivariantPushforwardBaseChange h f₁ t) := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp [bivariantBaseChangeMap, Category.assoc, hz_fst, hz_snd]
  have hzeq : z = (pullback.congrHom (rfl : f₂ = f₂) e).inv ≫
      bivariantBaseChangeMap f₂ (pullback.fst f₁ t ≫ f₁)
        (bivariantPushforwardBaseChange h f₁ t) := by
    rw [← hbcm, Iso.inv_hom_id_assoc]
  have hzproper : IsProper z := by rw [hzeq]; infer_instance
  have hcomp : bivariantPushforwardBaseChange h f₁ (pullback.fst f₂ t ≫ f₂) ≫
        commuteComparisonHom f₁ f₂ t = commuteComparisonHom (h ≫ f₁) f₂ t ≫ z := by
    refine pullback.hom_ext ?_ (pullback.hom_ext ?_ ?_) <;> simp [hz_fst, hz_snd]
  have hzbase : z ≫ (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX)) =
      pullback.fst f₂ (pullback.fst (h ≫ f₁) t ≫ (h ≫ f₁)) ≫ (f₂ ≫ sX) :=
    (Category.assoc z (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁)) (f₂ ≫ sX)).symm.trans
      (congrArg (· ≫ (f₂ ≫ sX)) hz_fst)
  have hA : pullback.fst (h ≫ f₁) t ≫ ((h ≫ f₁) ≫ sX) =
      (bivariantPushforwardBaseChange h f₁ t ≫ (pullback.fst f₁ t ≫ f₁)) ≫ sX := by
    rw [e]
    exact (Category.assoc _ _ _).symm
  have hcongrbase : (pullback.congrHom (rfl : f₂ = f₂) e).hom ≫
      (pullback.fst f₂ (pullback.fst (h ≫ f₁) t ≫ (h ≫ f₁)) ≫ (f₂ ≫ sX)) =
      pullback.fst f₂ (bivariantPushforwardBaseChange h f₁ t ≫ (pullback.fst f₁ t ≫ f₁)) ≫
        (f₂ ≫ sX) := by
    simp
  have hnat := c₂.proper_naturality (pullback.fst f₁ t ≫ f₁)
    (bivariantPushforwardBaseChange h f₁ t)
    (bivariantBaseChangeMap f₂ (pullback.fst f₁ t ≫ f₁)
      (bivariantPushforwardBaseChange h f₁ t))
    (isPullback_bivariantBaseChangeMap f₂ (pullback.fst f₁ t ≫ f₁)
      (bivariantPushforwardBaseChange h f₁ t))
    (by simp) (k - p₁) (hpp _ _ _ _ _) (hpp _ _ _ _ _)
    (chowGroupCongr C hA (k - p₁) (c₁.cap t k α))
  rw [bivariantIteratedCap_apply, bivariantIteratedCap_apply, hd, hd,
    bivariantProperPushforwardCap_apply, bivariantProperPushforwardCap_apply,
    properChowPushforward_chowGroupCongr C hA (Category.assoc (pullback.fst f₁ t) f₁ sX).symm
      (bivariantPushforwardBaseChange h f₁ t)
      (bivariantPushforwardBaseChange_comp_structure (Category.assoc h f₁ sX).symm f₁ t)
      (Category.assoc _ _ _).symm (k - p₁) (hpp _ _ _ _ _) (hpp _ _ _ _ _),
    hnat,
    properChowPushforward_comp_apply C
      (pullback.fst f₂ (bivariantPushforwardBaseChange h f₁ t ≫ (pullback.fst f₁ t ≫ f₁)) ≫
        (f₂ ≫ sX))
      (pullback.fst f₂ (pullback.fst (h ≫ f₁) t ≫ (h ≫ f₁)) ≫ (f₂ ≫ sX))
      (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
      (pullback.congrHom (rfl : f₂ = f₂) e).hom z
      (bivariantBaseChangeMap f₂ (pullback.fst f₁ t ≫ f₁)
        (bivariantPushforwardBaseChange h f₁ t))
      hbcm hcongrbase hzbase (by simp) ((k - p₁) - p₂)
      (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _),
    properChowPushforward_eq_chowPushforwardOfIso C _ _
      (pullback.congrHom (rfl : f₂ = f₂) e).hom hcongrbase ((k - p₁) - p₂) (hpp _ _ _ _ _),
    chowPushforwardOfIso_congrHom_cap C G (f₂ ≫ sX) sX f₂ rfl p₂ c₂ e hcongrbase (k - p₁)
      (c₁.cap t k α) hA (Category.assoc (pullback.fst (h ≫ f₁) t) (h ≫ f₁) sX).symm]
  rw [← properChowPushforward_eq_chowPushforwardOfIso C
      (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
      (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX)) (commuteComparisonHom f₁ f₂ t)
      (commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t) ((k - p₂) - p₁)
      (hpp _ _ _ _ _),
    properChowPushforward_comp_eq C
      (pullback.fst (h ≫ f₁) (pullback.fst f₂ t ≫ f₂) ≫ ((h ≫ f₁) ≫ sX))
      (pullback.fst f₁ (pullback.fst f₂ t ≫ f₂) ≫ (f₁ ≫ sX))
      (pullback.fst f₂ (pullback.fst (h ≫ f₁) t ≫ (h ≫ f₁)) ≫ (f₂ ≫ sX))
      (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX))
      (bivariantPushforwardBaseChange h f₁ (pullback.fst f₂ t ≫ f₂))
      (commuteComparisonHom f₁ f₂ t) (commuteComparisonHom (h ≫ f₁) f₂ t) z hcomp
      (bivariantPushforwardBaseChange_comp_structure (Category.assoc h f₁ sX).symm f₁
        (pullback.fst f₂ t ≫ f₂))
      (commuteComparisonHom_comp_structureMorphism C sX f₁ f₂ t)
      (commuteComparisonHom_comp_structureMorphism C sX (h ≫ f₁) f₂ t) hzbase
      ((k - p₂) - p₁) (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _),
    properChowPushforward_eq_chowPushforwardOfIso C
      (pullback.fst (h ≫ f₁) (pullback.fst f₂ t ≫ f₂) ≫ ((h ≫ f₁) ≫ sX))
      (pullback.fst f₂ (pullback.fst (h ≫ f₁) t ≫ (h ≫ f₁)) ≫ (f₂ ≫ sX))
      (commuteComparisonHom (h ≫ f₁) f₂ t)
      (commuteComparisonHom_comp_structureMorphism C sX (h ≫ f₁) f₂ t) ((k - p₂) - p₁)
      (hpp _ _ _ _ _),
    ← bivariantIteratedCap_apply C G sX (h ≫ f₁) f₂ p₁ p₂ c₁ c₂ t k α, hc t k α,
    properChowPushforward_chowGroupDegreeEquiv C
      (pullback.fst f₂ (pullback.fst (h ≫ f₁) t ≫ (h ≫ f₁)) ≫ (f₂ ≫ sX))
      (pullback.fst f₂ (pullback.fst f₁ t ≫ f₁) ≫ (f₂ ≫ sX)) z hzbase
      (by ring : (k - p₁) - p₂ = (k - p₂) - p₁) (hpp _ _ _ _ _) (hpp _ _ _ _ _),
    bivariantIteratedCap_apply]

end ProperPushforward

/-! ### The comparison isomorphism of the two base changes -/

section PointClassBaseChange

variable {C : ChowSituation.{u}} {X Z W T : Scheme.{u}} (sX : X ⟶ C.S) (sZ : Z ⟶ C.S)
  (g : W ⟶ X) (t : T ⟶ Z)

/-- The canonical isomorphism `W ×_S T ≅ (W ×_S Z) ×_Z T`. -/
def pointClassBaseChangeIso :
    pullback (g ≫ sX) (t ≫ sZ) ≅
      pullback (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t :=
  (pullbackLeftPullbackSndIso (g ≫ sX) sZ t).symm.trans
    (pullback.congrHom (bivariantPushforwardBaseChange_snd g sX sZ).symm (rfl : t = t))

/-- The comparison isomorphism `W ×_S T ≅ (W ×_S Z) ×_Z T` followed by the projection to `W`
is the first projection `W ×_S T ⟶ W`. -/
@[reassoc (attr := simp)]
theorem pointClassBaseChangeIso_hom_fst_fst :
    (pointClassBaseChangeIso sX sZ g t).hom ≫
        pullback.fst (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t ≫
          pullback.fst (g ≫ sX) sZ = pullback.fst (g ≫ sX) (t ≫ sZ) := by
  simp [pointClassBaseChangeIso]

/-- The comparison isomorphism `W ×_S T ≅ (W ×_S Z) ×_Z T` followed by the projection to `T`
is the second projection `W ×_S T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem pointClassBaseChangeIso_hom_snd :
    (pointClassBaseChangeIso sX sZ g t).hom ≫
        pullback.snd (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t =
      pullback.snd (g ≫ sX) (t ≫ sZ) := by
  simp [pointClassBaseChangeIso]

/-- The comparison isomorphism is a morphism over the base. -/
theorem pointClassBaseChangeIso_hom_comp_structureMorphism :
    (pointClassBaseChangeIso sX sZ g t).hom ≫
        (pullback.fst (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t ≫
          ((bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ)) =
      pullback.fst (g ≫ sX) (t ≫ sZ) ≫ (g ≫ sX) := by
  rw [pullback.condition_assoc, pointClassBaseChangeIso_hom_snd_assoc]
  exact pullback.condition.symm

/-- The comparison isomorphism carries the base change of `g` over the test scheme of the base to
the base change of `g` over `Z`. -/
theorem bivariantPushforwardBaseChange_comp_pullbackLeftPullbackSndIso_inv :
    bivariantPushforwardBaseChange g sX (t ≫ sZ) ≫ (pullbackLeftPullbackSndIso sX sZ t).inv =
      (pointClassBaseChangeIso sX sZ g t).hom ≫
        bivariantPushforwardBaseChange (bivariantPushforwardBaseChange g sX sZ)
          (pullback.snd sX sZ) t := by
  refine pullback.hom_ext (pullback.hom_ext ?_ ?_) ?_
  · simp
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
      bivariantPushforwardBaseChange_snd_assoc, bivariantPushforwardBaseChange_fst_assoc]
    rw [pullback.condition
        (f := bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) (g := t),
      ← Category.assoc (pointClassBaseChangeIso sX sZ g t).hom, pointClassBaseChangeIso_hom_snd]
  · simp

/-- The base change of `g` to `Z`, over a test scheme of `Z`, is a morphism over the base. -/
theorem bivariantPushforwardBaseChange_pointClass_comp_structureMorphism :
    bivariantPushforwardBaseChange (bivariantPushforwardBaseChange g sX sZ)
          (pullback.snd sX sZ) t ≫
        (pullback.fst (pullback.snd sX sZ) t ≫ (pullback.fst sX sZ ≫ sX)) =
      pullback.fst (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t ≫
        ((bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ) := by
  have h1 : pullback.fst (pullback.snd sX sZ) t ≫ (pullback.fst sX sZ ≫ sX) =
      pullback.snd (pullback.snd sX sZ) t ≫ (t ≫ sZ) := by
    rw [pullback.condition (f := sX) (g := sZ), pullback.condition_assoc]
  rw [h1, pullback.condition_assoc, bivariantPushforwardBaseChange_snd_assoc]

/-- The comparison isomorphism is compatible with the structure morphism of `X ×_S Z` read
through the first projection. -/
theorem pullbackLeftPullbackSndIso_inv_comp_structureMorphism :
    (pullbackLeftPullbackSndIso sX sZ t).inv ≫
        (pullback.fst (pullback.snd sX sZ) t ≫ (pullback.fst sX sZ ≫ sX)) =
      pullback.fst sX (t ≫ sZ) ≫ sX := by
  simp

end PointClassBaseChange

/-! ### The two heavy steps of the bridge -/

section BridgeSteps

variable (C : ChowSituation.{u}) {X Z W T : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (g : W ⟶ X)
  [LocallyOfFiniteType (g ≫ sX)] (t : T ⟶ Z) [LocallyOfFiniteType t]

omit [LocallyOfFiniteType sX] in
/-- The flat pullback along the base change of `W ⟶ S` to `Z` is the flat pullback along its base
change to the base, pushed forward along the comparison isomorphism: the isomorphism case of
Stacks 02RG. -/
theorem flatPullbackChow_pointClassBaseChangeIso [Flat (g ≫ sX)]
    [LocallyOfFiniteType (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ)]
    [Flat (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ)] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension (g ≫ sX) r)
    (hrbc : AlgebraicGeometry.RelativeDimension
      (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) r)
    (hS1 : FlatPullbackDescends C) (k : ℤ) (α : chowGroup C (t ≫ sZ) k) :
    flatPullbackChow C
        (pullback.fst (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t ≫
          ((bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ)) (t ≫ sZ)
        (pullback.snd (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t)
        (pullbackSnd_comp_structureMorphism
          (rfl : (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ =
            (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ) t) r
        (relativeDimension_pullbackSnd _ hrbc t) k (hS1 _ _ _ _ r _ k) α =
      chowPushforwardOfIso C (pullback.fst (g ≫ sX) (t ≫ sZ) ≫ (g ≫ sX))
        (pullback.fst (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t ≫
          ((bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ))
        (pointClassBaseChangeIso sX sZ g t).hom
        (pointClassBaseChangeIso_hom_comp_structureMorphism sX sZ g t) (k + (r : ℤ))
        (flatPullbackChow C (pullback.fst (g ≫ sX) (t ≫ sZ) ≫ (g ≫ sX)) (t ≫ sZ)
          (pullback.snd (g ≫ sX) (t ≫ sZ)) pullback.condition.symm r
          (relativeDimension_pullbackSnd (g ≫ sX) hr (t ≫ sZ)) k (hS1 _ _ _ _ r _ k) α) := by
  have h := flatPullbackChow_chowPushforwardOfIso C (t ≫ sZ)
    (pullback.fst (g ≫ sX) (t ≫ sZ) ≫ (g ≫ sX)) (t ≫ sZ)
    (pullback.fst (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t ≫
      ((bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ))
    (𝟙 T) (Category.id_comp (t ≫ sZ)) (pointClassBaseChangeIso sX sZ g t).hom
    (pointClassBaseChangeIso_hom_comp_structureMorphism sX sZ g t)
    (pullback.snd (g ≫ sX) (t ≫ sZ)) pullback.condition.symm
    (pullback.snd (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t)
    (pullbackSnd_comp_structureMorphism
      (rfl : (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ =
        (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ) t)
    (by rw [Category.comp_id]; exact (pointClassBaseChangeIso_hom_snd sX sZ g t).symm) r
    (relativeDimension_pullbackSnd (g ≫ sX) hr (t ≫ sZ))
    (relativeDimension_pullbackSnd _ hrbc t) k (hS1 _ _ _ _ r _ k) (hS1 _ _ _ _ r _ k) α
  rwa [chowPushforwardOfIso_id] at h

/-- The square traversed by the two proper pushforwards: pushing forward along the base change of
`g` over the base and then along the comparison isomorphism of `X ×_S Z` is pushing forward along
the comparison isomorphism of `W ×_S Z` and then along the base change of `g` over `Z`. -/
theorem properChowPushforward_pointClassBaseChangeIso_square [IsProper g]
    (hpp : ProperPushforwardDescends C) (m : ℤ)
    (x : chowGroup C (pullback.fst (g ≫ sX) (t ≫ sZ) ≫ (g ≫ sX)) m) :
    chowPushforwardOfIso C (pullback.fst sX (t ≫ sZ) ≫ sX)
        (pullback.fst (pullback.snd sX sZ) t ≫ (pullback.fst sX sZ ≫ sX))
        (pullbackLeftPullbackSndIso sX sZ t).inv
        (pullbackLeftPullbackSndIso_inv_comp_structureMorphism sX sZ t) m
        (properChowPushforward C (pullback.fst (g ≫ sX) (t ≫ sZ) ≫ (g ≫ sX))
          (pullback.fst sX (t ≫ sZ) ≫ sX) (bivariantPushforwardBaseChange g sX (t ≫ sZ))
          (bivariantPushforwardBaseChange_comp_structure (rfl : g ≫ sX = g ≫ sX) sX (t ≫ sZ)) m
          (hpp _ _ _ _ _) x) =
      properChowPushforward C
        (pullback.fst (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t ≫
          ((bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ))
        (pullback.fst (pullback.snd sX sZ) t ≫ (pullback.fst sX sZ ≫ sX))
        (bivariantPushforwardBaseChange (bivariantPushforwardBaseChange g sX sZ)
          (pullback.snd sX sZ) t)
        (bivariantPushforwardBaseChange_pointClass_comp_structureMorphism sX sZ g t) m
        (hpp _ _ _ _ _)
        (chowPushforwardOfIso C (pullback.fst (g ≫ sX) (t ≫ sZ) ≫ (g ≫ sX))
          (pullback.fst (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) t ≫
            ((bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ))
          (pointClassBaseChangeIso sX sZ g t).hom
          (pointClassBaseChangeIso_hom_comp_structureMorphism sX sZ g t) m x) := by
  rw [← properChowPushforward_eq_chowPushforwardOfIso C _ _
      (pullbackLeftPullbackSndIso sX sZ t).inv
      (pullbackLeftPullbackSndIso_inv_comp_structureMorphism sX sZ t) m (hpp _ _ _ _ _),
    ← properChowPushforward_eq_chowPushforwardOfIso C _ _
      (pointClassBaseChangeIso sX sZ g t).hom
      (pointClassBaseChangeIso_hom_comp_structureMorphism sX sZ g t) m (hpp _ _ _ _ _)]
  exact properChowPushforward_comp_eq C _ _ _ _
    (bivariantPushforwardBaseChange g sX (t ≫ sZ)) (pullbackLeftPullbackSndIso sX sZ t).inv
    (pointClassBaseChangeIso sX sZ g t).hom
    (bivariantPushforwardBaseChange (bivariantPushforwardBaseChange g sX sZ)
      (pullback.snd sX sZ) t)
    (bivariantPushforwardBaseChange_comp_pullbackLeftPullbackSndIso_inv sX sZ g t)
    (bivariantPushforwardBaseChange_comp_structure (rfl : g ≫ sX = g ≫ sX) sX (t ≫ sZ))
    (pullbackLeftPullbackSndIso_inv_comp_structureMorphism sX sZ t)
    (pointClassBaseChangeIso_hom_comp_structureMorphism sX sZ g t)
    (bivariantPushforwardBaseChange_pointClass_comp_structureMorphism sX sZ g t) m
    (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _) (hpp _ _ _ _ _) x

end BridgeSteps

/-- Proper pushforward depends on the structure morphisms of its source and target, its degree and
its argument only up to equality and heterogeneous equality. This strengthens
`Stacks.Chow.properChowPushforward_heq_congr` by letting the two structure morphisms vary: the
comparison below meets one pushforward written once over `pullback.fst sX sZ ≫ sX` and once over
`pullback.snd sX sZ ≫ sZ`. -/
theorem properChowPushforward_heq_congr_base (C : ChowSituation.{u}) {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [LocallyOfFiniteType sB'] (u : A ⟶ B)
    [IsProper u] (hsA : sA = sA') (hsB : sB = sB') (hu : u ≫ sB = sA) (hu' : u ≫ sB' = sA')
    {k k' : ℤ} (hkk' : k = k')
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB u hu k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C sA' sB' u hu' k')
    (α : chowGroup C sA k) (α' : chowGroup C sA' k') (hαα' : α ≍ α') :
    properChowPushforward C sA sB u hu k hfac α ≍
      properChowPushforward C sA' sB' u hu' k' hfac' α' := by
  subst hsA
  subst hsB
  subst hkk'
  obtain rfl := eq_of_heq hαα'
  rfl


/-! ### Stacks 0FBX -/

section Main

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (f : Y ⟶ Z) [LocallyOfFiniteType f] (p q : ℤ)
  (hgys : G.IsNaturalUnderBaseChangeIso)

/-- **Stacks 0F9Z for a class towards the point.** The base change to `Z` of a bivariant class
towards the point: the restriction of Stacks 0F9Z along the structure morphism of `Z`, read in the
indices `Stacks.Chow.BivariantCommute` consumes.

The restriction is a class for `pullback.snd sX sZ : X ×_S Z ⟶ Z` whose source is indexed by
`pullback.fst sX sZ ≫ sX` and whose target by `sZ ≫ 𝟙 S`, while Stacks 0FA2 asks for a class
indexed by `pullback.snd sX sZ ≫ sZ` and by `sZ`. The two pairs are the same morphisms, by
`pullback.condition` and `Category.comp_id`, and `Stacks.Chow.bivariantClassCongrBase` transports
between them. -/
def bivariantToBaseRestrictionHom :
    bivariantToBase C G sX p →+
      BivariantClass C G (pullback.snd sX sZ ≫ sZ) sZ (pullback.snd sX sZ) rfl p :=
  (bivariantClassCongrBase C G (pullback.snd sX sZ)
      (pullback.condition (f := sX) (g := sZ)) (Category.comp_id sZ) p).toAddMonoidHom.comp
    (bivariantRestrictionAddHom C G sX (𝟙 C.S) sX (Category.comp_id sX) sZ p hgys)

/-- **The step of the proof of Stacks 0FBX that moves the decomposition of Stacks 0FBW to `Z`.**
Let `g : W ⟶ X` be proper with `W` flat of relative dimension `r` over the base, and let
`d ∈ A^{-r}(X ⟶ S)` be the proper pushforward along `g` of the flat-pullback class of Stacks 0B78
for the structure morphism of `W`. Then the base change of `d` to `Z` is the proper pushforward,
along the base change of `g` to `Z`, of the flat-pullback class of Stacks 0B78 for the base change
`W ×_S Z ⟶ Z` of that structure morphism.

Both sides cap by a flat pullback of the test class followed by a proper pushforward. The two flat
pullbacks are taken along the two base changes `W ×_S T ⟶ T` and `(W ×_S Z) ×_Z T ⟶ T` of
`W ⟶ S`, which `Stacks.Chow.flatPullbackChow_pointClassBaseChangeIso` identifies; the two proper
pushforwards then traverse the square of
`Stacks.Chow.properChowPushforward_pointClassBaseChangeIso_square`. -/
theorem isBivariantProperPushforward_bivariantToBaseRestriction {W : Scheme.{u}} (g : W ⟶ X)
    [IsProper g] [LocallyOfFiniteType (g ≫ sX)] [Flat (g ≫ sX)] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension (g ≫ sX) r) (hS1 : FlatPullbackDescends C)
    (hRG : ProperPushforwardFlatPullbackBaseChange C) (hpp : ProperPushforwardDescends C)
    (h71 : G.FlatPullbackNaturality r)
    (hflatbc : Flat (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ))
    (hloftbc : LocallyOfFiniteType
      (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ))
    (hrbc : AlgebraicGeometry.RelativeDimension
      (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) r)
    {d : bivariantToBase C G sX (-(r : ℤ))}
    (hd : IsBivariantProperPushforward C G (g ≫ sX) sX (𝟙 C.S) g sX rfl (Category.comp_id sX) hpp
      (-(r : ℤ))
      (flatPullbackBivariantClass C G (g ≫ sX) (𝟙 C.S) (g ≫ sX)
        (comp_comp_structureMorphism_eq (rfl : g ≫ sX = g ≫ sX) (Category.comp_id sX)) r hr hS1
        hRG h71)
      d) :
    letI := hflatbc
    letI := hloftbc
    IsBivariantProperPushforward C G
      ((bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ)
      (pullback.snd sX sZ ≫ sZ) sZ (bivariantPushforwardBaseChange g sX sZ)
      (pullback.snd sX sZ)
      (Category.assoc (bivariantPushforwardBaseChange g sX sZ) (pullback.snd sX sZ) sZ).symm rfl
      hpp (-(r : ℤ))
      (flatPullbackBivariantClass C G
        ((bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) ≫ sZ) sZ
        (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) rfl r hrbc hS1 hRG h71)
      (bivariantToBaseRestrictionHom C G sX sZ (-(r : ℤ)) hgys d) := by
  let := hflatbc
  let := hloftbc
  intro T t _ k α
  have hWbase : pullback.snd (g ≫ sX) (t ≫ sZ) ≫ (t ≫ sZ) =
      pullback.fst (g ≫ sX) (t ≫ sZ) ≫ (g ≫ sX) := pullback.condition.symm
  have hT : t ≫ sZ = t ≫ (sZ ≫ 𝟙 C.S) := by rw [Category.comp_id]
  have hcap := bivariantClassCongrBase_cap C G (pullback.snd sX sZ)
    (pullback.condition (f := sX) (g := sZ)) (Category.comp_id sZ) (-(r : ℤ))
    (bivariantRestriction C G sX (𝟙 C.S) sX (Category.comp_id sX) sZ (-(r : ℤ)) hgys d) t k
    (chowGroupCongr C hT k α) α (chowGroupCongr_heq C hT k α) (hv' := rfl)
  have hbasecap : (flatPullbackBivariantClass C G (g ≫ sX) (𝟙 C.S) (g ≫ sX)
        (comp_comp_structureMorphism_eq (rfl : g ≫ sX = g ≫ sX) (Category.comp_id sX)) r hr hS1
        hRG h71).cap (t ≫ sZ) k
      (chowGroupCongr C (Category.assoc t sZ (𝟙 C.S)).symm k (chowGroupCongr C hT k α)) ≍
      flatPullbackChow C (pullback.fst (g ≫ sX) (t ≫ sZ) ≫ (g ≫ sX)) (t ≫ sZ)
        (pullback.snd (g ≫ sX) (t ≫ sZ)) hWbase r
        (relativeDimension_pullbackSnd (g ≫ sX) hr (t ≫ sZ)) k (hS1 _ _ _ hWbase r _ k) α :=
    (flatPullbackBivariantClass_cap C G (g ≫ sX) (𝟙 C.S) (g ≫ sX) _ r hr hS1 hRG h71 (t ≫ sZ) k
      _).trans
      (flatPullbackChow_heq_congr_base C rfl (Category.assoc t sZ (𝟙 C.S)).symm rfl _ hWbase rfl
        _ _ rfl _ _ _ _
        (((chowGroupCongr_heq C (Category.assoc t sZ (𝟙 C.S)).symm k _).trans
          (chowGroupCongr_heq C hT k α)))).symm
  rw [bivariantProperPushforwardCap_apply]
  refine eq_of_heq (HEq.trans hcap ?_)
  rw [bivariantRestriction_cap, bivariantRestrictionCap_apply, hd,
    bivariantProperPushforwardCap_apply]
  refine HEq.trans (chowPushforwardOfIso_heq_congr C (pullback.fst sX (t ≫ sZ) ≫ sX)
    (pullback.fst (pullback.snd sX sZ) t ≫ (pullback.fst sX sZ ≫ sX))
    (pullbackLeftPullbackSndIso sX sZ t).inv
    (pullbackLeftPullbackSndIso_inv_comp_structureMorphism sX sZ t)
    (by ring : k - -(r : ℤ) = k + (r : ℤ)) _ _
    (properChowPushforward_heq_congr C (pullback.fst (g ≫ sX) (t ≫ sZ) ≫ (g ≫ sX))
      (pullback.fst sX (t ≫ sZ) ≫ sX) (bivariantPushforwardBaseChange g sX (t ≫ sZ))
      (bivariantPushforwardBaseChange_comp_structure (rfl : g ≫ sX = g ≫ sX) sX (t ≫ sZ))
      (by ring : k - -(r : ℤ) = k + (r : ℤ)) (hpp _ _ _ _ _) (hpp _ _ _ _ _) _ _
      hbasecap)) ?_
  rw [properChowPushforward_pointClassBaseChangeIso_square C sX sZ g t hpp (k + (r : ℤ)),
    ← flatPullbackChow_pointClassBaseChangeIso C sX sZ g t r hr hrbc hS1 k α]
  exact properChowPushforward_heq_congr_base C
    (bivariantPushforwardBaseChange (bivariantPushforwardBaseChange g sX sZ)
      (pullback.snd sX sZ) t) rfl
    (congrArg (pullback.fst (pullback.snd sX sZ) t ≫ ·) (pullback.condition (f := sX) (g := sZ)))
    _ _ (by ring : k + (r : ℤ) = k - -(r : ℤ)) (hpp _ _ _ _ _) (hpp _ _ _ _ _) _ _
    (flatPullbackBivariantClass_cap C G _ sZ
      (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) rfl r hrbc hS1 hRG h71 t k
      α).symm

/-- **Stacks 0FBX.** Let `c ∈ A^p(X ⟶ S)` be a bivariant class towards the point and let
`c' ∈ A^q(Y ⟶ Z)` be an arbitrary bivariant class, for an arbitrary morphism `f : Y ⟶ Z` of
schemes locally of finite type over the base. Then the base change of `c` to `Z` and `c'`
commute, in the sense of Stacks 0FA2.

The proof is the source's. By Stacks 0FBW the map `c ↦ c ∩ [Spec k]` is a bijection of
`A^p(X ⟶ S)` with `CH_{-p}(X)`, and `CH_{-p}(X)` is generated by proper pushforwards of flat
pullbacks of the class of the point; so `c` is a `ℤ`-combination of classes `g_* ∘ (flat
pullback)`. Commuting with `c'` is preserved by `ℤ`-combinations, so it is enough to treat one
such class. Its base change to `Z` is again a proper pushforward of a flat-pullback class, by
`Stacks.Chow.isBivariantProperPushforward_bivariantToBaseRestriction`; that flat-pullback class
commutes with `c'` by the flat law of Stacks 0B76, which is
`Stacks.Chow.bivariantCommute_flatPullbackBivariantClass`; and proper pushforward preserves
commuting by `Stacks.Chow.bivariantCommute_of_isBivariantProperPushforward`.

Nothing here assumes that `c` and `c'` commute, nor that any other pair of classes does; the
hypotheses are the prerequisites of Stacks 0FBW together with the descent statements this part of
the library quantifies rather than parameterizes. -/
@[stacks 0FBX "a bivariant class towards the point commutes with every bivariant class, in the \
form of Stacks 0FA2, for the base being the spectrum of a field; hfund, hEPK and hgen are the \
prerequisites of Stacks 0FBW, hS1 is Stacks 02S1, hpp is Stacks 02S2, hRG is Stacks 02RG, h71 is \
Stacks 0B71 and hgys is the isomorphism case of Stacks 02TA"]
theorem bivariantCommute_bivariantToBase [Subsingleton C.S] [IsIntegral C.S]
    (c : bivariantToBase C G sX p)
    (c' : BivariantClass C G (f ≫ sZ) sZ f rfl q)
    (hpp : ProperPushforwardDescends C) (hS1 : FlatPullbackDescends C)
    (hRG : ProperPushforwardFlatPullbackBaseChange C)
    (h71 : ∀ r : ℕ, G.FlatPullbackNaturality r)
    (hEPK : BivariantProperPushforwardExists C G)
    (hgen : ChowClassesGeneratedByBaseFlatPullbacks C hS1 hpp)
    (hfund : IntegralFundamentalClassIsFlatPullback C hS1) :
    BivariantCommute C G sZ (pullback.snd sX sZ) f p q
      (bivariantToBaseRestrictionHom C G sX sZ p hgys c) c' := by
  have hle : AddSubgroup.closure
        {β : chowGroup C sX (-p) |
          ∃ (W : Scheme.{u}) (g : W ⟶ X) (hgp : IsProper g)
            (hgt : LocallyOfFiniteType (g ≫ sX)) (hgf : Flat (g ≫ sX)) (r : ℕ)
            (hr : AlgebraicGeometry.RelativeDimension (g ≫ sX) r), -(r : ℤ) = p ∧
            let := hgp
            let := hgt
            let := hgf
            β ≍ properChowPushforward C (g ≫ sX) sX g rfl (-(-(r : ℤ))) (hpp _ _ g rfl _)
              (flatPullbackBaseClass C (g ≫ sX) r hr hS1)} ≤
        AddSubgroup.map (bivariantToBaseEval C G sX p)
          (((commutingWith C G sZ (pullback.snd sX sZ) f p q c').comap
            (bivariantToBaseRestrictionHom C G sX sZ p hgys))) := by
    rw [AddSubgroup.closure_le]
    rintro β ⟨W, g, hgp, hgt, hgf, r, hr, hrp, hβ⟩
    let _ := hgp
    let _ := hgt
    let _ := hgf
    subst hrp
    obtain ⟨d, hdd⟩ := hEPK (g ≫ sX) sX (𝟙 C.S) g sX rfl (Category.comp_id sX) hpp (-(r : ℤ))
      (flatPullbackBivariantClass C G (g ≫ sX) (𝟙 C.S) (g ≫ sX)
        (comp_comp_structureMorphism_eq (rfl : g ≫ sX = g ≫ sX) (Category.comp_id sX)) r hr hS1
        hRG (h71 r))
    have hsq : IsPullback (pullback.fst (g ≫ sX) sZ)
        (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) (g ≫ sX) sZ := by
      rw [bivariantPushforwardBaseChange_snd]
      exact IsPullback.of_hasPullback (g ≫ sX) sZ
    have hloftbc : LocallyOfFiniteType
        (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) :=
      MorphismProperty.of_isPullback hsq (P := @LocallyOfFiniteType) inferInstance
    have hflatbc : Flat (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) :=
      MorphismProperty.of_isPullback hsq (P := @Flat) inferInstance
    have hrbc : AlgebraicGeometry.RelativeDimension
        (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) r :=
      AlgebraicGeometry.RelativeDimension.of_isPullback hsq hr
    refine ⟨d, ?_, ?_⟩
    · exact bivariantCommute_of_isBivariantProperPushforward C G sZ (pullback.snd sX sZ)
        (bivariantPushforwardBaseChange g sX sZ) f hpp (-(r : ℤ)) q _ c' _
        (isBivariantProperPushforward_bivariantToBaseRestriction C G sX sZ hgys g r hr
          hS1 hRG hpp (h71 r) hflatbc hloftbc hrbc hdd)
        (bivariantCommute_flatPullbackBivariantClass C G sZ
          (bivariantPushforwardBaseChange g sX sZ ≫ pullback.snd sX sZ) f r hrbc hS1 hRG
          (h71 r) q c')
    · rw [bivariantToBaseEval_flatPullbackProperPushforward C G sX hS1 hRG hpp g r hr (h71 r)
        hdd]
      exact (eq_of_heq hβ).symm
  obtain ⟨c₀, hc₀, hc₀eval⟩ := hle (hgen sX p (bivariantToBaseEval C G sX p c))
  obtain rfl : c₀ = c := bivariantToBaseEval_injective C G sX p hS1 hfund hc₀eval
  intro T t _ k α
  exact hc₀ t k α

/-- **Stacks 0FBX, in the shape the tag states it.** The two composites `c ∘ c'` and `c' ∘ c`,
both bivariant classes of degree `p + q` for `X ×_S Y ⟶ Z`, agree as operations on every test
Chow group, under the canonical identification of their sources and the equality `p + q = q + p`
of their degrees.

This is `Stacks.Chow.bivariantCommute_bivariantToBase` read through
`Stacks.Chow.bivariantCommute_iff_commuteCompositeCap_eq`, the equivalence of Stacks 0FA2 between
commuting and the equality of the two composites. -/
@[stacks 0FBX "the equality of the two composites c ∘ c' = c' ∘ c of the tag, as operations on \
every test Chow group; the hypotheses are those of \
Stacks.Chow.bivariantCommute_bivariantToBase"]
theorem bivariantToBase_commuteCompositeCap_eq [Subsingleton C.S] [IsIntegral C.S]
    (c : bivariantToBase C G sX p)
    (c' : BivariantClass C G (f ≫ sZ) sZ f rfl q)
    (hpp : ProperPushforwardDescends C) (hS1 : FlatPullbackDescends C)
    (hRG : ProperPushforwardFlatPullbackBaseChange C)
    (h71 : ∀ r : ℕ, G.FlatPullbackNaturality r)
    (hEPK : BivariantProperPushforwardExists C G)
    (hgen : ChowClassesGeneratedByBaseFlatPullbacks C hS1 hpp)
    (hfund : IntegralFundamentalClassIsFlatPullback C hS1) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sZ) k),
      chowPushforwardOfIso C
          (pullback.fst (pullback.snd (pullback.snd sX sZ) f ≫ f) t ≫
            (pullback.fst (pullback.snd sX sZ) f ≫ (pullback.snd sX sZ ≫ sZ)))
          (pullback.fst (pullback.snd f (pullback.snd sX sZ) ≫ pullback.snd sX sZ) t ≫
            (pullback.fst f (pullback.snd sX sZ) ≫ (f ≫ sZ)))
          (compositeComparisonHom (pullback.snd sX sZ) f t)
          (compositeComparisonHom_comp_structureMorphism C sZ (pullback.snd sX sZ) f t)
          ((k - q) - p)
          (commuteCompositeCap C G sZ (pullback.snd sX sZ) f p q
            (bivariantToBaseRestrictionHom C G sX sZ p hgys c) c' hgys hpp t k α) =
        chowGroupDegreeEquiv C
          (pullback.fst (pullback.snd f (pullback.snd sX sZ) ≫ pullback.snd sX sZ) t ≫
            (pullback.fst f (pullback.snd sX sZ) ≫ (f ≫ sZ)))
          (by ring : (k - p) - q = (k - q) - p)
          (commuteCompositeCap C G sZ f (pullback.snd sX sZ) q p c'
            (bivariantToBaseRestrictionHom C G sX sZ p hgys c) hgys hpp t k α) :=
  (bivariantCommute_iff_commuteCompositeCap_eq C G sZ (pullback.snd sX sZ) f p q
      (bivariantToBaseRestrictionHom C G sX sZ p hgys c) c' hgys hpp).mp
    (bivariantCommute_bivariantToBase C G sX sZ f p q hgys c c' hpp hS1 hRG h71 hEPK hgen hfund)

end Main

end Stacks.Chow

end
