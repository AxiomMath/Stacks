module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Canonical
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.ProperPushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.WeakBivariantCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Coproduct
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.PiecePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ProperPushforwardChowBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.PrincipalReductionExistence

/-!
# Stacks 0F9A: a weak cap rule is a bivariant class

Let `(S, δ)` be as in Situation 02QL, let `f : X ⟶ Y` be locally of finite type and let
`p ∈ ℤ`. [Stacks, Tag 0F9A] (a weak form of Fulton's Theorem 17.1) says that a rule
`c ∩ - : A_k(Y') ⟶ A_{k-p}(Y' ×_Y X)` satisfying conditions (1) and (2) of [Stacks, Tag 0B76],
and condition (3) only for divisors `(ℒ', s', i' : D' ⟶ Y')` with `ℒ'|_{D'} ≅ 𝒪_{D'}`, is a
bivariant class. This file proves it: `Stacks.Chow.WeakCapRule.toBivariantClass`.

## The proof

Let `(ℒ, s, i : D ⟶ T)` be a divisor on a test scheme `g : T ⟶ Y`, with pullback
`(ℒ', s', j : E ⟶ T ×_Y X)`. [Stacks, Tag 0F99] supplies a square `D'' ⟶ T''` over `D ⟶ T`,
with `ρ : T'' ⟶ T` and `p : D'' ⟶ D` flat of relative dimension one and `D''` the zero scheme of
a global function, together with its base change `E'' ⟶ T'' ×_Y X` over `E ⟶ T ×_Y X`,
for which `q^* : A_*(E) ⟶ A_{*+1}(E'')` is injective and `q^*j^* = (j'')^*h^*`. Both squares
are built here from one diagram of [Stacks, Tag 0F97] and its base change, so that the upper
corner of the second is literally `T'' ×_Y X`, the base change of `T''` used by the cap rule.

Then for `α ∈ A_{k+1}(T)`,

  `q^*((j)^*(c ∩ α)) = (j'')^*h^*(c ∩ α) = (j'')^*(c ∩ ρ^*α) = c ∩ (i'')^*ρ^*α`
  `                  = c ∩ p^*i^*α = q^*(c ∩ i^*α)`,

by [Stacks, Tag 0F98] downstairs, condition (2) for `ρ`, the restricted condition (3) at the
principal divisor `D''` (whose normal bundle is trivial), [Stacks, Tag 0F98] upstairs, and
condition (2) for `p` together with the compatibility of flat pullback with the
identification of `E` (Stacks 02RG for an isomorphism); injectivity of `q^*` concludes.

## Main results

* `Stacks.Chow.WeakCapRule.cap_add` — the cap operations of a weak cap rule are additive, by
  conditions (1) and (2) applied to the fold map `T ⊔ T ⟶ T` and the two summand inclusions; the
  source asks only for maps.
* `Stacks.Chow.WeakCapRule.gysin_naturality` — condition (3) of [Stacks, Tag 0B76] for every
  divisor, for a weak cap rule read against the canonical Gysin system.
* `Stacks.Chow.WeakCapRule.toBivariantClass` — **[Stacks, Tag 0F9A]**.

## Implementation notes

The additivity argument and the lemmas on pieces of a finite open and closed decomposition it
uses are the ones of the faithful bivariant classes of Stacks 0B76 developed on a sibling
branch (`Stacks.Chow.BivariantChowClass.cap_add`); they are stated here, privately, for a weak
cap rule, and should be shared once both developments meet.

## References

* [Stacks Project, Tag 0F9A](https://stacks.math.columbia.edu/tag/0F9A)
* [Stacks Project, Tag 0F99](https://stacks.math.columbia.edu/tag/0F99)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The cap operations of a weak cap rule are additive -/

section Additive

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
  [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}

/-- The cap operations of a weak cap rule at two degrees are carried to one another by a
heterogeneous equality of classes. -/
private theorem WeakCapRule.heq_cap (c : WeakCapRule C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] {k l : ℤ} (hkl : k = l) {x : chowGroup C (g ≫ sY) k}
    {y : chowGroup C (g ≫ sY) l} (hxy : HEq x y) : HEq (c.cap g k x) (c.cap g l y) := by
  cases hkl
  exact heq_of_eq (congrArg (c.cap g k) (eq_of_heq hxy))

/-- The cap operation commutes with restricting the test scheme along an open immersion: this is
condition (2) in relative dimension zero, where flat pullback is restriction. -/
private theorem WeakCapRule.cap_chowGroupRestrict (c : WeakCapRule C G sX sY f hf p)
    {T T' : Scheme.{u}}
    (g : T ⟶ Y) [LocallyOfFiniteType g] (v : T' ⟶ T) [IsOpenImmersion v] (k : ℤ)
    (α : chowGroup C (g ≫ sY) k) :
    chowGroupRestrict C (pullback.fst f g ≫ sX) (pullback.fst f (v ≫ g) ≫ sX)
        (bivariantBaseChangeMap f g v) (bivariantBaseChangeMap_comp_structureMorphism sX f g v)
        (k - p) (c.cap g k α) =
      c.cap (v ≫ g) k
        (chowGroupRestrict C (g ≫ sY) ((v ≫ g) ≫ sY) v (Category.assoc _ _ _).symm k α) := by
  have hr : AlgebraicGeometry.RelativeDimension v 0 := relativeDimension_of_isOpenImmersion v
  have hr' : AlgebraicGeometry.RelativeDimension (bivariantBaseChangeMap f g v) 0 :=
    relativeDimension_of_isOpenImmersion _
  refine eq_of_heq ((heq_chowGroupRestrict_flatPullbackChow C _ _ _
      (bivariantBaseChangeMap_comp_structureMorphism sX f g v) hr' (k - p)
      (flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion C _ _ _
        (bivariantBaseChangeMap_comp_structureMorphism sX f g v) (k - p))
      (c.cap g k α)).trans ((c.flat_naturality g v 0 hr (bivariantBaseChangeMap f g v)
      (isPullback_bivariantBaseChangeMap f g v)
      (by simp [bivariantBaseChangeMap]) k hr' (flatPullbackDescends C _ _ _ _ _ _ _)
      (flatPullbackDescends C _ _ _ _ _ _ _) α).symm.trans ?_))
  exact WeakCapRule.heq_cap c (v ≫ g) (by simp)
    (heq_chowGroupRestrict_flatPullbackChow C _ _ v (Category.assoc _ _ _).symm hr k
      (flatPullbackFactorsThroughRationalEquivalence_of_isOpenImmersion C _ _ v
        (Category.assoc _ _ _).symm k) α).symm

/-- A test morphism equal to `g`, and a morphism over `X` between the two base changes lying over
the identity of the test scheme: pushforward along it carries the cap operation at the first test
morphism to the cap operation at `g`. -/
private theorem WeakCapRule.properChowPushforward_cap_of_eq (c : WeakCapRule C G sX sY f hf p)
    {T : Scheme.{u}}
    {g g' : T ⟶ Y} [LocallyOfFiniteType g] [LocallyOfFiniteType g'] (hg : g' = g)
    (hgY : g ≫ sY = g' ≫ sY) (v : pullback f g' ⟶ pullback f g) [IsProper v]
    (hvfst : v ≫ pullback.fst f g = pullback.fst f g')
    (hvsnd : v ≫ pullback.snd f g = pullback.snd f g')
    (hv : v ≫ pullback.fst f g ≫ sX = pullback.fst f g' ≫ sX) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C (pullback.fst f g' ≫ sX)
      (pullback.fst f g ≫ sX) v hv (k - p))
    (x : chowGroup C (g ≫ sY) k) :
    properChowPushforward C (pullback.fst f g' ≫ sX) (pullback.fst f g ≫ sX) v hv (k - p) hfac
        (c.cap g' k (chowGroupCongr C hgY k x)) = c.cap g k x := by
  subst hg
  obtain rfl : v = 𝟙 _ := pullback.hom_ext (by simpa using hvfst) (by simpa using hvsnd)
  exact DFunLike.congr_fun (properChowPushforward_id C _ (k - p) hfac) _

/-- The cap operation of a weak cap rule is additive. Write `α + β` as the pushforward along the
fold map `ν : T ⊔ T ⟶ T` of the class `γ` that is `α` on one summand and `β` on the other;
condition (1) for `ν` reduces `c ∩ (α + β)` to `c ∩ γ`, condition (2) for the two summand
inclusions computes `c ∩ γ` summand by summand, and the composites `T ⟶ T ⊔ T ⟶ T` are the
identity. -/
theorem WeakCapRule.cap_add (c : WeakCapRule C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α β : chowGroup C (g ≫ sY) k) :
    c.cap g k (α + β) = c.cap g k α + c.cap g k β := by
  classical
  let Z : ULift.{u} Bool → Scheme.{u} := fun _ ↦ T
  let ι : ∀ _ : ULift.{u} Bool, T ⟶ ∐ Z := fun i ↦ Sigma.ι Z i
  let ν : (∐ Z) ⟶ T := Sigma.desc fun _ ↦ 𝟙 T
  have hιν (i : ULift.{u} Bool) : ι i ≫ ν = 𝟙 T := Sigma.ι_comp_desc _ _
  have : ∀ i, IsOpenImmersion (ι i) := fun i ↦ inferInstanceAs (IsOpenImmersion (Sigma.ι Z i))
  have : ∀ i, IsClosedImmersion (ι i) := fun i ↦ isClosedImmersion_sigmaι Z i
  have : ∀ i, IsProper (ι i) := fun _ ↦ inferInstance
  have : IsProper ν := isProper_sigmaDesc_of_locallyFinite Z _ (locallyFinite_of_finite _)
  have hsum2 {M : Type u} [AddCommMonoid M] (F : ULift.{u} Bool → M) :
      ∑ i, F i = F ⟨true⟩ + F ⟨false⟩ := by
    rw [← Fintype.sum_equiv Equiv.ulift.symm (fun b ↦ F (Equiv.ulift.symm b)) F (fun _ ↦ rfl),
      Fintype.sum_bool]
    rfl
  let a : ULift.{u} Bool → chowGroup C (g ≫ sY) k := fun i ↦ if i.down then α else β
  have hb (i : ULift.{u} Bool) : g ≫ sY = (ι i ≫ ν ≫ g) ≫ sY := by
    rw [← Category.assoc, hιν, Category.id_comp]
  -- the class `a i` read on the test morphism `ι i ≫ ν ≫ g`
  let y : ∀ i, chowGroup C ((ι i ≫ ν ≫ g) ≫ sY) k := fun i ↦ chowGroupCongr C (hb i) k (a i)
  -- the class `γ` on `T ⊔ T`
  have hι (i : ULift.{u} Bool) : ι i ≫ (ν ≫ g) ≫ sY = (ι i ≫ ν ≫ g) ≫ sY := by
    simp only [Category.assoc]
  let γ : chowGroup C ((ν ≫ g) ≫ sY) k := ∑ i,
    properChowPushforward C ((ι i ≫ ν ≫ g) ≫ sY) ((ν ≫ g) ≫ sY) (ι i) (hι i) k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ (hι i) k) (y i)
  have hγ : properChowPushforward C ((ν ≫ g) ≫ sY) (g ≫ sY) ν (Category.assoc _ _ _).symm k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
        (Category.assoc _ _ _).symm k) γ = α + β := by
    have key (i : ULift.{u} Bool) :
        properChowPushforward C ((ν ≫ g) ≫ sY) (g ≫ sY) ν (Category.assoc _ _ _).symm k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
            (Category.assoc _ _ _).symm k)
          (properChowPushforward C ((ι i ≫ ν ≫ g) ≫ sY) ((ν ≫ g) ≫ sY) (ι i) (hι i) k
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ (hι i) k)
            (y i)) = a i := by
      have hw : (ι i ≫ ν) ≫ g ≫ sY = (ι i ≫ ν ≫ g) ≫ sY := by simp only [Category.assoc]
      rw [← properChowPushforward_comp_apply C _ _ _ (ι i) ν (ι i ≫ ν) rfl (hι i)
        (Category.assoc _ _ _).symm hw k _ _
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ hw k)]
      exact properChowPushforward_chowGroupCongr_of_eq_id C (hb i) (ι i ≫ ν) (hιν i) hw k _ _
    simp only [γ, map_sum]
    rw [hsum2, key, key]
    rfl
  -- the pieces of `(T ⊔ T) ×_Y X`
  let m : ∀ i, pullback f (ι i ≫ ν ≫ g) ⟶ pullback f (ν ≫ g) := fun i ↦
    bivariantBaseChangeMap f (ν ≫ g) (ι i)
  have hm (i : ULift.{u} Bool) : m i ≫ pullback.fst f (ν ≫ g) ≫ sX =
      pullback.fst f (ι i ≫ ν ≫ g) ≫ sX :=
    bivariantBaseChangeMap_comp_structureMorphism sX f (ν ≫ g) (ι i)
  have hrange (i : ULift.{u} Bool) :
      Set.range (m i).base = (pullback.snd f (ν ≫ g)).base ⁻¹' Set.range (ι i).base :=
    range_base_of_isPullback _ (m i) (ι i) _
      (isPullback_bivariantBaseChangeMap f (ν ≫ g) (ι i)).flip
  have hdisjι : Pairwise fun i j ↦ Disjoint (Set.range (ι i).base) (Set.range (ι j).base) :=
    pairwise_disjoint_range_sigmaι Z
  have hdisjm : Pairwise fun i j ↦ Disjoint (Set.range (m i).base) (Set.range (m j).base) := by
    intro i j hij
    rw [hrange, hrange]
    exact (hdisjι hij).preimage _
  have hdec : IsClopenDecomposition fun i ↦ (m i).opensRange :=
    isClopenDecomposition_of_isOpenImmersion_cover m
      (fun x ↦ by
        obtain ⟨i, hi⟩ := exists_mem_range_sigmaι Z ((pullback.snd f (ν ≫ g)).base x)
        exact ⟨i, by rwa [hrange]⟩)
      hdisjm
  -- `c ∩ γ`, summand by summand
  have hcapγ : c.cap (ν ≫ g) k γ = ∑ i,
      properChowPushforward C (pullback.fst f (ι i ≫ ν ≫ g) ≫ sX)
        (pullback.fst f (ν ≫ g) ≫ sX) (m i) (hm i) (k - p)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ (hm i) (k - p))
        (c.cap (ι i ≫ ν ≫ g) k (y i)) := by
    rw [← sub_eq_zero]
    refine eq_zero_of_chowGroupRestrict_eq_zero C (pullback.fst f (ν ≫ g) ≫ sX)
      (fun i ↦ pullback.fst f (ι i ≫ ν ≫ g) ≫ sX) m hm hdec (k - p) _ fun j ↦ ?_
    rw [map_sub, sub_eq_zero, WeakCapRule.cap_chowGroupRestrict c (ν ≫ g) (ι j) k γ,
      chowGroupRestrict_sum_properChowPushforward C _ _ m hm hdisjm (k - p) _ j]
    congr 1
    exact chowGroupRestrict_sum_properChowPushforward C _ _ ι hι hdisjι k y j
  calc c.cap g k (α + β)
      = c.cap g k (properChowPushforward C ((ν ≫ g) ≫ sY) (g ≫ sY) ν
          (Category.assoc _ _ _).symm k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
            (Category.assoc _ _ _).symm k) γ) := by rw [hγ]
    _ = properChowPushforward C (pullback.fst f (ν ≫ g) ≫ sX) (pullback.fst f g ≫ sX)
          (bivariantBaseChangeMap f g ν) (bivariantBaseChangeMap_comp_structureMorphism sX f g ν)
          (k - p)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
            (bivariantBaseChangeMap_comp_structureMorphism sX f g ν) (k - p))
          (c.cap (ν ≫ g) k γ) :=
          c.proper_naturality g ν (bivariantBaseChangeMap f g ν)
            (isPullback_bivariantBaseChangeMap f g ν) (by simp [bivariantBaseChangeMap]) k _ _ γ
    _ = ∑ i, c.cap g k (a i) := by
      rw [hcapγ, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hv : (m i ≫ bivariantBaseChangeMap f g ν) ≫ pullback.fst f g ≫ sX =
          pullback.fst f (ι i ≫ ν ≫ g) ≫ sX := by
        simp [m, bivariantBaseChangeMap]
      rw [← properChowPushforward_comp_apply C _ _ _ (m i) (bivariantBaseChangeMap f g ν)
        (m i ≫ bivariantBaseChangeMap f g ν) rfl (hm i)
        (bivariantBaseChangeMap_comp_structureMorphism sX f g ν) hv (k - p) _ _
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _ hv (k - p))]
      exact WeakCapRule.properChowPushforward_cap_of_eq c
        (by rw [← Category.assoc, hιν, Category.id_comp])
        (hb i) _ (by simp [m, bivariantBaseChangeMap])
        (by simp [m, bivariantBaseChangeMap, hιν i]) hv k _ (a i)
    _ = c.cap g k α + c.cap g k β := by
      rw [hsum2]
      rfl

end Additive

/-! ### Congruence of the three operations -/

section Congr

variable (C : ChowSituation.{u})

/-- Flat pullback on Chow groups respects heterogeneous equality in all of its arguments. -/
theorem flatPullbackChow_heq_of_eq {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [hsAi : LocallyOfFiniteType sA] [hsA'i : LocallyOfFiniteType sA']
    {sB sB' : B ⟶ C.S} [hsBi : LocallyOfFiniteType sB] [hsB'i : LocallyOfFiniteType sB']
    {x x' : A ⟶ B} [hxl : LocallyOfFiniteType x] [hxf : Flat x] [hx'l : LocallyOfFiniteType x']
    [hx'f : Flat x']
    (hsA : sA = sA') (hsB : sB = sB') (hx : x = x')
    (hb : x ≫ sB = sA) (hb' : x' ≫ sB' = sA') {r r' : ℕ} (hr : r = r')
    (hxr : AlgebraicGeometry.RelativeDimension x r)
    (hxr' : AlgebraicGeometry.RelativeDimension x' r') {k k' : ℤ} (hk : k = k')
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB x hb r hxr k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sA' sB' x' hb' r' hxr' k')
    {a : chowGroup C sB k} {a' : chowGroup C sB' k'} (ha : a ≍ a') :
    flatPullbackChow C sA sB x hb r hxr k hfac a ≍
      flatPullbackChow C sA' sB' x' hb' r' hxr' k' hfac' a' := by
  subst hsA hsB hx hr hk
  rw [eq_of_heq ha]

/-- `Stacks.Chow.flatPullbackChowOfRelativeDimension` respects heterogeneous equality in all of
its arguments. -/
theorem flatPullbackChowOfRelativeDimension_heq_of_eq {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [hsAi : LocallyOfFiniteType sA] [hsA'i : LocallyOfFiniteType sA']
    {sB sB' : B ⟶ C.S} [hsBi : LocallyOfFiniteType sB] [hsB'i : LocallyOfFiniteType sB']
    {x x' : A ⟶ B} [hxl : LocallyOfFiniteType x] [hxf : Flat x] [hx'l : LocallyOfFiniteType x']
    [hx'f : Flat x']
    (hsA : sA = sA') (hsB : sB = sB') (hx : x = x')
    (hb : x ≫ sB = sA) (hb' : x' ≫ sB' = sA') {r r' : ℕ} (hr : r = r')
    (hxr : AlgebraicGeometry.RelativeDimension x r)
    (hxr' : AlgebraicGeometry.RelativeDimension x' r') {k k' : ℤ} (hk : k = k')
    {a : chowGroup C sB k} {a' : chowGroup C sB' k'} (ha : a ≍ a') :
    flatPullbackChowOfRelativeDimension C sA sB x hb r hxr k a ≍
      flatPullbackChowOfRelativeDimension C sA' sB' x' hb' r' hxr' k' a' := by
  subst hsA hsB hx hr hk
  rw [eq_of_heq ha]

/-- An additive map into the Chow group of a closed subscheme, read at an equal ideal sheaf. -/
theorem heq_apply_of_idealSheaf_eq {T : Scheme.{u}} (q : T ⟶ C.S) [LocallyOfFiniteType q]
    {A : Type*} [AddCommGroup A] {k : ℤ} {I J : T.IdealSheafData} (hIJ : I = J)
    (F : A →+ chowGroup C (I.subschemeι ≫ q) k) (G : A →+ chowGroup C (J.subschemeι ≫ q) k)
    (hFG : F ≍ G) (a : A) : F a ≍ G a := by
  subst hIJ
  rw [eq_of_heq hFG]

/-- The Gysin map of Stacks 02TO respects heterogeneous equality in the structure morphism, the
degree and the argument, and depends on the pair `(L, s)` only through its isomorphism class. -/
theorem gysinChowOfInvertible_heq_of_eq {T : Scheme.{u}} {q q' : T ⟶ C.S}
    [hqi : LocallyOfFiniteType q] [hq'i : LocallyOfFiniteType q'] (hq : q = q') {k k' : ℤ}
    (hk : k = k')
    {M N : T.Modules}
    [hMi : AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property M]
    [hNi : AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property N]
    (sM : Γ(M, ⊤)) (sN : Γ(N, ⊤)) (φ : M ≅ N)
    (hz : Stacks.Divisors.zeroScheme T M sM = Stacks.Divisors.zeroScheme T N sN)
    {a : chowGroup C q (k + 1)} {b : chowGroup C q' (k' + 1)} (hab : a ≍ b) :
    gysinChowOfInvertible C q k M sM a ≍ gysinChowOfInvertible C q' k' N sN b := by
  subst hq hk
  rw [eq_of_heq hab]
  exact heq_apply_of_idealSheaf_eq C q hz _ _
    (heq_gysinChowOfInvertible_of_moduleIso C q k sM sN φ hz) b

/-- Proper pushforward on Chow groups respects heterogeneous equality in the structure
morphisms, the degree and the argument. -/
theorem properChowPushforward_heq_of_eq {A B : Scheme.{u}}
    {sA sA' : A ⟶ C.S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    {sB sB' : B ⟶ C.S} [LocallyOfFiniteType sB] [hsB'i : LocallyOfFiniteType sB'] (v : A ⟶ B)
    [IsProper v] (hsA : sA = sA') (hsB : sB = sB') (hv : v ≫ sB = sA) (hv' : v ≫ sB' = sA')
    {k k' : ℤ} (hk : k = k')
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB v hv k)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence C sA' sB' v hv' k')
    {a : chowGroup C sA k} {a' : chowGroup C sA' k'} (ha : a ≍ a') :
    properChowPushforward C sA sB v hv k hfac a ≍
      properChowPushforward C sA' sB' v hv' k' hfac' a' := by
  subst hsA hsB hk
  rw [eq_of_heq ha]

end Congr

/-! ### Two isomorphisms of base changes -/

section Isos

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The map `Z ×_Y X ⟶ T ×_Y X` induced by `j : Z ⟶ T`, for a test morphism `b : Z ⟶ Y`
presented by an equality `j ≫ g₀ = b`. -/
def baseChangeMapOfComp {Z T : Scheme.{u}} (b : Z ⟶ Y) (j : Z ⟶ T) (g₀ : T ⟶ Y)
    (hb : j ≫ g₀ = b) : pullback f b ⟶ pullback f g₀ :=
  pullback.map f b f g₀ (𝟙 X) j (𝟙 Y) (by simp) (by simp [hb])

/-- For `j : Z ⟶ T` and `j ≫ g₀ = b`, the square formed by `Z ×_Y X ⟶ Z`, the induced map
`Z ×_Y X ⟶ T ×_Y X`, `j` and `T ×_Y X ⟶ T` is a pullback square. -/
theorem isPullback_baseChangeMapOfComp {Z T : Scheme.{u}} (b : Z ⟶ Y) (j : Z ⟶ T)
    (g₀ : T ⟶ Y) (hb : j ≫ g₀ = b) :
    IsPullback (pullback.snd f b) (baseChangeMapOfComp f b j g₀ hb) j (pullback.snd f g₀) := by
  subst hb
  exact isPullback_bivariantBaseChangeMap f g₀ j

/-- The maps `Z ×_Y X ⟶ T ×_Y X` induced by `j` at two equal test morphisms `a = b` are
heterogeneously equal. -/
theorem baseChangeMapOfComp_heq {Z T : Scheme.{u}} (a b : Z ⟶ Y) (hab : a = b) (j : Z ⟶ T)
    (g₀ : T ⟶ Y) (ha : j ≫ g₀ = a) (hb : j ≫ g₀ = b) :
    baseChangeMapOfComp f a j g₀ ha ≍ baseChangeMapOfComp f b j g₀ hb := by
  subst hab
  rfl

/-- **The base change of a closed subscheme pulled back along a base change.** For a closed
subscheme `I ⊆ T` and a test morphism `b : Z ⟶ Y` factoring as `I ↪ T ⟶ Y` (through `j`), the
base change `Z ×_Y X` is the closed subscheme `I.comap (T ×_Y X ⟶ T)` of `T ×_Y X`. -/
def baseChangeSubschemeIso {T : Scheme.{u}} (g₀ : T ⟶ Y) (I : T.IdealSheafData)
    (K : (pullback f g₀).IdealSheafData) (hK : I.comap (pullback.snd f g₀) = K)
    (b : I.subscheme ⟶ Y) (hb : I.subschemeι ≫ g₀ = b) :
    pullback f b ≅ K.subscheme :=
  (isPullback_baseChangeMapOfComp f b I.subschemeι g₀ hb).flip.isoIsPullback _ _
    (Scheme.IdealSheafData.isPullback_subschemeMap_of_comap (pullback.snd f g₀) hK)

/-- The isomorphism `baseChangeSubschemeIso` followed by the inclusion of `K.subscheme` into
`T ×_Y X` is the map `baseChangeMapOfComp` induced by the inclusion `I ↪ T`. -/
@[reassoc]
theorem baseChangeSubschemeIso_hom_subschemeι {T : Scheme.{u}} (g₀ : T ⟶ Y)
    (I : T.IdealSheafData) (K : (pullback f g₀).IdealSheafData)
    (hK : I.comap (pullback.snd f g₀) = K) (b : I.subscheme ⟶ Y)
    (hb : I.subschemeι ≫ g₀ = b) :
    (baseChangeSubschemeIso f g₀ I K hK b hb).hom ≫ K.subschemeι =
      baseChangeMapOfComp f b I.subschemeι g₀ hb :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

end Isos

/-! ### Transport of the cap operation along an equality of test morphisms -/

section CapTransport

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
  [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}

/-- The cap operation of a weak cap rule at two equal test morphisms, pushed forward along
isomorphisms onto two equal closed subschemes compatibly with given maps, gives heterogeneously
equal classes. -/
theorem WeakCapRule.properChowPushforward_cap_heq (w : WeakCapRule C G sX sY f hf p)
    {Z N : Scheme.{u}} {a b : Z ⟶ Y} [LocallyOfFiniteType a] [LocallyOfFiniteType b]
    (hab : a = b) {k k' : ℤ} (hk : k = k') {x : chowGroup C (a ≫ sY) k}
    {y : chowGroup C (b ≫ sY) k'} (hxy : x ≍ y) (sN : N ⟶ C.S) [LocallyOfFiniteType sN]
    {M M' : N.IdealSheafData} (hM : M = M') (ea : pullback f a ≅ M.subscheme)
    (eb : pullback f b ≅ M'.subscheme) (ua : pullback f a ⟶ N) (ub : pullback f b ⟶ N)
    (hua : ea.hom ≫ M.subschemeι = ua) (hub : eb.hom ≫ M'.subschemeι = ub) (hu : ua ≍ ub)
    (hba : ea.hom ≫ (M.subschemeι ≫ sN) = pullback.fst f a ≫ sX)
    (hbb : eb.hom ≫ (M'.subschemeι ≫ sN) = pullback.fst f b ≫ sX)
    (hfa : ProperPushforwardFactorsThroughRationalEquivalence C (pullback.fst f a ≫ sX)
      (M.subschemeι ≫ sN) ea.hom hba (k - p))
    (hfb : ProperPushforwardFactorsThroughRationalEquivalence C (pullback.fst f b ≫ sX)
      (M'.subschemeι ≫ sN) eb.hom hbb (k' - p)) :
    properChowPushforward C (pullback.fst f a ≫ sX) (M.subschemeι ≫ sN) ea.hom hba (k - p) hfa
        (w.cap a k x) ≍
      properChowPushforward C (pullback.fst f b ≫ sX) (M'.subschemeι ≫ sN) eb.hom hbb (k' - p)
        hfb (w.cap b k' y) := by
  subst hab hk hM
  rw [eq_of_heq hxy]
  obtain rfl : ua = ub := eq_of_heq hu
  obtain rfl : ea = eb := Iso.ext (by rw [← cancel_mono M.subschemeι, hua, hub])
  rfl

end CapTransport

/-! ### The Gysin condition for every divisor -/

section Main

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {f : X ⟶ Y}
  [LocallyOfFiniteType f] {hf : f ≫ sY = sX} {p : ℤ}

/-- Condition (2) of a weak cap rule for a flat `h`, along the canonical base change
`bivariantBaseChangeMap f g h` of `h`, with all side conditions discharged. -/
private theorem WeakCapRule.flat_naturality_baseChange {G : GysinSystem C}
    (w : WeakCapRule C G sX sY f hf p) {T T' : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (h : T' ⟶ T) [LocallyOfFiniteType h] [Flat h] (r : ℕ)
    (hr : AlgebraicGeometry.RelativeDimension h r) (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    letI : LocallyOfFiniteType (bivariantBaseChangeMap f g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g h) inferInstance
    letI : Flat (bivariantBaseChangeMap f g h) :=
      MorphismProperty.of_isPullback (isPullback_bivariantBaseChangeMap f g h) inferInstance
    HEq (w.cap (h ≫ g) (k + (r : ℤ))
        (flatPullbackChow C ((h ≫ g) ≫ sY) (g ≫ sY) h (by simp [Category.assoc]) r hr k
          (flatPullbackDescends C _ _ _ _ _ _ _) α))
      (flatPullbackChow C (pullback.fst f (h ≫ g) ≫ sX) (pullback.fst f g ≫ sX)
        (bivariantBaseChangeMap f g h) (bivariantBaseChangeMap_comp_structureMorphism sX f g h) r
        (AlgebraicGeometry.RelativeDimension.of_isPullback
          (isPullback_bivariantBaseChangeMap f g h) hr) (k - p)
        (flatPullbackDescends C _ _ _ _ _ _ _) (w.cap g k α)) :=
  w.flat_naturality g h r hr (bivariantBaseChangeMap f g h)
    (isPullback_bivariantBaseChangeMap f g h) (by simp [bivariantBaseChangeMap]) k _ _ _ α

open TensorZeroScheme in
/-- **Condition (3) of [Stacks, Tag 0B76] for a weak cap rule, for every divisor.** A weak cap
rule read against the canonical Gysin system commutes with the Gysin map of the zero scheme of
every section of every invertible module on every test scheme, not only of those whose normal
bundle is trivial. -/
theorem WeakCapRule.gysin_naturality (w : WeakCapRule C (canonicalGysinSystem C) sX sY f hf p) :
    ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (L : T.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
      [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback f g).sheaf.obj
        (pullback f g).ringCatSheaf.property
        ((Scheme.Modules.pullback (pullback.snd f g)).obj L)]
      (s : Γ(L, ⊤)) (k : ℤ),
      let D := Stacks.Divisors.zeroScheme T L s
      let L' := (Scheme.Modules.pullback (pullback.snd f g)).obj L
      let s' := AlgebraicGeometry.pullbackGlobalSections (pullback.snd f g) L s
      let E := Stacks.Divisors.zeroScheme (pullback f g) L' s'
      ∀ (e : pullback f (D.subschemeι ≫ g) ≅ E.subscheme)
        (_he : e.hom ≫ E.subschemeι = bivariantBaseChangeMap f g D.subschemeι)
        (hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst f g ≫ sX) =
          pullback.fst f (D.subschemeι ≫ g) ≫ sX)
        (hfac : ProperPushforwardFactorsThroughRationalEquivalence C
          (pullback.fst f (D.subschemeι ≫ g) ≫ sX) (E.subschemeι ≫ pullback.fst f g ≫ sX)
          e.hom hbase (k - p))
        (α : chowGroup C (g ≫ sY) (k + 1)),
        properChowPushforward C (pullback.fst f (D.subschemeι ≫ g) ≫ sX)
            (E.subschemeι ≫ pullback.fst f g ≫ sX) e.hom hbase (k - p) hfac
            (w.cap (D.subschemeι ≫ g) k ((canonicalGysinSystem C).onChow (g ≫ sY) L s k α)) =
          (canonicalGysinSystem C).onChow (pullback.fst f g ≫ sX) L' s' (k - p)
            (Eq.mp (congrArg (chowGroup C (pullback.fst f g ≫ sX))
              (by omega : (k + 1) - p = (k - p) + 1)) (w.cap g (k + 1) α)) := by
  intro T g₀ _ L _ _ s k D L' s' E e he hbase hfac α
  -- the diagram of Tag 0F97 for `s` read in `𝒪_T ⊗ ℒ`, and the two reductions of Tag 0F99
  let R0 := decomposition T (Scheme.unitModule T) L (unitTensorSection T L s)
  let RT := principalReductionOfDecomposition R0 (Iso.refl _) C (g₀ ≫ sY) L s
    (unitTensorUnitor T L) (zeroScheme_unitTensorSection T L s)
  have hsq := isPullback_bivariantBaseChangeMap f g₀ RT.g
  let RP := principalReductionBaseChange R0 (Iso.refl _) C L s (unitTensorUnitor T L)
    (zeroScheme_unitTensorSection T L s) (pullback.snd f g₀) (pullback.fst f g₀ ≫ sX) hsq
  have hRPbr : RP.branch = RT.branch.comap (pullback.snd f (RT.g ≫ g₀)) :=
    principalReductionBaseChange_branch R0 (Iso.refl _) C (g₀ ≫ sY) L s (unitTensorUnitor T L)
      (zeroScheme_unitTensorSection T L s) (pullback.snd f g₀) (pullback.fst f g₀ ≫ sX) hsq
  have : LocallyOfFiniteType RP.g := RP.g_locallyOfFiniteType
  have : AlgebraicGeometry.Flat RP.g := RP.g_flat
  have : LocallyOfFiniteType RP.p := RP.p_locallyOfFiniteType
  have : AlgebraicGeometry.Flat RP.p := RP.p_flat
  have : LocallyOfFiniteType (RP.g ≫ pullback.fst f g₀ ≫ sX) := inferInstance
  have : LocallyOfFiniteType RP.branchStructureMorphism := inferInstance
  -- the principal divisor `D'' = Z(t)` upstairs and its base change `E''`
  let D₂ := Stacks.Divisors.zeroScheme RT.X' (Scheme.unitModule RT.X') RT.s'
  let E₂ := Stacks.Divisors.zeroScheme (pullback f (RT.g ≫ g₀))
    ((Scheme.Modules.pullback (pullback.snd f (RT.g ≫ g₀))).obj (Scheme.unitModule RT.X'))
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd f (RT.g ≫ g₀))
      (Scheme.unitModule RT.X') RT.s')
  have hE'' : D₂.comap (pullback.snd f (RT.g ≫ g₀)) = E₂ :=
    (Stacks.Divisors.zeroScheme_pullback (pullback.snd f (RT.g ≫ g₀))
      (Scheme.unitModule RT.X') RT.s').symm
  obtain ⟨e₃, he₃⟩ : ∃ e₃ : pullback f (D₂.subschemeι ≫ (RT.g ≫ g₀)) ≅ E₂.subscheme,
      e₃.hom ≫ E₂.subschemeι = bivariantBaseChangeMap f (RT.g ≫ g₀) D₂.subschemeι :=
    ⟨baseChangeSubschemeIso f (RT.g ≫ g₀) _ _ hE'' _ rfl,
      baseChangeSubschemeIso_hom_subschemeι f (RT.g ≫ g₀) _ _ hE'' _ rfl⟩
  have hbase₃ : e₃.hom ≫ (E₂.subschemeι ≫ pullback.fst f (RT.g ≫ g₀) ≫ sX) =
      pullback.fst f (D₂.subschemeι ≫ (RT.g ≫ g₀)) ≫ sX := by
    have := congrArg (fun m => m ≫ pullback.fst f (RT.g ≫ g₀) ≫ sX) he₃
    simp only [Category.assoc] at this
    refine this.trans ?_
    simp [bivariantBaseChangeMap]
  have htriv : AlgebraicGeometry.SheafOfModules.IsTrivial D₂.subscheme.sheaf.obj
      D₂.subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback D₂.subschemeι).obj (Scheme.unitModule RT.X')) :=
    ⟨Scheme.Modules.pullbackUnitIso _⟩
  -- the restricted condition (3) at `D''`
  have h3 := w.gysin_naturality_of_isTrivial (RT.g ≫ g₀) (Scheme.unitModule RT.X') RT.s'
    (k + 1) htriv e₃ he₃ hbase₃ (properPushforwardDescends C _ _ _ _ _)
    (flatPullbackChow C ((RT.g ≫ g₀) ≫ sY) (g₀ ≫ sY) RT.g (by simp [Category.assoc]) 1
      RT.g_relativeDimension (k + 1) (flatPullbackDescends C _ _ _ _ _ _ _) α)
  -- condition (2) along `ρ = RT.g`
  have hfstρ : bivariantBaseChangeMap f g₀ RT.g ≫ pullback.fst f g₀ =
      pullback.fst f (RT.g ≫ g₀) := by
    simp [bivariantBaseChangeMap]
  have h2ρ := w.flat_naturality_baseChange g₀ RT.g 1 RT.g_relativeDimension (k + 1) α
  -- condition (2) along `p : D'' ⟶ D`
  have hfstp : bivariantBaseChangeMap f (D.subschemeι ≫ g₀) RT.p ≫
      pullback.fst f (D.subschemeι ≫ g₀) = pullback.fst f (RT.p ≫ (D.subschemeι ≫ g₀)) := by
    simp [bivariantBaseChangeMap]
  have h2p := w.flat_naturality_baseChange (D.subschemeι ≫ g₀) RT.p 1 RT.p_relativeDimension k
    (gysinChowOfInvertible C (g₀ ≫ sY) k L s α)
  -- Tag 0F98 upstairs and downstairs
  have h4T := RT.gysinBranch_flatPullbackAmbient k α
  have h4P := RP.gysinBranch_flatPullbackAmbient (k - p)
    (Eq.mp (congrArg (chowGroup C (pullback.fst f g₀ ≫ sX))
      (by omega : (k + 1) - p = (k - p) + 1)) (w.cap g₀ (k + 1) α))
  -- the identification of `E'' ⊆ T'' ×_Y X` used by the reduction, as a base change
  have hm : D₂.subschemeι ≫
      (RT.g ≫ g₀) = RT.p ≫ (D.subschemeι ≫ g₀) := by
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun m => m ≫ g₀) RT.comm
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : pullback f (RT.p ≫ (D.subschemeι ≫ g₀)) ≅ RP.branch.subscheme,
      e₂.hom ≫ RP.branch.subschemeι =
        baseChangeMapOfComp f (RT.p ≫ (D.subschemeι ≫ g₀)) RT.branch.subschemeι (RT.g ≫ g₀)
          hm :=
    ⟨baseChangeSubschemeIso f (RT.g ≫ g₀) RT.branch RP.branch hRPbr.symm _ hm,
      baseChangeSubschemeIso_hom_subschemeι f (RT.g ≫ g₀) RT.branch RP.branch hRPbr.symm _ hm⟩
  have hc1 : (bivariantBaseChangeMap f (D.subschemeι ≫ g₀) RT.p ≫ e.hom) ≫ E.subschemeι =
      bivariantBaseChangeMap f (D.subschemeι ≫ g₀) RT.p ≫
        bivariantBaseChangeMap f g₀ D.subschemeι :=
    (Category.assoc _ _ _).trans
      (congrArg (fun m => bivariantBaseChangeMap f (D.subschemeι ≫ g₀) RT.p ≫ m) he)
  have hc2 : (e₂.hom ≫ RP.p) ≫ E.subschemeι =
      baseChangeMapOfComp f (RT.p ≫ (D.subschemeι ≫ g₀)) RT.branch.subschemeι (RT.g ≫ g₀) hm ≫
        bivariantBaseChangeMap f g₀ RT.g :=
    (Category.assoc _ _ _).trans ((congrArg (fun m => e₂.hom ≫ m) RP.comm.symm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ RP.g) he₂)))
  have hc3 : bivariantBaseChangeMap f (D.subschemeι ≫ g₀) RT.p ≫
        bivariantBaseChangeMap f g₀ D.subschemeι =
      baseChangeMapOfComp f (RT.p ≫ (D.subschemeι ≫ g₀)) RT.branch.subschemeι (RT.g ≫ g₀) hm ≫
        bivariantBaseChangeMap f g₀ RT.g := by
    refine pullback.hom_ext ?_ ?_
    · simp only [bivariantBaseChangeMap, baseChangeMapOfComp, pullback.map, Category.assoc,
        Category.comp_id]
      repeat rw [pullback.lift_fst]
    · simp only [bivariantBaseChangeMap, baseChangeMapOfComp, pullback.map, Category.assoc]
      repeat rw [pullback.lift_snd]
      repeat rw [pullback.lift_snd_assoc]
      rw [Category.assoc, Category.assoc, RT.comm]
  have hcomm : bivariantBaseChangeMap f (D.subschemeι ≫ g₀) RT.p ≫ e.hom = e₂.hom ≫ RP.p :=
    (cancel_mono E.subschemeι).1 (hc1.trans (hc3.trans hc2.symm))
  have hpb : IsPullback (bivariantBaseChangeMap f (D.subschemeι ≫ g₀) RT.p) e₂.hom e.hom RP.p :=
    IsPullback.of_vert_isIso ⟨hcomm⟩
  -- `q^*` is injective: compare the two sides after pulling back to `E''`
  apply RP.flatPullbackBranch_injective (k - p)
  refine Eq.trans ?_ h4P
  apply eq_of_heq
  -- Stacks 02RG for the cartesian square `(h', e₂, e, q)`
  have hg' : bivariantBaseChangeMap f (D.subschemeι ≫ g₀) RT.p ≫
      (pullback.fst f (D.subschemeι ≫ g₀) ≫ sX) =
        pullback.fst f (RT.p ≫ (D.subschemeι ≫ g₀)) ≫ sX :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ sX) hfstp)
  have hrg := DFunLike.congr_fun (flatPullbackChow_comp_properChowPushforward_of_isPullback C
      (pullback.fst f (D.subschemeι ≫ g₀) ≫ sX) (E.subschemeι ≫ pullback.fst f g₀ ≫ sX)
      (pullback.fst f (RT.p ≫ (D.subschemeι ≫ g₀)) ≫ sX) RP.branchStructureMorphism
      e.hom RP.p (bivariantBaseChangeMap f (D.subschemeι ≫ g₀) RT.p) e₂.hom hpb hbase
      RP.p_comp_structureMorphism hg' 1 RP.p_relativeDimension (k - p))
      (w.cap (D.subschemeι ≫ g₀) k (gysinChowOfInvertible C (g₀ ≫ sY) k L s α))
  refine (heq_of_eq hrg).trans ?_
  -- condition (2) along `p`
  have hsN : RP.g ≫ pullback.fst f g₀ ≫ sX = pullback.fst f (RT.g ≫ g₀) ≫ sX := by
    rw [← Category.assoc]
    exact congrArg (fun m => m ≫ sX) hfstρ
  -- the class `p^*i^*α` and the class `(i'')^*ρ^*α` agree
  have hyy : flatPullbackChow C ((RT.p ≫ (D.subschemeι ≫ g₀)) ≫ sY) ((D.subschemeι ≫ g₀) ≫ sY)
        RT.p (by simp [Category.assoc]) 1 RT.p_relativeDimension k
        (flatPullbackDescends C _ _ _ _ _ _ _) (gysinChowOfInvertible C (g₀ ≫ sY) k L s α) ≍
      (canonicalGysinSystem C).onChow ((RT.g ≫ g₀) ≫ sY) (Scheme.unitModule RT.X') RT.s' (k + 1)
        (flatPullbackChow C ((RT.g ≫ g₀) ≫ sY) (g₀ ≫ sY) RT.g (by simp [Category.assoc]) 1
          RT.g_relativeDimension (k + 1) (flatPullbackDescends C _ _ _ _ _ _ _) α) := by
    refine HEq.trans ?_ (HEq.trans (heq_of_eq h4T.symm) ?_)
    · exact flatPullbackChow_heq_of_eq C
        (by rw [Category.assoc, Category.assoc, ← Category.assoc RT.p, ← RT.comm]; rfl)
        (Category.assoc _ _ _) rfl _ _ rfl _ _ rfl (flatPullbackDescends C _ _ _ _ _ _ _)
        (flatPullbackDescends C _ _ _ _ _ _ _) HEq.rfl
    · exact gysinChowOfInvertible_heq_of_eq C (Category.assoc _ _ _).symm rfl _ _ (Iso.refl _) rfl
        (flatPullbackChow_heq_of_eq C (Category.assoc _ _ _).symm rfl rfl _ _ rfl _ _ rfl
          (flatPullbackDescends C _ _ _ _ _ _ _) (flatPullbackDescends C _ _ _ _ _ _ _) HEq.rfl)
  have hv2 : e₂.hom ≫ (RP.branch.subschemeι ≫ pullback.fst f (RT.g ≫ g₀) ≫ sX) =
      pullback.fst f (RT.p ≫ (D.subschemeι ≫ g₀)) ≫ sX := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun m => m ≫ pullback.fst f (RT.g ≫ g₀) ≫ sX) he₂).trans ?_
    simp [baseChangeMapOfComp]
  have hsN' :
      RP.branchStructureMorphism = RP.branch.subschemeι ≫ pullback.fst f (RT.g ≫ g₀) ≫ sX :=
    congrArg (fun m => RP.branch.subschemeι ≫ m) hsN
  have hlft : LocallyOfFiniteType (RP.branch.subschemeι ≫ pullback.fst f (RT.g ≫ g₀) ≫ sX) :=
    hsN' ▸ (inferInstance : LocallyOfFiniteType RP.branchStructureMorphism)
  -- condition (2) along `p`, transported to the identification `e₂`
  refine HEq.trans (properChowPushforward_heq_of_eq C e₂.hom rfl hsN' _ hv2
    (by push_cast; ring) (properPushforwardDescends C _ _ _ _ _)
    (@properPushforwardDescends C _ _ _ _ _ hlft _ _ _ _) h2p.symm
    (hsB'i := hlft)) ?_
  -- the cap operation at the two presentations of `D'' ×_Y X`
  refine HEq.trans (w.properChowPushforward_cap_heq hm.symm (by norm_num) hyy
    (pullback.fst f (RT.g ≫ g₀) ≫ sX) (M' := E₂) (hRPbr.trans hE'')
    e₂ e₃ _ _ he₂ he₃
    (baseChangeMapOfComp_heq f _ _ hm.symm _ (RT.g ≫ g₀) hm rfl) hv2 hbase₃
    (@properPushforwardDescends C _ _ _ _ _ hlft _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _)) ?_
  -- the restricted condition (3) at `D''`
  refine (heq_of_eq h3).trans ?_
  -- condition (2) along `ρ`, and the two presentations of the Gysin map of `E''`
  refine gysinChowOfInvertible_heq_of_eq C hsN.symm (by omega) _ _
    (Scheme.Modules.pullbackUnitIso (pullback.snd f (RT.g ≫ g₀))) (hE''.symm.trans hRPbr.symm) ?_
    (hq'i := (inferInstance : LocallyOfFiniteType (RP.g ≫ pullback.fst f g₀ ≫ sX)))
    (hqi := inferInstanceAs (LocallyOfFiniteType (pullback.fst f (RT.g ≫ g₀) ≫ sX)))
    (hMi := Stacks.Divisors.pullback_isInvertible (pullback.snd f (RT.g ≫ g₀))
      (Scheme.unitModule RT.X'))
    (hNi := AlgebraicGeometry.Scheme.Modules.isInvertible_unitModule (pullback f (RT.g ≫ g₀)))
  refine (cast_heq _ _).trans (h2ρ.trans ?_)
  exact flatPullbackChowOfRelativeDimension_heq_of_eq C hsN.symm rfl rfl _ _ rfl _ _ (by omega)
    (cast_heq _ _).symm
    (hsA'i := inferInstanceAs (LocallyOfFiniteType (RP.g ≫ pullback.fst f g₀ ≫ sX)))
    (hsAi := inferInstanceAs (LocallyOfFiniteType (pullback.fst f (RT.g ≫ g₀) ≫ sX)))
    (hxl := MorphismProperty.of_isPullback hsq inferInstance)
    (hxf := MorphismProperty.of_isPullback hsq inferInstance)
    (hx'l := RP.g_locallyOfFiniteType) (hx'f := RP.g_flat)

/-- **[Stacks, Tag 0F9A], a weak form of Fulton's Theorem 17.1.** Let `(S, δ)` be as in Situation
02QL, let `f : X ⟶ Y` be a morphism of schemes locally of finite type over `S` and let `p ∈ ℤ`.
A rule assigning to every morphism `Y' ⟶ Y` locally of finite type and every `k` a map
`c ∩ - : A_k(Y') ⟶ A_{k-p}(Y' ×_Y X)`, satisfying conditions (1) and (2) of Stacks 0B76 and
condition (3) whenever `ℒ'|_{D'} ≅ 𝒪_{D'}` — a `Stacks.Chow.WeakCapRule` read against the
canonical Gysin system — is a bivariant class: an element of `A^p(X ⟶ Y)` with the same cap
operation (`Stacks.Chow.WeakCapRule.toBivariantClass_cap`). -/
@[stacks 0F9A]
def WeakCapRule.toBivariantClass (w : WeakCapRule C (canonicalGysinSystem C) sX sY f hf p) :
    CanonicalBivariantClass C sX sY f hf p where
  cap g _ k := AddMonoidHom.mk' (w.cap g k) (w.cap_add g k)
  cap_properPushforward := by
    intro T T' g _ h _ h' sq hfst k α
    have : IsProper h' := MorphismProperty.of_isPullback sq (P := @IsProper) inferInstance
    exact w.proper_naturality g h h' sq hfst k _ _ α
  cap_flatPullbackChow := by
    intro T T' g _ h _ _ r hr h' sq hfst k α
    have : LocallyOfFiniteType h' :=
      MorphismProperty.of_isPullback sq (P := @LocallyOfFiniteType) inferInstance
    have : Flat h' := MorphismProperty.of_isPullback sq (P := @Flat) inferInstance
    exact w.flat_naturality g h r hr h' sq hfst k _ _ _ α
  cap_gysin := by
    intro T g _ L _ s k _ _ _ _ e he hbase α
    have := Stacks.Divisors.pullback_isInvertible (pullback.snd f g) L
    exact w.gysin_naturality g L s k e he hbase _ α

/-- The bivariant class of a weak cap rule caps as the rule does. -/
@[simp]
theorem WeakCapRule.toBivariantClass_cap
    (w : WeakCapRule C (canonicalGysinSystem C) sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) :
    ⇑(w.toBivariantClass.cap g k) = w.cap g k :=
  rfl

end Main

end Stacks.Chow

end
