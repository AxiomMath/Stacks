module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernClassBivariant
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.GysinFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.AssociativityOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.SubbundleCompleted

/-!
# The first Chern class of an invertible module commutes with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℒ` be an invertible `𝒪_X`-module. **Stacks 0B7B** says that
`c₁(ℒ) ∈ A^1(X)` is in the center of `A^*(X)` and, more generally, that

  `c ∘ c₁(ℒ) = c₁(g^*ℒ) ∘ c`   in   `A^*(X' ⟶ X)`

for every `g : X' ⟶ X` locally of finite type and every `c ∈ A^*(X' ⟶ X)`.

Both composites are bivariant classes for `g`, and by the composition formula of Stacks 0FE0
their cap operations on a test scheme `t : T ⟶ X` are `c ∩ (c₁(t^*ℒ) ∩ -)` and
`c₁(t'^*g^*ℒ) ∩ (c ∩ -)`, where `t' : T ×_X X' ⟶ X'`. So the tag is the identity

  `c ∩ (c₁(ℒ_T) ∩ α) = c₁(ℒ_{T'}) ∩ (c ∩ α)`   for   `α ∈ A_{k+1}(T)`,

for an arbitrary invertible module `ℒ_T` on the test scheme and its pullback `ℒ_{T'}` to
`T' = T ×_X X'`. This is proved from the Gysin axiom of `c` at the *zero section* of `ℒ_T`. For
any global section `s` of `ℒ_T`, with zero scheme `i : D ⟶ T`, the composite `i_* ∘ i^*` is
`c₁(ℒ_T) ∩ -` by Stacks 02T9 on Chow groups
(`Stacks.Chow.GenuineChern.properChowPushforward_gysinChowOfInvertible`); capping with `c`
commutes with `i_*` (axiom (1) of Stacks 0B76) and with `i^*` (axiom (3)), and Stacks 02T9 on
`T'` turns the result into `c₁(ℒ_{T'}) ∩ (c ∩ α)`. The section `s = 0` is always available.

## Main results

* `Stacks.Chow.BivariantClass.bivariantCompositeOfInvertible_id_cap_heq`,
  `Stacks.Chow.BivariantClass.id_bivariantCompositeOfInvertible_cap_heq` — the cap operations of
  `c ∘ x` and of `x' ∘ c`, for `x ∈ A^p(X)` and `x' ∈ A^p(X')`, read on the test schemes.
* `Stacks.Chow.BivariantClass.heq_bivariantCompositeOfInvertible_iff` — `c ∘ x = x' ∘ c` exactly
  when `c` intertwines the operations of `x` and of `x'` on every test scheme.
* `Stacks.Chow.BivariantClass.heq_mulId_iff` — the same criterion for the product of `A^*(X)`.
* `Stacks.Chow.BivariantClass.cap_firstChernClassCapChow` — the identity above, on a test scheme.
* `Stacks.Chow.BivariantClass.heq_bivariantCompositeOfInvertible_firstChernClass` —
  **Stacks 0B7B (2)**.
* `Stacks.Chow.BivariantClass.heq_mulId_firstChernClass` — **Stacks 0B7B (1)**.

## Implementation notes

The two composites are classes for the morphisms `g ≫ 𝟙 X` and `𝟙 X' ≫ g`, of the degrees
`q + 1` and `1 + q`: equal, but not the same terms. The identity of the tag is therefore a
heterogeneous equality of bivariant classes.

The source's `c ∈ A^*(X' ⟶ X)` is an element of the direct sum `⨁_q A^q(X' ⟶ X)`; the statements
below are for a homogeneous `c ∈ A^q(X' ⟶ X)`, from which the general case follows by additivity
of the composition in `c`.

The source proves the tag with the line bundle `L ⟶ X` of `ℒ` and its zero section, through
Stacks 0B74 and 0F96. The proof here uses the zero scheme of a section of `ℒ` instead: it needs
only the three axioms of a bivariant class and Stacks 02T9.

## References

* [Stacks Project, Tag 0B7B](https://stacks.math.columbia.edu/tag/0B7B)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B77](https://stacks.math.columbia.edu/tag/0B77)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport across equal morphisms -/

section Transport

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- Heterogeneously equal bivariant classes, for equal morphisms and equal degrees, cap
heterogeneously equally on every test scheme. -/
theorem BivariantClass.cap_heq_of_heq {f₁ f₂ : X ⟶ Y} [LocallyOfFiniteType f₁]
    [LocallyOfFiniteType f₂] {hf₁ : f₁ ≫ sY = sX} {hf₂ : f₂ ≫ sY = sX} {p₁ p₂ : ℤ}
    (hf : f₁ = f₂) (hp : p₁ = p₂) {c₁ : BivariantClass C G sX sY f₁ hf₁ p₁}
    {c₂ : BivariantClass C G sX sY f₂ hf₂ p₂} (h : c₁ ≍ c₂) {T : Scheme.{u}} (t : T ⟶ Y)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sY) k) :
    c₁.cap t k α ≍ c₂.cap t k α := by
  subst hf hp
  obtain rfl := eq_of_heq h
  rfl

/-- Pushing forward along the comparison of the base changes of two equal morphisms is, up to
heterogeneous equality, the identity. -/
theorem chowPushforwardOfIso_congrHom_heq {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t]
    (h : (pullback.congrHom hff (rfl : t = t)).hom ≫ (pullback.fst f' t ≫ sX) =
      pullback.fst f t ≫ sX) (k : ℤ) (y : chowGroup C (pullback.fst f t ≫ sX) k) :
    chowPushforwardOfIso C (pullback.fst f t ≫ sX) (pullback.fst f' t ≫ sX)
        (pullback.congrHom hff rfl).hom h k y ≍ y := by
  subst hff
  rw [chowPushforwardOfIso_congr_apply C _ _ (pullback.congrHom rfl rfl).hom (𝟙 _) (by simp) _
    (Category.id_comp _), chowPushforwardOfIso_id]

/-- Proper pushforward into the base changes of two equal morphisms, along morphisms with the same
two projections, is the same up to heterogeneous equality. -/
theorem properChowPushforward_heq_of_pullback_eq {X' A T : Scheme.{u}} {sX' : X' ⟶ C.S}
    [LocallyOfFiniteType sX'] {sA : A ⟶ C.S} [LocallyOfFiniteType sA] {t : T ⟶ X}
    [LocallyOfFiniteType t] {f₁ f₂ : X' ⟶ X} [LocallyOfFiniteType f₁] [LocallyOfFiniteType f₂]
    (e : f₁ = f₂) (u₁ : A ⟶ pullback f₁ t) (u₂ : A ⟶ pullback f₂ t) [IsProper u₁] [IsProper u₂]
    (h₁ : u₁ ≫ pullback.fst f₁ t = u₂ ≫ pullback.fst f₂ t)
    (h₂ : u₁ ≫ pullback.snd f₁ t = u₂ ≫ pullback.snd f₂ t) {k : ℤ}
    (hu₁ : u₁ ≫ (pullback.fst f₁ t ≫ sX') = sA) (hu₂ : u₂ ≫ (pullback.fst f₂ t ≫ sX') = sA)
    (hfac₁ : ProperPushforwardFactorsThroughRationalEquivalence C sA (pullback.fst f₁ t ≫ sX') u₁
      hu₁ k)
    (hfac₂ : ProperPushforwardFactorsThroughRationalEquivalence C sA (pullback.fst f₂ t ≫ sX') u₂
      hu₂ k)
    (y : chowGroup C sA k) :
    properChowPushforward C sA (pullback.fst f₁ t ≫ sX') u₁ hu₁ k hfac₁ y ≍
      properChowPushforward C sA (pullback.fst f₂ t ≫ sX') u₂ hu₂ k hfac₂ y := by
  subst e
  obtain rfl : u₁ = u₂ := pullback.hom_ext h₁ h₂
  rfl

end Transport

/-! ### Composites with a Chow cohomology class, read on the test schemes -/

section Composite

variable {C : ChowSituation.{u}} {X X' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] {g : X' ⟶ X} [LocallyOfFiniteType g]
  {hg : g ≫ sX = sX'} {q p : ℤ}

/-- **The cap operation of `c ∘ x`** for `c ∈ A^q(X' ⟶ X)` and `x ∈ A^p(X)`: on a test scheme
`t : T ⟶ X` it is `c ∩ (x ∩ -)`, the operation of `x` on `T` followed by the cap product of `c`.
The two sides lie on the base changes of the equal morphisms `g ≫ 𝟙 X` and `g`. -/
theorem BivariantClass.bivariantCompositeOfInvertible_id_cap_heq
    (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q)
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) p)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    (bivariantCompositeOfInvertible C sX' sX sX g (𝟙 X) hg (Category.id_comp sX) q p c x).cap t
        k α ≍
      c.cap t (k - p) (x.idRule C sX (gysinSystemOfInvertible C) t k α) := by
  refine (isBivariantClassComposition_bivariantCompositeOfInvertible C sX' sX sX g (𝟙 X) hg
    (Category.id_comp sX) q p c x t k α).trans ?_
  rw [bivariantCompositeCap_apply]
  have hm : pullback.snd (𝟙 X) t ≫ t = pullback.fst (𝟙 X) t := by
    simpa using (pullback.condition (f := 𝟙 X) (g := t)).symm
  have hmb : pullback.snd (𝟙 X) t ≫ (t ≫ sX) = pullback.fst (𝟙 X) t ≫ sX := by
    rw [← Category.assoc, hm]
  have := isProper_of_isPullback _ _ _ _ (isPullback_baseChangeMapOfEq g t _ _ hm)
  have key : c.cap t (k - p) (x.idRule C sX (gysinSystemOfInvertible C) t k α) =
      properChowPushforward C (pullback.fst g (pullback.fst (𝟙 X) t) ≫ sX')
        (pullback.fst g t ≫ sX') (baseChangeMapOfEq g t _ _ hm)
        (baseChangeMapOfEq_comp_structure sX' g t _ _ hm) (k - p - q)
        (properPushforwardDescends C _ _ _ _ _)
        (c.cap (pullback.fst (𝟙 X) t) (k - p) (x.cap t k α)) :=
    c.proper_naturality_of_test_eq t (pullback.snd (𝟙 X) t) (pullback.fst (𝟙 X) t) hm
      (baseChangeMapOfEq g t _ _ hm) (isPullback_baseChangeMapOfEq g t _ _ hm)
      (baseChangeMapOfEq_fst g t _ _ hm) (k - p) hmb
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) (x.cap t k α)
  rw [key]
  exact properChowPushforward_heq_of_pullback_eq (Category.comp_id g) _ _ (by simp) (by simp) _ _
    _ _ _

/-- **The cap operation of `x' ∘ c`** for `x' ∈ A^p(X')` and `c ∈ A^q(X' ⟶ X)`: on a test scheme
`t : T ⟶ X` it is `x' ∩ (c ∩ -)`, the cap product of `c` followed by the operation of `x'` on the
test scheme `T ×_X X' ⟶ X'`. The two sides lie on the base changes of the equal morphisms
`𝟙 X' ≫ g` and `g`. -/
theorem BivariantClass.id_bivariantCompositeOfInvertible_cap_heq
    (x' : BivariantClass C (gysinSystemOfInvertible C) sX' sX' (𝟙 X') (Category.id_comp sX') p)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    (bivariantCompositeOfInvertible C sX' sX' sX (𝟙 X') g (Category.id_comp sX') hg p q x' c).cap
        t k α ≍
      x'.idRule C sX' (gysinSystemOfInvertible C) (pullback.fst g t) (k - q) (c.cap t k α) := by
  refine (isBivariantClassComposition_bivariantCompositeOfInvertible C sX' sX' sX (𝟙 X') g
    (Category.id_comp sX') hg p q x' c t k α).trans ?_
  rw [bivariantCompositeCap_apply, BivariantClass.idRule_apply, pullbackSndPush,
    chowPushforwardOfIso]
  have hc : pullback.fst (𝟙 X') (pullback.fst g t) =
      pullback.snd (𝟙 X') (pullback.fst g t) ≫ pullback.fst g t := by
    simpa using (pullback.condition (f := 𝟙 X') (g := pullback.fst g t))
  exact properChowPushforward_heq_of_pullback_eq (Category.id_comp g) _ _ (by simpa using hc)
    (by simp) _ _ _ (properPushforwardFactorsThroughRationalEquivalence_of_isIso C _ _ _ _ _) _

/-- **`c ∘ x = x' ∘ c`, read on the test schemes.** For `c ∈ A^q(X' ⟶ X)`, `x ∈ A^p(X)` and
`x' ∈ A^p(X')`, the two composites agree exactly when, on every test scheme `t : T ⟶ X`,

  `c ∩ (x ∩ α) = x' ∩ (c ∩ α)`   for   `α ∈ A_k(T)`,

the operation of `x'` being taken on the test scheme `T ×_X X' ⟶ X'`. -/
theorem BivariantClass.heq_bivariantCompositeOfInvertible_iff
    (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q)
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) p)
    (x' : BivariantClass C (gysinSystemOfInvertible C) sX' sX' (𝟙 X') (Category.id_comp sX') p) :
    bivariantCompositeOfInvertible C sX' sX sX g (𝟙 X) hg (Category.id_comp sX) q p c x ≍
        bivariantCompositeOfInvertible C sX' sX' sX (𝟙 X') g (Category.id_comp sX') hg p q x' c ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
        (α : chowGroup C (t ≫ sX) k),
        c.cap t (k - p) (x.idRule C sX (gysinSystemOfInvertible C) t k α) ≍
          x'.idRule C sX' (gysinSystemOfInvertible C) (pullback.fst g t) (k - q)
            (c.cap t k α) := by
  have hff : g ≫ 𝟙 X = 𝟙 X' ≫ g := by simp
  constructor
  · intro h T t _ k α
    refine (c.bivariantCompositeOfInvertible_id_cap_heq x t k α).symm.trans ?_
    refine HEq.trans ?_ (x'.id_bivariantCompositeOfInvertible_cap_heq c t k α)
    exact BivariantClass.cap_heq_of_heq hff (add_comm q p) h t k α
  · intro h
    refine BivariantClass.heq_of_congrHom_cap_heq hff (add_comm q p) _ _ fun t _ k α ↦ ?_
    refine (chowPushforwardOfIso_congrHom_heq hff t _ _ _).trans ?_
    refine (c.bivariantCompositeOfInvertible_id_cap_heq x t k α).trans ((h t k α).trans ?_)
    exact (x'.id_bivariantCompositeOfInvertible_cap_heq c t k α).symm

end Composite

/-! ### The product of `A^*(X)`, read on the test schemes -/

section Product

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {q p : ℤ}

/-- **`c · x = x · c` in `A^*(X)`, read on the test schemes.** For `c ∈ A^q(X)` and `x ∈ A^p(X)`
the products `c · x ∈ A^{q+p}(X)` and `x · c ∈ A^{p+q}(X)` agree exactly when, on every test
scheme `t : T ⟶ X`, `c ∩ (x ∩ α) = x ∩ (c ∩ α)`, the operation of `x` on the right being taken
on the test scheme `T ×_X X ⟶ X`. -/
theorem BivariantClass.heq_mulId_iff
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) q)
    (x : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) p) :
    c.mulId C sX x ≍ x.mulId C sX c ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
        (α : chowGroup C (t ≫ sX) k),
        c.cap t (k - p) (x.idRule C sX (gysinSystemOfInvertible C) t k α) ≍
          x.idRule C sX (gysinSystemOfInvertible C) (pullback.fst (𝟙 X) t) (k - q)
            (c.cap t k α) := by
  rw [← BivariantClass.heq_bivariantCompositeOfInvertible_iff c x x]
  constructor
  · intro h
    exact (bivariantClassCongr_heq_self _ _ _ _ _).symm.trans
      (h.trans (bivariantClassCongr_heq_self _ _ _ _ _))
  · intro h
    exact (bivariantClassCongr_heq_self _ _ _ _ _).trans
      (h.trans (bivariantClassCongr_heq_self _ _ _ _ _).symm)

end Product

/-! ### Stacks 0B7B -/

section FirstChern

variable {C : ChowSituation.{u}} {X X' : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {sX' : X' ⟶ C.S} [LocallyOfFiniteType sX'] {g : X' ⟶ X} [LocallyOfFiniteType g]
  {hg : g ≫ sX = sX'} {q : ℤ}

/-- **Stacks 0B7B, on a test scheme.** Let `c ∈ A^q(X' ⟶ X)`, let `t : T ⟶ X` be a test scheme,
let `ℒ` be an invertible module on `T` and `ℒ'` one on `T' = T ×_X X'` isomorphic to the pullback
of `ℒ`. Then capping with `c` commutes with the first Chern classes:

  `c ∩ (c₁(ℒ) ∩ α) = c₁(ℒ') ∩ (c ∩ α)`   in   `A_{k-q}(T')`   for   `α ∈ A_{k+1}(T)`,

where `c ∩ α ∈ A_{k+1-q}(T')` is read in the degree `k - q + 1` as any heterogeneously equal `β`.

The proof uses the zero scheme `i : D ⟶ T` of the zero section of `ℒ`: by Stacks 02T9 the
composite `i_* ∘ i^*` is `c₁(ℒ) ∩ -`, capping with `c` commutes with `i_*` and with the Gysin map
`i^*` by the axioms of a bivariant class, and Stacks 02T9 on `T'` concludes. -/
theorem BivariantClass.cap_firstChernClassCapChow
    (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q)
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (L : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property L]
    (L' : (pullback g t).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible (pullback g t).sheaf.obj
      (pullback g t).ringCatSheaf.property L']
    (eL : L' ≅ (Scheme.Modules.pullback (pullback.snd g t)).obj L) (k : ℤ)
    (α : chowGroup C (t ≫ sX) (k + 1)) (β : chowGroup C (pullback.fst g t ≫ sX') (k - q + 1))
    (hβ : β ≍ c.cap t (k + 1) α) :
    c.cap t k (firstChernClassCapChow C k (t ≫ sX) L α) =
      firstChernClassCapChow C (k - q) (pullback.fst g t ≫ sX') L' β := by
  have := GenuineChern.isInvertible_pullback (pullback.snd g t) L
  rw [firstChernClassCapChow_congr C _ (k - q) eL]
  set D := Stacks.Divisors.zeroScheme T L (0 : Γ(L, ⊤))
  set E := Stacks.Divisors.zeroScheme (pullback g t)
    ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
    (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L 0)
  -- Stacks 02T9 on `T`
  rw [← GenuineChern.properChowPushforward_gysinChowOfInvertible C (t ≫ sX) k L 0
    (properPushforwardDescends C _ _ _ _ _) α]
  -- axiom (1) of Stacks 0B76 along `i : D ⟶ T`
  set h' := bivariantBaseChangeMap g t D.subschemeι
  have := isProper_of_isPullback _ _ _ _ (isPullback_bivariantBaseChangeMap g t D.subschemeι)
  have hnat : c.cap t k (properChowPushforward C (D.subschemeι ≫ (t ≫ sX)) (t ≫ sX)
        D.subschemeι rfl k (properPushforwardDescends C _ _ _ _ _)
        (gysinChowOfInvertible C (t ≫ sX) k L 0 α)) =
      properChowPushforward C (pullback.fst g (D.subschemeι ≫ t) ≫ sX') (pullback.fst g t ≫ sX')
        h' (by rw [← Category.assoc, bivariantBaseChangeMap_fst]) (k - q)
        (properPushforwardDescends C _ _ _ _ _)
        (c.cap (D.subschemeι ≫ t) k (gysinChowOfInvertible C (t ≫ sX) k L 0 α)) :=
    c.proper_naturality t D.subschemeι h' (isPullback_bivariantBaseChangeMap g t D.subschemeι)
      (bivariantBaseChangeMap_fst g t D.subschemeι) k (properPushforwardDescends C _ _ _ _ _)
      (properPushforwardDescends C _ _ _ _ _) _
  rw [hnat]
  -- `h'` is the identification of Stacks 0B6Y followed by the zero scheme of the pulled-back
  -- section
  set e := bivariantDivisorBaseChangeIso g t L 0
  have hee : e.hom ≫ E.subschemeι = h' := bivariantDivisorBaseChangeIso_hom_subschemeι g t L 0
  have hbase : e.hom ≫ (E.subschemeι ≫ pullback.fst g t ≫ sX') =
      pullback.fst g (D.subschemeι ≫ t) ≫ sX' := by
    rw [← Category.assoc, hee, ← Category.assoc, bivariantBaseChangeMap_fst]
  rw [properChowPushforward_comp_apply C _ (E.subschemeι ≫ pullback.fst g t ≫ sX') _ e.hom
    E.subschemeι h' hee hbase rfl _ (k - q) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) (properPushforwardDescends C _ _ _ _ _)]
  -- axiom (3) of Stacks 0B76 for the zero section
  have hgys := c.gysin_naturality t L 0 k e hee hbase (properPushforwardDescends C _ _ _ _ _) α
  have hgys' : properChowPushforward C (pullback.fst g (D.subschemeι ≫ t) ≫ sX')
      (E.subschemeι ≫ pullback.fst g t ≫ sX') e.hom hbase (k - q)
      (properPushforwardDescends C _ _ _ _ _)
      (c.cap (D.subschemeι ≫ t) k (gysinChowOfInvertible C (t ≫ sX) k L 0 α)) =
      gysinChowOfInvertible C (pullback.fst g t ≫ sX') (k - q)
        ((Scheme.Modules.pullback (pullback.snd g t)).obj L)
        (AlgebraicGeometry.pullbackGlobalSections (pullback.snd g t) L 0) β := by
    refine hgys.trans ?_
    congr 1
    exact eq_of_heq ((cast_heq _ _).trans hβ.symm)
  rw [hgys']
  -- Stacks 02T9 on `T'`
  exact GenuineChern.properChowPushforward_gysinChowOfInvertible C (pullback.fst g t ≫ sX')
    (k - q) _ _ _ β

/-- **Stacks 0B7B, on the test schemes.** For `c ∈ A^q(X' ⟶ X)`, an invertible `ℒ` on `X` and an
invertible `ℒ'` on `X'` isomorphic to `g^*ℒ`, capping with `c` intertwines the operations of
`c₁(ℒ) ∈ A^1(X)` and of `c₁(ℒ') ∈ A^1(X')` on every test scheme `t : T ⟶ X`:

  `c ∩ (c₁(t^*ℒ) ∩ α) = c₁(t'^*ℒ') ∩ (c ∩ α)`,   `t' : T ×_X X' ⟶ X'`. -/
theorem BivariantClass.cap_idRule_firstChernClass
    (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (L' : X'.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X'.sheaf.obj X'.ringCatSheaf.property L']
    (eL : L' ≅ (Scheme.Modules.pullback g).obj L) {T : Scheme.{u}} (t : T ⟶ X)
    [LocallyOfFiniteType t] (k : ℤ) (α : chowGroup C (t ≫ sX) k) :
    c.cap t (k - 1)
        ((GenuineChern.firstChernClass C sX L).idRule C sX (gysinSystemOfInvertible C) t k α) ≍
      (GenuineChern.firstChernClass C sX' L').idRule C sX' (gysinSystemOfInvertible C)
        (pullback.fst g t) (k - q) (c.cap t k α) := by
  have := GenuineChern.isInvertible_pullback t L
  have := GenuineChern.isInvertible_pullback (pullback.fst g t) L'
  rw [GenuineChern.idRule_firstChernClass, GenuineChern.idRule_firstChernClass]
  have eL' : (Scheme.Modules.pullback (pullback.fst g t)).obj L' ≅
      (Scheme.Modules.pullback (pullback.snd g t)).obj ((Scheme.Modules.pullback t).obj L) :=
    (Scheme.Modules.pullback (pullback.fst g t)).mapIso eL ≪≫
      (Scheme.Modules.pullbackComp (pullback.fst g t) g).app L ≪≫
      (Scheme.Modules.pullbackCongr pullback.condition).app L ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd g t) t).app L).symm
  have hβ : chowGroupCast C (pullback.fst g t ≫ sX') (show k - q = k - 1 - q + 1 by omega)
      (c.cap t k α) ≍ c.cap t (k - 1 + 1) (chowGroupCast C (t ≫ sX) (by omega) α) :=
    (chowGroupCast_heq C _ _ _).trans (heq_apply_of_degree C (t ≫ sX) (pullback.fst g t ≫ sX')
      (fun d ↦ d) (fun d ↦ d - q) (fun d ↦ c.cap t d) (by omega)
      (chowGroupCast_heq C _ _ _).symm)
  have key := c.cap_firstChernClassCapChow t ((Scheme.Modules.pullback t).obj L)
    ((Scheme.Modules.pullback (pullback.fst g t)).obj L') eL' (k - 1)
    (chowGroupCast C (t ≫ sX) (by omega) α) _ hβ
  refine (heq_of_eq key).trans ?_
  exact heq_apply_of_degree C (pullback.fst g t ≫ sX') (pullback.fst g t ≫ sX') (fun d ↦ d + 1)
    (fun d ↦ d) (fun d ↦ firstChernClassCapChow C d (pullback.fst g t ≫ sX')
      ((Scheme.Modules.pullback (pullback.fst g t)).obj L')) (by omega)
    ((chowGroupCast_heq C _ _ _).trans (chowGroupCast_heq C _ _ _).symm)

/-- **Stacks 0B7B (2).** Let `g : X' ⟶ X` be locally of finite type, let `c ∈ A^q(X' ⟶ X)` and
let `ℒ` be an invertible `𝒪_X`-module. Then

  `c ∘ c₁(ℒ) = c₁(g^*ℒ) ∘ c`   in   `A^{q+1}(X' ⟶ X)`,

the composites being those of Stacks 0B75, classes for the equal morphisms `g ≫ 𝟙 X` and
`𝟙 X' ≫ g` of the equal degrees `q + 1` and `1 + q`. -/
@[stacks 0B7B "(2), for a homogeneous c in A^q(X' -> X) and the composition of Stacks 0B75 at the
Gysin system of the first Chern class of an invertible module; the two composites are classes for
g ≫ 𝟙 X and 𝟙 X' ≫ g of degrees q + 1 and 1 + q, whence the heterogeneous equality"]
theorem BivariantClass.heq_bivariantCompositeOfInvertible_firstChernClass
    (c : BivariantClass C (gysinSystemOfInvertible C) sX' sX g hg q) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    haveI := GenuineChern.isInvertible_pullback g L
    bivariantCompositeOfInvertible C sX' sX sX g (𝟙 X) hg (Category.id_comp sX) q 1 c
        (GenuineChern.firstChernClass C sX L) ≍
      bivariantCompositeOfInvertible C sX' sX' sX (𝟙 X') g (Category.id_comp sX') hg 1 q
        (GenuineChern.firstChernClass C sX' ((Scheme.Modules.pullback g).obj L)) c := by
  have := GenuineChern.isInvertible_pullback g L
  exact (c.heq_bivariantCompositeOfInvertible_iff _ _).2 fun t _ k α ↦
    c.cap_idRule_firstChernClass L _ (Iso.refl _) t k α

end FirstChern

section FirstChernCenter

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {q : ℤ}

/-- **Stacks 0B7B (1).** The first Chern class `c₁(ℒ) ∈ A^1(X)` of an invertible module is in the
center of `A^*(X)`: for every `c ∈ A^q(X)`,

  `c · c₁(ℒ) = c₁(ℒ) · c`,

the two products lying in `A^{q+1}(X)` and `A^{1+q}(X)`. -/
@[stacks 0B7B "(1), for the product of A^*(X) given by the composition of Stacks 0B75 at the Gysin
system of the first Chern class of an invertible module, against every homogeneous c in A^q(X);
the two products have degrees q + 1 and 1 + q, whence the heterogeneous equality"]
theorem BivariantClass.heq_mulId_firstChernClass
    (c : BivariantClass C (gysinSystemOfInvertible C) sX sX (𝟙 X) (Category.id_comp sX) q)
    (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    c.mulId C sX (GenuineChern.firstChernClass C sX L) ≍
      (GenuineChern.firstChernClass C sX L).mulId C sX c :=
  (c.heq_mulId_iff _).2 fun t _ k α ↦
    c.cap_idRule_firstChernClass L L ((Scheme.Modules.pullbackId X).app L).symm t k α

end FirstChernCenter

end Stacks.Chow

end
