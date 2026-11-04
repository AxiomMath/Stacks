module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Composition of bivariant Chow classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X`, `Y`, `Z` be
schemes locally of finite type over `S` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms over
`S`. The composite of bivariant classes `a ∈ A^p(X ⟶ Y)` and `b ∈ A^q(Y ⟶ Z)` is the class
`a ∘ b ∈ A^{p+q}(X ⟶ Z)` such that, for `t : T ⟶ Z` locally of finite type and `α ∈ A_k(T)`,

  `(a ∘ b) ∩ α = (a ∩ (b ∩ α))`,

where the right-hand side lives on `(T ×_Z Y) ×_Y X` and the left-hand side on `T ×_Z X`, the two
being identified by pushforward along the associativity isomorphism of pullbacks
`CategoryTheory.Limits.pullbackRightPullbackFstIso`.

This file states that formula as a property `Stacks.Chow.IsBivariantClassComposition` of a
bivariant class, proves that it determines the class uniquely, and that it is additive in each of
the two arguments.

## Main definitions

* `Stacks.Chow.chowGroupDegreeEquiv` — transport along an equality of degrees, as an additive
  equivalence of Chow groups.
* `Stacks.Chow.ProperPushforwardDescends` — Stacks 02S2 for every proper morphism over the base,
  as a single proposition.
* `Stacks.Chow.bivariantCompositeCap` — the cap operation `α ↦ a ∩ (b ∩ α)` of the composite,
  pushed forward to `T ×_Z X`.
* `Stacks.Chow.IsBivariantClassComposition` — the assertion that a bivariant class of degree
  `p + q` for `f ≫ g` caps by that formula.

## Main results

* `Stacks.Chow.isBivariantClassComposition_iff` — the characterization, with the heterogeneous
  equality of the degrees replaced by a transport.
* `Stacks.Chow.eq_of_isBivariantClassComposition` — **uniqueness**: two bivariant classes
  satisfying the composition formula for the same pair `a`, `b` are equal.
* `Stacks.Chow.IsBivariantClassComposition.add_left`,
  `Stacks.Chow.IsBivariantClassComposition.add_right`,
  `Stacks.Chow.IsBivariantClassComposition.neg_left`,
  `Stacks.Chow.IsBivariantClassComposition.neg_right`,
  `Stacks.Chow.IsBivariantClassComposition.zero_left`,
  `Stacks.Chow.IsBivariantClassComposition.zero_right` — composition is additive in each
  argument, in the sense that the characterization transports along the group operations.

## References

* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport along an equality of degrees -/

/-- The additive equivalence between the Chow groups of `X` in two equal degrees `k = l`, given by
transport along the equality. -/
def chowGroupDegreeEquiv (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {k l : ℤ} (h : k = l) :
    chowGroup C sX k ≃+ chowGroup C sX l := by
  subst h
  exact AddEquiv.refl _

/-- Transport along an equality of degrees does not change the element. -/
theorem chowGroupDegreeEquiv_heq (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {k l : ℤ} (h : k = l) (α : chowGroup C sX k) :
    chowGroupDegreeEquiv C sX h α ≍ α := by
  subst h
  rfl

/-- An element of a Chow group is heterogeneously equal to one of another degree exactly when its
transport is equal to it. -/
theorem chowGroupDegreeEquiv_eq_iff_heq (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] {k l : ℤ} (h : k = l) (α : chowGroup C sX k)
    (β : chowGroup C sX l) :
    chowGroupDegreeEquiv C sX h α = β ↔ α ≍ β := by
  subst h
  exact ⟨fun hβ ↦ heq_of_eq hβ, fun hβ ↦ eq_of_heq hβ⟩

/-! ### Stacks 02S2 as a single hypothesis -/

/-- **Stacks 02S2**, bundled: proper pushforward of cycles along every proper morphism over the
base, in every degree, carries cycles rationally equivalent to zero to cycles rationally
equivalent to zero. -/
def ProperPushforwardDescends (C : ChowSituation.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ),
    ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k

/-! ### The cap operation of a composite -/

/-- The associativity isomorphism `(T ×_Z Y) ×_Y X ≅ T ×_Z X` of
`CategoryTheory.Limits.pullbackRightPullbackFstIso` is compatible with the structure morphisms of
`X` over the base. -/
theorem pullbackRightPullbackFstIso_hom_comp_fst_comp {S X Y Z T : Scheme.{u}} (sX : X ⟶ S)
    (f : X ⟶ Y) (g : Y ⟶ Z) (t : T ⟶ Z) :
    (pullbackRightPullbackFstIso g t f).hom ≫ (pullback.fst (f ≫ g) t ≫ sX) =
      pullback.fst f (pullback.fst g t) ≫ sX := by
  rw [← Category.assoc, pullbackRightPullbackFstIso_hom_fst]

/-- The structure morphism of `X` over the base factors the one of `Z` through the composite. -/
theorem comp_comp_structureMorphism_eq {C : ChowSituation.{u}} {X Y Z : Scheme.{u}}
    {sX : X ⟶ C.S} {sY : Y ⟶ C.S} {sZ : Z ⟶ C.S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) :
    (f ≫ g) ≫ sZ = sX := by
  rw [Category.assoc, hg, hf]

section Composite

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY)
  (hpp : ProperPushforwardDescends C) (p q : ℤ)
  (a : BivariantClass C G sX sY f hf p) (b : BivariantClass C G sY sZ g hg q)

/-- The cap operation of the composite of two bivariant classes: cap with `b`, cap with `a`, then
push forward along the associativity isomorphism of pullbacks. -/
def bivariantCompositeCap {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ) :
    chowGroup C (t ≫ sZ) k →+
      chowGroup C (pullback.fst (f ≫ g) t ≫ sX) ((k - q) - p) :=
  (properChowPushforward C (pullback.fst f (pullback.fst g t) ≫ sX)
      (pullback.fst (f ≫ g) t ≫ sX) (pullbackRightPullbackFstIso g t f).hom
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t) ((k - q) - p)
      (hpp _ _ _ _ _)).comp
    ((a.cap (pullback.fst g t) (k - q)).comp (b.cap t k))

/-- The cap operation of a composite, read on an element. -/
theorem bivariantCompositeCap_apply {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sZ) k) :
    bivariantCompositeCap C G sX sY sZ f g hf hg hpp p q a b t k α =
      properChowPushforward C (pullback.fst f (pullback.fst g t) ≫ sX)
        (pullback.fst (f ≫ g) t ≫ sX) (pullbackRightPullbackFstIso g t f).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g t) ((k - q) - p)
        (hpp _ _ _ _ _) (a.cap (pullback.fst g t) (k - q) (b.cap t k α)) :=
  rfl

/-- **Stacks 0FE0.** The assertion that a bivariant class of degree `p + q` for `f ≫ g` is *the*
composite of `a` and `b`: on every test scheme its cap operation is cap with `b` followed by cap
with `a`, pushed forward along the associativity isomorphism of pullbacks. The two sides have the
same degree written two ways, whence the heterogeneous equality. -/
def IsBivariantClassComposition
    (c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q)) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sZ) k),
    c.cap t k α ≍ bivariantCompositeCap C G sX sY sZ f g hf hg hpp p q a b t k α

variable (c : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q))

/-- The composition formula, with the heterogeneous equality of degrees replaced by a transport. -/
theorem isBivariantClassComposition_iff :
    IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a b c ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (k : ℤ)
        (α : chowGroup C (t ≫ sZ) k),
        chowGroupDegreeEquiv C (pullback.fst (f ≫ g) t ≫ sX) (by ring : k - (p + q) = (k - q) - p)
            (c.cap t k α) =
          bivariantCompositeCap C G sX sY sZ f g hf hg hpp p q a b t k α := by
  exact ⟨fun h _ t _ k α ↦ (chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).2 (h t k α),
    fun h _ t _ k α ↦ (chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).1 (h t k α)⟩

end Composite

/-! ### Uniqueness and bilinearity of the composite -/

section Properties

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y Z : Scheme.{u}}
  {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]
  {sZ : Z ⟶ C.S} [LocallyOfFiniteType sZ] {f : X ⟶ Y} [LocallyOfFiniteType f]
  {g : Y ⟶ Z} [LocallyOfFiniteType g] {hf : f ≫ sY = sX} {hg : g ≫ sZ = sY}
  {hpp : ProperPushforwardDescends C} {p q : ℤ}
  {a a' : BivariantClass C G sX sY f hf p} {b b' : BivariantClass C G sY sZ g hg q}
  {c c' : BivariantClass C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q)}

/-- **Stacks 0FE0.** The composition formula determines the composite: two bivariant classes that
both compose `a` with `b` are equal. -/
theorem eq_of_isBivariantClassComposition
    (h : IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a b c)
    (h' : IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a b c') : c = c' := by
  exact BivariantClass.ext C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q)
    fun t _ k α ↦ eq_of_heq ((h t k α).trans (h' t k α).symm)

namespace IsBivariantClassComposition

/-- Composition is additive in its first argument. -/
theorem add_left (h : IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a b c)
    (h' : IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a' b c') :
    IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q (a + a') b (c + c') := by
  rw [isBivariantClassComposition_iff] at h h' ⊢
  intro T t _ k α
  simp only [BivariantClass.add_cap, map_add, h t k α, h' t k α, bivariantCompositeCap_apply]

/-- Composition is additive in its second argument. -/
theorem add_right (h : IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a b c)
    (h' : IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a b' c') :
    IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a (b + b') (c + c') := by
  rw [isBivariantClassComposition_iff] at h h' ⊢
  intro T t _ k α
  simp only [BivariantClass.add_cap, map_add, h t k α, h' t k α, bivariantCompositeCap_apply]

/-- Composition negates in its first argument. -/
theorem neg_left (h : IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a b c) :
    IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q (-a) b (-c) := by
  rw [isBivariantClassComposition_iff] at h ⊢
  intro T t _ k α
  simp only [BivariantClass.neg_cap, map_neg, h t k α, bivariantCompositeCap_apply]

/-- Composition negates in its second argument. -/
theorem neg_right (h : IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a b c) :
    IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a (-b) (-c) := by
  rw [isBivariantClassComposition_iff] at h ⊢
  intro T t _ k α
  simp only [BivariantClass.neg_cap, map_neg, h t k α, bivariantCompositeCap_apply]

/-- The composite of the zero class with any class is zero. -/
theorem zero_left :
    IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q 0 b 0 := by
  rw [isBivariantClassComposition_iff]
  intro T t _ k α
  simp only [BivariantClass.zero_cap, map_zero, bivariantCompositeCap_apply]

/-- The composite of any class with the zero class is zero. -/
theorem zero_right :
    IsBivariantClassComposition C G sX sY sZ f g hf hg hpp p q a 0 0 := by
  rw [isBivariantClassComposition_iff]
  intro T t _ k α
  simp only [BivariantClass.zero_cap, map_zero, bivariantCompositeCap_apply]

end IsBivariantClassComposition

end Properties

/-- Transport along an equality of degrees, on the class of a cycle: two cycles with the same
coefficient function have the same class in either of two equal degrees. -/
public theorem chowGroupDegreeEquiv_mk_eq_mk_of_val (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {d e : ℤ} (hde : d = e) (a : CycleGroup C sX d)
    (b : CycleGroup C sX e) (hab : a.1 = b.1) :
    chowGroupDegreeEquiv C sX hde (QuotientAddGroup.mk a) = QuotientAddGroup.mk b := by
  subst hde
  obtain rfl : a = b := Subtype.ext hab
  rfl

end Stacks.Chow

end
