module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Associativity
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.OpenImmersionComposite

/-!
# Associativity of the composition of bivariant classes at the first Chern class rule

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let
`f : X ⟶ Y`, `g : Y ⟶ Z` and `h : Z ⟶ W` be morphisms of schemes locally of finite type over `S`.
The paragraph of the Stacks Project following Definition 0B76 asserts that the bilinear composition

  `A^p(X ⟶ Y) × A^q(Y ⟶ Z) ⟶ A^{p+q}(X ⟶ Z)`

is associative: for `a ∈ A^p(X ⟶ Y)`, `b ∈ A^q(Y ⟶ Z)` and `c ∈ A^r(Z ⟶ W)`,

  `(a ∘ b) ∘ c = a ∘ (b ∘ c)` in `A^{p+q+r}(X ⟶ W)`.

This file proves it for the composition `Stacks.Chow.bivariantCompositeOfInvertible` of
Stacks 0B75 at the Gysin system of the first Chern class rule, where the composition carries no
hypothesis. `StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Associativity` proves it for
`Stacks.Chow.bivariantComposite` at a Gysin system natural under isomorphisms of base changes.

## Main results

* `Stacks.Chow.BivariantClass.heq_of_congrHom_cap_heq` — two bivariant classes for equal
  morphisms and of equal degrees are the same class as soon as their cap operations agree, read
  through the identification of the two base changes.
* `Stacks.Chow.bivariantCompositeOfInvertible_assoc` — associativity of the composition.

## Implementation notes

The two sides are bivariant classes for `(f ≫ g) ≫ h` and `f ≫ (g ≫ h)` of degrees
`(p + q) + r` and `p + (q + r)`; these morphisms and integers are equal but not definitionally,
so the equality is heterogeneous. On a test scheme `t : T ⟶ W` both cap operations are
cap with `c`, then with `b`, then with `a`, followed by a pushforward along an isomorphism of
iterated pullbacks onto `X ×_W T`. On the right the middle step is a pushforward along an
isomorphism of test schemes, which cap with `a` commutes with by the proper-pushforward law of
Stacks 0B76 (`Stacks.Chow.BivariantClass.cap_chowPushforwardOfIso`). The two resulting
isomorphisms of pullbacks agree, both being morphisms into `X ×_W T` with the same two
projections.

## References

* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Bivariant classes for equal morphisms and equal degrees -/

section HEq

variable {C : ChowSituation.{u}} {G : GysinSystem C} {X Y : Scheme.{u}} {sX : X ⟶ C.S}
  [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY]

/-- Two bivariant classes for equal morphisms `f = f'` and of equal degrees `p = p'` are the same
class as soon as their cap operations agree, read through the identification
`X ×_{f,Y} T ≅ X ×_{f',Y} T`. -/
theorem BivariantClass.heq_of_congrHom_cap_heq {f f' : X ⟶ Y} [LocallyOfFiniteType f]
    [LocallyOfFiniteType f'] (hff : f = f') {hf : f ≫ sY = sX} {hf' : f' ≫ sY = sX} {p p' : ℤ}
    (hpp' : p = p') (c : BivariantClass C G sX sY f hf p) (c' : BivariantClass C G sX sY f' hf' p')
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ Y) [LocallyOfFiniteType t] (k : ℤ)
      (α : chowGroup C (t ≫ sY) k),
      chowPushforwardOfIso C (pullback.fst f t ≫ sX) (pullback.fst f' t ≫ sX)
          (pullback.congrHom hff rfl).hom (by simp) (k - p) (c.cap t k α) ≍
        c'.cap t k α) :
    c ≍ c' := by
  subst hpp'
  exact BivariantClass.heq_of_cap_eq hff c c' fun t _ k α ↦ eq_of_heq (h t k α)

end HEq

section HEqCongr

variable {C : ChowSituation.{u}}

/-- The composite of Stacks 0B75 is compatible with heterogeneous equality of its factors, over
equal morphisms and degrees. -/
theorem bivariantCompositeOfInvertible_heq_congr {X Y Z : Scheme.{u}} {sX : X ⟶ C.S}
    [LocallyOfFiniteType sX] {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {sZ : Z ⟶ C.S}
    [LocallyOfFiniteType sZ] {f f' : X ⟶ Y} [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    {g g' : Y ⟶ Z} [LocallyOfFiniteType g] [LocallyOfFiniteType g'] (hff' : f = f')
    (hgg' : g = g') {hf : f ≫ sY = sX} {hf' : f' ≫ sY = sX} {hg : g ≫ sZ = sY}
    {hg' : g' ≫ sZ = sY} {p p' q q' : ℤ} (hp : p = p') (hq : q = q')
    {a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p}
    {a' : BivariantClass C (gysinSystemOfInvertible C) sX sY f' hf' p'}
    {b : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q}
    {b' : BivariantClass C (gysinSystemOfInvertible C) sY sZ g' hg' q'} (ha : a ≍ a')
    (hb : b ≍ b') :
    bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a b ≍
      bivariantCompositeOfInvertible C sX sY sZ f' g' hf' hg' p' q' a' b' := by
  subst hff' hgg' hp hq
  cases ha
  cases hb
  rfl

end HEqCongr

/-! ### Associativity -/

section Assoc

variable (C : ChowSituation.{u}) {X Y Z W : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (h : Z ⟶ W) [LocallyOfFiniteType h]
  (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (hh : h ≫ sW = sZ) (p q r : ℤ)

/-- **Associativity of the composition of bivariant classes**, the assertion of the Stacks
Project following Definition 0B76: for `a ∈ A^p(X ⟶ Y)`, `b ∈ A^q(Y ⟶ Z)` and
`c ∈ A^r(Z ⟶ W)`, `(a ∘ b) ∘ c = a ∘ (b ∘ c)`, at the Gysin system of the first Chern class rule.
The two sides are classes for `(f ≫ g) ≫ h` and `f ≫ (g ≫ h)`, of degrees `(p + q) + r` and
`p + (q + r)`, whence the heterogeneous equality. -/
theorem bivariantCompositeOfInvertible_assoc
    (a : BivariantClass C (gysinSystemOfInvertible C) sX sY f hf p)
    (b : BivariantClass C (gysinSystemOfInvertible C) sY sZ g hg q)
    (c : BivariantClass C (gysinSystemOfInvertible C) sZ sW h hh r) :
    bivariantCompositeOfInvertible C sX sZ sW (f ≫ g) h (comp_comp_structureMorphism_eq hf hg) hh
        (p + q) r (bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a b) c ≍
      bivariantCompositeOfInvertible C sX sY sW f (g ≫ h) hf (comp_comp_structureMorphism_eq hg hh)
        p (q + r) a (bivariantCompositeOfInvertible C sY sZ sW g h hg hh q r b c) := by
  refine BivariantClass.heq_of_congrHom_cap_heq (Category.assoc f g h) (add_assoc p q r) _ _ ?_
  intro T t _ k α
  -- the three successive cap operations
  set s := pullback.fst h t
  set γ := c.cap t k α
  set δ := b.cap s (k - r) γ
  set ε := a.cap (pullback.fst g s) (k - r - q) δ
  -- the left side is a double pushforward of `ε`
  have hL : (bivariantCompositeOfInvertible C sX sZ sW (f ≫ g) h
      (comp_comp_structureMorphism_eq hf hg) hh (p + q) r
      (bivariantCompositeOfInvertible C sX sY sZ f g hf hg p q a b) c).cap t k α ≍
      chowPushforwardOfIso C (pullback.fst f (pullback.fst g s) ≫ sX)
        (pullback.fst ((f ≫ g) ≫ h) t ≫ sX)
        ((pullbackRightPullbackFstIso g s f).hom ≫ (pullbackRightPullbackFstIso h t (f ≫ g)).hom)
        (by simp [s]) (k - r - q - p) ε := by
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _
      (chowGroupDegreeEquiv_heq C _ _ _)).trans ?_
    exact heq_of_eq (chowPushforwardOfIso_comp_apply C _ _ _ _ _ _ _ _ ε)
  -- the right side is a pushforward of `ε` too, after moving cap with `a` past the middle one
  have hR : (bivariantCompositeOfInvertible C sX sY sW f (g ≫ h) hf
      (comp_comp_structureMorphism_eq hg hh) p (q + r) a
      (bivariantCompositeOfInvertible C sY sZ sW g h hg hh q r b c)).cap t k α ≍
      chowPushforwardOfIso C (pullback.fst f (pullback.fst g s) ≫ sX)
        (pullback.fst (f ≫ g ≫ h) t ≫ sX)
        ((testBaseChangeIso f (pullback.fst (g ≫ h) t) (pullbackRightPullbackFstIso h t g).hom
            (pullback.fst g s) (pullbackRightPullbackFstIso_hom_fst h t g)).hom ≫
          (pullbackRightPullbackFstIso (g ≫ h) t f).hom)
        (by simp [s]) (k - r - q - p) ε := by
    rw [bivariantCompositeOfInvertible, bivariantComposite_cap, bivariantCompositeCap_apply]
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    have hcap := BivariantClass.cap_chowPushforwardOfIso a (pullback.fst (g ≫ h) t)
      (pullbackRightPullbackFstIso h t g).hom (pullback.fst g s)
      (pullbackRightPullbackFstIso_hom_fst h t g) (pullback.fst g s ≫ sY) rfl (k - r - q)
      (pullbackRightPullbackFstIso_hom_comp_fst_comp sY g h t) δ δ rfl
    refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _
      (chowPushforwardOfIso C _ _ (testBaseChangeIso f (pullback.fst (g ≫ h) t)
        (pullbackRightPullbackFstIso h t g).hom (pullback.fst g s)
        (pullbackRightPullbackFstIso_hom_fst h t g)).hom (by simp) (k - r - q - p) ε) ?_).trans
      (heq_of_eq (chowPushforwardOfIso_comp_apply C _ _ _ _ _ _ _ _ ε))
    refine (BivariantClass.cap_heq_congr a _ (by ring) _ _ ?_).trans (heq_of_eq hcap)
    rw [bivariantCompositeOfInvertible, bivariantComposite_cap]
    refine (chowGroupDegreeEquiv_heq C _ _ _).trans ?_
    rw [bivariantCompositeCap_apply]
    rfl
  refine (chowPushforwardOfIso_heq_congr C _ _ _ _ (by ring) _ _ hL).trans ?_
  refine HEq.trans (heq_of_eq (chowPushforwardOfIso_comp_apply C _ _ _ _ _ _ _ _ ε)) ?_
  refine HEq.trans (heq_of_eq (chowPushforwardOfIso_congr_apply C _ _ _ _ ?_ _ _ _ ε)) hR.symm
  refine pullback.hom_ext ?_ ?_ <;> simp [s]

end Assoc

end Stacks.Chow

end
