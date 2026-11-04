module

public import Mathlib.Algebra.Exact.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineBase
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# The Mayer--Vietoris union step of Tag 0DI7

The reduction of Stacks 0DI7 in
`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentAffineBase.lean` leaves two hypotheses.
This file supplies the second one, the union step: if Tag 0DI7 holds for the restriction of a
relative descent situation to a quasi-compact open `U₀`, to an affine open `V₀` lying over an
affine open of the base, and to `U₀ ∩ V₀`, then it holds for the restriction to `U₀ ∪ V₀`.

The Stacks proof is one sentence: apply Mayer--Vietoris for `Hom` in the derived category,
Stacks 08BW, at the stages and at the limit, and compare the two long exact sequences by the
five lemma. The five lemma in degree `n` consumes degrees `n - 1` and `n + 1`, so the inducted
property is Tag 0DI7 for a whole family `L : ℤ → D(𝒪_{X₀})` of second arguments rather than for
a single one, and the statement keeps that quantifier.

The five lemma is carried out here in the language `AlgebraicGeometry.
RelativeDescentSituation.HomDescent` is stated in — surjectivity of the comparison maps together
with eventual injectivity of the transition maps — so no colimit of abelian groups is formed and
no size hypothesis on the index is needed. What remains is the identification of the four
systems of derived morphism sets with the terms of the Mayer--Vietoris sequence of Stacks 08BW,
which is the content of `AlgebraicGeometry.RelativeDescentSituation.MayerVietorisHomSequence`.

## Main definitions

* `Stacks.MayerVietoris.Descends`: the conclusion of Tag 0DI7 for an abstract system of abelian
  groups over a directed index with a map to a target group — every element of the target comes
  from a stage, and two elements of a stage with the same image agree at a later stage.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomStage` and `restrictHomLimit`: the
  derived morphism sets of the situation restricted to a quasi-compact open, at a stage and at
  the limit, as abelian groups.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomTransition` and
  `restrictHomComparison`: the transition and comparison maps of that system, as group
  homomorphisms.
* `AlgebraicGeometry.RelativeDescentSituation.MayerVietorisHomSequence`: the Mayer--Vietoris
  sequence of Stacks 08BW read on the four systems of derived morphism sets attached to `U₀`,
  `V₀`, `U₀ ∩ V₀` and `U₀ ∪ V₀`, at the stages and at the limit, with its exactness, its
  naturality in the stage and its compatibility with the comparison maps.

## Main results

* `Stacks.MayerVietoris.descends_of_mayerVietoris`: **the five lemma for two Mayer--Vietoris
  sequences in the descent language.** If the product spot and the intersection spot descend in
  every degree, so does the ambient spot.
* `Stacks.MayerVietoris.Descends.prod`: a product of two descending systems descends, which is
  what turns the hypotheses for `U₀` and for `V₀` into the hypothesis at the product spot.
* `Stacks.DerivedPullback.schemeFactorAddHom`: the map on derived morphism sets attached to a
  factorisation of morphisms of schemes is additive, so the transition and comparison maps of
  the system of derived morphism sets are group homomorphisms.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_sup_of_mayerVietorisHomSequence`:
  **the Mayer--Vietoris union step of Tag 0DI7** for one pair of opens.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_sup_of_family`: the same in the
  shape of the hypothesis `hsup` of
  `restrictHomDescent_family_of_isAffineOpen_over_affine_of_sup`.
* `AlgebraicGeometry.RelativeDescentSituation.homDescent_family_of_mayerVietorisHomSequence`:
  Tag 0DI7 from the affine case over an affine open of the base together with the
  Mayer--Vietoris sequences, the two hypotheses of the reduction assembled.

## Implementation notes

The five lemma is a direct chase rather than an application of
`Stacks.MayerVietoris.bijective_of_ladder`. That lemma asks for bijectivity of the vertical maps
of a ladder of long exact sequences, and reaching it from `HomDescent` would mean building the
colimit of the system in `AddCommGrpCat`, together with the preservation and reflection of
filtered colimits by the forgetful functor, only to take it apart again; the chase uses the same
six exactness hypotheses and the same three commuting squares, with no colimit object and no
`UnivLE` hypothesis.

`restrictHomStage` and `restrictHomLimit` are defined through
`AlgebraicGeometry.RelativeDescentSituation.homFunctor` and `homCocone` rather than by writing
out the derived morphism sets, so that the long types are elaborated once, in the two instances
below, instead of once per field of `MayerVietorisHomSequence`. Both are definitionally the
spelled-out morphism sets, which is why the predicate `Stacks.MayerVietoris.Descends` of the
first section is `Iff.rfl`-equal to `RestrictHomDescent`.

The transition and comparison maps are additive because derived pullback is a triangulated
functor, hence additive, and the maps attached to a factorisation are `Iso.homCongr` of its
action on morphisms. This is the only use of
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPullback/Triangulated.lean` here.

`MayerVietorisHomSequence` states the Mayer--Vietoris sequence of Stacks 08BW on the morphism
sets of the restricted situations themselves rather than on the extension-by-zero morphism sets
the triangle of Stacks 08BU produces them in. The translation between the two is the adjunction
of Stacks 08BT, derived base change for extension by zero of a restriction, derived pullback
along an open immersion, and, since the sequence of Stacks 08BW moves a shift while the
predicate moves the family, the comparison of `(L n)|_W` with `(L 0)|_W⟦n⟧`. No affineness or
flatness beyond the data of Stacks 0DI6 enters.

## References

* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 08BW](https://stacks.math.columbia.edu/tag/08BW)
* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe w u

namespace Stacks.MayerVietoris

/-! ### Descent for an abstract filtered system -/

variable {J : Type w} [Preorder J]

/-- The conclusion of Stacks 0DI7 for an abstract system of types over a directed index with
transition maps `t` and comparison maps `c` to a target: every element of the target comes from
some stage, and two elements of one stage with the same image agree at some later stage. -/
def Descends {G : J → Type*} {G' : Type*}
    (t : ∀ i j : J, i ≤ j → G i → G j) (c : ∀ i : J, G i → G') : Prop :=
  (∀ y : G', ∃ (i : J) (x : G i), c i x = y) ∧
    ∀ (i : J) (x x' : G i), c i x = c i x' →
      ∃ (j : J) (h : i ≤ j), t i j h x = t i j h x'

/-- Elements identified by a transition map stay identified after composing with a further one. -/
private theorem transition_eq_of_transition_eq {G : J → Type*} {t : ∀ i j : J, i ≤ j → G i → G j}
    (ht : ∀ (i j k : J) (h : i ≤ j) (h' : j ≤ k) (x : G i),
      t j k h' (t i j h x) = t i k (h.trans h') x)
    {i j m : J} (hij : i ≤ j) (hjm : j ≤ m) {x x' : G i} (hj : t i j hij x = t i j hij x') :
    t i m (hij.trans hjm) x = t i m (hij.trans hjm) x' :=
  ((ht i j m hij hjm x).symm.trans (congrArg (t j m hjm) hj)).trans (ht i j m hij hjm x')

/-- **A product of two descending systems descends.** Directedness merges the two stages a pair
is defined over, and the transition maps of the factors compose. -/
theorem Descends.prod [IsDirected J (· ≤ ·)] {G H : J → Type*} {G' H' : Type*}
    {tG : ∀ i j : J, i ≤ j → G i → G j} {cG : ∀ i : J, G i → G'}
    {tH : ∀ i j : J, i ≤ j → H i → H j} {cH : ∀ i : J, H i → H'}
    (hG : Descends tG cG) (hH : Descends tH cH)
    (hcG : ∀ (i j : J) (h : i ≤ j) (x : G i), cG j (tG i j h x) = cG i x)
    (hcH : ∀ (i j : J) (h : i ≤ j) (x : H i), cH j (tH i j h x) = cH i x)
    (htG : ∀ (i j k : J) (h : i ≤ j) (h' : j ≤ k) (x : G i),
      tG j k h' (tG i j h x) = tG i k (h.trans h') x)
    (htH : ∀ (i j k : J) (h : i ≤ j) (h' : j ≤ k) (x : H i),
      tH j k h' (tH i j h x) = tH i k (h.trans h') x) :
    Descends (fun i j h p => (tG i j h p.1, tH i j h p.2))
      (fun i p => (cG i p.1, cH i p.2)) := by
  refine ⟨fun y => ?_, fun i p p' hp => ?_⟩
  · obtain ⟨i, x, hx⟩ := hG.1 y.1
    obtain ⟨i', x', hx'⟩ := hH.1 y.2
    obtain ⟨k, hik, hik'⟩ := directed_of (· ≤ ·) i i'
    exact ⟨k, (tG i k hik x, tH i' k hik' x'),
      Prod.ext ((hcG i k hik x).trans hx) ((hcH i' k hik' x').trans hx')⟩
  · obtain ⟨j, hij, hj⟩ := hG.2 i p.1 p'.1 (congrArg Prod.fst hp)
    obtain ⟨j', hij', hj'⟩ := hH.2 i p.2 p'.2 (congrArg Prod.snd hp)
    obtain ⟨m, hjm, hjm'⟩ := directed_of (· ≤ ·) j j'
    exact ⟨m, hij.trans hjm, Prod.ext (transition_eq_of_transition_eq htG hij hjm hj)
      (transition_eq_of_transition_eq htH hij' hjm' hj')⟩

/-! ### The five lemma for two Mayer--Vietoris sequences -/

section Ladder

variable {P M N : ℤ → J → Type*} {P' M' N' : ℤ → Type*}
  [∀ (n : ℤ) (i : J), AddCommGroup (P n i)] [∀ (n : ℤ) (i : J), AddCommGroup (M n i)]
  [∀ (n : ℤ) (i : J), AddCommGroup (N n i)]
  [∀ n : ℤ, AddCommGroup (P' n)] [∀ n : ℤ, AddCommGroup (M' n)] [∀ n : ℤ, AddCommGroup (N' n)]
  (tP : ∀ (n : ℤ) (i j : J), i ≤ j → P n i →+ P n j)
  (tM : ∀ (n : ℤ) (i j : J), i ≤ j → M n i →+ M n j)
  (tN : ∀ (n : ℤ) (i j : J), i ≤ j → N n i →+ N n j)
  (cP : ∀ (n : ℤ) (i : J), P n i →+ P' n) (cM : ∀ (n : ℤ) (i : J), M n i →+ M' n)
  (cN : ∀ (n : ℤ) (i : J), N n i →+ N' n)
  (restriction : ∀ (n : ℤ) (i : J), P n i →+ M n i)
  (difference : ∀ (n : ℤ) (i : J), M n i →+ N n i)
  (boundary : ∀ (n₀ n₁ : ℤ), n₀ + 1 = n₁ → ∀ i : J, N n₀ i →+ P n₁ i)
  (restriction' : ∀ n : ℤ, P' n →+ M' n) (difference' : ∀ n : ℤ, M' n →+ N' n)
  (boundary' : ∀ (n₀ n₁ : ℤ), n₀ + 1 = n₁ → (N' n₀ →+ P' n₁))

/-- **The five lemma for a filtered system of Mayer--Vietoris sequences and a Mayer--Vietoris
sequence at the limit, in the descent language.** Given the three maps of the sequence at every
stage and at the limit, exactness at all three spots of both, naturality of the maps in the
stage and commutativity of the three squares, descent at the product spot and at the
intersection spot in every degree gives descent at the ambient spot in every degree. -/
theorem descends_of_mayerVietoris [IsDirected J (· ≤ ·)]
    (htP : ∀ (n : ℤ) (i j k : J) (h : i ≤ j) (h' : j ≤ k) (x : P n i),
      tP n j k h' (tP n i j h x) = tP n i k (h.trans h') x)
    (htN : ∀ (n : ℤ) (i j k : J) (h : i ≤ j) (h' : j ≤ k) (z : N n i),
      tN n j k h' (tN n i j h z) = tN n i k (h.trans h') z)
    (hcP : ∀ (n : ℤ) (i j : J) (h : i ≤ j) (x : P n i), cP n j (tP n i j h x) = cP n i x)
    (hcM : ∀ (n : ℤ) (i j : J) (h : i ≤ j) (y : M n i), cM n j (tM n i j h y) = cM n i y)
    (hcN : ∀ (n : ℤ) (i j : J) (h : i ≤ j) (z : N n i), cN n j (tN n i j h z) = cN n i z)
    (hnr : ∀ (n : ℤ) (i j : J) (h : i ≤ j) (x : P n i),
      restriction n j (tP n i j h x) = tM n i j h (restriction n i x))
    (hnd : ∀ (n : ℤ) (i j : J) (h : i ≤ j) (y : M n i),
      difference n j (tM n i j h y) = tN n i j h (difference n i y))
    (hnb : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i j : J) (h : i ≤ j) (z : N n₀ i),
      boundary n₀ n₁ hn j (tN n₀ i j h z) = tP n₁ i j h (boundary n₀ n₁ hn i z))
    (hsr : ∀ (n : ℤ) (i : J) (x : P n i),
      cM n i (restriction n i x) = restriction' n (cP n i x))
    (hsd : ∀ (n : ℤ) (i : J) (y : M n i),
      cN n i (difference n i y) = difference' n (cM n i y))
    (hsb : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i : J) (z : N n₀ i),
      cP n₁ i (boundary n₀ n₁ hn i z) = boundary' n₀ n₁ hn (cN n₀ i z))
    (herd : ∀ (n : ℤ) (i : J), Function.Exact (restriction n i) (difference n i))
    (hedb : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i : J),
      Function.Exact (difference n₀ i) (boundary n₀ n₁ hn i))
    (hebr : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i : J),
      Function.Exact (boundary n₀ n₁ hn i) (restriction n₁ i))
    (herd' : ∀ n : ℤ, Function.Exact (restriction' n) (difference' n))
    (hedb' : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁),
      Function.Exact (difference' n₀) (boundary' n₀ n₁ hn))
    (hebr' : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁),
      Function.Exact (boundary' n₀ n₁ hn) (restriction' n₁))
    (hM : ∀ n : ℤ, Descends (fun i j h => (tM n i j h : M n i → M n j)) fun i => cM n i)
    (hN : ∀ n : ℤ, Descends (fun i j h => (tN n i j h : N n i → N n j)) fun i => cN n i)
    (n : ℤ) :
    Descends (fun i j h => (tP n i j h : P n i → P n j)) fun i => cP n i := by
  have hn₁ : n - 1 + 1 = n := by omega
  refine ⟨fun ψ => ?_, fun i x x' hxx => ?_⟩
  · obtain ⟨i, y, hy⟩ := (hM n).1 (restriction' n ψ)
    have hy' : cM n i y = restriction' n ψ := hy
    have h0 : cN n i (difference n i y) = cN n i 0 := by
      rw [hsd n i y, hy', map_zero]
      exact (herd' n).apply_apply_eq_zero ψ
    obtain ⟨j, hij, hj⟩ := (hN n).2 i (difference n i y) 0 h0
    have hj' : tN n i j hij (difference n i y) = tN n i j hij 0 := hj
    have hdj : difference n j (tM n i j hij y) = 0 := by
      rw [hnd n i j hij y, hj', map_zero]
    obtain ⟨x, hx⟩ := ((herd n j) (tM n i j hij y)).1 hdj
    have hz : restriction' n (cP n j x - ψ) = 0 := by
      rw [map_sub, ← hsr n j x, hx, hcM n i j hij y, hy', sub_self]
    obtain ⟨z', hz'⟩ := ((hebr' (n - 1) n hn₁) (cP n j x - ψ)).1 hz
    obtain ⟨k, z, hzk⟩ := (hN (n - 1)).1 z'
    have hzk' : cN (n - 1) k z = z' := hzk
    obtain ⟨l, hjl, hkl⟩ := directed_of (· ≤ ·) j k
    refine ⟨l, tP n j l hjl x - boundary (n - 1) n hn₁ l (tN (n - 1) k l hkl z), ?_⟩
    show cP n l _ = ψ
    rw [map_sub, hcP n j l hjl x, hsb (n - 1) n hn₁ l _, hcN (n - 1) k l hkl z, hzk', hz']
    exact sub_sub_cancel _ _
  · have hxx' : cP n i x = cP n i x' := hxx
    have h0 : cP n i (x - x') = 0 := by rw [map_sub, hxx', sub_self]
    have h1 : cM n i (restriction n i (x - x')) = cM n i 0 := by
      rw [hsr n i (x - x'), h0, map_zero, map_zero]
    obtain ⟨j, hij, hj⟩ := (hM n).2 i (restriction n i (x - x')) 0 h1
    have hj' : tM n i j hij (restriction n i (x - x')) = tM n i j hij 0 := hj
    have hrj : restriction n j (tP n i j hij (x - x')) = 0 := by
      rw [hnr n i j hij (x - x'), hj', map_zero]
    obtain ⟨z, hz⟩ := ((hebr (n - 1) n hn₁ j) (tP n i j hij (x - x'))).1 hrj
    have h2 : boundary' (n - 1) n hn₁ (cN (n - 1) j z) = 0 := by
      rw [← hsb (n - 1) n hn₁ j z, hz, hcP n i j hij (x - x'), h0]
    obtain ⟨w', hw'⟩ := ((hedb' (n - 1) n hn₁) (cN (n - 1) j z)).1 h2
    obtain ⟨k, w, hwk⟩ := (hM (n - 1)).1 w'
    have hwk' : cM (n - 1) k w = w' := hwk
    obtain ⟨l, hjl, hkl⟩ := directed_of (· ≤ ·) j k
    have h3 : cN (n - 1) l (tN (n - 1) j l hjl z) =
        cN (n - 1) l (difference (n - 1) l (tM (n - 1) k l hkl w)) := by
      rw [hcN (n - 1) j l hjl z, hsd (n - 1) l _, hcM (n - 1) k l hkl w, hwk', hw']
    obtain ⟨m, hlm, hm⟩ := (hN (n - 1)).2 l _ _ h3
    have hm' : tN (n - 1) l m hlm (tN (n - 1) j l hjl z) =
        tN (n - 1) l m hlm (difference (n - 1) l (tM (n - 1) k l hkl w)) := hm
    refine ⟨m, hij.trans (hjl.trans hlm), ?_⟩
    have h4 : tP n j m (hjl.trans hlm) (tP n i j hij (x - x')) = 0 := by
      rw [← hz, ← hnb (n - 1) n hn₁ j m (hjl.trans hlm) z,
        ← htN (n - 1) j l m hjl hlm z, hm', ← hnd (n - 1) l m hlm _]
      exact (hedb (n - 1) n hn₁ m).apply_apply_eq_zero _
    have h5 : tP n i m (hij.trans (hjl.trans hlm)) (x - x') = 0 :=
      (htP n i j m hij (hjl.trans hlm) (x - x')).symm.trans h4
    show tP n i m _ x = tP n i m _ x'
    exact sub_eq_zero.mp ((map_sub (tP n i m (hij.trans (hjl.trans hlm))) x x').symm.trans h5)

end Ladder

end Stacks.MayerVietoris

namespace Stacks.DerivedPullback

/-! ### Additivity of the maps attached to a factorisation -/

variable {X Y Z : Scheme.{u}}

/-- **The map on derived morphism sets attached to a factorisation is additive.** It is
`Iso.homCongr` of the action of the derived pullback on morphisms, and derived pullback is a
triangulated functor, hence additive. -/
theorem schemeFactorHom_add (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ φ' : (derivedPullback g.toLRSHom.toShHom).obj K ⟶
      (derivedPullback g.toLRSHom.toShHom).obj L) :
    schemeFactorHom f g k h K L (φ + φ') =
      schemeFactorHom f g k h K L φ + schemeFactorHom f g k h K L φ' := by
  simp only [schemeFactorHom, Iso.homCongr_apply, Functor.map_add, Preadditive.comp_add,
    Preadditive.add_comp]

/-- The map on derived morphism sets attached to a factorisation, as a group homomorphism. -/
def schemeFactorAddHom (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    ((derivedPullback g.toLRSHom.toShHom).obj K ⟶
        (derivedPullback g.toLRSHom.toShHom).obj L) →+
      ((derivedPullback k.toLRSHom.toShHom).obj K ⟶
        (derivedPullback k.toLRSHom.toShHom).obj L) :=
  AddMonoidHom.mk' (schemeFactorHom f g k h K L) (schemeFactorHom_add f g k h K L)

end Stacks.DerivedPullback

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

attribute [local implicit_reducible] restrict

variable (K₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-! ### The system of derived morphism sets of a restricted situation as abelian groups -/

section System

variable (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
  (L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- The derived morphism set of the situation restricted to `U₀`, at a stage:
`Hom_{D(𝒪_{Uᵢ})}(Lf_{i0}^*(K₀|_{U₀}), Lf_{i0}^*(L₀|_{U₀}))`. -/
def restrictHomStage (i : D.LaterIndex) : Type (u + 1) :=
  ((D.restrict U₀ hU₀).homFunctor ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀)
    ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀)).obj i

/-- The derived morphism set of the situation restricted to `U₀`, at the limit:
`Hom_{D(𝒪_U)}(Lf₀^*(K₀|_{U₀}), Lf₀^*(L₀|_{U₀}))`. -/
def restrictHomLimit : Type (u + 1) :=
  ((D.restrict U₀ hU₀).homCocone ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀)
    ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀)).pt

/-- The abelian group structure on the derived morphism set of the restricted situation at a
stage, as morphisms in a derived category. -/
instance instAddCommGroupRestrictHomStage (i : D.LaterIndex) :
    AddCommGroup (D.restrictHomStage K₀ U₀ hU₀ L₀ i) :=
  show AddCommGroup (_ ⟶ _) from inferInstance

/-- The abelian group structure on the derived morphism set of the restricted situation at the
limit, as morphisms in a derived category. -/
instance instAddCommGroupRestrictHomLimit :
    AddCommGroup (D.restrictHomLimit K₀ U₀ hU₀ L₀) :=
  show AddCommGroup (_ ⟶ _) from inferInstance

/-- The transition map of the system of derived morphism sets of the situation restricted to
`U₀`, as a group homomorphism. -/
def restrictHomTransition (i j : D.LaterIndex) (h : i ≤ j) :
    D.restrictHomStage K₀ U₀ hU₀ L₀ i →+ D.restrictHomStage K₀ U₀ hU₀ L₀ j :=
  Stacks.DerivedPullback.schemeFactorAddHom ((D.restrict U₀ hU₀).transition h)
    ((D.restrict U₀ hU₀).toFixedStage i) ((D.restrict U₀ hU₀).toFixedStage j)
    ((D.restrict U₀ hU₀).transition_comp_toFixedStage h) _ _

/-- The comparison map of the system of derived morphism sets of the situation restricted to
`U₀`, as a group homomorphism. -/
def restrictHomComparison (i : D.LaterIndex) :
    D.restrictHomStage K₀ U₀ hU₀ L₀ i →+ D.restrictHomLimit K₀ U₀ hU₀ L₀ :=
  Stacks.DerivedPullback.schemeFactorAddHom ((D.restrict U₀ hU₀).projection i)
    ((D.restrict U₀ hU₀).toFixedStage i) (D.restrict U₀ hU₀).limitToFixedStage
    ((D.restrict U₀ hU₀).projection_comp_toFixedStage i) _ _

/-- The transition maps of the system of derived morphism sets of a restricted situation
compose. -/
theorem restrictHomTransition_restrictHomTransition (i j k : D.LaterIndex) (h : i ≤ j)
    (h' : j ≤ k) (x : D.restrictHomStage K₀ U₀ hU₀ L₀ i) :
    D.restrictHomTransition K₀ U₀ hU₀ L₀ j k h' (D.restrictHomTransition K₀ U₀ hU₀ L₀ i j h x) =
      D.restrictHomTransition K₀ U₀ hU₀ L₀ i k (h.trans h') x :=
  (D.restrict U₀ hU₀).homTransition_homTransition _ _ h h' x

/-- The comparison maps of the system of derived morphism sets of a restricted situation are
compatible with its transition maps. -/
theorem restrictHomComparison_restrictHomTransition (i j : D.LaterIndex) (h : i ≤ j)
    (x : D.restrictHomStage K₀ U₀ hU₀ L₀ i) :
    D.restrictHomComparison K₀ U₀ hU₀ L₀ j (D.restrictHomTransition K₀ U₀ hU₀ L₀ i j h x) =
      D.restrictHomComparison K₀ U₀ hU₀ L₀ i x :=
  (D.restrict U₀ hU₀).homComparison_homTransition _ _ h x

/-- **Tag 0DI7 for the restriction to `U₀` is the abstract descent predicate** for the system of
derived morphism sets of the restricted situation. -/
theorem restrictHomDescent_iff_descends :
    D.RestrictHomDescent K₀ L₀ U₀ hU₀ ↔
      Stacks.MayerVietoris.Descends
        (fun i j h => (D.restrictHomTransition K₀ U₀ hU₀ L₀ i j h :
          D.restrictHomStage K₀ U₀ hU₀ L₀ i → D.restrictHomStage K₀ U₀ hU₀ L₀ j))
        fun i => D.restrictHomComparison K₀ U₀ hU₀ L₀ i :=
  Iff.rfl

end System

/-! ### The Mayer--Vietoris sequence on the systems of derived morphism sets -/

section Sup

variable (L : ℤ → DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))
  (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
  (hV₀ : IsCompact (V₀ : Set D.X₀.left))
  (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
  (hsup : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left))

/-- **The Mayer--Vietoris sequence of Stacks 08BW on the systems of derived morphism sets of the
situation restricted to `U₀`, `V₀`, `U₀ ∩ V₀` and `U₀ ∪ V₀`.** The three maps of the sequence at
every stage and at the limit, exactness at all three spots of both, naturality of the maps in
the stage, and the three squares saying that the comparison maps to the limit form a morphism of
sequences. Discharging it is Stacks 08BW at the stages and at the limit, read through the
adjunction of Stacks 08BT, derived base change for extension by zero of a restriction, and the
comparison of `(L n)|_W` with `(L 0)|_W⟦n⟧`. -/
structure MayerVietorisHomSequence where
  /-- The restriction map of the sequence at a stage. -/
  stageRestriction : ∀ (n : ℤ) (i : D.LaterIndex),
    D.restrictHomStage K₀ (U₀ ⊔ V₀) hsup (L n) i →+
      D.restrictHomStage K₀ U₀ hU₀ (L n) i × D.restrictHomStage K₀ V₀ hV₀ (L n) i
  /-- The difference map of the sequence at a stage. -/
  stageDifference : ∀ (n : ℤ) (i : D.LaterIndex),
    (D.restrictHomStage K₀ U₀ hU₀ (L n) i × D.restrictHomStage K₀ V₀ hV₀ (L n) i) →+
      D.restrictHomStage K₀ (U₀ ⊓ V₀) hinf (L n) i
  /-- The connecting map of the sequence at a stage. -/
  stageBoundary : ∀ (n₀ n₁ : ℤ), n₀ + 1 = n₁ → ∀ i : D.LaterIndex,
    D.restrictHomStage K₀ (U₀ ⊓ V₀) hinf (L n₀) i →+
      D.restrictHomStage K₀ (U₀ ⊔ V₀) hsup (L n₁) i
  /-- The restriction map of the sequence at the limit. -/
  limitRestriction : ∀ n : ℤ,
    D.restrictHomLimit K₀ (U₀ ⊔ V₀) hsup (L n) →+
      D.restrictHomLimit K₀ U₀ hU₀ (L n) × D.restrictHomLimit K₀ V₀ hV₀ (L n)
  /-- The difference map of the sequence at the limit. -/
  limitDifference : ∀ n : ℤ,
    (D.restrictHomLimit K₀ U₀ hU₀ (L n) × D.restrictHomLimit K₀ V₀ hV₀ (L n)) →+
      D.restrictHomLimit K₀ (U₀ ⊓ V₀) hinf (L n)
  /-- The connecting map of the sequence at the limit. -/
  limitBoundary : ∀ (n₀ n₁ : ℤ), n₀ + 1 = n₁ →
    (D.restrictHomLimit K₀ (U₀ ⊓ V₀) hinf (L n₀) →+
      D.restrictHomLimit K₀ (U₀ ⊔ V₀) hsup (L n₁))
  /-- The restriction map is natural in the stage. -/
  stageRestriction_transition : ∀ (n : ℤ) (i j : D.LaterIndex) (h : i ≤ j)
      (x : D.restrictHomStage K₀ (U₀ ⊔ V₀) hsup (L n) i),
    stageRestriction n j (D.restrictHomTransition K₀ (U₀ ⊔ V₀) hsup (L n) i j h x) =
      (D.restrictHomTransition K₀ U₀ hU₀ (L n) i j h (stageRestriction n i x).1,
        D.restrictHomTransition K₀ V₀ hV₀ (L n) i j h (stageRestriction n i x).2)
  /-- The difference map is natural in the stage. -/
  stageDifference_transition : ∀ (n : ℤ) (i j : D.LaterIndex) (h : i ≤ j)
      (y : D.restrictHomStage K₀ U₀ hU₀ (L n) i × D.restrictHomStage K₀ V₀ hV₀ (L n) i),
    stageDifference n j (D.restrictHomTransition K₀ U₀ hU₀ (L n) i j h y.1,
        D.restrictHomTransition K₀ V₀ hV₀ (L n) i j h y.2) =
      D.restrictHomTransition K₀ (U₀ ⊓ V₀) hinf (L n) i j h (stageDifference n i y)
  /-- The connecting map is natural in the stage. -/
  stageBoundary_transition : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i j : D.LaterIndex) (h : i ≤ j)
      (z : D.restrictHomStage K₀ (U₀ ⊓ V₀) hinf (L n₀) i),
    stageBoundary n₀ n₁ hn j (D.restrictHomTransition K₀ (U₀ ⊓ V₀) hinf (L n₀) i j h z) =
      D.restrictHomTransition K₀ (U₀ ⊔ V₀) hsup (L n₁) i j h (stageBoundary n₀ n₁ hn i z)
  /-- The comparison maps commute with the restriction maps. -/
  limitRestriction_comparison : ∀ (n : ℤ) (i : D.LaterIndex)
      (x : D.restrictHomStage K₀ (U₀ ⊔ V₀) hsup (L n) i),
    (D.restrictHomComparison K₀ U₀ hU₀ (L n) i (stageRestriction n i x).1,
        D.restrictHomComparison K₀ V₀ hV₀ (L n) i (stageRestriction n i x).2) =
      limitRestriction n (D.restrictHomComparison K₀ (U₀ ⊔ V₀) hsup (L n) i x)
  /-- The comparison maps commute with the difference maps. -/
  limitDifference_comparison : ∀ (n : ℤ) (i : D.LaterIndex)
      (y : D.restrictHomStage K₀ U₀ hU₀ (L n) i × D.restrictHomStage K₀ V₀ hV₀ (L n) i),
    D.restrictHomComparison K₀ (U₀ ⊓ V₀) hinf (L n) i (stageDifference n i y) =
      limitDifference n (D.restrictHomComparison K₀ U₀ hU₀ (L n) i y.1,
        D.restrictHomComparison K₀ V₀ hV₀ (L n) i y.2)
  /-- The comparison maps commute with the connecting maps. -/
  limitBoundary_comparison : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i : D.LaterIndex)
      (z : D.restrictHomStage K₀ (U₀ ⊓ V₀) hinf (L n₀) i),
    D.restrictHomComparison K₀ (U₀ ⊔ V₀) hsup (L n₁) i (stageBoundary n₀ n₁ hn i z) =
      limitBoundary n₀ n₁ hn (D.restrictHomComparison K₀ (U₀ ⊓ V₀) hinf (L n₀) i z)
  /-- Exactness at the product spot at a stage. -/
  exact_stageRestriction_stageDifference : ∀ (n : ℤ) (i : D.LaterIndex),
    Function.Exact (stageRestriction n i) (stageDifference n i)
  /-- Exactness at the intersection spot at a stage. -/
  exact_stageDifference_stageBoundary : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i : D.LaterIndex),
    Function.Exact (stageDifference n₀ i) (stageBoundary n₀ n₁ hn i)
  /-- Exactness at the ambient spot at a stage. -/
  exact_stageBoundary_stageRestriction : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁) (i : D.LaterIndex),
    Function.Exact (stageBoundary n₀ n₁ hn i) (stageRestriction n₁ i)
  /-- Exactness at the product spot at the limit. -/
  exact_limitRestriction_limitDifference : ∀ n : ℤ,
    Function.Exact (limitRestriction n) (limitDifference n)
  /-- Exactness at the intersection spot at the limit. -/
  exact_limitDifference_limitBoundary : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁),
    Function.Exact (limitDifference n₀) (limitBoundary n₀ n₁ hn)
  /-- Exactness at the ambient spot at the limit. -/
  exact_limitBoundary_limitRestriction : ∀ (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁),
    Function.Exact (limitBoundary n₀ n₁ hn) (limitRestriction n₁)

/-- **The Mayer--Vietoris union step of Tag 0DI7.** From the Mayer--Vietoris sequences on the
four systems of derived morphism sets, Tag 0DI7 for the restriction to `U₀`, to `V₀` and to
`U₀ ∩ V₀` in every degree gives Tag 0DI7 for the restriction to `U₀ ∪ V₀` in every degree. The
five lemma in degree `n` consumes the degree `n - 1`, which is why the whole family is
inducted. -/
theorem restrictHomDescent_sup_of_mayerVietorisHomSequence
    (mv : D.MayerVietorisHomSequence K₀ L U₀ V₀ hU₀ hV₀ hinf hsup)
    (hU : ∀ n : ℤ, D.RestrictHomDescent K₀ (L n) U₀ hU₀)
    (hV : ∀ n : ℤ, D.RestrictHomDescent K₀ (L n) V₀ hV₀)
    (hI : ∀ n : ℤ, D.RestrictHomDescent K₀ (L n) (U₀ ⊓ V₀) hinf) (n : ℤ) :
    D.RestrictHomDescent K₀ (L n) (U₀ ⊔ V₀) hsup := by
  have _ : IsDirected D.LaterIndex (· ≤ ·) := D.isDirected_laterIndex
  refine (D.restrictHomDescent_iff_descends K₀ (U₀ ⊔ V₀) hsup (L n)).2 ?_
  refine Stacks.MayerVietoris.descends_of_mayerVietoris
    (fun n i j h => D.restrictHomTransition K₀ (U₀ ⊔ V₀) hsup (L n) i j h)
    (fun n i j h => AddMonoidHom.prodMap (D.restrictHomTransition K₀ U₀ hU₀ (L n) i j h)
      (D.restrictHomTransition K₀ V₀ hV₀ (L n) i j h))
    (fun n i j h => D.restrictHomTransition K₀ (U₀ ⊓ V₀) hinf (L n) i j h)
    (fun n i => D.restrictHomComparison K₀ (U₀ ⊔ V₀) hsup (L n) i)
    (fun n i => AddMonoidHom.prodMap (D.restrictHomComparison K₀ U₀ hU₀ (L n) i)
      (D.restrictHomComparison K₀ V₀ hV₀ (L n) i))
    (fun n i => D.restrictHomComparison K₀ (U₀ ⊓ V₀) hinf (L n) i)
    mv.stageRestriction mv.stageDifference mv.stageBoundary
    mv.limitRestriction mv.limitDifference mv.limitBoundary
    (fun n i j k h h' x =>
      D.restrictHomTransition_restrictHomTransition K₀ (U₀ ⊔ V₀) hsup (L n) i j k h h' x)
    (fun n i j k h h' z =>
      D.restrictHomTransition_restrictHomTransition K₀ (U₀ ⊓ V₀) hinf (L n) i j k h h' z)
    (fun n i j h x =>
      D.restrictHomComparison_restrictHomTransition K₀ (U₀ ⊔ V₀) hsup (L n) i j h x)
    (fun n i j h y => Prod.ext
      (D.restrictHomComparison_restrictHomTransition K₀ U₀ hU₀ (L n) i j h y.1)
      (D.restrictHomComparison_restrictHomTransition K₀ V₀ hV₀ (L n) i j h y.2))
    (fun n i j h z =>
      D.restrictHomComparison_restrictHomTransition K₀ (U₀ ⊓ V₀) hinf (L n) i j h z)
    mv.stageRestriction_transition mv.stageDifference_transition mv.stageBoundary_transition
    mv.limitRestriction_comparison
    mv.limitDifference_comparison mv.limitBoundary_comparison
    mv.exact_stageRestriction_stageDifference mv.exact_stageDifference_stageBoundary
    mv.exact_stageBoundary_stageRestriction mv.exact_limitRestriction_limitDifference
    mv.exact_limitDifference_limitBoundary mv.exact_limitBoundary_limitRestriction
    (fun n => Stacks.MayerVietoris.Descends.prod
      ((D.restrictHomDescent_iff_descends K₀ U₀ hU₀ (L n)).1 (hU n))
      ((D.restrictHomDescent_iff_descends K₀ V₀ hV₀ (L n)).1 (hV n))
      (fun i j h x => D.restrictHomComparison_restrictHomTransition K₀ U₀ hU₀ (L n) i j h x)
      (fun i j h x => D.restrictHomComparison_restrictHomTransition K₀ V₀ hV₀ (L n) i j h x)
      (fun i j k h h' x =>
        D.restrictHomTransition_restrictHomTransition K₀ U₀ hU₀ (L n) i j k h h' x)
      (fun i j k h h' x =>
        D.restrictHomTransition_restrictHomTransition K₀ V₀ hV₀ (L n) i j k h h' x))
    (fun n => (D.restrictHomDescent_iff_descends K₀ (U₀ ⊓ V₀) hinf (L n)).1 (hI n)) n

end Sup

/-! ### The hypothesis `hsup` of the reduction -/

section Family

variable (L : ℤ → DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- **The hypothesis `hsup` of
`restrictHomDescent_family_of_isAffineOpen_over_affine_of_sup`**, from the Mayer--Vietoris
sequences on the systems of derived morphism sets. Neither the affineness of `V₀` nor its lying
over an affine open of the base is used: the union step is Mayer--Vietoris for a cover by two
quasi-compact opens. -/
theorem restrictHomDescent_sup_of_family
    (mv : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsCompact (V₀ : Set D.X₀.left))
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      D.MayerVietorisHomSequence K₀ L U₀ V₀ hU₀ hV₀ hinf hsupc) :
    ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsAffineOpen V₀) (_ : D.IsAffineOpenOverAffine V₀)
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      (∀ n : ℤ, D.RestrictHomDescent K₀ (L n) U₀ hU₀) →
      (∀ n : ℤ, D.RestrictHomDescent K₀ (L n) V₀ hV₀.isCompact) →
      (∀ n : ℤ, D.RestrictHomDescent K₀ (L n) (U₀ ⊓ V₀) hinf) →
        ∀ n : ℤ, D.RestrictHomDescent K₀ (L n) (U₀ ⊔ V₀) hsupc :=
  fun U₀ V₀ hU₀ hV₀ _ hinf hsupc hU hV hI =>
    D.restrictHomDescent_sup_of_mayerVietorisHomSequence K₀ L U₀ V₀ hU₀ hV₀.isCompact hinf hsupc
      (mv U₀ V₀ hU₀ hV₀.isCompact hinf hsupc) hU hV hI

/-- **Tag 0DI7 from its two hypotheses.** The affine case over an affine open of the base and the
Mayer--Vietoris sequences together give the conclusion of Stacks 0DI7 for every member of the
family. -/
theorem homDescent_family_of_mayerVietorisHomSequence
    (haffine : ∀ (n : ℤ) (V₀ : D.X₀.left.Opens) (hV₀ : IsAffineOpen V₀),
      D.IsAffineOpenOverAffine V₀ → D.RestrictHomDescent K₀ (L n) V₀ hV₀.isCompact)
    (mv : ∀ (U₀ V₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
      (hV₀ : IsCompact (V₀ : Set D.X₀.left))
      (hinf : IsCompact ((U₀ ⊓ V₀ : D.X₀.left.Opens) : Set D.X₀.left))
      (hsupc : IsCompact ((U₀ ⊔ V₀ : D.X₀.left.Opens) : Set D.X₀.left)),
      D.MayerVietorisHomSequence K₀ L U₀ V₀ hU₀ hV₀ hinf hsupc) (n : ℤ) :
    D.HomDescent K₀ (L n) :=
  D.homDescent_family_of_isAffineOpen_over_affine_of_sup K₀ L haffine
    (D.restrictHomDescent_sup_of_family K₀ L mv) n

end Family

end AlgebraicGeometry.RelativeDescentSituation

end
