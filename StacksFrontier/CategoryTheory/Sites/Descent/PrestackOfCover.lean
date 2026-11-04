module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Being a prestack for a sieve is local on the base

Let `F` be a pseudofunctor from the locally discrete bicategory on `Cᵒᵖ` to `Cat` and let `R` be
a sieve on an object `Y` of `C`. Whether `F` is a prestack for `R` — that is, whether the
descent data of `F` for `R` with a fixed pair of objects over `Y` form a sheaf of morphisms —
can be tested on a cover of `Y`: if `F` is a prestack for a family `g i : Z i ⟶ Y` and for all
its pullbacks, and a prestack for the restriction of `R` to each `Z i` and to the chosen
pullbacks `Z i ×_Y Z j`, then `F` is a prestack for `R`.

The statement for presheaves of which this is the pseudofunctor version — a presheaf is a sheaf
for a sieve as soon as it is a sheaf for a cover, separated for the pullbacks of that cover, a
sheaf for the restrictions of the sieve to the members and separated for its restrictions to
the pairwise overlaps — is proved first and is of independent interest.

## Main definitions

* `CategoryTheory.Limits.ChosenPullback.over`: a chosen pullback of two morphisms to `Y`, read
  as a chosen pullback in the slice category over `Y`.

## Main results

* `CategoryTheory.Presieve.isSheafFor_of_cover`: the sheaf condition for a sieve is local;
* `CategoryTheory.Pseudofunctor.isPrestackFor_of_cover`: being a prestack for a sieve is local;
* `CategoryTheory.Pseudofunctor.isPrestackFor_of_equivalence`: effective descent along a family
  implies being a prestack for the sieve it generates;
* `CategoryTheory.Pseudofunctor.isPrestackFor_pullback_of_equivalence`: the same for the
  pullback of that sieve along a morphism, given effective descent along the base-changed
  family.

## Implementation notes

The presheaf statement is proved by glueing: the local sections over the members of the cover
are glued by the sheaf condition for the cover, which applies because the two restrictions of
the glued family to a chosen pullback agree — and that is where separatedness for the
restriction of `R` to the pairwise overlaps is used. Uniqueness of the glued section needs only
separatedness for the pullbacks of the cover.

The pseudofunctor statement is the presheaf statement applied to
`CategoryTheory.Pseudofunctor.presheafHom` on the slice category over `Y`, which is what
`CategoryTheory.Pseudofunctor.isPrestackFor_iff_isSheafFor` reduces being a prestack to; the
sieves on the slice category are matched with the sieves on `C` by
`CategoryTheory.Sieve.overEquiv`.

Nothing here carries a Stacks attribute: this is category-theoretic substrate, and the source
states none of it.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits Opposite

universe t w v v' u u'

namespace Limits

/-- A chosen pullback of two morphisms to `Y`, read as a chosen pullback of the corresponding
morphisms to the terminal object of the slice category over `Y`. -/
@[sga "4 IV 5.11.1" "special case"]
noncomputable def ChosenPullback.over {C : Type u} [Category.{v} C] {Y Z W : C}
    {g : Z ⟶ Y} {h : W ⟶ Y} (sq : ChosenPullback g h) :
    ChosenPullback (Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 Y))
      (Over.homMk h : Over.mk h ⟶ Over.mk (𝟙 Y)) where
  pullback := Over.mk sq.p
  p₁ := Over.homMk sq.p₁
  p₂ := Over.homMk sq.p₂
  condition := by ext; exact sq.condition
  isLimit := by
    have hsq : IsPullback (Over.homMk sq.p₁ : Over.mk sq.p ⟶ Over.mk g)
        (Over.homMk sq.p₂ : Over.mk sq.p ⟶ Over.mk h)
        (Over.homMk g : Over.mk g ⟶ Over.mk (𝟙 Y))
        (Over.homMk h : Over.mk h ⟶ Over.mk (𝟙 Y)) :=
      IsPullback.of_map (Over.forget Y) (by ext; exact sq.condition) sq.isPullback
    exact hsq.isLimit

end Limits

/-- **The sheaf condition for a sieve is local on the base.** A presheaf is a sheaf for a sieve
`R` on `Y` as soon as it is a sheaf for a family `g`, separated for every pullback of that
family, a sheaf for the restriction of `R` to each member and separated for the restriction of
`R` to each chosen pairwise overlap. -/
theorem Presieve.isSheafFor_of_cover {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type w)
    {Y : C} {I : Type t} {Z : I → C} (g : ∀ i, Z i ⟶ Y)
    (sq : ∀ i j, ChosenPullback (g i) (g j)) (R : Sieve Y)
    (hg : Presieve.IsSheafFor P (.ofArrows Z g))
    (hg' : ∀ {T : C} (t : T ⟶ Y), Presieve.IsSeparatedFor P
      ((Sieve.ofArrows Z g).pullback t).arrows)
    (hloc : ∀ i, Presieve.IsSheafFor P (R.pullback (g i)).arrows)
    (hpair : ∀ i j, Presieve.IsSeparatedFor P (R.pullback (sq i j).p).arrows) :
    Presieve.IsSheafFor P R.arrows := by
  intro a ha
  choose s hs huniq using fun i ↦ hloc i (a.pullback (g i)) (ha.pullback (g i))
  have hcompat : Presieve.Arrows.Compatible P g s := by
    intro i j T p q hpq
    obtain ⟨r, hr, hq⟩ := (sq i j).isPullback.exists_lift p q hpq
    have heq : P.map (sq i j).p₁.op (s i) = P.map (sq i j).p₂.op (s j) := by
      apply (hpair i j).ext
      intro W b hb
      simp only [← comp_apply, ← Functor.map_comp, ← op_comp]
      rw [hs i (b ≫ (sq i j).p₁) (by simpa using hb),
        hs j (b ≫ (sq i j).p₂) (by simpa using hb)]
      dsimp only [Presieve.FamilyOfElements.pullback]
      congr 1
      simp
    rw [← hr, ← hq, op_comp, Functor.map_comp, op_comp, Functor.map_comp]
    exact congrArg (P.map r.op) heq
  obtain ⟨s', hs', huniq'⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hg s hcompat
  refine ⟨s', ?_, ?_⟩
  · intro T f hf
    apply (hg' f).ext
    rintro W b ⟨V, c, d, ⟨i⟩, hcd⟩
    rw [← comp_apply, ← Functor.map_comp, ← op_comp]
    have heq : a (b ≫ f) (by simp [hf]) = a (c ≫ g i) (by simp [hcd, hf]) := by
      congr 1
      exact hcd.symm
    simpa [← hcd, hs' i, ← a.comp_of_compatible _ ha, heq,
      Presieve.FamilyOfElements.pullback] using
        hs i c (by simpa [hcd] using R.downward_closed hf b)
  · intro y hy
    apply huniq'
    intro i
    apply huniq i
    intro T b hb
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hb]

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

/-- **Being a prestack for a sieve is local on the base.** -/
theorem isPrestackFor_of_cover {Y : C} {I : Type t} {Z : I → C} (g : ∀ i, Z i ⟶ Y)
    (sq : ∀ i j, ChosenPullback (g i) (g j)) (R : Sieve Y)
    (hg : F.IsPrestackFor (Sieve.ofArrows Z g).arrows)
    (hg' : ∀ {T : C} (t : T ⟶ Y), F.IsPrestackFor
      ((Sieve.ofArrows Z g).pullback t).arrows)
    (hloc : ∀ i, F.IsPrestackFor (R.pullback (g i)).arrows)
    (hpair : ∀ i j, F.IsPrestackFor (R.pullback (sq i j).p).arrows) :
    F.IsPrestackFor R.arrows := by
  rw [F.isPrestackFor_iff_isSheafFor]
  intro M N
  apply Presieve.isSheafFor_of_cover (F.presheafHom M N)
    (fun i ↦ (Over.homMk (g i) : Over.mk (g i) ⟶ Over.mk (𝟙 Y)))
    (fun i j ↦ (sq i j).over)
  · rw [Presieve.isSheafFor_iff_generate]
    have h := (F.isPrestackFor_iff_isSheafFor' _).mp hg M N (𝟙 Y)
    convert h using 1
    congr 1
    apply (Sieve.overEquiv _).injective
    simp only [Sieve.ofArrows, Sieve.overEquiv_ofArrows, OrderIso.apply_symm_apply]
    rfl
  · intro T t
    obtain ⟨T, a, rfl⟩ := T.mk_surjective
    have h := (F.isPrestackFor_iff_isSheafFor' _).mp (hg' t.left) M N a
    apply Presieve.IsSheafFor.isSeparatedFor
    convert h using 1
    congr 1
    apply (Sieve.overEquiv _).injective
    simp only [Sieve.overEquiv_pullback, Sieve.overEquiv_ofArrows,
      OrderIso.apply_symm_apply]
    rfl
  · intro i
    have h := (F.isPrestackFor_iff_isSheafFor' _).mp (hloc i) M N (g i)
    rw [← Sieve.overEquiv_symm_pullback]
    exact h
  · intro i j
    show Presieve.IsSeparatedFor (F.presheafHom M N)
      (((Sieve.overEquiv (Over.mk (𝟙 Y))).symm R).pullback
        (Over.homMk ((sq i j).p₁ ≫ g i) : Over.mk (sq i j).p ⟶ _)).arrows
    rw [← Sieve.overEquiv_symm_pullback]
    have h := (F.isPrestackFor_iff_isSheafFor' _).mp (hpair i j) M N (sq i j).p
    simpa using h.isSeparatedFor

/-- **Effective descent along a family implies being a prestack for the sieve it generates.** -/
theorem isPrestackFor_of_equivalence {Y : C} {I : Type t} {Z : I → C} (g : ∀ i, Z i ⟶ Y)
    (hg : (F.toDescentData g).IsEquivalence) :
    F.IsPrestackFor (Sieve.ofArrows Z g).arrows := by
  rw [Sieve.ofArrows, F.IsPrestackFor_generate_iff, F.isPrestackFor_ofArrows_iff]
  have := hg
  exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

/-- **Effective descent along a base-changed family implies being a prestack for the pullback of
the sieve.** -/
theorem isPrestackFor_pullback_of_equivalence {Y : C} {I : Type t} {Z : I → C}
    (g : ∀ i, Z i ⟶ Y) {T : C} (t : T ⟶ Y) (W : I → C)
    (p : ∀ i, W i ⟶ T) (q : ∀ i, W i ⟶ Z i)
    (hsq : ∀ i, IsPullback (p i) (q i) t (g i))
    (hp : (F.toDescentData p).IsEquivalence) :
    F.IsPrestackFor ((Sieve.ofArrows Z g).pullback t).arrows := by
  rw [← Sieve.ofArrows_eq_pullback_of_isPullback g hsq]
  exact isPrestackFor_of_equivalence F p hp

end Pseudofunctor

end CategoryTheory

end
