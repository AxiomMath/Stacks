module

public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

/-!
# Stacks 007Q — completing a square over an injective morphism

Tag 007Q is the standard application of tag 007P. Let `(C, F)` be a type of algebraic structure
(tag 007M) and let

```
A ⟶ B
    ↓
C ⟶ D
```

be a diagram in `C`, with morphisms `f : A ⟶ B`, `h : B ⟶ D` and `g : C ⟶ D`. If `F g` is
injective and the image of `F (f ≫ h)` is contained in the image of `F g`, then there is a
morphism `t : A ⟶ C` completing the square, i.e. `t ≫ g = f ≫ h`.

The definition of tag 007M is restated here as `AlgebraicStructureTypeBundled`, with the source
category `Sets` modelled by `Type w` and with the existence of limits and filtered colimits in
`C` asserted separately from their preservation by `F` (preservation does not imply existence).

The proof of `algebraicStructure_factor_exists` forms the fibre product of `f ≫ h` and `g`. Since
`F` preserves finite limits the image square is a pullback in `Type w`; the two hypotheses make
the projection `F (A ×_D C) → F A` injective and surjective, so it is an isomorphism there, and
because `F` reflects isomorphisms the projection `A ×_D C → A` is an isomorphism in `C`.
Composing its inverse with the other projection gives `t`.
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits

universe v u w

-- checkUnivs false positive: the objects, category structure and functor use `u`/`v`/`w`
-- separately, but they only occur together in the structure's sort; always used with
-- explicit universe arguments.
/-- A *type of algebraic structure* (Stacks 007M): a category `C` together with a
functor `F : C ⥤ Type` which is faithful, such that `C` has all limits and `F`
preserves them, `C` has filtered colimits and `F` preserves them, and `F`
reflects isomorphisms.

We model the category `Sets` of the source by the universe `Type w`. Existence of
limits and filtered colimits in `C` is asserted explicitly via `HasLimitsOfSize`
and `HasFilteredColimitsOfSize` (it is *not* implied by the preservation
hypotheses), faithfully matching Definition 6.15.1. -/
structure AlgebraicStructureTypeBundled where
  /-- The underlying type of objects of the category `C`. -/
  C : Type u
  /-- The category structure on `C`. -/
  category : Category.{v} C
  /-- The forgetful functor `F : C ⥤ Sets`. -/
  F : C ⥤ Type w
  /-- `F` is faithful. -/
  faithful : F.Faithful
  /-- `C` has all limits. -/
  hasLimits : HasLimitsOfSize.{v, v} C
  /-- `F` preserves all limits. -/
  preservesLimits : PreservesLimitsOfSize.{v, v} F
  /-- `C` has filtered colimits. -/
  hasFilteredColimits : HasFilteredColimitsOfSize.{v, v} C
  /-- `F` preserves filtered colimits. -/
  preservesFilteredColimits : PreservesFilteredColimitsOfSize.{v, v} F
  /-- `F` reflects isomorphisms. -/
  reflectsIsos : F.ReflectsIsomorphisms

attribute [instance] AlgebraicStructureTypeBundled.category AlgebraicStructureTypeBundled.faithful
  AlgebraicStructureTypeBundled.hasLimits AlgebraicStructureTypeBundled.preservesLimits
  AlgebraicStructureTypeBundled.hasFilteredColimits
  AlgebraicStructureTypeBundled.preservesFilteredColimits
  AlgebraicStructureTypeBundled.reflectsIsos

/-- In a pullback square of types, the projection opposite `g` is bijective as soon as `g` is
injective and the range of `f` is contained in the range of `g`. -/
lemma bijective_fst_of_isPullback {P X Y Z : Type w} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (hpb : IsPullback fst snd f g)
    (hg : Function.Injective g) (hf : Set.range f ⊆ Set.range g) :
    Function.Bijective fst :=
  ⟨(mono_iff_injective fst).1 (hpb.mono_fst_of_mono ((mono_iff_injective g).2 hg)),
    Set.range_eq_univ.1 <| by
      rw [Types.range_fst_of_isPullback hpb]
      exact Set.preimage_eq_univ_iff.2 hf⟩

/-- For a functor to types that preserves finite limits and reflects isomorphisms, the pullback
projection `pullback.fst k g` is an isomorphism as soon as `F g` is injective and the range of
`F k` is contained in the range of `F g`. -/
lemma isIso_pullbackFst_of_injective_of_range_subset {D : Type u} [Category.{v} D]
    (F : D ⥤ Type w) [PreservesFiniteLimits F] [F.ReflectsIsomorphisms]
    {X Y Z : D} (k : X ⟶ Z) (g : Y ⟶ Z) [HasPullback k g]
    (hg : Function.Injective (F.map g))
    (hk : Set.range (F.map k) ⊆ Set.range (F.map g)) :
    IsIso (pullback.fst k g) :=
  have : IsIso (F.map (pullback.fst k g)) := (isIso_iff_bijective _).2 <|
    bijective_fst_of_isPullback ((IsPullback.of_hasPullback k g).map F) hg hk
  isIso_of_reflects_iso (pullback.fst k g) F

/-- Stacks Project Example 6.15.5 (tag 007Q).

Given a type of algebraic structure `(C, F)`, objects `A, B, C, D` and morphisms
`f : A ⟶ B`, `h : B ⟶ D`, `g : C ⟶ D`, such that:

* `F(g)` is injective (`g` is injective on underlying sets); and
* the image of `F(f ≫ h)` is contained in the image of `F(g)`
  (here `f ≫ h : A ⟶ D` is the composite `A → B → D`, i.e. `h ∘ f`),

there exists a morphism `t : A ⟶ C` making the square commute, i.e.
`t ≫ g = f ≫ h` (equivalently `g ∘ t = h ∘ f`). -/
@[stacks 007Q]
theorem algebraicStructure_factor_exists (S : AlgebraicStructureTypeBundled.{v, u, w})
    (A B C D : S.C) (f : A ⟶ B) (h : B ⟶ D) (g : C ⟶ D)
    (hg : Function.Injective (S.F.map g))
    (himg : Set.range (S.F.map (f ≫ h)) ⊆ Set.range (S.F.map g)) :
    ∃ t : A ⟶ C, t ≫ g = f ≫ h := by
  have : HasPullbacks S.C := hasPullbacks_of_hasLimit_cospan S.C
  have : PreservesFiniteLimits S.F := PreservesLimitsOfSize.preservesFiniteLimits S.F
  have := isIso_pullbackFst_of_injective_of_range_subset S.F (f ≫ h) g hg himg
  refine ⟨inv (pullback.fst (f ≫ h) g) ≫ pullback.snd (f ≫ h) g, ?_⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
