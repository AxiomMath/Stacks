module

public import StacksFrontier.Topology.Sheaves.AlgebraicStructure.Defs
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
# Stacks 007O — consequences of the axioms for a type of algebraic structure

Let `(C, F)` be a type of algebraic structure (tag 007M): a category `C` with a faithful functor
`F : C ⥤ Type v` preserving all small limits and all small filtered colimits and reflecting
isomorphisms. Tag 007O lists seven consequences, one per theorem below:

1. `C` has a final object and `F` sends it to a one-element set;
2. `C` has all small products and `F` turns them into products of sets;
3. `C` has fibre products and `F (A ×_B C) = F A ×_{F B} F C`;
4. `C` has equalizers and `F` carries the equalizer of `a, b : A ⟶ B` to the equalizer of
   `F a, F b`;
5. `a : A ⟶ B` is a monomorphism iff `F a` is injective;
6. if `F a` is surjective then `a` is an epimorphism (the converse fails, e.g. `ℤ → ℚ` in rings);
7. filtered colimits exist in `C` and are computed on underlying sets.

The definition of tag 007M is `AlgebraicStructureType`, imported from
`StacksFrontier.Topology.Sheaves.AlgebraicStructure.Defs`. It is not restated
here, so that the tag has a single definition.
Items (1)–(4) and (7) come out of instance synthesis from the preservation
hypotheses, with the comparison maps `piComparison`, `pullbackComparison` and
`equalizerComparison` expressing the identifications; item (5) uses faithfulness together with
`Mono ↔ Injective` in `Type v`; item (6) is proved directly from faithfulness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicStructureType

variable (S : AlgebraicStructureType.{v, u})

/--
**Stacks 007O, Item (1).** `C` has a terminal (final) object and the value of `F` at
the terminal object is a one-element (singleton, i.e. `Unique`) set.
-/
@[stacks 007O "(1)"]
theorem has_terminal_and_F_terminal :
    HasTerminal S.C ∧ Nonempty (Unique (S.F.obj (⊤_ S.C))) :=
  ⟨inferInstance,
    ⟨Types.isTerminalEquivUnique _ (IsTerminal.isTerminalObj S.F _ terminalIsTerminal)⟩⟩

/--
**Stacks 007O, Item (2).** `C` has all (small) products, and for every small family
`{A i}` the canonical comparison map `F (∏ A i) ⟶ ∏ (F ∘ A)` is an isomorphism (a
bijection of sets).
-/
@[stacks 007O "(2)"]
theorem has_products_and_F_preserves_products :
    HasProducts.{v} S.C ∧
      ∀ {β : Type v} (f : β → S.C)
        [HasProduct f] [HasProduct fun b => S.F.obj (f b)],
        IsIso (piComparison S.F f) :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/--
**Stacks 007O, Item (3).** `C` has all fibre products (pullbacks), and the canonical
comparison map `F (A ×_B C) ⟶ F A ×_{F B} F C` is an isomorphism (a bijection of sets).
-/
@[stacks 007O "(3)"]
theorem has_pullbacks_and_F_preserves_pullbacks :
    HasPullbacks S.C ∧
      ∀ {X Y Z : S.C} (f : X ⟶ Z) (g : Y ⟶ Z)
        [HasPullback f g] [HasPullback (S.F.map f) (S.F.map g)],
        IsIso (pullbackComparison S.F f g) :=
  ⟨inferInstance, fun _ _ => inferInstance⟩

/--
**Stacks 007O, Item (4).** `C` has all equalizers, and if `e : E ⟶ A` is the
equalizer of `a b : A ⟶ B` in `C`, then `F e` is the equalizer of `F a, F b` in
`Type v` (the canonical comparison map is an isomorphism).
-/
@[stacks 007O "(4)"]
theorem has_equalizers_and_F_preserves_equalizers :
    HasEqualizers S.C ∧
      ∀ {X Y : S.C} (f g : X ⟶ Y)
        [HasEqualizer f g] [HasEqualizer (S.F.map f) (S.F.map g)],
        IsIso (equalizerComparison f g S.F) :=
  ⟨inferInstance, fun _ _ => inferInstance⟩

/--
**Stacks 007O, Item (5).** A morphism `a : A ⟶ B` in `C` is a monomorphism iff
the underlying function `F a : F A ⟶ F B` is injective.

`F` preserves pullbacks and is faithful, so `Mono a ↔ Mono (F.map a)`, and in
`Type v`, `Mono ↔ Injective`.
-/
@[stacks 007O "(5)"]
theorem mono_iff_F_injective {A B : S.C} (a : A ⟶ B) :
    Mono a ↔ Function.Injective (S.F.map a) :=
  (S.F.mono_map_iff_mono a).symm.trans (CategoryTheory.mono_iff_injective (S.F.map a))

/--
**Stacks 007O, Item (6).** If the underlying function `F a : F A ⟶ F B` is
surjective, then `a : A ⟶ B` is an epimorphism in `C`.

Note: this is only a one-way implication; the converse generally fails
(e.g. `ℤ → ℚ` is an epimorphism of rings whose underlying map is not surjective).
-/
@[stacks 007O "(6)"]
theorem epi_of_F_surjective {A B : S.C} (a : A ⟶ B)
    (h : Function.Surjective (S.F.map a)) : Epi a := by
  refine ⟨fun {Z} f g hfg => S.F.map_injective ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := h y
  have hcomp : (S.F.map a ≫ S.F.map f) x = (S.F.map a ≫ S.F.map g) x := by
    rw [← S.F.map_comp, ← S.F.map_comp, hfg]
  simpa using hcomp

/--
**Stacks 007O, Item (7).** For any filtered category `I` and any functor
`D : I ⥤ C`, the colimit of `D` exists in `C`, and the canonical comparison map
`colim (F ∘ D) ⟶ F (colim D)` (induced by the universal property) is an
isomorphism (a bijection of sets).

In particular this applies to sequential colimits along `ℕ`, which is a special
case of a filtered colimit.
-/
@[stacks 007O "(7)"]
theorem has_filtered_colimits_and_F_preserves :
    ∀ {I : Type v} [Category.{v} I] [IsFiltered I] (D : I ⥤ S.C),
      HasColimit D ∧ HasColimit (D ⋙ S.F) ∧
        PreservesColimit D S.F :=
  fun _ => ⟨inferInstance, inferInstance, inferInstance⟩

end AlgebraicStructureType
