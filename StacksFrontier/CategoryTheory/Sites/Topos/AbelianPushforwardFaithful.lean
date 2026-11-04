module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Sites.Abelian





import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.EffectiveEpi.Comp

public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-
# Problem Description

This is Stacks project Tag 04DA (Lemma 18.15.1, "Exactness of pushforward").

Let `f : Sh(C) → Sh(D)` be a morphism of topoi, with pushforward
`f_* : Sh(C) → Sh(D)` and pullback `f^{-1} : Sh(D) → Sh(C)`, where `f^{-1}`
is the left adjoint to `f_*` and `f^{-1}` is exact (in particular it
preserves epimorphisms / surjections). The same functors induce an adjoint
pair of additive functors on abelian sheaves
`f_* : Ab(C) → Ab(D)` and `f^{-1} : Ab(D) → Ab(C)` with `f^{-1}` exact.

For an abelian sheaf `F` on `C`, the counit
`ε_F : f^{-1} f_* F → F` is the morphism corresponding to the identity of
`f_* F` under the adjunction.

Statement 1 (Equivalence). The following are equivalent:
1. For all `F` in `Ab(C)`, the counit `ε_F : f^{-1} f_* F → F` is surjective
   (an epimorphism) in `Ab(C)`.
2. The functor `f_* : Ab(C) → Ab(D)` reflects surjections: whenever
   `f_* a` is surjective, `a` is surjective.

Statement 2 (Faithfulness). If conditions (1) and (2) of Statement 1 hold,
then `f_* : Ab(C) → Ab(D)` is faithful.

In an abelian category, "surjective morphism" means "epimorphism".
-/

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

noncomputable section

-- Background:
-- `C` and `D` are sites, given by categories equipped with Grothendieck topologies.
variable {C : Type u₁} [Category.{v₁} C] (JC : GrothendieckTopology C)
variable {D : Type u₂} [Category.{v₂} D] (JD : GrothendieckTopology D)

-- Main Definition(s)

/-- The category `Ab(C)` of abelian sheaves on a site `(C, J)`: sheaves valued
in the category of abelian groups. This is an abelian category. -/
@[sga "4 II 6.1" "special case",
  sga "4 II 6.3.3",
  sga "4 IV 11.1.2" "special case",
  sga "4 IV 11.1.5",
  sga "4 VII 1.3",
  sga "4 VIII 6.5",
  sga "4 Vbis 4.1.0" "partial",
  sga "4½ Arcata 1.6.3",
  sga "4½ Arcata 4.3"]
abbrev AbSh {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) :
    Type _ :=
  Sheaf J (AddCommGrpCat.{max u₁ v₁})

-- `AbSh J` is an abelian category (Definition 3 refers to surjections /
-- epimorphisms in this abelian category).
example : Abelian (AbSh JC) := by infer_instance

/-- **Definition 1 (Morphism of topoi), restricted to abelian sheaves.**

The data of a morphism of topoi `f : Sh(C) → Sh(D)` induces, on abelian
sheaves, a pushforward functor `pushforward : Ab(C) → Ab(D)`, a pullback
functor `pullback : Ab(D) → Ab(C)`, an adjunction `pullback ⊣ pushforward`
(condition 1: `f^{-1}` is left adjoint to `f_*`), together with exactness of
`f^{-1}` (condition 2). We record the only consequence of exactness used
below, namely that `pullback` preserves epimorphisms (surjections). -/
structure MorphismOfTopoiAb
    {C : Type u₁} [Category.{v₁} C] (JC : GrothendieckTopology C)
    {D : Type u₂} [Category.{v₂} D] (JD : GrothendieckTopology D) where
  /-- The pushforward `f_* : Ab(C) → Ab(D)`. -/
  pushforward : AbSh JC ⥤ AbSh JD
  /-- The pullback `f^{-1} : Ab(D) → Ab(C)`. -/
  pullback : AbSh JD ⥤ AbSh JC
  /-- Condition 1: `f^{-1}` is left adjoint to `f_*`. -/
  adj : pullback ⊣ pushforward
  /-- Condition 2 (the relevant consequence): `f^{-1}` is exact, hence in
  particular preserves epimorphisms (surjections of abelian sheaves). -/
  pullback_preserves_epi : pullback.PreservesEpimorphisms

namespace MorphismOfTopoiAb

variable {JC JD}
variable (f : MorphismOfTopoiAb JC JD)

/-- **Definition 2 (Counit).** For an abelian sheaf `F` on `C`, the counit
`ε_F : f^{-1} f_* F → F` is the component at `F` of the counit of the
adjunction `f^{-1} ⊣ f_*` (corresponding to the identity of `f_* F`). -/
abbrev counit (F : AbSh JC) :
    f.pullback.obj (f.pushforward.obj F) ⟶ F :=
  f.adj.counit.app F

/-- **Definition 4 (Reflecting surjections).** `f_*` reflects surjections if
whenever `f_* a` is an epimorphism (surjective), so is `a`. -/
def ReflectsSurjections : Prop :=
  ∀ ⦃F F' : AbSh JC⦄ (a : F ⟶ F'), Epi (f.pushforward.map a) → Epi a

/-- **Definition 5 (Faithful functor).** `f_*` is faithful if the induced map
on hom-groups `a ↦ f_* a` is injective. -/
def IsFaithful : Prop := f.pushforward.Faithful

end MorphismOfTopoiAb

-- Main Statement(s)

open MorphismOfTopoiAb

/-- **Statement 1 (Equivalence).** Let `f : Sh(C) → Sh(D)` be a morphism of
topoi. The following are equivalent:
1. For all `F` in `Ab(C)`, the counit `ε_F : f^{-1} f_* F → F` is surjective
   (an epimorphism) in `Ab(C)`.
2. The functor `f_* : Ab(C) → Ab(D)` reflects surjections. -/
@[stacks 04DA]
theorem main_statement_equivalence (f : MorphismOfTopoiAb JC JD) :
    (∀ F : AbSh JC, Epi (f.counit F)) ↔ f.ReflectsSurjections := by
  refine ⟨fun hcounit F F' a ha ↦ ?_,
    fun hrefl F ↦ hrefl _ (SplitEpi.epi ⟨_, f.adj.right_triangle_components F⟩)⟩
  have : Epi (f.pullback.map (f.pushforward.map a)) := f.pullback_preserves_epi.preserves _
  have := hcounit F'
  have : Epi (f.pullback.map (f.pushforward.map a) ≫ f.counit F') := epi_comp _ _
  rw [f.adj.counit_naturality a] at this
  exact epi_of_epi (f.counit F) a

/-- **Statement 2 (Faithfulness).** If the equivalent conditions of Statement 1
hold (we phrase the hypothesis via condition (1): the counit is surjective for
every abelian sheaf `F`), then `f_* : Ab(C) → Ab(D)` is faithful. -/
@[stacks 04DA]
theorem main_statement_faithful (f : MorphismOfTopoiAb JC JD)
    (h : ∀ F : AbSh JC, Epi (f.counit F)) : f.IsFaithful := by
  refine ⟨fun {X Y} g g' hgg' ↦ ?_⟩
  have := h X
  refine (cancel_epi (f.counit X)).1 ?_
  rw [← f.adj.counit_naturality g, ← f.adj.counit_naturality g', hgg']

end
