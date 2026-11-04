module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Functors
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
public import Mathlib.Topology.Sheaves.Forget
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 008Q: f-maps of sheaves of algebraic structures

Let `U : C ⥤ Type w` be a faithful, isomorphism-reflecting, limit-preserving functor from a
complete category `C`. Then `U` extends pointwise to sheaves on a topological space, and given an
f-map `φ` between the underlying sheaves of sets whose components all lift along `U`, there is a
unique f-map of sheaves of algebraic structures with underlying f-map `φ`.

## Main definitions

* `IsCategoryOfAlgebraicStructures`: A faithful, isomorphism-reflecting, limit-preserving functor
  `U : C ⥤ Type w` from a complete category `C`.
* `underlyingSheaf`: The sheaf of sets `F ⋙ U` underlying a sheaf `F` with values in `C`.
* `underlyingSheafMap`: The morphism of underlying sheaves of sets induced by a morphism of
  sheaves with values in `C`.

## Main results

* `main_theorem008Q`: An f-map of underlying sheaves of sets whose components all lift along `U`
  is the underlying f-map of a unique f-map of sheaves with values in `C`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

universe u w

/-- Data of a category of algebraic structures (Stacks 007L): a faithful, limit-preserving,
isomorphism-reflecting functor `U` from a complete category `C` to `Type`. -/
class IsCategoryOfAlgebraicStructures
    {C : Type u} [Category.{w} C] (U : C ⥤ Type w) : Prop where
  /-- The functor `U` is faithful. -/
  faithful : U.Faithful
  /-- The functor `U` reflects isomorphisms. -/
  reflectsIsos : U.ReflectsIsomorphisms
  /-- The category `C` has all limits. -/
  hasLimits : HasLimits C
  /-- The functor `U` preserves all limits. -/
  preservesLimits : PreservesLimits U

/-- The underlying sheaf of sets: post-compose with the forgetful functor `U`. -/
@[ega "0 3.1.3" "(E), special case",
  sga "4 II 6.2" "special case",
  sga "4 II 6.3.0" "object assignment of ε~"]
noncomputable def underlyingSheaf
    {C : Type u} [Category.{w} C] (U : C ⥤ Type w)
    [U.ReflectsIsomorphisms] [HasLimits C] [PreservesLimits U]
    {X : TopCat} (F : TopCat.Sheaf C X) : TopCat.Sheaf (Type w) X :=
  ⟨F.obj ⋙ U, (TopCat.Presheaf.isSheaf_iff_isSheaf_comp U F.obj).mp F.property⟩

/-- The underlying sheaf-of-sets morphism: whisker-right with `U`. -/
@[sga "4 II 6.3.0" "special case"]
noncomputable def underlyingSheafMap
    {C : Type u} [Category.{w} C] (U : C ⥤ Type w)
    [U.ReflectsIsomorphisms] [HasLimits C] [PreservesLimits U]
    {X : TopCat} {F G : TopCat.Sheaf C X} (ψ : F ⟶ G) :
    underlyingSheaf U F ⟶ underlyingSheaf U G :=
  ObjectProperty.homMk (Functor.whiskerRight ψ.hom U)

-- Works around the stricter isDefEq transparency change in the Lean bump, which
-- otherwise prevents `Functor.map_comp` from matching under the sheaf wrappers.
set_option backward.isDefEq.respectTransparency.types false in
/-- **Stacks 008Q.** Given an f-map `φ` of underlying sheaves of sets whose components all lift
along `U`, there exists a unique f-map of sheaves of algebraic structures with underlying
f-map `φ`. -/
@[stacks 008Q]
theorem main_theorem008Q
    {C : Type u} [Category.{w} C]
    (U : C ⥤ Type w) [U.Faithful] [U.ReflectsIsomorphisms]
    [HasLimits C] [PreservesLimits U]
    {X Y : TopCat} (f : X ⟶ Y)
    (F : TopCat.Sheaf C X) (G : TopCat.Sheaf C Y)
    (φ : underlyingSheaf U G ⟶
          (TopCat.Sheaf.pushforward (Type w) f).obj (underlyingSheaf U F))
    (hφ : ∀ (V : (Opens Y)ᵒᵖ),
            ∃ ψV : G.obj.obj V ⟶ F.obj.obj ((Opens.map f).op.obj V),
              U.map ψV = φ.hom.app V) :
    ∃! ψ : G ⟶ (TopCat.Sheaf.pushforward C f).obj F,
      underlyingSheafMap U ψ = φ := by
  choose ψV hψV using hφ
  refine ⟨ObjectProperty.homMk
      { app := ψV
        naturality := fun X' Y' g => U.map_injective <| by
          have hnat := φ.hom.naturality g
          change U.map (G.obj.map g) ≫ φ.hom.app Y' =
            φ.hom.app X' ≫ U.map (((TopCat.Sheaf.pushforward C f).obj F).obj.map g) at hnat
          rw [← hψV X', ← hψV Y'] at hnat
          rwa [Functor.map_comp, Functor.map_comp] },
    Sheaf.hom_ext (NatTrans.ext (funext hψV)), fun ψ' hψ' => ?_⟩
  exact Sheaf.hom_ext <| NatTrans.ext <| funext fun V => U.map_injective <|
    (congrArg (·.hom.app V) hψ').trans (hψV V).symm
