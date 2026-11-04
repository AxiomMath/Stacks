module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Presheaf
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 008U: Adjunction `f_p ⊣ f_*` for presheaves of modules

Let `f : X ⟶ Y` be a continuous map of topological spaces, let `O` be a presheaf of
rings on `Y`, and let `R` be a presheaf of rings on `X` together with a morphism
`φ : O ⟶ (Opens.map f).op ⋙ R` (the morphism `i_O : O ⟶ f_*f_pO` in the Stacks
notation). The Stacks lemma asserts that for `G` a presheaf of `O`-modules on `Y`
and `F` a presheaf of `R`-modules on `X`, there is a natural bijection
`Hom_R(f_p G, F) ≃ Hom_O(G, f_* F)`, i.e. `f_p ⊣ f_*` on presheaves of modules.

In Mathlib this is `PresheafOfModules.pullbackPushforwardAdjunction`, applied with
`F := Opens.map f`; `canonicalAdjunction` is that application at the lemma's own
data `R := f_p O`, `φ := i_O`, and carries the tag. We expose the underlying
TopCat-level adjunction `TopCat.Presheaf.pullbackPushforwardAdjunction` separately,
as it is the presheaves-of-abelian-groups adjunction (Sheaves, Section
`section-abelian-presheaves-functorial`) on which the Stacks proof relies.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace


section TopPresheaf

variable (C : Type u) [Category.{u} C] [Limits.HasColimits C]
variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The underlying presheaf-level adjunction `f_p ⊣ f_*` on presheaves valued in a
cocomplete category `C` (e.g. `Ab`, `RingCat`). For the Stacks lemma, only the
`RingCat`/`Ab` cases are used: the abelian-presheaf adjunction is the one cited in
the Stacks proof, and the ring-presheaf case provides the unit
`i_O : O ⟶ f_* f_p O`. This is a thin wrapper around
`TopCat.Presheaf.pullbackPushforwardAdjunction`. -/
noncomputable def topPresheafAdjunction :
    TopCat.Presheaf.pullback C f ⊣ TopCat.Presheaf.pushforward C f :=
  TopCat.Presheaf.pullbackPushforwardAdjunction C f

/-- Nonempty wrapper for the underlying TopCat presheaf adjunction. This is the
literal statement that the Crux proof produces. -/
theorem topPresheafAdjunction_nonempty :
    Nonempty (TopCat.Presheaf.pullback C f ⊣ TopCat.Presheaf.pushforward C f) :=
  ⟨topPresheafAdjunction C f⟩

end TopPresheaf

section ModuleAdjunction

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable (O : (Opens Y)ᵒᵖ ⥤ RingCat.{u}) (R : (Opens X)ᵒᵖ ⥤ RingCat.{u})
variable (φ : O ⟶ (Opens.map f).op ⋙ R)

/-- The pushforward functor on presheaves of modules induced by a continuous map
`f : X ⟶ Y` together with a morphism `φ : O ⟶ f_* R` of presheaves of rings.
On underlying presheaves of abelian groups this is precomposition with
`(Opens.map f).op`, matching `TopCat.Presheaf.pushforward Ab f`. -/
@[ega "0 4.2.1" "more general"]
noncomputable def pushforwardModules :
    PresheafOfModules.{u} R ⥤ PresheafOfModules.{u} O :=
  PresheafOfModules.pushforward (F := Opens.map f) φ

/-- The pullback (= inverse image) functor on presheaves of modules induced by
a continuous map `f : X ⟶ Y` together with a morphism `φ : O ⟶ f_* R` of
presheaves of rings. -/
@[sga "4 Vbis 1.3.6" "special case"]
noncomputable def pullbackModules :
    PresheafOfModules.{u} O ⥤ PresheafOfModules.{u} R :=
  PresheafOfModules.pullback (F := Opens.map f) φ

end ModuleAdjunction

section CanonicalCase

/-! The canonical Stacks 008U setup: take `R := f_p O := ((Opens.map f).op).lan.obj O`,
the left Kan extension of `O` along `(Opens.map f).op`, and `φ := i_O`, the unit of
the rings-level adjunction at `O`. With these choices the adjunction
`pullbackModules f O R φ ⊣ pushforwardModules f O R φ` is exactly the adjunction
of Stacks 008U as stated. -/

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (O : Y.Presheaf RingCat.{u})

/-- The pullback of `O` to `X` as a presheaf of rings, i.e. `f_p O`. -/
noncomputable def f_pRings : X.Presheaf RingCat.{u} :=
  (TopCat.Presheaf.pullback RingCat.{u} f).obj O

/-- The canonical map `i_O : O ⟶ f_* f_p O` of presheaves of rings on `Y`, i.e. the
unit of the pullback/pushforward adjunction on presheaves of rings, evaluated at
`O`. -/
noncomputable def iRings : O ⟶ (Opens.map f).op ⋙ f_pRings f O :=
  (TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app O

/-- **Stacks 008U.** Let `f : X ⟶ Y` be a continuous map of topological spaces and let
`O` be a presheaf of rings on `Y`. Then the pullback `f_p` of presheaves of modules,
from presheaves of `O`-modules on `Y` to presheaves of `f_p O`-modules on `X`, is left
adjoint to the pushforward `f_*`; in particular the hom-sets
`Hom_{f_p O}(f_p G, F)` and `Hom_O(G, f_* F)` are naturally bijective, which is the
bijection the lemma states.

This is Mathlib's `PresheafOfModules.pullbackPushforwardAdjunction` at `F := Opens.map f`
and at the lemma's own data `R := f_p O`, `φ := i_O` (the unit of the rings-level
pullback/pushforward adjunction). -/
@[stacks 008U, sga "4 IV 13.4" "special case"]
noncomputable def canonicalAdjunction :
    pullbackModules f O (f_pRings f O) (iRings f O) ⊣
      pushforwardModules f O (f_pRings f O) (iRings f O) :=
  PresheafOfModules.pullbackPushforwardAdjunction (F := Opens.map f) (iRings f O)

end CanonicalCase
