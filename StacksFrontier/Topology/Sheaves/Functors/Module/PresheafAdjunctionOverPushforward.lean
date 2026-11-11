module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Category.TopCat.Opens
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 008V — adjointness of pullback and pushforward for presheaves of modules

Let `f : X ⟶ Y` be a continuous map and `O` a presheaf of rings on `X`, so that `f_*O` is a
presheaf of rings on `Y`. Tag 008V says that the pullback functor
`PMod(f_*O) ⥤ PMod(O)` is left adjoint to the pushforward `PMod(O) ⥤ PMod(f_*O)`, i.e. that
`Mor(f^*G, F) ≃ Mor(G, f_*F)` naturally.

The first part of the file records Mathlib's abstract adjunction
`PresheafOfModules.pullback ⊣ PresheafOfModules.pushforward` along the identity ring morphism
`𝟙 (f_*O)` over `Opens.map f` (`main_adjunction`, `main_hom_equiv`). Mathlib defines that
pullback as the left adjoint of the pushforward, so these say nothing about which presheaf
the left adjoint is.

The Stacks lemma is about the explicit left-hand side `O ⊗_{p, f_p f_*O} f_p G`. It is built in
`StacksFrontier.Topology.Sheaves.Functors.Module.TensorPullbackAdjunction`
(`Stacks.PresheafOfModules.TensorPullback.tensorPullback`), where the natural bijection
`Mor(O ⊗_{p, f_p f_*O} f_p G, F) ≃ Mor(G, f_*F)`
(`Stacks.PresheafOfModules.TensorPullback.tensorPullbackAdjunction`) carries the tag.
-/

@[expose] public section

universe u

open CategoryTheory


-- `reducible` so that `PresheafOfModules.{u} (pushforwardRings f O)` unifies with the
-- shape expected by `PresheafOfModules.pullbackPushforwardAdjunction` in `main_adjunction`.
/-- The pushforward `f_*O` of a presheaf of rings `O` on `X`: the presheaf on `Y` with
`(f_*O)(V) = O(f^{-1}V)`. -/
@[reducible, ega "0 3.4.1" "special case"]
def pushforwardRings {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat.{u}) :
    (TopologicalSpace.Opens Y)ᵒᵖ ⥤ RingCat.{u} :=
  (TopologicalSpace.Opens.map f).op ⋙ O

/-- The pushforward functor `f_* : PMod(O) ⥤ PMod(f_*O)`, restriction of scalars along the
identity `f_*O ⟶ f_*O`. -/
@[ega "0 4.2.1" "more general"]
noncomputable def pushforwardModules008V {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat.{u}) :
    Functor (PresheafOfModules.{u} O) (PresheafOfModules.{u} (pushforwardRings f O)) :=
  PresheafOfModules.pushforward (S := pushforwardRings f O) (𝟙 _)

/-- The pullback functor `f^* : PMod(f_*O) ⥤ PMod(O)`, the base change of a presheaf of
`f_*O`-modules along `Opens.map f` tensored up to `O`. -/
noncomputable def pullbackModules008V {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat.{u}) :
    Functor (PresheafOfModules.{u} (pushforwardRings f O)) (PresheafOfModules.{u} O) :=
  PresheafOfModules.pullback (F := (TopologicalSpace.Opens.map f)) (R := O)
    (S := pushforwardRings f O) (𝟙 _)

/-- The adjunction `f^* ⊣ f_*` between presheaves of `f_*O`-modules and presheaves of
`O`-modules. -/
@[sga "4 IV 13.4" "(13.4.1) for (X", sga "4 Vbis 1.3.6" "adjunction φ* ⊣ φ_*"]
noncomputable def main_adjunction {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat.{u}) :
    pullbackModules008V f O ⊣ pushforwardModules008V f O :=
  PresheafOfModules.pullbackPushforwardAdjunction _

/-- The hom-set bijection `Mor_{PMod(O)}(f^*G, F) ≃ Mor_{PMod(f_*O)}(G, f_*F)` of Mathlib's
adjunction `f^* ⊣ f_*`, where `f^*` is `PresheafOfModules.pullback`, defined as *some* left
adjoint of `f_*`. This does not identify `f^*G` with the explicit `O ⊗_{p, f_p f_*O} f_p G` of
Stacks 008V; that statement is `Stacks.PresheafOfModules.TensorPullback.tensorPullbackAdjunction`
in `StacksFrontier.Topology.Sheaves.Functors.Module.TensorPullbackAdjunction`. -/
@[sga "4 IV 13.4" "special case"]
noncomputable def main_hom_equiv {X Y : TopCat.{u}} (f : X ⟶ Y)
    (O : (TopologicalSpace.Opens X)ᵒᵖ ⥤ RingCat.{u})
    (F : PresheafOfModules.{u} O)
    (G : PresheafOfModules.{u} (pushforwardRings f O)) :
    ((pullbackModules008V f O).obj G ⟶ F) ≃ (G ⟶ (pushforwardModules008V f O).obj F) :=
  (main_adjunction f O).homEquiv G F

