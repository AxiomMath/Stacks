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
import StacksCore.Tactic.EgaSgaAttribute
/-!
# Composition of `f`-maps

Suppose `f : X ⟶ Y` and `g : Y ⟶ Z` are continuous maps of topological spaces, `F` a sheaf on
`X`, `G` a sheaf on `Y`, `H` a sheaf on `Z`. Given an `f`-map `φ : G → F` and a `g`-map
`ψ : H → G`, the composition `φ ∘ ψ` is the `(g ∘ f)`-map with components

  `(φ ∘ ψ)_W = φ_{g⁻¹ W} ∘ ψ_W : H(W) ⟶ F(f⁻¹ g⁻¹ W)`.

An `f`-map is a family `φ_V : G(V) ⟶ F(f⁻¹V)` natural in `V`, which is the same datum as a
presheaf morphism `G ⟶ (pushforward f).obj F`; under this identification the composition is
`ψ ≫ (pushforward g).map φ`.

## Main definitions

* `StacksFMap`: an `f`-map `G → F`, a family `φ_V : G(V) ⟶ F(f⁻¹V)` natural in `V`.
* `StacksFMap.equivPresheafHom`, `StacksFMap.equivSheafHom`: `f`-maps `G → F` are the same as
  morphisms `G ⟶ (pushforward f).obj F`.
* `StacksFMap.compPresheaf`: the composition of an `f`-map and a `g`-map of presheaves.
* `fMapComp`: the composition of `f`-maps of sheaves, as morphisms into pushforwards.

## Main results

* `fMapComp_eq_compPresheaf`: the two compositions agree.
* `fMapComp_app`: the components of the composition are `ψ_W ≫ φ_{g⁻¹ W}`.
-/

@[expose] public section

open TopologicalSpace CategoryTheory Opposite

/-! ### `f`-maps -/

/-- An `f`-map from a presheaf `G` on `Y` to a presheaf `F` on `X`: a family
`φ_V : G(V) ⟶ F(f⁻¹ V)` natural in `V`. -/
@[ega "0 3.5.1", sga "4 XVII 0.2.1" "(ii), special case"]
structure StacksFMap {C : Type*} [Category C] {X Y : TopCat} (f : X ⟶ Y)
    (F : TopCat.Presheaf C X) (G : TopCat.Presheaf C Y) where
  /-- Component of the `f`-map on an open `V ⊆ Y`. -/
  app (V : (Opens Y)ᵒᵖ) : G.obj V ⟶ F.obj (op ((Opens.map f).obj V.unop))
  /-- Naturality with respect to restriction. -/
  naturality : ∀ {V W : (Opens Y)ᵒᵖ} (h : V ⟶ W),
    G.map h ≫ app W = app V ≫ F.map ((Opens.map f).op.map h)

namespace StacksFMap

variable {C : Type*} [Category C] {X Y Z : TopCat}

/-- The presheaf morphism `G ⟶ (pushforward f).obj F` of an `f`-map. -/
@[simps]
def toPresheafHom {f : X ⟶ Y}
    {F : TopCat.Presheaf C X} {G : TopCat.Presheaf C Y} (φ : StacksFMap f F G) :
    G ⟶ (TopCat.Presheaf.pushforward C f).obj F where
  app := φ.app
  naturality _ _ h := φ.naturality h

/-- The `f`-map of a presheaf morphism `G ⟶ (pushforward f).obj F`. -/
@[simps]
def ofPresheafHom {f : X ⟶ Y}
    {F : TopCat.Presheaf C X} {G : TopCat.Presheaf C Y}
    (α : G ⟶ (TopCat.Presheaf.pushforward C f).obj F) : StacksFMap f F G where
  app := α.app
  naturality h := α.naturality h

/-- `f`-maps from `G` to `F` are the same as presheaf morphisms `G ⟶ (pushforward f).obj F`. -/
@[simps]
def equivPresheafHom (f : X ⟶ Y) (F : TopCat.Presheaf C X) (G : TopCat.Presheaf C Y) :
    StacksFMap f F G ≃ (G ⟶ (TopCat.Presheaf.pushforward C f).obj F) where
  toFun := toPresheafHom
  invFun := ofPresheafHom
  left_inv _ := rfl
  right_inv _ := rfl

/-- `f`-maps between sheaves `G` and `F` are the same as sheaf morphisms
`G ⟶ (pushforward f).obj F`. -/
@[simps]
def equivSheafHom (f : X ⟶ Y) (F : TopCat.Sheaf C X) (G : TopCat.Sheaf C Y) :
    StacksFMap f F.obj G.obj ≃ (G ⟶ (TopCat.Sheaf.pushforward C f).obj F) where
  toFun φ := ⟨φ.toPresheafHom⟩
  invFun α := ofPresheafHom α.hom
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Composition of `f`-maps -/

/-- The composition of an `f`-map `φ : G → F` and a `g`-map `ψ : H → G` of presheaves: the
`(f ≫ g)`-map with components `ψ_W ≫ φ_{g⁻¹ W}`. -/
@[stacks 008L, ega "0 4.4.2", ega "0 4.4.8" "definition of v''", ega "0 3.5.2"]
def compPresheaf {f : X ⟶ Y} {g : Y ⟶ Z}
    {F : TopCat.Presheaf C X} {G : TopCat.Presheaf C Y} {H : TopCat.Presheaf C Z}
    (φ : StacksFMap f F G) (ψ : StacksFMap g G H) :
    StacksFMap (f ≫ g) F H :=
  ofPresheafHom (ψ.toPresheafHom ≫ (TopCat.Presheaf.pushforward C g).map φ.toPresheafHom)

/-- Component formula: `(φ ∘ ψ)_W = ψ_W ≫ φ_{g⁻¹ W}`. -/
@[simp, ega "0 3.5.2" "partial"]
lemma compPresheaf_app {f : X ⟶ Y} {g : Y ⟶ Z}
    {F : TopCat.Presheaf C X} {G : TopCat.Presheaf C Y} {H : TopCat.Presheaf C Z}
    (φ : StacksFMap f F G) (ψ : StacksFMap g G H) (W : (Opens Z)ᵒᵖ) :
    (φ.compPresheaf ψ).app W
      = ψ.app W ≫ φ.app (op ((Opens.map g).obj W.unop)) := rfl

end StacksFMap

/-! ### Composition of `f`-maps of sheaves -/

/-- The composition of `f`-maps of sheaves, as the morphism `ψ ≫ (pushforward g).map φ`. -/
@[stacks 008L, ega "0 4.4.2", ega "0 4.4.8" "definition of v''", ega "0 3.5.2" "special case"]
noncomputable def fMapComp {C : Type*} [Category C] {X Y Z : TopCat}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : TopCat.Sheaf C X) (G : TopCat.Sheaf C Y) (H : TopCat.Sheaf C Z)
    (φ : G ⟶ (TopCat.Sheaf.pushforward C f).obj F)
    (ψ : H ⟶ (TopCat.Sheaf.pushforward C g).obj G) :
    H ⟶ (TopCat.Sheaf.pushforward C (f ≫ g)).obj F :=
  ψ ≫ (TopCat.Sheaf.pushforward C g).map φ

/-- An `f`-map between sheaves `G` and `F` exists if and only if a sheaf morphism
`G ⟶ (pushforward f).obj F` exists. -/
theorem fMap_iff_sheafHom {C : Type*} [Category C] {X Y : TopCat} (f : X ⟶ Y)
    (F : TopCat.Sheaf C X) (G : TopCat.Sheaf C Y) :
    Nonempty (StacksFMap f F.obj G.obj) ↔
      Nonempty (G ⟶ (TopCat.Sheaf.pushforward C f).obj F) :=
  (StacksFMap.equivSheafHom f F G).nonempty_congr

/-- Under `StacksFMap.equivSheafHom`, `fMapComp` is the composition of `f`-maps. -/
theorem fMapComp_eq_compPresheaf {C : Type*} [Category C] {X Y Z : TopCat}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : TopCat.Sheaf C X) (G : TopCat.Sheaf C Y) (H : TopCat.Sheaf C Z)
    (φS : StacksFMap f F.obj G.obj) (ψS : StacksFMap g G.obj H.obj) :
    fMapComp f g F G H ((StacksFMap.equivSheafHom f F G) φS)
        ((StacksFMap.equivSheafHom g G H) ψS) =
      (StacksFMap.equivSheafHom (f ≫ g) F H) (φS.compPresheaf ψS) :=
  rfl

/-- The component of `fMapComp f g F G H φ ψ` at `W` is `ψ_W ≫ φ_{g⁻¹ W}`. -/
@[ega "0 3.5.2" "special case"]
theorem fMapComp_app {C : Type*} [Category C] {X Y Z : TopCat}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : TopCat.Sheaf C X) (G : TopCat.Sheaf C Y) (H : TopCat.Sheaf C Z)
    (φ : G ⟶ (TopCat.Sheaf.pushforward C f).obj F)
    (ψ : H ⟶ (TopCat.Sheaf.pushforward C g).obj G)
    (W : (Opens Z)ᵒᵖ) :
    (fMapComp f g F G H φ ψ).hom.app W =
      ψ.hom.app W ≫ φ.hom.app (op ((Opens.map g).obj W.unop)) :=
  rfl
