module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Category.Grp.Colimits
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
public import Mathlib.Order.CompletePartialOrder
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
# `u_p` on abelian presheaves does not compute `u_p` on sets

Stacks tag 00YU (Remark 7.44.4).  For a functor `u : C ⥤ D`, the left adjoint `u_p` of the
precomposition functor `u^p` is the left Kan extension along `uᵒᵖ`, computed pointwise as a
colimit over the comma category `CostructuredArrow uᵒᵖ V` (the opposite of the Stacks index
category `I^u_V`); the abelian version `u_p^{ab}` is the same colimit taken in `Ab`.  The
forgetful functor `Ab → Set` induces a comparison map
`θ_F : u_p (F^set) ⟶ forget ∘ (u_p^{ab} F)`, and the two constructions *agree* when every
`θ_{F,V}` is bijective.  Agreement fails already for `C` empty and `D = PUnit`, where the
index category is empty, so `(u_p F^set)(V)` is empty while `(u_p^{ab} F)(V)` contains `0`.
Only the bare functor `u` enters, no Grothendieck topology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-- If the comma (index) category `CostructuredArrow u'.op V` is empty, then the
value at `V` of the left Kan extension along `u'.op` of a `Type`-valued presheaf
is itself empty: the defining colimit is taken over an empty diagram, hence its
cocone point is the initial (empty) type. -/
theorem isEmpty_lan_obj {C D : Type} [SmallCategory C] [SmallCategory D]
    (u' : C ⥤ D) (G : Cᵒᵖ ⥤ Type) (V : Dᵒᵖ)
    [IsEmpty (CostructuredArrow u'.op V)] :
    IsEmpty ((u'.op.lan.obj G).obj V) := by
  have hpw := (u'.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit G) V
  refine ⟨fun x => ?_⟩
  let c : Cocone (CostructuredArrow.proj u'.op V ⋙ G) :=
    { pt := PEmpty.{1}
      ι := { app := fun j => isEmptyElim j, naturality := fun {j} => isEmptyElim j } }
  exact (hpw.desc c x).elim

universe u

namespace Stacks.Presheaf.AbelianVersusSets

variable {C D : Type u} [Category.{u} C] [Category.{u} D]

/-- The index category of the pointwise left Kan extension along `uᵒᵖ : Cᵒᵖ ⥤ Dᵒᵖ` at
`V : Dᵒᵖ`: the comma category `CostructuredArrow uᵒᵖ V`, whose objects are pairs
`(U, φ : uᵒᵖ(U) → V)` and whose morphisms are arrows over `V`. It is the opposite of the
category `I^u_V` of pairs `(U, φ : V → u(U))`. -/
abbrev indexCategory (u' : C ⥤ D) (V : Dᵒᵖ) : Type u :=
  CostructuredArrow u'.op V

/-- **Definition 5 (underlying presheaf of sets).** Postcomposition with the
forgetful functor `Ab → Set` turns an abelian presheaf into a presheaf of sets,
`F^set = forget ∘ F`. -/
@[sga "4 I 5.8.0" "special case"]
noncomputable def underlyingSet :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{u} (Type u)).obj (forget AddCommGrpCat)

/-- **Definition 2 (the functor `u^p`) on presheaves of sets.** Precomposition
with `uᵒᵖ`, i.e. `(u^p G)(U) = G(u U)`. -/
noncomputable def uPullbackSet (u' : C ⥤ D) :
    (Dᵒᵖ ⥤ Type u) ⥤ (Cᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type u)).obj u'.op

/-- **Definition 2 (the functor `u^p`) on presheaves of abelian groups.** -/
noncomputable def uPullbackAb (u' : C ⥤ D) :
    (Dᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj u'.op

/-- **Definition 3 (the functor `u_p` on presheaves of sets).** The left adjoint
of `u^p`, equivalently the left Kan extension along `uᵒᵖ`. Its pointwise value
`(u_p F)(V) = colim_{(I^u_V)ᵒᵖ} F_V` is the colimit (in `Set`) over the index
category recorded above. -/
@[sga "4 I 8.6.2", sga "4 IV 4.6.1"]
noncomputable def uShriekSet (u' : C ⥤ D) :
    (Cᵒᵖ ⥤ Type u) ⥤ (Dᵒᵖ ⥤ Type u) :=
  u'.op.lan

/-- **Definition 4 (the functor `u_p^{ab}` on presheaves of abelian groups).**
The left adjoint of `u^p` on abelian presheaves, equivalently the left Kan
extension along `uᵒᵖ`; its pointwise value is the *same* colimit diagram, now
taken in `Ab`. -/
noncomputable def uShriekAb (u' : C ⥤ D) :
    (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Dᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  u'.op.lan

/-- Adjointness `u_p ⊣ u^p` on presheaves of sets (Stacks Lemma 00VE). -/
noncomputable def uShriekSetAdjunction (u' : C ⥤ D) :
    uShriekSet u' ⊣ uPullbackSet u' :=
  u'.op.lanAdjunction (Type u)

/-- Adjointness `u_p^{ab} ⊣ u^p` on presheaves of abelian groups (Stacks
Remark 00VF). -/
noncomputable def uShriekAbAdjunction (u' : C ⥤ D) :
    uShriekAb u' ⊣ uPullbackAb u' :=
  u'.op.lanAdjunction AddCommGrpCat.{u}

/-- **Definition 5 (the comparison map `θ`).** For a presheaf of abelian groups
`F`, both `u_p (F^set)` and `forget ∘ (u_p^{ab} F)` are extensions of `F^set`
along `uᵒᵖ`. Since `u_p (F^set)` is the (universal) left Kan extension, the
universal property produces the canonical comparison morphism of presheaves of
sets `θ_F : u_p (F^set) ⟶ forget ∘ (u_p^{ab} F)`. -/
noncomputable def theta (u' : C ⥤ D) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (uShriekSet u').obj ((underlyingSet).obj F) ⟶
      (uShriekAb u').obj F ⋙ forget AddCommGrpCat :=
  Functor.descOfIsLeftKanExtension
    (u'.op.leftKanExtension (F ⋙ forget AddCommGrpCat))
    (u'.op.leftKanExtensionUnit (F ⋙ forget AddCommGrpCat))
    ((u'.op.leftKanExtension F) ⋙ forget AddCommGrpCat)
    (Functor.whiskerRight (u'.op.leftKanExtensionUnit F) (forget AddCommGrpCat))

/-- `u_p^{ab}` **agrees with** `u_p` on underlying presheaves of sets if the
comparison map `θ_{F,V}` is a bijection for every abelian presheaf `F` on `C`
and every object `V` of `D`. -/
def Agrees (u' : C ⥤ D) : Prop :=
  ∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (V : Dᵒᵖ), Function.Bijective ((theta u' F).app V)

/-- **Main Statement (Tag 00YU).** Agreement does not hold in general: there
exist categories `C`, `D`, a functor `u : C ⥤ D`, a presheaf of abelian groups
`F` on `C`, and an object `V` of `D` such that the comparison map `θ_{F,V}` is
*not* a bijection. -/
@[stacks 00YU]
theorem not_universally_agrees :
    ∃ (C D : Type) (_ : SmallCategory C) (_ : SmallCategory D) (u' : C ⥤ D)
      (F : Cᵒᵖ ⥤ AddCommGrpCat.{0}) (V : Dᵒᵖ),
      ¬ Function.Bijective ((theta u' F).app V) := by
  refine ⟨Discrete PEmpty.{1}, PUnit.{1}, inferInstance, inferInstance,
    Functor.empty _,
    { obj := fun X => X.unop.as.elim
      map := fun {X} => X.unop.as.elim
      map_id := fun X => X.unop.as.elim
      map_comp := fun {X} => X.unop.as.elim },
    Opposite.op PUnit.unit, ?_⟩
  intro h
  have hsurj := h.2
  rw [Function.Surjective] at hsurj
  -- target is nonempty: take 0 in the abelian group
  set G := (uShriekAb (Functor.empty PUnit.{1})).obj
    { obj := fun X => (Opposite.unop X).as.elim, map := fun {X Y} => (Opposite.unop X).as.elim,
      map_id := fun X => (Opposite.unop X).as.elim,
      map_comp := fun {X Y Z} => (Opposite.unop X).as.elim } with hG
  obtain ⟨a, ha⟩ := hsurj (0 : G.obj (Opposite.op PUnit.unit))
  -- source must be empty since the index category is empty
  have : IsEmpty (CostructuredArrow (Functor.empty PUnit.{1}).op (Opposite.op PUnit.unit)) :=
    ⟨fun j => j.left.unop.as.elim⟩
  have := isEmpty_lan_obj (Functor.empty PUnit.{1})
    ((underlyingSet).obj
      { obj := fun X => (Opposite.unop X).as.elim, map := fun {X Y} => (Opposite.unop X).as.elim,
        map_id := fun X => (Opposite.unop X).as.elim,
        map_comp := fun {X Y Z} => (Opposite.unop X).as.elim })
    (Opposite.op PUnit.unit)
  rw [uShriekSet] at a
  exact (isEmptyElim a)

end Stacks.Presheaf.AbelianVersusSets
