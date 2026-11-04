module

import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.Functor.Derived.Morphisms
public import StacksFrontier.CategoryTheory.Localization.Saturated.Closure
public import StacksFrontier.CategoryTheory.Functor.Derived.Shift.Situation
import all StacksFrontier.CategoryTheory.Functor.Derived.Shift.Situation
public import StacksFrontier.CategoryTheory.Localization.Saturated.Defs
import StacksCore.Tactic.EgaSgaAttribute


/-!
# Derived functors and shifts: computing objects

An object `X` computes `RF` (resp. `LF`) if and only if `X⟦n⟧` does ([Stacks, Tag 05SY]).

## References

* [Stacks, Tag 05SY](https://stacks.math.columbia.edu/tag/05SY)
-/

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v v' u u'

namespace Stacks.DerivedFunctor.Shift

namespace Situation

variable (sit : Situation)

/-! ## The shift equivalence on fraction categories and the diagram comparison

These lemmas package facts (i) and (ii) of the source: the shift induces an
equivalence on the fraction categories (using `S.IsCompatibleWithShift ℤ`), and `F`
commuting with shifts (`F.CommShift ℤ`) identifies the shifted diagram. -/

section ShiftEquiv

variable (X : sit.D) (n : ℤ)

/-- The base equivalence `StructuredArrow X (𝟭 D) ≌ StructuredArrow (X⟦n⟧) (𝟭 D)`
induced by the auto-equivalence `shiftFunctor D n`, via `StructuredArrow.map₂`.
On objects it sends `(s : X ⟶ X')` to `(s⟦n⟧ : X⟦n⟧ ⟶ X'⟦n⟧)`. -/
noncomputable def rightShiftBaseEquiv :
    StructuredArrow X (𝟭 sit.D) ≌ StructuredArrow (X⟦n⟧) (𝟭 sit.D) :=
  haveI : IsIso ((Functor.leftUnitor (shiftFunctor sit.D n)).hom ≫
      (Functor.rightUnitor (shiftFunctor sit.D n)).inv) := by infer_instance
  (StructuredArrow.map₂ (F := shiftFunctor sit.D n) (G := shiftFunctor sit.D n)
    (𝟙 (X⟦n⟧)) ((Functor.leftUnitor (shiftFunctor sit.D n)).hom ≫
      (Functor.rightUnitor (shiftFunctor sit.D n)).inv)).asEquivalence

/-- The hom of the base-equivalence image of `A` is the shift of `A.hom`. -/
lemma rightShiftBaseEquiv_functor_obj_hom (A : StructuredArrow X (𝟭 sit.D)) :
    ((sit.rightShiftBaseEquiv X n).functor.obj A).hom = (shiftFunctor sit.D n).map A.hom := by
  simp [rightShiftBaseEquiv, StructuredArrow.map₂]

/-- The right component of the base-equivalence image of a morphism is its shift. -/
lemma rightShiftBaseEquiv_functor_map_right {A B : StructuredArrow X (𝟭 sit.D)} (f : A ⟶ B) :
    ((sit.rightShiftBaseEquiv X n).functor.map f).right = (shiftFunctor sit.D n).map f.right := by
  simp [rightShiftBaseEquiv, StructuredArrow.map₂]

/-- Shifting restricts to an equivalence between the right-fraction index categories. -/
noncomputable def rightShiftEquiv : sit.RightFractions X ≌ sit.RightFractions (X⟦n⟧) := by
  -- Restrict `rightShiftBaseEquiv` to the `S`-full subcategories.
  -- Forward membership: `s ∈ S → s⟦n⟧ ∈ S` via `IsCompatibleWithShift.iff`.
  have hPQ : ∀ c : StructuredArrow X (𝟭 sit.D), sit.rightFractionProp X c →
      sit.rightFractionProp (X⟦n⟧) ((sit.rightShiftBaseEquiv X n).functor.obj c) := by
    intro c hc
    change sit.S _
    rw [sit.rightShiftBaseEquiv_functor_obj_hom]
    exact (MorphismProperty.IsCompatibleWithShift.iff sit.S c.hom n).mpr hc
  -- Backward membership: use the counit iso + saturation to cancel the iso.
  have hQP : ∀ B : StructuredArrow (X⟦n⟧) (𝟭 sit.D), sit.rightFractionProp (X⟦n⟧) B →
      sit.rightFractionProp X ((sit.rightShiftBaseEquiv X n).inverse.obj B) := by
    intro B hB
    change sit.S _
    set e := sit.rightShiftBaseEquiv X n with he
    -- counit: e.functor.obj (e.inverse.obj B) ≅ B
    have hcomm : ((e.functor.obj (e.inverse.obj B)).hom) ≫ (e.counitIso.app B).hom.right
        = B.hom := StructuredArrow.w (e.counitIso.app B).hom
    rw [sit.rightShiftBaseEquiv_functor_obj_hom] at hcomm
    -- The right component of the counit iso is an iso.
    have : IsIso ((e.counitIso.app B).hom.right) := by
      have : IsIso (e.counitIso.app B).hom := inferInstance
      exact (StructuredArrow.proj (X⟦n⟧) (𝟭 sit.D)).map_isIso (e.counitIso.app B).hom
    -- So `(shift n).map (inverse B).hom = B.hom ≫ inv` ∈ S, hence by iff `(inverse B).hom ∈ S`.
    have hSshift : sit.S ((shiftFunctor sit.D n).map ((e.inverse.obj B).hom)) := by
      have heq : (shiftFunctor sit.D n).map ((e.inverse.obj B).hom)
          = B.hom ≫ CategoryTheory.inv ((e.counitIso.app B).hom.right) := by
        rw [← hcomm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [heq]
      -- isos lie in the saturated `S`: prove `S (inv θ)` via `mem_of_comp_mem_comp`.
      have hinv : sit.S (CategoryTheory.inv ((e.counitIso.app B).hom.right)) := by
        refine sit.saturatedS.mem_of_comp_mem_comp
          ((e.counitIso.app B).hom.right) (CategoryTheory.inv ((e.counitIso.app B).hom.right))
          ((e.counitIso.app B).hom.right) ?_ ?_
        · rw [IsIso.hom_inv_id]; exact sit.S.id_mem _
        · rw [IsIso.inv_hom_id]; exact sit.S.id_mem _
      exact sit.S.comp_mem _ _ hB hinv
    exact (MorphismProperty.IsCompatibleWithShift.iff sit.S ((e.inverse.obj B).hom) n).mp hSshift
  exact
    { functor := (sit.rightFractionProp (X⟦n⟧)).lift
        ((sit.rightFractionProp X).ι ⋙ (sit.rightShiftBaseEquiv X n).functor)
        (fun A => hPQ A.1 A.2)
      inverse := (sit.rightFractionProp X).lift
        ((sit.rightFractionProp (X⟦n⟧)).ι ⋙ (sit.rightShiftBaseEquiv X n).inverse)
        (fun A => hQP A.1 A.2)
      unitIso := NatIso.ofComponents
        (fun A => ((sit.rightFractionProp X).fullyFaithfulι).preimageIso
          ((sit.rightShiftBaseEquiv X n).unitIso.app A.1))
        (by intro A B f; apply (sit.rightFractionProp X).ι.map_injective
            simp [ObjectProperty.fullyFaithfulι])
      counitIso := NatIso.ofComponents
        (fun A => ((sit.rightFractionProp (X⟦n⟧)).fullyFaithfulι).preimageIso
          ((sit.rightShiftBaseEquiv X n).counitIso.app A.1))
        (by intro A B f; apply (sit.rightFractionProp (X⟦n⟧)).ι.map_injective
            simp [ObjectProperty.fullyFaithfulι])
      functor_unitIso_comp := by
        intro A
        apply (sit.rightFractionProp (X⟦n⟧)).ι.map_injective
        simp [ObjectProperty.fullyFaithfulι] }

/-- **The shift diagram comparison (right).** Under the equivalence `rightShiftEquiv`,
the shifted ind-diagram `rightDiagram (X⟦n⟧)` is naturally isomorphic to the original
ind-diagram `rightDiagram X` reindexed by `(rightShiftEquiv).inverse` and postcomposed
with the target shift `shiftFunctor D' n`.

This is fact (ii): on objects, `rightDiagram (X⟦n⟧)` at `(s⟦n⟧ : X⟦n⟧ ⟶ X'⟦n⟧)` is
`F(X'⟦n⟧)`, and `F.commShiftIso n` gives `F(X'⟦n⟧) ≅ F(X')⟦n⟧ = (shiftFunctor D' n).obj (F X')`,
naturally in `X'`. Assemble these componentwise isos into a natural iso of functors using
`F.commShiftIso n` and naturality (`Functor.commShiftIso_hom_naturality`). -/
noncomputable def rightDiagramShiftIso :
    sit.rightDiagram (X⟦n⟧) ≅
      (sit.rightShiftEquiv X n).inverse ⋙ sit.rightDiagram X ⋙ shiftFunctor sit.D' n := by
  refine NatIso.ofComponents
    (fun A =>
      have objYiso : ((sit.rightShiftEquiv X n).inverse.obj A).1.right ⟦n⟧ ≅ A.1.right :=
        (StructuredArrow.proj _ _).mapIso ((sit.rightShiftBaseEquiv X n).counitIso.app A.1)
          ≪≫ Iso.refl _
      (sit.F.mapIso objYiso).symm ≪≫ (sit.F.commShiftIso n).app _)
    ?_
  intro A B f
  -- Notation for the base counit.
  set e := sit.rightShiftBaseEquiv X n with he
  -- The component isos unfold to F.map of the counit's right component.
  -- Reduce to a statement after the common `commShiftIso` factor.
  dsimp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.trans_inv, Iso.refl_inv, Functor.mapIso_hom, Iso.refl_hom]
  -- abbreviations
  set PA := ((sit.rightShiftEquiv X n).inverse.obj A).obj.right with hPA
  set PB := ((sit.rightShiftEquiv X n).inverse.obj B).obj.right with hPB
  -- The right component of `e.inverse.map f.hom` is the underlying map between PA, PB.
  set g : PA ⟶ PB := (e.inverse.map f.hom).right with hg
  -- Rewrite the structured-arrow / fraction functorialities.
  rw [StructuredArrow.proj_map, StructuredArrow.proj_map]
  -- `rightDiagram` and reindexing as `F.map` of the right components.
  change sit.F.map f.hom.right ≫ (sit.F.map (𝟙 _ ≫ (e.counitIso.app B.obj).inv.right)
        ≫ (sit.F.commShiftIso n).hom.app PB)
      = (sit.F.map (𝟙 _ ≫ (e.counitIso.app A.obj).inv.right)
          ≫ (sit.F.commShiftIso n).hom.app PA)
        ≫ (shiftFunctor sit.D' n).map (sit.F.map g)
  simp only [Category.id_comp]
  -- use commShiftIso naturality to move the shift past F on the RHS
  rw [Category.assoc, ← Functor.commShiftIso_hom_naturality sit.F g n]
  -- now reduce to the D-level naturality of the base counit (inverse direction)
  have hfun : (e.functor.map (e.inverse.map f.hom)).right
      = (shiftFunctor sit.D n).map g := by
    have h2 : (e.functor.map (e.inverse.map f.hom)).right
        = (shiftFunctor sit.D n).map (e.inverse.map f.hom).right :=
      sit.rightShiftBaseEquiv_functor_map_right X n (e.inverse.map f.hom)
    exact h2
  have key : f.hom.right ≫ (e.counitIso.app B.obj).inv.right
      = (e.counitIso.app A.obj).inv.right ≫ (shiftFunctor sit.D n).map g := by
    have hnat := e.counitIso.inv.naturality f.hom
    have hr := congrArg CategoryTheory.StructuredArrow.Hom.right hnat
    simp only [StructuredArrow.comp_right, Functor.id_map, Functor.comp_map] at hr
    rw [Iso.app_inv, Iso.app_inv, ← hfun]
    exact hr
  -- assemble
  rw [← Category.assoc (sit.F.map f.hom.right), ← Functor.map_comp, key,
    Functor.map_comp, Category.assoc]

/-- The distinguished object `rightId (X⟦n⟧)` corresponds, under the inverse reindexing
equivalence, to the distinguished object `rightId X` (both are the identity arrow); this
provides the object iso `φ` needed by `computesRightDerived_shift_iff`.

Proof sketch: `rightShiftEquiv` sends `rightId X = (𝟙 X)` to `(𝟙 X)⟦n⟧ = 𝟙 (X⟦n⟧)`, i.e.
to `rightId (X⟦n⟧)`, up to the canonical iso (`StructuredArrow.mk` of an identity, with
`Functor.map_id`). Equivalently `(rightShiftEquiv).inverse.obj (rightId (X⟦n⟧)) ≅ rightId X`. -/
noncomputable def rightShiftEquivInverseIdIso :
    (sit.rightShiftEquiv X n).inverse.obj (sit.rightId (X⟦n⟧)) ≅ sit.rightId X := by
  -- SKETCH: identities are sent to identities; `rightShiftEquiv` maps `𝟙 X ↦ 𝟙 (X⟦n⟧)`.
  set E := sit.rightShiftEquiv X n with hE
  have h : E.functor.obj (sit.rightId X) ≅ sit.rightId (X⟦n⟧) := by
    refine (sit.rightFractionProp (X⟦n⟧)).fullyFaithfulι.preimageIso ?_
    refine StructuredArrow.isoMk (Iso.refl _) ?_
    change ((sit.rightShiftBaseEquiv X n).functor.obj (StructuredArrow.mk (𝟙 X))).hom ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, sit.rightShiftBaseEquiv_functor_obj_hom]
    simp
  exact E.inverse.mapIso h.symm ≪≫ (E.unitIso.app (sit.rightId X)).symm

/-- The base equivalence on costructured arrows induced by `shiftFunctor D n`. -/
noncomputable def leftShiftBaseEquiv :
    CostructuredArrow (𝟭 sit.D) X ≌ CostructuredArrow (𝟭 sit.D) (X⟦n⟧) :=
  haveI : IsIso ((Functor.rightUnitor (shiftFunctor sit.D n)).hom ≫
      (Functor.leftUnitor (shiftFunctor sit.D n)).inv) := by infer_instance
  (CostructuredArrow.map₂ (F := shiftFunctor sit.D n) (G := shiftFunctor sit.D n)
    ((Functor.rightUnitor (shiftFunctor sit.D n)).hom ≫
      (Functor.leftUnitor (shiftFunctor sit.D n)).inv) (𝟙 (X⟦n⟧))).asEquivalence

/-- The hom of the base-equivalence image of `A` is the shift of `A.hom`. -/
lemma leftShiftBaseEquiv_functor_obj_hom (A : CostructuredArrow (𝟭 sit.D) X) :
    ((sit.leftShiftBaseEquiv X n).functor.obj A).hom = (shiftFunctor sit.D n).map A.hom := by
  simp [leftShiftBaseEquiv, CostructuredArrow.map₂]

/-- The left component of the base-equivalence image of a morphism is its shift. -/
lemma leftShiftBaseEquiv_functor_map_left {A B : CostructuredArrow (𝟭 sit.D) X} (f : A ⟶ B) :
    ((sit.leftShiftBaseEquiv X n).functor.map f).left = (shiftFunctor sit.D n).map f.left := by
  simp [leftShiftBaseEquiv, CostructuredArrow.map₂]

/-- **The shift reindexing equivalence on left fractions** (dual of `rightShiftEquiv`). -/
noncomputable def leftShiftEquiv : sit.LeftFractions X ≌ sit.LeftFractions (X⟦n⟧) := by
  -- Restrict `leftShiftBaseEquiv` to the `S`-full subcategories.
  have hPQ : ∀ c : CostructuredArrow (𝟭 sit.D) X, sit.leftFractionProp X c →
      sit.leftFractionProp (X⟦n⟧) ((sit.leftShiftBaseEquiv X n).functor.obj c) := by
    intro c hc
    change sit.S _
    rw [sit.leftShiftBaseEquiv_functor_obj_hom]
    exact (MorphismProperty.IsCompatibleWithShift.iff sit.S c.hom n).mpr hc
  have hQP : ∀ B : CostructuredArrow (𝟭 sit.D) (X⟦n⟧), sit.leftFractionProp (X⟦n⟧) B →
      sit.leftFractionProp X ((sit.leftShiftBaseEquiv X n).inverse.obj B) := by
    intro B hB
    change sit.S _
    set e := sit.leftShiftBaseEquiv X n with he
    -- counit: e.functor.obj (e.inverse.obj B) ≅ B
    -- CostructuredArrow.w gives: θ ≫ B.hom = (e.functor.obj (e.inverse.obj B)).hom
    have hcomm : (e.counitIso.app B).hom.left ≫ B.hom
        = (e.functor.obj (e.inverse.obj B)).hom := CostructuredArrow.w (e.counitIso.app B).hom
    rw [sit.leftShiftBaseEquiv_functor_obj_hom] at hcomm
    -- The left component of the counit iso is an iso.
    have : IsIso ((e.counitIso.app B).hom.left) := by
      have : IsIso (e.counitIso.app B).hom := inferInstance
      exact (CostructuredArrow.proj (𝟭 sit.D) (X⟦n⟧)).map_isIso (e.counitIso.app B).hom
    -- So `(shift n).map (inverse B).hom = θ ≫ B.hom` ∈ S, hence by iff `(inverse B).hom ∈ S`.
    have hSshift : sit.S ((shiftFunctor sit.D n).map ((e.inverse.obj B).hom)) := by
      have heq : (shiftFunctor sit.D n).map ((e.inverse.obj B).hom)
          = (e.counitIso.app B).hom.left ≫ B.hom := by
        rw [← hcomm]
      rw [heq]
      have hθ : sit.S ((e.counitIso.app B).hom.left) := by
        refine sit.saturatedS.mem_of_comp_mem_comp
          (CategoryTheory.inv ((e.counitIso.app B).hom.left)) ((e.counitIso.app B).hom.left)
          (CategoryTheory.inv ((e.counitIso.app B).hom.left)) ?_ ?_
        · rw [IsIso.inv_hom_id]; exact sit.S.id_mem _
        · rw [IsIso.hom_inv_id]; exact sit.S.id_mem _
      exact sit.S.comp_mem _ _ hθ hB
    exact (MorphismProperty.IsCompatibleWithShift.iff sit.S ((e.inverse.obj B).hom) n).mp hSshift
  exact
    { functor := (sit.leftFractionProp (X⟦n⟧)).lift
        ((sit.leftFractionProp X).ι ⋙ (sit.leftShiftBaseEquiv X n).functor)
        (fun A => hPQ A.1 A.2)
      inverse := (sit.leftFractionProp X).lift
        ((sit.leftFractionProp (X⟦n⟧)).ι ⋙ (sit.leftShiftBaseEquiv X n).inverse)
        (fun A => hQP A.1 A.2)
      unitIso := NatIso.ofComponents
        (fun A => ((sit.leftFractionProp X).fullyFaithfulι).preimageIso
          ((sit.leftShiftBaseEquiv X n).unitIso.app A.1))
        (by intro A B f; apply (sit.leftFractionProp X).ι.map_injective
            simp [ObjectProperty.fullyFaithfulι])
      counitIso := NatIso.ofComponents
        (fun A => ((sit.leftFractionProp (X⟦n⟧)).fullyFaithfulι).preimageIso
          ((sit.leftShiftBaseEquiv X n).counitIso.app A.1))
        (by intro A B f; apply (sit.leftFractionProp (X⟦n⟧)).ι.map_injective
            simp [ObjectProperty.fullyFaithfulι])
      functor_unitIso_comp := by
        intro A
        apply (sit.leftFractionProp (X⟦n⟧)).ι.map_injective
        simp [ObjectProperty.fullyFaithfulι] }

/-- **The shift diagram comparison (left)** (dual of `rightDiagramShiftIso`). -/
noncomputable def leftDiagramShiftIso :
    sit.leftDiagram (X⟦n⟧) ≅
      (sit.leftShiftEquiv X n).inverse ⋙ sit.leftDiagram X ⋙ shiftFunctor sit.D' n := by
  refine NatIso.ofComponents
    (fun A =>
      have objYiso : ((sit.leftShiftEquiv X n).inverse.obj A).1.left ⟦n⟧ ≅ A.1.left :=
        (CostructuredArrow.proj _ _).mapIso ((sit.leftShiftBaseEquiv X n).counitIso.app A.1)
          ≪≫ Iso.refl _
      (sit.F.mapIso objYiso).symm ≪≫ (sit.F.commShiftIso n).app _)
    ?_
  intro A B f
  set e := sit.leftShiftBaseEquiv X n with he
  dsimp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.trans_inv, Iso.refl_inv, Functor.mapIso_hom, Iso.refl_hom]
  set PA := ((sit.leftShiftEquiv X n).inverse.obj A).obj.left with hPA
  set PB := ((sit.leftShiftEquiv X n).inverse.obj B).obj.left with hPB
  set g : PA ⟶ PB := (e.inverse.map f.hom).left with hg
  rw [CostructuredArrow.proj_map, CostructuredArrow.proj_map]
  change sit.F.map f.hom.left ≫ (sit.F.map (𝟙 _ ≫ (e.counitIso.app B.obj).inv.left)
        ≫ (sit.F.commShiftIso n).hom.app PB)
      = (sit.F.map (𝟙 _ ≫ (e.counitIso.app A.obj).inv.left)
          ≫ (sit.F.commShiftIso n).hom.app PA)
        ≫ (shiftFunctor sit.D' n).map (sit.F.map g)
  simp only [Category.id_comp]
  rw [Category.assoc, ← Functor.commShiftIso_hom_naturality sit.F g n]
  have hfun : (e.functor.map (e.inverse.map f.hom)).left
      = (shiftFunctor sit.D n).map g := by
    have h2 : (e.functor.map (e.inverse.map f.hom)).left
        = (shiftFunctor sit.D n).map (e.inverse.map f.hom).left :=
      sit.leftShiftBaseEquiv_functor_map_left X n (e.inverse.map f.hom)
    exact h2
  have key : f.hom.left ≫ (e.counitIso.app B.obj).inv.left
      = (e.counitIso.app A.obj).inv.left ≫ (shiftFunctor sit.D n).map g := by
    have hnat := e.counitIso.inv.naturality f.hom
    have hr := congrArg CategoryTheory.CostructuredArrow.Hom.left hnat
    simp only [CostructuredArrow.comp_left, Functor.id_map, Functor.comp_map] at hr
    rw [Iso.app_inv, Iso.app_inv, ← hfun]
    exact hr
  rw [← Category.assoc (sit.F.map f.hom.left), ← Functor.map_comp, key,
    Functor.map_comp, Category.assoc]

/-- Dual of `rightShiftEquivInverseIdIso`. -/
noncomputable def leftShiftEquivInverseIdIso :
    (sit.leftShiftEquiv X n).inverse.obj (sit.leftId (X⟦n⟧)) ≅ sit.leftId X := by
  -- SKETCH: identities sent to identities, dual to the right case.
  set E := sit.leftShiftEquiv X n with hE
  have h : E.functor.obj (sit.leftId X) ≅ sit.leftId (X⟦n⟧) := by
    refine (sit.leftFractionProp (X⟦n⟧)).fullyFaithfulι.preimageIso ?_
    refine CostructuredArrow.isoMk (Iso.refl _) ?_
    change (𝟭 sit.D).map (Iso.refl _).hom ≫ (sit.leftId (X⟦n⟧)).obj.hom
        = ((sit.leftShiftBaseEquiv X n).functor.obj (CostructuredArrow.mk (𝟙 X))).hom
    rw [sit.leftShiftBaseEquiv_functor_obj_hom]
    have e1 : (sit.leftId (X⟦n⟧)).obj.hom = 𝟙 (X⟦n⟧) := rfl
    rw [e1]
    simp
  exact E.inverse.mapIso h.symm ≪≫ (E.unitIso.app (sit.leftId X)).symm

end ShiftEquiv

/-! ## Main statement (Stacks 13.14.11, Tag 05SY) -/

section IsoEquiv

/-- Isomorphisms lie in the saturated multiplicative system `S`. -/
theorem mem_S_of_isIso {A B : sit.D} (θ : A ⟶ B) [IsIso θ] : sit.S θ := by
  have h1 : sit.S (CategoryTheory.inv θ ≫ θ) := by rw [IsIso.inv_hom_id]; exact sit.S.id_mem _
  have h2 : sit.S (θ ≫ CategoryTheory.inv θ) := by rw [IsIso.hom_inv_id]; exact sit.S.id_mem _
  exact sit.saturatedS.mem_of_comp_mem_comp (CategoryTheory.inv θ) θ (CategoryTheory.inv θ) h1 h2

variable {X Y : sit.D} (φ : X ≅ Y)

/-- The base equivalence `StructuredArrow Y (𝟭 D) ≌ StructuredArrow X (𝟭 D)` induced by the
iso `φ : X ≅ Y` (reindexing the structure map `(s : Y ⟶ X')` to `(φ.hom ≫ s : X ⟶ X')`). -/
noncomputable def isoBaseEquiv : StructuredArrow Y (𝟭 sit.D) ≌ StructuredArrow X (𝟭 sit.D) :=
  (StructuredArrow.mapIso φ (T := 𝟭 sit.D)).symm

/-- The reindexing equivalence on the `S`-fraction categories:
`RightFractions Y ≌ RightFractions X`. -/
noncomputable def isoRightEquiv : sit.RightFractions Y ≌ sit.RightFractions X := by
  have hPQ : ∀ c : StructuredArrow Y (𝟭 sit.D), sit.rightFractionProp Y c →
      sit.rightFractionProp X ((sit.isoBaseEquiv φ).functor.obj c) := by
    intro c hc
    change sit.S (φ.hom ≫ c.hom)
    exact sit.S.comp_mem _ _ (sit.mem_S_of_isIso φ.hom) hc
  have hQP : ∀ B : StructuredArrow X (𝟭 sit.D), sit.rightFractionProp X B →
      sit.rightFractionProp Y ((sit.isoBaseEquiv φ).inverse.obj B) := by
    intro B hB
    change sit.S (φ.inv ≫ B.hom)
    exact sit.S.comp_mem _ _ (sit.mem_S_of_isIso φ.inv) hB
  exact
    { functor := (sit.rightFractionProp X).lift
        ((sit.rightFractionProp Y).ι ⋙ (sit.isoBaseEquiv φ).functor)
        (fun A => hPQ A.1 A.2)
      inverse := (sit.rightFractionProp Y).lift
        ((sit.rightFractionProp X).ι ⋙ (sit.isoBaseEquiv φ).inverse)
        (fun A => hQP A.1 A.2)
      unitIso := NatIso.ofComponents
        (fun A => ((sit.rightFractionProp Y).fullyFaithfulι).preimageIso
          ((sit.isoBaseEquiv φ).unitIso.app A.1))
        (by intro A B f; apply (sit.rightFractionProp Y).ι.map_injective
            simp [ObjectProperty.fullyFaithfulι])
      counitIso := NatIso.ofComponents
        (fun A => ((sit.rightFractionProp X).fullyFaithfulι).preimageIso
          ((sit.isoBaseEquiv φ).counitIso.app A.1))
        (by intro A B f; apply (sit.rightFractionProp X).ι.map_injective
            simp [ObjectProperty.fullyFaithfulι])
      functor_unitIso_comp := by
        intro A
        apply (sit.rightFractionProp X).ι.map_injective
        simp [ObjectProperty.fullyFaithfulι] }

/-- Under the reindexing equivalence, `rightDiagram Y` is naturally isomorphic to
`rightDiagram X` reindexed by `(isoRightEquiv).functor` (the target object `F(X')` is
unchanged, so this is the identity natural iso). -/
noncomputable def isoRightDiagramIso :
    sit.rightDiagram Y ≅
      (sit.isoRightEquiv φ).functor ⋙ sit.rightDiagram X ⋙ 𝟭 sit.D' :=
  Iso.refl _

/-- The distinguished object `rightId Y` maps, under the reindexing equivalence, to an
object isomorphic to `rightId X`. -/
noncomputable def isoRightEquivIdIso :
    (sit.isoRightEquiv φ).functor.obj (sit.rightId Y) ≅ sit.rightId X := by
  refine (sit.rightFractionProp X).fullyFaithfulι.preimageIso ?_
  refine StructuredArrow.isoMk φ.symm ?_
  change (φ.hom ≫ 𝟙 Y) ≫ φ.inv = 𝟙 X
  simp

/-- The base equivalence `CostructuredArrow (𝟭 D) Y ≌ CostructuredArrow (𝟭 D) X` induced by
the iso `φ : X ≅ Y` (reindexing the structure map `(s : X' ⟶ Y)` to `(s ≫ φ.inv : X' ⟶ X)`).
Dual of `isoBaseEquiv`. -/
noncomputable def isoLeftBaseEquiv :
    CostructuredArrow (𝟭 sit.D) Y ≌ CostructuredArrow (𝟭 sit.D) X :=
  (CostructuredArrow.mapIso φ (S := 𝟭 sit.D)).symm

/-- The reindexing equivalence on the `S`-fraction categories: `LeftFractions Y ≌ LeftFractions X`.
Dual of `isoRightEquiv`. -/
noncomputable def isoLeftEquiv : sit.LeftFractions Y ≌ sit.LeftFractions X := by
  have hPQ : ∀ c : CostructuredArrow (𝟭 sit.D) Y, sit.leftFractionProp Y c →
      sit.leftFractionProp X ((sit.isoLeftBaseEquiv φ).functor.obj c) := by
    intro c hc
    change sit.S (c.hom ≫ φ.inv)
    exact sit.S.comp_mem _ _ hc (sit.mem_S_of_isIso φ.inv)
  have hQP : ∀ B : CostructuredArrow (𝟭 sit.D) X, sit.leftFractionProp X B →
      sit.leftFractionProp Y ((sit.isoLeftBaseEquiv φ).inverse.obj B) := by
    intro B hB
    change sit.S (B.hom ≫ φ.hom)
    exact sit.S.comp_mem _ _ hB (sit.mem_S_of_isIso φ.hom)
  exact
    { functor := (sit.leftFractionProp X).lift
        ((sit.leftFractionProp Y).ι ⋙ (sit.isoLeftBaseEquiv φ).functor)
        (fun A => hPQ A.1 A.2)
      inverse := (sit.leftFractionProp Y).lift
        ((sit.leftFractionProp X).ι ⋙ (sit.isoLeftBaseEquiv φ).inverse)
        (fun A => hQP A.1 A.2)
      unitIso := NatIso.ofComponents
        (fun A => ((sit.leftFractionProp Y).fullyFaithfulι).preimageIso
          ((sit.isoLeftBaseEquiv φ).unitIso.app A.1))
        (by intro A B f; apply (sit.leftFractionProp Y).ι.map_injective
            simp [ObjectProperty.fullyFaithfulι])
      counitIso := NatIso.ofComponents
        (fun A => ((sit.leftFractionProp X).fullyFaithfulι).preimageIso
          ((sit.isoLeftBaseEquiv φ).counitIso.app A.1))
        (by intro A B f; apply (sit.leftFractionProp X).ι.map_injective
            simp [ObjectProperty.fullyFaithfulι])
      functor_unitIso_comp := by
        intro A
        apply (sit.leftFractionProp X).ι.map_injective
        simp [ObjectProperty.fullyFaithfulι] }

/-- Under the reindexing equivalence, `leftDiagram Y` is naturally isomorphic to
`leftDiagram X` reindexed by `(isoLeftEquiv).functor` (identity natural iso). Dual of
`isoRightDiagramIso`. -/
noncomputable def isoLeftDiagramIso :
    sit.leftDiagram Y ≅
      (sit.isoLeftEquiv φ).functor ⋙ sit.leftDiagram X ⋙ 𝟭 sit.D' :=
  Iso.refl _

/-- The distinguished object `leftId Y` maps, under the reindexing equivalence, to an
object isomorphic to `leftId X`. Dual of `isoRightEquivIdIso`. -/
noncomputable def isoLeftEquivIdIso :
    (sit.isoLeftEquiv φ).functor.obj (sit.leftId Y) ≅ sit.leftId X := by
  refine (sit.leftFractionProp X).fullyFaithfulι.preimageIso ?_
  refine CostructuredArrow.isoMk φ.symm ?_
  change (𝟭 sit.D).map φ.symm.hom ≫ (sit.leftId X).obj.hom = (𝟙 Y ≫ φ.inv)
  change φ.inv ≫ 𝟙 X = 𝟙 Y ≫ φ.inv
  simp

end IsoEquiv

/-- Computing `RF` is invariant under an isomorphism of objects `X ≅ Y` of `D`: the iso induces
an equivalence of the index categories under which the two ind-objects agree on the nose and the
index `𝟙` corresponds to `𝟙`. -/
theorem computesRightDerived_of_iso {X Y : sit.D} (φ : X ≅ Y)
    (h : sit.F.ComputesRightDerived sit.S X) : sit.F.ComputesRightDerived sit.S Y := by
  rw [Functor.computesRightDerived_iff] at h ⊢
  exact sit.canonical_of_rightFractions Y
    (EssentiallyConstantInd.exists_isIso_of_equivalence (sit.isoRightEquiv φ).functor
      (𝟭 sit.D') (sit.isoRightDiagramIso φ) (sit.isoRightEquivIdIso φ)
      (sit.rightFractions_of_canonical X h))

/-- Computing `LF` is invariant under an isomorphism of objects (dual of
`computesRightDerived_of_iso`). -/
theorem computesLeftDerived_of_iso {X Y : sit.D} (φ : X ≅ Y)
    (h : sit.F.ComputesLeftDerived sit.S X) : sit.F.ComputesLeftDerived sit.S Y := by
  rw [Functor.computesLeftDerived_iff] at h ⊢
  exact sit.canonical_of_leftFractions Y
    (EssentiallyConstantPro.exists_isIso_of_equivalence (sit.isoLeftEquiv φ).functor
      (𝟭 sit.D') (sit.isoLeftDiagramIso φ).symm (sit.isoLeftEquivIdIso φ)
      (sit.leftFractions_of_canonical X h))

/-- A property invariant under isos and stable under shifts holds for `X` iff for `X⟦n⟧`. -/
private theorem iff_shift_of_fwd {P : sit.D → Prop} (hiso : ∀ {X Y : sit.D}, (X ≅ Y) → P X → P Y)
    (fwd : ∀ (Y : sit.D) (m : ℤ), P Y → P (Y⟦m⟧)) (X : sit.D) (n : ℤ) : P X ↔ P (X⟦n⟧) :=
  ⟨fwd X n, fun h => hiso ((shiftFunctorCompIsoId sit.D n (-n) (by simp)).app X) (fwd _ (-n) h)⟩

/-- Stacks 13.14.11(1), Tag 05SY: `X` computes `RF` if and only if `X⟦n⟧` computes `RF`.

The shift restricts to an equivalence `rightShiftEquiv` of the index categories, under which the
ind-object at `X⟦n⟧` is the ind-object at `X` followed by `⟦n⟧` (`rightDiagramShiftIso`) and the
index `𝟙 (X⟦n⟧)` corresponds to `𝟙 X`; essential constancy and invertibility of the canonical map
are carried across. The converse applies this to `X⟦n⟧` and `-n` and uses
`computesRightDerived_of_iso` along `X⟦n⟧⟦-n⟧ ≅ X`. -/
@[stacks 05SY "(1)"]
theorem computesRightDerived_shift_iff (X : sit.D) (n : ℤ) :
    sit.F.ComputesRightDerived sit.S X ↔ sit.F.ComputesRightDerived sit.S (X⟦n⟧) := by
  refine sit.iff_shift_of_fwd (fun φ => sit.computesRightDerived_of_iso φ) ?_ X n
  intro Y m h
  rw [Functor.computesRightDerived_iff] at h ⊢
  exact sit.canonical_of_rightFractions _
    (EssentiallyConstantInd.exists_isIso_of_equivalence (sit.rightShiftEquiv Y m).inverse
      (shiftFunctor sit.D' m) (sit.rightDiagramShiftIso Y m)
      (sit.rightShiftEquivInverseIdIso Y m) (sit.rightFractions_of_canonical Y h))

/-- Stacks 13.14.11(2), Tag 05SY: `X` computes `LF` if and only if `X⟦n⟧` computes `LF`.
Dual to `computesRightDerived_shift_iff`. -/
@[stacks 05SY "(2)"]
theorem computesLeftDerived_shift_iff (X : sit.D) (n : ℤ) :
    sit.F.ComputesLeftDerived sit.S X ↔ sit.F.ComputesLeftDerived sit.S (X⟦n⟧) := by
  refine sit.iff_shift_of_fwd (fun φ => sit.computesLeftDerived_of_iso φ) ?_ X n
  intro Y m h
  rw [Functor.computesLeftDerived_iff] at h ⊢
  exact sit.canonical_of_leftFractions _
    (EssentiallyConstantPro.exists_isIso_of_equivalence (sit.leftShiftEquiv Y m).inverse
      (shiftFunctor sit.D' m) (sit.leftDiagramShiftIso Y m).symm
      (sit.leftShiftEquivInverseIdIso Y m) (sit.leftFractions_of_canonical Y h))

end Situation

end Stacks.DerivedFunctor.Shift

end

end
