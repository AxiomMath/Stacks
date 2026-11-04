module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Deformation.Diagram
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Filtration

/-!
# Reducing a deformation problem to first-order deformations

Let `P` be a property of morphisms of schemes. To know that `P` passes from `f` to `f'` in
every cartesian finite-order deformation diagram, it suffices to know it in every *first-order*
diagram: the finite-order thickening of the base is filtered by first-order thickenings
(`Stacks.Thickenings.PowerFiltration`), each layer of the filtration gives a first-order
deformation diagram, and the two endpoints of the filtration are the given diagram's `f`
and `f'`.

In the other direction nothing is needed beyond base change: `f` is the base change of `f'`
along the target thickening, so any base-change-stable property descends from `f'` to `f`.

## Main results

* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.lift_of_isFirstOrderThickening`
  reduces the forward implication to the first-order case.
* `Stacks.Thickenings.CartesianFiniteOrderDeformationDiagram.property_of_baseChange`
  gives the reverse implication for a property stable under base change.

## Implementation notes

The layers of the filtration are assembled into diagrams by
`Stacks.Thickenings.deformationFiltrationDiagram`, with the two endpoints handled separately:
the initial diagram replaces level zero by the given `X` and `Y` through the canonical
isomorphisms of the filtration, and the final diagram replaces the last level by `X'` and `Y'`.
The forward reduction does not itself require base-change stability of `P`; that hypothesis is
used only for the reverse implication.

## References

* [Stacks Project, Tag 06AG](https://stacks.math.columbia.edu/tag/06AG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.Thickenings

universe u

/-- The map induced by `f' : X' ⟶ Y'` between the `i`th levels of the power filtrations of
`X'` and `Y'` over a closed immersion `iS`. -/
noncomputable def deformationFiltrationMap
    {S S' X' Y' : Scheme.{u}} (iS : S ⟶ S')
    (pX' : X' ⟶ S') (pY' : Y' ⟶ S') (f' : X' ⟶ Y')
    (hf' : f' ≫ pY' = pX') (i : ℕ) :
    PowerFiltration.totalLevel iS pX' i ⟶ PowerFiltration.totalLevel iS pY' i :=
  pullback.lift
    (PowerFiltration.totalInclusion iS pX' i ≫ f')
    (PowerFiltration.totalProjection iS pX' i)
    (by
      calc
        (PowerFiltration.totalInclusion iS pX' i ≫ f') ≫ pY' =
            PowerFiltration.totalInclusion iS pX' i ≫ (f' ≫ pY') := by rw [Category.assoc]
        _ = PowerFiltration.totalInclusion iS pX' i ≫ pX' :=
          congrArg (fun k => PowerFiltration.totalInclusion iS pX' i ≫ k) hf'
        _ = PowerFiltration.totalProjection iS pX' i ≫
              PowerFiltration.baseInclusion iS i := pullback.condition)

/-- The induced map on levels is compatible with the inclusions into the original total
spaces. -/
lemma deformationFiltrationMap_comp_inclusion
    {S S' X' Y' : Scheme.{u}} (iS : S ⟶ S')
    (pX' : X' ⟶ S') (pY' : Y' ⟶ S') (f' : X' ⟶ Y')
    (hf' : f' ≫ pY' = pX') (i : ℕ) :
    deformationFiltrationMap iS pX' pY' f' hf' i ≫
      PowerFiltration.totalInclusion iS pY' i =
        PowerFiltration.totalInclusion iS pX' i ≫ f' := by
  show (pullback.lift _ _ _) ≫ pullback.fst pY' _ = _
  exact pullback.lift_fst _ _ _

/-- The induced map on levels is a morphism over the corresponding level of the base. -/
lemma deformationFiltrationMap_comp_projection
    {S S' X' Y' : Scheme.{u}} (iS : S ⟶ S')
    (pX' : X' ⟶ S') (pY' : Y' ⟶ S') (f' : X' ⟶ Y')
    (hf' : f' ≫ pY' = pX') (i : ℕ) :
    deformationFiltrationMap iS pX' pY' f' hf' i ≫
      PowerFiltration.totalProjection iS pY' i =
        PowerFiltration.totalProjection iS pX' i := by
  show (pullback.lift _ _ _) ≫ pullback.snd pY' _ = _
  exact pullback.lift_snd _ _ _

/-- The induced maps on levels commute with the steps of the two filtrations, so consecutive
levels form a morphism of thickenings. -/
lemma deformationFiltrationMap_step_comm
    {S S' X' Y' : Scheme.{u}} (iS : S ⟶ S')
    (pX' : X' ⟶ S') (pY' : Y' ⟶ S') (f' : X' ⟶ Y')
    (hf' : f' ≫ pY' = pX') (i : ℕ) :
    deformationFiltrationMap iS pX' pY' f' hf' i ≫ PowerFiltration.totalStep iS pY' i =
      PowerFiltration.totalStep iS pX' i ≫
        deformationFiltrationMap iS pX' pY' f' hf' (i + 1) := by
  apply (IsPullback.of_hasPullback pY'
    (PowerFiltration.baseInclusion iS (i + 1))).hom_ext
  · change _ ≫ PowerFiltration.totalInclusion iS pY' (i + 1) =
      _ ≫ PowerFiltration.totalInclusion iS pY' (i + 1)
    rw [Category.assoc, PowerFiltration.totalStep_comp_inclusion,
      deformationFiltrationMap_comp_inclusion, Category.assoc,
      deformationFiltrationMap_comp_inclusion, ← Category.assoc,
      PowerFiltration.totalStep_comp_inclusion]
  · change _ ≫ PowerFiltration.totalProjection iS pY' (i + 1) =
      _ ≫ PowerFiltration.totalProjection iS pY' (i + 1)
    rw [Category.assoc, Category.assoc, (PowerFiltration.totalStep_isPullback iS pY' i).w,
      ← Category.assoc, deformationFiltrationMap_comp_projection,
      deformationFiltrationMap_comp_projection, (PowerFiltration.totalStep_isPullback iS pX' i).w]

/-- A step of the power filtration of a closed immersion is a first-order, hence
finite-order, thickening. -/
lemma baseStep_finiteOrder {S S' : Scheme.{u}} (iS : S ⟶ S') (i : ℕ) :
    IsFiniteOrderThickening (PowerFiltration.baseStep iS i) :=
  ⟨(PowerFiltration.baseStep_firstOrder iS i).1, 1,
    by simpa using (PowerFiltration.baseStep_firstOrder iS i).2⟩

/-- The `i`th layer of the power filtration, as a cartesian finite-order deformation
diagram. -/
noncomputable def deformationFiltrationDiagram
    (D : CartesianFiniteOrderDeformationDiagram.{u}) (i : ℕ) :
    CartesianFiniteOrderDeformationDiagram.{u} where
  S := PowerFiltration.baseLevel D.iS i
  S' := PowerFiltration.baseLevel D.iS (i + 1)
  iS := PowerFiltration.baseStep D.iS i
  iS_finiteOrder := baseStep_finiteOrder D.iS i
  X := PowerFiltration.totalLevel D.iS D.pX' i
  X' := PowerFiltration.totalLevel D.iS D.pX' (i + 1)
  iX := PowerFiltration.totalStep D.iS D.pX' i
  iX_thickening := (PowerFiltration.totalStep_firstOrder D.iS D.pX' i).isThickening
  Y := PowerFiltration.totalLevel D.iS D.pY' i
  Y' := PowerFiltration.totalLevel D.iS D.pY' (i + 1)
  iY := PowerFiltration.totalStep D.iS D.pY' i
  iY_thickening := (PowerFiltration.totalStep_firstOrder D.iS D.pY' i).isThickening
  pX := PowerFiltration.totalProjection D.iS D.pX' i
  pX' := PowerFiltration.totalProjection D.iS D.pX' (i + 1)
  pY := PowerFiltration.totalProjection D.iS D.pY' i
  pY' := PowerFiltration.totalProjection D.iS D.pY' (i + 1)
  f := deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' i
  f' := deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' (i + 1)
  f_over_S := deformationFiltrationMap_comp_projection D.iS D.pX' D.pY' D.f' D.f'_over_S' i
  f'_over_S' :=
    deformationFiltrationMap_comp_projection D.iS D.pX' D.pY' D.f' D.f'_over_S' (i + 1)
  f_thickening_comm :=
    deformationFiltrationMap_step_comm D.iS D.pX' D.pY' D.f' D.f'_over_S' i
  X_cartesian := PowerFiltration.totalStep_isPullback D.iS D.pX' i
  Y_cartesian := PowerFiltration.totalStep_isPullback D.iS D.pY' i
  X'_flat := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback D.pX' (PowerFiltration.baseInclusion D.iS (i + 1))) D.X'_flat

/-- The base thickening of a layer of the filtration is a first-order thickening. -/
lemma deformationFiltrationDiagram_isFirstOrderThickening
    (D : CartesianFiniteOrderDeformationDiagram.{u}) (i : ℕ) :
    IsFirstOrderThickening (deformationFiltrationDiagram D i).iS :=
  PowerFiltration.baseStep_firstOrder D.iS i

/-- Each level of the base-changed power filtration of a deformation diagram is flat over the
corresponding level of the base. -/
lemma flat_totalProjection
    (D : CartesianFiniteOrderDeformationDiagram.{u}) (i : ℕ) :
    Flat (PowerFiltration.totalProjection D.iS D.pX' i) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback D.pX' (PowerFiltration.baseInclusion D.iS i)) D.X'_flat

/-- The initial layer of the filtration, with level zero of the two base changes replaced by
the given `X` and `Y`. -/
noncomputable def deformationFirstFiltrationDiagram
    (D : CartesianFiniteOrderDeformationDiagram.{u}) :
    CartesianFiniteOrderDeformationDiagram.{u} := by
  have _ : IsIso (PowerFiltration.baseInitialMap D.iS) :=
    PowerFiltration.baseInitialMap_isIso D.iS D.iS_finiteOrder.1
  have hx0 := PowerFiltration.totalLevel_zero_iso
    D.iS D.pX' D.iX D.pX D.X_cartesian D.iS_finiteOrder.1
  have hy0 := PowerFiltration.totalLevel_zero_iso
    D.iS D.pY' D.iY D.pY D.Y_cartesian D.iS_finiteOrder.1
  let eX := Classical.choose hx0
  let eY := Classical.choose hy0
  have hXinc := (Classical.choose_spec hx0).1
  have hXproj := (Classical.choose_spec hx0).2
  have hYinc := (Classical.choose_spec hy0).1
  have hYproj := (Classical.choose_spec hy0).2
  have hX0 : IsPullback eX.hom (D.pX ≫ PowerFiltration.baseInitialMap D.iS)
      (PowerFiltration.totalProjection D.iS D.pX' 0)
      (𝟙 (PowerFiltration.baseLevel D.iS 0)) :=
    IsPullback.of_horiz_isIso ⟨by simpa using hXproj⟩
  have hY0 : IsPullback eY.hom (D.pY ≫ PowerFiltration.baseInitialMap D.iS)
      (PowerFiltration.totalProjection D.iS D.pY' 0)
      (𝟙 (PowerFiltration.baseLevel D.iS 0)) :=
    IsPullback.of_horiz_isIso ⟨by simpa using hYproj⟩
  have hXcart : IsPullback (eX.hom ≫ PowerFiltration.totalStep D.iS D.pX' 0)
      (D.pX ≫ PowerFiltration.baseInitialMap D.iS)
      (PowerFiltration.totalProjection D.iS D.pX' 1) (PowerFiltration.baseStep D.iS 0) := by
    simpa using hX0.paste_horiz (PowerFiltration.totalStep_isPullback D.iS D.pX' 0)
  have hYcart : IsPullback (eY.hom ≫ PowerFiltration.totalStep D.iS D.pY' 0)
      (D.pY ≫ PowerFiltration.baseInitialMap D.iS)
      (PowerFiltration.totalProjection D.iS D.pY' 1) (PowerFiltration.baseStep D.iS 0) := by
    simpa using hY0.paste_horiz (PowerFiltration.totalStep_isPullback D.iS D.pY' 0)
  have hNat : eX.hom ≫ deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' 0 =
      D.f ≫ eY.hom := by
    apply (IsPullback.of_hasPullback D.pY'
      (PowerFiltration.baseInclusion D.iS 0)).hom_ext
    · calc
        (eX.hom ≫ deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' 0) ≫
            PowerFiltration.totalInclusion D.iS D.pY' 0 =
          eX.hom ≫ (deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' 0 ≫
            PowerFiltration.totalInclusion D.iS D.pY' 0) := by simp only [Category.assoc]
        _ = eX.hom ≫ (PowerFiltration.totalInclusion D.iS D.pX' 0 ≫ D.f') :=
          congrArg (fun k => eX.hom ≫ k)
            (deformationFiltrationMap_comp_inclusion D.iS D.pX' D.pY' D.f' D.f'_over_S' 0)
        _ = D.iX ≫ D.f' := by
          simpa using congrArg (fun k => k ≫ D.f') hXinc
        _ = D.f ≫ D.iY := D.f_thickening_comm.symm
        _ = D.f ≫ (eY.hom ≫ PowerFiltration.totalInclusion D.iS D.pY' 0) :=
          congrArg (fun k => D.f ≫ k) hYinc.symm
        _ = (D.f ≫ eY.hom) ≫ PowerFiltration.totalInclusion D.iS D.pY' 0 := by
          simp only [Category.assoc]
    · calc
        (eX.hom ≫ deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' 0) ≫
            PowerFiltration.totalProjection D.iS D.pY' 0 =
          eX.hom ≫ (deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' 0 ≫
            PowerFiltration.totalProjection D.iS D.pY' 0) := by simp only [Category.assoc]
        _ = eX.hom ≫ PowerFiltration.totalProjection D.iS D.pX' 0 :=
          congrArg (fun k => eX.hom ≫ k)
            (deformationFiltrationMap_comp_projection D.iS D.pX' D.pY' D.f' D.f'_over_S' 0)
        _ = D.pX ≫ PowerFiltration.baseInitialMap D.iS := by simpa using hXproj
        _ = D.f ≫ D.pY ≫ PowerFiltration.baseInitialMap D.iS := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ PowerFiltration.baseInitialMap D.iS) D.f_over_S.symm
        _ = (D.f ≫ eY.hom) ≫ PowerFiltration.totalProjection D.iS D.pY' 0 := by
          simp only [Category.assoc]; rw [hYproj]
  have hstepComm : D.f ≫ (eY.hom ≫ PowerFiltration.totalStep D.iS D.pY' 0) =
      (eX.hom ≫ PowerFiltration.totalStep D.iS D.pX' 0) ≫
        deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' 1 := by
    rw [← Category.assoc, ← hNat, Category.assoc, deformationFiltrationMap_step_comm,
      Category.assoc]
  exact
    { S := PowerFiltration.baseLevel D.iS 0
      S' := PowerFiltration.baseLevel D.iS 1
      iS := PowerFiltration.baseStep D.iS 0
      iS_finiteOrder := baseStep_finiteOrder D.iS 0
      X := D.X
      X' := PowerFiltration.totalLevel D.iS D.pX' 1
      iX := eX.hom ≫ PowerFiltration.totalStep D.iS D.pX' 0
      iX_thickening := isThickening_comp (isThickening_of_isIso eX.hom)
        (PowerFiltration.totalStep_firstOrder D.iS D.pX' 0).isThickening
      Y := D.Y
      Y' := PowerFiltration.totalLevel D.iS D.pY' 1
      iY := eY.hom ≫ PowerFiltration.totalStep D.iS D.pY' 0
      iY_thickening := isThickening_comp (isThickening_of_isIso eY.hom)
        (PowerFiltration.totalStep_firstOrder D.iS D.pY' 0).isThickening
      pX := D.pX ≫ PowerFiltration.baseInitialMap D.iS
      pX' := PowerFiltration.totalProjection D.iS D.pX' 1
      pY := D.pY ≫ PowerFiltration.baseInitialMap D.iS
      pY' := PowerFiltration.totalProjection D.iS D.pY' 1
      f := D.f
      f' := deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' 1
      f_over_S := by rw [← Category.assoc, D.f_over_S]
      f'_over_S' :=
        deformationFiltrationMap_comp_projection D.iS D.pX' D.pY' D.f' D.f'_over_S' 1
      f_thickening_comm := hstepComm
      X_cartesian := hXcart
      Y_cartesian := hYcart
      X'_flat := flat_totalProjection D 1 }

/-- The final layer of the filtration, with the last level of the two base changes replaced by
the given `X'` and `Y'`. -/
noncomputable def deformationLastFiltrationDiagram
    (D : CartesianFiniteOrderDeformationDiagram.{u}) (i : ℕ)
    (hn : D.iS.ker ^ ((i + 1) + 1) = ⊥) :
    CartesianFiniteOrderDeformationDiagram.{u} := by
  have _ : IsIso (PowerFiltration.baseInclusion D.iS (i + 1)) :=
    PowerFiltration.baseInclusion_isIso D.iS hn
  have _ : IsIso (PowerFiltration.totalInclusion D.iS D.pX' (i + 1)) :=
    PowerFiltration.totalInclusion_isIso D.iS D.pX' hn
  have _ : IsIso (PowerFiltration.totalInclusion D.iS D.pY' (i + 1)) :=
    PowerFiltration.totalInclusion_isIso D.iS D.pY' hn
  let eS : PowerFiltration.baseLevel D.iS (i + 1) ≅ D.S' :=
    asIso (PowerFiltration.baseInclusion D.iS (i + 1))
  have hj : PowerFiltration.baseInclusion D.iS (i + 1) ≫ eS.inv =
      𝟙 (PowerFiltration.baseLevel D.iS (i + 1)) := by
    simp [eS]
  have hXend : IsPullback (PowerFiltration.totalInclusion D.iS D.pX' (i + 1))
      (PowerFiltration.totalProjection D.iS D.pX' (i + 1)) (D.pX' ≫ eS.inv)
      (𝟙 (PowerFiltration.baseLevel D.iS (i + 1))) :=
    IsPullback.of_horiz_isIso
      ⟨by rw [← Category.assoc, pullback.condition, Category.assoc, hj]⟩
  have hYend : IsPullback (PowerFiltration.totalInclusion D.iS D.pY' (i + 1))
      (PowerFiltration.totalProjection D.iS D.pY' (i + 1)) (D.pY' ≫ eS.inv)
      (𝟙 (PowerFiltration.baseLevel D.iS (i + 1))) :=
    IsPullback.of_horiz_isIso
      ⟨by rw [← Category.assoc, pullback.condition, Category.assoc, hj]⟩
  have hXcart : IsPullback (PowerFiltration.totalStep D.iS D.pX' i ≫
        PowerFiltration.totalInclusion D.iS D.pX' (i + 1))
      (PowerFiltration.totalProjection D.iS D.pX' i) (D.pX' ≫ eS.inv)
      (PowerFiltration.baseStep D.iS i) := by
    simpa using (PowerFiltration.totalStep_isPullback D.iS D.pX' i).paste_horiz hXend
  have hYcart : IsPullback (PowerFiltration.totalStep D.iS D.pY' i ≫
        PowerFiltration.totalInclusion D.iS D.pY' (i + 1))
      (PowerFiltration.totalProjection D.iS D.pY' i) (D.pY' ≫ eS.inv)
      (PowerFiltration.baseStep D.iS i) := by
    simpa using (PowerFiltration.totalStep_isPullback D.iS D.pY' i).paste_horiz hYend
  have hflat : Flat (D.pX' ≫ eS.inv) := by
    have _ : Flat D.pX' := D.X'_flat
    infer_instance
  have hcomm :
      deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' i ≫
          (PowerFiltration.totalStep D.iS D.pY' i ≫
            PowerFiltration.totalInclusion D.iS D.pY' (i + 1)) =
        (PowerFiltration.totalStep D.iS D.pX' i ≫
          PowerFiltration.totalInclusion D.iS D.pX' (i + 1)) ≫ D.f' := by
    rw [← Category.assoc, deformationFiltrationMap_step_comm, Category.assoc,
      deformationFiltrationMap_comp_inclusion, Category.assoc]
  exact
    { S := PowerFiltration.baseLevel D.iS i
      S' := PowerFiltration.baseLevel D.iS (i + 1)
      iS := PowerFiltration.baseStep D.iS i
      iS_finiteOrder := baseStep_finiteOrder D.iS i
      X := PowerFiltration.totalLevel D.iS D.pX' i
      X' := D.X'
      iX := PowerFiltration.totalStep D.iS D.pX' i ≫
        PowerFiltration.totalInclusion D.iS D.pX' (i + 1)
      iX_thickening := isThickening_comp
        (PowerFiltration.totalStep_firstOrder D.iS D.pX' i).isThickening
        (isThickening_of_isIso (PowerFiltration.totalInclusion D.iS D.pX' (i + 1)))
      Y := PowerFiltration.totalLevel D.iS D.pY' i
      Y' := D.Y'
      iY := PowerFiltration.totalStep D.iS D.pY' i ≫
        PowerFiltration.totalInclusion D.iS D.pY' (i + 1)
      iY_thickening := isThickening_comp
        (PowerFiltration.totalStep_firstOrder D.iS D.pY' i).isThickening
        (isThickening_of_isIso (PowerFiltration.totalInclusion D.iS D.pY' (i + 1)))
      pX := PowerFiltration.totalProjection D.iS D.pX' i
      pX' := D.pX' ≫ eS.inv
      pY := PowerFiltration.totalProjection D.iS D.pY' i
      pY' := D.pY' ≫ eS.inv
      f := deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' i
      f' := D.f'
      f_over_S :=
        deformationFiltrationMap_comp_projection D.iS D.pX' D.pY' D.f' D.f'_over_S' i
      f'_over_S' := by rw [← Category.assoc, D.f'_over_S']
      f_thickening_comm := hcomm
      X_cartesian := hXcart
      Y_cartesian := hYcart
      X'_flat := hflat }

namespace CartesianFiniteOrderDeformationDiagram

/-- Lifting a morphism property across finite-order deformations reduces to lifting it across
first-order deformations. -/
theorem lift_of_isFirstOrderThickening
    (P : MorphismProperty Scheme.{u})
    (hfirst : ∀ E : CartesianFiniteOrderDeformationDiagram.{u},
      IsFirstOrderThickening E.iS → P E.f → P E.f')
    (D : CartesianFiniteOrderDeformationDiagram.{u})
    (hf : P D.f) : P D.f' := by
  obtain ⟨n, hn⟩ := D.iS_finiteOrder.2
  by_cases hnsmall : n ≤ 1
  · have hpow : D.iS.ker ^ 2 = ⊥ := by
      by_cases hzero : n = 0
      · subst n
        have hker : D.iS.ker = ⊥ := by simpa using hn
        apply Scheme.IdealSheafData.ext
        funext U
        have hkerU := congrArg (fun J : Scheme.IdealSheafData D.S' => J.ideal U) hker
        show (D.iS.ker.ideal U) ^ 2 = (⊥ : Scheme.IdealSheafData D.S').ideal U
        rw [hkerU]
        exact Ideal.bot_pow (by decide)
      · have hone : n = 1 := by omega
        subst n
        simpa using hn
    exact hfirst D ⟨D.iS_finiteOrder.1, hpow⟩ hf
  · have hE₀ : P (deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' 1) :=
      hfirst (deformationFirstFiltrationDiagram D) (PowerFiltration.baseStep_firstOrder D.iS 0) hf
    have hchain : ∀ k : ℕ,
        P (deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' (k + 1)) := by
      intro k
      induction k with
      | zero => simpa using hE₀
      | succ k ih =>
          exact hfirst (deformationFiltrationDiagram D (k + 1))
            (deformationFiltrationDiagram_isFirstOrderThickening D (k + 1)) ih
    have hnlast : D.iS.ker ^ (((n - 1) + 1) + 1) = ⊥ := by
      rwa [show n - 1 + 1 = n by omega]
    have hprev : P (deformationFiltrationMap D.iS D.pX' D.pY' D.f' D.f'_over_S' (n - 1)) := by
      have h := hchain (n - 1 - 1)
      rwa [Nat.sub_add_cancel (show 1 ≤ n - 1 by omega)] at h
    exact hfirst (deformationLastFiltrationDiagram D (n - 1) hnlast)
      (PowerFiltration.baseStep_firstOrder D.iS (n - 1)) hprev

/-- The morphism of closed subschemes is a base change of the morphism of ambient schemes, so
every base-change-stable property descends to it. -/
theorem property_of_baseChange
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (D : CartesianFiniteOrderDeformationDiagram.{u})
    (hf' : P D.f') : P D.f := by
  have hpb : IsPullback D.f D.iX D.iY D.f' := by
    apply IsPullback.mk'
    · exact D.f_thickening_comm
    · intro T c c' hc hc'
      apply D.X_cartesian.hom_ext
      · exact hc'
      · rw [← D.f_over_S, ← Category.assoc, hc, Category.assoc]
    · intro T a b hab
      let l := D.X_cartesian.lift b (a ≫ D.pY) (by
        rw [← D.f'_over_S', ← Category.assoc, ← hab, Category.assoc, Category.assoc,
          D.Y_cartesian.w])
      refine ⟨l, ?_, D.X_cartesian.lift_fst _ _ _⟩
      apply D.Y_cartesian.hom_ext
      · calc
          l ≫ D.f ≫ D.iY = l ≫ D.iX ≫ D.f' := congrArg (fun k => l ≫ k) D.f_thickening_comm
          _ = b ≫ D.f' := congrArg (fun k => k ≫ D.f') (D.X_cartesian.lift_fst _ _ _)
          _ = a ≫ D.iY := hab.symm
      · calc
          l ≫ D.f ≫ D.pY = l ≫ D.pX := congrArg (fun k => l ≫ k) D.f_over_S
          _ = a ≫ D.pY := D.X_cartesian.lift_snd _ _ _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb.flip hf'

end CartesianFiniteOrderDeformationDiagram

end Stacks.Thickenings

end
