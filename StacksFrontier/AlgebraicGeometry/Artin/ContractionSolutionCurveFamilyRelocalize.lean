module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase

/-!
# Pointwise étale-chart conditions under the forward functor of Stacks 04SG

Let `g : S ⟶ S'` be a morphism of a big fppf site and let `F` be an algebraic space over `S`. The
forward functor `AlgebraicGeometry.spacesOverSmallerBaseFunctor` of Stacks 04SG views `F` as an
algebraic space over `S'` with a morphism to the representable algebraic space of `S`. This file
proves that a property of morphisms of germs which is étale local on source and target, and which
holds at a point of `F` for the structural morphism of `F` to the terminal object over `S`, holds
at the corresponding point of the image for its structural morphism to the representable algebraic
space of `S`.

## Main results

* `AlgebraicGeometry.Space.exists_holdsOnEveryEtaleChartAtPoint_spacesOverSmallerBaseFunctor`:
  every point of the image comes from a point of `F` at which every such property transfers.
* `AlgebraicGeometry.Space.relativeDimensionLE_spacesOverSmallerBaseFunctor`: the pointwise bound
  `≤ 1` on the dimension of the fibres transfers.

## Implementation notes

A pointed étale chart `a : h_U ⟶ F` at `x` gives, over `S`, the pointed chart of the structural
morphism whose target chart is the terminal representable presheaf, and whose morphism of charts is
the structure morphism `U ⟶ S`. Over `S'`, the extension of `a`
(`AlgebraicGeometry.relocalizeChart`) read through
`AlgebraicGeometry.spacesOverSmallerBaseFunctorForgetIso` is a chart of the image, the target chart
is the identity of the representable presheaf of `S ⟶ S'`, and the morphism of charts is
`AlgebraicGeometry.relocalizeOverHom`, again the structure morphism `U ⟶ S`. Both charts have the
same underlying morphism of schemes and the same scheme point, so the germ condition is literally
the same; chart independence (`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_of_chart`)
does the rest.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] etale_scheme_respectsIso

/-- **Pointwise étale-local properties pass to the forward functor of Stacks 04SG.** Every point
`y` of the image of an algebraic space `F` over `S` under
`AlgebraicGeometry.spacesOverSmallerBaseFunctor` comes from a point `x` of `F` such that every
property of morphisms of germs which is étale local on source and target, and which holds at `x`
for the structural morphism of `F` to the terminal object over `S`, holds at `y` for the structural
morphism of the image to the representable algebraic space of `S` over `S'`. -/
theorem exists_holdsOnEveryEtaleChartAtPoint_spacesOverSmallerBaseFunctor
    {B : BigFppfSite.{u}} {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
    (g : B.obj hS ⟶ B.obj hS') (F : AlgebraicSpaces B S hS)
    (y : points B S' hS' ((spacesOverSmallerBaseFunctor B S S' hS hS' g).obj F).1.left) :
    ∃ x : points B S hS F.1,
      ∀ (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop),
        MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q →
        HoldsOnEveryEtaleChartAtPoint B S hS Q (terminal.from F.1) x →
        HoldsOnEveryEtaleChartAtPoint B S' hS' Q
          ((spacesOverSmallerBaseFunctor B S S' hS hS' g).obj F).1.hom y := by
  let E := ((spacesOverSmallerBaseFunctor B S S' hS hS' g).obj F).1.left
  let φ : (OverShriek.relocalizePresheafFunctor g).obj F.1 ⟶ E :=
    (spacesOverSmallerBaseFunctorForgetIso B S S' hS hS' g).inv.app F
  let ψ : E ⟶ (OverShriek.relocalizePresheafFunctor g).obj F.1 :=
    (spacesOverSmallerBaseFunctorForgetIso B S S' hS hS' g).hom.app F
  have hψφ : ψ ≫ φ = 𝟙 E := (spacesOverSmallerBaseFunctorForgetIso B S S' hS hS' g).hom_inv_id_app F
  obtain ⟨x, hx⟩ := pointsRelocalize_surjective B S S' hS hS' g F.1 (pointsMap B S' hS' _ ψ y)
  refine ⟨x, fun Q hQ H => ?_⟩
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS F.2 F.2 (𝟙 F.1) x
  have hx' : pointsMap B S hS _ c.a (c.representative.class B S hS _) = x := c.maps_to
  -- The terminal representable presheaf over `S`.
  let eT : yoneda.obj (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B S hS) ≅ ⊤_ _ :=
    (IsTerminal.isTerminalObj yoneda _ Over.mkIdTerminal).uniqueUpToIso terminalIsTerminal
  -- The pointed chart over `S` whose target chart is the terminal representable presheaf.
  let c₁ : EtaleChartAtPoint B S hS (terminal.from F.1) x :=
    { U := c.U
      V := Over.mk (𝟙 (B.obj hS))
      a := c.a
      b := eT.hom
      h := Over.homMk c.U.hom (by simp)
      a_etale := c.a_etale
      b_etale := presheaf_etale_of_iso B S hS eT
      comm := terminal.hom_ext _ _
      representative := c.representative
      point := c.point
      maps_to := hx' }
  -- The pointed chart over `S'` of the structural morphism of the image.
  let a' := relocalizeChart B S S' hS hS' g c.a ≫ φ
  have ha' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S' hS')).presheaf a' :=
    MorphismProperty.RespectsIso.postcomp _ φ _
      ((presheaf_relocalizeChart_iff B S S' hS hS' g (@Etale.{u}) c.a).mpr c.a_etale)
  have hcomm : yoneda.map (relocalizeOverHom B S S' hS hS' g c.U) ≫ 𝟙 _ =
      a' ≫ ((spacesOverSmallerBaseFunctor B S S' hS hS' g).obj F).1.hom := by
    rw [Category.comp_id, Category.assoc, relocalizeToYoneda_eq,
      relocalizeChart_comp_relocalizeToYoneda]
  have hmaps : pointsMap B S' hS' _ a'
      ((FieldValuedPoint.relocalizeRep B S S' hS hS' g c.U c.representative).class
        B S' hS' _) = y := by
    rw [pointsMap_comp_apply, pointsMap_class, class_map_relocalizeChart_relocalizeRep,
      ← pointsRelocalize_class, ← pointsMap_class, hx', hx, ← pointsMap_comp_apply, hψφ,
      pointsMap_id]
    rfl
  let c' : EtaleChartAtPoint B S' hS'
      ((spacesOverSmallerBaseFunctor B S S' hS hS' g).obj F).1.hom y :=
    { U := (Over.map g).obj c.U
      V := Over.mk g
      a := a'
      b := 𝟙 _
      h := relocalizeOverHom B S S' hS hS' g c.U
      a_etale := ha'
      b_etale := presheaf_etale_of_iso B S' hS' (Iso.refl _)
      comm := hcomm
      representative := FieldValuedPoint.relocalizeRep B S S' hS hS' g c.U c.representative
      point := c.point
      maps_to := hmaps }
  exact (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S' hS' Q hQ _ y c').mpr (H c₁)

/-- **The pointwise curve-family dimension bound passes to the forward functor of Stacks 04SG.**
If at every point of an algebraic space `F` over `S` the structural morphism to the terminal
object has fibre dimension `e ≤ 1` on every pointed étale chart, then so does, at every point of
its image under `AlgebraicGeometry.spacesOverSmallerBaseFunctor`, the structural morphism to the
representable algebraic space of `S` over `S'`. -/
theorem relativeDimensionLE_spacesOverSmallerBaseFunctor
    {B : BigFppfSite.{u}} {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
    (g : B.obj hS ⟶ B.obj hS') (F : AlgebraicSpaces B S hS)
    (h : ∀ x : points B S hS F.1, ∃ e : ℕ, e ≤ 1 ∧
      HoldsOnEveryEtaleChartAtPoint B S hS (@HasFiberDimensionAt.{u} (e : ℕ∞))
        (terminal.from F.1) x) :
    ∀ y, ∃ e : ℕ, e ≤ 1 ∧
      HoldsOnEveryEtaleChartAtPoint B S' hS' (@HasFiberDimensionAt.{u} (e : ℕ∞))
        ((spacesOverSmallerBaseFunctor B S S' hS hS' g).obj F).1.hom y := by
  intro y
  obtain ⟨x, hx⟩ := exists_holdsOnEveryEtaleChartAtPoint_spacesOverSmallerBaseFunctor g F y
  obtain ⟨e, he, hxe⟩ := h x
  exact ⟨e, he, hx _ (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞)) hxe⟩

end AlgebraicGeometry.Space

end
