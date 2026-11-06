module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmoothCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SyntomicCoverings

/-!
# Base change of a property local on the base

A property of morphisms of algebraic spaces over `S` which is local on the base for one of the
five topologies of Stacks 03YH is inherited by the base change of a morphism along any member
of a covering family for that topology, and in particular along any morphism of the kind
belonging to that topology.

## Main results

* `AlgebraicGeometry.Space.prop_fiberProduct_fst_of_mem_precoverage` gives the property of the
  base-changed morphism along a member of a covering presieve.
* `AlgebraicGeometry.Space.exists_mem_precoverage_containing` exhibits a morphism of the kind
  belonging to `τ` as a member of a `τ`-covering presieve.
* `AlgebraicGeometry.Space.prop_fiberProduct_fst_of_isLocalAtTarget` gives the property of the
  base-changed morphism along any morphism of the kind belonging to `τ`.

## References

* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 06EM](https://stacks.math.columbia.edu/tag/06EM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 200000 in
/-- A property of morphisms of algebraic spaces over `S` which is local on the base for `τ` is
inherited by the base change along any member of a `τ`-covering presieve of the target. -/
theorem prop_fiberProduct_fst_of_mem_precoverage
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (τ : Topology) (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (τ.precoverage.{u, v} B S hS)]
    {X Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (hf : P f)
    {R : Presieve Y} (hR : R ∈ τ.precoverage.{u, v} B S hS Y) (hg : R g) :
    P (ObjectProperty.homMk (pullback.fst g.hom f.hom) :
      AlgebraicSpaces.fiberProduct B S hS g f ⟶ Y') := by
  have hFP := AlgebraicSpaces.isPullback_fiberProduct B S hS g f
  have : HasPullback f g := hFP.flip.hasPullback
  convert (P.cancel_left_of_respectsIso (hFP.isoPullback ≪≫ pullbackSymmetry g f).hom
    (pullback.snd f g)).mpr (MorphismProperty.IsLocalAtTarget.pullbackSnd (P := P)
      (K := τ.precoverage.{u, v} B S hS) hR hg hf) using 1
  rw [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd, hFP.isoPullback_hom_fst]

/-- A morphism of algebraic spaces over `S` of the kind belonging to `τ` is a member of a
`τ`-covering presieve of its target. -/
theorem exists_mem_precoverage_containing
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (τ : Topology) {Y Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ Y)
    (hg : match τ with
      | .fpqc => IsFlat B S hS g.hom
      | .fppf => IsFlat B S hS g.hom ∧ IsLocallyOfFinitePresentation B S hS g.hom
      | .syntomic => IsSyntomic B S hS g.hom
      | .smooth => IsSmooth B S hS g.hom
      | .etale => IsEtale B S hS g.hom) :
    ∃ (Yi : ULift.{v, 0} Bool → AlgebraicSpaces B S hS) (q : ∀ i, Yi i ⟶ Y),
      Presieve.ofArrows Yi q ∈ τ.precoverage.{u, v} B S hS Y ∧ Presieve.ofArrows Yi q g := by
  let Yi : ULift.{v, 0} Bool → AlgebraicSpaces B S hS := fun i => if i.down then Y else Y'
  let q : ∀ i, Yi i ⟶ Y := fun i => match i with
    | ULift.up false => g
    | ULift.up true => 𝟙 Y
  have hsource : ∀ i, IsAlgebraicSpace B S hS (Yi i).obj := by
    intro ⟨i⟩; cases i <;> simp [Yi, Y.property, Y'.property]
  have hsurj : (⋃ i, Set.range (pointsMap B S hS (Yi i).obj (q i).hom)) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨ULift.up true, x, ?_⟩
    simp [Yi, q]
  have hcover : Topology.IsCovering τ B S hS (fun i => (Yi i).obj) (fun i => (q i).hom) := by
    cases τ with
    | fpqc =>
        have hId := isFpqcCovering_of_isIso.{u, v} B S hS (𝟙 Y.obj)
        refine ⟨Y.property, hsource, fun ⟨i⟩ => ?_, fun T h => ?_⟩
        · cases i
          exacts [hg, hId.1 PUnit.unit]
        · obtain ⟨U, hfinite, hmem, hfactor⟩ := hId.2 T h
          refine ⟨U, hfinite, hmem, fun j => ?_⟩
          obtain ⟨_, a, ha⟩ := hfactor j
          exact ⟨ULift.up true, a, ha⟩
    | fppf =>
        have hId := isFppfCovering_of_isIso.{u, v} B S hS Y.obj Y.obj (𝟙 Y.obj) Y.property
        refine ⟨Y.property, hsource, Y.property, hsource, fun ⟨i⟩ => ?_, fun ⟨i⟩ => ?_, hsurj⟩
        · cases i
          exacts [hg.1, hId.flat PUnit.unit]
        · cases i
          exacts [hg.2, hId.locallyOfFinitePresentation PUnit.unit]
    | syntomic =>
        have hId := isSyntomicCovering_of_isIso B S hS (𝟙 Y.obj) Y.property
        refine ⟨Y.property, hsource, Y.property, hsource, fun ⟨i⟩ => ?_, hsurj⟩
        cases i
        exacts [hg, hId.syntomic ()]
    | smooth =>
        have hId := isSmoothCovering_of_isIso B S hS (𝟙 Y.obj) Y.property
        refine ⟨Y.property, hsource, Y.property, hsource, fun ⟨i⟩ => ?_, hsurj⟩
        cases i
        exacts [hg, hId.smooth ()]
    | etale =>
        have hId := isEtaleCovering_of_isIso B S hS (𝟙 Y.obj) Y.property
        refine ⟨Y.property, hsource, Y.property, hsource, fun ⟨i⟩ => ?_, hsurj⟩
        cases i
        exacts [hg, hId.etale ()]
  exact ⟨Yi, q, ⟨ULift.{v, 0} Bool, Yi, q, rfl, hcover⟩,
    Presieve.ofArrows.mk' (ULift.up false) rfl (by rfl)⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- A property of morphisms of algebraic spaces over `S` which is local on the base for `τ` is
inherited by the base change along any morphism of the kind belonging to `τ`. -/
@[stacks 06EM]
theorem prop_fiberProduct_fst_of_isLocalAtTarget
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (τ : Topology) (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (τ.precoverage.{u, v} B S hS)]
    {X Y Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hf : P f)
    (hg : match τ with
      | .fpqc => IsFlat B S hS g.hom
      | .fppf => IsFlat B S hS g.hom ∧ IsLocallyOfFinitePresentation B S hS g.hom
      | .syntomic => IsSyntomic B S hS g.hom
      | .smooth => IsSmooth B S hS g.hom
      | .etale => IsEtale B S hS g.hom) :
    P (ObjectProperty.homMk (pullback.fst g.hom f.hom) :
      AlgebraicSpaces.fiberProduct B S hS g f ⟶ Y') := by
  obtain ⟨Yi, q, hR, hgm⟩ := exists_mem_precoverage_containing.{u, v} B S hS τ g hg
  exact prop_fiberProduct_fst_of_mem_precoverage B S hS τ P f g hf hR hgm

end AlgebraicGeometry.Space

end
