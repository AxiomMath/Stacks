module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.PointBlowupSequence
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.BaseChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.Fibre
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.BaseChangeEquivalenceSupplement

/-!
# Further results on `PointBlowupSequence`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.PointBlowupSequence`
that need imports beyond those of that module.

## Main results

All names are in the namespace `AlgebraicGeometry.FinitePresentationAwayPointsSituation`.

* `factorsAsPointBlowups_of_corresponds_finitePresentationAway`: the necessity direction of
  [Stacks, Tag 0BFY] for the base-change functor of [Stacks, Tag 0BFU].
* `factorsAsPointBlowups_of_baseChange_iso_unconditional`: a modification of `S` supported at the
  distinguished points factors as a finite sequence of blowups at closed points lying over them
  as soon as a modification with isomorphic localizations does.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

open Stacks.ResolutionOfSurfaces

namespace FinitePresentationAwayPointsSituation

/-- **Stacks Project, Tag 0BFY**, necessity. If `f : X ⟶ S` factors as a finite sequence of
blowups at closed points lying over the distinguished points, then every local modification
`g i : Y i ⟶ Spec 𝒪_{S, s i}` corresponding to it under the base-change functor `F` of
[Stacks, Tag 0BFU] factors as a finite sequence of blowups at closed points lying over the closed
point. -/
theorem factorsAsPointBlowups_of_corresponds_finitePresentationAway
    (D : FinitePresentationAwayPointsSituation.{u}) (X : D.globalCategory) (i : Fin D.n)
    (Y : D.localCategory i)
    (hY : (finitePresentationAwayPointsBaseChange D).functor.obj X i ≅ Y)
    (h : FactorsAsPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom) :
    FactorsAsPointBlowups (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} Y.obj.left Y.obj.hom :=
  D.factorsAsPointBlowups_of_corresponds
    (finitePresentationAwayPointsBaseChange D) X i Y hY h

/-- **Stacks Project, Tag 0BFY**, sufficiency, the step supplied by Tag 0BFV. A modification of
`S` supported at the distinguished points is determined by its localizations: if the
localizations of `Z` and of `X` agree and `Z` factors as a finite sequence of blowups at closed
points lying over the distinguished points, then so does `X`. -/
theorem factorsAsPointBlowups_of_baseChange_iso_unconditional
    (D : FinitePresentationAwayPointsSituation.{u}) (BC : BaseChangeFunctor D)
    {X Z : D.globalCategory} (hXZ : BC.functor.obj Z ≅ BC.functor.obj X)
    (hZ : FactorsAsPointBlowups D.S (Set.range D.points) Z.obj.left Z.obj.hom) :
    FactorsAsPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom :=
  have : BC.functor.IsEquivalence := BC.isEquivalence_unconditional
  factorsAsPointBlowups_of_overIso
    ((ObjectProperty.ι (IsFinitePresentationAway D.complement)).mapIso
      (BC.functor.preimageIso hXZ).symm) hZ

end FinitePresentationAwayPointsSituation

end AlgebraicGeometry
