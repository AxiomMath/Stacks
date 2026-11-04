module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaLocalizationOnTheBase

/-!
# The two legs of the base-change diagram of the projection formula

For abstract functors standing in for derived pullback, pushforward and tensor product, this file
proves that the left-hand leg of the diagram of [Stacks, Tag 0B6B], and its right-hand leg after
the projection-formula morphism, are isomorphisms once each of their constituent maps is.

## References

* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.DerivedProjectionFormula

universe u

attribute [local instance] HasDerivedCategory.standard

section Abstract

variable {P P' Q Q' : Type*} [Category P] [Category P'] [Category Q] [Category Q']

/-- **The left-hand leg of the diagram of [Stacks, Tag 0B6B] is invertible.**  It is the
comparison of [Stacks, Tag 079U] for `g` at `(Rf E, K)`, then the base-change map at `E` in the
first tensor factor, then the projection-formula morphism for the other vertical edge; the middle
map is `AP'` applied to a pair one component of which is `bcE` and the other an identity. -/
lemma isIso_projectionFormulaBaseChangeSquare_lhs (Rf : Q ⥤ P) (Rf' : Q' ⥤ P')
    (Lg : P ⥤ P') (Lg' : Q ⥤ Q') (AP : P × P ⥤ P) (AP' : P' × P' ⥤ P')
    (αg : AP ⋙ Lg ⟶ Lg.prod Lg ⋙ AP') (E : Q) (K : P)
    (bcE : Lg.obj (Rf.obj E) ⟶ Rf'.obj (Lg'.obj E)) {W : P'}
    (p' : AP'.obj (Rf'.obj (Lg'.obj E), Lg.obj K) ⟶ W)
    (hαg : IsIso (αg.app (Rf.obj E, K))) (hbcE : IsIso bcE) (hp' : IsIso p') :
    IsIso (αg.app (Rf.obj E, K) ≫ AP'.map (bcE ×ₘ 𝟙 (Lg.obj K)) ≫ p') := by
  have : IsIso (bcE ×ₘ 𝟙 (Lg.obj K)) := ((asIso bcE).prod (Iso.refl (Lg.obj K))).isIso_hom
  infer_instance

/-- **The right-hand leg of the diagram of [Stacks, Tag 0B6B], after the projection-formula
morphism, is invertible.**  It is the base-change map at `AQ (E, Lf K)`, then `Rf'` of the
comparison of [Stacks, Tag 079U] for `g'` followed by the identification of the two iterated
pullbacks in the second tensor factor. -/
lemma isIso_projectionFormulaBaseChangeSquare_tail (Rf' : Q' ⥤ P') (Lf : P ⥤ Q)
    (Lf' : P' ⥤ Q') (Lg : P ⥤ P') (Lg' : Q ⥤ Q') (AQ : Q × Q ⥤ Q) (AQ' : Q' × Q' ⥤ Q')
    (αg' : AQ ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ AQ') (E : Q) (K : P) {V : P'}
    (bc : V ⟶ Rf'.obj (Lg'.obj (AQ.obj (E, Lf.obj K))))
    (c : Lg'.obj (Lf.obj K) ⟶ Lf'.obj (Lg.obj K))
    (hbc : IsIso bc) (hαg' : IsIso (αg'.app (E, Lf.obj K))) (hc : IsIso c) :
    IsIso (bc ≫ Rf'.map (αg'.app (E, Lf.obj K) ≫ AQ'.map (𝟙 (Lg'.obj E) ×ₘ c))) := by
  have : IsIso (𝟙 (Lg'.obj E) ×ₘ c) := ((Iso.refl (Lg'.obj E)).prod (asIso c)).isIso_hom
  infer_instance

end Abstract

/-! ### A commutative square of ringed spaces -/

section RingedSpaces

variable {X' X Y' Y : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  (sq : g' ≫ f = f' ≫ g)
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

end RingedSpaces

/-! ### A Cartesian square of schemes over an open of the base -/

section Schemes

variable {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X'.toRingedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.toRingedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.toRingedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toRingedSpace.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y'.toRingedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y'.toRingedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.toRingedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.toRingedSpace.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

end Schemes

end Stacks.Cohomology.DerivedProjectionFormula

end
