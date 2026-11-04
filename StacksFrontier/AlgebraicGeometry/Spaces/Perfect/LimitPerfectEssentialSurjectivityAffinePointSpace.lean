module

public import
  StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssentialSurjectivityAffineCase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackAlongIso

/-!
# The affine case of essential surjectivity for Stacks 09RJ, on the base-changed limit itself

In Situation 09RH — a directed inverse system `i ↦ X_i` of quasi-compact quasi-separated
algebraic spaces over a scheme `S` with affine transition morphisms, a chosen limit `X` and a
chosen index `0` — the affine case of the essential-surjectivity half of Stacks 09RJ is proved
in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssentialSurjectivityAffineCase`
as `AlgebraicGeometry.Space.DescentSituation.exists_isPerfect_affineModelStage`, but *about the
chosen affine models*: for an affine point `u : h_U ⟶ X₀` of the chosen stage, the affine models
`V_i` of `X_i ×_{X₀} U` and `V_∞` of `X ×_{X₀} U` are objects of the big fppf site with affine
underlying scheme, chosen together with isomorphisms of algebraic spaces
`AlgebraicGeometry.Space.DescentSituation.affineModelSpaceIso` and `affineModelLimitSpaceIso`,
and that statement quantifies over the perfect objects of `D(𝒪_{h_{V_∞}})` rather than over
those of `D(𝒪_{X ×_{X₀} U})`.

**This file restates it over `D(𝒪_{X ×_{X₀} U})` itself**, which is the form the induction
principle of Stacks 08GP consumes: the predicate being verified is one about the objects of
`(X_0)_{spaces,étale}`, and the base change `X ×_{X₀} U` of the limit is the object the affine
case is about.

## Main results

* `AlgebraicGeometry.Space.DescentSituation.exists_isPerfect_affinePointStage`: **the affine
  case of the essential-surjectivity half of Stacks 09RJ for Situation 09RH, on the base-changed
  limit itself.**  Every perfect object `E` of `D(𝒪_{X ×_{X₀} U})` is, at some stage `j`, the
  derived pullback along the projection `X ×_{X₀} U ⟶ X_j ×_{X₀} U` of a perfect object of
  `D(𝒪_{X_j ×_{X₀} U})`.

Nothing here is tagged: this is the affine case of the induction inside the source's proof of
Stacks 09RJ, not Stacks 09RJ, and the step for an elementary distinguished square is not here.

## How the transport goes

Write `α` for `AlgebraicGeometry.Space.DescentSituation.affineModelLimitSpaceIso`, the chosen
isomorphism `X ×_{X₀} U ≅ h_{V_∞}`, and `β_j` for
`AlgebraicGeometry.Space.DescentSituation.affineModelSpaceIso` at `j`, the chosen isomorphism
`X_j ×_{X₀} U ≅ h_{V_j}`.

* `Lα^{-1*}E` is a perfect object of `D(𝒪_{h_{V_∞}})` by Stacks 08H6,
  `AlgebraicGeometry.Space.isPerfect_smallEtaleDerivedModulePullback`, so the affine case on the
  models produces a stage `j`, a perfect `E_j'` on `h_{V_j}` and an isomorphism
  `Lp_j^*E_j' ≅ Lα^{-1*}E`, where `p_j : h_{V_∞} ⟶ h_{V_j}` is the projection of the models.
* `E_j := Lβ_j^*E_j'` is then perfect on `X_j ×_{X₀} U`, again by Stacks 08H6.
* The required isomorphism `Lπ_j^*E_j ≅ E`, for `π_j : X ×_{X₀} U ⟶ X_j ×_{X₀} U` the
  projection of the base-changed situation, is the composition law of Stacks 0D6D
  (`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso`) applied twice around the
  commuting square `π_j ≫ β_j = α ≫ p_j`, which is
  `AlgebraicGeometry.Space.DescentSituation.projection_comp_affineModelSpaceIso_hom`, and then
  `AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackHomInvIso` to cancel
  `Lα^{-1*}` against `Lα^*`.

## The hypotheses carried, and why each is an input of the source's proof

Exactly the two hypotheses of
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssentialSurjectivityAffineCase`
are carried, and no others; in particular the transport adds none.

*`I : Type u`, the index set of the situation lies in the universe of the site.*  Forced by
`AlgebraicGeometry.Space.DescentSituation.isGlobalFunctionsColimit`, through which Stacks 07SI
for the structure sheaf is proved.  Situation 09RH itself allows an index in any universe.

*`hI : #I < B.cutoff.ord.cof`, the size hypothesis of Stacks 07SF.*  It enters only through the
affineness of `X ×_{X₀} U` and through the colimit of rings, and in the big fppf sites of this
library it is not removable:
`AlgebraicGeometry.Space.Refute07SQ.not_forall_exists_isAffineSpace_system_obj` of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineStageLargeIndexCounterexample` refutes
the unbounded statement.

`hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)` and the point `u : h_U ⟶ X₀` are not
hypotheses but the data of the case being treated.  No clause of Stacks 09RJ, 09RI or 09RF is
assumed, and no `Prop` binder stands in for missing mathematics.

## What is not here

*The step of the induction of Stacks 08GP for an elementary distinguished square is not here*,
so essential surjectivity for Stacks 09RJ is not concluded.  See "What is not here" in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssentialSurjectivityAffineModels`
for what that step needs.

## References

* [Stacks Project, Lemma 75.24.3 (Tag 09RJ)](https://stacks.math.columbia.edu/tag/09RJ)
* [Stacks Project, Situation 75.24.1 (Tag 09RH)](https://stacks.math.columbia.edu/tag/09RH)
* [Stacks Project, Lemma 75.9.3 (Tag 08GP)](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Lemma 70.5.1 (Tag 07SF)](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Lemma 75.14.2 (Tag 08H6)](https://stacks.math.columbia.edu/tag/08H6)
* [Stacks Project, Lemma 20.42.? (Tag 0D6D)](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  {D : DescentSituation B S hS hZ I} {U : BigFppfOver B S hS}
  (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
  (u : yoneda.obj U ⟶ (stagesSystem D).obj (op (baseStage D)))
  (hI : #I < B.cutoff.ord.cof)

attribute [local instance 10000] HasDerivedCategory.standard

include hI in
/-- **The affine case of the essential-surjectivity half of Stacks 09RJ, for Situation 09RH, on
the base-changed limit itself.**

Let `U` be an object of `(X_0)_{étale}` with affine underlying scheme, given by an affine object
of the big fppf site over `S` and a point `u : h_U ⟶ X₀` of the chosen stage.  Then every
perfect object `E` of `D(𝒪_{X ×_{X₀} U})` is, at some stage `j`, the derived pullback along the
projection `X ×_{X₀} U ⟶ X_j ×_{X₀} U` of a perfect object of `D(𝒪_{X_j ×_{X₀} U})`.

This is `AlgebraicGeometry.Space.DescentSituation.exists_isPerfect_affineModelStage`, which says
the same for the chosen affine models of these spaces, transported along the chosen isomorphisms
`AlgebraicGeometry.Space.DescentSituation.affineModelLimitSpaceIso` and `affineModelSpaceIso`;
the square the transport consumes is
`AlgebraicGeometry.Space.DescentSituation.projection_comp_affineModelSpaceIso_hom`.  Only the
two hypotheses of this file's module documentation are carried, the same two the statement about
the models carries.

Nothing here is tagged: the step of the induction for an elementary distinguished square is
absent, so this is a case of the source's proof and not Stacks 09RJ. -/
theorem exists_isPerfect_affinePointStage
    (E : DerivedCategory (Modules.{u, u} B S hS (affinePointSituation D hU u).limitSpace.obj
      (affinePointSituation D hU u).limitSpace.property))
    (hE : (smallEtaleRingedSite B S hS (affinePointSituation D hU u).limitSpace.obj
      (affinePointSituation D hU u).limitSpace.property).IsPerfect E) :
    ∃ (j : D.Stages) (Ej : DerivedCategory (Modules.{u, u} B S hS
        ((affinePointSituation D hU u).stage j).obj
        ((affinePointSituation D hU u).stage j).property)),
      (smallEtaleRingedSite B S hS ((affinePointSituation D hU u).stage j).obj
          ((affinePointSituation D hU u).stage j).property).IsPerfect Ej ∧
        Nonempty ((smallEtaleDerivedModulePullback B S hS
          ((affinePointSituation D hU u).projection j)).obj Ej ≅ E) := by
  obtain ⟨j, Ej, hEj, ⟨ι⟩⟩ := exists_isPerfect_affineModelStage hU u hI
    ((smallEtaleDerivedModulePullback B S hS (affineModelLimitSpaceIso hU u hI).inv).obj E)
    (isPerfect_smallEtaleDerivedModulePullback (affineModelLimitSpaceIso hU u hI).inv E hE)
  refine ⟨j, (smallEtaleDerivedModulePullback B S hS (affineModelSpaceIso hU u j).hom).obj Ej,
    isPerfect_smallEtaleDerivedModulePullback (affineModelSpaceIso hU u j).hom Ej hEj, ⟨?_⟩⟩
  exact (smallEtaleDerivedModulePullbackCompIso B S hS
        ((affinePointSituation D hU u).projection j) (affineModelSpaceIso hU u j).hom).app Ej ≪≫
    (smallEtaleDerivedModulePullbackCongr B S hS
        (projection_comp_affineModelSpaceIso_hom hU u hI j)).app Ej ≪≫
      (smallEtaleDerivedModulePullbackCompIso B S hS (affineModelLimitSpaceIso hU u hI).hom
        (representedSpaceMap B S hS (affineModelProj hU u hI j))).symm.app Ej ≪≫
        (smallEtaleDerivedModulePullback B S hS
            (affineModelLimitSpaceIso hU u hI).hom).mapIso ι ≪≫
          (smallEtaleDerivedModulePullbackHomInvIso B S hS
            (affineModelLimitSpaceIso hU u hI)).app E

end DescentSituation

end AlgebraicGeometry.Space

end
