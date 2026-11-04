module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackWithEnoughPoints
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkRetractFromFreeModules

/-!
# Pullback of K-flat complexes on ringed topoi with enough points, on one input

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi.  If `C` has enough points,
then the degreewise pullback of a K-flat complex of `O'`-modules is a K-flat complex of
`O`-modules.  This is Stacks 0DEP, and the source deduces it from three inputs: Stacks 0DEN,
Modules on Sites 05V5, and More on Algebra 06Y1.

Of those three, two are now available with the hypotheses of the source and nothing more:
Stacks 06Y1 is `kFlat_baseChange`, and **both parts of Stacks 0DEN** are proved — part (2) as
`Stacks.SheafOfModules.SitePointStalkSheafify.kFlat_of_stalks` and part (1) as
`Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat_unconditional`.  This file feeds part
(1) into the deduction, so that the K-flatness assertion of Stacks 0DEP rests on Stacks 05V5
alone.

## Main results

* `Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints.stalkKFlat`: part (1) of
  Stacks 0DEN in the shape the deduction consumes — a K-flat complex of modules on a ringed
  topos has K-flat stalk complex at every point of the site.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints.kFlat_pullbackComplex_of_enoughPoints`:
  the K-flatness assertion of Stacks 0DEP, granted Stacks 05V5 at the level of complexes and
  nothing else.

## Implementation notes

**The deduction.**  K-flatness of `f^*K` is tested at a point `Φ` of the source site by part (2)
of Stacks 0DEN, which applies because the source site has a conservative family of points.
There the stalk complex of `f^*K` is an extension of scalars of a stalk complex of `K`, which is
K-flat by part (1) of Stacks 0DEN on the target topos; and extension of scalars preserves
K-flatness, which is Stacks 06Y1.  The two parts of Stacks 0DEN are used at two different ringed
topoi and under different hypotheses — part (2) on the source, which is the one assumed to have
enough points, part (1) on the target, about whose points nothing is assumed — so neither can
replace the other.

**Why no tag is placed here.**  The results below carry Stacks 05V5
— the stalk of a module pullback is the base change of the stalk along the stalk ring map — as
the hypothesis `PullbackStalkBaseChange`, so a `0DEP` tag on them would be a weakening and none
is placed.  But that hypothesis is *not* unreachable: three apparent obstructions are recorded below
with their refutations, the reasoning being worth keeping and the conclusion not.

* *The point of the target.*  One might argue that no point `Ψ` of the target site is reachable,
  because the two transports of points available are
  `CategoryTheory.GrothendieckTopology.Point.comap` along a representably flat cover-preserving
  functor and `CategoryTheory.GrothendieckTopology.Point.map` along a cocontinuous one, while an
  `AlgebraicGeometry.RingedToposSiteHom` carries only continuity of its underlying functor — and
  neither representable flatness nor cocontinuity follows from that, nor from
  `CategoryTheory.Functor.IsMorphismOfSites`, whose finite-limit conditions are on the induced
  pullback of sheaves rather than on the functor.  All of that is true and none of it binds: the
  point is transported through the *topos*, not through a functor of sites.  A point `Φ` of the
  source site is a point of the source topos by Stacks 00YA part (1); its composite with the
  underlying morphism of topoi is a point `q = f ∘ Φ` of the target topos (Stacks 05V2); and
  Stacks 00YA part (2) presents `q` by a point of the target *site* whose stalk functor is
  `f⁻¹ ⋙ Φ.sheafFiber` up to a canonical isomorphism.  That is
  `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.targetPoint` for a morphism of
  sites, and `Stacks.Sheaves.StalkPullback.targetSitePoint` for an arbitrary morphism of ringed
  topoi.
* *The base change at the stalk.*  Granted `Ψ`, the module-level comparison
  `(f^*M)_Φ ≅ M_Ψ ⊗_{O'_Ψ} O_Φ` might seem unavailable, reachable only by the route used on
  ringed *spaces* in `Stacks.RingedSpace.stalkModulePullbackFunctorIso`, which needs a module
  skyscraper over a point of a site.  It is in fact available without one:
  `Stacks.Sheaves.StalkPullback.stalkFunctorIso` at a matched pair of points,
  `Stacks.Sheaves.StalkPullback.pointStalkFunctorIso` at a bare point of an arbitrary morphism
  of ringed topoi, and
  `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.stalkFunctorIso` at the point of
  the target site produced above — whose complex-level form `stalkComplexIso` inhabits
  `StalkBaseChange`, hence `PullbackStalkBaseChange`.  Stacks 0DEP is accordingly tagged, with
  that hypothesis discharged rather than assumed, in
  `StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkBaseChangeAtTheTargetPoint`.
* *The ringed-point square.*  The route through
  `AlgebraicGeometry.RingedToposHom.pullbackModulesSquareIso` does still want a morphism of
  ringed points over `Ψ = f ∘ Φ` and a composition for the four-field
  `Stacks.Sheaves.RingedToposModules.RingedToposHom`, and neither exists.  Nothing above goes
  through it.

**The morphism and the universes.**  Both are as in
`Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints.kFlat_pullback_of_enoughPoints`: the
morphism is spelled with `AlgebraicGeometry.RingedToposSiteHom`, which is the generality in which
the module pullback of Stacks 03D6 part (2) is defined here, and both ringed topoi are taken at
`AlgebraicGeometry.RingedTopos.{u, u, u}`, a narrowing forced independently by
`SheafOfModules.pullback` and by both parts of Stacks 0DEN.

## References

* [Stacks Project, Tag 0DEP](https://stacks.math.columbia.edu/tag/0DEP)
* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints

/-! ### Part (1) of Stacks 0DEN on a ringed topos -/

/-- **Part (1) of Stacks 0DEN at a ringed topos.**  A K-flat complex of `O`-modules has K-flat
stalk complex at every point of the site.

This is `Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat_unconditional` packaged as the
predicate `StalkKFlat`, which the deduction of Stacks 0DEP consumes on the *target* ringed
topos.  No tag is placed here: the statement is part (1) of Stacks 0DEN restated at a ringed
topos rather than a ringed site, and the tag sits on the ringed-site form. -/
theorem stalkKFlat (Z : AlgebraicGeometry.RingedTopos.{u, u, u})
    [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [HasWeakSheafify Z.J AddCommGrpCat.{u}]
    [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Stacks.SheafOfModules.Tensor.sheafTensor Z.O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Z.O).obj M).Additive]
    [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
        (ComplexShape.up ℤ)] :
    StalkKFlat Z :=
  fun K hK Φ ↦
    Stacks.Sheaves.KFlatStalkCriterion.kFlatStalk_of_kFlat_unconditional Z.O Φ K hK

/-! ### The K-flatness assertion of Stacks 0DEP on Stacks 05V5 alone -/

section Pullback

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The K-flatness assertion of Stacks 0DEP, granted Stacks 05V5 at the level of complexes
and nothing else.**  If the source site has a conservative family of points, the degreewise
pullback along `f` of a K-flat complex of `O_Y`-modules is a K-flat complex of `O_X`-modules.

The proof is the source's, and of its three inputs two are now unconditional: part (2) of
Stacks 0DEN tests K-flatness of `f^*K` at the points of the source site, part (1) of
Stacks 0DEN gives K-flatness of the stalk complexes of `K` on the target, and Stacks 06Y1
carries that along the extension of scalars.  The third input, Stacks 05V5, is the hypothesis
`PullbackStalkBaseChange`.

This declaration carries no tag: `PullbackStalkBaseChange` is a hypothesis Stacks 0DEP does not
have and no declaration in this development inhabits, so it is a weakening.  See the
implementation notes for what inhabiting it needs. -/
theorem kFlat_pullbackComplex_of_enoughPoints (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (hX : X.J.HasConservativeFamily.{u}) (h05V5 : PullbackStalkBaseChange f)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat Y.O K) :
    Stacks.SheafOfModules.IsKFlat X.O ((KFlatPullback.pullbackComplex f).obj K) :=
  kFlat_pullback_of_enoughPoints f hX (stalkKFlat Y) h05V5 K hK

end Pullback

end Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints

end

end
