module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductRepresentableEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CoproductRepresentableEtaleConsequences
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcompositionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCoverRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChangeRefined
import all StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition
import all StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover

/-!
# Stacks 0AJ9 with the assertions about coproducts and about reductions supplied

Let `S` be a scheme contained in a big fppf site `B`. **Stacks 0AJ9** states the equivalence of
three conditions on a formal algebraic space `X` over `S`, and
`StacksFrontier/AlgebraicGeometry/FormalSpace/QuasiCompactSpaceCriteria.lean` proves the three
implications it needs, two of them on an auxiliary assertion carried as a hypothesis:
`AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale` for the implication (2) ⇒ (3) and
`AlgebraicGeometry.FormalSpace.ReductionsOfEtaleSurjectionsEtaleSurjective` for the implication
(3) ⇒ (1). This file supplies what the library now has for each of them.

The first is supplied outright. `AlgebraicGeometry.FormalSpace.coproductsRepresentableEtale`
proves `CoproductsRepresentableEtale`, so the implication (2) ⇒ (3) holds with nothing assumed
beyond the setting of the tag. It cannot be stated that way where it is proved:
`StacksFrontier/AlgebraicGeometry/FormalSpace/CoproductRepresentableEtale.lean` imports
`StacksFrontier/AlgebraicGeometry/FormalSpace/QuasiCompactSpaceCriteria.lean`, so the reverse
import would be a cycle. The implication is stated unconditionally downstream of both, as
`AlgebraicGeometry.FormalSpace.isQuasiCompactSpace_of_hasFiniteFormalAtlas` in
`StacksFrontier/AlgebraicGeometry/FormalSpace/CoproductRepresentableEtaleConsequences.lean`, which
this file imports.

The second is supplied only in part, and the part that is missing is not a theorem. The
assertion `ReductionsOfEtaleSurjectionsEtaleSurjective` has two conjuncts about the morphism of
reductions `g : Yred ⟶ Zred` induced by a morphism `c : Y ⟶ Z` which is representable by
algebraic spaces, étale and a surjection of sheaves:

* that `g` be étale, which is `AlgebraicGeometry.FormalSpace.IsReduction.isEtaleULift_map`
  below, assuming nothing beyond the two reductions and the hypotheses on `c`;
* that `g` satisfy `AlgebraicGeometry.Space.HasSchemePropertyULift` at surjectivity of
  morphisms of schemes. That condition is `MorphismProperty.relative` along the universe-lifted
  Yoneda embedding, so it asserts in particular that `g` is *representable by objects of the
  site*, and that does not follow: `g` is, by
  `AlgebraicGeometry.FormalSpace.IsReduction.pullback_of_smooth`, the base change of `c` along
  the inclusion of the reduction of `Z`, so its represented base changes are the represented
  base changes of `c`, which the hypothesis on `c` makes algebraic spaces and not schemes. What
  Stacks 0AJ9 asserts of `g` is that it be a surjective morphism of *algebraic spaces*, which
  for a morphism representable by algebraic spaces is surjectivity on points by Stacks 03ME and
  is **Stacks 0GB8**,
  `AlgebraicGeometry.FormalSpace.hasPropertyULift_isSurjectiveULift_iff_isSurjectiveULift_red`.

So only the étale conjunct is proved here, and
`AlgebraicGeometry.FormalSpace.ReductionsOfEtaleSurjectionsEtaleSurjective` stays a hypothesis
of the implication (3) ⇒ (1) and of the equivalence.

## Main results

* `AlgebraicGeometry.FormalSpace.IsReduction.isEtaleULift_map`: the morphism of reductions
  induced by a morphism which is representable by algebraic spaces and étale is étale.

## Implementation notes

`IsReduction.isEtaleULift_map` is the assertion of **Stacks 0DED** that the induced morphism of
reductions is étale, which the library carries for a *chosen* reduction as
`AlgebraicGeometry.FormalSpace.Reduction.isEtale_map`. That form does not apply here: its
reductions are `AlgebraicGeometry.FormalSpace.Reduction` data, whose source is the universe lift
of an algebraic space over `S` with values in `Type u`, while the reductions of
`ReductionsOfEtaleSurjectionsEtaleSurjective` are arbitrary fppf sheaves, with values in
`Type (u + 1)`, carrying the predicate `AlgebraicGeometry.FormalSpace.IsReduction`; and its
conclusion is étaleness in the value universe of the site rather than
`AlgebraicGeometry.Space.IsEtaleULift`. The argument is the one of Stacks 0DED, and no part of
it is reproved: Stacks 0GB7 identifies the reduction of `Y` with `Y ×_Z Zred`, so `g` is the
second projection of that fibre product up to the comparison isomorphism, and that projection is
a base change of `c`, hence étale after every represented base change of its target; étaleness
of a morphism whose target is an algebraic space may be checked on one surjective étale chart of
the target, which is
`AlgebraicGeometry.FormalSpace.isEtaleULift_of_targetChart`. Since `Y` and `Z` are not assumed
to be formal algebraic spaces, the form of Stacks 0GB7 used is
`AlgebraicGeometry.FormalSpace.IsReduction.pullback_of_smooth`, which carries no such
hypothesis.

## References

* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0DED](https://stacks.math.columbia.edu/tag/0DED)
* [Stacks Project, Tag 0GB7](https://stacks.math.columbia.edu/tag/0GB7)
* [Stacks Project, Tag 0GB8](https://stacks.math.columbia.edu/tag/0GB8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The étale conjunct of the assertion about reductions -/

/-- **The morphism of reductions induced by a representable étale morphism is étale.** Let
`c : Y ⟶ Z` be a morphism of fppf sheaves on the big fppf site of `S` which is representable by
algebraic spaces and étale, let `iY : Yred ⟶ Y` and `iZ : Zred ⟶ Z` be reductions and let
`g : Yred ⟶ Zred` be compatible with `c`. Then `g` is étale.

This is the étale conjunct of
`AlgebraicGeometry.FormalSpace.ReductionsOfEtaleSurjectionsEtaleSurjective`; the other conjunct
asks `g` to be representable by objects of the site, which does not follow, as the module
docstring explains. Surjectivity of `c` is not used.

A fibre product `Y ×_Z Zred` is a reduction of `Y`, by Stacks 0GB7 in the form
`AlgebraicGeometry.FormalSpace.IsReduction.pullback_of_smooth`, an étale morphism being smooth.
Two reductions of `Y` are isomorphic over `Y`, so the comparison morphism
`k : Yred ⟶ Y ×_Z Zred` is an isomorphism, and `g = k ≫ pullback.snd` because both sides are
factorisations of `iY ≫ c` through `iZ` out of a reduced algebraic space. The projection
`pullback.snd` is a base change of `c`, hence étale after every represented base change of
`Zred`, and that is enough: étaleness of a morphism into an algebraic space may be checked after
base change to one surjective étale chart of the target. -/
theorem IsReduction.isEtaleULift_map {Y Z Yred Zred : FppfSheaf B S hS}
    {c : Y ⟶ Z} {iY : Yred ⟶ Y} {iZ : Zred ⟶ Z} {g : Yred ⟶ Zred}
    (hiY : IsReduction B S hS Y Yred iY) (hiZ : IsReduction B S hS Z Zred iZ)
    (hcrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS c.hom)
    (hcetale : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) c.hom hcrep)
    (hcomm : g ≫ iZ = iY ≫ c) :
    Space.IsEtaleULift.{u + 1} B S hS g.hom := by
  have hsmooth := hasPropertyULift_smooth_of_etale B S hS hcrep hcetale
  have sq : IsPullback (pullback.fst c iZ) (pullback.snd c iZ) c iZ :=
    IsPullback.of_hasPullback c iZ
  have sqh : IsPullback (pullback.fst c iZ).hom (pullback.snd c iZ).hom c.hom iZ.hom :=
    sq.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have hP : IsReduction B S hS Y (pullback c iZ) (pullback.fst c iZ) :=
    IsReduction.pullback_of_smooth B S hS hcrep hsmooth hiZ sq
  set k : Yred ⟶ pullback c iZ := sq.lift iY g hcomm.symm with hk
  have hkfst : k ≫ pullback.fst c iZ = iY := sq.lift_fst _ _ _
  have hksnd : k ≫ pullback.snd c iZ = g := sq.lift_snd _ _ _
  have _ : IsIso k := IsReduction.isIso_of_comp_eq B S hS hiY hP hkfst
  have _ : IsIso k.hom := CategoryTheory.Functor.map_isIso
    (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))) k
  obtain ⟨V, q, hqSurjective, hqEtale⟩ := hiZ.algebraic.exists_atlas
  have hsnd : Space.IsEtaleULift.{u + 1} B S hS (pullback.snd c iZ).hom :=
    isEtaleULift_of_targetChart B S hS hiZ.algebraic _ V q hqSurjective hqEtale
      (isEtaleULift_pullback_fst_of_isPullback B S hS sqh (fun U ξ ↦ hcetale U ξ) V q)
  have hcomp := isEtaleULift_precomp_iso B S hS (asIso k.hom) (pullback.snd c iZ).hom hsnd
  have heq : k.hom ≫ (pullback.snd c iZ).hom = g.hom :=
    congrArg (fun m : Yred ⟶ Zred ↦ m.hom) hksnd
  simpa only [asIso_hom, heq] using hcomp

end AlgebraicGeometry.FormalSpace

end
