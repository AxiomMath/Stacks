module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupSmoothCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnitySmoothProjectiveCurve
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomologyVanishing

/-!
# The higher cohomology of `𝐆_m` on the size-bounded small étale site of a smooth curve

[Stacks, Tag 03RM] — `H^q_ét(X, 𝐆_m) = 0` for `q ≥ 2` on a smooth curve over an algebraically
closed field — is proved in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/MultiplicativeGroupHigherVanishing.lean`
as `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve`, on *Mathlib's*
small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology` and for
`Stacks.Kummer.multiplicativeSheaf`, whose coefficients are `AddCommGrpCat.{max (u + 1) v}`.
The Kummer-sequence computation of [Stacks, Tag 03RQ] runs instead on the size-bounded small
étale site `AlgebraicGeometry.SmallEtale.topology` of [Stacks, Tag 021B] and for
`AlgebraicGeometry.unitsPresheaf`, whose coefficients are `AddCommGrpCat.{u}`.

This file carries the vanishing across that gap, unconditionally.

## Why the coefficient universes need not agree

`Stacks.Kummer.multiplicativePresheaf` is the units presheaf postcomposed with
`AddCommGrpCat.uliftFunctor`, and `AlgebraicGeometry.unitsPresheaf` is the units presheaf
itself, so the two coefficient universes are indeed never equal.  They do not have to be:
restriction along a dense subsite inclusion is precomposition with the functor, which commutes
with postcomposition on coefficients, so the restriction of `𝐆_m` from Mathlib's site is
*definitionally* the coefficient-universe lift of `𝐆_m` on the size-bounded site — and
`Stacks.Cohomology.CoefficientLift.subsingleton_cohomology_of_ulift` says that a sheaf and its
coefficient-universe lift have the same vanishing.  Two steps, in that order:

* the site comparison, at the *upper* coefficient universe `AddCommGrpCat.{u + 1}`, by
  `AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`;
* the descent of the coefficient universe, on the size-bounded site, from `AddCommGrpCat.{u + 1}`
  to `AddCommGrpCat.{u}`.

## Main results

* `AlgebraicGeometry.boundedSmallEtaleUlift_properties`: on the size-bounded small étale site the
  universe lift of the coefficients is compatible with sheafification and preserves injective
  objects — the two hypotheses of the coefficient-universe comparison.  The site is essentially
  `u`-small (`AlgebraicGeometry.SmallEtale.essentiallySmall`), so its own small model serves as
  the small dense subsite that
  `Stacks.Cohomology.CoefficientLift.sheafUlift_properties_of_small_subsite` asks for.
* `AlgebraicGeometry.subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve`: **the vanishing**, in
  the exact shape the Kummer computation of [Stacks, Tag 03RQ] carries as a hypothesis.

## What is and is not proved

No tag attribute is placed here.  [Stacks, Tag 03RM] is not restated: it is *consumed*, from
`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve`, which keeps
its own registration; what is added is the transport, which is site theory and no mathematics of
the source.  The consumers of the transported form are the [Stacks, Tag 03RQ] registrations in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Curves/RootsOfUnityAllDegreesGmVanishing.lean`.

The dense-subsite transport itself is consumed too, not restated: it is
`Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_H_restriction_of_isDenseSubsite`, which
carries the vanishing of the cohomology of an arbitrary abelian sheaf from a site to a dense
subsite.

## References

* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
* [Stacks Project, Tag 03RQ](https://stacks.math.columbia.edu/tag/03RQ)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Stacks.Cohomology.CoefficientLift

universe w w' a v₁ u₁ v₂ u₂ t u

namespace AlgebraicGeometry

/-- **Universe lifting of abelian coefficients on the size-bounded small étale site is
compatible with sheafification and preserves injective objects.**  These are the two hypotheses
of `Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv`, and neither is formal: the universe
lift of abelian groups has no left adjoint.  Both are proved on a small dense subsite and
transported, and the site of [Stacks, Tag 021B] supplies such a subsite out of itself, being
essentially `u`-small by `AlgebraicGeometry.SmallEtale.essentiallySmall`. -/
theorem boundedSmallEtaleUlift_properties
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (SmallEtale.topology B S hS).PreservesSheafification AddCommGrpCat.uliftFunctor.{t, u} ∧
    (sheafCompose (SmallEtale.topology B S hS)
      AddCommGrpCat.uliftFunctor.{t, u}).PreservesInjectiveObjects := by
  let A := SmallEtale B S hS
  let e := equivSmallModel.{u} A
  let J := SmallEtale.topology B S hS
  let J₀ := e.inverse.inducedTopology J
  have : (e.inverse.sheafPushforwardContinuous AddCommGrpCat.{u} J₀ J).IsEquivalence :=
    (e.sheafCongr J J₀ AddCommGrpCat.{u}).isEquivalence_functor
  have : (e.inverse.sheafPushforwardContinuous AddCommGrpCat.{max u t} J₀ J).IsEquivalence :=
    (e.sheafCongr J J₀ AddCommGrpCat.{max u t}).isEquivalence_functor
  exact sheafUlift_properties_of_small_subsite.{u, t} J₀ J e.inverse

/-- The final object `S / S` of the size-bounded small étale site of [Stacks, Tag 021D] is
carried by the embedding to a terminal object of Mathlib's small étale site, namely the identity
of `S`. -/
private def isTerminal_toEtaleSite_final (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    IsTerminal ((SmallEtale.toEtaleSite B S hS).obj (SmallEtale.final B S hS)) :=
  have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    ⟨fun _ => inferInstance⟩
  MorphismProperty.Over.mkIdTerminal _ _

section

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- `Ext` of abelian sheaves on the size-bounded small étale site at the universe of the objects
of that site.  Instance search does not reach this on its own, the general instance being
indexed by a `max`. -/
local instance hasExt_boundedSmallEtale_objectUniverse :
    HasExt.{u + 1} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :=
  smallEtaleSheaf_hasExt B X hX

/-- The universe lift of the coefficients preserves injective abelian sheaves on the size-bounded
small étale site, from the morphism universe of the site to its object universe. -/
local instance preservesInjectiveObjects_uliftFunctor_boundedSmallEtale :
    (sheafCompose (SmallEtale.topology B X hX)
      AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesInjectiveObjects :=
  (boundedSmallEtaleUlift_properties B X hX).2

/-- **`H^q_ét(X, 𝐆_m) = 0` for `q ≥ 2` on the size-bounded small étale site of a smooth curve
over an algebraically closed field, at coefficients `AddCommGrpCat.{u}`** — the middle term of
the Kummer sequence `AlgebraicGeometry.kummerSmallEtale` being the sheaf of units there.
Unconditional: no hypothesis is carried.

This is [Stacks, Tag 03RM] transported, not restated.  The mathematics is
`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve`, which proves it on
Mathlib's small étale site for `Stacks.Kummer.multiplicativeSheaf` at coefficients
`AddCommGrpCat.{u + 1}`; what is added here is the two-step transport.  Restriction along
`AlgebraicGeometry.SmallEtale.toEtaleSite` carries `Stacks.Kummer.multiplicativeSheaf` to the
coefficient-universe lift of the middle term of `AlgebraicGeometry.kummerSmallEtale` *on the
nose*, both being the units presheaf precomposed with a functor of sites and postcomposed with
`AddCommGrpCat.uliftFunctor`; so the site comparison runs at the upper coefficient universe and
the coefficient universe then descends on the size-bounded site alone. -/
theorem subsingleton_sheafH_kummerSmallEtale_X₂_smoothCurve
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsCurve k g] [Smooth g] (B : BigEtaleSite.{u}) (hX : B.Contains X) (n : ℕ)
    [HasExt.{t} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{t} (kummerSmallEtale B X hX n).X₂ q) := by
  have h1 := Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve g q hq
  have h2 : Subsingleton (Sheaf.H.{u + 1}
      ((sheafCompose (SmallEtale.topology B X hX)
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (kummerSmallEtale B X hX n).X₂) q) :=
    Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_H_restriction_of_isDenseSubsite
      (SmallEtale.topology B X hX) X.smallEtaleTopology (SmallEtale.toEtaleSite B X hX)
      (SmallEtale.finalIsTerminal B X hX) (isTerminal_toEtaleSite_final B X hX)
      (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) q h1
  exact subsingleton_cohomology_of_ulift.{u, t, u + 1, u + 1, u, u + 1}
    (SmallEtale.topology B X hX) (kummerSmallEtale B X hX n).X₂ q h2

end

end AlgebraicGeometry

end
