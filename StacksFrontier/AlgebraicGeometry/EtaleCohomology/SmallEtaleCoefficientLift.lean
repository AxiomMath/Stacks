module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoefficientUniverseLift

/-!
# The coefficient universe of étale cohomology can be raised freely

Let `X : Scheme.{u}`.  The small étale site of `X` has its objects in `Type (u + 1)` and its
morphisms in `Type u`, so two coefficient universes for abelian sheaves on it are in use in this
chapter: `AddCommGrpCat.{u}`, the morphism universe, where the comparison of étale with Zariski
cohomology of a quasi-coherent module lives, and `AddCommGrpCat.{u + 1}`, the object universe,
where the stalk equivalence of [Stacks, Tag 04JQ] and the Galois-cohomology comparison of
[Stacks, Tag 03QU] live -- the stalk at a geometric point being a colimit over a category whose
objects are in `Type (u + 1)`, which does not exist at `AddCommGrpCat.{u}`.

This file shows the two choices compute the same cohomology: for an abelian sheaf `F` at
coefficients `AddCommGrpCat.{u}`,

  `H ^ n(X_étale, F) ≅ H ^ n(X_étale, F ⋙ uliftFunctor)`.

So a vanishing theorem proved at either coefficient universe holds at the other.

## Main definitions

* `AlgebraicGeometry.smallEtaleSheafHUliftAddEquiv`: **the comparison**.

## Main results

* `AlgebraicGeometry.etaleUlift_properties`: on the small étale site the universe lift of the
  coefficients is compatible with sheafification and preserves injective objects.
* `AlgebraicGeometry.subsingleton_smallEtaleSheafH_ulift_iff`: the two cohomology groups vanish
  together.

## Implementation notes

The two hypotheses that
`Stacks.Cohomology.CoefficientLift.sheafHUliftAddEquiv` needs on the small étale site are
compatibility of the lift with sheafification and preservation of injective objects.  Neither is
formal -- the universe lift of abelian groups has no left adjoint -- and both are obtained by
transporting the corresponding statements along the small dense subsite of `X.AffineEtale`, which
is essentially `u`-small.  Enough injectives at coefficients `AddCommGrpCat.{u}`, the remaining
hypothesis, is
`AlgebraicGeometry.enoughInjectives_sheaf_smallEtaleTopology`.

**The two `Ext` universes are pinned to the two coefficient universes.**  On the lower side the
`Ext` universe is `u`, which is what the quasi-coherent comparison of [Stacks, Tag 03P2] uses;
instance search would pick `u + 1` instead, because
`AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology` is declared after
`CategoryTheory.IsGrothendieckAbelian.hasExt` and so wins, and the priority is therefore flipped
locally exactly as in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/CechComparison/SmallEtaleGlobalCohomology.lean`.
On the upper side it is `u + 1`, supplied by
`Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale` with its coefficient universe
pinned, since the general instance is indexed by `max (u + 1) v` and instance search cannot solve
`max (u + 1) ?v = u + 1`.

## References

* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Stacks.Cohomology.CoefficientLift

universe u v t

namespace AlgebraicGeometry

/-- The affine étale site of a `u`-scheme is essentially `v`-small once `u ≤ v`. -/
public lemma affineEtale_essentiallySmall_of_univLE (X : Scheme.{u}) [UnivLE.{u, v}] :
    EssentiallySmall.{v} X.AffineEtale :=
  (essentiallySmall_iff _).mpr ⟨Small.trans_univLE.{u, v} _, inferInstance⟩

/-- Restriction of abelian sheaves along the small dense subsite `Spec : X.AffineEtale ⥤ X.Etale`
is an equivalence once the coefficients have limits of size `u`. -/
private lemma isEquivalence_sheafPushforwardContinuous_affineEtale_spec (X : Scheme.{u})
    [HasLimitsOfSize.{u, u} AddCommGrpCat.{v}] :
    ((Scheme.AffineEtale.Spec X).sheafPushforwardContinuous AddCommGrpCat.{v}
      (Scheme.AffineEtale.topology X) X.smallEtaleTopology).IsEquivalence :=
  Functor.isEquivalence_of_isOneHypercoverDense _ _ _ _

/-- Sheafification exists for abelian sheaves at coefficient universe `v` on the small étale site
of a `u`-scheme once `u ≤ v`, by comparison with the essentially small affine étale site. -/
public lemma etaleSheaves_hasSheafify_of_univLE (X : Scheme.{u}) [UnivLE.{u, v}] :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{v} := by
  have := affineEtale_essentiallySmall_of_univLE.{u, v} X
  have : HasLimitsOfSize.{u, u} AddCommGrpCat.{v} := hasLimitsOfSizeOfUnivLE _
  have : HasSheafify (Scheme.AffineEtale.topology X) AddCommGrpCat.{v} :=
    hasSheafifyEssentiallySmallSite _ _
  have := isEquivalence_sheafPushforwardContinuous_affineEtale_spec.{u, v} X
  exact Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
    (Scheme.AffineEtale.topology X) X.smallEtaleTopology (Scheme.AffineEtale.Spec X)

/-- Universe lifting of abelian groups on the small étale site of a `u`-scheme is compatible with
sheafification and preserves injective objects, once `u ≤ v`.  The small dense subsite is a
small model of the affine étale site. -/
public lemma etaleUlift_properties (X : Scheme.{u}) [UnivLE.{u, v}] :
    X.smallEtaleTopology.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, v} ∧
    (sheafCompose X.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{t, v}).PreservesInjectiveObjects := by
  have := affineEtale_essentiallySmall_of_univLE.{u, v} X
  have : HasLimitsOfSize.{u, u} AddCommGrpCat.{v} := hasLimitsOfSizeOfUnivLE _
  have : HasLimitsOfSize.{u, u} AddCommGrpCat.{max v t} := hasLimitsOfSizeOfUnivLE _
  let A := X.AffineEtale
  let e := equivSmallModel.{v} A
  let J := Scheme.AffineEtale.topology X
  let J₀ := e.inverse.inducedTopology J
  let i := Scheme.AffineEtale.Spec X
  have := isEquivalence_sheafPushforwardContinuous_affineEtale_spec.{u, v} X
  have := isEquivalence_sheafPushforwardContinuous_affineEtale_spec.{u, max v t} X
  have : (e.inverse.sheafPushforwardContinuous AddCommGrpCat.{v} J₀ J).IsEquivalence :=
    (e.sheafCongr J J₀ AddCommGrpCat.{v}).isEquivalence_functor
  have : (e.inverse.sheafPushforwardContinuous AddCommGrpCat.{max v t} J₀ J).IsEquivalence :=
    (e.sheafCongr J J₀ AddCommGrpCat.{max v t}).isEquivalence_functor
  obtain ⟨_, _⟩ := sheafUlift_properties_of_small_subsite.{v, t} J₀ J e.inverse
  exact ⟨GrothendieckTopology.PreservesSheafification.transport
      X.smallEtaleTopology J i _ _,
    sheafCompose_preservesInjectives_of_restriction J X.smallEtaleTopology i _⟩

section

variable (X : Scheme.{u})

/-- Sheafification of abelian groups at the object universe of the small étale site. -/
local instance hasSheafify_smallEtale_objectUniverse :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  etaleSheaves_hasSheafify_of_univLE.{u, u + 1} X

/-- `Ext` of abelian sheaves at the morphism universe of the small étale site lives in that
universe, the sheaves there being Grothendieck abelian relative to it.  Instance search does not
find this on its own: `AlgebraicGeometry.hasExt_sheaf_smallEtaleTopology` gives
`CategoryTheory.HasExt.{u + 1}` for the same coefficients and is declared later. -/
local instance hasExt_sheaf_smallEtale_morphismUniverse :
    HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  haveI : IsGrothendieckAbelian.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
    Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology X AddCommGrpCat.{u}
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- `Ext` of abelian sheaves at the object universe of the small étale site lives in that
universe.  The Grothendieck abelianness it comes from is
`Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale` with its coefficient universe
pinned: the general instance is indexed by `max (u + 1) v` and instance search cannot solve
`max (u + 1) ?v = u + 1`. -/
local instance hasExt_sheaf_smallEtale_objectUniverse :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  haveI : IsGrothendieckAbelian.{u + 1}
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- The universe lift of the coefficients is compatible with sheafification on the small étale
site, from the morphism universe to the object universe. -/
local instance preservesSheafification_uliftFunctor_smallEtale :
    X.smallEtaleTopology.PreservesSheafification AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  (etaleUlift_properties.{u, u, u + 1} X).1

/-- The universe lift of the coefficients preserves injective abelian sheaves on the small étale
site, from the morphism universe to the object universe. -/
local instance preservesInjectiveObjects_uliftFunctor_smallEtale :
    (sheafCompose X.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).PreservesInjectiveObjects :=
  (etaleUlift_properties.{u, u, u + 1} X).2

/-- **The coefficient universe of étale cohomology can be raised freely.**  For an abelian sheaf
`F` on the small étale site of `X` with values at the morphism universe of the site, the
cohomology of `F` and the cohomology of its universe lift to the object universe of the site
agree in every degree. -/
public def smallEtaleSheafHUliftAddEquiv
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u, u} F n ≃+
      Sheaf.H.{u + 1, u + 1} ((sheafCompose X.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F) n :=
  sheafHUliftAddEquiv.{u, u, u + 1, u + 1} X.smallEtaleTopology F n

/-- **The cohomology of an abelian sheaf on the small étale site and the cohomology of its
coefficient-universe lift vanish together.** -/
public theorem subsingleton_smallEtaleSheafH_ulift_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} ((sheafCompose X.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F) n) ↔
      Subsingleton (Sheaf.H.{u, u} F n) :=
  (smallEtaleSheafHUliftAddEquiv X F n).toEquiv.subsingleton_congr.symm

end

end AlgebraicGeometry

end
