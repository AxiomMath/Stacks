module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAcyclicResolutionPushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineAcyclic
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSheafLevelCechExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleEnoughAffineObjects

/-!
# The higher direct images along an affine `ε_a` vanish

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site whose underlying morphism of
schemes is affine, and let `ε_a : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` be the morphism of small
étale ringed sites of [Stacks, Tag 070R] (2).  Then for every `𝒪_{X_étale}`-module `𝓜` that is
quasi-coherent on the site

`R ᵠ (ε_a)_*(𝓜) = 0` for `q > 0`,

which is `AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_of_isAffineHom` below.

## The route

By [Stacks, Tag 072W] the sheaf `R ᵠ (ε_a)_*(𝓜)` is the sheafification of the presheaf
`V ↦ H ᵠ (X ×_Y V, 𝓜)` on `Y_étale`, so it vanishes as soon as that presheaf vanishes on a
covering family of every object.  The small étale site of `Y` has enough affine objects
(`AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine`), the base change `X ×_Y V` of an
affine object along an affine morphism is affine
(`AlgebraicGeometry.SmallEtale.isAffine_toScheme_smallEtaleBaseChange`), and a module
quasi-coherent on the site is acyclic over an affine object
(`AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isAffine`).  The criterion that
assembles these is
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`, the
module-valued form of [Stacks, Tag 072W] plus [Stacks, Tag 01FW]; no naturality in the object of
`Y_étale` is involved, the hypothesis being consumed one object and one covering member at a
time.

## Why this is here

It is the acyclicity input of the Čech route to the étale half of [Stacks, Tag 071N] above
degree zero.  The resolution that
`AlgebraicGeometry.SmallEtale.rightDerivedPushforwardIsoHomologyOfAcyclic` consumes must have
terms acyclic for `(ε_a)_*`; in the intended application those terms are direct images from the
small étale sites of the members of a cover of `X` whose structure morphisms to `Y` are affine,
and this file is what makes such a term acyclic once it has been identified with a direct image
along the affine composite.  In degree zero the corresponding statement is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pushforward`.

It is also the small-étale-site analogue, for schemes, of [Stacks, Tag 073H], whose algebraic
spaces statement is `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_isAffineHom`;
here the affine acyclicity is the theorem
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isAffine`.

## Main results

* `AlgebraicGeometry.SmallEtale.acyclic_pushforward_of_isZero_rightDerived_evaluation_baseChange`:
  **acyclicity for `(ε_a)_*` from the vanishing of cohomology over the base changes of the
  affine objects of `Y_étale`**, for an arbitrary `a`.  This is the criterion a term of a Čech
  resolution is checked against.
* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_of_isAffineHom`: **the higher
  direct images along an affine `ε_a` of a module quasi-coherent on the site vanish.**
* `AlgebraicGeometry.SmallEtale.acyclic_pushforward_of_isAffineHom`: the same statement as
  acyclicity for `(ε_a)_*` in the sense of `Stacks.RightDerivedComp.acyclic`, which is the shape
  `AlgebraicGeometry.SmallEtale.rightDerivedPushforwardIsoHomologyOfAcyclic` consumes.
* `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_rightDerived_pushforward_of_resolution`:
  **the interface the Čech route reduces to** — the cartesian condition on every higher direct
  image along an arbitrary `ε_a`, from a resolution of the module whose terms are
  cohomologically trivial over the affine base changes and have quasi-coherent direct images.
  Both remaining hypotheses are geometry of a cover; nothing homological is left.
* `AlgebraicGeometry.SmallEtale.rightDerivedPushforwardIsoHomologySheafLevelCech` and
  `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_rightDerived_pushforward_sheafLevelCech`:
  **the higher direct images computed by, and cartesian by way of, the sheaf-level Čech complex
  of a covering family of the final object of `X_étale`** — the two statements above with the
  resolution hypothesis discharged, that complex being a resolution by
  `AlgebraicGeometry.SmallEtale.quasiIso_sheafLevelCechAugmentation`.  What is left in their
  hypotheses is conditions on the *terms* of the Čech complex and nothing else.  The docstring of
  the second records precisely what the étale clause of [Stacks, Tag 071N] still owes on top of
  them, and that neither remaining condition is homological.

## Implementation notes

The covering family produced by `AlgebraicGeometry.GrothendieckTopology.HasEnoughObjects` is a
family of arrows, and `CategoryTheory.Sieve.ofArrows` is by definition the sieve generated by
`CategoryTheory.Presieve.ofArrows` on it, so the criterion's presieve hypothesis is met by that
presieve with no further work;  destructing membership in it names the index, which is where
affineness of the member comes from.

**No `@[stacks]` attribute is placed.**  [Stacks, Tag 073H] is stated for algebraic spaces and
is registered in
`StacksFrontier/AlgebraicGeometry/Spaces/AffineHigherPushforwardVanishingUnconditional.lean`;
the statement here is about a morphism of the small étale sites of two schemes, which is not an
instance of it in this development.

## References

* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **Acyclicity for the direct image along `ε_a` from the vanishing of cohomology over the
base changes of the affine objects.**  If, for every affine object `W` of `Y_étale`, the
cohomology of `𝓝` over the object `X ×_Y W` of `X_étale` vanishes in positive degrees, then `𝓝`
is acyclic for `(ε_a)_*`.

By [Stacks, Tag 072W] the sheaf `R ᵠ (ε_a)_*(𝓝)` is the sheafification of the presheaf
`V ↦ H ᵠ (X ×_Y V, 𝓝)`, and the affine objects cover every object of `Y_étale` by
`AlgebraicGeometry.SmallEtale.hasEnoughObjects_isAffine`, so a presheaf vanishing on them
sheafifies to zero.

This is the form in which a term of a Čech resolution is shown to be acyclic: for a direct image
from a member `U` of a cover of `X` the cohomology over `X ×_Y W` is the cohomology over
`U ×_Y W`, which is affine as soon as `U ⟶ Y` is affine and `W` is. -/
public theorem acyclic_pushforward_of_isZero_rightDerived_evaluation_baseChange
    (𝓝 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h : ∀ W : SmallEtale B Y.obj Y.property,
      AlgebraicGeometry.IsAffine ((toScheme B Y.obj Y.property).obj W) → ∀ q, 0 < q →
        IsZero (((SheafOfModules.evaluation (structureSheaf B X.obj X.property)
          (op ((smallEtaleBaseChange B a).obj W))).rightDerived q).obj 𝓝)) :
    Stacks.RightDerivedComp.acyclic
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)) 𝓝 := by
  intro q hq
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (smallEtaleBaseChange B a) _ _ (smallEtaleStructureMapRing B a) q 𝓝 fun V ↦ ?_
  obtain ⟨I, Ui, f, hmem, hUi⟩ := hasEnoughObjects_isAffine B Y.obj Y.property V
  refine ⟨Presieve.ofArrows Ui f, hmem, ?_⟩
  rintro W g ⟨i⟩
  exact h (Ui i) (hUi i) q hq

/-- **The higher direct images along an affine morphism of small étale ringed sites vanish.**
For `a : X ⟶ Y` with affine underlying morphism of schemes and `𝓜` an `𝒪_{X_étale}`-module
quasi-coherent on the site, `R ᵠ (ε_a)_*(𝓜) = 0` for every `q > 0`.

The base change `X ×_Y W` of an affine object along an affine morphism is affine, and `𝓜` is
acyclic over an affine object, so
`AlgebraicGeometry.SmallEtale.acyclic_pushforward_of_isZero_rightDerived_evaluation_baseChange`
applies. -/
public theorem isZero_rightDerived_pushforward_of_isAffineHom [IsAffineHom (schemeHom B a)]
    (𝓜 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓜 : 𝓜.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q) :
    IsZero (((SheafOfModules.pushforward.{u}
      (smallEtaleStructureMapRing B a)).rightDerived q).obj 𝓜) :=
  acyclic_pushforward_of_isZero_rightDerived_evaluation_baseChange B a 𝓜
    (fun W hW p hp => isZero_rightDerived_evaluation_of_isAffine B X.obj X.property 𝓜 h𝓜 _
      (isAffine_toScheme_smallEtaleBaseChange B a W hW) p hp) q hq

/-- **A module quasi-coherent on the site is acyclic for the direct image along an affine
`ε_a`.**  This is `AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_of_isAffineHom`
in the shape `AlgebraicGeometry.SmallEtale.rightDerivedPushforwardIsoHomologyOfAcyclic` takes its
terms, so a resolution by such modules computes the higher direct images along any `ε_a`. -/
public theorem acyclic_pushforward_of_isAffineHom [IsAffineHom (schemeHom B a)]
    (𝓜 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓜 : 𝓜.IsQuasicoherentOnSite) :
    Stacks.RightDerivedComp.acyclic
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)) 𝓜 :=
  fun q hq => isZero_rightDerived_pushforward_of_isAffineHom B a 𝓜 h𝓜 q hq

/-- **The higher direct images along `ε_a` are cartesian on the affine objects as soon as the
module has a resolution whose terms are cohomologically trivial over the affine base changes and
have quasi-coherent direct images.**

This is the interface the Čech route to the étale half of [Stacks, Tag 071N] above degree zero
reduces to:  the two hypotheses on the terms of `K` are the geometry of a cover — positive-degree
cohomology of `K ʲ` over `X ×_Y W` vanishes for affine `W`, and `(ε_a)_*(K ʲ)` is quasi-coherent
on the site — and everything homological is discharged, by
`AlgebraicGeometry.SmallEtale.acyclic_pushforward_of_isZero_rightDerived_evaluation_baseChange`
and
`AlgebraicGeometry.SmallEtale.isCartesianOnAffines_rightDerived_pushforward_of_acyclic`.  No
hypothesis is placed on `a` or on the degree. -/
public theorem isCartesianOnAffines_rightDerived_pushforward_of_resolution
    {𝓜 : SheafOfModules.{u} (structureSheaf B X.obj X.property)}
    {K : CochainComplex (SheafOfModules.{u} (structureSheaf B X.obj X.property)) ℕ}
    (ε : (CochainComplex.single₀ (SheafOfModules.{u}
      (structureSheaf B X.obj X.property))).obj 𝓜 ⟶ K) [QuasiIso ε]
    (hvan : ∀ (j : ℕ) (W : SmallEtale B Y.obj Y.property),
      AlgebraicGeometry.IsAffine ((toScheme B Y.obj Y.property).obj W) → ∀ q, 0 < q →
        IsZero (((SheafOfModules.evaluation (structureSheaf B X.obj X.property)
          (op ((smallEtaleBaseChange B a).obj W))).rightDerived q).obj (K.X j)))
    (hqc : ∀ j, ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
      (K.X j)).IsQuasicoherentOnSite)
    (n : ℕ) :
    IsCartesianOnAffines B Y.obj Y.property
      (((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓜) :=
  isCartesianOnAffines_rightDerived_pushforward_of_acyclic B a ε
    (fun j => acyclic_pushforward_of_isZero_rightDerived_evaluation_baseChange B a _ (hvan j))
    hqc n

/-! ### The Čech resolution supplied

The three statements above take the resolution `ε` as a hypothesis.  The sheaf-level Čech complex
of a covering family of the final object of `X_étale` *is* such a resolution, by
`AlgebraicGeometry.SmallEtale.quasiIso_sheafLevelCechAugmentation`, so the three can be read with
`ε` discharged and only conditions on the *terms* of that complex left standing.  That is what
the two statements below do.  They are the Čech route to the étale clause of [Stacks, Tag 071N]
above degree zero with everything homological discharged: what remains in their hypotheses is
the geometry of the covering family and nothing else. -/

/-- **The higher direct image along `ε_a` is the cohomology of the direct image of the
sheaf-level Čech complex of a covering of `X`**, for a covering family whose Čech terms are
acyclic for `(ε_a)_*`:

`R ⁿ (ε_a)_*(𝓕) ≅ H ⁿ ((ε_a)_* Č(E, 𝓕))`.

This is `AlgebraicGeometry.SmallEtale.rightDerivedPushforwardIsoHomologyOfAcyclic` with its
resolution hypothesis discharged by
`AlgebraicGeometry.SmallEtale.quasiIso_sheafLevelCechAugmentation`;  `E` is required only to
cover the final object of `X_étale`, terminality being what makes the Čech complex a resolution
at all.  No hypothesis is placed on `a` or on the degree. -/
public def rightDerivedPushforwardIsoHomologySheafLevelCech
    (E : PreZeroHypercover.{u} (SmallEtale.final B X.obj X.property))
    (hE : (SmallEtale.topology B X.obj X.property).CoversTop E.X)
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (hK : ∀ q, Stacks.RightDerivedComp.acyclic
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
      (((sheafLevelCechComplex B X.obj X.property E).obj 𝓕).X q))
    (n : ℕ) :
    ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕 ≅
      (pushforwardCochainComplex B a
        ((sheafLevelCechComplex B X.obj X.property E).obj 𝓕)).homology n :=
  haveI := quasiIso_sheafLevelCechAugmentation B X.obj X.property E hE 𝓕
  rightDerivedPushforwardIsoHomologyOfAcyclic B a
    (sheafLevelCechAugmentation B X.obj X.property E 𝓕) hK n

/-- **The higher direct images along `ε_a` are cartesian on the affine objects as soon as the
terms of the sheaf-level Čech complex of a covering of `X` are acyclic for `(ε_a)_*` and have
quasi-coherent direct images.**

This is `AlgebraicGeometry.SmallEtale.isCartesianOnAffines_rightDerived_pushforward_of_acyclic`
with its resolution hypothesis discharged, as in
`AlgebraicGeometry.SmallEtale.rightDerivedPushforwardIsoHomologySheafLevelCech`.  Through
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isCartesianOnAffines` it also gives
quasi-coherence on the site of every higher direct image. -/
public theorem isCartesianOnAffines_rightDerived_pushforward_sheafLevelCech
    (E : PreZeroHypercover.{u} (SmallEtale.final B X.obj X.property))
    (hE : (SmallEtale.topology B X.obj X.property).CoversTop E.X)
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (hK : ∀ q, Stacks.RightDerivedComp.acyclic
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
      (((sheafLevelCechComplex B X.obj X.property E).obj 𝓕).X q))
    (hqc : ∀ q, ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
      (((sheafLevelCechComplex B X.obj X.property E).obj 𝓕).X q)).IsQuasicoherentOnSite)
    (n : ℕ) :
    IsCartesianOnAffines B Y.obj Y.property
      (((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕) :=
  have := quasiIso_sheafLevelCechAugmentation B X.obj X.property E hE 𝓕
  isCartesianOnAffines_rightDerived_pushforward_of_acyclic B a
    (sheafLevelCechAugmentation B X.obj X.property E 𝓕) hK hqc n

end AlgebraicGeometry.SmallEtale

end
