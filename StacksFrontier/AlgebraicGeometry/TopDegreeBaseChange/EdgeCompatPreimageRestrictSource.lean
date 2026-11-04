module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatPreimageRestrict

/-!
# The edge morphism of derived sections over an inverse image, against a smaller open upstairs

`Stacks.Cohomology.DerivedSectionsLeray.preimageSections f V` is sections over `f⁻¹V` read over
`Γ(V, 𝒪_Y)`. The tail of conclusion (c) of [Stacks, Tag 0EX3] leaves its edge morphism where the
crossing at `f''` over a smaller affine `W ⊆ h⁻¹V` meets the edge morphism of `RΓ(W, -)`, so what
the glue needs is the compatibility of that edge morphism with **restriction to a smaller open of
the source**, the scalars staying over `Γ(V, 𝒪_Y)`.

That is not `Stacks.Cohomology.DerivedSectionsLeray.preimageSectionsRestrictLE`, which restricts
along `W ≤ V` in the **base** — both opens there are opens of `Y`. And it is not
`Stacks.EdgeCompat.derivedHomologyComparison_sectionsOverOpenRestrict` either, which is at two
opens of one space along `…DerivedSectionsLeray.sectionsRingRestrict`, with no `f^♯` in it.

## Main results

* `Stacks.EdgeCompat.preimageSectionsRestrictSource`: restriction of sections from `f⁻¹V` to
  `W ⊆ f⁻¹V`, read over `Γ(V, 𝒪_Y)`. Its source is definitionally `preimageSections f V`.
* `Stacks.EdgeCompat.preimageSectionsRestrictSourceCompUnit` and
  `Stacks.EdgeCompat.isRightDerivedFunctor_preimageSectionsRestrictSourceCompUnit`: `RΓ(W, -)`
  followed by restriction of scalars from `Γ(W, 𝒪_X)` to `Γ(V, 𝒪_Y)` is a right derived functor
  of the target of that transformation. One application of
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit`.
* `Stacks.EdgeCompat.preimageSectionsRestrictSourceModelComparison` and
  `Stacks.EdgeCompat.preimageSectionsRestrictSourceModelComparison_fac_app`: the derived
  restriction, through the universal property of the first right derived functor, and the
  factorisation that characterises it.
* `Stacks.EdgeCompat.derivedHomologyComparison_preimageSectionsRestrictSource`: **the edge
  morphism of derived sections over an inverse image is compatible with restriction to a smaller
  open upstairs.** No hypothesis on `f`, on `V`, on `W` or on `q`.
* `Stacks.EdgeCompat.derivedHomologyComparison_preimageSectionsRestrictSourceCompUnit_eq`: the
  edge morphism that identity ends at, **split**, which reaches the edge morphism of `RΓ(W, -)`
  over `Γ(W, 𝒪_X)` in one application and leaves one exact prefix.
* `Stacks.EdgeCompat.isIso_derivedHomologyComparison_restrictScalarsComp`: **that prefix is
  invertible**, the composite of the two restrictions of scalars being exact. This is what
  disposes of it.
* `Stacks.EdgeCompat.derivedHomologyComparison_derivedPreimageSections_comp_restrictSource`:
  **the four above composed into the one chain the tail consumes** — the edge morphism of
  `RΓ(f⁻¹V, -)` in the total model
  `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections`, followed by restriction of
  sections to `W`, is the two model comparisons, the exact prefix, and the two restrictions of
  scalars applied to the edge morphism of `RΓ(W, -)` over `Γ(W, 𝒪_X)`. Nothing new is proved;
  the left-hand side is the edge morphism the composite of the first three factors of the
  tail ends at, so this is what a chase rewrites with in one step rather than four.

## Implementation notes

*Why this and not factor 4 whiskered by restriction of scalars.* The two routes from the split
`Stacks.EdgeCompat.derivedHomologyComparison_preimageSectionsCompUnit_eq` to sections over `W`
are: whisker `derivedHomologyComparison_sectionsOverOpenRestrict` — the compatibility at two
opens of `X` — by `preimageRestrictScalars f V`, or instantiate
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.derivedHomologyComparison_naturality_natTrans` a second time, here. This file takes the second,
and the deciding evidence is what each leaves for the **next** step of the chain, which needs the
edge morphism of `RΓ(W, -)` itself:

* whiskering factor 4 ends at `Functor.whiskerRight (edge of Γ(W, -) ⋙ res_{W ≤ f⁻¹V}) res_{f^♯}`,
  which is not an edge morphism of anything; reaching the edge morphism of `RΓ(W, -)` from there
  needs the split applied to `Γ(W, -) ⋙ res_{W ≤ f⁻¹V}` **and** a reassociation identifying a
  twice-whiskered edge morphism with the edge morphism whiskered by the composite — so two exact
  prefixes and a bookkeeping step;
* this route ends at the edge morphism of `Γ(W, -) ⋙ (res_{W ≤ f⁻¹V} ⋙ res_{f^♯})`, a genuine
  edge morphism at a composite target, which the split takes to the edge morphism of `RΓ(W, -)` in
  one application, leaving **one** exact prefix.

Each prefix is the edge morphism of an exact functor, hence invertible by
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.isIso_derivedHomologyComparison_mapDerivedCategory`, so neither route is blocked; the count of
them is the whole difference, and it decides for this one. The cost that used to argue the other
way — the `CompUnit`-plus-instance pair re-run at a second pair of functors — is now two lines,
`exactPostcomposeUnit` being general.

This makes `derivedHomologyComparison_sectionsOverOpenRestrict` unnecessary **for this chain**; it
is not thereby wrong or redundant, being the statement at two opens of one space with no morphism
of spaces in it, and it stays in the library.

*The second factor of the target is a composite of two restrictions of scalars, written out.* It
is `sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V` and not the single restriction of
scalars along the `appLE` ring map `Γ(V, 𝒪_Y) ⟶ Γ(W, 𝒪_X)`; the two are identified by
`AlgebraicGeometry.Scheme.Hom.appLE` bookkeeping and `ModuleCat.restrictScalarsComp'`, which is a
step for the consumer and not for this file. Writing the composite keeps every instance needed
here — additivity, finite limits, finite colimits — a composition of ones already found.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison
  derivedHomologyComparison_naturality_natTrans exactPostcomposeUnit
  isRightDerivedFunctor_exactPostcomposeUnit
  isIso_derivedHomologyComparison_mapDerivedCategory)

namespace Stacks.EdgeCompat

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Sheaves of modules on a ringed space have enough injectives: they form a Grothendieck abelian
category, in the one module universe available there. This is
`SheafOfModules.enoughInjectivesU` at three equal universes, which is not the shape instance
search finds unaided. -/
local instance moduleSheaves_enoughInjectives_restrictSource (Z : RingedSpace.{u, u}) :
    EnoughInjectives (SheafOfModules.{u} (structureSheafRing Z)) :=
  SheafOfModules.enoughInjectivesU.{u, u, u} (structureSheafRing Z)

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (V : Opens Y.carrier) {W : Opens X.carrier}
  (hW : W ≤ (opensMap f).obj V)

/-- **Restriction of sections over `f⁻¹V` to a smaller open `W` of `X`, read over
`Γ(V, 𝒪_Y)`.** It is `Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpenRestrictLE` on `X`,
pushed along restriction of scalars by `f^♯`.

The source is `Stacks.Cohomology.DerivedSectionsLeray.preimageSections f V` by definition; the
target's type is written with the two restrictions of scalars associated so that the composite's
second factor is a single functor, which is the spelling the right derived functor below is a
derived functor of. -/
def preimageSectionsRestrictSource :
    sectionsOverOpen X ((opensMap f).obj V) ⋙ preimageRestrictScalars f V ⟶
      sectionsOverOpen X W ⋙ (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V) :=
  Functor.whiskerRight (sectionsOverOpenRestrictLE X hW) (preimageRestrictScalars f V)

/-- **The unit exhibiting `RΓ(W, -)` followed by restriction of scalars from `Γ(W, 𝒪_X)` to
`Γ(V, 𝒪_Y)` as a right derived functor** of the target of `preimageSectionsRestrictSource`. One
application of `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.exactPostcomposeUnit`,
at the pair `(Γ(W, -), res_{W ≤ f⁻¹V} ⋙ res_{f^♯})`: the second factor is a composite of two
restrictions of scalars, so exact, which is the brick's only hypothesis on it. -/
def preimageSectionsRestrictSourceCompUnit :
    (sectionsOverOpen X W ⋙
          (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSectionsOverOpen X W ⋙
        (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V).mapDerivedCategory :=
  exactPostcomposeUnit (sectionsOverOpen X W)
    (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V)
    (derivedSectionsOverOpen X W) (derivedSectionsOverOpenUnit X W)

/-- **`preimageSectionsRestrictSourceCompUnit` does exhibit a right derived functor.** The
general brick `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.isRightDerivedFunctor_exactPostcomposeUnit`, with the K-injective resolutions on `X` supplied by
`Stacks.Cohomology.DerivedSectionsLeray.exists_quasiIso_isKInjective`. -/
instance isRightDerivedFunctor_preimageSectionsRestrictSourceCompUnit :
    (derivedSectionsOverOpen X W ⋙
        (sectionsRestrictScalars X hW ⋙
          preimageRestrictScalars f V).mapDerivedCategory).IsRightDerivedFunctor
      (preimageSectionsRestrictSourceCompUnit f V hW)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)) :=
  isRightDerivedFunctor_exactPostcomposeUnit _ _ _ _ (exists_quasiIso_isKInjective X)

/-- **The derived restriction of sections over `f⁻¹V` to `W`, read over `Γ(V, 𝒪_Y)`**: the
transformation induced by `preimageSectionsRestrictSource` on the homotopy category followed by
`preimageSectionsRestrictSourceCompUnit`, through the universal property of
`RΓ(f⁻¹V, -) ⋙ res_{f^♯}`. By `preimageSectionsRestrictSourceModelComparison_fac_app` its
composite with that functor's unit is the inducing transformation, and that equation determines
it. -/
def preimageSectionsRestrictSourceModelComparison :
    derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
        (preimageRestrictScalars f V).mapDerivedCategory ⟶
      derivedSectionsOverOpen X W ⋙
        (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V).mapDerivedCategory :=
  (derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
      (preimageRestrictScalars f V).mapDerivedCategory).rightDerivedDesc
    (preimageSectionsCompUnit f V)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) _
    (Functor.whiskerRight
        (NatTrans.mapHomotopyCategory (preimageSectionsRestrictSource f V hW)
          (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
      preimageSectionsRestrictSourceCompUnit f V hW)

/-- The equation characterising `preimageSectionsRestrictSourceModelComparison`, pointwise. -/
theorem preimageSectionsRestrictSourceModelComparison_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (preimageSectionsCompUnit f V).app K ≫
        (preimageSectionsRestrictSourceModelComparison f V hW).app
          (DerivedCategory.Qh.obj K) =
      (Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (preimageSectionsRestrictSource f V hW)
            (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        preimageSectionsRestrictSourceCompUnit f V hW).app K :=
  Functor.rightDerived_fac_app _ _ _ _ _ K

/-- **The cohomology edge morphism of derived sections over an inverse image is compatible with
restriction to a smaller open upstairs.** For a morphism `f : X ⟶ Y` of ringed spaces, an open
`V ⊆ Y`, an open `W ⊆ f⁻¹V` of `X` and a degree `q`,

> `H^q(RΓ(f⁻¹V, K)) ⟶ Γ(f⁻¹V, H^q K) ⟶ Γ(W, H^q K)` versus
> `H^q(RΓ(f⁻¹V, K)) ⟶ H^q(RΓ(W, K)) ⟶ Γ(W, H^q K)`

commute, everything read over `Γ(V, 𝒪_Y)`: the edge morphism over `f⁻¹V` followed by restriction
of sections to `W` is `preimageSectionsRestrictSourceModelComparison` followed by the edge
morphism of `Γ(W, -) ⋙ res_{W ≤ f⁻¹V} ⋙ res_{f^♯}`.

This is `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.derivedHomologyComparison_naturality_natTrans` at the transformation
`preimageSectionsRestrictSource`, whose coherence datum is
`preimageSectionsRestrictSourceModelComparison_fac_app`. Nothing is assumed of `f`, of `V`, of `W`
or of `q`. -/
theorem derivedHomologyComparison_preimageSectionsRestrictSource (q : ℤ) :
    derivedHomologyComparison
            (sectionsOverOpen X ((opensMap f).obj V) ⋙ preimageRestrictScalars f V)
            (derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
              (preimageRestrictScalars f V).mapDerivedCategory)
            (preimageSectionsCompUnit f V) (exists_quasiIso_isKInjective X) q ≫
        Functor.whiskerLeft
          (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) q)
          (preimageSectionsRestrictSource f V hW) =
      Functor.whiskerRight (preimageSectionsRestrictSourceModelComparison f V hW)
          (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q) ≫
        derivedHomologyComparison
          (sectionsOverOpen X W ⋙ (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V))
          (derivedSectionsOverOpen X W ⋙
            (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V).mapDerivedCategory)
          (preimageSectionsRestrictSourceCompUnit f V hW) (exists_quasiIso_isKInjective X) q := by
  have hcoh : Functor.whiskerRight
          (NatTrans.mapHomotopyCategory (preimageSectionsRestrictSource f V hW)
            (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        preimageSectionsRestrictSourceCompUnit f V hW =
      preimageSectionsCompUnit f V ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (preimageSectionsRestrictSourceModelComparison f V hW) := by
    ext K
    exact (preimageSectionsRestrictSourceModelComparison_fac_app f V hW K).symm
  exact derivedHomologyComparison_naturality_natTrans
    (sectionsOverOpen X ((opensMap f).obj V) ⋙ preimageRestrictScalars f V)
    (preimageSectionsRestrictSource f V hW)
    (derivedSectionsOverOpen X ((opensMap f).obj V) ⋙
      (preimageRestrictScalars f V).mapDerivedCategory)
    (preimageSectionsCompUnit f V)
    (derivedSectionsOverOpen X W ⋙
      (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V).mapDerivedCategory)
    (preimageSectionsRestrictSourceCompUnit f V hW)
    (preimageSectionsRestrictSourceModelComparison f V hW) hcoh
    (exists_quasiIso_isKInjective X) q

/-- **The edge morphism this route ends at splits, reaching the edge morphism of `RΓ(W, -)`.**
`derivedHomologyComparison_exactPostcomposeUnit_eq` at the pair
`(Γ(W, -), res_{W ≤ f⁻¹V} ⋙ res_{f^♯})`: the edge morphism of the composite of the two
restrictions of scalars at `RΓ(W, K)` — invertible, by
`isIso_derivedHomologyComparison_restrictScalarsComp` — followed by those restrictions applied to
the edge morphism of `RΓ(W, -)` over `Γ(W, 𝒪_X)`.

That is the whole gain over whiskering factor 4: **one** application of the splitting and one
exact prefix. Nothing is assumed of `f`, of `V`, of `W` or of `q`. -/
theorem derivedHomologyComparison_preimageSectionsRestrictSourceCompUnit_eq (q : ℤ) :
    derivedHomologyComparison
        (sectionsOverOpen X W ⋙ (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V))
        (derivedSectionsOverOpen X W ⋙
          (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V).mapDerivedCategory)
        (preimageSectionsRestrictSourceCompUnit f V hW) (exists_quasiIso_isKInjective X) q =
      (Functor.associator (derivedSectionsOverOpen X W)
            (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V).mapDerivedCategory
            (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q)).hom ≫
        Functor.whiskerLeft (derivedSectionsOverOpen X W)
            (derivedHomologyComparison
              (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V)
              (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V).mapDerivedCategory
              (sectionsRestrictScalars X hW ⋙
                preimageRestrictScalars f V).mapDerivedCategoryFactorsh.inv
              (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
                (C := ModuleCat.{u} ((structureSheafRing X).obj.obj (op W)))) q) ≫
          (Functor.associator (derivedSectionsOverOpen X W)
              (DerivedCategory.homologyFunctor
                (ModuleCat.{u} ((structureSheafRing X).obj.obj (op W))) q)
              (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V)).inv ≫
            Functor.whiskerRight
                (derivedHomologyComparison (sectionsOverOpen X W)
                  (derivedSectionsOverOpen X W) (derivedSectionsOverOpenUnit X W)
                  (exists_quasiIso_isKInjective X) q)
                (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V) ≫
              (Functor.associator
                  (DerivedCategory.homologyFunctor
                    (SheafOfModules.{u} (structureSheafRing X)) q)
                  (sectionsOverOpen X W)
                  (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V)).hom := by
  have := isRightDerivedFunctor_preimageSectionsRestrictSourceCompUnit f V hW
  unfold preimageSectionsRestrictSourceCompUnit at this
  exact derivedHomologyComparison_exactPostcomposeUnit_eq (sectionsOverOpen X W)
    (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V)
    (derivedSectionsOverOpen X W) (derivedSectionsOverOpenUnit X W)
    (exists_quasiIso_isKInjective X)
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
      (C := ModuleCat.{u} ((structureSheafRing X).obj.obj (op W)))) q

/-- **The one exact prefix the splitting leaves is invertible.** The composite of the two
restrictions of scalars is exact, so
`Stacks.Cohomology.HypercohomologyEdge.HomologyComparison`
`.isIso_derivedHomologyComparison_mapDerivedCategory` applies: no K-injectivity, no boundedness
and no acyclicity, and in particular nothing assumed of `f`. This is what disposes of the prefix
in `derivedHomologyComparison_preimageSectionsRestrictSourceCompUnit_eq`. -/
theorem isIso_derivedHomologyComparison_restrictScalarsComp (q : ℤ) :
    IsIso (derivedHomologyComparison
      (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V)
      (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V).mapDerivedCategory
      (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V).mapDerivedCategoryFactorsh.inv
      (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
        (C := ModuleCat.{u} ((structureSheafRing X).obj.obj (op W)))) q) :=
  isIso_derivedHomologyComparison_mapDerivedCategory _ _ q

/-- **The glue of conclusion (c) of [Stacks, Tag 0EX3], as one chain.** For a morphism
`f : X ⟶ Y` of ringed spaces, an open `V ⊆ Y`, an open `W ⊆ f⁻¹V` of `X` and a degree `q`, the
edge morphism of `RΓ(f⁻¹V, -)` **in the total model**
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections` — which is the one the
composite of the first three factors of the tail ends at — followed by restriction of sections to
`W`, is

> the two model comparisons, then the exact prefix, then the two restrictions of scalars applied
> to the edge morphism of `RΓ(W, -)` over `Γ(W, 𝒪_X)`.

Nothing is proved here: it is `derivedHomologyComparison_preimageSectionsModelComparison`, then
`derivedHomologyComparison_preimageSectionsCompUnitComp_eq` crossing the two spellings of the
degreewise functor, then `derivedHomologyComparison_preimageSectionsRestrictSource`, then
`derivedHomologyComparison_preimageSectionsRestrictSourceCompUnit_eq`, composed. It is stated
because the four are what the chase has to rewrite with in that order, and because the chain is
the one object the next step of the tail consumes.

The exact prefix is kept where the splitting leaves it rather than cancelled;
`isIso_derivedHomologyComparison_restrictScalarsComp` is what disposes of it, and it is invertible
with no hypothesis, so this statement assumes nothing of `f`, of `V`, of `W` or of `q`. -/
theorem derivedHomologyComparison_derivedPreimageSections_comp_restrictSource (q : ℤ) :
    derivedHomologyComparison (modulePushforward f ⋙ sectionsOverOpen Y V)
            (derivedPreimageSections f V) (derivedPreimageSectionsUnitComp f V)
            (exists_quasiIso_isKInjective X) q ≫
        Functor.whiskerLeft
          (DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) q)
          (preimageSectionsRestrictSource f V hW) =
      Functor.whiskerRight (preimageSectionsModelComparison f V)
          (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q) ≫
        Functor.whiskerRight (preimageSectionsRestrictSourceModelComparison f V hW)
            (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q) ≫
          (Functor.associator (derivedSectionsOverOpen X W)
                (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V).mapDerivedCategory
                (DerivedCategory.homologyFunctor
                  (ModuleCat.{u} ((structureSheafRing Y).obj.obj (op V))) q)).hom ≫
            Functor.whiskerLeft (derivedSectionsOverOpen X W)
                (derivedHomologyComparison
                  (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V)
                  (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V).mapDerivedCategory
                  (sectionsRestrictScalars X hW ⋙
                    preimageRestrictScalars f V).mapDerivedCategoryFactorsh.inv
                  (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian
                    (C := ModuleCat.{u} ((structureSheafRing X).obj.obj (op W)))) q) ≫
              (Functor.associator (derivedSectionsOverOpen X W)
                  (DerivedCategory.homologyFunctor
                    (ModuleCat.{u} ((structureSheafRing X).obj.obj (op W))) q)
                  (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V)).inv ≫
                Functor.whiskerRight
                    (derivedHomologyComparison (sectionsOverOpen X W)
                      (derivedSectionsOverOpen X W) (derivedSectionsOverOpenUnit X W)
                      (exists_quasiIso_isKInjective X) q)
                    (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V) ≫
                  (Functor.associator
                      (DerivedCategory.homologyFunctor
                        (SheafOfModules.{u} (structureSheafRing X)) q)
                      (sectionsOverOpen X W)
                      (sectionsRestrictScalars X hW ⋙ preimageRestrictScalars f V)).hom := by
  have hhead := (derivedHomologyComparison_preimageSectionsModelComparison f V q).trans
    (whisker_eq _ (derivedHomologyComparison_preimageSectionsCompUnitComp_eq f V q))
  have htail := (derivedHomologyComparison_preimageSectionsRestrictSource f V hW q).trans
    (whisker_eq _
      (derivedHomologyComparison_preimageSectionsRestrictSourceCompUnit_eq f V hW q))
  exact (eq_whisker hhead _).trans ((Category.assoc _ _ _).trans (whisker_eq _ htail))

end Stacks.EdgeCompat

end
