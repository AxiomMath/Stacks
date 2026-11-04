module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianSupportedSectionsCounit

/-!
# The two models of the abelian local cohomology sheaves `ℋ ⁿ_Z` agree

Let `Z` be a closed subset of a ringed space `X` and `i : Z ⟶ X` the inclusion.  On sheaves of
**abelian groups** the local cohomology sheaves occur in this library in two models which, before
this file, no declaration related:

* the *unbounded* model: the degree-`n` cohomology sheaf of
  `Stacks.Cohomology.SupportedComplexes.derivedAbelianSupportedSectionsOnClosed` applied to a
  sheaf placed in degree `0`, and — with the direct image from `Z` folded in — the degree-`n`
  cohomology sheaf of
  `Stacks.Cohomology.AbelianSupportedCounit.derivedAbelianSupportedPushforward`. This is the
  model the square `Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare` of step
  (ii) of [Stacks, Tag 0G85] is stated in, and the model
  `Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison` — the
  comparison of [Stacks, Tag 0G74] part (2) with `i_*` folded in — takes its values in.
* the *classical* model: `ClosedImmersionSheaves.localCohomologySheafFunctor`, Mathlib's
  `ℕ`-indexed `CategoryTheory.Functor.rightDerived` of abelian sections supported on `Z`, computed
  from an injective resolution.  This is the model
  `Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso` lands in, by way of
  `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexForgetIso`.

This file identifies the two, naturally in the coefficient abelian sheaf.  Both halves are the
abelian counterparts of module-level statements the library already has:

* `abelianPushHomologyIso` is the counterpart of
  `Stacks.Perfect.CechSupportTransport.pushHomologyIso`, namely [Stacks, Tag 0G74] part (2) for
  the exact direct image from a closed subset: the degree-`n` cohomology sheaf of
  `i_* R𝓗_Z^{ab}(K)` is the direct image of the degree-`n` cohomology sheaf of `R𝓗_Z^{ab}(K)`.
  Like its module-level counterpart it is
  `CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso` at the direct image, which is
  exact.
* `abelianLocalCohomologySheafOfComplexFunctorIso` is the counterpart of
  `Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctorIso`, namely the
  comparison of the unbounded model on `Z` with Mathlib's `rightDerived`.  Like its module-level
  counterpart it is `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` at the
  canonical derived functor, whose `IsRightDerivedFunctor` instance
  `derivedAbelianSupportedSectionsOnClosed_isRightDerivedFunctor` holds unconditionally.

## Main definitions

* `abelianLocalCohomologySheafOfComplexFunctor`: the unbounded model of `ℋ ⁿ_Z` on abelian
  sheaves, read as a functor of the coefficient sheaf, in an arbitrary integer degree.
* `abelianPushHomologyIso`, with `abelianPushHomologyIso_hom_naturality` and the natural
  isomorphism `abelianPushforwardHomologyIso` it assembles into: **[Stacks, Tag 0G74] part (2)
  for the exact direct image from `Z`, on abelian sheaves.**
* `abelianLocalCohomologySheafOfComplexFunctorIso`: **the unbounded model on `Z` is the classical
  model**, naturally in the coefficient sheaf.
* `abelianSupportedPushforwardModelIso`: **the two models agree with the direct image folded
  in** — the composite of the two previous items, a natural isomorphism

  `G ↦ H ⁿ(i_* R𝓗_Z^{ab}(G[0]))  ≅  G ↦ i_*ℋ ⁿ_Z(G)`

  between the unbounded model with `i_*` folded in and `i_*` of the classical model.  This is the
  abelian counterpart of
  `Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafFunctorLocalCohomologyIso`.
* `abelianSupportedPushforwardLocalCohomologyIso`: the same isomorphism with its target spelled
  through `ClosedImmersionSheaves`, in which spelling the target *is*
  `Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward X T hT n` — by `rfl`, the
  two respellings `Stacks.Cohomology.SupportedComplexes.abelianClosedPushforward` and
  `Stacks.Perfect.GysinAbelianSquare.abelianClosedPushforward` of the direct image of abelian
  sheaves along the inclusion of a closed subset being the same functor.  That is the functor
  `Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso` takes its values in.

## Implementation notes

**Carried hypotheses: none beyond `hZ : IsClosed Z`.**  Closedness is used twice and only twice:
`derivedAbelianSupportedPushforward` does not exist without it (the direct image from `Z` is exact
only for a closed subset, which is what lets it be applied through
`CategoryTheory.Functor.mapDerivedCategory` rather than derived), and the two exactness instances
`Stacks.Cohomology.AbelianSupportedCounit.abelianClosedPushforward_preservesFiniteLimits` and
`abelianClosedPushforward_preservesFiniteColimits` need it.  No hypothesis whatsoever is placed on
the coefficient sheaf; in particular nothing here is about quasi-coherence, there being no module
structure in sight.  The degree of `abelianLocalCohomologySheafOfComplexFunctorIso` and of
`abelianSupportedPushforwardModelIso` is a natural number read as `(n : ℤ)`, because the classical
model is `ℕ`-indexed; `abelianPushHomologyIso` holds in every integer degree.

**Why the comparisons are assembled from object-level components.**  `abelianPushHomologyIso` and
the components of `abelianSupportedPushforwardModelIso` are stated at an object and the natural
isomorphisms are assembled from them by `CategoryTheory.NatIso.ofComponents`, rather than by an
`Iso.trans` chain of whiskerings.  The reason is the one recorded in the implementation notes of
`StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived`:
`(E ⋙ G) ⋙ H` and `E ⋙ (G ⋙ H)` are definitionally equal but are not unifiable as applications
of `CategoryTheory.Functor.comp`, whose universe arguments the two groupings instantiate
differently — and `derivedAbelianSupportedPushforward` is *defined* as a composite, so every
statement about it followed by a cohomology functor meets that mismatch.  At `.obj` and `.map` the
two groupings reduce by projection and the mismatch does not arise.  For the same reason
`abelianModelOnClosed_naturality` restates the naturality of
`abelianLocalCohomologySheafOfComplexFunctorIso` with the functors applied one at a time.

**What is *not* proved here.**  Nothing here identifies the comparison of [Stacks, Tag 0G74]
part (2) in the unbounded model,
`Stacks.Cohomology.AbelianSupportedCounit.abelianSupportedEndoForgetComparison`, with the one in
the classical model,
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexForgetIso`; this file supplies
the bridge between the two *models*, not between the two *comparisons*.  Concretely, the
statement still owed is that

`(abelianSheaf X).map (supportCohomologySheafFunctorIso hT n).hom.app ℱ ≫`
`  (pushforwardLocalCohomologyForgetIso hT n).hom.app ℱ`

agrees with the degree-`n` cohomology of
`Stacks.Perfect.AbelianCechDerivedSquare.forgetComparison` at `ℱ[0]`, read across
`abelianSupportedPushforwardLocalCohomologyIso` above together with
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` and Mathlib's
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` for the forgetful functor.  Both sides
are `CategoryTheory.Functor.rightDerivedDesc` of their respective transported underived
comparisons, so the proof is a `CategoryTheory.Functor.rightDerived_ext` argument of the same
shape and size as
`Stacks.Cohomology.AbelianSupportedCounitForget.whiskerRight_derivedSupportedSectionsToId`, and it
is not carried out here.  Nothing here mentions a Čech complex, a cokernel, a class map or
[Stacks, Tag 0G85].

**No `@[stacks ...]` attribute is attached to any declaration here.**

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Lemma 20.34.6 (Tag 0G72)](https://stacks.math.columbia.edu/tag/0G72)
* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.AbelianSupportedCounit
open Stacks.Cohomology.Localization (enoughKInjectives)
open Stacks.Cohomology.SupportedComplexes

universe u

namespace Stacks.Cohomology.AbelianModelComparison

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.Cohomology.UnderlyingAbelianSectionsWithSupport.abelianSheaves_isGrothendieckAbelian

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z)

/-! ### Stacks 0G74 part (2) for the exact direct image, on abelian sheaves -/

/-- **[Stacks, Tag 0G74] part (2) for the exact direct image from a closed subset, on sheaves of
abelian groups**: the degree-`c` cohomology sheaf of `i_* R𝓗_Z^{ab}(K)` is the direct image of
the degree-`c` cohomology sheaf of `R𝓗_Z^{ab}(K)`.

The direct image of abelian sheaves along the inclusion of a closed subset is exact
([Stacks, Tag 01AX]), and an exact functor commutes with the cohomology functors of the derived
categories.  This is the abelian counterpart of
`Stacks.Perfect.CechSupportTransport.pushHomologyIso`, built from the same
`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`. -/
public def abelianPushHomologyIso (c : ℤ)
    (K : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})) :
    (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) c).obj
        ((derivedAbelianSupportedPushforward X Z hZ).obj K) ≅
      (abelianClosedPushforward Z).obj
        ((DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) c).obj
          ((derivedAbelianSupportedSectionsOnClosed X Z hZ).obj K)) :=
  letI := abelianClosedPushforward_preservesFiniteLimits X Z hZ
  letI := abelianClosedPushforward_preservesFiniteColimits X Z hZ
  ((abelianClosedPushforward Z).mapDerivedCategoryHomologyFunctorIso c).app
    ((derivedAbelianSupportedSectionsOnClosed X Z hZ).obj K)

/-- The comparison of [Stacks, Tag 0G74] part (2) on abelian sheaves is natural in the
complex. -/
public lemma abelianPushHomologyIso_hom_naturality (c : ℤ)
    {K L : DerivedCategory (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})}
    (g : K ⟶ L) :
    (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) c).map
          ((derivedAbelianSupportedPushforward X Z hZ).map g) ≫
        (abelianPushHomologyIso X Z hZ c L).hom =
      (abelianPushHomologyIso X Z hZ c K).hom ≫
        (abelianClosedPushforward Z).map
          ((DerivedCategory.homologyFunctor
              (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) c).map
            ((derivedAbelianSupportedSectionsOnClosed X Z hZ).map g)) :=
  let := abelianClosedPushforward_preservesFiniteLimits X Z hZ
  let := abelianClosedPushforward_preservesFiniteColimits X Z hZ
  ((abelianClosedPushforward Z).mapDerivedCategoryHomologyFunctorIso c).hom.naturality
    ((derivedAbelianSupportedSectionsOnClosed X Z hZ).map g)

/-- **[Stacks, Tag 0G74] part (2) for the exact direct image, as a natural isomorphism of
functors on the derived category of abelian sheaves.** -/
public def abelianPushforwardHomologyIso (c : ℤ) :
    derivedAbelianSupportedPushforward X Z hZ ⋙
        DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) c ≅
      derivedAbelianSupportedSectionsOnClosed X Z hZ ⋙
        DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) c ⋙
          abelianClosedPushforward Z :=
  NatIso.ofComponents (abelianPushHomologyIso X Z hZ c)
    (fun g => abelianPushHomologyIso_hom_naturality X Z hZ c g)

/-! ### The unbounded model on `Z` is the classical model -/

/-- **`G ↦ ℋ ⁿ_Z(G[0])` with the cohomology sheaf taken in the unbounded derived category**, as a
functor of the coefficient abelian sheaf: the sheaf placed in degree `0`, its derived abelian
sections supported on `Z`, and the degree-`n` cohomology sheaf of the result.

This is the abelian counterpart of
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctor`. -/
public def abelianLocalCohomologySheafOfComplexFunctor (n : ℤ) :
    Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u} :=
  DerivedCategory.singleFunctor
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0 ⋙
    derivedAbelianSupportedSectionsOnClosed X Z hZ ⋙
      DerivedCategory.homologyFunctor
        (Sheaf (Opens.grothendieckTopology (TopCat.of Z)) AddCommGrpCat.{u}) n

/-- **The two models of `ℋ ⁿ_Z` on abelian sheaves agree, naturally in the coefficient sheaf.**
For `n : ℕ`, the degree-`n` cohomology sheaf of `R𝓗_Z^{ab}(G[0])` taken in the unbounded derived
category is Mathlib's classical right derived functor `Rⁿ H_Z` applied to `G`.

`R𝓗_Z^{ab}` is a right derived functor of abelian supported sections with unit
`derivedAbelianSupportedSectionsOnClosedUnit` — the instance
`derivedAbelianSupportedSectionsOnClosed_isRightDerivedFunctor` — so this is the general
comparison `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` instantiated
there, exactly as its module-level counterpart
`Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplexFunctorIso` is.  Both sides
are computed from the chosen injective resolution of `G`: the right-hand side by definition, the
left-hand side because the extended resolution is K-injective, so the unit of `R𝓗_Z^{ab}` is
invertible on it.  The existence of K-injective resolutions is
`Stacks.Cohomology.Localization.enoughKInjectives`, abelian sheaves on a space being Grothendieck
abelian; there are no hypotheses beyond `hZ`. -/
public def abelianLocalCohomologySheafOfComplexFunctorIso (n : ℕ) :
    abelianLocalCohomologySheafOfComplexFunctor X Z hZ (n : ℤ) ≅
      (abelianSupportedSectionsOnClosed X Z hZ).rightDerived n :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
    (abelianSupportedSectionsOnClosed X Z hZ)
    (derivedAbelianSupportedSectionsOnClosed X Z hZ)
    (derivedAbelianSupportedSectionsOnClosedUnit X Z hZ)
    Stacks.Cohomology.Localization.enoughKInjectives n

/-- **The same comparison with its target spelled by `ClosedImmersionSheaves`.**  The respelled
abelian supported-sections functor `abelianSupportedSectionsOnClosed` *is*
`ClosedImmersionSheaves.supportedSectionsOnClosedFunctor`, so its `ℕ`-indexed right derived
functor is `ClosedImmersionSheaves.localCohomologySheafFunctor`; only the spelling of the two
sheaf categories differs.  This is the form a consumer written in the `ClosedImmersionSheaves`
spelling — such as
`Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward` — needs. -/
public def abelianLocalCohomologySheafFunctorIso (n : ℕ) :
    abelianLocalCohomologySheafOfComplexFunctor X Z hZ (n : ℤ) ≅
      ClosedImmersionSheaves.localCohomologySheafFunctor Z hZ n :=
  abelianLocalCohomologySheafOfComplexFunctorIso X Z hZ n

/-- **[Stacks, Tag 0G74] part (2) for the exact direct image, at a sheaf placed in degree `0`**,
with the target written through the unbounded model `abelianLocalCohomologySheafOfComplexFunctor`.

This is `abelianPushHomologyIso` at `G[0]`; the restatement exists because the composite below
has to have the two objects of its middle node spelled the same way on both sides, and the
`abelianLocalCohomologySheafOfComplexFunctor` spelling is the one the comparison of the two
models on `Z` is stated in.  The two types differ only by the projections computing
`CategoryTheory.Functor.comp`. -/
public def abelianPushHomologySingleIso (n : ℤ)
    (G : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :
    (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) n).obj
        ((derivedAbelianSupportedPushforward X Z hZ).obj
          ((DerivedCategory.singleFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj G)) ≅
      (abelianClosedPushforward Z).obj
        ((abelianLocalCohomologySheafOfComplexFunctor X Z hZ n).obj G) :=
  abelianPushHomologyIso X Z hZ n
    ((DerivedCategory.singleFunctor
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj G)

/-- The comparison of [Stacks, Tag 0G74] part (2) for the direct image is natural in the
coefficient sheaf placed in degree `0`. -/
public lemma abelianPushHomologySingleIso_hom_naturality (n : ℤ)
    {G G' : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}} (φ : G ⟶ G') :
    (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) n).map
          ((derivedAbelianSupportedPushforward X Z hZ).map
            ((DerivedCategory.singleFunctor
              (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).map φ)) ≫
        (abelianPushHomologySingleIso X Z hZ n G').hom =
      (abelianPushHomologySingleIso X Z hZ n G).hom ≫
        (abelianClosedPushforward Z).map
          ((abelianLocalCohomologySheafOfComplexFunctor X Z hZ n).map φ) :=
  abelianPushHomologyIso_hom_naturality X Z hZ n
    ((DerivedCategory.singleFunctor
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).map φ)

/-- The naturality of the comparison of the two models on `Z`: its `naturality` field, with the
identity functor of the target category removed. -/
public lemma abelianModelOnClosed_naturality (n : ℕ)
    {G G' : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}} (φ : G ⟶ G') :
    (abelianLocalCohomologySheafOfComplexFunctor X Z hZ (n : ℤ)).map φ ≫
        (abelianLocalCohomologySheafOfComplexFunctorIso X Z hZ n).hom.app G' =
      (abelianLocalCohomologySheafOfComplexFunctorIso X Z hZ n).hom.app G ≫
        ((abelianSupportedSectionsOnClosed X Z hZ).rightDerived n).map φ :=
  (abelianLocalCohomologySheafOfComplexFunctorIso X Z hZ n).hom.naturality φ

/-! ### The two models agree with the direct image folded in -/

/-- The component of the model comparison at a coefficient abelian sheaf: move the exact direct
image past the degree-`n` cohomology sheaf, then identify the unbounded model on `Z` with the
classical one. -/
public def abelianModelComponent (n : ℕ)
    (G : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :
    (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).obj
        ((derivedAbelianSupportedPushforward X Z hZ).obj
          ((DerivedCategory.singleFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).obj G)) ≅
      (abelianClosedPushforward Z).obj
        (((abelianSupportedSectionsOnClosed X Z hZ).rightDerived n).obj G) :=
  abelianPushHomologySingleIso X Z hZ (n : ℤ) G ≪≫
    (abelianClosedPushforward Z).mapIso
      ((abelianLocalCohomologySheafOfComplexFunctorIso X Z hZ n).app G)

/-- The component of the model comparison, with its two factors displayed.  Both sides are the
same term, `CategoryTheory.Iso.trans`, `CategoryTheory.Functor.mapIso` and
`CategoryTheory.Iso.app` all computing their `hom` field by projection. -/
public lemma abelianModelComponent_hom (n : ℕ)
    (G : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) :
    (abelianModelComponent X Z hZ n G).hom =
      (abelianPushHomologySingleIso X Z hZ (n : ℤ) G).hom ≫
        (abelianClosedPushforward Z).map
          ((abelianLocalCohomologySheafOfComplexFunctorIso X Z hZ n).hom.app G) :=
  rfl

/-- The component of the model comparison is natural in the coefficient abelian sheaf: the
naturality of the comparison of [Stacks, Tag 0G74] part (2) for the direct image, then the
naturality of the comparison of the two models on `Z`. -/
public lemma abelianModelComponent_hom_naturality (n : ℕ)
    {G G' : Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}} (φ : G ⟶ G') :
    (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ)).map
          ((derivedAbelianSupportedPushforward X Z hZ).map
            ((DerivedCategory.singleFunctor
              (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0).map φ)) ≫
        (abelianModelComponent X Z hZ n G').hom =
      (abelianModelComponent X Z hZ n G).hom ≫
        (abelianClosedPushforward Z).map
          (((abelianSupportedSectionsOnClosed X Z hZ).rightDerived n).map φ) := by
  rw [abelianModelComponent_hom, abelianModelComponent_hom, Category.assoc, ← Category.assoc,
    abelianPushHomologySingleIso_hom_naturality, Category.assoc,
    ← CategoryTheory.Functor.map_comp, abelianModelOnClosed_naturality,
    CategoryTheory.Functor.map_comp]

/-- **The abelian model comparison.**  For `n : ℕ`, the degree-`n` cohomology sheaf of
`i_* R𝓗_Z^{ab}(G[0])` — the unbounded model of `i_*ℋ ⁿ_Z` with the direct image folded into the
derived functor, which is the model the derived square of step (ii) of [Stacks, Tag 0G85] is
stated in — is the direct image of `Rⁿ H_Z(G)`, the classical `ℕ`-indexed model, naturally in the
coefficient abelian sheaf `G`.

This composes `abelianPushHomologyIso`, which moves the exact direct image past the cohomology
sheaf, with `abelianLocalCohomologySheafOfComplexFunctorIso`, which identifies the unbounded
model on `Z` with the classical one.  It is the abelian counterpart of
`Stacks.Perfect.GysinAbelianSquare.supportCohomologySheafFunctorLocalCohomologyIso`, and its
target is the functor
`Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward` in which
`Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso` takes its values. -/
public def abelianSupportedPushforwardModelIso (n : ℕ) :
    DerivedCategory.singleFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0 ⋙
        derivedAbelianSupportedPushforward X Z hZ ⋙
          DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ) ≅
      (abelianSupportedSectionsOnClosed X Z hZ).rightDerived n ⋙
        abelianClosedPushforward Z :=
  NatIso.ofComponents (abelianModelComponent X Z hZ n)
    (fun φ => abelianModelComponent_hom_naturality X Z hZ n φ)

/-- **The abelian model comparison with its target spelled by `ClosedImmersionSheaves`**, which is
the spelling of `Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward`, the functor
`Stacks.Perfect.GysinAbelianSquare.pushforwardLocalCohomologyForgetIso` takes its values in.  Only
the spelling of the sheaf categories differs from
`abelianSupportedPushforwardModelIso`. -/
public def abelianSupportedPushforwardLocalCohomologyIso (n : ℕ) :
    DerivedCategory.singleFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) 0 ⋙
        derivedAbelianSupportedPushforward X Z hZ ⋙
          DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (n : ℤ) ≅
      ClosedImmersionSheaves.localCohomologySheafFunctor Z hZ n ⋙ abelianClosedPushforward Z :=
  abelianSupportedPushforwardModelIso X Z hZ n

end Stacks.Cohomology.AbelianModelComparison

end
