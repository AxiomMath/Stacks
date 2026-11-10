module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedObjectRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtalePseudoCoherentObligation
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.ZariskiRingedSiteOpenSliceQuasicoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.RestrictionGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Restriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.IteratedSliceFiniteFreeSummands

/-!
# The étale conjunct of `P` travels across the open slice

The induction of Stacks 0DII carries a predicate `P` on objects of `D(𝒪_X)` with two conjuncts:
that `ε^*E` is `m`-pseudo-coherent on the small étale site, and that the cohomology sheaves of
`E` are quasi-coherent.  The locality capstone
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme` hands over,
over each member `V` of a covering of an open of `X`, the restriction of `E` read as a complex of
`𝒪_V`-modules along Mathlib's `AlgebraicGeometry.Scheme.Modules.overEquiv`; to run the induction
on `V` one needs `P` of *that* object, on `V`.

The quasi-coherence conjunct crosses the slice by
`AlgebraicGeometry.Scheme.isQuasicoherent_homology_modulesOverEquiv_overFunctor`.  **This module
carries the other one**: if `ε_X^*E` is `m`-pseudo-coherent on the small étale site of `X`, then
`ε_V^*(E|_V)` is `m`-pseudo-coherent on the small étale site of the open subscheme `V`.  With
both, `P` is available in full over each member of the covering.

## The route

Nothing about an open subscheme is used until the last step; the work is done at an arbitrary
object `U` of the small étale site of a scheme `S`, whose underlying scheme is
`AlgebraicGeometry.SmallEtale.objScheme B S hS U`.

1. **Stacks 08FU (3), restricting.**  `AlgebraicGeometry.RingedSite`
   `.isPseudoCoherentFrom_derivedRestriction_general` takes `m`-pseudo-coherence on
   `(S_étale, 𝒪)` to `m`-pseudo-coherence on the localization `(S_étale/U, 𝒪|_U)`.  It is stated
   at a free sections universe, so it reaches `RingedSite.{u + 1, u, u}`.
2. **The crossover `S_étale/U ≅ (objScheme U)_étale`.**  That identification is an
   equivalence of ringed sites *on the nose*,
   `AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence`, and the transport of
   `m`-pseudo-coherence along an arbitrary equivalence of ringed sites is
   `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse`.
   The two are joined below; see the implementation notes for the orientation, which is the one
   point that needs care.
3. **Stacks 03DV, the step the source leaves implicit.**  At an open `V` the composite of the two
   previous steps produces `m`-pseudo-coherence of `(𝓕^a)|_{V_étale}`, whereas what is wanted is
   `(𝓕|_V)^a`.  The two are identified by
   `AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictIso`, read through Mathlib's own
   identification of the slice reading with restriction along `V.ι`
   (`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`) and of restriction along an open
   immersion with pullback along it
   (`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`), and lifted to the derived
   categories by `Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso` and
   `.mapDerivedCategoryCompIso` — every functor in sight being additive and exact.

## Main results

* `AlgebraicGeometry.SmallEtale.isPseudoCoherentFrom_mapDerivedCategory_objRestrict`:
  **`m`-pseudo-coherence on the small étale site of `S` restricts, across the crossover, to the
  small étale site of the scheme of any object `U` of that site.**  Steps 1 and 2.
* `AlgebraicGeometry.SmallEtale.isPseudoCoherentFrom_mapDerivedCategory_opensRestrict`: the same
  at an open subscheme, with the target ringed site written as that of the scheme `V`.
* `AlgebraicGeometry.SmallEtale.associatedModuleOpensRestrictIso`: at an *open* `V` of `S`, the
  associated module of the reading of `𝓕|_V` as an `𝒪_V`-module is the crossover restriction of
  `𝓕^a` to `V_étale`.  Step 3 at the module level.
* `AlgebraicGeometry.SmallEtale.isPseudoCoherentFromSmallEtale_modulesOverEquiv_overFunctor`:
  **the étale conjunct of `P`, transported across the open slice.**
* `AlgebraicGeometry.SmallEtale`
  `.isPseudoCoherentFromSmallEtale_and_isQuasicoherent_homology_modulesOverEquiv`: **both
  conjuncts of `P` at once**, the second being
  `AlgebraicGeometry.Scheme.isQuasicoherent_homology_modulesOverEquiv_overFunctor`.
* `AlgebraicGeometry.SmallEtale.isPseudoCoherentFrom_of_locally_toScheme_smallEtale_quasicoherent`:
  **the locality step of Stacks 0DII, with `P` available in full over each member of the
  covering.**  This is the locality capstone with its last obligation on the local hypothesis
  removed.

## Implementation notes

**The orientation of the crossover, and why the symmetric equivalence is the one used.**
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse`
transports along `eqv : Y.C ≌ X.C` *from* `Y` *to* `X`, through a structure map
`φ : O_Y ⟶ eqv_* O_X` which it asks to be invertible.  Read at
`AlgebraicGeometry.SmallEtale.localizationEquivalence` itself — whose source is the small étale
site of the scheme of `U` and whose target is the slice — that moves pseudo-coherence from
`(objScheme U)_étale` to the slice, which is the wrong way round; so the transport is taken at
the *symmetric* equivalence, where the slice is the source.

In that orientation **both** structure maps are the identity, which is more than the orientation
of `Stacks.SheafOfModules.reindexEquivalence` gives: that construction uses
`Stacks.SheafOfModules.reindexBackSharp`, the counit whiskered into the sheaf of rings, for its
second structure map.  Here both reindexings are equalities —
`AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence` in one direction and
`AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence_symm` in the other, both by
`rfl` — because the structure sheaf of either site sends an object to the global functions on its
underlying scheme, and neither functor of the equivalence changes that scheme.  Taking the
identity rather than `reindexBackSharp` is what makes invertibility of `φ` free and the resulting
inverse transport *literally* `AlgebraicGeometry.SmallEtale.objRestrictFunctor`, with no bridging
isomorphism between two spellings of the crossover.

The first compatibility is then `𝒪.map (𝟙)ᵒᵖ = 𝟙`, the unit of
`AlgebraicGeometry.SmallEtale.localizationEquivalence` being the identity on objects and on
morphisms by `rfl`.  The second is not proved by hand but obtained from the first by
`Stacks.SheafOfModules.InternalHom.unit_of_counit`, exactly as at the Zariski open slice; the
direct computation that discharges the first exhausts the heartbeat budget on the second.

**The universes are not free here.**  `Stacks.SheafOfModules.InternalHom.siteEquivModulesOver`,
which the transport is built from, is stated at a single `RingedSite.{u, v, w}`; the small étale
ringed site of a scheme is `RingedSite.{u + 1, u, u}` and so is its slice at an object, the object
universe `max (u + 1) u` of `AlgebraicGeometry.RingedSite.over` being `u + 1`.  The two ringed
sites are therefore passed positionally with explicit universes, since letting them be inferred
leaves the stuck constraint `u + 1 =?= max (u + 1) ?m`.

**Which associated-module functor, on each side.**  `AlgebraicGeometry.SmallEtale.associatedModule`
and its retyping `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf` are the same functor, and
the comparison of step 3 uses both, each side of it being forced.  On `X` the source has to be
`SheafOfModules` of the sheaf of rings, which is where the object `E` and the derived functor of
`AlgebraicGeometry.SmallEtale.IsPseudoCoherentFromSmallEtale` live, so the retyping is used there.
On `V` the source has to be Mathlib's `AlgebraicGeometry.Scheme.Modules`, which is where
`AlgebraicGeometry.Scheme.Modules.overEquiv` lands, so the unretyped form is used there.  The two
categories are equal but their `CategoryTheory.Category` instances are not syntactically the same,
so a composite formed at one spelling does not admit the instances of the other; the two
`local instance`s below are the bridge, and they are `inferInstanceAs` and the theorem of
Stacks 08H8 respectively, so that nothing definitionally new is introduced.

The same phenomenon forces `AlgebraicGeometry.SmallEtale.opensRestrict`, a retyping of the
crossover whose target is written with the open subscheme `V` rather than with
`AlgebraicGeometry.SmallEtale.objScheme` of the corresponding object of the small étale site.  The
two schemes are equal by `rfl`, but `AlgebraicGeometry.SmallEtale.opensToSmallEtale` is a
definition and does not reduce at instance transparency, so a composite formed at one spelling
does not admit the exactness instances found at the other — the derived lift of step 3 needs its
two functors to have *one* target category, and that forces the choice.  The retyping is again
only a type ascription: its body is `AlgebraicGeometry.SmallEtale.objRestrict`, and its three
exactness instances are `inferInstanceAs` of the ones at the other spelling.

**The sheafification data of the iterated slices is `local` here.**  Restriction to a slice of the
small étale site has `HasSheafify` and `WEqualsLocallyBijective` as instances
(`AlgebraicGeometry.SmallEtale.hasSheafify_smallEtaleOver` and its companion), but the *iterated*
slices do not; they come from `Stacks.SheafOfModules.iteratedSliceHasSheafify` and the two
statements beside it, bridged to the `AlgebraicGeometry.RingedSite.over` spelling, which does not
reduce at instance transparency.  None of those bridges occurs in any statement below.

**Quasi-compactness and affineness are not used, and are not hidden.**  Every ε-side declaration
on the path takes `(B : BigEtaleSite) (S : Scheme) (hS : B.Contains S)` with `S` an ordinary
parameter and no affineness, quasi-compactness, noetherian or separatedness hypothesis; and the
big site containing `X` contains every open subscheme of it,
`AlgebraicGeometry.BigEtaleOver.contains_opens` (Stacks 000R (3)).  So the statements below carry
none either.  Quasi-compactness is a genuine cost of the *boundedness* step of clause (2) ⇒ (1),
`AlgebraicGeometry.SmallEtale.exists_isLE_Q_obj_of_isPseudoCoherentComplexFrom`, which is a
different statement and is not invoked here; the covering that the locality capstone lets one
choose — by `AlgebraicGeometry.Scheme.affineZeroHypercover_sieve₀_mem`, say — is where that cost
is to be paid.

## References

* [Stacks Project, Tag 0DII](https://stacks.math.columbia.edu/tag/0DII)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u d dZ dV dE

namespace AlgebraicGeometry.SmallEtale

/-! ### The two ringed sites the crossover compares -/

/-- The small étale ringed site of the scheme of an object `U` of the small étale site of `S`, at
the universes it actually has: left free, the object universe stays a metavariable and the
transports below produce a stuck universe constraint. -/
abbrev objRingedSite (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : SmallEtale B S hS) : RingedSite.{u + 1, u, u} :=
  smallEtaleRingedSite B (objScheme B S hS U) (contains_objScheme B S hS U)

/-- The localization of the small étale ringed site of `S` at an object `U`, at the universes it
actually has; the object universe `max (u + 1) u` of `AlgebraicGeometry.RingedSite.over` is
`u + 1`. -/
abbrev sliceRingedSite (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : SmallEtale B S hS) : RingedSite.{u + 1, u, u} :=
  (smallEtaleRingedSite B S hS).over U

/-- The inverse of the localization equivalence is continuous, at the
`CategoryTheory.Equivalence.symm` spelling that the transports of sheaves of modules along an
equivalence of ringed sites ask for. -/
instance isContinuous_localizationEquivalence_symm_functor (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS) :
    (localizationEquivalence B S hS U).symm.functor.IsContinuous
      ((topology B S hS).over U)
      (topology B (objScheme B S hS U) (contains_objScheme B S hS U)) :=
  inferInstanceAs ((localizationEquivalence B S hS U).inverse.IsContinuous
    ((topology B S hS).over U)
    (topology B (objScheme B S hS U) (contains_objScheme B S hS U)))

/-- The localization equivalence is continuous, at the `CategoryTheory.Equivalence.symm`
spelling. -/
instance isContinuous_localizationEquivalence_symm_inverse (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS) :
    (localizationEquivalence B S hS U).symm.inverse.IsContinuous
      (topology B (objScheme B S hS U) (contains_objScheme B S hS U))
      ((topology B S hS).over U) :=
  inferInstanceAs ((localizationEquivalence B S hS U).functor.IsContinuous
    (topology B (objScheme B S hS U) (contains_objScheme B S hS U))
    ((topology B S hS).over U))

/-- The inverse of the localization equivalence is continuous, at the
`AlgebraicGeometry.RingedSite.over` spelling of the slice topology, which does not reduce at
instance transparency. -/
instance isContinuous_localizationEquivalence_symm_functor' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS) :
    (localizationEquivalence B S hS U).symm.functor.IsContinuous
      (sliceRingedSite B S hS U).J (objRingedSite B S hS U).J :=
  isContinuous_localizationEquivalence_symm_functor B S hS U

/-- The localization equivalence is continuous, at the `AlgebraicGeometry.RingedSite.over`
spelling of the slice topology. -/
instance isContinuous_localizationEquivalence_symm_inverse' (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS) :
    (localizationEquivalence B S hS U).symm.inverse.IsContinuous
      (objRingedSite B S hS U).J (sliceRingedSite B S hS U).J :=
  isContinuous_localizationEquivalence_symm_inverse B S hS U

/-! ### The sheafification data of the iterated slices -/

/-- Sheafification of abelian-group-valued presheaves exists on an iterated slice `(S_étale/U)/W`
of the small étale site. -/
local instance iteratedSliceHasSheafify (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) (W : Over U) :
    HasSheafify (((topology B S hS).over U).over W) AddCommGrpCat.{u} :=
  Stacks.SheafOfModules.iteratedSliceHasSheafify AddCommGrpCat.{u} W

/-- On an iterated slice `(S_étale/U)/W` of the small étale site, the morphisms of
abelian-group-valued presheaves inverted by sheafification are the locally bijective ones. -/
local instance iteratedSliceWEqualsLocallyBijective (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) (W : Over U) :
    (((topology B S hS).over U).over W).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  Stacks.SheafOfModules.iteratedSliceWEqualsLocallyBijective AddCommGrpCat.{u} W

/-- Sheafification of abelian-group-valued presheaves exists on the slice of the ringed site
`S_étale/U` over any of its objects `W`. -/
local instance sliceRingedSiteHasSheafifyOver (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) (W : (sliceRingedSite B S hS U).C) :
    HasSheafify ((sliceRingedSite B S hS U).J.over W) AddCommGrpCat.{u} :=
  iteratedSliceHasSheafify B S hS U W

/-- On the slice of the ringed site `S_étale/U` over an object `W`, the morphisms of
abelian-group-valued presheaves inverted by sheafification are the locally bijective ones. -/
local instance sliceRingedSiteWEqualsLocallyBijectiveOver (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)
    (W : (sliceRingedSite B S hS U).C) :
    ((sliceRingedSite B S hS U).J.over W).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  iteratedSliceWEqualsLocallyBijective B S hS U W

/-- On the slice of the ringed site `S_étale/U` over an object `W`, the forgetful functor from
rings to abelian groups preserves sheaves. -/
local instance sliceRingedSiteHasSheafComposeOver (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) (W : (sliceRingedSite B S hS U).C) :
    ((sliceRingedSite B S hS U).J.over W).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  Stacks.SheafOfModules.iteratedSliceHasSheafCompose _ W

/-- Sheafification of abelian-group-valued presheaves exists on the ringed site `S_étale/U`. -/
local instance sliceRingedSiteHasSheafify (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) :
    HasSheafify (sliceRingedSite B S hS U).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify ((topology B S hS).over U) AddCommGrpCat.{u})

/-- On the ringed site `S_étale/U`, the morphisms of abelian-group-valued presheaves inverted by
sheafification are the locally bijective ones. -/
local instance sliceRingedSiteWEqualsLocallyBijective (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) :
    (sliceRingedSite B S hS U).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs (((topology B S hS).over U).WEqualsLocallyBijective AddCommGrpCat.{u})

/-! ### Exactness of the two factors of the crossover -/

/-- The reindexing half of the crossover is additive: it is a pushforward of sheaves of modules,
which acts on a morphism by acting on its underlying map of presheaves. -/
local instance additive_objRestrictFunctor (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) : (objRestrictFunctor B S hS U).Additive where
  map_add := by intros; rfl

/-- The reindexing half of the crossover preserves finite limits, being the functor of the
equivalence `AlgebraicGeometry.SmallEtale.objRestrictEquivalence`. -/
local instance preservesFiniteLimits_objRestrictFunctor (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) :
    PreservesFiniteLimits (objRestrictFunctor B S hS U) :=
  inferInstanceAs (PreservesFiniteLimits (objRestrictEquivalence B S hS U).functor)

/-- The reindexing half of the crossover preserves finite colimits, for the same reason as
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_objRestrictFunctor`. -/
local instance preservesFiniteColimits_objRestrictFunctor (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) :
    PreservesFiniteColimits (objRestrictFunctor B S hS U) :=
  inferInstanceAs (PreservesFiniteColimits (objRestrictEquivalence B S hS U).functor)

/-- Restriction of `𝒪_étale`-modules to the localization at `U` is additive. -/
local instance additive_etaleOverFunctor (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) :
    (SheafOfModules.overFunctor.{u} (structureSheaf B S hS) U).Additive where
  map_add := by intros; rfl

/-- Restriction of `𝒪_étale`-modules to the localization at `U` preserves finite limits. -/
local instance preservesFiniteLimits_etaleOverFunctor (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf B S hS) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction of `𝒪_étale`-modules to the localization at `U` preserves finite colimits. -/
local instance preservesFiniteColimits_etaleOverFunctor (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U : SmallEtale B S hS) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf B S hS) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

/-- `ε^*` is additive at the spelling whose source is Mathlib's
`AlgebraicGeometry.Scheme.Modules`.  The instance
`AlgebraicGeometry.SmallEtale.additive_associatedModuleOfSheaf` is at the retyping whose source is
`SheafOfModules` of the sheaf of rings; the two categories are equal but their
`CategoryTheory.Category` instances are not syntactically the same, so instance search does not
cross between them. -/
local instance additive_associatedModuleScheme (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : (associatedModule B S hS).Additive :=
  inferInstanceAs (associatedModuleOfSheaf B S hS).Additive

/-- `ε^*` is left exact at the `AlgebraicGeometry.Scheme.Modules` spelling.  This is the exactness
assertion of Stacks 08H8, `AlgebraicGeometry.SmallEtale.preservesFiniteLimits_associatedModule`,
which is stated at exactly this spelling and is a theorem rather than an instance there. -/
local instance preservesFiniteLimits_associatedModuleScheme (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) : PreservesFiniteLimits (associatedModule B S hS) :=
  preservesFiniteLimits_associatedModule B S hS

section Crossover

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : SmallEtale B S hS)

/-- **The second reindexing of the crossover is an equality too.**  The structure sheaf of the
small étale site of the scheme of `U`, transported along the *inverse* of
`AlgebraicGeometry.SmallEtale.localizationEquivalence`, *is* the structure sheaf of the
localization of `S_étale` at `U`.

This is the companion of `AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence` in the
other orientation, and holds for the same reason: both sheaves send an object over `U` to the
global functions on its underlying scheme, and the inverse of the localization equivalence leaves
that scheme untouched. -/
theorem reindexRing_localizationEquivalence_symm :
    Stacks.SheafOfModules.reindexRing ((topology B S hS).over U)
        (localizationEquivalence B S hS U).symm
        (structureSheaf B (objScheme B S hS U) (contains_objScheme B S hS U)) =
      (structureSheaf B S hS).over U :=
  rfl

/-- **The structure map of the crossover, in the orientation the transport uses, is the
identity.**  Its two sides are equal sheaves of rings by
`AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence_symm`. -/
def objRestrictPhi : (Stacks.SheafOfModules.Tensor.ringSheaf (sliceRingedSite B S hS U).O) ⟶
    ((localizationEquivalence B S hS U).symm.functor.sheafPushforwardContinuous RingCat.{u}
      (sliceRingedSite B S hS U).J (objRingedSite B S hS U).J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (objRingedSite B S hS U).O) :=
  𝟙 _

/-- **The inverse structure map of the crossover is the identity as well**, by
`AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence`.  It is the structure map
through which the transport below produces its functor, which is why the pseudo-coherence
statement that comes out is literally about
`AlgebraicGeometry.SmallEtale.objRestrictFunctor`. -/
def objRestrictPsi : (Stacks.SheafOfModules.Tensor.ringSheaf (objRingedSite B S hS U).O) ⟶
    ((localizationEquivalence B S hS U).symm.inverse.sheafPushforwardContinuous RingCat.{u}
      (objRingedSite B S hS U).J (sliceRingedSite B S hS U).J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (sliceRingedSite B S hS U).O) :=
  𝟙 _

/-- The structure map of the crossover is invertible, being the identity. -/
instance isIso_objRestrictPhi : IsIso (objRestrictPhi B S hS U) :=
  inferInstanceAs (IsIso (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (sliceRingedSite B S hS U).O)))

/-- **The first compatibility of the two structure maps of the crossover.**  With both of them the
identity it says that the structure sheaf of `(objScheme U)_étale` carries the counit of the
symmetric localization equivalence to the identity, which it does because that counit *is* the
identity: the unit of `AlgebraicGeometry.SmallEtale.localizationEquivalence` is `𝟙` on objects and
on morphisms, by `rfl`. -/
theorem objRestrictPhi_counit :
    Functor.whiskerRight (NatTrans.op (localizationEquivalence B S hS U).symm.counit)
        (Stacks.SheafOfModules.Tensor.ringSheaf (objRingedSite B S hS U).O).obj =
      (objRestrictPsi B S hS U).hom ≫
        (localizationEquivalence B S hS U).symm.inverse.op.whiskerLeft
          (objRestrictPhi B S hS U).hom := by
  ext A : 2
  change (Stacks.SheafOfModules.Tensor.ringSheaf (objRingedSite B S hS U).O).obj.map _ = 𝟙 _ ≫ 𝟙 _
  rw [Category.comp_id,
    ← (Stacks.SheafOfModules.Tensor.ringSheaf (objRingedSite B S hS U).O).obj.map_id]
  congr 1

/-- **The second compatibility of the two structure maps of the crossover.**  It is
`Stacks.SheafOfModules.InternalHom.unit_of_counit`: the first compatibility together with
invertibility of `φ` already determines it. -/
theorem objRestrictPhi_unit :
    (objRestrictPhi B S hS U).hom ≫
        (localizationEquivalence B S hS U).symm.functor.op.whiskerLeft
          (objRestrictPsi B S hS U).hom ≫
        Functor.whiskerRight (NatTrans.op (localizationEquivalence B S hS U).symm.unit)
          (Stacks.SheafOfModules.Tensor.ringSheaf (sliceRingedSite B S hS U).O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (sliceRingedSite B S hS U).O).obj :=
  @Stacks.SheafOfModules.InternalHom.unit_of_counit.{u + 1, u, u}
    (objRingedSite B S hS U) (sliceRingedSite B S hS U) (localizationEquivalence B S hS U).symm
    (isContinuous_localizationEquivalence_symm_functor' B S hS U)
    (isContinuous_localizationEquivalence_symm_inverse' B S hS U)
    (objRestrictPhi B S hS U) (isIso_objRestrictPhi B S hS U)
    (objRestrictPsi B S hS U) (objRestrictPhi_counit B S hS U)

/-- **The images of the objects over `U` cover the final object of `(objScheme U)_étale`.**  Every
object of the small étale site of the scheme of `U` is isomorphic to one of them — indeed equal to
one, the unit of the localization equivalence being the identity — so the sieve of arrows
factoring through them is the maximal sieve.

This is the covering hypothesis that the transport of pseudo-coherence along an equivalence of
ringed sites asks for. -/
theorem coversTop_localizationEquivalence_symm_functor :
    (objRingedSite B S hS U).J.CoversTop
      (localizationEquivalence B S hS U).symm.functor.obj := by
  intro Z
  refine (objRingedSite B S hS U).J.superset_covering ?_
    ((objRingedSite B S hS U).J.top_mem Z)
  intro T g _
  exact ⟨(localizationEquivalence B S hS U).functor.obj T,
    ⟨(localizationEquivalence B S hS U).unitIso.hom.app T⟩⟩

/-! ### Pseudo-coherence across the crossover -/

variable [HasDerivedCategory.{dE} (SheafOfModules.{u} (structureSheaf B S hS))]
  [hSliceDer : ∀ W : SmallEtale B S hS,
    HasDerivedCategory.{dE} (SheafOfModules.{u} ((structureSheaf B S hS).over W))]
  [HasDerivedCategory.{dE}
    (SheafOfModules.{u} (structureSheaf B (objScheme B S hS U) (contains_objScheme B S hS U)))]

/-- A derived-category model for the sheaves of modules of a slice of the small étale site, at the
`AlgebraicGeometry.RingedSite.ringSheaf` spelling of its sheaf of rings. -/
local instance hasDerivedCategory_etaleRingSheafOver (W : (smallEtaleRingedSite B S hS).C) :
    HasDerivedCategory.{dE}
      (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).over W)) :=
  hSliceDer W

/-- A derived-category model for the sheaves of modules of the localization of the small étale
ringed site at `U`. -/
local instance hasDerivedCategory_sliceRingedSite :
    HasDerivedCategory.{dE}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (sliceRingedSite B S hS U).O)) :=
  hSliceDer U

/-- **Pseudo-coherence restricts across the crossover, in two steps.**  If `F` is an
`m`-pseudo-coherent object of `D(𝒪_étale)` on `S`, then its restriction to the localization at
`U`, read on the small étale site of the scheme of `U`, is `m`-pseudo-coherent there.

The first step is Stacks 08FU (3),
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction_general`; the second is
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse` at
the symmetric localization equivalence, whose inverse transport of sheaves of modules is
`AlgebraicGeometry.SmallEtale.objRestrictFunctor` because the structure map it is taken along is
the identity.  See the implementation notes for the orientation and the universes. -/
theorem isPseudoCoherentFrom_objRestrictFunctor_overFunctor
    (F : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS))) (m : ℤ)
    (hF : (smallEtaleRingedSite B S hS).IsPseudoCoherentFrom F m) :
    (objRingedSite B S hS U).IsPseudoCoherentFrom
      ((objRestrictFunctor B S hS U).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u} (structureSheaf B S hS) U).mapDerivedCategory.obj
          F)) m :=
  @AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_pushforwardPushforwardEquivalence_inverse.{u
      + 1, u, u, dE, dE}
    (objRingedSite B S hS U) (sliceRingedSite B S hS U) (localizationEquivalence B S hS U).symm
    (isContinuous_localizationEquivalence_symm_functor' B S hS U)
    (isContinuous_localizationEquivalence_symm_inverse' B S hS U)
    (objRestrictPhi B S hS U) (objRestrictPsi B S hS U)
    (objRestrictPhi_counit B S hS U) (objRestrictPhi_unit B S hS U)
    (isIso_objRestrictPhi B S hS U)
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance
    (coversTop_localizationEquivalence_symm_functor B S hS U) _ m
    (@AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_derivedRestriction_general.{u + 1, u, u,
        dE, dE}
      (smallEtaleRingedSite B S hS) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance F m hF U)

/-- **Pseudo-coherence restricts across the crossover.**  The same statement as
`AlgebraicGeometry.SmallEtale.isPseudoCoherentFrom_objRestrictFunctor_overFunctor`, with the two
steps of the crossover composed into `AlgebraicGeometry.SmallEtale.objRestrict`, which is the
functor the comparison of Stacks 03DV is stated about.

The two readings agree because the descent of a composite of exact functors to the derived
categories is the composite of the descents,
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso`. -/
theorem isPseudoCoherentFrom_mapDerivedCategory_objRestrict
    (F : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS))) (m : ℤ)
    (hF : (smallEtaleRingedSite B S hS).IsPseudoCoherentFrom F m) :
    (objRingedSite B S hS U).IsPseudoCoherentFrom
      ((objRestrict B S hS U).mapDerivedCategory.obj F) m :=
  AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_iso (objRingedSite B S hS U) m
    (isPseudoCoherentFrom_objRestrictFunctor_overFunctor B S hS U F m hF)
    ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor.{u} (structureSheaf B S hS) U)
      (objRestrictFunctor B S hS U)).app F)

end Crossover

/-! ### At an open subscheme -/

-- Exactness of restriction to a slice of the Zariski site, and the derived-category model for
-- Mathlib's `AlgebraicGeometry.Scheme.Modules` of an open subscheme, with the attribute taken on
-- the very declarations whose instances the locality capstone's statement is elaborated against:
-- a second copy would be definitionally equal but not syntactically the same, and the object
-- spoken about below has to be the one the capstone hands over.
attribute [local instance] Scheme.overFunctorPreservesFiniteLimits
  Scheme.overFunctorPreservesFiniteColimits Scheme.hasDerivedCategory_opensToSchemeModules
  Scheme.hasDerivedCategory_ringCatSheafOver

section Opens

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (V : X.Opens)

/-- **The crossover at an open subscheme**, retyped so that its target is the category of
`𝒪_étale`-modules of the *open subscheme* `V` rather than of the scheme
`AlgebraicGeometry.SmallEtale.objScheme` of the corresponding object of the small étale site.

The two schemes are equal by `rfl`, but `AlgebraicGeometry.SmallEtale.opensToSmallEtale` is a
definition and does not reduce at instance transparency, so instance search does not cross between
the two spellings; the three `local instance`s below carry the exactness of the crossover across
by `inferInstanceAs`, whose defeq check is at default transparency and does.  This is a retyping
and not a second functor: the body is `AlgebraicGeometry.SmallEtale.objRestrict` itself. -/
abbrev opensRestrict : SheafOfModules.{u} (structureSheaf B X hX) ⥤
    SheafOfModules.{u} (structureSheaf B V.toScheme (BigEtaleOver.contains_opens B hX V)) :=
  objRestrict B X hX ((opensToSmallEtale B X hX).obj V)

/-- The crossover at an open subscheme is additive, by
`AlgebraicGeometry.SmallEtale.additive_objRestrictFunctor` and
`AlgebraicGeometry.SmallEtale.additive_etaleOverFunctor` read across the retyping. -/
local instance additive_opensRestrict : (opensRestrict B X hX V).Additive :=
  inferInstanceAs (objRestrict B X hX ((opensToSmallEtale B X hX).obj V)).Additive

/-- The crossover at an open subscheme preserves finite limits. -/
local instance preservesFiniteLimits_opensRestrict :
    PreservesFiniteLimits (opensRestrict B X hX V) :=
  inferInstanceAs
    (PreservesFiniteLimits (objRestrict B X hX ((opensToSmallEtale B X hX).obj V)))

/-- The crossover at an open subscheme preserves finite colimits. -/
local instance preservesFiniteColimits_opensRestrict :
    PreservesFiniteColimits (opensRestrict B X hX V) :=
  inferInstanceAs
    (PreservesFiniteColimits (objRestrict B X hX ((opensToSmallEtale B X hX).obj V)))

/-- **Stacks 03DV, the step the source leaves implicit, at an open subscheme, in the shape the
locality capstone hands over.**  Reading an `𝒪_X`-module on the open subscheme `V` — restrict it
to the slice of the small Zariski site at `V`, then read the result as an `𝒪_V`-module along
Mathlib's `AlgebraicGeometry.Scheme.Modules.overEquiv` — and then taking its associated module on
`V_étale` is the same as taking its associated module on `X_étale` and restricting that across the
crossover to `V_étale`.

This is `AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictIso` at the object
`(opensToSmallEtale B X hX).obj V`, whose scheme is `V.toScheme` and whose structure morphism is
`V.ι`, both by `rfl`; what is prefixed to it is Mathlib's own identification of that reading with
restriction along `V.ι` (`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv`) and of restriction
along an open immersion with pullback along it
(`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`).  No second comparison is
introduced: the slice identification used is Mathlib's. -/
def associatedModuleOpensRestrictIso :
    SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O) V ⋙
        (Scheme.Modules.overEquiv V).functor ⋙
          associatedModule B V.toScheme (BigEtaleOver.contains_opens B hX V) ≅
      associatedModuleOfSheaf B X hX ⋙ opensRestrict B X hX V :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv V) _ ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι) _ ≪≫
    associatedModuleObjRestrictIso B X hX ((opensToSmallEtale B X hX).obj V)

variable [HasDerivedCategory.{d}
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))]
  [∀ W : X.Opens,
    HasDerivedCategory.{dZ}
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O).over W))]
  [∀ W : X.Opens,
    HasDerivedCategory.{dV}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.toScheme.zariskiRingedSite.O))]
  [HasDerivedCategory.{dE} (SheafOfModules.{u} (structureSheaf B X hX))]
  [∀ W : SmallEtale B X hX,
    HasDerivedCategory.{dE} (SheafOfModules.{u} ((structureSheaf B X hX).over W))]
  [hVDer : HasDerivedCategory.{dE}
    (SheafOfModules.{u} (structureSheaf B V.toScheme (BigEtaleOver.contains_opens B hX V)))]

/-- A derived-category model for the `𝒪_étale`-modules of the open subscheme `V`, at the spelling
`AlgebraicGeometry.SmallEtale.objScheme` of its scheme that
`AlgebraicGeometry.SmallEtale.objRingedSite` produces.  The two schemes are equal by `rfl` but
`AlgebraicGeometry.SmallEtale.opensToSmallEtale` does not reduce at instance transparency. -/
local instance hasDerivedCategory_objSchemeOpens :
    HasDerivedCategory.{dE} (SheafOfModules.{u}
      (structureSheaf B (objScheme B X hX ((opensToSmallEtale B X hX).obj V))
        (contains_objScheme B X hX ((opensToSmallEtale B X hX).obj V)))) :=
  hVDer

omit [HasDerivedCategory.{d}
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))]
  [∀ W : X.Opens,
    HasDerivedCategory.{dZ}
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O).over W))]
  [∀ W : X.Opens,
    HasDerivedCategory.{dV}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf W.toScheme.zariskiRingedSite.O))] in
/-- **Pseudo-coherence restricts across the crossover at an open subscheme**, stated at the
`V.toScheme` spelling of the target ringed site.  This is
`AlgebraicGeometry.SmallEtale.isPseudoCoherentFrom_mapDerivedCategory_objRestrict` at the object
`(opensToSmallEtale B X hX).obj V`, retyped. -/
theorem isPseudoCoherentFrom_mapDerivedCategory_opensRestrict
    (F : DerivedCategory (SheafOfModules.{u} (structureSheaf B X hX))) (m : ℤ)
    (hF : (smallEtaleRingedSite B X hX).IsPseudoCoherentFrom F m) :
    (smallEtaleRingedSite B V.toScheme
        (BigEtaleOver.contains_opens B hX V)).IsPseudoCoherentFrom
      ((opensRestrict B X hX V).mapDerivedCategory.obj F) m :=
  isPseudoCoherentFrom_mapDerivedCategory_objRestrict B X hX
    ((opensToSmallEtale B X hX).obj V) F m hF

/-- **The étale conjunct of `P` travels across the open slice.**  Let `E` be an object of `D(𝒪_X)`
whose pullback `ε_X^*E` along the comparison of Stacks 08H7 is `m`-pseudo-coherent on the small
étale site of `X`.  Then, for every open `V` of `X`, the pullback `ε_V^*(E|_V)` is
`m`-pseudo-coherent on the small étale site of the open subscheme `V`, where `E|_V` is the reading
of the restriction of `E` as a complex of `𝒪_V`-modules along Mathlib's
`AlgebraicGeometry.Scheme.Modules.overEquiv` — the very object the locality capstone
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme` asks about.

This is the conjunct of the predicate `P` of the induction of Stacks 0DII that
`AlgebraicGeometry.Scheme.isQuasicoherent_homology_modulesOverEquiv_overFunctor` does not carry;
with both, `P` is available in full over each member of the capstone's covering.

The proof restricts `ε_X^*E` across the crossover
(`AlgebraicGeometry.SmallEtale.isPseudoCoherentFrom_mapDerivedCategory_opensRestrict`) and then
identifies the result with `ε_V^*(E|_V)` by the derived lift of
`AlgebraicGeometry.SmallEtale.associatedModuleOpensRestrictIso`, every functor involved being
additive and exact.

The comparisons are applied with their additivity and exactness arguments written out, ascribed at
each functor's own source and target.  The chain crosses the two spellings of the sheaf of rings of
the Zariski site and of its slice — `AlgebraicGeometry.Scheme.ringCatSheaf`, which Mathlib's
`AlgebraicGeometry.Scheme.Modules.overEquiv` and the associated-module functor are stated at, and
`Stacks.SheafOfModules.Tensor.ringSheaf` of `AlgebraicGeometry.Scheme.zariskiRingedSite`, which the
pseudo-coherence predicate of Stacks 08FT is stated at.  They are the same sheaves of rings by
`AlgebraicGeometry.Scheme.zariskiRingedSite_ringSheaf`, and the one derived-category model serves
both; what instance search does not cross is the *preadditive* structure, so an additivity instance
asked for at the other spelling of a composite's middle category is not found.  Ascribed, each is
found at the spelling it was registered at and crosses the definitional equality once. -/
theorem isPseudoCoherentFromSmallEtale_modulesOverEquiv_overFunctor
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))) (m : ℤ)
    (hE : IsPseudoCoherentFromSmallEtale B X hX E m) :
    IsPseudoCoherentFromSmallEtale B V.toScheme (BigEtaleOver.contains_opens B hX V)
      ((Scheme.Modules.overEquiv V).functor.mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)
          V).mapDerivedCategory.obj E)) m :=
  AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_iso
    (smallEtaleRingedSite B V.toScheme (BigEtaleOver.contains_opens B hX V)) m
    (isPseudoCoherentFrom_mapDerivedCategory_opensRestrict B X hX V _ m hE)
    ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          ((Scheme.Modules.overEquiv V).functor)
          (associatedModule B V.toScheme
            (BigEtaleOver.contains_opens B hX V))).symm.app
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)
          V).mapDerivedCategory.obj E) ≪≫
      (@Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _ _ _ _ _ _ _ _ _ _ _
        (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O) V)
        ((Scheme.Modules.overEquiv V).functor ⋙
          associatedModule B V.toScheme
            (BigEtaleOver.contains_opens B hX V))
        _ _ _
        (inferInstance : ((Scheme.Modules.overEquiv V).functor ⋙
          associatedModule B V.toScheme (BigEtaleOver.contains_opens B hX V)).Additive)
        (inferInstance : PreservesFiniteLimits ((Scheme.Modules.overEquiv V).functor ⋙
          associatedModule B V.toScheme (BigEtaleOver.contains_opens B hX V)))
        (inferInstance : PreservesFiniteColimits ((Scheme.Modules.overEquiv V).functor ⋙
          associatedModule B V.toScheme
            (BigEtaleOver.contains_opens B hX V)))).symm.app E ≪≫
      (@Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ _ _ _ _ _ _
        (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O) V ⋙
          (Scheme.Modules.overEquiv V).functor ⋙
            associatedModule B V.toScheme (BigEtaleOver.contains_opens B hX V))
        (associatedModuleOfSheaf B X hX ⋙ opensRestrict B X hX V)
        (@Functor.instAdditiveComp _ _ _ _ _ _
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O) V)
          inferInstance _ _ _
          ((Scheme.Modules.overEquiv V).functor ⋙
            associatedModule B V.toScheme (BigEtaleOver.contains_opens B hX V))
          (inferInstance : ((Scheme.Modules.overEquiv V).functor ⋙
            associatedModule B V.toScheme (BigEtaleOver.contains_opens B hX V)).Additive))
        (@Limits.comp_preservesFiniteLimits _ _ _ _ _ _
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O) V)
          ((Scheme.Modules.overEquiv V).functor ⋙
            associatedModule B V.toScheme (BigEtaleOver.contains_opens B hX V))
          inferInstance
          (inferInstance : PreservesFiniteLimits ((Scheme.Modules.overEquiv V).functor ⋙
            associatedModule B V.toScheme (BigEtaleOver.contains_opens B hX V))))
        (@Limits.comp_preservesFiniteColimits _ _ _ _ _ _
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O) V)
          ((Scheme.Modules.overEquiv V).functor ⋙
            associatedModule B V.toScheme (BigEtaleOver.contains_opens B hX V))
          inferInstance
          (inferInstance : PreservesFiniteColimits ((Scheme.Modules.overEquiv V).functor ⋙
            associatedModule B V.toScheme (BigEtaleOver.contains_opens B hX V))))
        (inferInstance : (associatedModuleOfSheaf B X hX ⋙ opensRestrict B X hX V).Additive)
        (inferInstance : PreservesFiniteLimits
          (associatedModuleOfSheaf B X hX ⋙ opensRestrict B X hX V))
        (inferInstance : PreservesFiniteColimits
          (associatedModuleOfSheaf B X hX ⋙ opensRestrict B X hX V))
        (associatedModuleOpensRestrictIso B X hX V)).app E ≪≫
      (@Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso _ _ _
        (inferInstance : HasDerivedCategory.{d}
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)))
        _ _ _ _ _ _ _ _ (associatedModuleOfSheaf B X hX) (opensRestrict B X hX V)
        (inferInstance : (associatedModuleOfSheaf B X hX).Additive)
        (inferInstance : PreservesFiniteLimits (associatedModuleOfSheaf B X hX))
        (inferInstance : PreservesFiniteColimits (associatedModuleOfSheaf B X hX))
        _ _ _).app E)

/-- **Both conjuncts of `P` travel across the open slice.**  The predicate of the induction of
Stacks 0DII — `m`-pseudo-coherence of `ε^*E` together with quasi-coherence of the cohomology
sheaves of `E` — holds of the reading of `E|_V` as a complex of `𝒪_V`-modules on the open
subscheme `V` as soon as it holds of `E` on `X`.

The second conjunct is
`AlgebraicGeometry.Scheme.isQuasicoherent_homology_modulesOverEquiv_overFunctor`; the first is
`AlgebraicGeometry.SmallEtale.isPseudoCoherentFromSmallEtale_modulesOverEquiv_overFunctor` above.
-/
theorem isPseudoCoherentFromSmallEtale_and_isQuasicoherent_homology_modulesOverEquiv
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))) (m : ℤ)
    (hE : IsPseudoCoherentFromSmallEtale B X hX E m)
    (hQ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)) j).obj
        E).IsQuasicoherent) :
    IsPseudoCoherentFromSmallEtale B V.toScheme (BigEtaleOver.contains_opens B hX V)
        ((Scheme.Modules.overEquiv V).functor.mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)
            V).mapDerivedCategory.obj E)) m ∧
      ∀ j : ℤ, ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O)) j).obj
        ((Scheme.Modules.overEquiv V).functor.mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)
            V).mapDerivedCategory.obj E))).IsQuasicoherent :=
  ⟨isPseudoCoherentFromSmallEtale_modulesOverEquiv_overFunctor B X hX V E m hE,
    fun j => Scheme.isQuasicoherent_homology_modulesOverEquiv_overFunctor X V E hQ j⟩

end Opens

/-! ### The locality step of Stacks 0DII, with `P` available over each member -/

section Locality

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))]
  [∀ W : X.Opens,
    HasDerivedCategory.{dZ}
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O).over W))]
  [∀ W : X.Opens,
    HasDerivedCategory.{dV}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.toScheme.zariskiRingedSite.O))]
  [HasDerivedCategory.{dE} (SheafOfModules.{u} (structureSheaf B X hX))]
  [∀ W : SmallEtale B X hX,
    HasDerivedCategory.{dE} (SheafOfModules.{u} ((structureSheaf B X hX).over W))]
  [∀ W : X.Opens, HasDerivedCategory.{dE}
    (SheafOfModules.{u} (structureSheaf B W.toScheme (BigEtaleOver.contains_opens B hX W)))]

/-- **The locality step of Stacks 0DII, with the predicate `P` available in full over each member
of the covering.**  Let `E` be an object of `D(𝒪_X)` satisfying `P` — that is, `ε_X^*E` is
`m`-pseudo-coherent on the small étale site of `X` and the cohomology sheaves of `E` are
quasi-coherent.  Suppose that every open `U` of `X` admits a covering over each member `V` of
which `m`-pseudo-coherence of `E|_V` on the *scheme* `V` follows from `P` of `E|_V` there.  Then
`E` is `m`-pseudo-coherent on `X`.

This is the shape in which the reduction "the question is local, so we may assume `X` affine"
is usable for 0DII: the local hypothesis may *assume* `P`, because both of its conjuncts are
discharged from `P` of `E` — the étale one by
`AlgebraicGeometry.SmallEtale.isPseudoCoherentFromSmallEtale_modulesOverEquiv_overFunctor` above
and the quasi-coherence one by
`AlgebraicGeometry.Scheme.isQuasicoherent_homology_modulesOverEquiv_overFunctor`, applied to the
capstone
`AlgebraicGeometry.Scheme.isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme_quasicoherent`.
-/
theorem isPseudoCoherentFrom_of_locally_toScheme_smallEtale_quasicoherent
    (E : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O))) (m : ℤ)
    (hE : IsPseudoCoherentFromSmallEtale B X hX E m)
    (hQ : ∀ j : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)) j).obj
        E).IsQuasicoherent)
    (h : ∀ U : X.Opens, ∃ S : Presieve U, Sieve.generate S ∈ X.zariskiRingedSite.J U ∧
      ∀ ⦃V : X.Opens⦄ (f : V ⟶ U), S f →
        IsPseudoCoherentFromSmallEtale B V.toScheme (BigEtaleOver.contains_opens B hX V)
            ((Scheme.Modules.overEquiv V).functor.mapDerivedCategory.obj
              ((SheafOfModules.overFunctor.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)
                V).mapDerivedCategory.obj E)) m →
          (∀ j : ℤ, ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf V.toScheme.zariskiRingedSite.O)) j).obj
            ((Scheme.Modules.overEquiv V).functor.mapDerivedCategory.obj
              ((SheafOfModules.overFunctor.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)
                V).mapDerivedCategory.obj E))).IsQuasicoherent) →
          V.toScheme.zariskiRingedSite.IsPseudoCoherentFrom
            ((Scheme.Modules.overEquiv V).functor.mapDerivedCategory.obj
              ((SheafOfModules.overFunctor.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.O)
                V).mapDerivedCategory.obj E)) m) :
    X.zariskiRingedSite.IsPseudoCoherentFrom E m := by
  refine Scheme.isPseudoCoherentFrom_zariskiRingedSite_of_locally_toScheme_quasicoherent
    X E m hQ fun U => ?_
  obtain ⟨S, hS, hdata⟩ := h U
  refine ⟨S, hS, fun {V} f hf hq => ?_⟩
  exact hdata f hf
    (isPseudoCoherentFromSmallEtale_modulesOverEquiv_overFunctor B X hX V E m hE) hq

end Locality

end AlgebraicGeometry.SmallEtale

end
