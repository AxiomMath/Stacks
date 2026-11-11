module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactCocontinuous
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionComparisonAlgebraicSpace

/-!
# Exactness of the restriction of modules to the small étale site of an algebraic space

Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over `(Sch/S)_{fppf}` with `𝒰`
representable by an algebraic space `U`, through a chosen equivalence over the site as in
Stacks 073M. Stacks 0GQS considers the functor

```
a : Mod(𝒳_étale, 𝒪_𝒳) ⟶ Mod(U_étale, 𝒪_U),    ℱ ↦ f^*ℱ|_{U_étale}
```

and its part (1) says that `a` is exact, because `f^* = f^{-1}` is exact and restriction to
`U_étale` is exact.

Here `a` is restriction of modules along the functor `u_U : U_étale ⥤ 𝒰` of Stacks 073M followed
by `f`, with the coefficient homomorphism `𝒪_U = (u_U ∘ f)^*𝒪_𝒳` of
`AlgebraicGeometry.Space.etaleChartStructureHom`; the two steps of the source's reason become the
two factors of that functor, and exactness is a single statement about the composite because the
composite is again continuous and cocontinuous.

## Main definitions

* `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImageFunctor`: the functor `a`, whose
  value on objects is `AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage`.

## Main results

* `AlgebraicGeometry.Space.isCocontinuous_etaleChartToFibred`: the functor `U_étale ⥤ 𝒳` is
  cocontinuous for the étale topologies.
* `AlgebraicGeometry.Space.preservesFiniteLimits_etaleRestrictedModuleInverseImageFunctor`:
  `a` preserves finite limits, with no smallness of `𝒳`.
* `AlgebraicGeometry.Space.exactFunctor_etaleRestrictedModuleInverseImageFunctor`: `a` is
  exact, item (1) of Stacks 0GQS.

The whole of Stacks 0GQS, all of its items, is
`AlgebraicGeometry.Stack.AlgebraicStacks.spaceRestriction_properties`, in
`StacksFrontier/AlgebraicGeometry/Stacks/RestrictionToAlgebraicSpaceProperties.lean`, for `𝒰` the
algebraic stack of `U`; it uses the exactness proved here.

## Implementation notes

**Why one statement about the composite.** The source factors `a` as `f^*` followed by
restriction to `U_étale`, and gives a reason for each factor. Both factors are restriction along
a functor of sites: `f^{-1}` is restriction along `f`, which is continuous and cocontinuous for
the inherited topologies by Stacks 06NW, and `·|_{U_étale}` is restriction along `u_U`, which is
continuous and cocontinuous by Stacks 073M. Restriction along a continuous and cocontinuous
functor of ringed sites is exact on modules, which is Stacks 04BD (2) at
`SheafOfModules.exactFunctor_pushforward_of_isCocontinuous`, so the composite is exact as soon as
it is continuous and cocontinuous; and `AlgebraicGeometry.Space.etaleChartToFibred` is the
composite functor, with continuity already available as
`AlgebraicGeometry.Space.etaleChartToFibred_isContinuous` and cocontinuity proved below from the
cocontinuity of the two factors. Factoring the proof instead of the functor would need the
intermediate category `Mod(𝒰_étale, 𝒪_𝒰)` and the comparison of its structure sheaf with both
others, which is not needed for the conclusion.

**The codomain.** It is written `SheafOfModules.{u} (structureRingSheaf B S hS U)`, which is
`AlgebraicGeometry.Space.Modules.{u, u} B S hS U.1 U.2` — the category `Mod(U_étale, 𝒪_U)` — with
the topology spelled as `AlgebraicGeometry.Space.SmallEtale.topology` rather than through
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which is the spelling in which the continuity and
cocontinuity instances below are stated.

**Left exactness costs nothing.** `SheafOfModules.preservesFiniteLimits_pushforward` holds for
every continuous functor, so the first result below needs no hypothesis beyond the source's: the
limits of sheaves of modules are computed in presheaves, where restriction is pointwise. It is
recorded separately because the second result adds the size hypothesis on `𝒳` described next.

**Essential smallness of `𝒳`.** Finite colimits of sheaves of modules are sheafifications of
presheaf colimits, so a statement about them presupposes that sheafification of
`AddCommGrpCat.{u}`-valued presheaves exists on `𝒳_étale`, which is what makes
`Mod(𝒳_étale, 𝒪_𝒳)` an abelian category in the first place. In this library that comes from
`EssentiallySmall.{u} 𝒳`, the standing size convention for the sites of a category fibred in
groupoids recorded in `StacksFrontier/AlgebraicGeometry/Stacks/EssentiallySmallSite.lean`; it is
the same binder that `AlgebraicGeometry.Stack.quasicoherentToFlatBaseChange` and
`AlgebraicGeometry.FibredSite.preservesColimitsOfSize_quasicoherentInclusion'` carry. No such
binder is needed on the small étale side: `AlgebraicGeometry.Space.SmallEtale.instEssentiallySmall`
is an instance.

**The other items of Stacks 0GQS.** They are about the restrictions `b`, `c`, `d` of `a` to
`LQCoh(𝒪_𝒳)`, `LQCoh^fbc(𝒪_𝒳)` and `QCoh(𝒪_𝒳)`, landing in `QCoh(U_étale, 𝒪_U)`. These
functors are `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohSpaceRestriction`,
`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcSpaceRestriction` and
`AlgebraicGeometry.Stack.AlgebraicStacks.qcohSpaceRestriction`, which exist because of the
general form of Stacks 0GQC,
`Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent`;
all the items are proved in the files around them and collected in
`AlgebraicGeometry.Stack.AlgebraicStacks.spaceRestriction_properties`.

## References

* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
* [Stacks Project, Tag 073M](https://stacks.math.columbia.edu/tag/073M)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 04BD](https://stacks.math.columbia.edu/tag/04BD)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒳 : Type v'} [Category.{w'} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)

/-- The functor `U_étale ⥤ 𝒳` of `AlgebraicGeometry.Space.etaleChartToFibred` is cocontinuous
for the étale topologies: a covering sieve of the image of an étale chart pulls back to a
covering sieve of that chart.

It is the composite of the functor `u_U` of Stacks 073M, cocontinuous by
`AlgebraicGeometry.Space.restrictionFunctor_isCocontinuous`, with the 1-morphism `f`, which is
cocontinuous for the inherited topologies by Stacks 06NW. -/
theorem isCocontinuous_etaleChartToFibred (hp : p.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) :
    (etaleChartToFibred B S hS p eU f).IsCocontinuous (SmallEtale.topology B S hS U.1)
      (BigFppfOver.associatedTopology B S hS r .etale) :=
  let := hp.isFibered
  let := restrictionFunctor_isCocontinuous B S hS U.1 p hp eU
  let := hf.isCocontinuous_inheritedTopology (BigFppfOver.baseOverTopology B S hS .etale)
  isCocontinuous_comp (restrictionFunctor B S hS U.1 p eU) f
    (SmallEtale.topology B S hS U.1) (BigFppfOver.associatedTopology B S hS p .etale)

/-- The functor `a : Mod(𝒳_étale, 𝒪_𝒳) ⥤ Mod(U_étale, 𝒪_U)` sending an
`𝒪_𝒳`-module `ℱ` to the restriction `f^*ℱ|_{U_étale}` of its inverse image along a 1-morphism
`f : 𝒰 ⥤ 𝒳` out of a category fibred in groupoids representable by the algebraic space `U`.

It is restriction of modules along the functor `U_étale ⥤ 𝒳` of
`AlgebraicGeometry.Space.etaleChartToFibred` with the coefficient homomorphism
`AlgebraicGeometry.Space.etaleChartStructureHom`, so its value on an object is
`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage`. -/
noncomputable abbrev etaleRestrictedModuleInverseImageFunctor (hp : p.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) :
    inheritedEtaleModules B S hS r hr ⥤ SheafOfModules.{u} (structureRingSheaf B S hS U) :=
  haveI := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
  SheafOfModules.pushforward (etaleChartStructureHom B S hS p r hp hr eU f hf)

/-- The value of the functor `a` on an object is the restriction `f^*ℱ|_{U_étale}` of
`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImage`. -/
theorem etaleRestrictedModuleInverseImageFunctor_obj (hp : p.IsFiberedInGroupoids)
    (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)
    (ℱ : inheritedEtaleModules B S hS r hr) :
    (etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf).obj ℱ =
      etaleRestrictedModuleInverseImage B S hS p r hp hr eU f hf ℱ :=
  rfl

/-- The functor `a : ℱ ↦ f^*ℱ|_{U_étale}` of Stacks 0GQS preserves finite limits.
This is half of the exactness of `a`
(`AlgebraicGeometry.Space.exactFunctor_etaleRestrictedModuleInverseImageFunctor`), and needs no
smallness of `𝒳`.

Limits of sheaves of modules are computed in presheaves, where restriction along a functor is
pointwise, so this holds for the direct image along any continuous functor of ringed sites. -/
theorem preservesFiniteLimits_etaleRestrictedModuleInverseImageFunctor
    (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) :
    PreservesFiniteLimits (etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf) :=
  let := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
  SheafOfModules.preservesFiniteLimits_pushforward
    (etaleChartStructureHom B S hS p r hp hr eU f hf)

/-- **Item (1) of Stacks 0GQS.** The functor `a : Mod(𝒳_étale, 𝒪_𝒳) ⥤ Mod(U_étale, 𝒪_U)`,
`ℱ ↦ f^*ℱ|_{U_étale}`, is exact. The whole of Stacks 0GQS is
`AlgebraicGeometry.Stack.AlgebraicStacks.spaceRestriction_properties`.

The source's two reasons are the continuity and the cocontinuity of the functor `U_étale ⥤ 𝒳`
along which the restriction is taken: `f^{-1}` is restriction along the 1-morphism `f` and
`·|_{U_étale}` is restriction along `u_U`, and both functors are continuous and cocontinuous, so
Stacks 04BD (2) applies to their composite. -/
theorem exactFunctor_etaleRestrictedModuleInverseImageFunctor [EssentiallySmall.{u} 𝒳]
    (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
    (eU : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (U.1 ⋙ typeToCat)).p)
    (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f) :
    exactFunctor (inheritedEtaleModules B S hS r hr)
      (SheafOfModules.{u} (structureRingSheaf B S hS U))
      (etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf) :=
  let := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
  let := isCocontinuous_etaleChartToFibred B S hS p r hp eU f hf
  let : HasSheafify (BigFppfOver.associatedTopology B S hS r .etale) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (BigFppfOver.associatedTopology B S hS r .etale).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let : HasSheafify (SmallEtale.topology B S hS U.1) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (SmallEtale.topology B S hS U.1).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  SheafOfModules.exactFunctor_pushforward_of_isCocontinuous
    (etaleChartToFibred B S hS p eU f) (etaleChartStructureHom B S hS p r hp hr eU f hf)

end AlgebraicGeometry.Space

end
