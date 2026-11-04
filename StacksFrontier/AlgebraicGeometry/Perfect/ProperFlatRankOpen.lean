module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
import StacksCore.Tactic.StacksAttribute

/-!
# The open subscheme over which a proper flat family has a single locally free direct image

Let `f : X ⟶ S` be a proper morphism of finite presentation, let `ℱ` be an `𝒪_X`-module of finite
presentation, flat over `S`, and fix `i` and `r`. [Stacks, Tag 0B9S] asserts that there is an open
subscheme `U ⊆ S` such that a morphism `T ⟶ S` factors through `U` exactly when `Rf_{T,*}ℱ_T` is
isomorphic to a finite locally free module of rank `r` placed in degree `i`.

The source proof is a reduction: by cohomology and base change ([Stacks, Tag 0B91]) the object
`K = Rf_*ℱ` of `D(𝒪_S)` is perfect and its formation commutes with arbitrary base change, and then
the assertion is [Stacks, Tag 0BDK] for `K`.

This file is that reduction. The open subscheme and the universal property it needs are already
available, as `AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen` and
`AlgebraicGeometry.Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff`, the latter for open
immersions `T ⟶ S` and with the exact restriction functor along `T ⟶ S` in place of the derived
pullback. What has to be supplied is the base change, which identifies that restriction of `Rf_*ℱ`
with `Rf_{T,*}ℱ_T`. Because `T ⟶ S` is an open immersion, this is not the base-change half of
[Stacks, Tag 0B91] in its full strength but [Stacks, Tag 08FE] — derived direct image commutes
with restriction to an open of the base — which this library carries unconditionally; so it is
proved here rather than assumed.

## Main definitions

* `AlgebraicGeometry.ProperFlatRankOpen.rankOpen`: **the open subscheme of [Stacks, Tag 0B9S]**,
  namely `AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen` at `Rf_*ℱ`.
* `AlgebraicGeometry.ProperFlatRankOpen.OpenImmersionBaseChangeDerivedPushforward`: the
  base-change half of [Stacks, Tag 0B91], clause (2), for an open immersion of the base and with
  restriction in place of the derived pullback.

## Main results

* `AlgebraicGeometry.ProperFlatRankOpen.openImmersionBaseChangeDerivedPushforward`: that
  base-change statement, **proved** from [Stacks, Tag 08FE].
* `AlgebraicGeometry.ProperFlatRankOpen.factorsThrough_rankOpen_iff`: **the characterising
  property of [Stacks, Tag 0B9S]**, for an open immersion `T ⟶ S`: it factors through `rankOpen`
  exactly when `Rf_{T,*}ℱ_T` is isomorphic to a finite locally free module of rank `r` placed in
  degree `i`.
* `AlgebraicGeometry.ProperFlatRankOpen.exists_isFiniteLocallyFreeOfRank_rankOpen`: taking
  `T = U` in that property, `Rf_{U,*}ℱ_U` *is* a finite locally free module of rank `r` placed in
  degree `i`.

## Implementation notes

**For which `T ⟶ S` the property is proved.** Only for open immersions. The universal property of
`AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen` is available only in that case, for the
reason its own file records: the description of `singleDegreeRankOpen` along an arbitrary morphism
needs the pointwise description of the open through the Betti numbers of the derived fibres, which
uses perfectness of the object and is not proved there. The statement below is correspondingly
restricted, and the clause string says so.

**The rank is a natural number**, where the source says "`i, r ∈ **Z**`". This follows
`AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen`, whose file notes that for a negative `r`
no open carries the object with that rank, so the open subscheme the source asserts is empty and
the statement is vacuous.

**How the base change is proved, and why no tensor machinery is involved.** Because the base
`g : T ⟶ S` is an *open immersion*, the base change needed here is not the general clause (2) of
[Stacks, Tag 0B91] — whose proof passes through cohomology and base change for a tensor product —
but the much weaker statement that forming the total direct image commutes with localization on
the base. That is [Stacks, Tag 08FE], carried unconditionally in this tree as
`Stacks.Cohomology.derivedPushforwardRestrictIso`: for a cartesian square of ringed spaces whose
two vertical edges are open immersions, `Rf_* ⋙ Rj^* ≅ Ri^* ⋙ Rg_*`, for arbitrary choices of
the four right derived functors presented by their units. Three small identifications turn that
into the statement below.

* The square is pushed to ringed spaces by `AlgebraicGeometry.isPullback_toShHom`, which applies
  because one edge is an open immersion; and `g'` is an open immersion because
  `AlgebraicGeometry.IsOpenImmersion` is stable under base change.
* Restriction along an open immersion is exact, so `Scheme.Modules.pullback` on it has a derived
  functor given by `CategoryTheory.Functor.mapDerivedCategory`, which is its own right derived
  functor (`CategoryTheory.Functor.isRightDerivedFunctor_of_inverts` at
  `mapDerivedCategoryFactorsh`); left exactness is
  `AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion`. This is what supplies
  the two restriction edges of [Stacks, Tag 08FE], and it is also why no derived functor appears
  on the left of the conclusion: `Scheme.Modules.restrictFunctor g` is isomorphic to
  `Scheme.Modules.pullback g` by `Scheme.Modules.restrictFunctorIsoPullback`, and
  `Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso` carries that
  isomorphism to the derived categories.
* On the other side, `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` moves the exact
  restriction past the placement of `ℱ` in degree zero, which is what makes the right-hand side
  `Rf_{T,*}` of an honest module rather than of a derived pullback.

So neither the tensor form of the base change at `𝒢` in degree zero nor the
unit coherence of `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso`
([Stacks, Tag 079U]) is used; for an arbitrary `g : T ⟶ S` those *are* the ingredients.

The perfectness half of [Stacks, Tag 0B91] is *not* needed and is not assumed: nothing in
`AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen` or in the universal property for open
immersions uses it.

**The derived-category model.** `HasDerivedCategory.standard` is installed at a raised priority,
for the reason recorded in `StacksFrontier/AlgebraicGeometry/DerivedAcyclic/Pushforward.lean`: the
import closure now also carries the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` as a global instance, and with the two at
equal priority instance search no longer resolves `HasDerivedCategory.{u + 1} X.Modules`.
[Stacks, Tag 08FE] and the derived direct image are stated in the standard model.

## References

* [Stacks Project, Tag 0B9S](https://stacks.math.columbia.edu/tag/0B9S)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic (derivedPushforwardModule)
open Stacks.SchemeCohomology (hom)
open Stacks.Cohomology.PerfectComplexTriangles (mapDerivedCategoryIsoOfNatIso)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProperFlatRankOpen

variable {X S : Scheme.{u}}

/-- **The open subscheme of [Stacks, Tag 0B9S].** The largest open subscheme of `S` on which
`Rf_*ℱ` is a finite locally free module of rank `r` placed in degree `i`, namely the open
subscheme of [Stacks, Tag 0BDK] at `Rf_*ℱ`. -/
public abbrev rankOpen (f : X ⟶ S) (F : X.Modules) (i : ℤ) (r : ℕ) : S.Opens :=
  Scheme.Modules.singleDegreeRankOpen (derivedPushforwardModule f F) i r

/-- **The base-change half of [Stacks, Tag 0B91], clause (2), for an open immersion of the base**:
for every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
T  --g---> S
```

with `g` an open immersion and `f` proper of finite presentation, and for every `𝒪_X`-module `ℱ`
of finite presentation, flat over `S`, the restriction of `Rf_*ℱ` along `g` is isomorphic to
`Rf'_*(g')^*ℱ`.

Restriction along an open immersion is exact, so no derived functor appears on the left; this is
the shape `AlgebraicGeometry.Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff` consumes.
It is proved in `openImmersionBaseChangeDerivedPushforward` below. -/
public def OpenImmersionBaseChangeDerivedPushforward : Prop :=
  ∀ {X S X' T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) [IsOpenImmersion g] (f' : X' ⟶ T)
      (g' : X' ⟶ X), IsPullback g' f' f g → FinitePresentation f → IsProper f →
    ∀ F : X.Modules, F.IsFinitePresentation → IsFlatOver f.toLRSHom.toShHom F →
      Nonempty ((Scheme.Modules.restrictFunctor g).mapDerivedCategory.obj
          (derivedPushforwardModule f F) ≅
        derivedPushforwardModule f' ((Scheme.Modules.pullback g').obj F))

/-- **The base-change half of [Stacks, Tag 0B91], clause (2), holds for an open immersion of the
base.** Over an open immersion the identification of the restriction of `Rf_*ℱ` with
`Rf_{T,*}(g')^*ℱ` is [Stacks, Tag 08FE], derived direct image commuting with restriction to an
open of the base, applied to the square pushed to ringed spaces; the finite presentation,
properness and flatness hypotheses are not used.

The restriction edges of [Stacks, Tag 08FE] are instantiated at
`CategoryTheory.Functor.mapDerivedCategory` of the exact pullback along the two open immersions,
and the resulting pullback of `ℱ` placed in degree zero is moved past the placement by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. -/
public theorem openImmersionBaseChangeDerivedPushforward :
    OpenImmersionBaseChangeDerivedPushforward.{u} := by
  intro X S X' T f g _ f' g' hsq _ _ F _ _
  have hg' : IsOpenImmersion g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hli : PreservesFiniteLimits (Scheme.Modules.pullback g') :=
    pullback_preservesFiniteLimits_of_isOpenImmersion g'
  have hlj : PreservesFiniteLimits (Scheme.Modules.pullback g) :=
    pullback_preservesFiniteLimits_of_isOpenImmersion g
  set Fi := Scheme.Modules.pullback g'
  set Fj := Scheme.Modules.pullback g
  -- The four right-derived-functor witnesses are supplied explicitly: their statements are
  -- phrased in the scheme spelling of the module categories, which instance search does not
  -- unify with the ringed-space spelling of [Stacks, Tag 08FE].
  have hiR : Fi.mapDerivedCategory.IsRightDerivedFunctor Fi.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _ Fi.mapDerivedCategoryFactorsh
  have hjR : Fj.mapDerivedCategory.IsRightDerivedFunctor Fj.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso S.Modules (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _ Fj.mapDerivedCategoryFactorsh
  have hfR : (schemeDerivedPushforward f).IsRightDerivedFunctor (schemeDerivedPushforwardUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := inferInstance
  have hf'R : (schemeDerivedPushforward f').IsRightDerivedFunctor (schemeDerivedPushforwardUnit f')
      (HomotopyCategory.quasiIso X'.Modules (ComplexShape.up ℤ)) := inferInstance
  let e : schemeDerivedPushforward f ⋙ Fj.mapDerivedCategory ≅
      Fi.mapDerivedCategory ⋙ schemeDerivedPushforward f' :=
    @Stacks.Cohomology.derivedPushforwardRestrictIso _ _ _ _
      (hom f) (hom g') (hom g) (hom f') _ _
      (isPullback_toShHom g' f' f g hsq) _ _ _ _
      (schemeDerivedPushforward f) (schemeDerivedPushforward f')
      Fi.mapDerivedCategory Fj.mapDerivedCategory
      (schemeDerivedPushforwardUnit f) (schemeDerivedPushforwardUnit f')
      Fi.mapDerivedCategoryFactorsh.inv Fj.mapDerivedCategoryFactorsh.inv
      hfR hf'R hiR hjR
  exact ⟨(mapDerivedCategoryIsoOfNatIso (Scheme.Modules.restrictFunctor g) Fj
        (Scheme.Modules.restrictFunctorIsoPullback g)).app _ ≪≫
      e.app _ ≪≫
      (schemeDerivedPushforward f').mapIso ((Fi.mapDerivedCategorySingleFunctor 0).app F)⟩

/-- **[Stacks, Tag 0B9S], the characterising property of the open subscheme, for an open immersion
of the base.** Let `f : X ⟶ S` be proper of finite presentation, let `ℱ` be an `𝒪_X`-module of
finite presentation, flat over `S`, and fix `i` and `r`. An open immersion `g : T ⟶ S` factors
through `rankOpen f ℱ i r` exactly when `Rf_{T,*}ℱ_T` is isomorphic to a finite locally free module
of rank `r` placed in degree `i`.

This is [Stacks, Tag 0BDK] at `Rf_*ℱ`, together with the base change of
`openImmersionBaseChangeDerivedPushforward`.

**Nothing is assumed.** The base-change input — the half of [Stacks, Tag 0B91] clause (2) which
identifies the restriction of `Rf_*ℱ` along `g` with `Rf_{T,*}(g')^*ℱ` — is proved here, as
`openImmersionBaseChangeDerivedPushforward`, from [Stacks, Tag 08FE]: derived direct image
commutes with restriction to an open of the base, which is available precisely because `g` is an
open immersion. So neither the tensor form of Tag 0B91 nor the unit coherence of
[Stacks, Tag 079U] is involved. The *perfectness* half of Tag 0B91 is likewise not needed:
neither `singleDegreeRankOpen` nor its universal property for open immersions uses it.

**Two scope restrictions**, neither a carried hypothesis. First, the characterising property is
delivered only for an open immersion `T ⟶ S`, not for an arbitrary morphism as the source states
it: the universal property of the open subscheme of [Stacks, Tag 0BDK] is available in this
library only for open immersions, as
`AlgebraicGeometry.Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff`, the description along
an arbitrary morphism needing the pointwise description of that open through the Betti numbers of
the derived fibres, which uses perfectness. Second, the rank `r` is a natural number where the
source says `i, r ∈ ℤ`; this follows `singleDegreeRankOpen`, and for a negative `r` the open the
source asserts is empty and the statement vacuous. -/
@[stacks 0B9S "for an open immersion T --> S only, and with rank r : N; nothing is assumed -- \
the base-change input is proved here as openImmersionBaseChangeDerivedPushforward from Tag 08FE. \
See the declaration docstring"]
public theorem factorsThrough_rankOpen_iff
    (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (i : ℤ) (r : ℕ)
    {T XT : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g] (fT : XT ⟶ T) (g' : XT ⟶ X)
    (hsq : IsPullback g' fT f g) :
    (∃ h : T ⟶ (rankOpen f F i r).toScheme, h ≫ (rankOpen f F i r).ι = g) ↔
      ∃ M : T.Modules,
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
          Nonempty (derivedPushforwardModule fT ((Scheme.Modules.pullback g').obj F) ≅
            (DerivedCategory.singleFunctor T.Modules i).obj M) := by
  obtain ⟨e⟩ := openImmersionBaseChangeDerivedPushforward.{u} f g fT g' hsq hf hproper F hfp hflat
  rw [Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff
    (derivedPushforwardModule f F) i r g]
  exact exists_congr fun M => and_congr_right fun _ =>
    ⟨fun hw => ⟨e.symm ≪≫ hw.some⟩, fun hw => ⟨e ≪≫ hw.some⟩⟩

/-- **On the open subscheme of [Stacks, Tag 0B9S] the direct image is what the tag says it is.**
Taking `T = U` in the characterising property: for a cartesian square over the inclusion of
`rankOpen f ℱ i r`, the object `Rf_{U,*}ℱ_U` is isomorphic to a finite locally free module of rank
`r` placed in degree `i`.

The `h0B91open` argument is **retained for interface compatibility and is not used**: the
base change it stands for is proved, as `openImmersionBaseChangeDerivedPushforward`.
This declaration carries no `@[stacks]` attribute, so the argument registers nothing — only
`factorsThrough_rankOpen_iff`, which does carry the tag, is stated without it. -/
public theorem exists_isFiniteLocallyFreeOfRank_rankOpen
    (h0B91open : OpenImmersionBaseChangeDerivedPushforward.{u})
    (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (i : ℤ) (r : ℕ)
    {XU : Scheme.{u}} (fU : XU ⟶ (rankOpen f F i r).toScheme) (g' : XU ⟶ X)
    (hsq : IsPullback g' fU f (rankOpen f F i r).ι) :
    ∃ M : (rankOpen f F i r).toScheme.Modules,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
        Nonempty (derivedPushforwardModule fU ((Scheme.Modules.pullback g').obj F) ≅
          (DerivedCategory.singleFunctor (rankOpen f F i r).toScheme.Modules i).obj M) :=
  (factorsThrough_rankOpen_iff f hf hproper F hfp hflat i r
    (rankOpen f F i r).ι fU g' hsq).1 ⟨𝟙 _, Category.id_comp _⟩

end AlgebraicGeometry.ProperFlatRankOpen

end
