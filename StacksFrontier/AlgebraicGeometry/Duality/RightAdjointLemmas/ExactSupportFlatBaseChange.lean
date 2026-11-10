module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.ClosedQuotient
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedPushforwardConservative
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedTensorHomMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent

/-!
# Base change for sheaf Hom with exact support along a flat morphism

Consider a cartesian diagram of schemes

```
Z' --i'--> X'
|g         |f
Z --i----> X
```

in which `i` is a closed immersion and `Z`, `X'` are Tor independent over `X`. Then `i'` is a
closed immersion too, both `i` and `i'` present their sources as closed quotients of ringed
spaces, and the right adjoint `R ℰom(𝒪_Z, -)` of [Stacks, Tag 0A76] is available on both. The
section of the source opened by [Stacks, Tag 0E2J] attaches to this situation a canonical map

`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)`

in `D(𝒪_{Z'})`, functorial in `K`; that map is [Stacks, Tag 0E2K], and
`baseChangeSheafHomExactSupport` below is it. [Stacks, Tag 0E2M] asserts that it is invertible
when `f` is flat, `i` is pseudo-coherent and `K` lies in `D⁺_QCoh(𝒪_X)`.

## Main definitions

* `closedQuotientOfBaseChange` presents the base change `i'` of the closed immersion as a
  closed quotient morphism of ringed spaces, so that the right adjoint of [Stacks, Tag 0A76] is
  available on the left-hand column of the square.
* `derivedBaseChangeMapAt` is the derived base-change map of [Stacks, Tag 08HY] evaluated at
  `R ℰom(𝒪_Z, K)`, the one place the square enters the construction.
* `baseChangeSheafHomExactSupport` is the map of [Stacks, Tag 0E2K].

## Main results

* `isIso_derivedBaseChangeMapAt` is the invertibility of `derivedBaseChangeMapAt` supplied by
  [Stacks, Tag 0E23], the component of the Tor-independent base-change isomorphism.
* `isIso_of_isIso_modulePushforward_map` is the step "since `i'_*` is exact and faithful it
  suffices to show the map is an isomorphism after applying `Ri'_*`" of the source's proof of
  [Stacks, Tag 0E2L], read off the conservativity of derived pushforward along a closed quotient
  morphism.
* `baseChangeSheafHomExactSupport_isIso_of_flat_pseudoCoherent` is [Stacks, Tag 0E2M], in the
  restricted form described below.

## Implementation notes

**How the map is built.** The source constructs the map of [Stacks, Tag 0E2K] by adjointness:
under `Ri'_* ⊣ R ℰom(𝒪_{Z'}, -)` of [Stacks, Tag 0A76] on the left column, a map
`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` is the same thing as a map
`Ri'_* Lg^* R ℰom(𝒪_Z, K) ⟶ Lf^*K`; Tor independence turns `Ri'_* ∘ Lg^*` into `Lf^* ∘ Ri_*`,
and then `Lf^*` of the counit `Ri_* R ℰom(𝒪_Z, K) ⟶ K` does it. That is the composite passed to
`derivedSheafHomAdjunction.homEquiv` below, read right to left.

**The two models of pushforward.** The adjunction of [Stacks, Tag 0A76] has the functor induced
on derived categories by the exact functor `i_*` as its left adjoint, while the base-change map
of [Stacks, Tag 08HY] is stated for the total right derived functor `Ri_*`. The composite
passes through `derivedPushforwardComparison`, the identification of the two models, in both
directions — once on each column of the square.

**The hypothesis that is carried.** [Stacks, Tag 0E23] is stated in this library granted
`DerivedStalkBaseChangeEqKFlat`, the stalkwise identification of the derived
base-change map with the comparison of [Stacks, Tag 0661], demanded at K-flat complexes. That
hypothesis is therefore carried here as `hst`, exactly as
`derivedBaseChangeSquareIsoOfKFlatEq` carries it. It is a `Prop`, so the construction chooses
no data from it.

**What `D⁺_QCoh(𝒪_X)` is here.** The library has no single named `D⁺_QCoh`; the established
spelling is a conjunction at the use site, and that is what is used below: `_hbb` is
`DerivedCategoryB.IsBoundedBelow K`, cohomological boundedness below, and `_hqc` is
`Stacks.DerivedQCoh.IsDQCoh K`, quasi-coherence of every cohomology sheaf. Neither is weakened
and neither is dropped. The two are named with a leading underscore because, as explained
below, they are stated but not consumed.

**How much of [Stacks, Tag 0E2M] is covered.** The map is built unconditionally (granted the
carried `hst`), and the reduction of its invertibility to invertibility after `Ri'_*` is
proved. The remaining content of the tag is **not** covered, and the clause string on the
attribute says so: `baseChangeSheafHomExactSupport_isIso_of_flat_pseudoCoherent` takes that
invertibility after `Ri'_*` as the hypothesis `hpush`, and the hypotheses `[Flat f]`,
`[PseudoCoherent i]`, `_hbb` and `_hqc` of the tag are stated but not consumed.

The source's first proof reduces to affine schemes and then to the ring-level equality
`RHom_A(B, K) ⊗^L_A A' = RHom_{A'}(B', K ⊗^L_A A')` for `K ∈ D⁺(A)`, by way of [Stacks,
Tag 0E2L] and of the comparison of derived Hom on rings with derived sheaf Hom on schemes for a
**pseudo-coherent** module. Discharging `hpush` along that route takes three steps beyond the
reduction step below. First, `Ri'_*` of the map above must be identified with the internal-Hom
base-change map of [Stacks, Tag 08I3], the verification the source omits. Second, the map of
[Stacks, Tag 08I3] or of [Stacks, Tag 08I4] must be shown invertible. Third, the affine
comparison of [Stacks, Tag 0A6H] is needed for a pseudo-coherent first argument, whereas
`affinePerfectDerivedSheafHomIso` states it for a **perfect** one, and the structure sheaf of a
pseudo-coherent closed immersion is pseudo-coherent and not perfect. The ring-level criterion of
[Stacks, Tag 0E2A] is available, so these steps are the geometry between it and the tag, not the
algebra.

## References

* [Stacks Project, Tag 0E2J](https://stacks.math.columbia.edu/tag/0E2J)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0E2L](https://stacks.math.columbia.edu/tag/0E2L)
* [Stacks Project, Tag 0E2M](https://stacks.math.columbia.edu/tag/0E2M)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.ClosedImmersionBaseChange
open Stacks.ClosedImmersion

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Duality.ExactSupportBaseChange

/-! ### Conservativity of pushforward along a closed quotient morphism -/

/-- **The step "it suffices after `Ri'_*`".** A morphism of `D(𝒪_Z)` whose image under derived
pushforward along a closed quotient morphism of ringed spaces is invertible is itself
invertible. This is the opening move of the source's proof of [Stacks, Tag 0E2L]; the content
is `reflectsIsomorphisms_mapDerivedCategory_modulePushforward`, which holds because
`i_*` is exact and fully faithful by [Stacks, Tag 08KS]. -/
theorem isIso_of_isIso_modulePushforward_map (S : ClosedQuotientMorphismOfRingedSpaces.{u})
    {A B : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing S.Z))} (a : A ⟶ B)
    (h : IsIso ((modulePushforward S.i).mapDerivedCategory.map a)) :
    IsIso a :=
  CategoryTheory.isIso_of_reflects_iso _ (modulePushforward S.i).mapDerivedCategory

/-! ### The situation of Stacks 0E2J -/

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-- The base change `i'` of the closed immersion `i`, presented as a closed quotient morphism of
ringed spaces. A closed immersion is stable under base change, and
`closedQuotientOfClosedImmersion` turns it into the input of the adjunction of
[Stacks, Tag 0A76]. -/
def closedQuotientOfBaseChange (sq : IsPullback i' g f i) [IsClosedImmersion i] :
    ClosedQuotientMorphismOfRingedSpaces.{u} :=
  @closedQuotientOfClosedImmersion _ _ i' (isClosedImmersion_of_isPullback sq)

/-- The derived base-change map `Lf^* Ri_* M ⟶ Ri'_* Lg^* M` of [Stacks, Tag 08HY] at
`M = R ℰom(𝒪_Z, K)`. This is the only place the square enters the construction of the map of
[Stacks, Tag 0E2K]. -/
abbrev derivedBaseChangeMapAt (sq : IsPullback i' g f i) [IsClosedImmersion i]
    (K : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :=
  derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
    f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)
    ((closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport.obj K)

/-- **[Stacks, Tag 0E23] at `R ℰom(𝒪_Z, K)`.** For a cartesian square with `i` a closed
immersion and `Z`, `X'` Tor independent over `X`, the derived base-change map is invertible,
granted the stalkwise identification at K-flat complexes. -/
theorem isIso_derivedBaseChangeMapAt (sq : IsPullback i' g f i) [IsClosedImmersion i]
    (htor : AlgebraicGeometry.TorIndependent i f) (hst : DerivedStalkBaseChangeEqKFlat sq)
    (K : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    IsIso (derivedBaseChangeMapAt sq K) :=
  have := isIso_derivedBaseChangeSquare_of_kFlatEq sq htor hst
  NatIso.isIso_app_of_isIso (derivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom
    i.toLRSHom.toShHom f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)) _

/-! ### The base-change map of Stacks 0E2K -/

/-- **Stacks Project, Tag 0E2K.** The canonical base-change map

`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)`

in `D(𝒪_{Z'})`, for a cartesian square whose right-hand column `i` is a closed immersion and
whose corners `Z`, `X'` are Tor independent over `X`.

It is the map corresponding, under the adjunction `Ri'_* ⊣ R ℰom(𝒪_{Z'}, -)` of
[Stacks, Tag 0A76] on the left-hand column, to the composite

`Ri'_* Lg^* R ℰom(𝒪_Z, K) = Lf^* Ri_* R ℰom(𝒪_Z, K) ⟶ Lf^*K`

whose equality is the inverse of the derived base-change map of [Stacks, Tag 08HY], invertible
by [Stacks, Tag 0E23], and whose arrow is `Lf^*` of the counit of [Stacks, Tag 0A76]. The two
occurrences of `derivedPushforwardComparison` pass between the exact-functor and the total
right derived models of pushforward, which the adjunction and the base-change map are
respectively stated for. The stalkwise identification `hst` is the hypothesis [Stacks,
Tag 0E23] carries in this library. -/
@[stacks 0E2K "the canonical base-change map"]
def baseChangeSheafHomExactSupport (sq : IsPullback i' g f i) [IsClosedImmersion i]
    (htor : AlgebraicGeometry.TorIndependent i f) (hst : DerivedStalkBaseChangeEqKFlat sq)
    (K : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (derivedPullback g.toLRSHom.toShHom).obj
        ((closedQuotientOfClosedImmersion i).derivedSheafHomExactSupport.obj K) ⟶
      (closedQuotientOfBaseChange sq).derivedSheafHomExactSupport.obj
        ((derivedPullback f.toLRSHom.toShHom).obj K) :=
  ((closedQuotientOfBaseChange sq).derivedSheafHomAdjunction.homEquiv _ _)
    ((closedQuotientOfBaseChange sq).derivedPushforwardComparison.hom.app _ ≫
      CategoryTheory.inv (I := isIso_derivedBaseChangeMapAt sq htor hst K)
        (derivedBaseChangeMapAt sq K) ≫
      (derivedPullback f.toLRSHom.toShHom).map
        ((closedQuotientOfClosedImmersion i).derivedPushforwardComparison.inv.app _) ≫
      (derivedPullback f.toLRSHom.toShHom).map
        ((closedQuotientOfClosedImmersion i).derivedSheafHomAdjunction.counit.app K))

/-! ### Stacks 0E2M -/

/-- **Stacks Project, Tag 0E2M, in part.** In the situation of [Stacks, Tag 0E2J] — a cartesian
square whose right-hand column `i` is a closed immersion, with `Z` and `X'` Tor independent over
`X` — assume `f` flat and `i` pseudo-coherent. Then the map of [Stacks, Tag 0E2K] is an
isomorphism for `K` in `D⁺_QCoh(𝒪_X)`, which is `_hbb` together with `_hqc`.

**What is assumed rather than derived.** The hypothesis `hpush` says the map is already
invertible after derived pushforward along `i'`, and the proof is only the reduction
`isIso_of_isIso_modulePushforward_map`, that is, the step "since `i'_*` is exact and faithful it
suffices to show the map is an isomorphism after applying `Ri'_*`" of the source's proof of
[Stacks, Tag 0E2L]. The flatness of `f`, the pseudo-coherence of `i`, the boundedness `_hbb`
and the quasi-coherence `_hqc` are stated, so the statement is the tag's own and no hypothesis
of it has been dropped or weakened, but they are not consumed: discharging `hpush` from them is
precisely the remaining content of [Stacks, Tag 0E2M], and the module docstring names the three
steps it takes.

The attribute's clause string is deliberately narrow, and it is worth being explicit about why.
Read as an implication this statement is close to circular: `hpush` is invertibility of the map
after `Ri'_*`, the proof is conservativity of `Ri'_*`, and that conservativity is exactly what
makes `hpush` and the conclusion interchangeable. What the clause claims is therefore not that
the map is invertible — the tag's assertion, which is **not** proved here — but only that the
source's reduction step for [Stacks, Tag 0E2L], "since `i'_*` is exact and faithful it suffices
to show the map is an isomorphism after applying `Ri'_*`", is available in this library. -/
@[stacks 0E2M "only the reduction to invertibility after Ri'_*; see the docstring"]
theorem baseChangeSheafHomExactSupport_isIso_of_flat_pseudoCoherent
    (sq : IsPullback i' g f i) [IsClosedImmersion i] [AlgebraicGeometry.Flat f]
    [AlgebraicGeometry.PseudoCoherent i]
    (htor : AlgebraicGeometry.TorIndependent i f) (hst : DerivedStalkBaseChangeEqKFlat sq)
    (K : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (_hbb : DerivedCategoryB.IsBoundedBelow K)
    (_hqc : @Stacks.DerivedQCoh.IsDQCoh _ _ _
      (structureSheafRing X.toRingedSpace) _ _ _ _ _ K)
    (hpush : IsIso ((modulePushforward (closedQuotientOfBaseChange sq).i).mapDerivedCategory.map
      (baseChangeSheafHomExactSupport sq htor hst K))) :
    IsIso (baseChangeSheafHomExactSupport sq htor hst K) :=
  isIso_of_isIso_modulePushforward_map (closedQuotientOfBaseChange sq) _ hpush

end Stacks.Duality.ExactSupportBaseChange

end
