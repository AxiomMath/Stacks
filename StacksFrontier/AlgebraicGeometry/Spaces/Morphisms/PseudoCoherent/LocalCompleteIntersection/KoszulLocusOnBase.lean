module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection.KoszulLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# The local complete intersection locus on the base

Consider a commutative triangle of algebraic spaces over a scheme `S`: a morphism `f : X ⟶ Y`
together with morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` such that `f ≫ q = p`. If `p` is flat,
locally of finite presentation and closed, and `q` is flat and locally of finite presentation,
then there is an open subspace `W` of `Z` through which a morphism `Z' ⟶ Z` factors exactly
when the base change `f_{Z'} : X_{Z'} ⟶ Y_{Z'}` is a local complete intersection morphism.
This is **Stacks 06CE**.

## Main definitions

* `AlgebraicGeometry.Space.koszulLocusOnBase` is the open subspace `W ⊂ Z`: the subspace cut
  out by the complement of the image under `p` of the non-Koszul locus of `f`, so that a point
  of `|Z|` lies in `W` exactly when `f` is Koszul at every point of `|X|` above it.
* `AlgebraicGeometry.Space.KoszulLocusStableUnderBaseChange` is the base-change assertion of
  Stacks 06CA: for a commutative triangle with `p` and `q` flat and locally of finite
  presentation, the base change of `f` along `Z' ⟶ Z` is Koszul at a point exactly when `f` is
  Koszul at its image in `|X|`.

## Main results

* `AlgebraicGeometry.Space.isLocalCompleteIntersection_iff_forall_koszulAt`: a morphism of
  algebraic spaces is a local complete intersection morphism exactly when it is Koszul at
  every point of its source.
* `AlgebraicGeometry.Space.isOpenSubspace_koszulLocusOnBase`: `W` is an open subspace of `Z`.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isLocalCompleteIntersection_baseChange`
  is the factorization criterion of **Stacks 06CE**, and
  `AlgebraicGeometry.Space.factorsThrough_koszulLocusOnBase_iff_isLocalCompleteIntersection`
  is the same statement with `W` named rather than quantified over. Both take two hypotheses:
  the base-change assertion of Stacks 06CA, and étale source locality of the Koszul property
  of morphisms of schemes, which is Stacks 069P restricted to étale coverings.

## Implementation notes

`W` is not obtained from an existence statement. The Koszul locus of `f` is open in `|X|` by
Stacks 06CA, so its complement is closed, and closedness of `p` makes the image of that
complement closed; `W` is the subspace `AlgebraicGeometry.Space.openSubspaceOfPoints` cut out
by the complement of that image through the correspondence of Stacks 03BZ. Consequently `W`
has a defining equation and its point set is that complement with no hypothesis at all;
openness of the Koszul locus, closedness of `p` and algebraicity of `Z` enter only in the
proof that it is an open subspace.

Factoring through `W` is the containment of the image of the points of `Z'` in that
complement, by Stacks 03IE. Being a local complete intersection morphism is being Koszul at
every point of the source, by the chart criterion of Stacks 04RF applied to the Koszul
property of morphisms of schemes; the base-change hypothesis identifies the latter, for
`f_{Z'}`, with the Koszul property of `f` at each point of `|X|` lying over a point of the
image of `Z'`, and the two conditions then agree by a complementation.

Of Stacks 06CA only the base-change half is taken as a hypothesis; the openness half is used
outright, as `AlgebraicGeometry.Space.isOpen_setOf_koszulAt`.

## References

* [Stacks Project, Tag 06CE](https://stacks.math.columbia.edu/tag/06CE)
* [Stacks Project, Tag 06CA](https://stacks.math.columbia.edu/tag/06CA)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 069P](https://stacks.math.columbia.edu/tag/069P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The Koszul property read off the Koszul locus -/

/-- A morphism of algebraic spaces over `S` is a local complete intersection morphism exactly
when it is Koszul at every point of its source: both sides are the every-étale-chart condition
of Stacks 03MJ at the Koszul property of morphisms of schemes, read globally and pointwise, and
the chart criterion of Stacks 04RF identifies them once that property is étale local on the
source and target. -/
public theorem isLocalCompleteIntersection_iff_forall_koszulAt
    (hsrc : MorphismProperty.IsLocalAtSource
      (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
        MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsLocalCompleteIntersection B S hS f ↔
      ∀ x : points B S hS X, KoszulAt B S hS f x := by
  have hP := isEtaleLocalOnSourceAndTarget_isLocalCompleteIntersectionMorphism hsrc
  show HoldsOnEveryEtaleChart B S hS
    (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
      MorphismProperty Scheme.{u}) f ↔ _
  rw [holdsOnEveryEtaleChart_iff_forall_atPoint B S hS _ hP hX hY f]
  refine forall_congr' fun x => ?_
  rw [holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS _ hP hX hY f x]
  exact ⟨fun ⟨U, hU, ⟨x', hx'⟩, hUf⟩ => ⟨U, hU, x', hx', hUf⟩,
    fun ⟨U, hU, x', hx', hUf⟩ => ⟨U, hU, ⟨x', hx'⟩, hUf⟩⟩

/-! ### The base-change assertion of Stacks 06CA, carried as a hypothesis -/

/-- **The base-change assertion of Stacks 06CA.** For a commutative triangle of algebraic
spaces over `S` given by `f : X ⟶ Y`, `p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`, with `p`
and `q` both flat and locally of finite presentation, the formation of the Koszul locus of `f`
commutes with base change along any morphism `Z' ⟶ Z`: the base change of `f` is Koszul at a
point of `|X ×_Z Z'|` exactly when `f` is Koszul at its image in `|X|`.

Its counterpart for morphisms of schemes is `AlgebraicGeometry.koszulAt_baseChange_iff`. -/
public def KoszulLocusStableUnderBaseChange : Prop :=
  ∀ {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X →
    IsAlgebraicSpace B S hS Y → IsAlgebraicSpace B S hS Z →
      ∀ (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p),
        IsFlat B S hS p → IsLocallyOfFinitePresentation B S hS p →
          IsFlat B S hS q → IsLocallyOfFinitePresentation B S hS q →
            ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Z' →
              ∀ (g : Z' ⟶ Z) (x' : points B S hS (pullback p g)),
                KoszulAt B S hS (baseChangeOverBase B S hS f p q hfq g) x' ↔
                  KoszulAt B S hS f
                    (pointsMap B S hS (pullback p g) (pullback.fst p g) x')

variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The local complete intersection locus on the base, Stacks 06CE -/

/-- **Stacks 06CE.** The open subspace `W ⊂ Z` of a morphism `f : X ⟶ Y` of algebraic spaces
over `S` whose source is given over `Z` by `p : X ⟶ Z`: the subspace of the base cut out by
the complement of the image under `p` of the set of points at which `f` is not Koszul, so that
a point of `|Z|` lies in `W` exactly when `f` is Koszul at every point of `|X|` above it. -/
@[stacks 06CE "the open subspace of the base"]
public def koszulLocusOnBase (f : X ⟶ Y) (p : X ⟶ Z) : Subfunctor Z :=
  openSubspaceOfPoints B S hS Z
    (pointsMap B S hS X p '' {x : points B S hS X | KoszulAt B S hS f x}ᶜ)ᶜ

/-- The point set of `W` is the complement of the image under `p` of the non-Koszul locus
of `f`. -/
@[stacks 06CE "the point set of the open subspace of the base"]
public theorem range_pointsMap_ι_koszulLocusOnBase (f : X ⟶ Y) (p : X ⟶ Z) :
    Set.range (pointsMap B S hS (koszulLocusOnBase B S hS f p).toFunctor
        (koszulLocusOnBase B S hS f p).ι) =
      (pointsMap B S hS X p '' {x : points B S hS X | KoszulAt B S hS f x}ᶜ)ᶜ :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- **Stacks 06CE.** `W` is an open subspace of `Z`.

The non-Koszul locus of `f` is closed because the Koszul locus is open by Stacks 06CA, its
image under `p` is closed because `p` is closed, and the complement of a closed set is open,
hence the point set of an open subspace by Stacks 03BZ. -/
@[stacks 06CE "the subspace of the base is open"]
public theorem isOpenSubspace_koszulLocusOnBase (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y)
    (p : X ⟶ Z) (hpc : IsClosedMorphism B S hS p) :
    IsOpenSubspace B S hS (koszulLocusOnBase B S hS f p) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hZ _
    (hpc _ (isOpen_setOf_koszulAt B S hS f).isClosed_compl).isOpen_compl

/-- The factorization criterion of Stacks 06CE, from the base-change assertion of Stacks 06CA
and étale source locality of the Koszul property of morphisms of schemes. Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` whose source and target are given over a third algebraic
space `Z` by morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`. If `p` is flat, locally of
finite presentation and closed and `q` is flat and locally of finite presentation, then a
morphism `Z' ⟶ Z` from an algebraic space factors through
`AlgebraicGeometry.Space.koszulLocusOnBase` exactly when the base change of `f` along it is a
local complete intersection morphism.

Factoring through `W` is the containment of the image of the points of `Z'` in the complement
of the image under `p` of the non-Koszul locus, by Stacks 03IE, and the base change of `f` is
a local complete intersection morphism exactly when it is Koszul at each of its points; the
base-change input reads the latter off from the Koszul property of `f` over the image of `Z'`,
and the two conditions then agree by a complementation. -/
public theorem factorsThrough_koszulLocusOnBase_iff_isLocalCompleteIntersection
    (hsrc : MorphismProperty.IsLocalAtSource
      (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
        MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage)
    (h06CA : KoszulLocusStableUnderBaseChange B S hS)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hpflat : IsFlat B S hS p) (hplfp : IsLocallyOfFinitePresentation B S hS p)
    (hpc : IsClosedMorphism B S hS p) (hqflat : IsFlat B S hS q)
    (hqlfp : IsLocallyOfFinitePresentation B S hS q)
    (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ' : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z) :
    (∃ r : Z' ⟶ (koszulLocusOnBase B S hS f p).toFunctor,
        r ≫ (koszulLocusOnBase B S hS f p).ι = g) ↔
      IsLocalCompleteIntersection B S hS (baseChangeOverBase B S hS f p q hfq g) := by
  have hbc := h06CA hX hY hZ f p q hfq hpflat hplfp hqflat hqlfp Z' hZ' g
  have hX' : IsAlgebraicSpace B S hS (pullback p g) :=
    isAlgebraicSpace_pullback B S hS p g hX hZ' hZ
  have hY' : IsAlgebraicSpace B S hS (pullback q g) :=
    isAlgebraicSpace_pullback B S hS q g hY hZ' hZ
  have hfibre : Set.range (pointsMap B S hS (pullback p g) (pullback.fst p g)) =
      pointsMap B S hS X p ⁻¹' Set.range (pointsMap B S hS Z' g) := by
    rw [← Set.image_univ, ← Set.image_univ,
      preimage_image_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback p g).flip Set.univ,
      Set.preimage_univ]
  rw [factorsThrough_openSubspace_iff_points B S hS hZ hZ' (koszulLocusOnBase B S hS f p)
      (isOpenSubspace_koszulLocusOnBase B S hS hZ f p hpc) g,
    range_pointsMap_ι_koszulLocusOnBase B S hS f p,
    isLocalCompleteIntersection_iff_forall_koszulAt B S hS hsrc hX' hY'
      (baseChangeOverBase B S hS f p q hfq g)]
  constructor
  · intro hsub x'
    rw [hbc x']
    by_contra hbad
    exact hsub ⟨_, rfl⟩ ⟨_, hbad, (pointsMap_apply_comm B S hS
      (IsPullback.of_hasPullback p g).flip.w x').symm⟩
  · intro hall z hz
    rintro ⟨x, hxbad, hx⟩
    obtain ⟨z', rfl⟩ := hz
    obtain ⟨x', hx'⟩ : x ∈ Set.range (pointsMap B S hS (pullback p g) (pullback.fst p g)) := by
      rw [hfibre]
      exact ⟨z', hx.symm⟩
    exact hxbad (hx' ▸ (hbc x').mp (hall x'))

/-- The existential form of Stacks 06CE, from the base-change assertion of Stacks 06CA and
étale source locality of the Koszul property of morphisms of schemes. Let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S` whose source and target are given over a third algebraic
space `Z` by `p : X ⟶ Z` and `q : Y ⟶ Z` with `f ≫ q = p`. If `p` is flat, locally of finite
presentation and closed and `q` is flat and locally of finite presentation, then there is an
open subspace `W` of `Z` through which a morphism `Z' ⟶ Z` from an algebraic space factors
exactly when the base change of `f` along it is a local complete intersection morphism.

The open subspace is `AlgebraicGeometry.Space.koszulLocusOnBase`. -/
public theorem exists_isOpenSubspace_iff_isLocalCompleteIntersection_baseChange
    (hsrc : MorphismProperty.IsLocalAtSource
      (@_root_.AlgebraicGeometry.IsLocalCompleteIntersectionMorphism.{u} :
        MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage)
    (h06CA : KoszulLocusStableUnderBaseChange B S hS)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hpflat : IsFlat B S hS p) (hplfp : IsLocallyOfFinitePresentation B S hS p)
    (hpc : IsClosedMorphism B S hS p) (hqflat : IsFlat B S hS q)
    (hqlfp : IsLocallyOfFinitePresentation B S hS q) :
    ∃ W : Subfunctor Z, IsOpenSubspace B S hS W ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z),
        (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
          IsLocalCompleteIntersection B S hS (baseChangeOverBase B S hS f p q hfq g) :=
  ⟨koszulLocusOnBase B S hS f p, isOpenSubspace_koszulLocusOnBase B S hS hZ f p hpc,
    fun Z' hZ' g =>
      factorsThrough_koszulLocusOnBase_iff_isLocalCompleteIntersection B S hS hsrc
        h06CA hX hY hZ f p q hfq hpflat hplfp hpc hqflat hqlfp Z' hZ' g⟩

end AlgebraicGeometry.Space

end
