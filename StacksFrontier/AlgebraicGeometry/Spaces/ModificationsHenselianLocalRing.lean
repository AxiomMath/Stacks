module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPoints
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType

/-!
# Modifications of a decent algebraic space at a closed point and its henselian local ring

Let `X` be a decent algebraic space over a scheme `S` and let `x ∈ |X|` be a closed point whose
open complement `U = X ∖ {x}` has quasi-compact inclusion. Let `(W, w) → (X, x)` be an
elementary étale neighborhood with `W` affine and `w` the only point above `x` (Stacks 0BBP),
and let `R` be a henselization of the local ring of `W` at `w`, so that `R = 𝒪^h_{X, x}` by
Stacks 0EMY. With `V = Spec(R) ∖ {𝔪^h_x}` the base change along the canonical morphism
`Spec(R) ⟶ X` is a functor

`C_{X, x} ⟶ C_{Spec(R), V}`

from the category of morphisms `f : Y ⟶ X` of finite presentation with `f⁻¹(U) ⟶ U` an
isomorphism to the category of morphisms `g : Y ⟶ Spec(R)` of finite presentation with
`g⁻¹(V) ⟶ V` an isomorphism. These two categories and this functor are the data displayed in
Stacks 0BH0, whose assertion is that the functor is an equivalence of categories.

This file defines finite-presentation modifications, their base change, and the two categories
and the functor of the displayed equation.

## Main definitions

* `AlgebraicGeometry.Space.IsFinitePresentationModification` and
  `AlgebraicGeometry.Space.FinitePresentationModification` are the property and the category of
  algebraic spaces over `W` of finite presentation over `W` and unchanged over `W₀`.
* `AlgebraicGeometry.Space.finitePresentationBaseChangeFunctor` is base change of
  finite-presentation modifications along a morphism of algebraic spaces, taken into the
  modifications outside any open subspace of the source contained in the preimage.
* `AlgebraicGeometry.Space.ClosedPointNeighborhood` is the data fixed above: the space, the
  closed point, the quasi-compactness hypothesis, and the chosen affine elementary étale
  neighborhood.
* `AlgebraicGeometry.Space.ClosedPointNeighborhood.henselianSpace`,
  `AlgebraicGeometry.Space.ClosedPointNeighborhood.henselianClosedPoint` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhood.openAwayFromClosedPoint` are `Spec(R)`, its
  closed point `𝔪^h_x` and the punctured spectrum `V`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhood.modificationsAwayFromPoint`,
  `AlgebraicGeometry.Space.ClosedPointNeighborhood.modificationsAwayFromClosedPoint` and
  `AlgebraicGeometry.Space.ClosedPointNeighborhood.henselianBaseChangeFunctor` are the two
  categories and the functor displayed in Stacks 0BH0.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhood.map_ne_point`: a point of `Spec(R)` other
  than its closed point lies above a point of `X` other than `x`, so the punctured spectrum
  lands in `U`.
* `AlgebraicGeometry.Space.ClosedPointNeighborhood.henselianBaseChangeFunctorCompιIso`: the
  functor is base change along `Spec(R) ⟶ X`.

The assertion of Stacks 0BH0, that this functor is an equivalence of categories, is
`ClosedPointNeighborhood.isEquivalence_henselianBaseChangeFunctor_of_isHenselization` in
`StacksFrontier/AlgebraicGeometry/Spaces/ModificationsHenselianLocalRingEquivalence.lean`.

## Implementation notes

The henselian local ring of Stacks 0BGW is a colimit taken over the elementary étale
neighborhoods of `x`, whose index category has objects one universe up; it therefore lives in
`CommRingCat.{u + 1}` and its spectrum is not a scheme of the big fppf site of `S`. It is
carried here instead as an abstract henselization `R` in `Type u` of the local ring of a chosen
elementary étale neighborhood at its distinguished point, which is what it is by Stacks 0EMY,
together with the containment of `Spec(R)` in the site. The canonical morphism
`Spec(R) ⟶ Spec(𝒪_{W, w}) ⟶ W ⟶ X` is then built from Mathlib's
`AlgebraicGeometry.Scheme.fromSpecStalk`, so the site object representing `Spec(R)` is
constructed rather than assumed.

That the punctured spectrum lands in `U` is checked on points and factors into three steps: the
maximal ideal of a henselization is extended from the base, so only the closed
point of `Spec(R)` lies over the closed point of `Spec(𝒪_{W, w})`; the morphism from the
spectrum of a local ring is a pre-immersion, hence injective on points, so only that closed
point lies over `w`; and `w` is the only point of `W` above `x`. The comparison between the
points of a represented presheaf and the points of the representing scheme is
`AlgebraicGeometry.Space.pointsToScheme` and the homeomorphism of Stacks 03BX.

Decency of the space, affineness of the chosen neighborhood and quasi-compactness of the
inclusion of `U` are part of the data, as in the source; the construction of the functor uses
only closedness of `x`, uniqueness of `w` above `x`, and the henselization property of `R`.

## References

* [Stacks Project, Tag 0BH0](https://stacks.math.columbia.edu/tag/0BH0)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0BGW](https://stacks.math.columbia.edu/tag/0BGW)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimit_cospan_presheaf_modificationsHenselian
    {Z₁ Z₂ Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z₁ ⟶ Z) (f : Z₂ ⟶ Z) :
    HasLimit (cospan g f) :=
  @HasLimitsOfShape.has_limit _ _ _ _ functorCategoryHasLimitsOfShape _

/-! ### Modifications of finite presentation -/

/-- An algebraic space over `W`, of finite presentation over `W` and unchanged over `W₀`. -/
def IsFinitePresentationModification {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W₀ : Subfunctor W)
    (X : Over W) : Prop :=
  IsModification B S hS W₀ X ∧ IsFinitePresentation B S hS X.hom

/-- The category of algebraic spaces over `W` of finite presentation over `W` which are
isomorphisms over `W₀`. -/
abbrev FinitePresentationModification {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W₀ : Subfunctor W) :=
  ObjectProperty.FullSubcategory (IsFinitePresentationModification B S hS W₀)

/-- The three conditions on a finite-presentation modification: the source is an algebraic
space, the structure morphism is of finite presentation, and its base change to `W₀` is an
isomorphism. -/
theorem isFinitePresentationModification_iff {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W₀ : Subfunctor W} {X : Over W} :
    IsFinitePresentationModification B S hS W₀ X ↔
      IsAlgebraicSpace B S hS X.left ∧ IsFinitePresentation B S hS X.hom ∧
        IsIso (pullback.snd X.hom W₀.ι) :=
  ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩

/-- A finite-presentation modification is in particular a modification. -/
theorem IsFinitePresentationModification.isModification
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W₀ : Subfunctor W} {X : Over W}
    (h : IsFinitePresentationModification B S hS W₀ X) : IsModification B S hS W₀ X := h.1

/-- The base change of a morphism of finite presentation along a morphism of algebraic spaces
is of finite presentation. -/
theorem isFinitePresentation_pullback_snd {F G Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : F ⟶ G)
    (g : Z ⟶ G) (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hZ : IsAlgebraicSpace B S hS Z) (hk : IsFinitePresentation B S hS k) :
    IsFinitePresentation B S hS (pullback.snd k g) := by
  have _hsb := isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  refine ⟨?_, isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback k g) hk.2.1,
    isQuasiSeparated_pullback_snd B S hS k g hk.2.2⟩
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun ⦃X Y : AlgebraicSpaces B S hS⦄ (φ : X ⟶ Y) =>
      IsLocallyOfFinitePresentation B S hS φ.hom)
    (isPullback_homMk B S hS hF hZ hG
      (isAlgebraicSpace_pullback B S hS k g hF hZ hG)
      (IsPullback.of_hasPullback k g)) hk.1

/-- Base change of a finite-presentation modification of `W` outside `W₀` along a morphism
`f : V ⟶ W` is a finite-presentation modification of `V` outside any open subspace of `V`
contained in the preimage of `W₀`. -/
theorem isFinitePresentationModification_pullback {V W : AlgebraicSpaces B S hS} (f : V ⟶ W)
    (W₀ : Subfunctor W.obj) (V₀ : Subfunctor V.obj) (hV₀ : V₀ ≤ W₀.preimage f.hom)
    (X : FinitePresentationModification B S hS W₀) :
    IsFinitePresentationModification B S hS V₀
      ((Over.pullback f.hom).obj
        (ObjectProperty.ι (IsFinitePresentationModification B S hS W₀) |>.obj X)) := by
  have hrange : Subfunctor.range V₀.ι ≤ W₀.preimage f.hom := by
    rw [Subfunctor.range_ι]
    exact hV₀
  refine ⟨⟨isAlgebraicSpace_pullback B S hS X.obj.hom f.hom X.property.1.1 V.property
      W.property, ?_⟩, ?_⟩
  · exact Space.isIso_pullback_snd_of_factor _ (Subfunctor.lift V₀.ι hrange)
      (Subfunctor.lift_ι _ hrange)
      (isIso_pullback_snd_preimage B S hS X.obj.hom f.hom W₀ X.property.1.2)
  · exact isFinitePresentation_pullback_snd B S hS X.obj.hom f.hom X.property.1.1 W.property
      V.property X.property.2

/-- Base change along `f : V ⟶ W` of finite-presentation modifications of `W` outside `W₀`,
landing in the modifications of `V` outside an open subspace `V₀` of the preimage of `W₀`,
together with the natural isomorphism identifying it with pullback of slice categories. -/
def finitePresentationBaseChangeFunctor {V W : AlgebraicSpaces B S hS} (f : V ⟶ W)
    (W₀ : Subfunctor W.obj) (V₀ : Subfunctor V.obj) (hV₀ : V₀ ≤ W₀.preimage f.hom) :
    Σ F : FinitePresentationModification B S hS W₀ ⥤ FinitePresentationModification B S hS V₀,
      F ⋙ ObjectProperty.ι (IsFinitePresentationModification B S hS V₀) ≅
        ObjectProperty.ι (IsFinitePresentationModification B S hS W₀) ⋙
          Over.pullback f.hom :=
  ⟨ObjectProperty.lift _
      (ObjectProperty.ι (IsFinitePresentationModification B S hS W₀) ⋙ Over.pullback f.hom)
      (isFinitePresentationModification_pullback B S hS f W₀ V₀ hV₀),
    ObjectProperty.liftCompιIso _ _ _⟩

/-! ### Only the closed point of a henselization lies over the closed point -/

/-- The maximal ideal of a henselization is extended from the base, so the only prime of a
henselization contracting to the maximal ideal of the base is its own maximal ideal. -/
theorem eq_closedPoint_of_comap_eq_closedPoint {A : Type u} [CommRing A] [IsLocalRing A]
    (R : Type u) [CommRing R] [IsLocalRing R] [Algebra A R]
    [IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) R] (q : PrimeSpectrum R)
    (hq : PrimeSpectrum.comap (algebraMap A R) q = IsLocalRing.closedPoint A) :
    q = IsLocalRing.closedPoint R := by
  have hcomap : q.asIdeal.comap (algebraMap A R) = IsLocalRing.maximalIdeal A :=
    congrArg PrimeSpectrum.asIdeal hq
  have hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A R) ≤ q.asIdeal :=
    Ideal.map_le_iff_le_comap.2 (le_of_eq hcomap.symm)
  rw [IsLocalRing.IsHenselization.map_maximalIdeal (L := IsLocalRing.ResidueField A)] at hmap
  exact PrimeSpectrum.ext
    ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le q.isPrime.ne_top hmap).symm

/-! ### The situation of Stacks 0BH0 -/

/-- The data fixed in the description of the modifications of a decent algebraic space at a
closed point by its henselian local ring: the space, a closed point whose open complement has
quasi-compact inclusion, and an affine elementary étale neighborhood of it carrying a single
point above it. -/
structure ClosedPointNeighborhood where
  /-- The algebraic space over the base. -/
  space : AlgebraicSpaces B S hS
  /-- The space is decent. -/
  decent : IsDecentSpace B S hS space.obj
  /-- The chosen point of the space. -/
  point : points B S hS space.obj
  /-- The chosen point is a closed point. -/
  isClosed_point : IsClosed ({point} : Set (points B S hS space.obj))
  /-- The inclusion of the open complement `X ∖ {x}` is quasi-compact. -/
  quasiCompact_complement : IsQuasiCompact B S hS
    (openSubspaceOfPoints B S hS space.obj {point}ᶜ).ι
  /-- The elementary étale neighborhood chosen at the point. -/
  neighborhood : ElementaryEtaleNeighborhood B S hS space.obj space.property point
  /-- The chosen neighborhood is an affine scheme. -/
  isAffine_neighborhood : IsAffine neighborhood.scheme.left.1
  /-- The distinguished point is the only point of the neighborhood above the chosen point. -/
  eq_of_map_eq_point : ∀ y : points B S hS (yoneda.obj neighborhood.scheme),
    pointsMap B S hS (yoneda.obj neighborhood.scheme) neighborhood.toSpace y = point →
      y = presheafPoint B S hS neighborhood.scheme neighborhood.point
        neighborhood.residueField_contained

namespace ClosedPointNeighborhood

variable {B S hS} (D : ClosedPointNeighborhood B S hS)

/-- The open subspace `U = X ∖ {x}` of the space. -/
def openAwayFromPoint : Subfunctor D.space.obj :=
  openSubspaceOfPoints B S hS D.space.obj {D.point}ᶜ

/-- The point set of `U = X ∖ {x}` is the complement of the chosen point. -/
theorem range_pointsMap_ι_openAwayFromPoint :
    Set.range (pointsMap B S hS D.openAwayFromPoint.toFunctor D.openAwayFromPoint.ι) =
      {D.point}ᶜ :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- `U = X ∖ {x}` is an open subspace of the space. -/
theorem isOpenSubspace_openAwayFromPoint :
    IsOpenSubspace B S hS D.openAwayFromPoint :=
  isOpenSubspace_openSubspaceOfPoints B S hS D.space.property _
    D.isClosed_point.isOpen_compl

/-- The local ring of the chosen neighborhood at its distinguished point. -/
abbrev neighborhoodStalk : CommRingCat.{u} :=
  D.neighborhood.scheme.left.1.presheaf.stalk D.neighborhood.point

section Henselian

variable (R : Type u) [CommRing R] [IsLocalRing R] [Algebra (D.neighborhoodStalk) R]
    [IsLocalRing.IsHenselization (D.neighborhoodStalk)
      (IsLocalRing.ResidueField (D.neighborhoodStalk)) R]
    (hR : B.Contains (Spec (.of R)))

/-- The canonical morphism of schemes `Spec(R) ⟶ W`: the spectrum of the henselization maps to
the spectrum of the local ring of `W` at `w`, which maps to `W`. -/
def specToNeighborhoodScheme : Spec (.of R) ⟶ D.neighborhood.scheme.left.1 :=
  Spec.map (CommRingCat.ofHom (algebraMap (D.neighborhoodStalk) R)) ≫
    D.neighborhood.scheme.left.1.fromSpecStalk D.neighborhood.point

/-- `Spec(R) = Spec(𝒪^h_{X, x})`, as an object of the big fppf site over `S`. -/
def henselianObj : BigFppfOver B S hS :=
  Over.mk (⟨D.specToNeighborhoodScheme R ≫ D.neighborhood.scheme.hom.1⟩ :
    B.obj hR ⟶ B.obj hS)

/-- The canonical morphism `Spec(R) ⟶ W` of objects of the site. -/
def toNeighborhoodHom : D.henselianObj R hR ⟶ D.neighborhood.scheme :=
  Over.homMk ⟨D.specToNeighborhoodScheme R⟩ rfl

/-- `Spec(R) = Spec(𝒪^h_{X, x})`, as an algebraic space over the base. -/
def henselianSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (D.henselianObj R hR),
    isAlgebraicSpace_yoneda B S hS (D.henselianObj R hR)⟩

/-- The canonical morphism `Spec(𝒪^h_{X, x}) ⟶ X` of algebraic spaces over the base. -/
def toSpaceHom : D.henselianSpace R hR ⟶ D.space :=
  ObjectProperty.homMk (yoneda.map (D.toNeighborhoodHom R hR) ≫ D.neighborhood.toSpace)

/-- The closed point `𝔪^h_x` of `Spec(𝒪^h_{X, x})`, as a point of the algebraic space that
spectrum represents. -/
def henselianClosedPoint : points B S hS (D.henselianSpace R hR).obj :=
  presheafPoint B S hS (D.henselianObj R hR) (IsLocalRing.closedPoint R)
    (B.residueField_spec_contains (D.henselianObj R hR).left.property
      (IsLocalRing.closedPoint R))

omit [IsLocalRing.IsHenselization (D.neighborhoodStalk)
  (IsLocalRing.ResidueField (D.neighborhoodStalk)) R] in
/-- The scheme point underlying `𝔪^h_x` is the closed point of `Spec(R)`. -/
theorem pointsToScheme_henselianClosedPoint :
    pointsToScheme B S hS (D.henselianObj R hR) (D.henselianClosedPoint R hR) =
      IsLocalRing.closedPoint R :=
  pointsToScheme_presheafPoint B S hS _ _ _

omit [IsLocalRing.IsHenselization (D.neighborhoodStalk)
  (IsLocalRing.ResidueField (D.neighborhoodStalk)) R] in
/-- The closed point of `Spec(𝒪^h_{X, x})` is a closed point of the point space. -/
theorem isClosed_henselianClosedPoint :
    IsClosed ({D.henselianClosedPoint R hR} :
      Set (points B S hS (D.henselianSpace R hR).obj)) := by
  have hpre : ({D.henselianClosedPoint R hR} :
        Set (points B S hS (D.henselianSpace R hR).obj)) =
      pointsToScheme B S hS (D.henselianObj R hR) ⁻¹'
        {IsLocalRing.closedPoint R} := by
    ext y
    have := (injective_pointsToScheme B S hS (D.henselianObj R hR)).eq_iff
      (a := y) (b := D.henselianClosedPoint R hR)
    rw [D.pointsToScheme_henselianClosedPoint R hR] at this
    exact this.symm
  rw [hpre]
  refine IsClosed.preimage ?_ (IsLocalRing.isClosed_singleton_closedPoint R)
  exact (schemePointsHomeomorph B S hS (D.henselianObj R hR)).continuous

/-- A point of `Spec(𝒪^h_{X, x})` other than its closed point lies above a point of `X` other
than `x`. -/
theorem map_ne_point (y : points B S hS (D.henselianSpace R hR).obj)
    (hy : y ≠ D.henselianClosedPoint R hR) :
    pointsMap B S hS (D.henselianSpace R hR).obj (D.toSpaceHom R hR).hom y ≠ D.point := by
  intro hcon
  set z := pointsMap B S hS (yoneda.obj (D.henselianObj R hR))
    (yoneda.map (D.toNeighborhoodHom R hR)) y
  have himg : pointsMap B S hS (yoneda.obj D.neighborhood.scheme) D.neighborhood.toSpace z =
      D.point :=
    (congrFun (pointsMap_comp B S hS (yoneda.obj (D.henselianObj R hR))
      (yoneda.map (D.toNeighborhoodHom R hR)) D.neighborhood.toSpace) y).symm.trans hcon
  have hnbhd := D.eq_of_map_eq_point _ himg
  have hpoint : pointsToScheme B S hS D.neighborhood.scheme z = D.neighborhood.point := by
    rw [hnbhd]
    exact pointsToScheme_presheafPoint B S hS D.neighborhood.scheme D.neighborhood.point
      D.neighborhood.residueField_contained
  have hscheme : D.neighborhood.scheme.left.1.fromSpecStalk D.neighborhood.point
      (Spec.map (CommRingCat.ofHom (algebraMap (D.neighborhoodStalk) R))
        (pointsToScheme B S hS (D.henselianObj R hR) y)) = D.neighborhood.point :=
    (pointsToScheme_pointsMap B S hS (D.toNeighborhoodHom R hR) y).symm.trans hpoint
  have hstalk : Spec.map (CommRingCat.ofHom (algebraMap (D.neighborhoodStalk) R))
      (pointsToScheme B S hS (D.henselianObj R hR) y) =
      IsLocalRing.closedPoint (D.neighborhoodStalk) :=
    (D.neighborhood.scheme.left.1.fromSpecStalk D.neighborhood.point).isEmbedding.injective
      (hscheme.trans Scheme.fromSpecStalk_closedPoint.symm)
  have hclosed := eq_closedPoint_of_comap_eq_closedPoint (A := D.neighborhoodStalk) R
    (pointsToScheme B S hS (D.henselianObj R hR) y) hstalk
  exact hy (AlgebraicGeometry.Space.injective_pointsToScheme B S hS (D.henselianObj R hR)
    (hclosed.trans (D.pointsToScheme_henselianClosedPoint R hR).symm))

/-- The punctured spectrum `V = Spec(𝒪^h_{X, x}) ∖ {𝔪^h_x}`. -/
def openAwayFromClosedPoint : Subfunctor (D.henselianSpace R hR).obj :=
  openSubspaceOfPoints B S hS (D.henselianSpace R hR).obj {D.henselianClosedPoint R hR}ᶜ

omit [IsLocalRing.IsHenselization (D.neighborhoodStalk)
  (IsLocalRing.ResidueField (D.neighborhoodStalk)) R] in
/-- The point set of `V` is the complement of the closed point. -/
theorem range_pointsMap_ι_openAwayFromClosedPoint :
    Set.range (pointsMap B S hS (D.openAwayFromClosedPoint R hR).toFunctor
        (D.openAwayFromClosedPoint R hR).ι) = {D.henselianClosedPoint R hR}ᶜ :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

omit [IsLocalRing.IsHenselization (D.neighborhoodStalk)
  (IsLocalRing.ResidueField (D.neighborhoodStalk)) R] in
/-- `V` is an open subspace of `Spec(𝒪^h_{X, x})`. -/
theorem isOpenSubspace_openAwayFromClosedPoint :
    IsOpenSubspace B S hS (D.openAwayFromClosedPoint R hR) :=
  isOpenSubspace_openSubspaceOfPoints B S hS (D.henselianSpace R hR).property _
    (D.isClosed_henselianClosedPoint R hR).isOpen_compl

/-- `V` is contained in the preimage of `U = X ∖ {x}`, because a point of
`Spec(𝒪^h_{X, x})` other than the closed point lies above a point of `X` other than `x`. -/
theorem openAwayFromClosedPoint_le_preimage :
    D.openAwayFromClosedPoint R hR ≤
      D.openAwayFromPoint.preimage (D.toSpaceHom R hR).hom := by
  have hsubset :
      Set.range (pointsMap B S hS (D.openAwayFromClosedPoint R hR).toFunctor
          ((D.openAwayFromClosedPoint R hR).ι ≫ (D.toSpaceHom R hR).hom)) ⊆
        Set.range (pointsMap B S hS D.openAwayFromPoint.toFunctor D.openAwayFromPoint.ι) := by
    rw [D.range_pointsMap_ι_openAwayFromPoint, pointsMap_comp]
    rintro z ⟨w, rfl⟩
    refine D.map_ne_point R hR _ ?_
    intro hcon
    have hmem : D.henselianClosedPoint R hR ∈
        ({D.henselianClosedPoint R hR} :
          Set (points B S hS (D.henselianSpace R hR).obj))ᶜ := by
      rw [← D.range_pointsMap_ι_openAwayFromClosedPoint R hR]
      exact ⟨w, hcon⟩
    exact hmem rfl
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS D.space.property
    (D.isOpenSubspace_openAwayFromClosedPoint R hR).1 D.openAwayFromPoint
    D.isOpenSubspace_openAwayFromPoint _).2 hsubset
  rw [← Subfunctor.image_le_iff]
  calc (D.openAwayFromClosedPoint R hR).image (D.toSpaceHom R hR).hom
      = Subfunctor.range ((D.openAwayFromClosedPoint R hR).ι ≫ (D.toSpaceHom R hR).hom) := by
        rw [Subfunctor.range_comp, Subfunctor.range_ι]
    _ = Subfunctor.range (g ≫ D.openAwayFromPoint.ι) := by rw [hg]
    _ ≤ D.openAwayFromPoint := by
        simpa only [Subfunctor.range_ι] using
          Subfunctor.range_comp_le g D.openAwayFromPoint.ι

/-! ### The two categories and the functor of Stacks 0BH0 -/

/-- The category of morphisms `f : Y ⟶ X` of finite presentation such that `f⁻¹(U) ⟶ U` is an
isomorphism, where `U = X ∖ {x}`: the source category displayed in Stacks 0BH0. -/
abbrev modificationsAwayFromPoint := FinitePresentationModification B S hS D.openAwayFromPoint

/-- The category of morphisms `g : Y ⟶ Spec(𝒪^h_{X, x})` of finite presentation such that
`g⁻¹(V) ⟶ V` is an isomorphism, where `V = Spec(𝒪^h_{X, x}) ∖ {𝔪^h_x}`: the target category
displayed in Stacks 0BH0. -/
abbrev modificationsAwayFromClosedPoint :=
  FinitePresentationModification B S hS (D.openAwayFromClosedPoint R hR)

/-- The base change functor along `Spec(𝒪^h_{X, x}) ⟶ X`: the base change of a
finite-presentation modification of `X` away from `x` is a finite-presentation modification of
`Spec(𝒪^h_{X, x})` away from its closed point, since `V` lies in the preimage of `U`. -/
def henselianBaseChangeFunctor :
    D.modificationsAwayFromPoint ⥤ D.modificationsAwayFromClosedPoint R hR :=
  (finitePresentationBaseChangeFunctor B S hS (D.toSpaceHom R hR) D.openAwayFromPoint
    (D.openAwayFromClosedPoint R hR) (D.openAwayFromClosedPoint_le_preimage R hR)).1

/-- The functor above is base change along `Spec(𝒪^h_{X, x}) ⟶ X` after forgetting the
finite-presentation and isomorphism-away conditions. -/
def henselianBaseChangeFunctorCompιIso :
    D.henselianBaseChangeFunctor R hR ⋙
        ObjectProperty.ι
          (IsFinitePresentationModification B S hS (D.openAwayFromClosedPoint R hR)) ≅
      ObjectProperty.ι (IsFinitePresentationModification B S hS D.openAwayFromPoint) ⋙
        Over.pullback (D.toSpaceHom R hR).hom :=
  (finitePresentationBaseChangeFunctor B S hS (D.toSpaceHom R hR) D.openAwayFromPoint
    (D.openAwayFromClosedPoint R hR) (D.openAwayFromClosedPoint_le_preimage R hR)).2

end Henselian

end ClosedPointNeighborhood

end AlgebraicGeometry.Space

end
