module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.MatrixSubstitution
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.GeneralLinearTwoPowerSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.NoRationalCurves
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SliceFiniteProducts

/-!
# The action of `(GL₂)^m` on `(ℙ¹_k)^m` as a morphism of functors of points

The contraction step of [Stacks, Tag 0AEM] applies [Stacks, Tag 0AEJ] to the morphism
`G × C ⟶ G × Z` over `G = (GL_{2,k})^m`, built from the action of `G` on `(ℙ¹_k)^m`. Tag 0AEJ is
a statement about algebraic spaces over a base contained in a big fppf site, that is, about
functors on `AlgebraicGeometry.BigFppfOver`, whereas the action
`AlgebraicGeometry.projectiveLinePowerGeneralLinearAction` exists only as a morphism of schemes.
This file transports it.

Three things are needed, and each is obtained from the comparison functor
`CategoryTheory.Over.post B.inclusion` of
`StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SliceFiniteProducts`. First, `(ℙ¹_k)^m` is an
object of the site: it is a finite product in the site of copies of `ℙ¹_k`, whose image under the
comparison functor is the `m`-fold self-product `AlgebraicGeometry.projectiveSpacePowerOver` of
`ℙ¹_k` over `Spec k`, so that self-product has small enough underlying scheme. Second,
`(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` is an object of the site, by the fibre-product clause of
[Stacks, Tag 000R], and it is the product of `(GL₂)^m` and `(ℙ¹_k)^m` in the site. Third, the
comparison functor is fully faithful, so the action morphism of schemes, which lies over
`Spec k`, is the image of a unique morphism of the site, and the functor of points of an object
of the site is the restriction of the functor of points of the scheme over `Spec k` that it
names. The last identification is what makes the target of the action the power
`AlgebraicGeometry.Space.projectiveLinePower` that 0AEM's statement is phrased with.

## Main definitions

* `AlgebraicGeometry.Space.projectiveSpacePowerSiteObject`: `(ℙ¹_k)^m` as an object of the big
  fppf site over `Spec k`.
* `AlgebraicGeometry.Space.generalLinearTwoPowerProjectiveLinePowerSiteObject`:
  `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` as an object of the big fppf site over `Spec k`.
* `AlgebraicGeometry.Space.generalLinearTwoPowerProjection` and
  `AlgebraicGeometry.Space.projectiveSpacePowerProjection`: its two projections.
* `AlgebraicGeometry.Space.generalLinearTwoPowerActionSite`: the action, as a morphism of the
  big fppf site over `Spec k`.
* `AlgebraicGeometry.Space.generalLinearTwoPowerAction`: **the action, as a morphism of functors
  of points over the big fppf site** — a morphism
  `yoneda.obj ((GL₂)^m ×_{Spec k} (ℙ¹_k)^m) ⟶ projectiveLinePower k B hk (Fin m)`.
* `AlgebraicGeometry.Space.generalLinearTwoPowerActionGraph`: the morphism
  `(g, x) ↦ (g, g · x)` of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` over `(GL₂)^m`.

## Main results

* `AlgebraicGeometry.Space.isLimitBinaryFanProjections` and
  `AlgebraicGeometry.Space.isLimitBinaryFanFunctorProjections`: the site object is the fibre
  product of `(GL₂)^m` and `(ℙ¹_k)^m` over `Spec k`, in the site and at the level of functors of
  points.
* `AlgebraicGeometry.Space.isAlgebraicSpace_generalLinearTwoPowerProjectiveLinePower`: its
  functor of points is an algebraic space over `Spec k`, so [Stacks, Tag 0AEJ] applies to it.
* `AlgebraicGeometry.Space.generalLinearTwoPowerPointSection_comp_action`: the action restricted
  to the fibre over the `k`-point of `(GL₂)^m` named by an `m`-tuple `M` of invertible
  two-by-two matrices is the automorphism of `projectiveLinePower k B hk (Fin m)` that `M` gives.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0AEJ](https://stacks.math.columbia.edu/tag/0AEJ)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (k : Type u) [Field k] (B : BigFppfSite.{u})
  (hk : B.Contains (Spec (CommRingCat.of k))) (m : ℕ)

/-! ### `(ℙ¹_k)^m` as an object of the big fppf site over `Spec k` -/

include hk in
/-- **The `m`-fold self-product of `ℙ¹_k` over `Spec k` belongs to the big fppf site.** The
projective line belongs to it by `AlgebraicGeometry.Space.projectiveLine_mem_site`; the site has
finite products, and the comparison functor to schemes over `Spec k` preserves them, so the
`m`-fold product formed in the site has `AlgebraicGeometry.projectiveSpacePowerOver` as its
image. -/
theorem contains_projectiveSpacePowerOver :
    B.Contains (projectiveSpacePowerOver k 1 m).left := by
  have := preservesFiniteProducts_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk
  have e : ((Over.post (X := B.obj hk) B.inclusion).obj
        (∏ᶜ fun _ : Fin m => projectiveLineSiteObject k B hk)).left ≅
      (projectiveSpacePowerOver k 1 m).left :=
    (Over.forget (Spec (CommRingCat.of k))).mapIso
      (PreservesProduct.iso (Over.post (X := B.obj hk) B.inclusion)
        (fun _ : Fin m => projectiveLineSiteObject k B hk))
  show (projectiveSpacePowerOver k 1 m).left.size < B.cutoff
  rw [← Scheme.size_congr e]
  exact (∏ᶜ fun _ : Fin m => projectiveLineSiteObject k B hk).left.property

/-- **`(ℙ¹_k)^m` as an object of the big fppf site over `Spec k`**: the `m`-fold self-product of
`ℙ¹_k` over `Spec k`, with its structure morphism. -/
def projectiveSpacePowerSiteObject : BigFppfOver B (Spec (CommRingCat.of k)) hk :=
  siteObject B (Spec (CommRingCat.of k)) hk (contains_projectiveSpacePowerOver k B hk m)
    (projectiveSpacePowerOver k 1 m).hom

/-- The scheme over `Spec k` named by the site object of `(ℙ¹_k)^m` is the `m`-fold self-product
of `ℙ¹_k` over `Spec k`. -/
theorem projectiveSpacePowerSiteObject_overPost :
    (Over.post (X := B.obj hk) B.inclusion).obj (projectiveSpacePowerSiteObject k B hk m) =
      projectiveSpacePowerOver k 1 m :=
  rfl

/-! ### `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` as an object of the big fppf site over `Spec k` -/

include hk in
/-- **`(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` belongs to the big fppf site**, being a fibre product of two
objects of the site. This is the fibre-product clause of [Stacks, Tag 000R]. -/
theorem contains_generalLinearTwoPowerProjectiveLinePower :
    B.Contains (pullback (projectiveSpacePowerOver k 1 m).hom
      (Spec.map (generalLinearTwoPowerStructureMap k m))) :=
  Scheme.size_pullback_lt _ _ (contains_projectiveSpacePowerOver k B hk m)
    (contains_generalLinearTwoPowerCoordinateRing k B hk m)

/-- **`(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` as an object of the big fppf site over `Spec k`.** Its
underlying scheme is the fibre product over `Spec k` of the `m`-fold self-product of `ℙ¹_k` with
the general linear group, which is the scheme the action morphism
`AlgebraicGeometry.projectiveLinePowerGeneralLinearAction` is defined on, and its structure
morphism is the projection to `(GL₂)^m` followed by the structure morphism of `(GL₂)^m`. -/
def generalLinearTwoPowerProjectiveLinePowerSiteObject :
    BigFppfOver B (Spec (CommRingCat.of k)) hk :=
  siteObject B (Spec (CommRingCat.of k)) hk
    (contains_generalLinearTwoPowerProjectiveLinePower k B hk m)
    (pullback.snd (projectiveSpacePowerOver k 1 m).hom
        (Spec.map (generalLinearTwoPowerStructureMap k m)) ≫
      Spec.map (generalLinearTwoPowerStructureMap k m))

/-- The projection of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` to `(GL₂)^m`, as a morphism of schemes over
`Spec k`. -/
def generalLinearTwoPowerProjectionOver :
    (Over.post (X := B.obj hk) B.inclusion).obj
        (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) ⟶
      (Over.post (X := B.obj hk) B.inclusion).obj (generalLinearTwoPowerSiteObject k B hk m) :=
  Over.homMk (pullback.snd (projectiveSpacePowerOver k 1 m).hom
    (Spec.map (generalLinearTwoPowerStructureMap k m))) rfl

/-- The projection of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` to `(ℙ¹_k)^m`, as a morphism of schemes over
`Spec k`. -/
def projectiveSpacePowerProjectionOver :
    (Over.post (X := B.obj hk) B.inclusion).obj
        (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) ⟶
      (Over.post (X := B.obj hk) B.inclusion).obj (projectiveSpacePowerSiteObject k B hk m) :=
  Over.homMk (pullback.fst (projectiveSpacePowerOver k 1 m).hom
    (Spec.map (generalLinearTwoPowerStructureMap k m))) pullback.condition

/-- **The projection of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` to `(GL₂)^m` in the big fppf site.** -/
def generalLinearTwoPowerProjection :
    generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m ⟶
      generalLinearTwoPowerSiteObject k B hk m :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimage
    (generalLinearTwoPowerProjectionOver k B hk m)

/-- **The projection of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` to `(ℙ¹_k)^m` in the big fppf site.** -/
def projectiveSpacePowerProjection :
    generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m ⟶
      projectiveSpacePowerSiteObject k B hk m :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimage
    (projectiveSpacePowerProjectionOver k B hk m)

/-- **The two projections exhibit `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` as the product of `(GL₂)^m` and
`(ℙ¹_k)^m` in schemes over `Spec k`**: a binary product in a slice category is a fibre product
over its base. -/
def isLimitBinaryFanProjectionsOver :
    IsLimit (BinaryFan.mk (generalLinearTwoPowerProjectionOver k B hk m)
      (projectiveSpacePowerProjectionOver k B hk m)) :=
  IsLimit.pullbackConeEquivBinaryFanFunctor
    ((IsPullback.of_hasPullback (projectiveSpacePowerOver k 1 m).hom
      (Spec.map (generalLinearTwoPowerStructureMap k m))).flip.isLimit)

/-- **The two projections exhibit `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` as the product of `(GL₂)^m` and
`(ℙ¹_k)^m` in the big fppf site over `Spec k`**, the product in that site being the fibre product
over `Spec k`: the comparison functor to schemes over `Spec k` is fully faithful, hence reflects
limits, and the image of this fan is a limit by
`AlgebraicGeometry.Space.isLimitBinaryFanProjectionsOver`. -/
def isLimitBinaryFanProjections :
    IsLimit (BinaryFan.mk (generalLinearTwoPowerProjection k B hk m)
      (projectiveSpacePowerProjection k B hk m)) := by
  have : (Over.post (X := B.obj hk) B.inclusion).Full :=
    (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).full
  have : (Over.post (X := B.obj hk) B.inclusion).Faithful :=
    (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).faithful
  refine isLimitOfReflectsOfMapIsLimit (Over.post (X := B.obj hk) B.inclusion) _ _ ?_
  change IsLimit (BinaryFan.mk
    ((Over.post (X := B.obj hk) B.inclusion).map
      ((fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimage
        (generalLinearTwoPowerProjectionOver k B hk m)))
    ((Over.post (X := B.obj hk) B.inclusion).map
      ((fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimage
        (projectiveSpacePowerProjectionOver k B hk m))))
  rw [Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage]
  exact isLimitBinaryFanProjectionsOver k B hk m

/-! ### The functor of points of `(ℙ¹_k)^m` -/

/-- **The restricted functor of points of the `m`-fold self-product of `ℙ¹_k` over `Spec k` is
the `m`-fold power of the restricted functor of points of `ℙ¹_k`**: the restriction along the
comparison functor of the functor of points preserves finite products. -/
def projectiveSpacePowerRestrictedYonedaIso :
    (bigFppfRestrictedYoneda B (Spec (CommRingCat.of k)) hk).obj
        (projectiveSpacePowerOver k 1 m) ≅
      projectiveLinePower k B hk (Fin m) :=
  PreservesProduct.iso (bigFppfRestrictedYoneda B (Spec (CommRingCat.of k)) hk)
    (fun _ : Fin m => (projectiveSpaceOverRing 1 (CommRingCat.of k)).asOver
      (Spec (CommRingCat.of k)))

/-- **The functor of points of the site object of `(ℙ¹_k)^m` is the `m`-fold power
`AlgebraicGeometry.Space.projectiveLinePower` of the restricted functor of points of `ℙ¹_k`**,
which is the functor that [Stacks, Tag 0AEM] is stated with. -/
def projectiveSpacePowerYonedaIso :
    yoneda.obj (projectiveSpacePowerSiteObject k B hk m) ≅ projectiveLinePower k B hk (Fin m) :=
  (bigFppfOverRestrictedYonedaIso B (Spec (CommRingCat.of k)) hk
      (projectiveSpacePowerSiteObject k B hk m)).symm ≪≫
    projectiveSpacePowerRestrictedYonedaIso k B hk m

/-! ### The action -/

/-- The action morphism of `(GL₂)^m` on `(ℙ¹_k)^m`, as a morphism of schemes over `Spec k`: the
morphism of schemes `AlgebraicGeometry.projectiveLinePowerGeneralLinearAction` lies over
`Spec k` by
`AlgebraicGeometry.projectiveLinePowerGeneralLinearAction_comp_structureMorphism`. -/
def generalLinearTwoPowerActionOver :
    (Over.post (X := B.obj hk) B.inclusion).obj
        (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) ⟶
      (Over.post (X := B.obj hk) B.inclusion).obj (projectiveSpacePowerSiteObject k B hk m) :=
  Over.homMk (projectiveLinePowerGeneralLinearAction k m)
    (projectiveLinePowerGeneralLinearAction_comp_structureMorphism k m)

/-- **The action of `(GL₂)^m` on `(ℙ¹_k)^m` as a morphism of the big fppf site over `Spec k`**,
the comparison functor to schemes over `Spec k` being fully faithful. -/
def generalLinearTwoPowerActionSite :
    generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m ⟶
      projectiveSpacePowerSiteObject k B hk m :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimage
    (generalLinearTwoPowerActionOver k B hk m)

/-- **The action of `(GL₂)^m` on `(ℙ¹_k)^m` as a morphism of functors of points over the big
fppf site over `Spec k`**: the morphism
`yoneda.obj ((GL₂)^m ×_{Spec k} (ℙ¹_k)^m) ⟶ projectiveLinePower k B hk (Fin m)` given by
`(g, x) ↦ g · x`.

This is the datum the contraction step of [Stacks, Tag 0AEM] applies [Stacks, Tag 0AEJ] to:
paired with `AlgebraicGeometry.Space.generalLinearTwoPowerFunctorProjection` it is
`AlgebraicGeometry.Space.generalLinearTwoPowerActionGraph`, the morphism
`G × (ℙ¹_k)^m ⟶ G × (ℙ¹_k)^m`, `(g, x) ↦ (g, g · x)`, over `G`. -/
def generalLinearTwoPowerAction :
    yoneda.obj (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) ⟶
      projectiveLinePower k B hk (Fin m) :=
  yoneda.map (generalLinearTwoPowerActionSite k B hk m) ≫
    (projectiveSpacePowerYonedaIso k B hk m).hom

/-- **The projection of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` to `(GL₂)^m`, as a morphism of functors of
points.** -/
def generalLinearTwoPowerFunctorProjection :
    yoneda.obj (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) ⟶
      yoneda.obj (generalLinearTwoPowerSiteObject k B hk m) :=
  yoneda.map (generalLinearTwoPowerProjection k B hk m)

/-- **The projection of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` to `(ℙ¹_k)^m`, as a morphism of functors of
points.** -/
def projectiveLinePowerFunctorProjection :
    yoneda.obj (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) ⟶
      projectiveLinePower k B hk (Fin m) :=
  yoneda.map (projectiveSpacePowerProjection k B hk m) ≫
    (projectiveSpacePowerYonedaIso k B hk m).hom

/-- **The functor of points of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` is the product of the functor of
points of `(GL₂)^m` with `AlgebraicGeometry.Space.projectiveLinePower`.** This is what lets the
contraction step of [Stacks, Tag 0AEM] form `G × C` from a subfunctor `C` of
`projectiveLinePower k B hk (Fin m)`, and pair the projection to `G` with the action. -/
def isLimitBinaryFanFunctorProjections :
    IsLimit (BinaryFan.mk (generalLinearTwoPowerFunctorProjection k B hk m)
      (projectiveLinePowerFunctorProjection k B hk m)) :=
  BinaryFan.isLimitCompRightIso _ (projectiveSpacePowerYonedaIso k B hk m).hom
    (mapIsLimitOfPreservesOfIsLimit yoneda _ _ (isLimitBinaryFanProjections k B hk m))

/-- **The morphism `(g, x) ↦ (g, g · x)` of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` over `(GL₂)^m`**, as a
morphism of functors of points: the pair of the projection to `(GL₂)^m` and the action, taken
through the fibre-product property
`AlgebraicGeometry.Space.isLimitBinaryFanFunctorProjections`.

This is the morphism the contraction step of [Stacks, Tag 0AEM] restricts to `G × C` and
composes with `G × f` to get the `G × C ⟶ G × Z` over `G` that [Stacks, Tag 0AEJ] is applied
to. -/
def generalLinearTwoPowerActionGraph :
    yoneda.obj (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) ⟶
      yoneda.obj (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) :=
  (isLimitBinaryFanFunctorProjections k B hk m).lift
    (BinaryFan.mk (generalLinearTwoPowerFunctorProjection k B hk m)
      (generalLinearTwoPowerAction k B hk m))

/-- **`(g, x) ↦ (g, g · x)` lies over `(GL₂)^m`**: its first component is the projection to
`(GL₂)^m`. -/
theorem generalLinearTwoPowerActionGraph_comp_generalLinearTwoPowerFunctorProjection :
    generalLinearTwoPowerActionGraph k B hk m ≫
        generalLinearTwoPowerFunctorProjection k B hk m =
      generalLinearTwoPowerFunctorProjection k B hk m :=
  (isLimitBinaryFanFunctorProjections k B hk m).fac _ ⟨WalkingPair.left⟩

/-- **The second component of `(g, x) ↦ (g, g · x)` is the action.** -/
theorem generalLinearTwoPowerActionGraph_comp_projectiveLinePowerFunctorProjection :
    generalLinearTwoPowerActionGraph k B hk m ≫
        projectiveLinePowerFunctorProjection k B hk m =
      generalLinearTwoPowerAction k B hk m :=
  (isLimitBinaryFanFunctorProjections k B hk m).fac _ ⟨WalkingPair.right⟩

include hk in
/-- **The functor of points of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` is an algebraic space over
`Spec k`**, being representable by an object of the site. This is the hypothesis
[Stacks, Tag 0AEJ] asks of the source of the morphism it is applied to. -/
theorem isAlgebraicSpace_generalLinearTwoPowerProjectiveLinePower :
    IsAlgebraicSpace B (Spec (CommRingCat.of k)) hk
      (yoneda.obj (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m)) :=
  isAlgebraicSpace_yoneda B (Spec (CommRingCat.of k)) hk _

/-! ### The action at a `k`-point of the group -/

section Point

variable (M : Fin m → Matrix.GeneralLinearGroup (Fin 2) k)

/-- The section of the projection to `(GL₂)^m` over the `k`-point of `(GL₂)^m` named by `M`, as a
morphism of schemes. -/
def generalLinearTwoPowerPointSectionHom :
    (projectiveSpacePowerOver k 1 m).left ⟶
      pullback (projectiveSpacePowerOver k 1 m).hom
        (Spec.map (generalLinearTwoPowerStructureMap k m)) :=
  pullbackSectionOfRetraction (projectiveSpacePowerOver k 1 m)
    (Spec.map (generalLinearTwoPowerStructureMap k m))
    (Spec.map (CommRingCat.ofHom (generalLinearTwoPowerPoint k m M)))
    (specMap_comp_specMap_eq_id k (algebraMap k (generalLinearTwoPowerCoordinateRing k m))
      (generalLinearTwoPowerPoint k m M)
      (generalLinearTwoPowerPoint_comp_algebraMap k m M))

/-- The second component of the section at the `k`-point named by `M` is that point. -/
theorem generalLinearTwoPowerPointSectionHom_comp_snd :
    generalLinearTwoPowerPointSectionHom k m M ≫
        pullback.snd (projectiveSpacePowerOver k 1 m).hom
          (Spec.map (generalLinearTwoPowerStructureMap k m)) =
      (projectiveSpacePowerOver k 1 m).hom ≫
        Spec.map (CommRingCat.ofHom (generalLinearTwoPowerPoint k m M)) :=
  pullbackSectionOfRetraction_comp_snd _ _ _ _

/-- The section at the `k`-point named by `M` is a morphism over `Spec k`. -/
theorem generalLinearTwoPowerPointSectionHom_comp_structureMorphism :
    generalLinearTwoPowerPointSectionHom k m M ≫
        (pullback.snd (projectiveSpacePowerOver k 1 m).hom
            (Spec.map (generalLinearTwoPowerStructureMap k m)) ≫
          Spec.map (generalLinearTwoPowerStructureMap k m)) =
      (projectiveSpacePowerOver k 1 m).hom := by
  rw [← Category.assoc, generalLinearTwoPowerPointSectionHom_comp_snd, Category.assoc,
    specMap_comp_specMap_eq_id k (algebraMap k (generalLinearTwoPowerCoordinateRing k m))
      (generalLinearTwoPowerPoint k m M)
      (generalLinearTwoPowerPoint_comp_algebraMap k m M), Category.comp_id]

/-- The section at the `k`-point named by `M`, as a morphism of schemes over `Spec k`. -/
def generalLinearTwoPowerPointSectionOver :
    (Over.post (X := B.obj hk) B.inclusion).obj (projectiveSpacePowerSiteObject k B hk m) ⟶
      (Over.post (X := B.obj hk) B.inclusion).obj
        (generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m) :=
  Over.homMk (generalLinearTwoPowerPointSectionHom k m M)
    (generalLinearTwoPowerPointSectionHom_comp_structureMorphism k m M)

/-- **The fibre of `(GL₂)^m ×_{Spec k} (ℙ¹_k)^m` over the `k`-point of `(GL₂)^m` named by `M`**,
as a morphism of the big fppf site over `Spec k`: a section of the projection to `(GL₂)^m` whose
component in `(GL₂)^m` is that point. -/
def generalLinearTwoPowerPointSection :
    projectiveSpacePowerSiteObject k B hk m ⟶
      generalLinearTwoPowerProjectiveLinePowerSiteObject k B hk m :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimage
    (generalLinearTwoPowerPointSectionOver k B hk m M)

/-- The automorphism of `(ℙ¹_k)^m` attached to `M`, as a morphism of schemes over `Spec k`. -/
def projectiveSpacePowerMatrixAutOver :
    (Over.post (X := B.obj hk) B.inclusion).obj (projectiveSpacePowerSiteObject k B hk m) ⟶
      (Over.post (X := B.obj hk) B.inclusion).obj (projectiveSpacePowerSiteObject k B hk m) :=
  (projectiveSpacePowerMatrixAut k 1 m M).asIso.hom

/-- **The automorphism of the site object of `(ℙ¹_k)^m` attached to `M`.** -/
def projectiveSpacePowerSiteMatrixAut :
    projectiveSpacePowerSiteObject k B hk m ≅ projectiveSpacePowerSiteObject k B hk m :=
  (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimageIso
    (X := projectiveSpacePowerSiteObject k B hk m)
    (Y := projectiveSpacePowerSiteObject k B hk m)
    (projectiveSpacePowerMatrixAut k 1 m M).asIso

/-- The forward morphism of the automorphism of the site object attached to `M`. -/
theorem projectiveSpacePowerSiteMatrixAut_hom :
    (projectiveSpacePowerSiteMatrixAut k B hk m M).hom =
      (fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimage
        (projectiveSpacePowerMatrixAutOver k B hk m M) :=
  rfl

/-- **The action restricted to the fibre over the `k`-point of `(GL₂)^m` named by `M` is the
automorphism of `(ℙ¹_k)^m` that `M` gives**, in the big fppf site over `Spec k`. This is
`AlgebraicGeometry.pullbackSectionOfRetraction_comp_projectiveLinePowerGeneralLinearAction_point`
transported along the comparison functor, and it is what makes the morphism of functors of
points an *action*: its fibre over `g ∈ (GL₂)^m(k)` is `x ↦ g · x`. -/
theorem generalLinearTwoPowerPointSection_comp_actionSite :
    generalLinearTwoPowerPointSection k B hk m M ≫ generalLinearTwoPowerActionSite k B hk m =
      (projectiveSpacePowerSiteMatrixAut k B hk m M).hom := by
  rw [projectiveSpacePowerSiteMatrixAut_hom]
  exact ((fullyFaithful_overPost_bigFppfInclusion B (Spec (CommRingCat.of k)) hk).preimage_comp
    _ _).symm.trans (congrArg _ (Over.OverMorphism.ext
      (pullbackSectionOfRetraction_comp_projectiveLinePowerGeneralLinearAction_point k m M)))

/-- **The automorphism of `AlgebraicGeometry.Space.projectiveLinePower` attached to `M`.** -/
def projectiveLinePowerFunctorMatrixAut :
    projectiveLinePower k B hk (Fin m) ≅ projectiveLinePower k B hk (Fin m) :=
  (projectiveSpacePowerYonedaIso k B hk m).symm ≪≫
    yoneda.mapIso (projectiveSpacePowerSiteMatrixAut k B hk m M) ≪≫
      projectiveSpacePowerYonedaIso k B hk m

/-- **The action, as a morphism of functors of points, restricted to the fibre over the
`k`-point of `(GL₂)^m` named by `M`, is the automorphism of
`AlgebraicGeometry.Space.projectiveLinePower` that `M` gives.**

This is the form in which the contraction step of [Stacks, Tag 0AEM] uses the family: a property
of the action over a Zariski open subset of the group gives, at each `k`-point of that open
subset, the same property of the single automorphism `x ↦ M · x`. -/
theorem generalLinearTwoPowerPointSection_comp_action :
    yoneda.map (generalLinearTwoPowerPointSection k B hk m M) ≫
        generalLinearTwoPowerAction k B hk m =
      (projectiveSpacePowerYonedaIso k B hk m).hom ≫
        (projectiveLinePowerFunctorMatrixAut k B hk m M).hom := by
  rw [generalLinearTwoPowerAction, projectiveLinePowerFunctorMatrixAut, Iso.trans_hom,
    Iso.trans_hom, Iso.symm_hom, ← Category.assoc, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp, ← Functor.map_comp,
    generalLinearTwoPowerPointSection_comp_actionSite]
  rfl

end Point

end AlgebraicGeometry.Space

end
