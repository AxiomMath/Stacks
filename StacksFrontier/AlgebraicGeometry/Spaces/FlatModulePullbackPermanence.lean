module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChangeAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleGeometricPointCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleLocusOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FaithfullyFlatLocalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.CompositeChartData
public import StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra

/-!
# Stacks 05VY: relative flatness of a module along a flat pullback

Let `X ⟶ Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S` of a big fppf site, let
`G` be a quasi-coherent `𝒪_Y`-module, let `x` be a point of `|X|` and let `y` be its image in
`|Y|`.  If `f : X ⟶ Y` is flat at `x`, then

`G` is flat over `Z` at `y` ⟺ `f^*G` is flat over `Z` at `x`.

In particular, if `f` is surjective and flat then `G` is flat over `Z` if and only if `f^*G`
is flat over `Z`.

## Main results

* `AlgebraicGeometry.Space.faithfullyFlat_etaleLocalRingMap_of_isFlatAt`: the canonical
  homomorphism of étale local rings of a morphism flat *at a point* is faithfully flat there.
  This is the pointwise form of Stacks 03MK,
  `AlgebraicGeometry.Space.faithfullyFlat_etaleLocalRingMap`.
* `AlgebraicGeometry.Space.isFlatOverAtGeometricPoint_modulePullback_iff_of_isFlatAt`:
  **Stacks 05VY, the pointwise equivalence**, at a geometric point of `X`.
* `AlgebraicGeometry.Space.mem_flatLocus_modulePullback_iff_of_isFlatAt` and
  `AlgebraicGeometry.Space.isFlatOverAtPoint_modulePullback_iff_of_isFlatAt`: **Stacks 05VY,
  the pointwise equivalence** in the source's own shape, at a point of `|X|` and its image in
  `|Y|`, read respectively on `AlgebraicGeometry.Space.flatLocus` and on
  `AlgebraicGeometry.Space.IsFlatOverAtPoint`.
* `AlgebraicGeometry.Space.isFlatOverAtPoint_iff_mem_flatLocus`: those two readings are the
  same predicate.
* `AlgebraicGeometry.Space.isFlatOver_modulePullback_iff_of_isSurjective_of_isFlat`:
  **Stacks 05VY, the final assertion**, for a surjective flat `f`.

## Implementation notes

The proof is the source's.  A geometric point `x̄` of `X` is chosen, with images `ȳ` in `Y` and
`z̄` in `Z`; the two sides are read on the étale local rings
`𝒪_{Z, z̄} ⟶ 𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}` and the stalk module `G_ȳ`, after which the assertion is
Stacks 0584 (2).  Concretely:

* flatness over `Z` at a point is condition (2) of Stacks 05VU,
  `AlgebraicGeometry.Space.IsFlatOverAtGeometricPoint`;
* `AlgebraicGeometry.Space.geometricModuleStalkPullbackIso` of Stacks 05VQ identifies
  `(f^*G)_{x̄}` with `𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} G_ȳ`;
* flatness of `f` at `x` makes `𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}` flat by Stacks 04NG,
  `AlgebraicGeometry.Space.isFlatAt_iff_etaleLocalRingMap_flat`, and it is a local
  homomorphism of local rings, hence faithfully flat;
* `Module.Flat.tensorProduct_iff_of_faithfullyFlat` is Stacks 0584 (2), and it turns flatness
  of `𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} G_ȳ` over `𝒪_{Z, z̄}` into flatness of `G_ȳ` over `𝒪_{Z, z̄}`, in
  both directions.

The geometric-point form needs no quasi-coherence: the base-change formula of Stacks 05VQ
holds for every `𝒪_Y`-module.  Quasi-coherence enters only where the condition is read at a
point of `|X|` rather than at a geometric point, since that reading is Stacks 05VU.

The point of `|Y|` of the source is `pointsMap B S hS X.1 f.hom x`, and flatness over `Z` at a
point of the point space is membership of `AlgebraicGeometry.Space.flatLocus`, which is the
some-chart condition (1) of Stacks 05VU — the same predicate as
`AlgebraicGeometry.Space.IsFlatOverAtPoint`.  That it depends only on the point, and not on
the geometric point above it chosen to run the argument, is
`AlgebraicGeometry.Space.mem_flatLocus_iff_isFlatOverAtGeometricPoint`.

Reading the condition at a point needs Stacks 05VU on `X` for `f^*G` as well as on `Y` for
`G`, so quasi-coherence of the pullback is needed too; it is not an extra hypothesis, being
Stacks 03GA,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`, which
holds for an arbitrary morphism of algebraic spaces.

Surjectivity of `f` is used only through `AlgebraicGeometry.Space.IsSurjective`, which is
surjectivity of `|X| → |Y|`; a point of `|Y|` is lifted to a point of `|X|` and then to a
geometric point by `AlgebraicGeometry.Space.exists_geometricRepresentative`.

The module universe is the universe `u` of the structure rings, as it must be for
`AlgebraicGeometry.Space.IsFlatOver` and for Stacks 05VU.

## References

* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
* [Stacks Project, Tag 03MK](https://stacks.math.columbia.edu/tag/03MK)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Faithful flatness of the étale local rings at a point of flatness -/

/-- **Stacks 03MK at a point.**  The canonical homomorphism of étale local rings
`𝒪_{G, f ∘ x̄} ⟶ 𝒪_{F, x̄}` induced by a morphism `f : F ⟶ G` of algebraic spaces which is flat
at the image point of a geometric point `x̄` of its source is faithfully flat.

It is flat by Stacks 04NG and it is a local homomorphism of local rings, so Stacks 03MK in the
ring-level form `RingHom.Flat.faithfullyFlat_of_isLocalHom` applies.  This is the pointwise
refinement of `AlgebraicGeometry.Space.faithfullyFlat_etaleLocalRingMap`, which asks `f` to be
flat everywhere. -/
theorem faithfullyFlat_etaleLocalRingMap_of_isFlatAt
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (x : GeometricPoint B S hS F)
    (hf : IsFlatAt B S hS f x.image) :
    (etaleLocalRingMap hF f x).FaithfullyFlat := by
  have : IsLocalRing ↥(etaleLocalRing B S hS G (geometricPointMap f x)) :=
    isLocalRing_etaleLocalRing B S hS G hG (geometricPointMap f x)
  have : IsLocalRing ↥(etaleLocalRing B S hS F x) :=
    isLocalRing_etaleLocalRing B S hS F hF x
  have : IsLocalHom (etaleLocalRingMap hF f x) :=
    isLocalHom_etaleLocalRingMap B S hS hF hG f x
  exact ((isFlatAt_iff_etaleLocalRingMap_flat hF hG f x).mp hf).faithfullyFlat_of_isLocalHom

/-! ### Stacks 05VY at a geometric point -/

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **Stacks 05VY, the pointwise equivalence.**  Let `X --f--> Y --g--> Z` be morphisms of
algebraic spaces over `S`, let `G` be an `𝒪_Y`-module and let `x̄` be a geometric point of `X`
at whose image `f` is flat.  Then `G` is flat over `Z` at the image geometric point
`ȳ = f ∘ x̄` exactly when the pullback `f^*G` is flat over `Z` at `x̄`.

Writing `z̄` for the image of `ȳ` in `Z`, the stalk of `f^*G` at `x̄` is
`𝒪_{X, x̄} ⊗_{𝒪_{Y, ȳ}} G_ȳ` by Stacks 05VQ, and `𝒪_{Y, ȳ} ⟶ 𝒪_{X, x̄}` is faithfully flat
because `f` is flat at `x̄`; so flatness of the two modules over `𝒪_{Z, z̄}` agree by
Stacks 0584 (2). -/
theorem isFlatOverAtGeometricPoint_modulePullback_iff_of_isFlatAt (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (xbar : GeometricPoint B S hS X.1)
    (hf : IsFlatAt B S hS f.hom xbar.image) :
    IsFlatOverAtGeometricPoint B S hS g G (geometricPointMap f.hom xbar) ↔
      IsFlatOverAtGeometricPoint B S hS (f ≫ g) ((modulePullback B S hS f).obj G) xbar := by
  let : Algebra ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      ↥(etaleLocalRing B S hS X.1 xbar) := (etaleLocalRingMap X.2 f.hom xbar).toAlgebra
  let : Algebra
      ↥(etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap f.hom xbar)))
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar)) :=
    (etaleLocalRingMap Y.2 g.hom (geometricPointMap f.hom xbar)).toAlgebra
  let : Algebra
      ↥(etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap f.hom xbar)))
      ↥(etaleLocalRing B S hS X.1 xbar) := (etaleLocalRingMap X.2 (f ≫ g).hom xbar).toAlgebra
  let : IsScalarTower
      ↥(etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap f.hom xbar)))
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      ↥(etaleLocalRing B S hS X.1 xbar) :=
    IsScalarTower.of_algebraMap_eq' (etaleLocalRingMap_comp X.2 Y.2 f.hom g.hom xbar).symm
  let : Module
      ↥(etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap f.hom xbar)))
      ↥(geometricModuleStalk B S hS Y (geometricPointMap f.hom xbar) G) :=
    Module.compHom _ (etaleLocalRingMap Y.2 g.hom (geometricPointMap f.hom xbar))
  let : IsScalarTower
      ↥(etaleLocalRing B S hS Z.1 (geometricPointMap g.hom (geometricPointMap f.hom xbar)))
      ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      ↥(geometricModuleStalk B S hS Y (geometricPointMap f.hom xbar) G) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.FaithfullyFlat ↥(etaleLocalRing B S hS Y.1 (geometricPointMap f.hom xbar))
      ↥(etaleLocalRing B S hS X.1 xbar) :=
    faithfullyFlat_etaleLocalRingMap_of_isFlatAt B S hS X.2 Y.2 f.hom xbar hf
  refine Iff.trans ?_ (ModuleCat.flat_iff_of_iso (etaleLocalRingMap X.2 (f ≫ g).hom xbar)
    (geometricModuleStalkPullbackIso B S hS f xbar G)).symm
  refine Iff.trans ?_ (ModuleCat.flat_extendScalars_obj_iff (etaleLocalRingMap X.2 f.hom xbar)
    (etaleLocalRingMap X.2 (f ≫ g).hom xbar)
    (geometricModuleStalk B S hS Y (geometricPointMap f.hom xbar) G)).symm
  exact Module.Flat.tensorProduct_iff_of_faithfullyFlat.symm

/-! ### Stacks 05VY at a point of the point space -/

/-- **Stacks 05VY, the pointwise equivalence, at a point of `|X|`.**  Let `X --f--> Y --g--> Z`
be morphisms of algebraic spaces over `S`, let `G` be a quasi-coherent `𝒪_Y`-module whose
pullback is quasi-coherent, and let `x` be a point of `|X|` at which `f` is flat, with image
`y` in `|Y|`.  Then `G` is flat over `Z` at `y` exactly when `f^*G` is flat over `Z` at `x`.

Flatness over `Z` at a point is membership of `AlgebraicGeometry.Space.flatLocus`, the
some-chart condition (1) of Stacks 05VU.  A geometric point above `x` turns both sides into
the geometric-stalk condition (2), where the previous result applies. -/
theorem mem_flatLocus_modulePullback_iff_of_isFlatAt (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Modules.{u, u} B S hS Y.1 Y.2) [hG : G.IsQuasicoherentOnSite] (x : points B S hS X.1)
    (hf : IsFlatAt B S hS f.hom x) :
    pointsMap B S hS X.1 f.hom x ∈ flatLocus B S hS Y.2 g.hom G ↔
      x ∈ flatLocus B S hS X.2 (f ≫ g).hom ((modulePullback B S hS f).obj G) := by
  have : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hG
  obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B S hS X.1 x
  rw [← geometricPointMap_image f.hom xbar,
    mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS g G (geometricPointMap f.hom xbar),
    mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS (f ≫ g)
      ((modulePullback B S hS f).obj G) xbar]
  exact isFlatOverAtGeometricPoint_modulePullback_iff_of_isFlatAt B S hS f g G xbar hf

/-- The relative flat locus of `AlgebraicGeometry.Space.flatLocus` is the locus of
`AlgebraicGeometry.Space.IsFlatOverAtPoint`: both are the some-chart condition (1) of
Stacks 05VU, at a point of the point space. -/
theorem isFlatOverAtPoint_iff_mem_flatLocus {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X') (f : X' ⟶ Y') (F : Modules.{u, u} B S hS X' hX)
    (x : points B S hS X') :
    IsFlatOverAtPoint B S hS hX f F x ↔ x ∈ flatLocus B S hS hX f F :=
  Iff.rfl

/-- **Stacks 05VY, the pointwise equivalence**, stated through
`AlgebraicGeometry.Space.IsFlatOverAtPoint`, which is Stacks 05VV at a point of `|X|`.  For
`f : X ⟶ Y` flat at a point `x` of `|X|` with image `y` in `|Y|`, and a quasi-coherent
`𝒪_Y`-module `G`, `G` is flat over `Z` at `y` if and only if `f^*G` is flat over `Z` at
`x`. -/
theorem isFlatOverAtPoint_modulePullback_iff_of_isFlatAt (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Modules.{u, u} B S hS Y.1 Y.2) [G.IsQuasicoherentOnSite] (x : points B S hS X.1)
    (hf : IsFlatAt B S hS f.hom x) :
    IsFlatOverAtPoint B S hS Y.2 g.hom G (pointsMap B S hS X.1 f.hom x) ↔
      IsFlatOverAtPoint B S hS X.2 (f ≫ g).hom ((modulePullback B S hS f).obj G) x :=
  mem_flatLocus_modulePullback_iff_of_isFlatAt B S hS f g G x hf

/-! ### Stacks 05VY along a surjective flat morphism -/

/-- **Stacks 05VY, the final assertion.**  Let `X --f--> Y --g--> Z` be morphisms of algebraic
spaces over `S` with `f` surjective and flat, and let `G` be a quasi-coherent `𝒪_Y`-module
whose pullback is quasi-coherent.  Then `G` is flat over `Z` if and only if `f^*G` is.

Chartwise flatness of Stacks 05VV is flatness of every geometric stalk over the étale local
ring of the base, by Stacks 05VU; `f` is flat at every point, so the pointwise equivalence
applies at every geometric point of `X`, and surjectivity of `|X| → |Y|` puts a geometric
point of `X` above every point of `|Y|`. -/
theorem isFlatOver_modulePullback_iff_of_isSurjective_of_isFlat (f : X ⟶ Y) (g : Y ⟶ Z)
    (G : Modules.{u, u} B S hS Y.1 Y.2) [hG : G.IsQuasicoherentOnSite]
    (hsurj : IsSurjective B S hS f.hom) (hflat : IsFlat B S hS f.hom) :
    IsFlatOver B S hS Y.2 g.hom G ↔
      IsFlatOver B S hS X.2 (f ≫ g).hom ((modulePullback B S hS f).obj G) := by
  have : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f G hG
  rw [isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS g G,
    isFlatOver_iff_forall_isFlatOverAtGeometricPoint B S hS (f ≫ g)
      ((modulePullback B S hS f).obj G)]
  refine ⟨fun h xbar => ?_, fun h ybar => ?_⟩
  · exact (isFlatOverAtGeometricPoint_modulePullback_iff_of_isFlatAt B S hS f g G xbar
      (isFlatAt_of_isFlat B S hS f.hom hflat xbar.image)).mp (h _)
  · obtain ⟨x, hx⟩ := hsurj ybar.image
    obtain ⟨xbar, rfl⟩ := exists_geometricRepresentative B S hS X.1 x
    rw [← mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS g G ybar, ← hx]
    exact (mem_flatLocus_modulePullback_iff_of_isFlatAt B S hS f g G _
      (isFlatAt_of_isFlat B S hS f.hom hflat _)).mpr
      ((mem_flatLocus_iff_isFlatOverAtGeometricPoint B S hS (f ≫ g) _ xbar).mpr (h xbar))

end AlgebraicGeometry.Space

end
