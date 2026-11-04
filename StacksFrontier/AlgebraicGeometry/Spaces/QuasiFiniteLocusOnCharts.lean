module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae

/-!
# Open subspaces of an étale chart, and the quasi-finite locus read on a chart

An open subspace of the presheaf represented by an object `V` of the big fppf site of `S` is the
same thing as an open subset of the scheme underlying `V`: the point space of a represented
presheaf is the point space of the representing scheme
(`AlgebraicGeometry.Space.pointsToScheme`, a homeomorphism), and an open subspace of an
algebraic space is determined by its point set, which is part (1) of Tag 03BZ. This file sets up
that dictionary in the form the chart arguments use it, and then applies it to the quasi-finite
locus: the open subspace of the source cut out by the points of quasi-finiteness, which exists
by part (1) of Tag 0ABM, is on a chart the quasi-finite locus
`AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus` of the morphism of schemes.

That last comparison is what lets Zariski's main theorem for schemes be used on a chart of a
morphism of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.subspaceOfOpens` is the open subspace of a represented presheaf cut
  out by an open subset of the representing scheme.
* `AlgebraicGeometry.Space.quasiFiniteLocusSubspace` is the open subspace of the source of a
  morphism of algebraic spaces cut out by the points at which the morphism is quasi-finite.
* `AlgebraicGeometry.Space.rangeIsoOfMono` identifies the source of a monomorphism of presheaves
  with its image subfunctor.

## Main results

* `AlgebraicGeometry.Space.mem_pointsRange_preimage_iff`: a point lies in the point set of the
  inverse image of a subfunctor exactly when its image lies in the point set of the subfunctor.
* `AlgebraicGeometry.Space.eq_of_preimage_eq_of_isSurjective`: two open subspaces with the same
  inverse image along a morphism surjective on points are equal. This is the descent step every
  chart argument below ends with.
* `AlgebraicGeometry.Space.range_yoneda_map_eq_subspaceOfOpens`: an open immersion of the site
  has as image the open subspace cut out by its image on the schemes.
* `AlgebraicGeometry.Space.isQuasiFiniteAt_yoneda_map_iff`: for a morphism of the site locally of
  finite type, quasi-finiteness of the induced morphism of represented presheaves at a point is
  quasi-finiteness of the morphism of schemes at the corresponding scheme point.
* `AlgebraicGeometry.Space.quasiFiniteLocusSubspace_yoneda_map`: the quasi-finite locus of a
  morphism of represented presheaves is the open subspace cut out by Mathlib's
  `AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus`.
* `AlgebraicGeometry.Space.isIso_fromPreimage_range_of_preimage_eq`: if the inverse image of the
  image of `A.ι ≫ p` is `A` itself then the canonical morphism from that inverse image to the
  image is an isomorphism.

## Implementation notes

**Why the locus is `AlgebraicGeometry.Space.openSubspaceOfPoints` and not a chosen subspace.**
Part (1) of Tag 0ABM says the point set of quasi-finiteness is open; part (1) of Tag 03BZ then
produces an open subspace with that point set. Taking it to be the *explicit*
`AlgebraicGeometry.Space.openSubspaceOfPoints` rather than the value of the order isomorphism of
Tag 03BZ keeps the definition free of `Classical.choose` and makes the comparison with the
chart-level locus an equality of two applications of one construction to two sets of points,
which is then `congrArg` of the pointwise comparison.

**The pointed-chart route to the chart comparison.** Quasi-finiteness at a point of an algebraic
space is the pointed-chart condition of Tag 04NC for the germ property induced by local
quasi-finiteness of morphisms of schemes
(`AlgebraicGeometry.Space.isQuasiFiniteAt_iff_holdsOnEveryEtaleChartAtPoint`), and for a morphism
of *represented* presheaves that condition is the germ property of the underlying morphism of
schemes at the corresponding scheme point
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_yoneda_map_iff`). The germ property is in
turn quasi-finiteness at a point of a morphism of schemes
(`AlgebraicGeometry.quasiFiniteAt_iff_hasRepresentativeWithProperty`). So the comparison needs no
geometry of its own; the finite-type half of `AlgebraicGeometry.quasiFiniteAt` is recovered from
the finite-type hypothesis on the chart, which is the only place it is used.

`AlgebraicGeometry.Space.pointsToScheme` and `AlgebraicGeometry.Space.pointsToScheme` are the
same function — both are `Quot.lift` of `AlgebraicGeometry.Space.schemePoint` — and
`AlgebraicGeometry.Space.pointsToScheme_eq_pointsToScheme` records that, so the two halves of
the library's point API can be used together without translation.

## References

* [Stacks Project, Tag 01TD](https://stacks.math.columbia.edu/tag/01TD)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Point sets of inverse images, and descent of open subspaces -/

section Preimage

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A point of the source of a morphism of presheaves lies in the point set of the inverse image
of a subfunctor exactly when its image lies in the point set of that subfunctor.

The forward direction maps a point of the inverse image through
`CategoryTheory.Subfunctor.fromPreimage`; the converse is the surjectivity of the comparison map
from the points of a fibre product, `AlgebraicGeometry.Space.exists_points_of_isPullback`, applied
to the cartesian square `CategoryTheory.Subfunctor.isPullback_preimage` of Tag 083Q. -/
theorem mem_pointsRange_preimage_iff (g : Y ⟶ X) (Z : Subfunctor X) (x : points B S hS Y) :
    x ∈ Set.range (pointsMap B S hS (Z.preimage g).toFunctor (Z.preimage g).ι) ↔
      pointsMap B S hS Y g x ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨pointsMap B S hS (Z.preimage g).toFunctor (Z.fromPreimage g) q, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]
  · rintro ⟨z, hz⟩
    obtain ⟨w, -, hw⟩ :=
      exists_points_of_isPullback B S hS (Subfunctor.isPullback_preimage g Z) z x hz
    exact ⟨w, hw⟩

/-- The point set of the inverse image of a subfunctor is the preimage of its point set. -/
theorem pointsRange_preimage (g : Y ⟶ X) (Z : Subfunctor X) :
    Set.range (pointsMap B S hS (Z.preimage g).toFunctor (Z.preimage g).ι) =
      pointsMap B S hS Y g ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) :=
  Set.ext fun x ↦ mem_pointsRange_preimage_iff B S hS g Z x

/-- Two open subspaces of an algebraic space over `S` whose inverse images along a morphism
surjective on points agree are equal.

Both sides are determined by their point sets, which is the injectivity half of part (1) of
Tag 03BZ in the form `AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset`, and a point of the
target is the image of a point of the source. -/
theorem eq_of_preimage_eq_of_isSurjective (g : Y ⟶ X) (hg : IsSurjective B S hS g)
    {A A' : Subfunctor X} (hA : IsOpenSubspace B S hS A) (hA' : IsOpenSubspace B S hS A')
    (h : A.preimage g = A'.preimage g) : A = A' := by
  have hpts : Set.range (pointsMap B S hS A.toFunctor A.ι) =
      Set.range (pointsMap B S hS A'.toFunctor A'.ι) := by
    ext x
    obtain ⟨z, rfl⟩ := hg x
    rw [← mem_pointsRange_preimage_iff, ← mem_pointsRange_preimage_iff, h]
  exact eq_of_range_pointsMap_ι_eq B S hS hA hA' hpts

end Preimage

/-! ### The image of an open immersion -/

section Range

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The source of a monomorphism of presheaves is isomorphic to its image subfunctor. -/
noncomputable def rangeIsoOfMono (p : F ⟶ G) [Mono p] : F ≅ (Subfunctor.range p).toFunctor :=
  asIso (Subfunctor.toRange p)

/-- The isomorphism `AlgebraicGeometry.Space.rangeIsoOfMono p` followed by the inclusion of the
image subfunctor is `p`. -/
@[simp]
theorem rangeIsoOfMono_hom_ι (p : F ⟶ G) [Mono p] :
    (rangeIsoOfMono B S hS p).hom ≫ (Subfunctor.range p).ι = p :=
  Subfunctor.toRange_ι p

/-- The inverse of `AlgebraicGeometry.Space.rangeIsoOfMono p` followed by `p` is the inclusion of
the image subfunctor. -/
@[simp]
theorem rangeIsoOfMono_inv_comp (p : F ⟶ G) [Mono p] :
    (rangeIsoOfMono B S hS p).inv ≫ p = (Subfunctor.range p).ι :=
  (Iso.inv_comp_eq _).2 (rangeIsoOfMono_hom_ι B S hS p).symm

end Range

/-! ### Open subspaces of a chart -/

section Charts

variable {V W : BigFppfOver B S hS}

/-- The subfunctor of the presheaf represented by `V` whose points are those lying over the open
subset `Q` of the associated scheme. -/
def subspaceOfOpens (V : BigFppfOver B S hS)
    (Q : ((BigFppfOver.toScheme B S hS).obj V).Opens) : Subfunctor (yoneda.obj V) :=
  openSubspaceOfPoints B S hS (yoneda.obj V) (pointsToScheme B S hS V ⁻¹' (Q : Set _))

/-- The point set of `AlgebraicGeometry.Space.subspaceOfOpens` is the preimage of the open
subset under the comparison of points with scheme points. -/
theorem range_pointsMap_subspaceOfOpens (V : BigFppfOver B S hS)
    (Q : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    Set.range (pointsMap B S hS (subspaceOfOpens B S hS V Q).toFunctor
        (subspaceOfOpens B S hS V Q).ι) =
      pointsToScheme B S hS V ⁻¹' (Q : Set _) :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- `AlgebraicGeometry.Space.subspaceOfOpens` is an open subspace: the preimage of an open subset
of the scheme is open in the point space, by
`AlgebraicGeometry.Space.isOpen_pointTopology_yoneda_iff_isOpen_image` and bijectivity of the
comparison of points with scheme points. -/
theorem isOpenSubspace_subspaceOfOpens (V : BigFppfOver B S hS)
    (Q : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    IsOpenSubspace B S hS (subspaceOfOpens B S hS V Q) := by
  refine isOpenSubspace_openSubspaceOfPoints B S hS (isAlgebraicSpace_yoneda B S hS V) _ ?_
  rw [isOpen_pointTopology_yoneda_iff_isOpen_image,
    Set.image_preimage_eq _ (surjective_pointsToScheme B S hS V)]
  exact Q.isOpen

/-- The comparison of points with scheme points commutes with the morphism induced by a morphism
of the site. -/
private theorem pointsToScheme_comp_pointsMap_yoneda (m : W ⟶ V) :
    pointsToScheme B S hS V ∘ pointsMap B S hS (yoneda.obj W) (yoneda.map m) =
      (BigFppfOver.toScheme B S hS).map m ∘ pointsToScheme B S hS W :=
  funext fun z ↦ pointsToScheme_pointsMap_yoneda B S hS m z

/-- Two open subspaces of a represented presheaf with the same set of scheme points are equal. -/
theorem eq_of_image_pointsToScheme_eq {A A' : Subfunctor (yoneda.obj V)}
    (hA : IsOpenSubspace B S hS A) (hA' : IsOpenSubspace B S hS A')
    (h : pointsToScheme B S hS V '' Set.range (pointsMap B S hS A.toFunctor A.ι) =
      pointsToScheme B S hS V '' Set.range (pointsMap B S hS A'.toFunctor A'.ι)) :
    A = A' :=
  eq_of_range_pointsMap_ι_eq B S hS hA hA'
    ((Set.image_eq_image (injective_pointsToScheme B S hS V)).mp h)

/-- **An open immersion of the big fppf site of `S` has as image the open subspace cut out by its
image on the schemes.** -/
theorem range_yoneda_map_eq_subspaceOfOpens (i : W ⟶ V)
    (hi : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i))
    (Q : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (hQ : Set.range ((BigFppfOver.toScheme B S hS).map i) = (Q : Set _)) :
    Subfunctor.range (yoneda.map i) = subspaceOfOpens B S hS V Q := by
  have hopen : IsOpenImmersion B S hS (yoneda.map i) :=
    (presheaf_yoneda_map_iff B S hS inferInstance i).2 hi
  have _ : Mono (yoneda.map i) := mono_of_presheaf_isOpenImmersion hopen
  refine eq_of_image_pointsToScheme_eq B S hS
    (isOpenSubspace_range_of_isAlgebraicSpace B S hS (isAlgebraicSpace_yoneda B S hS W) _ hopen)
    (isOpenSubspace_subspaceOfOpens B S hS V Q) ?_
  rw [range_pointsMap_ι_range, range_pointsMap_subspaceOfOpens,
    Set.image_preimage_eq _ (surjective_pointsToScheme B S hS V), ← hQ]
  rw [← Set.range_comp, pointsToScheme_comp_pointsMap_yoneda, Set.range_comp,
    (surjective_pointsToScheme B S hS W).range_eq, Set.image_univ]

/-- The inverse image of `AlgebraicGeometry.Space.subspaceOfOpens` along a morphism of the site
is the subspace cut out by the preimage of the open subset. -/
theorem subspaceOfOpens_preimage_yoneda_map (m : W ⟶ V)
    (Q : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    (subspaceOfOpens B S hS V Q).preimage (yoneda.map m) =
      subspaceOfOpens B S hS W ((BigFppfOver.toScheme B S hS).map m ⁻¹ᵁ Q) := by
  refine eq_of_image_pointsToScheme_eq B S hS
    (isOpenSubspace_preimage B S hS (yoneda.map m) _ (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS W) (isOpenSubspace_subspaceOfOpens B S hS V Q))
    (isOpenSubspace_subspaceOfOpens B S hS W _) ?_
  rw [pointsRange_preimage, range_pointsMap_subspaceOfOpens,
    range_pointsMap_subspaceOfOpens, ← Set.preimage_comp,
    pointsToScheme_comp_pointsMap_yoneda, Set.preimage_comp,
    Set.image_preimage_eq _ (surjective_pointsToScheme B S hS W),
    Set.image_preimage_eq _ (surjective_pointsToScheme B S hS W), Scheme.Hom.coe_preimage]

end Charts

/-! ### The quasi-finite locus as an open subspace -/

section QuasiFiniteLocus

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The open subspace of the source of a morphism of algebraic spaces over `S` cut out by the
points at which the morphism is quasi-finite.

It is an open subspace by part (1) of Tag 0ABM together with part (1) of Tag 03BZ, which is
`AlgebraicGeometry.Space.isOpenSubspace_quasiFiniteLocusSubspace`, and its point set is exactly
the quasi-finite locus, which is
`AlgebraicGeometry.Space.range_pointsMap_quasiFiniteLocusSubspace`. -/
def quasiFiniteLocusSubspace (f : X ⟶ Y) : Subfunctor X :=
  openSubspaceOfPoints B S hS X {x | IsQuasiFiniteAt B S hS f x}

/-- The point set of `AlgebraicGeometry.Space.quasiFiniteLocusSubspace` is the locus of
quasi-finiteness. -/
theorem range_pointsMap_quasiFiniteLocusSubspace (f : X ⟶ Y) :
    Set.range (pointsMap B S hS (quasiFiniteLocusSubspace B S hS f).toFunctor
        (quasiFiniteLocusSubspace B S hS f).ι) = {x | IsQuasiFiniteAt B S hS f x} :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- `AlgebraicGeometry.Space.quasiFiniteLocusSubspace` is an open subspace, by part (1) of
Tag 0ABM. -/
theorem isOpenSubspace_quasiFiniteLocusSubspace (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    IsOpenSubspace B S hS (quasiFiniteLocusSubspace B S hS f) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hX _ (isOpen_setOf_isQuasiFiniteAt B S hS f)

/-- **Quasi-finiteness at a point, on a chart.** For a morphism of the big fppf site of `S` whose
underlying morphism of schemes is locally of finite type, the induced morphism of represented
presheaves is quasi-finite at a point exactly when the morphism of schemes is quasi-finite at the
corresponding scheme point. -/
theorem isQuasiFiniteAt_yoneda_map_iff {V W : BigFppfOver B S hS} (k : W ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k)]
    (x : points B S hS (yoneda.obj W)) :
    IsQuasiFiniteAt B S hS (yoneda.map k) x ↔
      ((BigFppfOver.toScheme B S hS).map k).QuasiFiniteAt (pointsToScheme B S hS W x) := by
  rw [isQuasiFiniteAt_iff_holdsOnEveryEtaleChartAtPoint B S hS
      (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS V) (yoneda.map k) x,
    holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B S hS _
      (MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget _
        locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget) k x,
    ← quasiFiniteAt_iff_hasRepresentativeWithProperty]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨finiteTypeAt_of_locallyOfFiniteType _ _, h⟩⟩

/-- **The quasi-finite locus, on a chart.** For a morphism of the big fppf site of `S` whose
underlying morphism of schemes is locally of finite type, the quasi-finite locus of the induced
morphism of represented presheaves is the open subspace cut out by Mathlib's
`AlgebraicGeometry.Scheme.Hom.quasiFiniteLocus`. -/
theorem quasiFiniteLocusSubspace_yoneda_map {V W : BigFppfOver B S hS} (k : W ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map k)] :
    quasiFiniteLocusSubspace B S hS (yoneda.map k) =
      subspaceOfOpens B S hS W ((BigFppfOver.toScheme B S hS).map k).quasiFiniteLocus :=
  congrArg (openSubspaceOfPoints B S hS (yoneda.obj W))
    (Set.ext fun x ↦ isQuasiFiniteAt_yoneda_map_iff B S hS k x)

end QuasiFiniteLocus

/-! ### The image of an open immersion out of an open subspace -/

section FromPreimage

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Two comparison morphisms between subfunctors coming from an equality are inverse to each
other. -/
private theorem homOfLe_comp_homOfLe {G₁ G₂ : Subfunctor F} (h₁ : G₁ ≤ G₂) (h₂ : G₂ ≤ G₁) :
    Subfunctor.homOfLe h₁ ≫ Subfunctor.homOfLe h₂ = 𝟙 _ := by
  apply (cancel_mono G₁.ι).mp
  rw [Category.assoc, Subfunctor.homOfLe_ι, Subfunctor.homOfLe_ι, Category.id_comp]

/-- If the inverse image along `p` of the image of `A.ι ≫ p` is `A` itself, then the canonical
morphism from that inverse image to the image is an isomorphism.

Both are identified with `A`: the inverse image by the hypothesis, and the image because
`A.ι ≫ p` is a monomorphism, so `CategoryTheory.Subfunctor.toRange` is an isomorphism. -/
theorem isIso_fromPreimage_range_of_preimage_eq (p : F ⟶ G) (A : Subfunctor F)
    [Mono (A.ι ≫ p)] (h : (Subfunctor.range (A.ι ≫ p)).preimage p = A) :
    IsIso ((Subfunctor.range (A.ι ≫ p)).fromPreimage p) := by
  have hψ : IsIso (Subfunctor.homOfLe (le_of_eq h)) :=
    ⟨⟨Subfunctor.homOfLe (le_of_eq h.symm), homOfLe_comp_homOfLe B S hS _ _,
      homOfLe_comp_homOfLe B S hS _ _⟩⟩
  have hfac : (Subfunctor.range (A.ι ≫ p)).fromPreimage p =
      Subfunctor.homOfLe (le_of_eq h) ≫ Subfunctor.toRange (A.ι ≫ p) := by
    apply (cancel_mono (Subfunctor.range (A.ι ≫ p)).ι).mp
    rw [Subfunctor.fromPreimage_ι, Category.assoc, Subfunctor.toRange_ι, ← Category.assoc,
      Subfunctor.homOfLe_ι]
  rw [hfac]
  infer_instance

end FromPreimage

end AlgebraicGeometry.Space

end
