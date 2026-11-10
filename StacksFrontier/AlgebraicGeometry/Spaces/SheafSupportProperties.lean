module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The support of an abelian sheaf on the small étale site of an algebraic space

Let `X` be an algebraic space over `S`.  The support of a local section of an abelian sheaf on
the small étale site of `X` is closed, subadditive, and shrinks along a map of abelian sheaves;
the support of the sheaf itself is the union of the images of the supports of all its local
sections, and it shrinks along a surjection and grows along an injection.  This is
Stacks 04KB.

The support of a general abelian sheaf need not be closed, but the support of a sheaf of
*rings* is: a ring is zero exactly when its unit is zero, so for a sheaf of rings the support
is cut out by the unit sections alone, and these are compatible with restriction.  This is
Stacks 04KC.

## Main results

* `AlgebraicGeometry.Space.largestOpenZeroLocus_le_of_hom`: the maximal open zero locus of a
  local section is contained in the maximal open zero locus of its image under a map of abelian
  sheaves.  Part (3) of Stacks 04KB is the statement about the complements, and is
  `AlgebraicGeometry.Space.supportOfSection_map_subset`, proved with the construction of the
  support itself.
* `AlgebraicGeometry.Space.supportOfSheaf_subset_of_injective`: the support of the source of an
  injection of abelian sheaves is contained in the support of its target.  This is part (6) of
  Stacks 04KB.
* `AlgebraicGeometry.Space.isClosed_supportOfSheaf`: the support of a sheaf of rings on the
  small étale site of an algebraic space is closed.  This is Stacks 04KC, and
  `AlgebraicGeometry.Space.pointsMap_mem_supportOfSheaf_iff` is the computation of that
  support on an étale chart that it rests on:
  `AlgebraicGeometry.Space.largestOpenZeroLocus_one_le` and
  `AlgebraicGeometry.Space.mem_largestOpenZeroLocus_one_of_pointsMap_eq` are the two
  ring-theoretic inputs.

Parts (1) and (2) of Stacks 04KB are
`AlgebraicGeometry.Space.isClosed_supportOfSection` and
`AlgebraicGeometry.Space.supportOfSection_add_subset`, already proved with the construction of
the support itself; they are registered against the tag here.  Part (4) is
`AlgebraicGeometry.Space.supportOfSheaf_eq_iUnion_image_supportOfSection`, proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafSupportSections.lean` together with part (5).

## Implementation notes

Part (3) is maximality of the zero locus of the image section applied to the zero locus of the
section: a restriction killing the section kills its image by naturality, so the zero locus of
the section is one of the opens that maximality compares against.  Nothing but naturality and
additivity of the components of `φ` is used, so no hypothesis on `X` is needed.

Parts (5) and (6) go through the geometric stalks, since
`AlgebraicGeometry.Space.supportOfSheaf` is defined by nonvanishing of the set-valued stalk of
Stacks 04JY.  Surjectivity and injectivity of the maps on those stalks is Stacks 04K5,
`AlgebraicGeometry.Space.surjective_iff_stalkSetMap_surjective` and
`AlgebraicGeometry.Space.injective_iff_stalkSetMap_injective`, which are stated for sheaves of
*sets*; the underlying sheaf of sets of an abelian sheaf is obtained by `sheafCompose` with the
forgetful functor, and `CategoryTheory.Sheaf.IsLocallySurjective` and
`CategoryTheory.Presheaf.IsLocallyInjective` are inherited by that composition.  Because
Stacks 04K5 is a statement about an algebraic space, both parts carry the algebraicity
hypothesis on `X` that Stacks 04KB carries anyway.

Nonvanishing of the stalk is the failure of `Subsingleton`, so the two parts are the two
elementary transfers of `Subsingleton` along a surjection and along an injection.

Surjectivity of a map of sheaves is `CategoryTheory.Sheaf.IsLocallySurjective`, local
liftability of sections, which is the source's notion; it implies being an epimorphism by
`CategoryTheory.Sheaf.epi_of_isLocallySurjective`, and the converse is
`CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`, whose extra instance hypotheses
(`CategoryTheory.HasSheafify`, `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`
and `CategoryTheory.Balanced` for this site) are not available here, so the epimorphism reading
is not recorded.  Injectivity of a map of sheaves is injectivity on sections over every étale
chart, which is how part (6) states it.

Stacks 04KC is read here as a statement about `AlgebraicGeometry.Space.toAddCommGrp`, the
abelian sheaf underlying a sheaf of rings, which is the sheaf whose support
`AlgebraicGeometry.Space.supportOfSheaf` is; nothing is lost, since a ring is zero exactly
when its underlying abelian group is.  Its support is therefore the locus where the ring sheaf
is *not* the zero ring, and the proof says just that: on an étale chart the support is the
support of the unit section, so its complement is the image of an open set.

The small étale site of an algebraic space has **no final object** — the space itself is not
a scheme — so, unlike the scheme-level
`AlgebraicGeometry.SmallEtale.isClosed_supportSheaf` of Stacks 04FU, there is no single global
unit section to reduce to; and the support is defined by the existence of *one* geometric
point with nonzero stalk, so a statement about one chosen geometric point over a point does
not immediately compute it (that would be Tag 04K0, which is unavailable).  Both obstructions
are met by `AlgebraicGeometry.Space.mem_largestOpenZeroLocus_one_of_pointsMap_eq`: the zero
locus of the unit section of a chart is saturated for the map to the space, because two points
of two charts with the same image come from one point of their fibre product — their product
in the small étale site, `AlgebraicGeometry.Space.SmallEtale.prodObj` — on which the two unit
sections agree.  Closedness then only needs one surjective étale chart, which is the atlas of
`AlgebraicGeometry.IsAlgebraicSpace`, surjective on points by Stacks 03H5.

## References

* [Stacks Project, Lemma 66.21.2 (Tag 04KB)](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 04KC](https://stacks.math.columbia.edu/tag/04KC)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

attribute [local instance] pointTopology

/-! ### Supports of local sections along a map of abelian sheaves -/

/-- The maximal open zero locus of a local section is contained in the maximal open zero locus
of its image under a map of abelian sheaves.

This is maximality of the latter applied to the former: a restriction of the section to an
étale chart which vanishes has vanishing image by naturality. -/
theorem largestOpenZeroLocus_le_of_hom
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}} (φ : F ⟶ G)
    (U : SmallEtale B S hS X) (σ : F.obj.obj (op U)) :
    largestOpenZeroLocus B S hS X F U σ ≤
      largestOpenZeroLocus B S hS X G U (φ.hom.app (op U) σ) := by
  refine largestOpenZeroLocus_maximal B S hS X G U _ _ fun V f hf ↦ ?_
  have h0 : F.obj.map f.op σ = 0 :=
    (largestOpenZeroLocus_restrict_iff B S hS X F U σ V f).2 hf
  rw [show G.obj.map f.op (φ.hom.app (op U) σ) = _ from
    (NatTrans.naturality_apply (φ := φ.hom) (f := f.op) σ).symm, h0, map_zero]

/-! ### Supports of abelian sheaves along surjections and injections -/

/-- **Stacks 04KB, part (6).** If a map of abelian sheaves on the small étale site of an
algebraic space is injective on sections over every étale chart, then the support of its source
is contained in the support of its target.

Such a map is injective on every geometric stalk by Stacks 04K5, and an injection into a
subsingleton has subsingleton source.

The hypothesis is the sectionwise one, which is what a splitting of sheaves supplies.
`AlgebraicGeometry.Space.supportOfSheaf_subset_of_mono` draws the same conclusion from a `Mono`
instance in the sheaf category; neither hypothesis is the other, the passage between them being
full faithfulness of `CategoryTheory.sheafToPresheaf` together with
`CategoryTheory.NatTrans.mono_iff_mono_app`, so both forms are stated. -/
@[stacks 04KB "part (6): support along an injection"]
theorem supportOfSheaf_subset_of_injective (hX : IsAlgebraicSpace B S hS X)
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}} (φ : F ⟶ G)
    (hφ : ∀ U : SmallEtale B S hS X, Function.Injective (φ.hom.app (op U))) :
    supportOfSheaf B S hS X F ⊆ supportOfSheaf B S hS X G := by
  have : Sheaf.IsLocallyInjective φ :=
    Presheaf.isLocallyInjective_of_injective _ _ fun U ↦ hφ U.unop
  have hinj := (injective_iff_stalkSetMap_injective B S hS X hX
    ((sheafCompose (SmallEtale.topology B S hS X)
      (forget AddCommGrpCat.{v})).map φ)).1
      (fun U ↦ (Sheaf.isLocallyInjective_iff_injective
        ((sheafCompose (SmallEtale.topology B S hS X)
          (forget AddCommGrpCat.{v})).map φ)).1 inferInstance (op U))
  rintro x ⟨p, hp, hns⟩
  exact ⟨p, hp, fun hsub ↦ hns ⟨fun a b ↦ hinj p (hsub.elim _ _)⟩⟩

/-! ### The support of a sheaf of rings -/

section Ring

variable (R : Sheaf (SmallEtale.topology B S hS X) RingCat.{v})

/-- The additive sheaf underlying a sheaf of rings on the small étale site: the forgetful
functor from rings to abelian groups preserves limits, hence carries sheaves to sheaves.

This is the sheaf whose support `AlgebraicGeometry.Space.supportOfSheaf` is; a ring is the
zero ring exactly when its underlying abelian group is zero, so no information about the
support is lost by forgetting the multiplication. -/
abbrev toAddCommGrp : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v} :=
  (sheafCompose (SmallEtale.topology B S hS X)
    (forget₂ RingCat.{v} AddCommGrpCat.{v})).obj R

/-- Restriction of sections of a sheaf of rings carries the unit section to the unit
section. -/
private theorem restrict_one {U V : SmallEtale B S hS X} (f : V ⟶ U) :
    (toAddCommGrp B S hS X R).obj.map f.op (1 : R.obj.obj (op U)) =
      (1 : R.obj.obj (op V)) := by
  change (R.obj.map f.op).hom (1 : R.obj.obj (op U)) = _
  exact map_one _

/-- The maximal open zero locus of the unit section of a sheaf of rings is contained in the
maximal open zero locus of every section over the same étale chart.

A chart on which the unit section restricts to zero is one whose ring of sections is the zero
ring, so every section restricts to zero on it. -/
theorem largestOpenZeroLocus_one_le (U : SmallEtale B S hS X) (σ : R.obj.obj (op U)) :
    largestOpenZeroLocus B S hS X (toAddCommGrp B S hS X R) U (1 : R.obj.obj (op U)) ≤
      largestOpenZeroLocus B S hS X (toAddCommGrp B S hS X R) U σ := by
  refine largestOpenZeroLocus_mono_of_restrict B S hS X (toAddCommGrp B S hS X R) U
    (1 : R.obj.obj (op U)) σ fun V f hf ↦ ?_
  have h1 : (1 : R.obj.obj (op V)) = 0 := by
    rwa [← restrict_one B S hS X R f]
  change (R.obj.map f.op).hom σ = 0
  exact eq_zero_of_zero_eq_one h1.symm _

/-- Membership in the maximal open zero locus of the unit section depends only on the image
point of the algebraic space: if a point of an étale chart lying in that zero locus has the
same image as a point of another étale chart, then the second point lies in the zero locus of
the unit section of the second chart.

The two points are the images of a single point of the fibre product of the two charts, which
is their product in the small étale site: that product square is cartesian already as a square
of presheaves, because an étale chart is a representable morphism, and a point of the fibre
product over the two given points is `AlgebraicGeometry.Space.exists_points_of_isPullback`.
The unit section restricts to the unit section, so the zero locus of the unit section of
either chart pulls back to the zero locus of the unit section of the product
(`AlgebraicGeometry.Space.zeroImages_restrict`), and the two conditions on the single point of
the product contradict each other. -/
theorem mem_largestOpenZeroLocus_one_of_pointsMap_eq (U V : SmallEtale B S hS X)
    (y : points B S hS (yoneda.obj U.obj.left))
    (z : points B S hS (yoneda.obj V.obj.left))
    (hyz : pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom y =
      pointsMap B S hS (yoneda.obj V.obj.left) V.obj.hom z)
    (hy : y ∈ (largestOpenZeroLocus B S hS X (toAddCommGrp B S hS X R) U
      (1 : R.obj.obj (op U))).1) :
    z ∈ (largestOpenZeroLocus B S hS X (toAddCommGrp B S hS X R) V
      (1 : R.obj.obj (op V))).1 := by
  by_contra hz
  have hsq : IsPullback
      (yoneda.map ((SmallEtale.toOver B S hS X).map (SmallEtale.prodFst B S hS X U V)))
      (yoneda.map ((SmallEtale.toOver B S hS X).map (SmallEtale.prodSnd B S hS X U V)))
      U.obj.hom V.obj.hom := U.property.rep.isPullback' V.obj.hom
  obtain ⟨w, hw₁, hw₂⟩ := exists_points_of_isPullback B S hS hsq y z hyz
  have key : ∀ (W : SmallEtale B S hS X) (f : SmallEtale.prodObj B S hS X U V ⟶ W) x,
      x ∈ zeroImages B S hS X (toAddCommGrp B S hS X R) _ (1 : R.obj.obj (op _)) ↔
        pointsMap B S hS _ (yoneda.map ((SmallEtale.toOver B S hS X).map f)) x ∈
          zeroImages B S hS X (toAddCommGrp B S hS X R) W (1 : R.obj.obj (op W)) := fun W f x ↦ by
    simpa only [restrict_one, Set.ext_iff, Set.mem_preimage] using
      Set.ext_iff.1 (zeroImages_restrict B S hS X (toAddCommGrp B S hS X R) W
        (1 : R.obj.obj (op W)) (SmallEtale.prodObj B S hS X U V) f) x
  exact hz (hw₂ ▸ (key V (SmallEtale.prodSnd B S hS X U V) w).1
    ((key U (SmallEtale.prodFst B S hS X U V) w).2 (hw₁ ▸ hy)))

/-- A point of an étale chart of an algebraic space lies over a point of the support of a
sheaf of rings exactly when it lies in the support of the unit section of that chart.

For a sheaf of rings the geometric stalks are controlled by the unit section alone
(`AlgebraicGeometry.Space.largestOpenZeroLocus_one_le`), and whether the unit section vanishes
near a point of a chart only depends on the image of that point
(`AlgebraicGeometry.Space.mem_largestOpenZeroLocus_one_of_pointsMap_eq`); the geometric point
needed for the converse is a geometric representative of the point of the chart
(`AlgebraicGeometry.Space.exists_geometricRepresentative`), for which the chart itself is a
small étale neighbourhood. -/
theorem pointsMap_mem_supportOfSheaf_iff (hX : IsAlgebraicSpace B S hS X)
    (U : SmallEtale B S hS X) (y : points B S hS (yoneda.obj U.obj.left)) :
    pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom y ∈
        supportOfSheaf B S hS X (toAddCommGrp B S hS X R) ↔
      y ∈ supportOfSection B S hS X (toAddCommGrp B S hS X R) U
        (1 : R.obj.obj (op U)) := by
  constructor
  · rintro ⟨p, hp, hn⟩ hy
    refine hn ((subsingleton_stalkSet_iff B S hS X hX (toAddCommGrp B S hS X R) p).mpr ?_)
    intro N σ
    refine largestOpenZeroLocus_one_le B S hS X R N.chart σ ?_
    refine mem_largestOpenZeroLocus_one_of_pointsMap_eq B S hS X R U N.chart y
      (neighborhoodPoint B S hS X N).image ?_ hy
    exact ((neighborhoodPoint_image B S hS X N).trans hp).symm
  · intro hy
    obtain ⟨q, hq⟩ := exists_geometricRepresentative B S hS (yoneda.obj U.obj.left) y
    let p : GeometricPoint B S hS X :=
      ⟨FieldValuedPoint.map B S hS _ U.obj.hom q.val, q.property⟩
    let N : SmallEtaleNeighborhood p := ⟨U, q.val.value, rfl⟩
    refine ⟨p, ?_, ?_⟩
    · change (FieldValuedPoint.map B S hS _ U.obj.hom q.val).class B S hS X =
        pointsMap B S hS _ U.obj.hom y
      rw [← hq, pointsMap_class]
    · intro hn
      have hz := (subsingleton_stalkSet_iff B S hS X hX (toAddCommGrp B S hS X R) p).mp hn N
        (1 : R.obj.obj (op U))
      change q.image ∈ (largestOpenZeroLocus B S hS X (toAddCommGrp B S hS X R) U
        (1 : R.obj.obj (op U))).1 at hz
      exact hy (hq ▸ hz)

/-- **Stacks 04KC.** The support of a sheaf of rings on the small étale site of an algebraic
space is closed.

The support is the set of points of the space at which the stalk of the underlying abelian
sheaf at some geometric point is nonzero; for a sheaf of rings that is the set of points at
which the ring of germs is not the zero ring, since a ring vanishes exactly when its unit
does. Its complement is exhibited as the image of the maximal open zero locus of the unit
section of a surjective étale atlas, which is open because an étale chart is open on points
by clause (3) of Stacks 03BX. -/
@[stacks 04KC]
theorem isClosed_supportOfSheaf (hX : IsAlgebraicSpace B S hS X) :
    IsClosed (supportOfSheaf B S hS X (toAddCommGrp B S hS X R)) := by
  obtain ⟨A, a, hsurj, hetale⟩ := hX.exists_atlas
  let C : SmallEtale B S hS X := ⟨CostructuredArrow.mk a, hetale⟩
  have hsurjC : Function.Surjective
      (pointsMap B S hS (yoneda.obj C.obj.left) C.obj.hom) :=
    (surjective_iff_surjective_pointsMap B S hS X hX A a).1 hsurj
  have hset : (supportOfSheaf B S hS X (toAddCommGrp B S hS X R))ᶜ =
      pointsMap B S hS (yoneda.obj C.obj.left) C.obj.hom ''
        (largestOpenZeroLocus B S hS X (toAddCommGrp B S hS X R) C
          (1 : R.obj.obj (op C))).1 := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hsurjC x
      refine ⟨y, ?_, rfl⟩
      by_contra hy
      exact hx ((pointsMap_mem_supportOfSheaf_iff B S hS X R hX C y).2 hy)
    · rintro ⟨y, hy, rfl⟩
      exact fun hmem ↦ (pointsMap_mem_supportOfSheaf_iff B S hS X R hX C y).1 hmem hy
  rw [← isOpen_compl_iff, hset]
  exact isOpenMap_pointsMap_of_presheafEtale B S hS C.obj.hom C.property _
    (largestOpenZeroLocus B S hS X (toAddCommGrp B S hS X R) C (1 : R.obj.obj (op C))).2

end Ring

end AlgebraicGeometry.Space

/-! ### Parts (1) and (2) of Stacks 04KB

Closedness of the support of a local section and the containment of the support of a sum in the
union of the supports are proved together with the construction of the support, in
`StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport`, where
`AlgebraicGeometry.Space.isClosed_supportOfSection` and
`AlgebraicGeometry.Space.supportOfSection_add_subset` carry the tag at their declarations. -/

end
