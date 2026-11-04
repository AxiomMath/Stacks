module

public import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf

/-!
# The zero locus of a section on the spaces-étale site of an algebraic space

Let `F` be an abelian sheaf on the spaces-étale site of an algebraic space `X` over `S` and
let `σ` be a section of `F` over an object `U` of that site. There is an open subspace `W` of
the algebraic space underlying `U` which is the largest one on which `σ` vanishes: it is the
subspace whose points are those lying in the image of some object of the site over `U` on
which `σ` restricts to zero. The same subspace is detected by restriction along an arbitrary
morphism of the site and by the germs of `σ` at the geometric points of `U`.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.ImageInOpen` is the condition on a morphism of the
  spaces-étale site that the image of the points of its source lands in a prescribed set of
  points of its target, and `AlgebraicGeometry.Space.SpacesEtale.openPoints` is the point set
  of an open subspace.
* `AlgebraicGeometry.Space.SpacesEtale.zeroImages` is the set of points of `U` in the image
  of some object of the site over `U` on which the section vanishes, and
  `AlgebraicGeometry.Space.SpacesEtale.largestOpenZeroSubspace` is the open subspace of `U`
  it corresponds to.
* `AlgebraicGeometry.Space.SpacesEtale.openSubspaceObject` and
  `AlgebraicGeometry.Space.SpacesEtale.openSubspaceInclusion` read an open subspace of the
  algebraic space underlying an object of the site as an object of the site over it.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.largestOpenZeroSubspace_restrict_iff` is the
  restriction criterion: the section vanishes on an object over `U` exactly when the image of
  that object lies in the largest open zero subspace. Its substantial direction is
  `AlgebraicGeometry.Space.SpacesEtale.eq_zero_of_imageInOpen_zeroImages`.
* `AlgebraicGeometry.Space.SpacesEtale.restrict_largestOpenZeroSubspace_eq_zero` and
  `AlgebraicGeometry.Space.SpacesEtale.largestOpenZeroSubspace_maximal` say that the section
  vanishes on the largest open zero subspace and that every open subspace on which it
  vanishes is contained in it.
* `AlgebraicGeometry.Space.SpacesEtale.germ_eq_zero_iff_mem_largestOpenZeroSubspace` is the
  geometric-point criterion: the germ of the section at a geometric point of `U` vanishes in
  the spaces-étale stalk at the image of that point in `X` exactly when the point lies in the
  largest open zero subspace.
* `AlgebraicGeometry.Space.SpacesEtale.exists_largestOpenZeroSubspace` collects the three
  clauses into the existence statement of **Stacks 04K9**.

## Implementation notes

The topology on the point sets is `AlgebraicGeometry.Space.pointTopology`, installed as a
local instance; open subspaces are subfunctors, and the passage between an open subspace and
its point set is the order isomorphism of Tag 03BZ. Openness of the zero images is Tag 03IR:
every morphism of the spaces-étale site is étale by Tag 03FV, hence open on points, so the
zero images are a union of open ranges.

The restriction criterion is proved by covering: for the objects `g : Z ⟶ U` killing the
section, the fibre products `V ×_U Z` jointly cover any `V` whose image lies in the zero
images, because a point of `V` and a point of `Z` with the same image in `U` lift to a point
of the fibre product by Tag 03H4. Unlike on the small étale site, this family is already a
chosen covering family: the covering families of the spaces-étale site are all families
indexed at the universe of its objects. Separatedness of the sheaf then gives the vanishing.

Maximality uses `AlgebraicGeometry.Space.SpacesEtale.openSubspaceObject`: an open subspace of
the algebraic space underlying an object of the site is itself such an object, because an
open immersion is étale, so the restriction criterion applies to it directly.

The geometric-point clause is read in the stalk of Tag 04JZ, the colimit of the sections of
the sheaf over the étale neighbourhoods of the image geometric point. That colimit is
filtered because the category of étale neighbourhoods is cofiltered (Tag 04JW), so a germ
vanishes exactly when the section already vanishes on some neighbourhood; the two directions
are then the restriction criterion together with Tag 03IE, which factors the field-valued
point of `U` through the open subspace once its class lies in the point set.

## References

* [Stacks Project, Lemma 66.20.2 (Tag 04K9)](https://stacks.math.columbia.edu/tag/04K9)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 04JZ](https://stacks.math.columbia.edu/tag/04JZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

namespace SpacesEtale

/-- The algebraic space over `S` underlying an object of the spaces-étale site of `X`. -/
abbrev underlying (U : SpacesEtale B S hS X) : AlgebraicSpaces B S hS :=
  (toSpaces B S hS X).obj U

/-- The condition on a morphism `f : V ⟶ U` of the spaces-étale site of `X` that the image of
the points of `V` lands inside a prescribed set of points of the algebraic space underlying
`U`. -/
def ImageInOpen {U : SpacesEtale B S hS X}
    (W : Set (points B S hS (underlying B S hS X U).1))
    {V : SpacesEtale B S hS X} (f : V ⟶ U) : Prop :=
  ∀ y : points B S hS (underlying B S hS X V).1,
    pointsMap B S hS (underlying B S hS X V).1 ((toSpaces B S hS X).map f).hom y ∈ W

/-! ### Open subspaces of an object of the site -/

/-- The set of points of an open subspace of the algebraic space underlying an object of the
spaces-étale site of `X`, as a subset of the points of that algebraic space. -/
noncomputable def openPoints (U : SpacesEtale B S hS X)
    (W : {W : Subfunctor (underlying B S hS X U).1 // IsOpenSubspace B S hS W}) :
    Set (points B S hS (underlying B S hS X U).1) :=
  Set.range (pointsMap B S hS W.1.toFunctor W.1.ι)

/-- **Stacks 03BZ, part (1).** The point set of an open subspace is open. -/
theorem isOpen_openPoints (U : SpacesEtale B S hS X)
    (W : {W : Subfunctor (underlying B S hS X U).1 // IsOpenSubspace B S hS W}) :
    IsOpen (openPoints B S hS X U W) :=
  isOpen_range_pointsMap_of_isOpenImmersion B S hS W.1.ι W.2.2

/-- **Stacks 03BZ, part (1).** The point set of an open subspace is the open set the
correspondence of Tag 03BZ attaches to it. -/
theorem coe_openSubspacesOrderIso (U : SpacesEtale B S hS X)
    (W : {W : Subfunctor (underlying B S hS X U).1 // IsOpenSubspace B S hS W}) :
    (openSubspacesOrderIso B S hS (underlying B S hS X U).1
        (underlying B S hS X U).2 W).1 = openPoints B S hS X U W :=
  openSubspacesOrderIso_apply B S hS (underlying B S hS X U).1
    (underlying B S hS X U).2 W

/-- Two open subspaces of the algebraic space underlying an object of the spaces-étale site
of `X` are nested as soon as their point sets are. -/
theorem le_of_openPoints_subset (U : SpacesEtale B S hS X)
    {W W' : {W : Subfunctor (underlying B S hS X U).1 // IsOpenSubspace B S hS W}}
    (h : openPoints B S hS X U W ⊆ openPoints B S hS X U W') : W.1 ≤ W'.1 := by
  refine Subtype.coe_le_coe.2 ?_
  refine (openSubspacesOrderIso B S hS (underlying B S hS X U).1
    (underlying B S hS X U).2).le_iff_le.1 fun z hz ↦ ?_
  rw [← coe_openSubspacesOrderIso B S hS X U W'] at h
  rw [← coe_openSubspacesOrderIso B S hS X U W] at h
  exact h hz

/-- An open subspace of the algebraic space underlying an object `U` of the spaces-étale site
of `X`, read as an object of that site: an open immersion is étale, so its composite with the
structure morphism of `U` is étale by Tag 03FT. -/
noncomputable def openSubspaceObject (U : SpacesEtale B S hS X)
    (W : {W : Subfunctor (underlying B S hS X U).1 // IsOpenSubspace B S hS W}) :
    SpacesEtale B S hS X :=
  ⟨Over.mk ((ObjectProperty.homMk W.1.ι :
      (⟨W.1.toFunctor, W.2.1⟩ : AlgebraicSpaces B S hS) ⟶ underlying B S hS X U) ≫ U.1.hom),
    isEtale_comp B S hS
      (isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS W.2.2))
      U.property⟩

/-- The inclusion of `AlgebraicGeometry.Space.SpacesEtale.openSubspaceObject` into the
ambient object of the spaces-étale site of `X`. -/
noncomputable def openSubspaceInclusion (U : SpacesEtale B S hS X)
    (W : {W : Subfunctor (underlying B S hS X U).1 // IsOpenSubspace B S hS W}) :
    openSubspaceObject B S hS X U W ⟶ U :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk W.1.ι) rfl)

/-- The image of the points of an open subspace is its own point set. -/
theorem imageInOpen_openSubspaceInclusion (U : SpacesEtale B S hS X)
    (W : {W : Subfunctor (underlying B S hS X U).1 // IsOpenSubspace B S hS W}) :
    ImageInOpen B S hS X (openPoints B S hS X U W)
      (openSubspaceInclusion B S hS X U W) :=
  fun y ↦ ⟨y, rfl⟩

/-! ### The zero images of a section -/

/-- The points of an object `U` of the spaces-étale site of `X` lying in the image of some
object of the site over `U` on which a section restricts to zero. -/
def zeroImages (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    (U : SpacesEtale B S hS X) (σ : F.obj.obj (op U)) :
    Set (points B S hS (underlying B S hS X U).1) :=
  {x | ∃ (V : SpacesEtale B S hS X) (f : V ⟶ U), F.obj.map f.op σ = 0 ∧
    ∃ y : points B S hS (underlying B S hS X V).1,
      pointsMap B S hS (underlying B S hS X V).1
        ((toSpaces B S hS X).map f).hom y = x}

/-- **Stacks 03IR.** The zero images of a section form an open set: they are a union of the
ranges of the maps on points of the morphisms of the site killing the section, and each such
morphism is étale, hence open on points. -/
theorem isOpen_zeroImages (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    (U : SpacesEtale B S hS X) (σ : F.obj.obj (op U)) :
    IsOpen (zeroImages B S hS X F U σ) := by
  rw [show zeroImages B S hS X F U σ =
      ⋃ V : SpacesEtale B S hS X, ⋃ f : V ⟶ U,
        {x | F.obj.map f.op σ = 0 ∧ x ∈ Set.range
          (pointsMap B S hS (underlying B S hS X V).1
            ((toSpaces B S hS X).map f).hom)} by
    ext x
    simp only [zeroImages, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range]]
  refine isOpen_iUnion fun V ↦ isOpen_iUnion fun f ↦ ?_
  by_cases hf : F.obj.map f.op σ = 0
  · simp only [hf, true_and]
    exact (isOpenMap_pointsMap_of_isEtale B S hS ((toSpaces B S hS X).map f).hom
      (underlying B S hS X V).2 (underlying B S hS X U).2
      (isEtale_toSpaces_map B S hS X f)).isOpen_range
  · simp [hf]

/-- A section of a sheaf on the spaces-étale site that restricts to zero along `b` restricts to
zero along any composite `a ≫ b`. -/
private theorem map_comp_op_eq_zero (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    {U V W : SpacesEtale B S hS X} (a : U ⟶ V) (b : V ⟶ W) (s : F.obj.obj (op W))
    (h : F.obj.map b.op s = 0) : F.obj.map (a ≫ b).op s = 0 := by
  rw [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, h]
  simp

/-- A section of a sheaf on the spaces-étale site of `X` vanishing after restriction along
every member of a covering family is zero. -/
theorem eq_zero_of_isCovering (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    (V : SpacesEtale B S hS X) (E : PreZeroHypercover.{u + 1} V)
    (hE : IsCovering B S hS X ⟨V, E⟩) (s : F.obj.obj (op V))
    (hz : ∀ i, F.obj.map (E.f i).op s = 0) : s = 0 := by
  have htop : Sieve.generate E.presieve₀ ∈ topology B S hS X V := by
    rw [Precoverage.mem_toGrothendieck_iff]
    exact Precoverage.Saturate.of V E.presieve₀
      ((mem_precoverage_iff B S hS X).2 ⟨E, rfl, hE⟩)
  refine F.property.isSeparated V (Sieve.generate E.presieve₀) htop s 0 ?_
  rintro Y g ⟨Z, k, hk, ⟨i⟩, rfl⟩
  simpa using map_comp_op_eq_zero B S hS X F _ _ s (hz i)

/-- The substantial half of the restriction criterion: a section whose restriction to an
object `V` of the site over `U` has image inside the zero images restricts to zero on `V`.

The objects over `V` accounted for by some `g : Z ⟶ U` killing the section are the fibre
products `V ×_U Z`, and these jointly cover `V`: a point of `V` is witnessed by a point of
`Z` with the same image in `U`, and `AlgebraicGeometry.Space.exists_point_of_isPullback`
lifts the pair to a point of the fibre product. The family is indexed by the objects of the
site, hence is a chosen covering family, and separatedness of the sheaf concludes. -/
theorem eq_zero_of_imageInOpen_zeroImages
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    (U : SpacesEtale B S hS X) (σ : F.obj.obj (op U))
    (V : SpacesEtale B S hS X) (f : V ⟶ U)
    (himage : ImageInOpen B S hS X (zeroImages B S hS X F U σ) f) :
    F.obj.map f.op σ = 0 := by
  classical
  let I := Σ Z : SpacesEtale B S hS X, {g : Z ⟶ U // F.obj.map g.op σ = 0}
  let E : PreZeroHypercover.{u + 1} V :=
    ⟨I, fun i ↦ pullback f i.2.1, fun i ↦ pullback.fst f i.2.1⟩
  have hcov : IsCovering B S hS X ⟨V, E⟩ := by
    intro y
    obtain ⟨Z, g, hg, z, hzy⟩ := himage y
    have hsq : IsPullback ((toSpaces B S hS X).map (pullback.fst f g))
        ((toSpaces B S hS X).map (pullback.snd f g))
        ((toSpaces B S hS X).map f) ((toSpaces B S hS X).map g) :=
      (IsPullback.of_hasPullback f g).map (toSpaces B S hS X)
    obtain ⟨w, hwp, -⟩ := exists_point_of_isPullback B S hS hsq y z hzy.symm
    exact ⟨⟨Z, ⟨g, hg⟩⟩, w, hwp⟩
  refine eq_zero_of_isCovering B S hS X F V E hcov (F.obj.map f.op σ) fun i ↦ ?_
  have h := map_comp_op_eq_zero B S hS X F (pullback.snd f i.2.1) i.2.1 σ i.2.2
  rw [← pullback.condition] at h
  simpa only [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply] using h

/-! ### The largest open subspace on which a section vanishes -/

/-- **Stacks 04K9, part (1).** The largest open subspace of the algebraic space underlying an
object `U` of the spaces-étale site of `X` on which a section of an abelian sheaf over `U`
vanishes: the open subspace whose point set is the zero images of the section. -/
@[stacks 04K9 "part (1): the open subspace"]
noncomputable def largestOpenZeroSubspace
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    (U : SpacesEtale B S hS X) (σ : F.obj.obj (op U)) :
    {W : Subfunctor (underlying B S hS X U).1 // IsOpenSubspace B S hS W} :=
  (openSubspacesOrderIso B S hS (underlying B S hS X U).1
      (underlying B S hS X U).2).symm
    ⟨zeroImages B S hS X F U σ, isOpen_zeroImages B S hS X F U σ⟩

/-- The point set of the largest open zero subspace is the zero images of the section. -/
@[simp]
theorem openPoints_largestOpenZeroSubspace
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    (U : SpacesEtale B S hS X) (σ : F.obj.obj (op U)) :
    openPoints B S hS X U (largestOpenZeroSubspace B S hS X F U σ) =
      zeroImages B S hS X F U σ := by
  rw [← coe_openSubspacesOrderIso]
  exact congrArg (fun W : TopologicalSpace.Opens _ ↦ W.1)
    ((openSubspacesOrderIso B S hS (underlying B S hS X U).1
      (underlying B S hS X U).2).apply_symm_apply _)

/-- **Stacks 04K9, part (2).** A section restricts to zero on an object of the spaces-étale
site over `U` exactly when the image of the points of that object lies in the largest open
zero subspace. -/
@[stacks 04K9 "part (2): the pullback criterion"]
theorem largestOpenZeroSubspace_restrict_iff
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    (U : SpacesEtale B S hS X) (σ : F.obj.obj (op U))
    (V : SpacesEtale B S hS X) (f : V ⟶ U) :
    F.obj.map f.op σ = 0 ↔
      ImageInOpen B S hS X
        (openPoints B S hS X U (largestOpenZeroSubspace B S hS X F U σ)) f := by
  rw [openPoints_largestOpenZeroSubspace]
  exact ⟨fun hzero y ↦ ⟨V, f, hzero, y, rfl⟩,
    eq_zero_of_imageInOpen_zeroImages B S hS X F U σ V f⟩

/-- **Stacks 04K9, part (1).** A section vanishes on its largest open zero subspace. -/
@[stacks 04K9 "part (1): the section vanishes on the open subspace"]
theorem restrict_largestOpenZeroSubspace_eq_zero
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    (U : SpacesEtale B S hS X) (σ : F.obj.obj (op U)) :
    F.obj.map (openSubspaceInclusion B S hS X U
      (largestOpenZeroSubspace B S hS X F U σ)).op σ = 0 :=
  (largestOpenZeroSubspace_restrict_iff B S hS X F U σ _ _).2
    (imageInOpen_openSubspaceInclusion B S hS X U
      (largestOpenZeroSubspace B S hS X F U σ))

/-- **Stacks 04K9, part (1).** Every open subspace on which a section vanishes is contained in
its largest open zero subspace. -/
@[stacks 04K9 "part (1): maximality"]
theorem largestOpenZeroSubspace_maximal
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    (U : SpacesEtale B S hS X) (σ : F.obj.obj (op U))
    (W : {W : Subfunctor (underlying B S hS X U).1 // IsOpenSubspace B S hS W})
    (hW : F.obj.map (openSubspaceInclusion B S hS X U W).op σ = 0) :
    W.1 ≤ (largestOpenZeroSubspace B S hS X F U σ).1 := by
  refine le_of_openPoints_subset B S hS X U ?_
  rintro z ⟨w, rfl⟩
  exact (largestOpenZeroSubspace_restrict_iff B S hS X F U σ _
    (openSubspaceInclusion B S hS X U W)).1 hW w

/-! ### The criterion at a geometric point -/

/-- The image in `X` of a geometric point of the algebraic space underlying an object of the
spaces-étale site of `X`. -/
noncomputable abbrev imageGeometricPoint (U : SpacesEtale B S hS X)
    (p : GeometricPoint B S hS (underlying B S hS X U).1) : GeometricPoint B S hS X.1 :=
  geometricPointMap ((inclusion B S hS X).obj U).hom.hom p

/-- An object of the spaces-étale site of `X` is an étale neighbourhood in `X` of the image
of any geometric point of its underlying algebraic space. -/
noncomputable abbrev neighborhoodOfGeometricPoint (U : SpacesEtale B S hS X)
    (p : GeometricPoint B S hS (underlying B S hS X U).1) :
    EtaleNeighborhood B S hS X.1 X.2 (imageGeometricPoint B S hS X U p) :=
  etaleNeighborhoodOfSitePoint B S hS X (imageGeometricPoint B S hS X U p) U
    p.val.value rfl

/-- **Stacks 04K9, part (3).** The germ of a section at a geometric point of the algebraic
space underlying an object `U` of the spaces-étale site of `X` vanishes in the spaces-étale
stalk at the image of that point in `X` exactly when the point lies in the largest open zero
subspace of the section.

The colimit defining the stalk is filtered, so the germ vanishes exactly when the section
already vanishes on some étale neighbourhood refining `U`; one direction is then the
restriction criterion applied to such a refinement, and the other is the restriction
criterion applied to the largest open zero subspace itself, which the field-valued point
factors through by Tag 03IE. -/
@[stacks 04K9 "part (3): the geometric-point criterion", sga "2 XIV 1.8.2.1" "abelian, geom. point"]
theorem germ_eq_zero_iff_mem_largestOpenZeroSubspace
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    (U : SpacesEtale B S hS X) (σ : F.obj.obj (op U))
    (p : GeometricPoint B S hS (underlying B S hS X U).1) :
    (spacesNeighborhoodSections (imageGeometricPoint B S hS X U p)
        (F.obj ⋙ forget AddCommGrpCat.{v})).ιColimitType
      (op (neighborhoodOfGeometricPoint B S hS X U p)) σ =
    (spacesNeighborhoodSections (imageGeometricPoint B S hS X U p)
        (F.obj ⋙ forget AddCommGrpCat.{v})).ιColimitType
      (op (neighborhoodOfGeometricPoint B S hS X U p)) (0 : F.obj.obj (op U)) ↔
      p.image ∈ openPoints B S hS X U (largestOpenZeroSubspace B S hS X F U σ) := by
  set x := imageGeometricPoint B S hS X U p
  set N := neighborhoodOfGeometricPoint B S hS X U p
  have hgerm :
      (spacesNeighborhoodSections x
          (F.obj ⋙ forget AddCommGrpCat.{v})).ιColimitType (op N) σ =
        (spacesNeighborhoodSections x
          (F.obj ⋙ forget AddCommGrpCat.{v})).ιColimitType (op N)
            (0 : F.obj.obj (op U)) ↔
        ∃ (T : EtaleNeighborhood B S hS X.1 X.2 x) (h : T ⟶ N),
          F.obj.map (spacesNeighborhoodMap x h).op σ = 0 := by
    have hcol := Functor.ιColimitType_eq_iff_of_isFiltered'
      (F := spacesNeighborhoodSections x (F.obj ⋙ forget AddCommGrpCat.{v}))
      (j := op N) σ (0 : F.obj.obj (op U))
    refine hcol.trans ⟨fun ⟨T, k, heq⟩ ↦ ⟨T.unop, k.unop, ?_⟩,
      fun ⟨T, h, hh⟩ ↦ ⟨op T, h.op, ?_⟩⟩
    · change F.obj.map (spacesNeighborhoodMap x k.unop).op σ =
        F.obj.map (spacesNeighborhoodMap x k.unop).op 0 at heq
      simpa only [map_zero] using heq
    · show F.obj.map (spacesNeighborhoodMap x h).op σ =
        F.obj.map (spacesNeighborhoodMap x h).op 0
      simpa only [map_zero] using hh

  rw [hgerm]
  constructor
  · rintro ⟨T, h, hzero⟩
    let V := etaleSiteObjectOfNeighborhood B S hS X x T
    let f : V ⟶ U := spacesNeighborhoodMap x h
    let qv : FieldValuedPoint B S hS (underlying B S hS X V).1 :=
      { carrier := x.val.carrier
        contained := x.val.contained
        toBase := x.val.toBase
        value := T.point }
    have hclass : pointsMap B S hS (underlying B S hS X V).1
        ((toSpaces B S hS X).map f).hom (qv.class B S hS _) = p.image := by
      rw [pointsMap_class]
      refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
        ⟨p.val, ?_, FieldValuedPoint.dominates_refl B S hS _ p.val⟩
      obtain ⟨i, hi⟩ := FieldValuedPoint.dominates_refl B S hS
        (underlying B S hS X U).1
        (FieldValuedPoint.map B S hS (underlying B S hS X V).1
          ((toSpaces B S hS X).map f).hom qv)
      refine ⟨i, ?_⟩
      show (underlying B S hS X U).1.map i.op _ = p.val.value
      rw [hi]
      exact h.point_comp
    exact hclass ▸ (largestOpenZeroSubspace_restrict_iff B S hS X F U σ V f).1 hzero
      (qv.class B S hS _)
  · intro hmem
    set W := largestOpenZeroSubspace B S hS X F U σ
    let A := p.val.siteObject B S hS (underlying B S hS X U).1
    obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points B S hS
      (underlying B S hS X U).2 (isAlgebraicSpace_yoneda B S hS A) W.1 W.2
      (yonedaEquiv.symm p.val.value)).2 (by
        rintro y ⟨z, rfl⟩
        rw [FieldValuedPoint.pointsMap_eq_class B S hS p.val z]
        exact hmem)
    let s : W.1.toFunctor.obj (op A) := g.app (op A) (𝟙 A)
    have hs : W.1.ι.app (op A) s = p.val.value := by
      simpa [s] using congrArg
        (fun k : yoneda.obj A ⟶ (underlying B S hS X U).1 ↦ k.app (op A) (𝟙 A)) hg
    let V := openSubspaceObject B S hS X U W
    let f := openSubspaceInclusion B S hS X U W
    let T : EtaleNeighborhood B S hS X.1 X.2 x :=
      etaleNeighborhoodOfSitePoint B S hS X x V s (by
        show ((inclusion B S hS X).obj U).hom.hom.app (op A) (W.1.ι.app (op A) s) =
          ((inclusion B S hS X).obj U).hom.hom.app (op A) p.val.value
        rw [hs])
    refine ⟨T, { hom := ((toSpaces B S hS X).map f).hom, «over» := rfl, point_comp := hs }, ?_⟩
    show F.obj.map f.op σ = 0
    exact restrict_largestOpenZeroSubspace_eq_zero B S hS X F U σ

/-- **Stacks 04K9.** A section `σ` of an abelian sheaf on the spaces-étale site of an
algebraic space `X`, over an object `U` of that site, has an open subspace `W` of the
algebraic space underlying `U` such that: `σ` vanishes on `W` and `W` contains every open
subspace on which `σ` vanishes; `σ` restricts to zero on an object of the site over `U`
exactly when the image of its points lies in `W`; and the germ of `σ` at a geometric point of
`U` vanishes in the spaces-étale stalk at its image in `X` exactly when that point lies in
`W`. -/
@[stacks 04K9, sga "2 XIV 1.8.2.1" "abelian, spaces"]
theorem exists_largestOpenZeroSubspace
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{v})
    (U : SpacesEtale B S hS X) (σ : F.obj.obj (op U)) :
    ∃ W : {W : Subfunctor (underlying B S hS X U).1 // IsOpenSubspace B S hS W},
      F.obj.map (openSubspaceInclusion B S hS X U W).op σ = 0 ∧
      (∀ W' : {W : Subfunctor (underlying B S hS X U).1 // IsOpenSubspace B S hS W},
        F.obj.map (openSubspaceInclusion B S hS X U W').op σ = 0 → W'.1 ≤ W.1) ∧
      (∀ (V : SpacesEtale B S hS X) (f : V ⟶ U),
        F.obj.map f.op σ = 0 ↔ ImageInOpen B S hS X (openPoints B S hS X U W) f) ∧
      (∀ p : GeometricPoint B S hS (underlying B S hS X U).1,
        (spacesNeighborhoodSections (imageGeometricPoint B S hS X U p)
            (F.obj ⋙ forget AddCommGrpCat.{v})).ιColimitType
          (op (neighborhoodOfGeometricPoint B S hS X U p)) σ =
        (spacesNeighborhoodSections (imageGeometricPoint B S hS X U p)
            (F.obj ⋙ forget AddCommGrpCat.{v})).ιColimitType
          (op (neighborhoodOfGeometricPoint B S hS X U p)) (0 : F.obj.obj (op U)) ↔
          p.image ∈ openPoints B S hS X U W) :=
  ⟨largestOpenZeroSubspace B S hS X F U σ,
    restrict_largestOpenZeroSubspace_eq_zero B S hS X F U σ,
    largestOpenZeroSubspace_maximal B S hS X F U σ,
    largestOpenZeroSubspace_restrict_iff B S hS X F U σ,
    germ_eq_zero_iff_mem_largestOpenZeroSubspace B S hS X F U σ⟩

end SpacesEtale

end AlgebraicGeometry.Space

end
