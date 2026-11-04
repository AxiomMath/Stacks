module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Open subspaces and open sets of points

For an algebraic space `F` over a scheme `S`, sending an open subspace of `F` to the image of
its points is an inclusion-preserving bijection from the open subspaces of `F` onto the open
subsets of the point space `|F|` of Tag 03BU, with the topology of Tag 03BX (part (1) of
Tag 03BZ). This file constructs it as an order isomorphism, together with its inverse.

The subspace attached to a set `W` of points is the subfunctor
`AlgebraicGeometry.Space.openSubspaceOfPoints` whose sections over an object of the site are the
sections of `F` all of whose points lie in `W`. For an open `W` its inclusion is an open
immersion: over each object `A` of the site, the preimage of `W` is cut out by an open subscheme
of `A`.

## Main definitions

* `AlgebraicGeometry.Space.openSubspaceOfPoints`: the subfunctor of `F` cut out by a set of
  points of `F`.
* `AlgebraicGeometry.Space.openSubspacesOrderIso`: the order isomorphism from the open subspaces
  of `F` to the open subsets of `|F|`.

## Main results

* `AlgebraicGeometry.Space.existsUnique_openSubspacesOrderIso`: there is a unique order
  isomorphism from the open subspaces of `F` to the open subsets of `|F|` sending an open
  subspace to the image of its points; `AlgebraicGeometry.Space.openSubspacesOrderIso_apply` is
  its defining equation.
* `AlgebraicGeometry.Space.isOpen_range_pointsMap_of_isOpenImmersion`: the image of the points
  of an open immersion is open.
* `AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints` and
  `AlgebraicGeometry.Space.range_pointsMap_ι_openSubspaceOfPoints`: the subfunctor cut out by an
  open set of points is an open subspace, and its point set is that set; together they are
  `AlgebraicGeometry.Space.exists_isOpenSubspace_range_pointsMap_eq`.
* `AlgebraicGeometry.Space.range_yoneda_map_eq_preimage_openSubspaceOfPoints`: the preimage of
  that subfunctor along a morphism from a representable presheaf is the functor of points of the
  open subscheme cutting out the preimage of the set of points.
* `AlgebraicGeometry.Space.le_of_range_pointsMap_ι_subset`: a subfunctor is contained in an open
  subspace as soon as the image of its points is.
* `AlgebraicGeometry.Space.isIso_of_presheaf_isOpenImmersion_of_presheafSurjective`: a relative
  open immersion of presheaves surjective after every represented base change is an
  isomorphism.

## Implementation notes

The topology on the point sets is `AlgebraicGeometry.Space.pointTopology`, installed as a local
instance in this file.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 02WY](https://stacks.math.columbia.edu/tag/02WY)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open immersions are open on points -/

/-- A morphism of the big fppf category over `S` whose underlying morphism of schemes is an
open immersion has open underlying map of topological spaces. -/
theorem inverseImage_isOpenImmersion_le_isOpenMap :
    (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ≤
      MorphismProperty.inverseImage
        (topologically @IsOpenMap : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) :=
  fun _ _ _ hf ↦ (show _root_.AlgebraicGeometry.IsOpenImmersion _ from hf).base_open.isOpenMap

variable {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An open immersion of presheaves on the big fppf site of `S` is an open map on point sets. -/
theorem isOpenMap_pointsMap_of_isOpenImmersion (f : F ⟶ G)
    (hf : IsOpenImmersion B S hS f) :
    IsOpenMap (pointsMap B S hS F f) :=
  isOpenMap_pointsMap_of_presheafIsOpenMap B S hS f
    (MorphismProperty.relative_monotone
      (inverseImage_isOpenImmersion_le_isOpenMap B S hS) f hf)

/-- The image of the points of an open immersion of presheaves on the big fppf site of `S` is
open. -/
theorem isOpen_range_pointsMap_of_isOpenImmersion (f : F ⟶ G)
    (hf : IsOpenImmersion B S hS f) :
    IsOpen (Set.range (pointsMap B S hS F f)) :=
  (isOpenMap_pointsMap_of_isOpenImmersion B S hS f hf).isOpen_range

/-- The range of an open immersion out of an algebraic space is an open subspace. -/
theorem isOpenSubspace_subfunctorRange (hF : IsAlgebraicSpace B S hS F) {k : F ⟶ G}
    (hk : IsOpenImmersion B S hS k) : IsOpenSubspace B S hS (Subfunctor.range k) := by
  have _ : Mono k := mono_of_presheaf_isOpenImmersion hk
  have hι : inv (Subfunctor.toRange k) ≫ k = (Subfunctor.range k).ι :=
    (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι k).symm
  exact ⟨hF.of_iso (asIso (Subfunctor.toRange k)),
    hι ▸ MorphismProperty.RespectsIso.precomp _ _ _ hk⟩

/-! ### The subspace cut out by a set of points -/

variable (F) in
/-- The subfunctor of `F` cut out by a set `W` of points of `F`: its sections over an object
of the site are the sections of `F` all of whose points lie in `W`. -/
def openSubspaceOfPoints (W : Set (points B S hS F)) : Subfunctor F where
  obj X := {x | Set.range (pointsMap B S hS (yoneda.obj X.unop) (yonedaEquiv.symm x)) ⊆ W}
  map i x hx := by
    refine Set.Subset.trans ?_ hx
    rw [yonedaEquiv_symm_map, pointsMap_comp]
    exact Set.range_comp_subset_range _ _

/-- Membership in the subfunctor cut out by a set of points, unfolded. -/
theorem mem_openSubspaceOfPoints_iff (W : Set (points B S hS F))
    {X : (BigFppfOver B S hS)ᵒᵖ} (x : F.obj X) :
    x ∈ (openSubspaceOfPoints B S hS F W).obj X ↔
      Set.range (pointsMap B S hS (yoneda.obj X.unop) (yonedaEquiv.symm x)) ⊆ W :=
  Iff.rfl

/-- The subspace cut out by a set of points is monotone in that set. -/
theorem openSubspaceOfPoints_mono {s t : Set (points B S hS F)} (hst : s ⊆ t) :
    openSubspaceOfPoints B S hS F s ≤ openSubspaceOfPoints B S hS F t :=
  fun _ _ hx ↦ Set.Subset.trans hx hst

/-- The inverse image of the subfunctor cut out by a set of points is the subfunctor cut out by
the preimage of that set: a section of the source lands in the inverse image exactly when all
of its points are carried into the set. -/
theorem preimage_openSubspaceOfPoints' (f : G ⟶ F) (W : Set (points B S hS F)) :
    (openSubspaceOfPoints B S hS F W).preimage f =
      openSubspaceOfPoints B S hS G (pointsMap B S hS G f ⁻¹' W) := by
  ext T x
  show Set.range (pointsMap B S hS (yoneda.obj T.unop) (yonedaEquiv.symm (f.app T x))) ⊆ W ↔
    Set.range (pointsMap B S hS (yoneda.obj T.unop) (yonedaEquiv.symm x)) ⊆
      pointsMap B S hS G f ⁻¹' W
  rw [← yonedaEquiv_symm_naturality_right, pointsMap_comp, Set.range_comp, Set.image_subset_iff]

/-- The point set of the subspace cut out by a set of points is that set. -/
theorem range_pointsMap_ι_openSubspaceOfPoints (W : Set (points B S hS F)) :
    Set.range (pointsMap B S hS (openSubspaceOfPoints B S hS F W).toFunctor
      (openSubspaceOfPoints B S hS F W).ι) = W := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro y ⟨w, rfl⟩
    obtain ⟨p, rfl⟩ := Quot.exists_rep w
    exact p.value.2 ⟨_, FieldValuedPoint.pointsMap_class_eq_class B S hS
      (FieldValuedPoint.map B S hS _ (openSubspaceOfPoints B S hS F W).ι p)
      (FieldValuedPoint.tautological B S hS _)⟩
  · intro x hx
    obtain ⟨p, rfl⟩ := Quot.exists_rep x
    have hp : p.value ∈ (openSubspaceOfPoints B S hS F W).obj (Opposite.op p.siteObject) := by
      rintro y ⟨w, rfl⟩
      obtain ⟨q, rfl⟩ := Quot.exists_rep w
      rwa [FieldValuedPoint.pointsMap_class_eq_class]
    exact ⟨FieldValuedPoint.class B S hS _
      ({ carrier := p.carrier, field := p.field, contained := p.contained, toBase := p.toBase
         value := ⟨p.value, hp⟩ } :
        FieldValuedPoint B S hS (openSubspaceOfPoints B S hS F W).toFunctor), rfl⟩

/-! ### The sheaf condition -/

/-- The morphism from a representable presheaf determined by a section, in terms of the
component of a morphism out of a representable presheaf. -/
private theorem yonedaEquiv_symm_app_eq {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ F)
    {X : (BigFppfOver B S hS)ᵒᵖ} (f : X.unop ⟶ A) :
    yonedaEquiv.symm (q.app X f) = yoneda.map f ≫ q := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

/-- A point of a represented presheaf lies in the image of the points of a morphism of the
site as soon as its underlying scheme point lies in the image of the underlying morphism of
schemes. -/
theorem mem_range_pointsMap_yoneda_map {A A' : BigFppfOver B S hS} (h : A' ⟶ A)
    (w : points B S hS (yoneda.obj A))
    (hw : pointsToScheme B S hS A w ∈ Set.range ((BigFppfOver.toScheme B S hS).map h)) :
    w ∈ Set.range (pointsMap B S hS (yoneda.obj A') (yoneda.map h)) := by
  obtain ⟨z, hz⟩ := hw
  refine ⟨(pointsEquivScheme B S hS A').symm z, injective_pointsToScheme B S hS A ?_⟩
  rw [pointsToScheme_pointsMap_yoneda]
  exact congrArg ((BigFppfOver.toScheme B S hS).map h)
    ((pointsEquivScheme B S hS A').apply_symm_apply z) |>.trans hz

/-- The subfunctor of an fppf sheaf cut out by a set of points is an fppf sheaf. -/
theorem isSheaf_openSubspaceOfPoints
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (W : Set (points B S hS F)) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (openSubspaceOfPoints B S hS F W).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type,
    Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1 hF)]
  rintro X x hx y ⟨w, rfl⟩
  obtain ⟨A', h, hh, hmem⟩ :=
    BigFppfOver.exists_mem_arrows_mem_range B S hS hx (pointsToScheme B S hS X.unop w)
  obtain ⟨w', rfl⟩ := mem_range_pointsMap_yoneda_map B S hS h w hmem
  have hkey : yoneda.map h ≫ yonedaEquiv.symm x = yonedaEquiv.symm (F.map h.op x) :=
    (yonedaEquiv_symm_map h.op x).symm
  rw [← Function.comp_apply (f := pointsMap B S hS (yoneda.obj X.unop) (yonedaEquiv.symm x)),
    ← pointsMap_comp, hkey]
  exact (hh : F.map h.op x ∈ (openSubspaceOfPoints B S hS F W).obj _) ⟨w', rfl⟩

/-! ### Openness of the subspace cut out by an open set of points -/

/-- The preimage along a morphism from a representable presheaf of the subfunctor cut out by a
set of points is the functor of points of an open subscheme of the representing object: namely
of any open subscheme which, tested at the scheme points of field-valued points, cuts out the
preimage of the set of points. -/
theorem range_yoneda_map_eq_preimage_openSubspaceOfPoints
    (W : Set (points B S hS F)) {A : BigFppfOver B S hS} (q : yoneda.obj A ⟶ F)
    {b : BigFppfOver B S hS} (i : b ⟶ A)
    (V : Set ((BigFppfOver.toScheme B S hS).obj A))
    (hirange : Set.range ((BigFppfOver.toScheme B S hS).map i) = V)
    (hiuniv : ∀ {A' : BigFppfOver B S hS} (g : A' ⟶ A),
      Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆ V → ∃ h : A' ⟶ b, h ≫ i = g)
    (hpoints : ∀ p : FieldValuedPoint B S hS (yoneda.obj A),
      pointsMap B S hS (yoneda.obj A) q (p.class B S hS (yoneda.obj A)) ∈ W ↔
        schemePoint B S hS A p ∈ V) :
    Subfunctor.range (yoneda.map i) = (openSubspaceOfPoints B S hS F W).preimage q := by
  ext X f
  have hmem : ∀ g : X.unop ⟶ A,
      (q.app X g ∈ (openSubspaceOfPoints B S hS F W).obj X ↔
        Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆ V) := by
    intro g
    rw [mem_openSubspaceOfPoints_iff, yonedaEquiv_symm_app_eq]
    constructor
    · rintro hg z ⟨y, rfl⟩
      obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS X.unop y
      have hz : schemePoint B S hS A (FieldValuedPoint.map B S hS (yoneda.obj X.unop)
          (yoneda.map g) p) = (BigFppfOver.toScheme B S hS).map g y := by
        rw [schemePoint_map_yoneda, hp]
      rw [← hz]
      refine (hpoints _).1 (hg ⟨p.class B S hS (yoneda.obj X.unop), ?_⟩)
      rw [pointsMap_comp_apply, pointsMap_class]
    · rintro hg y ⟨w, rfl⟩
      obtain ⟨p, rfl⟩ := Quot.exists_rep w
      rw [pointsMap_comp_apply, pointsMap_class,
        hpoints (FieldValuedPoint.map B S hS (yoneda.obj X.unop) (yoneda.map g) p),
        schemePoint_map_yoneda]
      exact hg ⟨_, rfl⟩
  constructor
  · rintro ⟨g, rfl⟩
    refine (hmem _).2 ?_
    rintro z ⟨y, rfl⟩
    refine hirange ▸ ⟨(BigFppfOver.toScheme B S hS).map g y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    rfl
  · exact fun hf ↦ hiuniv f ((hmem f).1 hf)

/-- The inclusion of the subfunctor cut out by an open set of points is an open immersion. -/
theorem presheaf_isOpenImmersion_ι_openSubspaceOfPoints
    (W : Set (points B S hS F)) (hW : IsOpen W) :
    IsOpenImmersion B S hS (openSubspaceOfPoints B S hS F W).ι := by
  have hRI : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  rw [isOpen_pointTopology_iff] at hW
  refine MorphismProperty.relative.of_exists fun A q ↦ ?_
  obtain ⟨V, hV, hpoints⟩ := hW A q
  obtain ⟨b, i, hi, hirange, hiuniv⟩ := exists_restrict_bigFppfOver A ⟨V, hV⟩
  have hmono : Mono i := inverseImage_isOpenImmersion_le_monomorphisms i hi
  have hmi : Mono (yoneda.map i) := inferInstance
  have hkey : Subfunctor.range (yoneda.map i) =
      (openSubspaceOfPoints B S hS F W).preimage q :=
    range_yoneda_map_eq_preimage_openSubspaceOfPoints B S hS W q i V hirange hiuniv hpoints
  have hsq := Subfunctor.isPullback_fromPreimage (openSubspaceOfPoints B S hS F W) q
  have hiso := Subfunctor.isIso_lift hkey.le hkey.ge
  refine ⟨b, Subfunctor.lift (yoneda.map i) hkey.le ≫
    (openSubspaceOfPoints B S hS F W).fromPreimage q, i, ?_, hi⟩
  refine IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, (openSubspaceOfPoints B S hS F W).fromPreimage_ι q,
      ← Category.assoc, Subfunctor.lift_ι]⟩
    (asIso (Subfunctor.lift (yoneda.map i) hkey.le) ≪≫ hsq.isoPullback) ?_ ?_
  · simp [hsq.isoPullback_hom_fst]
  · simp [hsq.isoPullback_hom_snd]

/-- The subfunctor cut out by an open set of points of an algebraic space is an open
subspace. -/
theorem isOpenSubspace_openSubspaceOfPoints (hF : IsAlgebraicSpace B S hS F)
    (W : Set (points B S hS F)) (hW : IsOpen W) :
    IsOpenSubspace B S hS (openSubspaceOfPoints B S hS F W) :=
  have hι := presheaf_isOpenImmersion_ι_openSubspaceOfPoints B S hS W hW
  ⟨IsAlgebraicSpace.of_relativelyRepresentable
    (isSheaf_openSubspaceOfPoints B S hS hF.isSheaf W) hF hι.rep, hι⟩

/-- Every open subset of the point space of an algebraic space over `S` is the point set of an
open subspace. -/
theorem exists_isOpenSubspace_range_pointsMap_eq (hF : IsAlgebraicSpace B S hS F)
    (W : Set (points B S hS F)) (hW : IsOpen W) :
    ∃ G : Subfunctor F, IsOpenSubspace B S hS G ∧
      Set.range (pointsMap B S hS G.toFunctor G.ι) = W :=
  ⟨openSubspaceOfPoints B S hS F W, isOpenSubspace_openSubspaceOfPoints B S hS hF W hW,
    range_pointsMap_ι_openSubspaceOfPoints B S hS W⟩

/-! ### Comparison of two open subspaces -/

/-- A relative open immersion of presheaves on the big fppf site of `S` which is surjective
after every represented base change is an isomorphism. -/
theorem isIso_of_presheaf_isOpenImmersion_of_presheafSurjective (f : F ⟶ G)
    (hopen : IsOpenImmersion B S hS f)
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsIso f := by
  have hmono : Mono f := mono_of_presheaf_isOpenImmersion hopen
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  refine ⟨(mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app f).mp hmono T), fun x ↦ ?_⟩
  set t : yoneda.obj T.unop ⟶ G := yonedaEquiv.symm x with ht
  have hpb := hopen.rep.isPullback t
  have : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hopen.rep.snd t)) := hopen.property_snd t
  have : Surjective ((BigFppfOver.toScheme B S hS).map (hopen.rep.snd t)) :=
    hsurj.property_snd t
  have : IsIso ((BigFppfOver.toScheme B S hS).map (hopen.rep.snd t)) :=
    (_root_.AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective _).2
      ⟨inferInstance, inferInstance⟩
  have : IsIso (hopen.rep.snd t) := isIso_of_reflects_iso _ (BigFppfOver.toScheme B S hS)
  refine ⟨yonedaEquiv (inv (yoneda.map (hopen.rep.snd t)) ≫ hopen.rep.fst t), ?_⟩
  rw [← yonedaEquiv_comp, Category.assoc, hpb.w, IsIso.inv_hom_id_assoc, ht,
    Equiv.apply_symm_apply]

/-- A subfunctor is contained in an open subspace as soon as its point set is. -/
theorem le_of_range_pointsMap_ι_subset {G H : Subfunctor F}
    (hH : IsOpenSubspace B S hS H)
    (hsub : Set.range (pointsMap B S hS G.toFunctor G.ι) ⊆
      Set.range (pointsMap B S hS H.toFunctor H.ι)) :
    G ≤ H := by
  have hsq : IsPullback (pullback.fst G.ι H.ι) (pullback.snd G.ι H.ι) G.ι H.ι :=
    IsPullback.of_hasPullback G.ι H.ι
  have hfst : IsOpenImmersion B S hS (pullback.fst G.ι H.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq.flip hH.2
  have hpsurj : Function.Surjective
      (pointsMap B S hS (pullback G.ι H.ι) (pullback.fst G.ι H.ι)) := fun z ↦ by
    obtain ⟨x, hx⟩ := hsub ⟨z, rfl⟩
    exact (exists_points_of_isPullback B S hS hsq z x hx.symm).imp fun _ h ↦ h.1
  have : IsIso (pullback.fst G.ι H.ι) :=
    isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS _ hfst
      (presheafSurjective_of_isSurjective B S hS _ hfst.rep hpsurj)
  have hfac : (inv (pullback.fst G.ι H.ι) ≫ pullback.snd G.ι H.ι) ≫ H.ι = G.ι := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  intro T x hx
  set g := inv (pullback.fst G.ι H.ι) ≫ pullback.snd G.ι H.ι
  have hval : (g.app T ⟨x, hx⟩).val = x := congrArg (fun η ↦ η.app T ⟨x, hx⟩) hfac
  exact hval ▸ (g.app T ⟨x, hx⟩).property

/-! ### The correspondence -/

variable (F) in
/-- The open subset of the space of points attached to an open subspace: the image of its
points. -/
def pointsOpensOfOpenSubspace (G : {G : Subfunctor F // IsOpenSubspace B S hS G}) :
    TopologicalSpace.Opens (points B S hS F) :=
  ⟨Set.range (pointsMap B S hS G.1.toFunctor G.1.ι),
    isOpen_range_pointsMap_of_isOpenImmersion B S hS G.1.ι G.2.2⟩

variable (F) in
/-- One open subspace is contained in another exactly when its point set is. -/
theorem pointsOpensOfOpenSubspace_le_iff
    (G H : {G : Subfunctor F // IsOpenSubspace B S hS G}) :
    pointsOpensOfOpenSubspace B S hS F G ≤ pointsOpensOfOpenSubspace B S hS F H ↔ G ≤ H := by
  refine ⟨fun h ↦ le_of_range_pointsMap_ι_subset B S hS H.2 h, fun h ↦ ?_⟩
  rintro _ ⟨w, rfl⟩
  exact ⟨pointsMap B S hS G.1.toFunctor (Subfunctor.homOfLe h) w, by
    rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]⟩

variable (F) in
/-- Every open subset of the space of points is the point set of an open subspace. -/
theorem surjective_pointsOpensOfOpenSubspace (hF : IsAlgebraicSpace B S hS F) :
    Function.Surjective (OrderEmbedding.ofMapLEIff (pointsOpensOfOpenSubspace B S hS F)
      (pointsOpensOfOpenSubspace_le_iff B S hS F)) := fun W ↦
  ⟨⟨openSubspaceOfPoints B S hS F W, isOpenSubspace_openSubspaceOfPoints B S hS hF _ W.2⟩,
    TopologicalSpace.Opens.ext (range_pointsMap_ι_openSubspaceOfPoints B S hS (F := F) W)⟩

variable (F) in
/-- The order isomorphism from the open subspaces of an algebraic space over `S` to the open
subsets of its space of points, sending an open subspace to the image of its point set. -/
@[stacks 03BZ "part (1)"]
noncomputable def openSubspacesOrderIso (hF : IsAlgebraicSpace B S hS F) :
    {G : Subfunctor F // IsOpenSubspace B S hS G} ≃o
      TopologicalSpace.Opens (points B S hS F) :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (pointsOpensOfOpenSubspace B S hS F)
      (pointsOpensOfOpenSubspace_le_iff B S hS F))
    (surjective_pointsOpensOfOpenSubspace B S hS F hF)

variable (F) in
/-- The open subset of points attached to an open subspace is the image of its points. -/
@[simp, stacks 03BZ "part (1)"]
theorem openSubspacesOrderIso_apply (hF : IsAlgebraicSpace B S hS F)
    (G : {G : Subfunctor F // IsOpenSubspace B S hS G}) :
    (openSubspacesOrderIso B S hS F hF G).1 =
      Set.range (pointsMap B S hS G.1.toFunctor G.1.ι) :=
  rfl

variable (F) in
/-- Taking the image of the points of an open subspace is an inclusion-preserving bijection
from the open subspaces of an algebraic space over `S` to the open subsets of its space of
points, and it is the unique order isomorphism doing so. -/
@[stacks 03BZ "part (1)"]
theorem existsUnique_openSubspacesOrderIso (hF : IsAlgebraicSpace B S hS F) :
    ∃! e : {G : Subfunctor F // IsOpenSubspace B S hS G} ≃o
      TopologicalSpace.Opens (points B S hS F),
      ∀ G, (e G).1 = Set.range (pointsMap B S hS G.1.toFunctor G.1.ι) :=
  ⟨openSubspacesOrderIso B S hS F hF, openSubspacesOrderIso_apply B S hS F hF,
    fun _ he' ↦ OrderIso.ext (funext fun G ↦ TopologicalSpace.Opens.ext (he' G))⟩

end AlgebraicGeometry.Space

end
