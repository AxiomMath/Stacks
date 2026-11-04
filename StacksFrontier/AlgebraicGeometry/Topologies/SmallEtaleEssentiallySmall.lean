module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.BaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites

/-!
# Essential smallness of the small étale categories

Sheafification of presheaves on a category `C : Type (u + 1)` with `Category.{u} C` and values in
a `u`-concrete category is not available from the general theory: the presheaf category only has
colimits of size `u + 1`.  Mathlib supplies the missing input in the form of
`CategoryTheory.hasSheafifyEssentiallySmallSite`, which asks for `EssentiallySmall.{u} C`.  The
categories of Stacks 021B are exactly of that shape, since
`AlgebraicGeometry.BigEtaleSite.Scheme` is a full subcategory of `AlgebraicGeometry.Scheme.{u}`,
so this file establishes `EssentiallySmall.{u}` for the two étale ones.

The size cutoff is *essential* and not an artefact: the category of all schemes étale over `S`
is not essentially small, because `∐ i : I, S` is étale over `S` for every index type
`I : Type u`.  What the cutoff buys is a bound on the number of affine opens, and a scheme is
determined by its affine opens: a scheme is the colimit of the diagram of the spectra of the
rings of sections of its affine opens (`AlgebraicGeometry.Scheme.AffineZariskiSite.isColimitCocone`
in Mathlib).  So the whole argument is the following chain.

* Affine schemes étale over `S` form an essentially small category; this is Mathlib's
  `AlgebraicGeometry.essentiallySmall_costructuredArrow_Spec`, which rests on an étale morphism
  being locally of finite type.  An affine object of Mathlib's small étale site
  `AlgebraicGeometry.Scheme.Etale` is isomorphic over `S` to the spectrum of its ring of global
  functions, so the affine objects form an essentially small *property* of that site.
* An object of the small étale site is a colimit of affine objects, over the poset of its affine
  opens.  Mathlib's colimit is a colimit of schemes; it is lifted here to a colimit in
  `AlgebraicGeometry.Scheme.Etale`.
* The shape of that colimit has cardinality below the cutoff, since the arrows of the poset of
  affine opens of a scheme inject into pairs of affine opens and there are fewer than `κ` of
  those.  Hence the size-bounded objects lie in the closure of the affine objects under colimits
  of shapes of cardinality `< κ`, and `CategoryTheory.ObjectProperty.colimitsCardinalClosure` of
  an essentially small property is essentially small.
* The small étale category of Stacks 021B embeds fully faithfully in Mathlib's small étale site,
  with image inside the size-bounded objects, so its skeleton is small.

## Main definitions

* `AlgebraicGeometry.Scheme.Etale.isAffineObj` is the property of an object of Mathlib's small
  étale site that its underlying scheme is affine.
* `AlgebraicGeometry.Scheme.Etale.affineDiagram` and
  `AlgebraicGeometry.Scheme.Etale.affineCocone` are the diagram of affine opens of an object of
  the small étale site and its cocone over that object.
* `AlgebraicGeometry.SmallEtale.toEtaleSite` is the fully faithful functor from the small étale
  category of Stacks 021B to Mathlib's small étale site.

## Main results

* `AlgebraicGeometry.Scheme.Etale.isColimitAffineCocone`: an object of the small étale site is
  the colimit, in the small étale site, of the diagram of affine opens of its underlying scheme.
* `AlgebraicGeometry.Scheme.Etale.essentiallySmall_sizeLT`: for every cardinal `κ ≥ ℵ₀`, the
  objects of the small étale site whose underlying scheme has size `< κ` form an essentially
  small property.
* `AlgebraicGeometry.SmallEtale.essentiallySmall`: **the small étale category of `S` is
  `EssentiallySmall.{u}`.**
* `AlgebraicGeometry.SmallAffineEtale.essentiallySmall`: so is the small affine étale category.
* `AlgebraicGeometry.BigEtaleOver.essentiallySmall`: the big étale category over `S` is
  essentially small as soon as the ambient size-bounded category of schemes is — a slice of an
  essentially small category is essentially small (`CategoryTheory.essentiallySmall_over`).
  Unlike the two small categories, the big one has no finiteness condition on its objects, so
  the argument above does not apply to it.

## Implementation notes

`CategoryTheory.small_skeleton_of_fullyFaithful` is the bridge from a property of objects of an
ambient category to essential smallness of a subcategory: a fully faithful functor induces an
injection of skeleta, and if the image satisfies an essentially small property then the
injection lands in a small set.  It is applied here with the small étale category of Stacks 021B
as source.

`AlgebraicGeometry.Scheme.Etale.affineDiagram` is a lift of Mathlib's diagram of affine opens
along the forgetful functor to schemes rather than a new construction, and
`AlgebraicGeometry.Scheme.Etale.isColimitAffineCocone` is proved by descending to schemes, where
Mathlib's colimit is available; the resulting morphism is a morphism over `S` because two
morphisms out of a colimit that agree on the cocone are equal.

Only the two small categories get `EssentiallySmall` instances here.
`AlgebraicGeometry.BigEtaleOver.essentiallySmall` is a plain theorem: as an instance it would
register a search for essential smallness of a slice in terms of essential smallness of an
ambient category, and the ambient category of a slice of a full subcategory is again of that
form.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty CategoryTheory.Limits Cardinal

universe w v' v u' u

namespace CategoryTheory

/-- If a fully faithful functor sends every object into an essentially small property of objects
of the target, then the isomorphism classes of the source form a small type.  The injection of
skeleta induced by the functor lands in the set of isomorphism classes of a small property. -/
public theorem small_skeleton_of_fullyFaithful {C : Type u} [Category.{v} C] {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) [F.Full] [F.Faithful] (Q : ObjectProperty D)
    [ObjectProperty.EssentiallySmall.{w} Q] (hQ : ∀ X : C, Q (F.obj X)) :
    Small.{w} (Skeleton C) := by
  obtain ⟨Q₀, _, -, hQ₀⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{w} Q
  have key : ∀ x : Skeleton C,
      F.mapSkeleton.obj x ∈ Set.range fun y : Subtype Q₀ ↦ toSkeleton y.1 := by
    intro x
    obtain ⟨X, rfl⟩ : ∃ X, toSkeleton X = x :=
      ⟨(fromSkeleton _).obj x, toSkeleton_fromSkeleton_obj x⟩
    obtain ⟨Y, hY, ⟨e⟩⟩ := hQ₀ _ (hQ X)
    refine ⟨⟨Y, hY⟩, ?_⟩
    rw [Functor.mapSkeleton_obj_toSkeleton]
    exact (congr_toSkeleton_of_iso e).symm
  have : Small.{w} (Set.range fun y : Subtype Q₀ ↦ toSkeleton (C := D) y.1) := small_range _
  exact small_of_injective (f := fun x ↦ (⟨_, key x⟩ :
      Set.range fun y : Subtype Q₀ ↦ toSkeleton y.1))
    fun _ _ h ↦ Functor.mapSkeleton_injective _ (Subtype.ext_iff.mp h)

/-- In a thin category the arrows are determined by their source and target, so there are at most
`#J * #J` of them; below an infinite cardinal bounding the objects, that is again a bound. -/
public theorem hasCardinalLT_arrow_of_isThin {J : Type u} [Category.{u} J] [Quiver.IsThin J]
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (hJ : #J < κ) : HasCardinalLT (Arrow J) κ := by
  rw [hasCardinalLT_iff_cardinal_mk_lt]
  refine lt_of_le_of_lt (Cardinal.mk_le_of_injective
    (f := fun a : Arrow J ↦ (a.left, a.right)) ?_) ?_
  · rintro ⟨_, _, af⟩ ⟨_, _, bf⟩ hab
    cases congrArg (fun p : J × J ↦ p.1) hab
    cases congrArg (fun p : J × J ↦ p.2) hab
    rw [Subsingleton.elim af bf]
  · rw [Cardinal.mk_prod]
    simpa using Cardinal.mul_lt_of_lt hκ hJ hJ

end CategoryTheory

namespace AlgebraicGeometry

namespace Scheme.Etale

variable {S : Scheme.{u}}

/-- The property of an object of the small étale site of `S` that its underlying scheme is
affine.  This is a `def` rather than an `abbrev` so that the essential smallness instance below
is keyed on its name rather than on a lambda. -/
public def isAffineObj (S : Scheme.{u}) : ObjectProperty S.Etale := fun T ↦ IsAffine T.left

/-- Membership in `AlgebraicGeometry.Scheme.Etale.isAffineObj` is affineness of the underlying
scheme. -/
public theorem isAffineObj_iff {T : S.Etale} : isAffineObj S T ↔ IsAffine T.left := Iff.rfl

/-- An affine object of the small étale site of `S` is isomorphic, over `S`, to the spectrum of
its ring of global functions, viewed as an object of Mathlib's small affine étale site. -/
public theorem exists_affineEtale_iso (T : S.Etale) (hT : isAffineObj S T) :
    ∃ A : S.AffineEtale, Nonempty ((AffineEtale.Spec S).obj A ≅ T) :=
  have : IsAffine T.left := hT
  have : Etale T.hom := T.prop
  ⟨AffineEtale.mk (T.left.isoSpec.inv ≫ T.hom),
    ⟨MorphismProperty.Over.isoMk T.left.isoSpec.symm rfl⟩⟩

/-- The affine objects of the small étale site of `S` form an essentially small property: by
Mathlib's `AlgebraicGeometry.essentiallySmall_costructuredArrow_Spec` there are only `u`-small
many affine schemes étale over `S` up to isomorphism. -/
public instance essentiallySmall_isAffineObj :
    ObjectProperty.EssentiallySmall.{u} (isAffineObj S) where
  exists_small_le' := by
    refine ⟨ObjectProperty.ofObj fun x : Skeleton S.AffineEtale ↦
      (AffineEtale.Spec S).obj ((fromSkeleton _).obj x), inferInstance, fun T hT ↦ ?_⟩
    obtain ⟨A, ⟨e⟩⟩ := exists_affineEtale_iso T hT
    exact ⟨_, ObjectProperty.ofObj_apply _ (toSkeleton A),
      ⟨e.symm.trans ((AffineEtale.Spec S).mapIso (fromSkeletonToSkeletonIso A)).symm⟩⟩

/-- Mathlib's diagram of the spectra of the rings of sections of the affine opens of a scheme,
indexed by `AlgebraicGeometry.Scheme.AffineZariskiSite`. -/
public noncomputable abbrev affineOpensFunctor (X : Scheme.{u}) :
    X.AffineZariskiSite ⥤ Scheme.{u} :=
  Scheme.AffineZariskiSite.toOpensFunctor X ⋙ Functor.rightOp X.presheaf ⋙ Scheme.Spec

/-- The canonical maps from the spectra of the rings of sections of the affine opens of `X` are
compatible with any morphism out of `X`. -/
public theorem affineOpensFunctor_map_comp_fromSpec {X Y : Scheme.{u}} (g : X ⟶ Y)
    {U V : X.AffineZariskiSite} (f : U ⟶ V) :
    (affineOpensFunctor X).map f ≫ (V.2.fromSpec ≫ g) = U.2.fromSpec ≫ g :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ g) ((Scheme.AffineZariskiSite.cocone X).w f))

/-- The diagram of affine opens of an object `T` of the small étale site of `S`, as a diagram in
the small étale site: the spectrum of the ring of sections of an affine open is étale over `S`,
being an open subscheme of a scheme étale over `S`. -/
public noncomputable def affineDiagram (T : S.Etale) : T.left.AffineZariskiSite ⥤ S.Etale :=
  have : Etale T.hom := T.prop
  { obj U := MorphismProperty.Over.mk ⊤ (U.2.fromSpec ≫ T.hom) inferInstance
    map {_ _} f := MorphismProperty.Over.homMk ((affineOpensFunctor T.left).map f)
      (affineOpensFunctor_map_comp_fromSpec T.hom f)
    map_id U := MorphismProperty.Over.Hom.ext ((affineOpensFunctor T.left).map_id U)
    map_comp f g := MorphismProperty.Over.Hom.ext ((affineOpensFunctor T.left).map_comp f g) }

/-- Every object of the diagram of affine opens is affine. -/
public instance isAffineObj_affineDiagram_obj (T : S.Etale) (U : T.left.AffineZariskiSite) :
    IsAffine ((affineDiagram T).obj U).left :=
  inferInstanceAs (IsAffine (Spec _))

/-- The cocone of the diagram of affine opens of `T` over `T` itself. -/
public noncomputable def affineCocone (T : S.Etale) : Cocone (affineDiagram T) where
  pt := T
  ι.app U := MorphismProperty.Over.homMk ((Scheme.AffineZariskiSite.cocone T.left).ι.app U) rfl
  ι.naturality {_ _} f := MorphismProperty.Over.Hom.ext
    (((Scheme.AffineZariskiSite.cocone T.left).w f).trans (Category.comp_id _).symm)

/-- The underlying cocone of schemes of a cocone of the diagram of affine opens. -/
public noncomputable def schemeCocone {T : S.Etale} (s : Cocone (affineDiagram T)) :
    Cocone (affineOpensFunctor T.left) where
  pt := s.pt.left
  ι.app U := (s.ι.app U).left
  ι.naturality {_ _} f := congrArg (fun k ↦ k.left) (s.ι.naturality f)

/-- **An object of the small étale site of `S` is the colimit of the diagram of affine opens of
its underlying scheme.**  The colimit of schemes is Mathlib's
`AlgebraicGeometry.Scheme.AffineZariskiSite.isColimitCocone`; the descended morphism is a
morphism over `S` because it agrees with the structure morphism on the cocone. -/
public noncomputable def isColimitAffineCocone (T : S.Etale) : IsColimit (affineCocone T) where
  desc s := MorphismProperty.Over.homMk
    ((Scheme.AffineZariskiSite.isColimitCocone T.left).desc (schemeCocone s))
    ((Scheme.AffineZariskiSite.isColimitCocone T.left).hom_ext fun U ↦
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ s.pt.hom)
            ((Scheme.AffineZariskiSite.isColimitCocone T.left).fac (schemeCocone s) U)).trans
          (MorphismProperty.Over.w (s.ι.app U))))
  fac s U := MorphismProperty.Over.Hom.ext
    ((Scheme.AffineZariskiSite.isColimitCocone T.left).fac (schemeCocone s) U)
  uniq s m h := MorphismProperty.Over.Hom.ext
    ((Scheme.AffineZariskiSite.isColimitCocone T.left).uniq (schemeCocone s) m.left
      fun U ↦ congrArg (fun k ↦ k.left) (h U))

/-- The poset of affine opens of a scheme of size `< κ` has fewer than `κ` arrows. -/
public theorem hasCardinalLT_arrow_affineZariskiSite {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    {X : Scheme.{u}} (hX : X.size < κ) : HasCardinalLT (Arrow X.AffineZariskiSite) κ :=
  hasCardinalLT_arrow_of_isThin hκ (lt_of_le_of_lt X.mk_affineOpens_le_size hX)

/-- An object of the small étale site of `S` whose underlying scheme has size `< κ` lies in the
closure of the affine objects under colimits of shapes of cardinality `< κ`. -/
public theorem sizeLT_le_colimitsCardinalClosure (S : Scheme.{u}) {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ) :
    (fun T : S.Etale ↦ T.left.size < κ) ≤ (isAffineObj S).colimitsCardinalClosure κ := by
  intro T hT
  have := (isAffineObj S).isClosedUnderColimitsOfShape_colimitsCardinalClosure κ
    T.left.AffineZariskiSite (hasCardinalLT_arrow_affineZariskiSite hκ hT)
  exact ((isAffineObj S).colimitsCardinalClosure κ).prop_of_isColimit
    (isColimitAffineCocone T) fun U ↦
      (isAffineObj S).le_colimitsCardinalClosure κ _ (isAffineObj_affineDiagram_obj T U)

/-- The objects of the small étale site of `S` whose underlying scheme has size `< κ` form an
essentially small property, for every infinite cardinal `κ`. -/
public theorem essentiallySmall_sizeLT (S : Scheme.{u}) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) :
    ObjectProperty.EssentiallySmall.{u} (fun T : S.Etale ↦ T.left.size < κ) :=
  ObjectProperty.EssentiallySmall.of_le (sizeLT_le_colimitsCardinalClosure S hκ)

end Scheme.Etale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SmallEtale

/-- The small étale category of `S` in the sense of Stacks 021B sits inside Mathlib's small
étale site of `S`: an object is a scheme below the size cutoff whose structure morphism to `S`
is étale, and the functor forgets the size bound. -/
public def toEtaleSite : SmallEtale B S hS ⥤ S.Etale where
  obj X := MorphismProperty.Over.mk ⊤ (B.inclusion.map X.obj.hom) X.property
  map {_ _} f := MorphismProperty.Over.homMk (B.inclusion.map f.hom.left)
    ((B.inclusion.map_comp _ _).symm.trans
      (congrArg B.inclusion.map (CategoryTheory.Over.w f.hom)))
  map_id _ := MorphismProperty.Over.Hom.ext (B.inclusion.map_id _)
  map_comp _ _ := MorphismProperty.Over.Hom.ext (B.inclusion.map_comp _ _)

/-- The functor to Mathlib's small étale site is faithful, since the inclusion of the
size-bounded category of schemes is. -/
public instance : (toEtaleSite B S hS).Faithful where
  map_injective h :=
    InducedCategory.hom_ext (CategoryTheory.Over.OverMorphism.ext
      (B.inclusion.map_injective (congrArg (fun k ↦ k.left) h)))

/-- The functor to Mathlib's small étale site is full: a morphism of schemes over `S` between
two objects below the size cutoff is a morphism of the size-bounded category. -/
public instance : (toEtaleSite B S hS).Full where
  map_surjective f :=
    ⟨InducedCategory.homMk (CategoryTheory.Over.homMk (InducedCategory.homMk f.left)
      (InducedCategory.hom_ext (MorphismProperty.Over.w f))),
      MorphismProperty.Over.Hom.ext rfl⟩

/-- The underlying scheme of an object of the small étale category of `S` has size below the
cutoff of the ambient big étale site. -/
public theorem size_lt_cutoff (X : SmallEtale B S hS) :
    ((toEtaleSite B S hS).obj X).left.size < B.cutoff :=
  X.obj.left.property

/-- **The small étale category of a scheme is essentially small.**  Its objects are schemes
étale over `S` of size below the cutoff of the ambient big étale site, and such a scheme is a
colimit of fewer than `cutoff` many affine schemes étale over `S`, of which there are only
`u`-small many up to isomorphism. -/
public instance essentiallySmall : EssentiallySmall.{u} (SmallEtale B S hS) :=
  have := Scheme.Etale.essentiallySmall_sizeLT S B.aleph0_lt_cutoff.le
  (essentiallySmall_iff _).2
    ⟨small_skeleton_of_fullyFaithful (toEtaleSite B S hS)
        (fun T : S.Etale ↦ T.left.size < B.cutoff) (size_lt_cutoff B S hS),
      inferInstance⟩

end SmallEtale

namespace SmallAffineEtale

/-- **The small affine étale category of a scheme is essentially small**, being a full
subcategory of the small étale category. -/
public instance essentiallySmall : EssentiallySmall.{u} (SmallAffineEtale B S hS) :=
  essentiallySmall_of_fully_faithful (inclusion B S hS)

end SmallAffineEtale

namespace BigEtaleOver

/-- The big étale category over `S` is essentially small as soon as the ambient size-bounded
category of schemes is, being a slice of it.  Unlike the small étale category, it is not known
to be essentially small outright: its objects carry no étale or finiteness condition. -/
public theorem essentiallySmall [EssentiallySmall.{u} (SchemeBelow B.cutoff)] :
    EssentiallySmall.{u} (BigEtaleOver B S hS) :=
  essentiallySmall_over _

end BigEtaleOver

end AlgebraicGeometry

end
