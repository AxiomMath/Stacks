module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.LocalFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.SmoothAtFiber.Locality
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.StalkCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Syntomic

/-!
# Smooth morphisms of algebraic spaces, and the smooth locus

A smooth morphism of schemes is syntomic — flat and locally of finite presentation with local
complete intersection fibres — by Stacks 01VD. Smoothness and syntomicity of a morphism of
algebraic spaces over a scheme `S` are both defined by testing the corresponding property of
schemes on every commuting square of étale charts, so the implication between them transfers
chartwise.

This file also constructs the *smooth locus* of a morphism of algebraic spaces: the largest
open subspace of its source on which it is smooth. It is the supremum, in the complete
lattice of subfunctors, of the open subspaces on which the morphism is smooth, and the work
is to see that this supremum is itself open and that the morphism is still smooth on it.
Forming it commutes with base change along a morphism which is flat and locally of finite
presentation, and along an arbitrary flat morphism when the morphism itself is locally of
finite presentation; together with the three defining properties these are **Stacks 0DZI**.

## Main definitions

* `AlgebraicGeometry.Space.maximalSmoothOpen` is the smooth locus.

## Main results

* `AlgebraicGeometry.Space.isSyntomic_of_isSmooth` is **Stacks 06CP**.
* `AlgebraicGeometry.Space.isOpen_setOf_isSmoothAt`: the set of points at which a morphism of
  algebraic spaces is smooth is open in the point topology.
* `AlgebraicGeometry.Space.isOpenSubspace_maximalSmoothOpen`,
  `AlgebraicGeometry.Space.isSmooth_maximalSmoothOpen` and
  `AlgebraicGeometry.Space.le_maximalSmoothOpen` are the three defining properties of the
  smooth locus: it is an open subspace, the morphism restricted to it is smooth, and it
  contains every open subspace with that property.
* `AlgebraicGeometry.Space.maximalSmoothOpen_eq_preimage_of_isFlat_isLocallyOfFinitePresentation`
  and
  `AlgebraicGeometry.Space.maximalSmoothOpen_eq_preimage_of_isLocallyOfFinitePresentation_isFlat`
  are the two base-change clauses of Stacks 0DZI.
* `AlgebraicGeometry.smoothAt_iff_hasRepresentativeWithProperty`: for a morphism of schemes,
  smoothness at a point is the germ condition of Stacks 04R6 induced by smoothness.
* `AlgebraicGeometry.smoothAt_iff_smoothAt_of_isPullback` is **Stacks 02V4** read at a point.

## Implementation notes

Nothing in Stacks 06CP needs the source or the target to be an algebraic space: the statement
is about an arbitrary morphism of presheaves on the big fppf site of `S`, since
`AlgebraicGeometry.Space.IsSmooth` and `AlgebraicGeometry.Space.IsSyntomic` are both
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` at a property of scheme morphisms and the
quantifier is the same on both sides. The algebraic-space axioms enter only where a chart is
produced, which this implication never does.

Likewise `AlgebraicGeometry.Space.maximalSmoothOpen` is defined, and
`AlgebraicGeometry.Space.le_maximalSmoothOpen` proved, for an arbitrary morphism of
presheaves; algebraicity is a hypothesis only of the two statements that need it, where the
order isomorphism of Stacks 03BZ between the open subspaces of an algebraic space and the
open subsets of its point space is used to see that the supremum is open.

That the morphism is smooth on the supremum is the pointwise criterion of Stacks 03ZF
(`AlgebraicGeometry.Space.isSmooth_tfae`, condition (2)) applied on the open subspace
corresponding to the open set of points at which the morphism is smooth; the two orderings
agree because an open subspace on which the morphism is smooth has all its points in that
set, and conversely an open subspace witnessing smoothness at a point of the supremum can be
intersected with the supremum, which is
`CategoryTheory.Subfunctor.preimage` along the inclusion.

The subspaces are Mathlib's `CategoryTheory.Subfunctor`, so the supremum is the one of that
complete lattice and no choice is involved in forming it.

The two base-change clauses of Stacks 0DZI are stated for an arbitrary cartesian square of
algebraic spaces rather than for the chosen fibre product, and are split exactly as the source
splits them. The containment of the inverse image of the smooth locus in the smooth locus of
the base change needs neither hypothesis: the inverse image is an open subspace and the
restriction of the base change to it is a base change of the restriction to the smooth locus,
so smoothness transfers by Stacks 03ZE. The reverse containment is where the hypotheses enter.
It is tested on points through Stacks 03IE, and a point of the smooth locus of the base change
is carried to a point of smoothness of the original morphism by passing to compatible
surjective étale charts of the square (`AlgebraicGeometry.Space.exists_compatible_etale_charts`)
and a field-valued point of the chart of the fibre product, exactly as for the quasi-finite
locus of Stacks 0ABM. Smoothness of morphisms of schemes being étale local on the source and
target (Stacks 04R3), smoothness at a point is the induced germ condition read in any one
pointed chart (Stacks 04NC), which turns each side into smoothness of a morphism of schemes at
corresponding points of a cartesian square of schemes. That is **Stacks 02V4**,
`AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_preimage_of_isPullback`, read at a point.

Stacks 02V4 needs the morphism of schemes to be locally of finite presentation. In the first
clause the chart of the original morphism need not be, and the extra work is to produce an open
of that chart which is: the smooth open neighbourhood of the point upstairs maps to the chart by
a flat morphism locally of finite presentation, hence an open one, and local finite presentation
descends along it by Stacks 02KL. Restricting the cartesian square of charts to that open puts
Stacks 02V4 back in force, and smoothness at a point is unaffected by restricting the source
along an open immersion.

## References

* [Stacks Project, Tag 02KL](https://stacks.math.columbia.edu/tag/02KL)
* [Stacks Project, Tag 02V4](https://stacks.math.columbia.edu/tag/02V4)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 04R6](https://stacks.math.columbia.edu/tag/04R6)
* [Stacks Project, Tag 04RF](https://stacks.math.columbia.edu/tag/04RF)
* [Stacks Project, Tag 06CP](https://stacks.math.columbia.edu/tag/06CP)
* [Stacks Project, Tag 0DZI](https://stacks.math.columbia.edu/tag/0DZI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Smoothness at a point of a scheme -/

/-- **Smoothness at a point is the germ condition induced by smoothness.** A morphism of
schemes is smooth at a point of its source exactly when the germ it defines there has a smooth
representative, which is the property of Stacks 04R6 associated with smoothness.

Both directions restrict along an open neighbourhood: a neighbourhood witnessing smoothness is
the source of a representative, and conversely a smooth representative agrees with the morphism
on a common open neighbourhood of the point, on which the morphism is then smooth. -/
theorem smoothAt_iff_hasRepresentativeWithProperty {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    InfinitesimalLifting.SmoothAt f x ↔
      MorphismOfGerms.HasRepresentativeWithProperty
        (@Smooth.{u} : MorphismProperty Scheme.{u}) (MorphismOfGerms.ofSchemeHom f x) := by
  rw [InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp]
  constructor
  · rintro ⟨U, hxU, hU⟩
    exact ⟨{ source := U, mem_source := hxU, hom := U.ι ≫ f, map_point := rfl },
      MorphismOfGerms.mk_eq_mk_iff.mpr ⟨U, hxU, le_rfl, le_top, by simp⟩, hU⟩
  · rintro ⟨r, hr, hP⟩
    obtain ⟨W, hxW, hWr, hWtop, heq⟩ : r.AgreeNear
        ({ source := ⊤, mem_source := by simp, hom := X.topIso.hom ≫ f,
            map_point := rfl } : MorphismOfGerms.Representative ⟨X, x⟩ ⟨Y, f x⟩) :=
      MorphismOfGerms.mk_eq_mk_iff.mp hr
    refine ⟨W, hxW, ?_⟩
    have hrestrict : W.ι ≫ f = X.homOfLE hWr ≫ r.hom := by
      rw [heq, ← Category.assoc]
      exact (congrArg (fun k => k ≫ f) (by simp : X.homOfLE hWtop ≫ X.topIso.hom = W.ι)).symm
    rw [hrestrict]
    exact MorphismProperty.comp_mem (W := @Smooth) _ _ inferInstance hP

/-- **Stacks 02V4 at a point.** For a cartesian square of schemes whose right-hand morphism `f`
is locally of finite presentation, and with `f` or the base morphism `g` flat, the base change
`f'` is smooth at a point of its source exactly when `f` is smooth at the image of that point.

Smoothness at a point of a morphism locally of finite presentation is membership of
`AlgebraicGeometry.Scheme.Hom.smoothLocus`, and
`AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_preimage_of_isPullback` identifies the two loci. -/
@[ega "IV 17.7.1" "(ii), special case",
  ega "IV 17.7.2" "more general",
  ega "IV 17.7.4" "Clause (v), special case",
  ega "IV 6.8.2" "smoothness at a point",
  sga "1 II 4.13" "special case",
  sga "3 VIB 3.10" "(ii) ⇒ (i), special case",
  sga "3 XIX 2.1" "more general"]
theorem smoothAt_iff_smoothAt_of_isPullback {X Y Y' X' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} [LocallyOfFinitePresentation f] (sq : IsPullback g' f' f g)
    (hflat : Flat f ∨ Flat g) (x' : X') :
    InfinitesimalLifting.SmoothAt f' x' ↔ InfinitesimalLifting.SmoothAt f (g' x') := by
  have : LocallyOfFinitePresentation f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
  change Stacks.SmoothAtJacobian.Condition1 f' x' ↔
    Stacks.SmoothAtJacobian.Condition1 f (g' x')
  rw [Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus f' x',
    Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus f (g' x'),
    Scheme.Hom.smoothLocus_eq_preimage_of_isPullback sq hflat]
  exact Iff.rfl

/-- Smoothness of a morphism at a point of the image of an open immersion, from smoothness of
the composite at the corresponding point of the source of that immersion. -/
private theorem smoothAt_of_smoothAt_comp {X' X Y : Scheme.{u}} (i : X' ⟶ X)
    [IsOpenImmersion i] (f : X ⟶ Y) (x' : X')
    (h : InfinitesimalLifting.SmoothAt (i ≫ f) x') :
    InfinitesimalLifting.SmoothAt f (i x') := by
  obtain ⟨U, hxU, hU⟩ :=
    (InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp (i ≫ f) x').mp h
  have hs : Smooth ((U.ι ≫ i) ≫ f) := by rwa [Category.assoc]
  exact InfinitesimalLifting.smoothAt_of_smooth_comp (U.ι ≫ i) f hs ⟨x', hxU⟩

/-- **A point of smoothness of a flat, locally finitely presented base change lies over an open
on which the morphism is locally of finite presentation.** For a cartesian square of schemes
whose base morphism `g` is flat and locally of finite presentation, a point at which the base
change `f'` is smooth has an open neighbourhood `W` of its own on which `f'` is smooth; the
image of `W` in `X` is open, because `W ⟶ X` is flat and locally of finite presentation, and
`f` is locally of finite presentation on it by descent along that morphism, Stacks 02KL. -/
private theorem exists_opens_locallyOfFinitePresentation_of_smoothAt
    {X Y Y' X' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) [Flat g] [LocallyOfFinitePresentation g]
    (x' : X') (hx' : InfinitesimalLifting.SmoothAt f' x') :
    ∃ I : X.Opens, g' x' ∈ I ∧ LocallyOfFinitePresentation (I.ι ≫ f) := by
  obtain ⟨W, hxW, hW⟩ :=
    (InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp f' x').mp hx'
  have : Flat g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip inferInstance
  have : LocallyOfFinitePresentation g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip inferInstance
  set h : W.toScheme ⟶ X := W.ι ≫ g' with hhdef
  have : Flat h := by rw [hhdef]; infer_instance
  have : LocallyOfFinitePresentation h := by rw [hhdef]; infer_instance
  have hopen : IsOpen (Set.range h.base) := by
    simpa using h.isOpenMap Set.univ isOpen_univ
  set I : X.Opens := ⟨Set.range h.base, hopen⟩
  refine ⟨I, ⟨⟨x', hxW⟩, rfl⟩, ?_⟩
  have hIsurj : Surjective (h ∣_ I) := by
    refine (surjective_iff (h ∣_ I)).2 fun y ↦ ?_
    obtain ⟨w, hw⟩ := y.2
    have hwI : h w ∈ I := by rw [hw]; exact y.2
    exact ⟨⟨w, hwI⟩, Subtype.ext ((morphismRestrict_base_coe h I ⟨w, hwI⟩).trans hw)⟩
  have : Flat (h ∣_ I) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict h I).flip inferInstance
  have : LocallyOfFinitePresentation (h ∣_ I) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict h I).flip inferInstance
  have htriangle : h ≫ f = (W.ι ≫ f') ≫ g := by
    rw [hhdef, Category.assoc, Category.assoc, sq.w]
  have : LocallyOfFinitePresentation (h ≫ f) := by
    rw [htriangle]
    have : Smooth (W.ι ≫ f') := hW
    infer_instance
  have : LocallyOfFinitePresentation ((h ∣_ I) ≫ I.ι ≫ f) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  exact locallyOfFinitePresentation_of_comp_of_fppf (h ∣_ I) (I.ι ≫ f)

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}


/-! ### The smooth locus -/

section SmoothLocus

attribute [local instance] pointTopology

/-- The *smooth locus* of a morphism of presheaves on the big fppf site of `S`: the union of
the open subspaces of its source on which it is smooth.

For a morphism of algebraic spaces this is an open subspace on which the morphism is smooth,
and it is the largest such — see `AlgebraicGeometry.Space.isOpenSubspace_maximalSmoothOpen`,
`AlgebraicGeometry.Space.isSmooth_maximalSmoothOpen` and
`AlgebraicGeometry.Space.le_maximalSmoothOpen`. -/
def maximalSmoothOpen (f : X ⟶ Y) : Subfunctor X :=
  sSup {U : Subfunctor X | IsOpenSubspace B S hS U ∧ IsSmooth B S hS (U.ι ≫ f)}

/-- **Stacks 0DZI, maximality.** Every open subspace on which `f` is smooth is contained in the
smooth locus: it is a member of the family the smooth locus is the supremum of. -/
@[stacks 0DZI "maximality of the smooth locus"]
theorem le_maximalSmoothOpen (f : X ⟶ Y) {U : Subfunctor X}
    (hU : IsOpenSubspace B S hS U) (hUf : IsSmooth B S hS (U.ι ≫ f)) :
    U ≤ maximalSmoothOpen B S hS f := le_sSup ⟨hU, hUf⟩

/-- Smoothness of a morphism of presheaves transports along an isomorphism of its source:
precomposing a chart of the source with the isomorphism turns a square for the one morphism
into a square for the other. -/
private theorem isSmooth_of_iso_source {V V' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : V' ≅ V) (f : V ⟶ Y) (g : V' ⟶ Y) (hg : e.hom ≫ f = g)
    (hf : IsSmooth B S hS f) :
    IsSmooth B S hS g := by
  subst hg
  intro U Z a b h ha hb hs
  exact hf U Z (a ≫ e.hom) b h (MorphismProperty.RespectsIso.postcomp _ e.hom a ha) hb
    (by simpa only [Category.assoc] using hs)

/-- The inclusion of the preimage of a subfunctor along a second subfunctor's inclusion,
composed with that second inclusion, lands in the first subfunctor. -/
private theorem range_preimage_ι_comp_ι_le {C : Type*} [Category C] {F : C ⥤ Type u}
    (V W : Subfunctor F) :
    Subfunctor.range ((V.preimage W.ι).ι ≫ W.ι) ≤ V := by
  rintro T x ⟨y, rfl⟩
  exact y.property

/-- The inclusion of a subfunctor contained in a second lands in the preimage of the first
along the second's inclusion. -/
private theorem range_homOfLe_le_preimage {C : Type*} [Category C] {F : C ⥤ Type u}
    {V W : Subfunctor F} (hVW : V ≤ W) :
    Subfunctor.range (Subfunctor.homOfLe hVW) ≤ V.preimage W.ι := by
  rintro T z ⟨v, rfl⟩
  exact v.property

/-- A subfunctor contained in another is isomorphic to its preimage along that other's
inclusion: the two lifts of the inclusions are mutually inverse. -/
private def preimageIsoOfLE {C : Type*} [Category C] {F : C ⥤ Type u}
    (V W : Subfunctor F) (hVW : V ≤ W) :
    V.toFunctor ≅ (V.preimage W.ι).toFunctor where
  hom := Subfunctor.lift _ (range_homOfLe_le_preimage hVW)
  inv := Subfunctor.lift _ (range_preimage_ι_comp_ι_le V W)
  hom_inv_id := by
    refine (cancel_mono V.ι).1 ?_
    rw [Category.assoc, Subfunctor.lift_ι, ← Category.assoc, Subfunctor.lift_ι,
      Subfunctor.homOfLe_ι, Category.id_comp]
  inv_hom_id := by
    ext T x
    exact Subtype.ext rfl

/-- The inverse of `AlgebraicGeometry.Space.preimageIsoOfLE` identifies the inclusion of the
smaller subfunctor with the composite of the two inclusions. -/
private theorem preimageIsoOfLE_inv_ι {C : Type*} [Category C] {F : C ⥤ Type u}
    (V W : Subfunctor F) (hVW : V ≤ W) :
    (preimageIsoOfLE V W hVW).inv ≫ V.ι = (V.preimage W.ι).ι ≫ W.ι :=
  Subfunctor.lift_ι _ (range_preimage_ι_comp_ι_le V W)

/-- The pullback square of a subfunctor along a morphism, as a square of algebraic spaces. -/
private theorem isPullback_homMk_preimage {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X' ⟶ X) (V : Subfunctor X) (hX' : IsAlgebraicSpace B S hS X')
    (hX : IsAlgebraicSpace B S hS X) (hV : IsAlgebraicSpace B S hS V.toFunctor)
    (hP : IsAlgebraicSpace B S hS (V.preimage f).toFunctor) :
    IsPullback
      (ObjectProperty.homMk (V.fromPreimage f) :
        (⟨(V.preimage f).toFunctor, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨V.toFunctor, hV⟩)
      (ObjectProperty.homMk (V.preimage f).ι : _ ⟶ ⟨X', hX'⟩)
      (ObjectProperty.homMk V.ι : _ ⟶ ⟨X, hX⟩) (ObjectProperty.homMk f) :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS G))
    (Subfunctor.isPullback_preimage f V)

/-- The set of points of the source at which a morphism of algebraic spaces over `S` is
smooth is open: by definition of
`AlgebraicGeometry.Space.IsSmoothAt` it is the union of the point sets of the open subspaces
on which the morphism is smooth, and each of those is open by Stacks 03BZ. -/
theorem isOpen_setOf_isSmoothAt (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    IsOpen {x : points B S hS X | IsSmoothAt B S hS f x} := by
  have hEq : {x : points B S hS X | IsSmoothAt B S hS f x} =
      ⋃ V : {V : Subfunctor X //
          IsOpenSubspace B S hS V ∧ IsSmooth B S hS (V.ι ≫ f)},
        Set.range (pointsMap B S hS V.1.toFunctor V.1.ι) := by
    ext x
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨V, hV, p, hp, hVf⟩ := hx
      exact Set.mem_iUnion.mpr ⟨⟨V, hV, hVf⟩, ⟨p, hp⟩⟩
    · obtain ⟨V, p, hp⟩ := Set.mem_iUnion.mp hx
      exact ⟨V.1, V.2.1, p, hp, V.2.2⟩
  rw [hEq]
  refine isOpen_iUnion fun V ↦ ?_
  rw [← openSubspacesOrderIso_apply B S hS X hX ⟨V.1, V.2.1⟩]
  exact (openSubspacesOrderIso B S hS X hX ⟨V.1, V.2.1⟩).2

/-- The smooth locus of a morphism of algebraic spaces over `S` is an open subspace on which
the morphism is smooth.

The open subspace corresponding under Stacks 03BZ to the open set of points at which `f` is
smooth contains every open subspace on which `f` is smooth, hence contains the smooth locus;
and it is itself one of them, by the pointwise criterion of Stacks 03ZF: a point of it is a
point at which `f` is smooth, so some open subspace `V` witnesses that, and `V` meets the
supremum in an open subspace of it through which the restriction is still smooth. So the two
coincide. -/
private theorem isOpenSubspace_and_isSmooth_maximalSmoothOpen
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsOpenSubspace B S hS (maximalSmoothOpen B S hS f) ∧
      IsSmooth B S hS ((maximalSmoothOpen B S hS f).ι ≫ f) := by
  obtain ⟨W, hWopen, hWrange⟩ := exists_isOpenSubspace_range_pointsMap_eq B S hS hX
    {x | IsSmoothAt B S hS f x} (isOpen_setOf_isSmoothAt B S hS hX f)
  -- Every open subspace on which `f` is smooth is contained in `W`.
  have leW : ∀ V : Subfunctor X, IsOpenSubspace B S hS V →
      IsSmooth B S hS (V.ι ≫ f) → V ≤ W := by
    intro V hV hVsm
    refine le_of_range_pointsMap_ι_subset B S hS hWopen ?_
    rw [hWrange]
    rintro x ⟨p, rfl⟩
    exact ⟨V, hV, p, rfl, hVsm⟩
  -- `f` is smooth on `W`, by the pointwise criterion of Stacks 03ZF.
  have hWsm : IsSmooth B S hS (W.ι ≫ f) := by
    refine ((isSmooth_tfae B S hS hWopen.1 hY (W.ι ≫ f)).out 2 1).mp fun xW ↦ ?_
    have hxT : IsSmoothAt B S hS f (pointsMap B S hS W.toFunctor W.ι xW) :=
      hWrange.subset (Set.mem_range.mpr ⟨xW, rfl⟩)
    obtain ⟨V, hV, pV, hpV, hVsm⟩ := hxT
    have hVW : V ≤ W := leW V hV hVsm
    have hV' : IsOpenSubspace B S hS (V.preimage W.ι) :=
      isOpenSubspace_preimage B S hS W.ι V hX hWopen.1 hV
    -- `V ∩ W`, as an open subspace of `W`, carries a point over `xW` and the restriction of
    -- `f` to it is smooth, being the restriction to `V` up to the isomorphism `V ≅ V ∩ W`.
    have hinv := preimageIsoOfLE_inv_ι V W hVW
    have hV'sm : IsSmooth B S hS ((V.preimage W.ι).ι ≫ W.ι ≫ f) :=
      isSmooth_of_iso_source B S hS (preimageIsoOfLE V W hVW).symm (V.ι ≫ f) _
        (by rw [Iso.symm_hom, ← Category.assoc, hinv, Category.assoc]) hVsm
    obtain ⟨pV', -, hpW⟩ := exists_point_of_isPullback B S hS
      (isPullback_homMk_preimage B S hS W.ι V hWopen.1 hX hV.1 hV'.1) pV xW hpV
    exact ⟨V.preimage W.ι, hV', pV', hpW, hV'sm⟩
  have heq : maximalSmoothOpen B S hS f = W :=
    le_antisymm (sSup_le fun V hV ↦ leW V hV.1 hV.2)
      (le_maximalSmoothOpen B S hS f hWopen hWsm)
  rw [heq]
  exact ⟨hWopen, hWsm⟩

/-- **Stacks 0DZI, openness.** The smooth locus of a morphism of algebraic spaces over `S` is
an open subspace. -/
@[stacks 0DZI "the smooth locus is an open subspace"]
theorem isOpenSubspace_maximalSmoothOpen (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsOpenSubspace B S hS (maximalSmoothOpen B S hS f) :=
  (isOpenSubspace_and_isSmooth_maximalSmoothOpen B S hS hX hY f).1

/-- **Stacks 0DZI, smoothness on the open.** A morphism of algebraic spaces over `S` is smooth
on its smooth locus. -/
@[stacks 0DZI "the morphism is smooth on its smooth locus"]
theorem isSmooth_maximalSmoothOpen (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsSmooth B S hS ((maximalSmoothOpen B S hS f).ι ≫ f) :=
  (isOpenSubspace_and_isSmooth_maximalSmoothOpen B S hS hX hY f).2

end SmoothLocus

/-! ### The smooth locus under base change -/

section SmoothLocusBaseChange

/-- Smoothness of a morphism of algebraic spaces over `S` at a point of its source is the
pointed-chart condition of Stacks 04NC for the germ property induced by smoothness of morphisms
of schemes.

The two sides are the same existential statement read with the point condition inside or
outside the witnessing open subspace: part (2) of Stacks 04RF turns the chart condition into an
open neighbourhood on which the morphism is smooth, which is
`AlgebraicGeometry.Space.IsSmoothAt`. -/
theorem isSmoothAt_iff_holdsOnEveryEtaleChartAtPoint
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X) :
    IsSmoothAt B S hS f x ↔
      HoldsOnEveryEtaleChartAtPoint B S hS
        (MorphismOfGerms.HasRepresentativeWithProperty
          (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})) f x := by
  rw [holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
    Smooth.isEtaleLocalOnSourceAndTarget hX hY f x]
  constructor
  · rintro ⟨U, hU, y, hy, hsm⟩
    exact ⟨U, hU, ⟨y, hy⟩, hsm⟩
  · rintro ⟨U, hU, ⟨y, hy⟩, hsm⟩
    exact ⟨U, hU, y, hy, hsm⟩

variable {X₁ X₀ Y₁ Y₀ : AlgebraicSpaces B S hS} {g' : X₁ ⟶ X₀} {f' : X₁ ⟶ Y₁} {f : X₀ ⟶ Y₀}
    {g : Y₁ ⟶ Y₀}

/-- A morphism into a pullback whose first projection is `h` gives a commuting square over the
second leg of the cospan. -/
private theorem comp_eq_snd_comp_of_comp_fst_eq {C : Type*} [Category C] [HasPullbacks C]
    {A P Q R : C} (v : Q ⟶ R) (f : P ⟶ R) (a : A ⟶ pullback v f) (h : A ⟶ Q)
    (hap : a ≫ pullback.fst v f = h) : h ≫ v = (a ≫ pullback.snd v f) ≫ f := by
  rw [← hap, Category.assoc, Category.assoc, pullback.condition]

/-- **Smoothness at a point descends from a base change.** For a cartesian square of algebraic
spaces over `S` in which either `f` is locally of finite presentation and one of `f`, `g` is
flat, or `g` is both flat and locally of finite presentation, a point at which the base change
`f'` is smooth lies over a point at which `f` is smooth.

Compatible surjective étale charts of the square put the two morphisms into a cartesian square
of morphisms of schemes, and a field-valued point of the chart of the fibre product makes both
squares into pointed charts whose selected scheme points correspond. Smoothness at a point is
read off any one pointed chart, which reduces the statement to Stacks 02V4 for schemes — in the
second case after restricting the square of charts to an open on which the chart of `f` is
locally of finite presentation. -/
private theorem isSmoothAt_of_isSmoothAt_of_isPullback_of_flat_lfp (sq : IsPullback g' f' f g)
    (hyp : (IsLocallyOfFinitePresentation B S hS f.hom ∧
        (IsFlat B S hS f.hom ∨ IsFlat B S hS g.hom)) ∨
      (IsFlat B S hS g.hom ∧ IsLocallyOfFinitePresentation B S hS g.hom))
    (x' : points B S hS X₁.1) (hx' : IsSmoothAt B S hS f'.hom x') :
    IsSmoothAt B S hS f.hom (pointsMap B S hS X₁.1 g'.hom x') := by
  let T := BigFppfOver.toScheme B S hS
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition
  have hQbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T) (F := yoneda)
  have hQcomp := MorphismProperty.relative_isStableUnderComposition
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T) (F := yoneda)
  have hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget
      (MorphismOfGerms.HasRepresentativeWithProperty
        (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})) :=
    MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget _
      Smooth.isEtaleLocalOnSourceAndTarget
  obtain ⟨U, V, U', V', p, q, pU, pV', v, a, b, c, hcharts, hap, hbq, hcX, hcY,
      hvSurj, hvEtale, haSurj, haEtale, hbSurj, hbEtale, hcSurj, hcEtale⟩ :=
    exists_compatible_etale_charts B S hS f g
  -- the comparison of the given cartesian square with the chosen fibre product
  let eAs : X₁ ≅ AlgebraicSpaces.fiberProduct B S hS f g :=
    sq.isoIsPullback _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS f g)
  let e : X₁.1 ≅ pullback f.hom g.hom :=
    { hom := eAs.hom.hom
      inv := eAs.inv.hom
      hom_inv_id := congrArg (fun k => k.hom) eAs.hom_inv_id
      inv_hom_id := congrArg (fun k => k.hom) eAs.inv_hom_id }
  have heFst : e.hom ≫ pullback.fst f.hom g.hom = g'.hom :=
    congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_fst _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  have heSnd : e.hom ≫ pullback.snd f.hom g.hom = f'.hom :=
    congrArg (fun k => k.hom) (IsPullback.isoIsPullback_hom_snd _ _ sq
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f g))
  have heInvSnd : e.inv ≫ f'.hom = pullback.snd f.hom g.hom := by
    rw [← heSnd, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  -- étaleness of the chart morphisms into the two sources
  have hSndFEtale := hQbc.of_isPullback (IsPullback.of_hasPullback v f.hom) hvEtale
  have hSndGEtale := hQbc.of_isPullback (IsPullback.of_hasPullback v g.hom) hvEtale
  have hAEtale := MorphismProperty.comp_mem _ a (pullback.snd v f.hom) haEtale hSndFEtale
  have hBEtale := MorphismProperty.comp_mem _ b (pullback.snd v g.hom) hbEtale hSndGEtale
  have hcXEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf (c ≫ e.inv) :=
    have _ : IsIso e.inv := ⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩
    MorphismProperty.RespectsIso.postcomp _ e.inv c hcEtale
  have hcommF := comp_eq_snd_comp_of_comp_fst_eq v f.hom a _ hap
  have hcommG := comp_eq_snd_comp_of_comp_fst_eq v g.hom b _ hbq
  have hcommF' : yoneda.map pV' ≫ (b ≫ pullback.snd v g.hom) = (c ≫ e.inv) ≫ f'.hom := by
    calc yoneda.map pV' ≫ (b ≫ pullback.snd v g.hom) = c ≫ pullback.snd f.hom g.hom := by
          simpa only [Category.assoc] using hcY.symm
      _ = (c ≫ e.inv) ≫ f'.hom := by
          rw [← heInvSnd]
          simp only [Category.assoc]
  -- a field-valued representative of `x'` on the chart `U'` of the fibre product
  have hPull : IsAlgebraicSpace B S hS (pullback f.hom g.hom) :=
    isAlgebraicSpace_pullback B S hS f.hom g.hom X₀.property Y₁.property Y₀.property
  obtain ⟨z, hz⟩ :=
    (surjective_iff_surjective_pointsMap B S hS (pullback f.hom g.hom) hPull U' c).mp hcSurj
      (pointsMap B S hS X₁.1 e.hom x')
  obtain ⟨r, rfl⟩ := Quot.exists_rep z
  have hz' : pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U')) =
      pointsMap B S hS X₁.1 e.hom x' := hz
  -- the two pointed charts
  let chartF : EtaleChartAtPoint B S hS f.hom (pointsMap B S hS X₁.1 g'.hom x') :=
    { U := U
      V := V
      a := a ≫ pullback.snd v f.hom
      b := v
      h := p
      a_etale := hAEtale
      b_etale := hvEtale
      comm := hcommF
      representative := FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        have h₁ : pointsMap B S hS (yoneda.obj U) (a ≫ pullback.snd v f.hom)
            ((FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r).class B S hS
              (yoneda.obj U)) =
            pointsMap B S hS (yoneda.obj U') (yoneda.map pU ≫ a ≫ pullback.snd v f.hom)
              (r.class B S hS (yoneda.obj U')) := rfl
        have h₂ : pointsMap B S hS (yoneda.obj U') (c ≫ pullback.fst f.hom g.hom)
            (r.class B S hS (yoneda.obj U')) =
            pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom)
              (pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U'))) := rfl
        have h₃ : pointsMap B S hS (pullback f.hom g.hom) (pullback.fst f.hom g.hom)
            (pointsMap B S hS X₁.1 e.hom x') =
            pointsMap B S hS X₁.1 (e.hom ≫ pullback.fst f.hom g.hom) x' :=
          (congrFun (pointsMap_comp B S hS X₁.1 e.hom (pullback.fst f.hom g.hom)) x').symm
        rw [h₁, ← hcX, h₂, hz', h₃, heFst] }
  let chartF' : EtaleChartAtPoint B S hS f'.hom x' :=
    { U := U'
      V := V'
      a := c ≫ e.inv
      b := b ≫ pullback.snd v g.hom
      h := pV'
      a_etale := hcXEtale
      b_etale := hBEtale
      comm := hcommF'
      representative := r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        have h₁ : pointsMap B S hS (yoneda.obj U') (c ≫ e.inv)
            (r.class B S hS (yoneda.obj U')) =
            pointsMap B S hS (pullback f.hom g.hom) e.inv
              (pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U'))) := rfl
        have h₂ : pointsMap B S hS (pullback f.hom g.hom) e.inv
            (pointsMap B S hS X₁.1 e.hom x') =
            pointsMap B S hS X₁.1 (e.hom ≫ e.inv) x' :=
          (congrFun (pointsMap_comp B S hS X₁.1 e.hom e.inv) x').symm
        rw [h₁, hz', h₂, e.hom_inv_id, pointsMap_id, id_eq] }
  have hsource : chartF.sourcePoint B S hS = T.map pU (chartF'.sourcePoint B S hS) := by
    change (T.map (r.value ≫ pU)) (IsLocalRing.closedPoint r.carrier) =
      T.map pU ((T.map r.value) (IsLocalRing.closedPoint r.carrier))
    rw [Functor.map_comp]
    exact Scheme.Hom.comp_apply _ _ _
  have hsmooth' : InfinitesimalLifting.SmoothAt (T.map pV') (chartF'.sourcePoint B S hS) :=
    (smoothAt_iff_hasRepresentativeWithProperty (T.map pV') _).mpr
      ((isSmoothAt_iff_holdsOnEveryEtaleChartAtPoint B S hS X₁.property Y₁.property f'.hom x').mp
        hx' chartF')
  have hsmooth : InfinitesimalLifting.SmoothAt (T.map p) (chartF.sourcePoint B S hS) := by
    rw [hsource]
    cases hyp with
    | inl hfl =>
        have _ : LocallyOfFinitePresentation (T.map p) :=
          hfl.1 U V (a ≫ pullback.snd v f.hom) v p hAEtale hvEtale hcommF
        refine (smoothAt_iff_smoothAt_of_isPullback hcharts ?_
          (chartF'.sourcePoint B S hS)).mp hsmooth'
        exact hfl.2.imp (fun h => h U V (a ≫ pullback.snd v f.hom) v p hAEtale hvEtale hcommF)
          (fun h => h V' V (b ≫ pullback.snd v g.hom) v q hBEtale hvEtale hcommG)
    | inr hgl =>
        have hqFlat : Flat (T.map q) :=
          hgl.1 V' V (b ≫ pullback.snd v g.hom) v q hBEtale hvEtale hcommG
        have _ : LocallyOfFinitePresentation (T.map q) :=
          hgl.2 V' V (b ≫ pullback.snd v g.hom) v q hBEtale hvEtale hcommG
        obtain ⟨I, hxI, hpI⟩ := exists_opens_locallyOfFinitePresentation_of_smoothAt
          hcharts (chartF'.sourcePoint B S hS) hsmooth'
        have _ : LocallyOfFinitePresentation (I.ι ≫ T.map p) := hpI
        have hsqI : IsPullback (T.map pU ∣_ I) ((T.map pU ⁻¹ᵁ I).ι ≫ T.map pV')
            (I.ι ≫ T.map p) (T.map q) :=
          (isPullback_morphismRestrict (T.map pU) I).paste_vert hcharts
        have hxJ : chartF'.sourcePoint B S hS ∈ T.map pU ⁻¹ᵁ I := hxI
        have hsmoothJ : InfinitesimalLifting.SmoothAt
            ((T.map pU ⁻¹ᵁ I).ι ≫ T.map pV') ⟨chartF'.sourcePoint B S hS, hxJ⟩ :=
          InfinitesimalLifting.SmoothAt.comp_isOpenImmersion (T.map pU ⁻¹ᵁ I).ι (T.map pV')
            ⟨chartF'.sourcePoint B S hS, hxJ⟩ hsmooth'
        have hsmoothI := (smoothAt_iff_smoothAt_of_isPullback hsqI (Or.inr hqFlat)
          ⟨chartF'.sourcePoint B S hS, hxJ⟩).mp hsmoothJ
        have hpt : I.ι ((T.map pU ∣_ I) ⟨chartF'.sourcePoint B S hS, hxJ⟩) =
            T.map pU (chartF'.sourcePoint B S hS) := by
          calc I.ι ((T.map pU ∣_ I) ⟨chartF'.sourcePoint B S hS, hxJ⟩)
              = ((T.map pU ∣_ I) ≫ I.ι) ⟨chartF'.sourcePoint B S hS, hxJ⟩ :=
                (Scheme.Hom.comp_apply _ _ _).symm
            _ = ((T.map pU ⁻¹ᵁ I).ι ≫ T.map pU) ⟨chartF'.sourcePoint B S hS, hxJ⟩ := by
                rw [morphismRestrict_ι]
            _ = T.map pU (chartF'.sourcePoint B S hS) := Scheme.Hom.comp_apply _ _ _
        exact hpt ▸ smoothAt_of_smoothAt_comp I.ι (T.map p) _ hsmoothI
  refine (isSmoothAt_iff_holdsOnEveryEtaleChartAtPoint B S hS X₀.property Y₀.property f.hom
    _).mpr ((holdsOnEveryEtaleChartAtPoint_iff_some B S hS _ hQ X₀.property Y₀.property f.hom
      _).mpr ⟨chartF, ?_⟩)
  exact (smoothAt_iff_hasRepresentativeWithProperty (T.map p) _).mp hsmooth

/-- **Smoothness at a point descends from a flat base change.** For a cartesian square of
algebraic spaces over `S` with `g` flat, and with `f` or `g` locally of finite presentation, a
point at which the base change `f'` is smooth lies over a point at which `f` is smooth. -/
private theorem isSmoothAt_of_isSmoothAt_of_isPullback (sq : IsPullback g' f' f g)
    (hgflat : IsFlat B S hS g.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom ∨
      IsLocallyOfFinitePresentation B S hS g.hom)
    (x' : points B S hS X₁.1) (hx' : IsSmoothAt B S hS f'.hom x') :
    IsSmoothAt B S hS f.hom (pointsMap B S hS X₁.1 g'.hom x') :=
  isSmoothAt_of_isSmoothAt_of_isPullback_of_flat_lfp B S hS sq
    (hlfp.elim (fun h => Or.inl ⟨h, Or.inr hgflat⟩) (fun h => Or.inr ⟨hgflat, h⟩)) x' hx'

/-- **The inverse image of the smooth locus lies in the smooth locus of a base change.** For a
cartesian square of algebraic spaces over `S`, the inverse image along `g'` of the smooth locus
of `f` is an open subspace on which `f'` is smooth, hence is contained in the smooth locus of
`f'`.

Neither flatness nor local finite presentation is needed: the inverse image is an open subspace
because an open immersion of algebraic spaces is stable under base change, and the restriction
of `f'` to it is a base change of the restriction of `f` to the smooth locus, so smoothness
transfers by Stacks 03ZE. -/
theorem preimage_maximalSmoothOpen_le (sq : IsPullback g' f' f g) :
    (maximalSmoothOpen B S hS f.hom).preimage g'.hom ≤ maximalSmoothOpen B S hS f'.hom := by
  have hWopen := isOpenSubspace_maximalSmoothOpen B S hS X₀.property Y₀.property f.hom
  have hWsm := isSmooth_maximalSmoothOpen B S hS X₀.property Y₀.property f.hom
  have hPopen : IsOpenSubspace B S hS ((maximalSmoothOpen B S hS f.hom).preimage g'.hom) :=
    isOpenSubspace_preimage B S hS g'.hom (maximalSmoothOpen B S hS f.hom) X₀.property
      X₁.property hWopen
  refine le_maximalSmoothOpen B S hS f'.hom hPopen ?_
  let Wₒ : AlgebraicSpaces B S hS := ⟨(maximalSmoothOpen B S hS f.hom).toFunctor, hWopen.1⟩
  let Pₒ : AlgebraicSpaces B S hS :=
    ⟨((maximalSmoothOpen B S hS f.hom).preimage g'.hom).toFunctor, hPopen.1⟩
  let Psm : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃A D⦄ (k : A ⟶ D) => IsSmooth B S hS k.hom
  have hsq : IsPullback
      (ObjectProperty.homMk ((maximalSmoothOpen B S hS f.hom).fromPreimage g'.hom) : Pₒ ⟶ Wₒ)
      (ObjectProperty.homMk ((maximalSmoothOpen B S hS f.hom).preimage g'.hom).ι : Pₒ ⟶ X₁)
      (ObjectProperty.homMk (maximalSmoothOpen B S hS f.hom).ι : Wₒ ⟶ X₀) g' :=
    isPullback_homMk_preimage B S hS g'.hom _ X₁.property X₀.property hWopen.1 hPopen.1
  have _ : Psm.IsStableUnderBaseChange := isSmooth_isStableUnderBaseChange B S hS
  have hbase : Psm ((ObjectProperty.homMk (maximalSmoothOpen B S hS f.hom).ι : Wₒ ⟶ X₀) ≫ f) :=
    hWsm
  have hcomp : Psm ((ObjectProperty.homMk
      ((maximalSmoothOpen B S hS f.hom).preimage g'.hom).ι : Pₒ ⟶ X₁) ≫ f') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hsq.paste_vert sq) hbase
  exact hcomp

/-- **The smooth locus of a base change lies in the inverse image of the smooth locus.** This is
the direction of the two base-change clauses of Stacks 0DZI which uses their hypotheses: `g`
flat, and `f` or `g` locally of finite presentation.

By Stacks 03IE it suffices to see that every point of the smooth locus of `f'` is carried by
`g'` into the point set of the smooth locus of `f`, and that is
`AlgebraicGeometry.Space.isSmoothAt_of_isSmoothAt_of_isPullback` followed by maximality. -/
@[ega "IV 17.7.2" "(ii)"]
private theorem maximalSmoothOpen_le_preimage (sq : IsPullback g' f' f g)
    (hgflat : IsFlat B S hS g.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom ∨
      IsLocallyOfFinitePresentation B S hS g.hom) :
    maximalSmoothOpen B S hS f'.hom ≤ (maximalSmoothOpen B S hS f.hom).preimage g'.hom := by
  set A := maximalSmoothOpen B S hS f'.hom
  set W := maximalSmoothOpen B S hS f.hom
  have hAopen : IsOpenSubspace B S hS A :=
    isOpenSubspace_maximalSmoothOpen B S hS X₁.property Y₁.property f'.hom
  have hAsm : IsSmooth B S hS (A.ι ≫ f'.hom) :=
    isSmooth_maximalSmoothOpen B S hS X₁.property Y₁.property f'.hom
  have hWopen : IsOpenSubspace B S hS W :=
    isOpenSubspace_maximalSmoothOpen B S hS X₀.property Y₀.property f.hom
  have hRange : Set.range (pointsMap B S hS A.toFunctor (A.ι ≫ g'.hom)) ⊆
      Set.range (pointsMap B S hS W.toFunctor W.ι) := by
    rintro z ⟨xA, rfl⟩
    have hAt' : IsSmoothAt B S hS f'.hom (pointsMap B S hS A.toFunctor A.ι xA) :=
      ⟨A, hAopen, xA, rfl, hAsm⟩
    obtain ⟨V, hV, xV, hxV, hVsm⟩ :=
      isSmoothAt_of_isSmoothAt_of_isPullback B S hS sq hgflat hlfp _ hAt'
    have hVW : V ≤ W := le_maximalSmoothOpen B S hS f.hom hV hVsm
    refine ⟨pointsMap B S hS V.toFunctor (Subfunctor.homOfLe hVW) xV, ?_⟩
    calc pointsMap B S hS W.toFunctor W.ι
            (pointsMap B S hS V.toFunctor (Subfunctor.homOfLe hVW) xV)
        = pointsMap B S hS V.toFunctor (Subfunctor.homOfLe hVW ≫ W.ι) xV :=
          (congrFun (pointsMap_comp B S hS V.toFunctor (Subfunctor.homOfLe hVW) W.ι) xV).symm
      _ = pointsMap B S hS V.toFunctor V.ι xV := by rw [Subfunctor.homOfLe_ι]
      _ = pointsMap B S hS X₁.1 g'.hom (pointsMap B S hS A.toFunctor A.ι xA) := hxV
      _ = pointsMap B S hS A.toFunctor (A.ι ≫ g'.hom) xA :=
          (congrFun (pointsMap_comp B S hS A.toFunctor A.ι g'.hom) xA).symm
  obtain ⟨t, ht⟩ := (factorsThrough_openSubspace_iff_points B S hS X₀.property hAopen.1 W
    hWopen (A.ι ≫ g'.hom)).2 hRange
  intro Z x hx
  have he := congrArg (fun k => k.app Z ⟨x, hx⟩) ht
  change (t.app Z ⟨x, hx⟩).1 = g'.hom.app Z x at he
  change g'.hom.app Z x ∈ W.obj Z
  rw [← he]
  exact (t.app Z ⟨x, hx⟩).property

/-- **Stacks 0DZI, part (1).** Formation of the smooth locus commutes with base change by a
morphism which is flat and locally of finite presentation. -/
@[stacks 0DZI "part (1): base change by a flat morphism locally of finite presentation",
  ega "IV 17.7.4" "more general"]
theorem maximalSmoothOpen_eq_preimage_of_isFlat_isLocallyOfFinitePresentation
    (sq : IsPullback g' f' f g) (hgflat : IsFlat B S hS g.hom)
    (hglfp : IsLocallyOfFinitePresentation B S hS g.hom) :
    maximalSmoothOpen B S hS f'.hom = (maximalSmoothOpen B S hS f.hom).preimage g'.hom :=
  le_antisymm (maximalSmoothOpen_le_preimage B S hS sq hgflat (Or.inr hglfp))
    (preimage_maximalSmoothOpen_le B S hS sq)

/-- **Stacks 0DZI, part (2).** For a morphism locally of finite presentation, formation of the
smooth locus commutes with every flat base change. -/
@[stacks 0DZI "part (2): flat base change of a morphism locally of finite presentation",
  ega "IV 17.7.4" "(v), special case"]
theorem maximalSmoothOpen_eq_preimage_of_isLocallyOfFinitePresentation_isFlat
    (sq : IsPullback g' f' f g) (hflfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (hgflat : IsFlat B S hS g.hom) :
    maximalSmoothOpen B S hS f'.hom = (maximalSmoothOpen B S hS f.hom).preimage g'.hom :=
  le_antisymm (maximalSmoothOpen_le_preimage B S hS sq hgflat (Or.inl hflfp))
    (preimage_maximalSmoothOpen_le B S hS sq)

/-- **Smoothness at a point under an arbitrary base change of a flat morphism locally of finite
presentation.** For a cartesian square of algebraic spaces over `S` whose right-hand morphism
`f` is flat and locally of finite presentation, the base change `f'` is smooth at a point of its
source exactly when `f` is smooth at the image of that point; no hypothesis on the base morphism
`g` is needed.

One direction is Stacks 02V4 in the case of a flat morphism, read on compatible étale charts.
The other needs no hypothesis at all: the inverse image of the smooth locus of `f` is an open
subspace on which `f'` is smooth, so it is contained in the smooth locus of `f'`, and the point
lies in it because the inverse image is the fibre product. -/
@[ega "IV 17.7.4" "(v), special case"]
theorem isSmoothAt_iff_isSmoothAt_of_isPullback (sq : IsPullback g' f' f g)
    (hflat : IsFlat B S hS f.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (x' : points B S hS X₁.1) :
    IsSmoothAt B S hS f'.hom x' ↔
      IsSmoothAt B S hS f.hom (pointsMap B S hS X₁.1 g'.hom x') := by
  refine ⟨isSmoothAt_of_isSmoothAt_of_isPullback_of_flat_lfp B S hS sq
    (Or.inl ⟨hlfp, Or.inl hflat⟩) x', ?_⟩
  rintro ⟨V, hV, v, hv, hVsm⟩
  have hVW : V ≤ maximalSmoothOpen B S hS f.hom := le_maximalSmoothOpen B S hS f.hom hV hVsm
  obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS
    (Subfunctor.isPullback_preimage g'.hom (maximalSmoothOpen B S hS f.hom))
    (pointsMap B S hS V.toFunctor (Subfunctor.homOfLe hVW) v) x'
    (by rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]; exact hv)
  refine ⟨maximalSmoothOpen B S hS f'.hom,
    isOpenSubspace_maximalSmoothOpen B S hS X₁.property Y₁.property f'.hom,
    pointsMap B S hS _ (Subfunctor.homOfLe (preimage_maximalSmoothOpen_le B S hS sq)) w, ?_,
    isSmooth_maximalSmoothOpen B S hS X₁.property Y₁.property f'.hom⟩
  rw [← pointsMap_comp_apply, Subfunctor.homOfLe_ι]
  exact hw

end SmoothLocusBaseChange

end Space

end AlgebraicGeometry

end
