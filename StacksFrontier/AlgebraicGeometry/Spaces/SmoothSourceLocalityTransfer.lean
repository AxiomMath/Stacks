module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothSourceLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion

/-!
# Source locality for the smooth topology transferred from schemes to algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `P` be a property of morphisms of
schemes which is étale local on the source and target (**Stacks 04QZ**). **Stacks 06ER** says
that if `P` is local on the source for one of the five topologies of **Stacks 03YH** then so is
the chart property `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart B S hS P` of
**Stacks 03MJ**. This module proves the **smooth case**, which the fpqc case in
`StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer` records as missing exactly
three lemmas, and applies it to smoothness itself: **Stacks 06F2**, and then **Stacks 06FC** at
the smooth case.

The argument is the source's, and is the fpqc one verbatim once its three topology-dependent
inputs are supplied for the smooth topology. Those three are cheaper here than for the fpqc
topology, because a smooth covering is a jointly surjective family of smooth morphisms with no
refinement clause attached:

* a smooth covering of algebraic spaces all of whose members and whose target are representable
  is a smooth covering of the representing schemes, i.e. lies in `Scheme.precoverage @Smooth` —
  joint surjectivity on scheme points comes from joint surjectivity on presheaf points, and
  smoothness of each member from the chart condition read at the two identity charts;
* a smooth covering base-changed along a chart of its target is a smooth covering of the chart —
  smoothness of the projections is base-change stability (**Stacks 03ZE**) and joint
  surjectivity is **Stacks 03H4**, points of a cartesian square;
* a smooth covering composed with a surjective étale scheme atlas of each member is a smooth
  covering — an étale morphism of algebraic spaces is smooth and smooth morphisms compose
  (**Stacks 03ZD**).

## Main results

* `AlgebraicGeometry.Space.isSmooth_yoneda_map_iff`: a morphism of the site is a smooth morphism
  of algebraic spaces exactly when the morphism of schemes underneath it is smooth; the forward
  direction alone is `AlgebraicGeometry.Space.smooth_toScheme_map_of_isSmooth_yoneda_map`.
* `AlgebraicGeometry.Space.isSmoothCovering_pullback`: **Stacks 041D**, base change, in the
  shape that names the second projection.
* `AlgebraicGeometry.Space.isSmoothCovering_yoneda_of_isCovering`,
  `AlgebraicGeometry.Space.isSmoothCovering_baseChange_of_chart`,
  `AlgebraicGeometry.Space.etale_atlases_comp_isSmoothCovering`: the three smooth-topology
  inputs of Stacks 06ER.
* `AlgebraicGeometry.Space.isLocalAtSource_smooth_of_schemes`: **Stacks 06ER**, the smooth case.
* `AlgebraicGeometry.Space.isSmooth_isLocalAtSource_smooth`: **Stacks 06F2**.
* `AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_smooth`: **Stacks 06FC**, the smooth
  case.

## Implementation notes

`isLocalAtSource_smooth_of_schemes` is the smooth case of Stacks 06ER; the statement for all five
topologies at once is `AlgebraicGeometry.Space.Topology.isLocalAtSource_holdsOnEveryEtaleChart`.

Its scheme-level hypothesis is `MorphismProperty.IsLocalAtSource P (Scheme.precoverage @Smooth)`,
which for `P = AlgebraicGeometry.Smooth` is **Stacks 036U**, proved in
`StacksFrontier.AlgebraicGeometry.Morphisms.SmoothSourceLocality`. The fpqc version of that
instance is *false* for smoothness and not merely missing: source locality for an fpqc
precoverage forces smoothness to be preserved by precomposition with any flat surjective
morphism, and the relative Frobenius of the affine line over a field of characteristic `p` is a
flat surjective morphism whose composition with the identity is not smooth. So the smooth case
of Stacks 06ER, not an `of_le` from the fpqc case, is what Stacks 06F2 needs.

Stacks 06F2 is registered as an **instance**, which is the form the criterion of Stacks 06FB
consumes it in, exactly as `AlgebraicGeometry.Space.isFlat_isLocalAtSource_fpqc` is.

The target locality that Stacks 06FC needs is the smooth restriction of
`@[stacks 0429] AlgebraicGeometry.Space.smooth_isLocalAtTarget_fpqc` along
`AlgebraicGeometry.Space.smooth_precoverage_le_fpqc`, which is the smooth case of
**Stacks 0DFQ**; this is the flat case's route with flatness replaced by smoothness throughout.

## References

* [Stacks Project, Tag 041D](https://stacks.math.columbia.edu/tag/041D)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 06ER](https://stacks.math.columbia.edu/tag/06ER)
* [Stacks Project, Tag 06F2](https://stacks.math.columbia.edu/tag/06F2)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves of types on the site, supplied directly: under Mathlib v4.35.0 the
instance search for `HasPullback` there times out. -/
local instance (priority := high) hasPullback_presheaf_SmoothSourceLocalityTransfer
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) : HasPullback f g :=
  HasLimitsOfShape.has_limit _

/-- Products of presheaves of types on the site indexed by a small discrete type, supplied
directly for the same reason. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-! ### Smoothness of a morphism of the site -/

/-- A smooth chart of a presheaf on the big fppf site of `S` is a smooth morphism of algebraic
spaces in the sense of Stacks 03ZC: the two identity charts of a morphism of the site compute
the chart condition of Stacks 03MJ at the morphism of schemes itself. -/
theorem smooth_toScheme_map_of_isSmooth_yoneda_map
    {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hh : IsSmooth B S hS (yoneda.map h)) :
    Smooth ((BigFppfOver.toScheme B S hS).map h) :=
  hh U V (𝟙 (yoneda.obj U)) (𝟙 (yoneda.obj V)) h
    (presheaf_etale_id B S hS U) (presheaf_etale_id B S hS V) (by simp)

/-- **A morphism of the big fppf category of `S` is a smooth morphism of algebraic spaces exactly
when the morphism of schemes underneath it is smooth.**

The forward direction is `AlgebraicGeometry.Space.smooth_toScheme_map_of_isSmooth_yoneda_map`.
The converse is **Stacks 03MJ** for a morphism of representable presheaves
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_representable`), whose conclusion is about
the morphism read off the *canonical* representations of the two presheaves rather than the given
one; the two differ by the representation isomorphisms, which are isomorphisms of the site and so
smooth, and smoothness is stable under composition. -/
theorem isSmooth_yoneda_map_iff {U V : BigFppfOver B S hS} (j : U ⟶ V) :
    IsSmooth B S hS (yoneda.map j) ↔ Smooth ((BigFppfOver.toScheme B S hS).map j) := by
  refine ⟨smooth_toScheme_map_of_isSmooth_yoneda_map B S hS j, fun hj => ?_⟩
  change HoldsOnEveryEtaleChart B S hS
    (@Smooth.{u} : MorphismProperty Scheme.{u}) (yoneda.map j)
  rw [holdsOnEveryEtaleChart_iff_representable
    (B := B) (S := S) (hS := hS) (P := @Smooth.{u})
    Smooth.isEtaleLocalOnSourceAndTarget]
  let T := BigFppfOver.toScheme B S hS
  let eV := yoneda.preimageIso (yoneda.obj U).reprW
  let eU := yoneda.preimageIso (yoneda.obj V).reprW
  have hreV : (yoneda.obj U).reprW.hom = yoneda.map eV.hom :=
    (Functor.map_preimage yoneda (yoneda.obj U).reprW.hom).symm
  have hreU : (yoneda.obj V).reprW.inv = yoneda.map eU.inv :=
    (Functor.map_preimage yoneda (yoneda.obj V).reprW.inv).symm
  have hpre : yoneda.preimage
      ((yoneda.obj U).reprW.hom ≫ yoneda.map j ≫ (yoneda.obj V).reprW.inv) =
      eV.hom ≫ j ≫ eU.inv := by
    rw [hreV, hreU, ← Functor.map_comp, ← Functor.map_comp]
    apply yoneda.map_injective
    simp
  rw [hpre, Functor.map_comp, Functor.map_comp]
  exact MorphismProperty.comp_mem @Smooth
    (T.map eV.hom ≫ T.map j) (T.map eU.inv)
    (MorphismProperty.comp_mem @Smooth (T.map eV.hom) (T.map j) inferInstance hj) inferInstance

/-! ### The three smooth-topology inputs of Stacks 06ER -/

/-- A smooth covering family of algebraic spaces over `S` all of whose members and whose target
are representable is a smooth covering family of the representing schemes, that is, lies in the
precoverage of jointly surjective families of smooth morphisms of schemes.

This is the one step of Stacks 06ER where the choice of topology is load-bearing. For the smooth
topology it needs no quasi-compactness: joint surjectivity on the schemes' points follows from
joint surjectivity on the presheaves' points, and smoothness of each member is the chart
condition of Stacks 03MJ read at the two identity charts. -/
theorem isSmoothCovering_yoneda_of_isCovering
    {I : Type v} (U : I → BigFppfOver B S hS) (V : BigFppfOver B S hS) (f : ∀ i, U i ⟶ V)
    (hcover : Topology.IsCovering .smooth B S hS
      (fun i => yoneda.obj (U i)) (fun i => yoneda.map (f i))) :
    Presieve.ofArrows
      (fun i => (BigFppfOver.toScheme B S hS).obj (U i))
      (fun i => (BigFppfOver.toScheme B S hS).map (f i)) ∈
      Scheme.precoverage (@Smooth.{u}) ((BigFppfOver.toScheme B S hS).obj V) := by
  let T := BigFppfOver.toScheme B S hS
  let E : PreZeroHypercover (T.obj V) :=
    { I₀ := I
      X := fun i => T.obj (U i)
      f := fun i => T.map (f i) }
  have hsurj := scheme_family_jointly_surjective_of_points B S hS U V f
    hcover.2.2.jointly_surjective
  have hsmooth : ∀ i, Smooth (T.map (f i)) := fun i =>
    (hcover.2.2.smooth i) (U i) V (𝟙 (yoneda.obj (U i))) (𝟙 (yoneda.obj V)) (f i)
      (presheaf_etale_id B S hS (U i)) (presheaf_etale_id B S hS V) (by simp)
  exact (Scheme.presieve₀_mem_precoverage_iff (P := @Smooth.{u}) E).mpr
    ⟨fun x => by
      obtain ⟨i, y, hy⟩ := hsurj x
      exact ⟨i, y, hy⟩, hsmooth⟩

/-- **Stacks 041D**, the base-change clause, in the shape that names the *second* projection:
pulling a smooth covering family of algebraic spaces over `S` back along a morphism `f : X ⟶ Y`
gives a smooth covering of `X`. This is the shape
`AlgebraicGeometry.Space.isFpqcCovering_pullback` has for the fpqc topology, and the
base change along a chart below is its special case at a chart of the target. -/
theorem isSmoothCovering_pullback
    {I : Type v} {Y X : AlgebraicSpaces B S hS} {Yi : I → AlgebraicSpaces B S hS}
    (g : ∀ i, Yi i ⟶ Y) (f : X ⟶ Y)
    (hg : IsSmoothCovering B S hS (fun i => (Yi i).1) (fun i => (g i).hom)) :
    IsSmoothCovering B S hS
      (fun i => (AlgebraicSpaces.fiberProduct B S hS (g i) f).1)
      (fun i => pullback.snd (g i).hom f.hom) := by
  refine ⟨X.property, fun i => (AlgebraicSpaces.fiberProduct B S hS (g i) f).property,
    fun i => ?_, ?_⟩
  · exact (isSmooth_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS (g i) f) (hg.smooth i)
  · refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨i, yi, hyi⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hg.jointly_surjective
      (pointsMap B S hS X.1 f.hom x))
    obtain ⟨w, -, hw⟩ := exists_point_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS (g i) f) yi x hyi
    exact Set.mem_iUnion.mpr ⟨i, ⟨w, hw⟩⟩

/-- A smooth covering family of an algebraic space over `S`, base-changed along a scheme chart
of its target, is a smooth covering family of that chart, and each member sits in a cartesian
square over the chart and the corresponding member of the original family.

Smoothness of the projections is base-change stability of smoothness (Stacks 03ZE); joint
surjectivity is Stacks 03H4, which produces a point of a cartesian square from a compatible
pair of points. -/
theorem isSmoothCovering_baseChange_of_chart
    {I : Type v} {X : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering .smooth B S hS (fun i => (Zi i).1) (fun i => (gi i).hom))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1) :
    ∃ (Ai : I → AlgebraicSpaces B S hS)
      (qi : ∀ i, Ai i ⟶ representedAlgebraicSpace B S hS U)
      (projZ : ∀ i, Ai i ⟶ Zi i),
        Topology.IsCovering .smooth B S hS (fun i => (Ai i).1) (fun i => (qi i).hom) ∧
        (∀ i, IsPullback (qi i) (projZ i)
          (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi i)) := by
  let Uobj := representedAlgebraicSpace B S hS U
  let au : Uobj ⟶ X := ObjectProperty.homMk a
  let Ai : I → AlgebraicSpaces B S hS :=
    fun i => AlgebraicSpaces.fiberProduct B S hS (gi i) au
  let qi : ∀ i, Ai i ⟶ Uobj := fun i => ObjectProperty.homMk (pullback.snd (gi i).hom au.hom)
  let projZ : ∀ i, Ai i ⟶ Zi i := fun i => ObjectProperty.homMk (pullback.fst (gi i).hom au.hom)
  have hpb : ∀ i, IsPullback (qi i) (projZ i) au (gi i) :=
    fun i => (AlgebraicSpaces.isPullback_fiberProduct B S hS (gi i) au).flip
  refine ⟨Ai, qi, projZ, ⟨Uobj.property, fun i => (Ai i).property, Uobj.property,
    fun i => (Ai i).property, fun i => (isSmooth_isStableUnderBaseChange B S hS).of_isPullback
      (hpb i).flip (hcover.2.2.smooth i), Set.eq_univ_of_forall fun u => ?_⟩, hpb⟩
  obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp
    hcover.2.2.jointly_surjective (pointsMap B S hS Uobj.1 au.hom u))
  obtain ⟨w, hw, -⟩ := exists_point_of_isPullback B S hS (hpb i) u z hz.symm
  exact Set.mem_iUnion.mpr ⟨i, w, hw⟩

/-- Composing a smooth covering of an algebraic space over `S` with a surjective étale scheme
atlas of each of its members gives a smooth covering, indexed by the members paired with a
one-element type.

An étale morphism of algebraic spaces is smooth and smooth morphisms compose (Stacks 03ZD), and
joint surjectivity is transitive. -/
theorem etale_atlases_comp_isSmoothCovering
    {I : Type v} (Z : I → AlgebraicSpaces B S hS) (V : AlgebraicSpaces B S hS)
    (g : ∀ i, Z i ⟶ V)
    (hbase : Topology.IsCovering .smooth B S hS (fun i => (Z i).1) (fun i => (g i).hom))
    (U : I → BigFppfOver B S hS) (a : ∀ i, yoneda.obj (U i) ⟶ (Z i).1)
    (hsurj : ∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i))
    (hetale : ∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a i)) :
    Topology.IsCovering .smooth B S hS
      (fun p : Σ _ : I, PUnit.{v + 1} => yoneda.obj (U p.1))
      (fun p => a p.1 ≫ (g p.1).hom) := by
  have hUspace : ∀ i, IsAlgebraicSpace B S hS (yoneda.obj (U i)) := fun i =>
    isAlgebraicSpace_yoneda B S hS (U i)
  have haSmooth : ∀ i, IsSmooth B S hS (a i) := fun i =>
    isSmooth_of_isEtale B S hS (hbase.2.1 i)
      (chart_map_isEtale B S hS (U i) (a i) (hetale i))
  refine ⟨hbase.1, fun p => hUspace p.1, hbase.1, fun p => hUspace p.1, ?_, ?_⟩
  · intro p
    exact isSmooth_comp B S hS (hUspace p.1) (hbase.2.1 p.1) hbase.1
      (a p.1) (g p.1).hom (haSmooth p.1) (hbase.2.2.smooth p.1)
  · refine Set.eq_univ_of_forall fun v => ?_
    obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp
      (Set.eq_univ_iff_forall.mp hbase.2.2.jointly_surjective v)
    obtain ⟨w, hw⟩ := (surjective_iff_surjective_pointsMap B S hS (Z i).1 (hbase.2.1 i)
      (U i) (a i)).mp (hsurj i) z
    refine Set.mem_iUnion.mpr ⟨⟨i, PUnit.unit⟩, w, ?_⟩
    rw [pointsMap_comp]
    change pointsMap B S hS (Z i).1 (g i).hom (pointsMap B S hS _ (a i) w) = v
    rw [hw, hz]

/-- Around a smooth covering and an étale scheme chart `a` of its target: the base change of the
covering to the chart, an étale atlas of each base-changed member, and the resulting smooth
covering of the chart by schemes, with the commutation relations needed to read the chart
conditions off along any square `a ≫ f = h₀ ≫ b`. -/
private theorem exists_scheme_cover_of_etale_chart
    {I : Type v} {X : AlgebraicSpaces B S hS}
    (Zi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Zi i ⟶ X)
    (hcover : Topology.IsCovering .smooth B S hS (fun i => (Zi i).1) (fun i => (gi i).hom))
    (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ X.1)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ∃ (Ai : I → AlgebraicSpaces B S hS)
      (qi : ∀ i, Ai i ⟶ representedAlgebraicSpace B S hS U) (projZ : ∀ i, Ai i ⟶ Zi i)
      (Wi : I → BigFppfOver B S hS) (wi : ∀ i, yoneda.obj (Wi i) ⟶ (Ai i).1)
      (d : ∀ p : Σ _ : I, PUnit.{v + 1}, Wi p.1 ⟶ U),
        (∀ i, IsPullback (qi i) (projZ i)
          (ObjectProperty.homMk a : representedAlgebraicSpace B S hS U ⟶ X) (gi i)) ∧
        (∀ i, (qi i).hom ≫ a = (projZ i).hom ≫ (gi i).hom) ∧
        (∀ i, (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (wi i)) ∧
        (∀ i, (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf (wi i ≫ (projZ i).hom)) ∧
        (∀ p, yoneda.map (d p) = wi p.1 ≫ (qi p.1).hom) ∧
        (∀ {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {V : BigFppfOver B S hS}
          (b : yoneda.obj V ⟶ Y.1) (h₀ : U ⟶ V), a ≫ f.hom = yoneda.map h₀ ≫ b →
          ∀ p, yoneda.map (d p ≫ h₀) ≫ b =
            (wi p.1 ≫ (projZ p.1).hom) ≫ (gi p.1).hom ≫ f.hom) ∧
        Presieve.ofArrows (fun p : Σ _ : I, PUnit.{v + 1} => (BigFppfOver.toScheme B S hS).obj
            (Wi p.1)) (fun p => (BigFppfOver.toScheme B S hS).map (d p)) ∈
          Scheme.precoverage (@Smooth.{u}) ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨Ai, qi, projZ, hAi, hpb⟩ := isSmoothCovering_baseChange_of_chart B S hS Zi gi hcover U a
  choose Wi wi hsurjWi hetaleWi using fun i => (Ai i).property.exists_atlas
  let d : ∀ p : Σ _ : I, PUnit.{v + 1}, Wi p.1 ⟶ U :=
    fun p => yoneda.preimage (wi p.1 ≫ (qi p.1).hom)
  have hd (p : Σ _ : I, PUnit.{v + 1}) : yoneda.map (d p) = wi p.1 ≫ (qi p.1).hom := by
    simp [d]
  have hpbw (i : I) : (qi i).hom ≫ a = (projZ i).hom ≫ (gi i).hom :=
    congrArg (fun k => k.hom) (hpb i).w
  have hspaceCover := etale_atlases_comp_isSmoothCovering B S hS Ai
    (representedAlgebraicSpace B S hS U) qi hAi Wi wi hsurjWi hetaleWi
  refine ⟨Ai, qi, projZ, Wi, wi, d, hpb, hpbw, hsurjWi, fun i => ?_, hd, ?_,
    isSmoothCovering_yoneda_of_isCovering B S hS (fun p : Σ _ : I, PUnit.{v + 1} => Wi p.1) U d
      (by simpa only [hd] using hspaceCover)⟩
  · exact (isEtale_iff_presheaf_of_yoneda B S hS _).1 (isEtale_comp B S hS
      (chart_map_isEtale B S hS (Wi i) (wi i) (hetaleWi i))
      (isEtale_of_isPullback B S hS (qi i) (projZ i) _ (gi i) (hpb i)
        (chart_map_isEtale B S hS U a ha)))
  · intro Y f V b h₀ hcomm p
    rw [Functor.map_comp, hd, Category.assoc, Category.assoc, ← hcomm, ← Category.assoc (qi _).hom,
      hpbw]
    simp only [Category.assoc]

/-! ### Stacks 06ER, the smooth case -/

/-- **Stacks 06ER**, the smooth case. If a property `P` of morphisms of schemes is étale local on
the source and target and local on the source for the smooth topology of schemes, then the
associated property of morphisms of algebraic spaces over `S` of Stacks 03MJ is local on the
source for the smooth topology of algebraic spaces.

Stacks 06ER for all five topologies of Stacks 03YH at once is
`AlgebraicGeometry.Space.Topology.isLocalAtSource_holdsOnEveryEtaleChart`. -/
theorem isLocalAtSource_smooth_of_schemes
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    [P.IsLocalAtSource (Scheme.precoverage (@Smooth.{u}))] :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) =>
        HoldsOnEveryEtaleChart B S hS P f.hom)
      (Topology.precoverage.{u, v} .smooth B S hS) := by
  have hlocal : P.IsLocalAtSource (Scheme.precoverage (@Smooth.{u})) := ‹_›
  let C := AlgebraicSpaces B S hS
  let Q : MorphismProperty C := fun {F G} f => HoldsOnEveryEtaleChart B S hS P f.hom
  let T := BigFppfOver.toScheme B S hS
  let : Q.RespectsIso := holdsOnEveryEtaleChart_respectsIso B S hS P
  refine MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover ?_
  intro X Y f E
  rcases E.mem₀ with ⟨I, Zi, gi, hpres, hcover⟩
  constructor
  · intro hf i
    have hgiQ : ∀ j : I, Q ((gi j) ≫ f) := by
      intro j
      obtain ⟨V, b, hbSurj, hbEtale⟩ := Y.property.exists_atlas
      obtain ⟨T0, t, alpha, hα, htSurj, htEtale⟩ :=
        exists_surjective_etale_presentation_lift B S hS
          X.property Y.property f.hom V b hbSurj hbEtale
      have hPalpha : P (T.map alpha) := hf T0 V t b alpha htEtale hbEtale hα.symm
      let Tobj : AlgebraicSpaces B S hS :=
        ⟨yoneda.obj T0, isAlgebraicSpace_yoneda B S hS T0⟩
      let tX : Tobj ⟶ X := ObjectProperty.homMk t
      obtain ⟨Ai, qi, projZ, Wi, wi, d, hpb, hpbw, hsurjWi, hcEtale, hd, hcommD, hschemeCover⟩ :=
        exists_scheme_cover_of_etale_chart B S hS Zi gi hcover T0 t htEtale
      let p : Σ _ : I, PUnit.{v + 1} := ⟨j, PUnit.unit⟩
      have hPh : P (T.map (d p ≫ alpha)) := by
        rw [Functor.map_comp]
        exact hlocal.comp hschemeCover (T.map (d p)) (by exact ⟨p⟩) hPalpha
      have htSurjPts : IsSurjective B S hS t :=
        (surjective_iff_surjective_pointsMap B S hS X.1 X.property T0 t).mp htSurj
      have hcSurj := (surjective_iff_surjective_pointsMap B S hS
        (Zi j).1 (Zi j).property (Wi j) (wi j ≫ (projZ j).hom)).mpr
        (isSurjective_comp B S hS
          ((surjective_iff_surjective_pointsMap B S hS (Ai j).1 (Ai j).property
            (Wi j) (wi j)).mp (hsurjWi j))
          (isSurjective_of_isPullback B S hS (hpb j) htSurjPts))
      exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP (Zi j).property
        Y.property ((gi j ≫ f).hom)).2
          ⟨Wi j, V, wi j ≫ (projZ j).hom, b, d p ≫ alpha, hcEtale j, hbEtale, hcSurj,
            hcommD f b alpha (by simpa using hα) p, hPh⟩
    have hmem : E.presieve₀ (E.f i) := ⟨i⟩
    obtain ⟨j, hobj, hindex⟩ := Presieve.ofArrows_surj gi (E.f i) (by
      simpa only [hpres] using hmem)
    let e : E.toPreZeroHypercover.2 i ⟶ Zi j := eqToHom hobj.symm
    let : IsIso e := inferInstance
    have hcomp : Q (e ≫ (gi j ≫ f)) :=
      MorphismProperty.RespectsIso.precomp Q e (gi j ≫ f) (hgiQ j)
    change Q (E.f i ≫ f)
    rw [hindex]
    exact hcomp
  · intro hall U V a b h ha hb hcomm
    obtain ⟨Ai, qi, projZ, Wi, wi, d, hpb, hpbw, hsurjWi, hwzEtale, hd, hcommD, hschemeCover⟩ :=
      exists_scheme_cover_of_etale_chart B S hS Zi gi hcover U a ha
    apply hlocal.of_forall_comp hschemeCover
    intro W' k hk
    cases hk with
    | mk p =>
      rcases p with ⟨i, ji⟩
      have hmem : E.presieve₀ (gi i) := by rw [hpres]; exact ⟨i⟩
      obtain ⟨j, hobj, hgi⟩ := Presieve.ofArrows_surj E.f (gi i) (by
        simpa only [hpres] using hmem)
      have hi := hall j
      change HoldsOnEveryEtaleChart B S hS P ((E.f j ≫ f).hom) at hi
      let e : Zi i ⟶ E.toPreZeroHypercover.2 j := eqToHom hobj.symm
      let : IsIso e := inferInstance
      have hi' : HoldsOnEveryEtaleChart B S hS P ((gi i).hom ≫ f.hom) := by
        have := MorphismProperty.RespectsIso.precomp Q e (E.f j ≫ f) hi
        change Q (e ≫ (E.f j ≫ f)) at this
        change Q (gi i ≫ f)
        rw [hgi]
        exact this
      rw [← Functor.map_comp]
      exact hi' (Wi i) V _ b _ (hwzEtale i) hb (hcommD f b h hcomm.symm ⟨i, ji⟩)


/-! ### Stacks 06F2 and the smooth case of Stacks 06FC -/

/-- **Stacks 06F2.** Smoothness of morphisms of algebraic spaces over `S` is local on the source
for the smooth topology.

One application of the smooth case of Stacks 06ER to smoothness of morphisms of schemes, which
is étale local on the source and target (Stacks 04R3, smooth case) and smooth local on the
source (Stacks 036U). Registered as an instance, which is the form the criterion of Stacks 06FB
takes it in. -/
@[stacks 06F2]
instance isSmooth_isLocalAtSource_smooth :
    MorphismProperty.IsLocalAtSource
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsSmooth B S hS f.hom)
      (Topology.precoverage.{u, v} .smooth B S hS) :=
  isLocalAtSource_smooth_of_schemes B S hS (@Smooth.{u} : MorphismProperty Scheme.{u})
    Smooth.isEtaleLocalOnSourceAndTarget

/-- **Stacks 06FC**, the smooth case. Smoothness of morphisms of algebraic spaces over `S` is
smooth local on the source-and-target.

The source locality hypothesis of Stacks 06FB is Stacks 06F2; the target locality one comes from
the fpqc one (Stacks 0429) along `AlgebraicGeometry.Space.smooth_precoverage_le_fpqc`, and the
postcomposition hypothesis is composition of smooth morphisms (Stacks 03ZD). -/
@[stacks 06FC "smooth"]
theorem isSmoothLocalOnSourceAndTarget_smooth :
    IsSmoothLocalOnSourceAndTarget B S hS (fun _ _ f => IsSmooth B S hS f) := by
  let P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    fun _ _ f => IsSmooth B S hS f
  let Q : MorphismProperty (AlgebraicSpaces B S hS) :=
    P.inverseImage (ObjectProperty.ι fun F => IsAlgebraicSpace B S hS F)
  let : Q.IsLocalAtSource (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    isSmooth_isLocalAtSource_smooth B S hS
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .fpqc B S hS) :=
    smooth_isLocalAtTarget_fpqc B S hS
  let : Q.IsLocalAtTarget (Topology.precoverage.{u, u + 1} .smooth B S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (smooth_precoverage_le_fpqc B S hS)
  exact isSmoothLocalOnSourceAndTarget B S hS P
    (fun hX hY hZ f g hf hg => isSmooth_comp B S hS hX hY hZ f g hf hg)

end AlgebraicGeometry.Space

end
