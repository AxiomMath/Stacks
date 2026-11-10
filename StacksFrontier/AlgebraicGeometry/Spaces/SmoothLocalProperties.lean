module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import Mathlib.Data.List.TFAE
import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Consequences of smooth locality on the source and target (Stacks 06F9, 06FA)

A property of morphisms of algebraic spaces over `S` which is smooth local on the
source-and-target (**Stacks 06F8**) is in particular smooth local on the source and smooth local
on the target in Mathlib's sense, is preserved by postcomposition with a smooth morphism, and
admits the seven equivalent local and covering criteria of **Stacks 06FA**. These are the facts
Stacks 06FM uses to transport such a property to morphisms of algebraic stacks.

All three parts of 06F9 reduce to the third field of 06F8: a property smooth local on the
source-and-target can be tested in a smooth neighbourhood of each point of the source, so each
locality statement is proved by producing, for a given point, a neighbourhood built from the
given covering family. The seven criteria of 06FA are compared the same way, each against the
pointwise condition, using `List.tfae_of_forall` with `P f` as the hub.

## Main results

* `AlgebraicGeometry.Space.isSmoothLocalAtSource`: **Stacks 06F9**, smooth locality on the
  source.
* `AlgebraicGeometry.Space.isSmoothLocalAtTarget`: **Stacks 06F9**, smooth locality on the
  target.
* `AlgebraicGeometry.Space.comp_smooth`: **Stacks 06F9**, preservation under smooth
  postcomposition.
* `AlgebraicGeometry.Space.smoothLocalOnSourceAndTarget_tfae`: **Stacks 06FA**, the seven
  equivalent criteria.

## Implementation notes

The property is a predicate on morphisms of presheaves, while Mathlib's
`CategoryTheory.MorphismProperty.IsLocalAtSource` and `IsLocalAtTarget` are stated for a
property of a category; the two locality results therefore use the inverse image of the property
along the inclusion of `AlgebraicGeometry.AlgebraicSpaces`, and the precoverage is
`AlgebraicGeometry.Space.Topology.smooth.precoverage` of Stacks 03YH.

Two facts that Stacks 041D supplies are proved here instead, because 041D is not in the library:
the identity of an algebraic space is smooth, and an
isomorphism of algebraic spaces is smooth. The first is Stacks 03MJ
(`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_surjectiveChart`) applied to a surjective
étale atlas with the identity as the chart morphism; the second follows from the first and
`CategoryTheory.MorphismProperty.RespectsIso` of the packaged smooth property, which comes from
its base-change stability (Stacks 03ZE). They are public but deliberately untagged: Stacks 041D
is their proper home, and `AlgebraicGeometry.Stack.isAlgebraicStack_schemeFibredCategory` needs
the first of them from outside this file.

No private helpers are needed for the pointwise `pointsMap_comp` and
`pointsMap_id`: they follow from the `@[simp]` lemmas of the same names in
`StacksFrontier/AlgebraicGeometry/Spaces/Points.lean`, stated there as equalities of functions, so
the pointwise form is `congrFun` away.

These are tags of Chapter 74, Descent on Spaces.

## References

* [Stacks Project, Tag 06F9](https://stacks.math.columbia.edu/tag/06F9)
* [Stacks Project, Tag 06FA](https://stacks.math.columbia.edu/tag/06FA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Smoothness of identities and isomorphisms -/

/-- The identity of an algebraic space is smooth: by Stacks 03MJ it suffices to exhibit one
surjective étale chart square, and a surjective étale atlas with the identity as its chart
morphism is one. -/
theorem isSmooth_id {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) : IsSmooth B S hS (𝟙 X) := by
  obtain ⟨U, a, haSurj, haEtale⟩ := hX.exists_atlas
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
    Smooth.isEtaleLocalOnSourceAndTarget hX hX (𝟙 X)).mpr ?_
  refine ⟨U, U, a, a, 𝟙 U, haEtale, haEtale, haSurj, by simp, ?_⟩
  simp only [CategoryTheory.Functor.map_id]
  infer_instance

/-- An isomorphism of algebraic spaces is smooth, by `isSmooth_id` and the fact that the
packaged smooth property respects isomorphisms. -/
theorem isSmooth_of_isIso {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (e : X ⟶ Y) [IsIso e] : IsSmooth B S hS e := by
  let Xsp : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ysp : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let esp : Xsp ⟶ Ysp := ObjectProperty.homMk e
  have : IsIso esp := ⟨ObjectProperty.homMk (inv e),
    ObjectProperty.hom_ext _ (by simp [esp]), ObjectProperty.hom_ext _ (by simp [esp])⟩
  exact MorphismProperty.RespectsIso.precomp (smoothMorphismProperty B S hS)
    esp (𝟙 Ysp) (isSmooth_id B S hS hY)

/-- The pointwise form of `AlgebraicGeometry.Space.pointsMap_id`. -/
theorem pointsMap_id_apply {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : points B S hS F) : pointsMap B S hS F (𝟙 F) x = x :=
  congrFun (pointsMap_id B S hS F) x

/-! ### Stacks 06F9 -/

/-- The inverse image of a smooth local property of morphisms of algebraic spaces under the
inclusion of `AlgebraicSpaces` respects isomorphisms. -/
private theorem respectsIso_inverseImage_of_isSmoothLocalOnSourceAndTarget
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : IsSmoothLocalOnSourceAndTarget B S hS P) :
    (P.inverseImage (ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))).RespectsIso := by
  let C := AlgebraicSpaces B S hS
  let Q : MorphismProperty C := P.inverseImage (ObjectProperty.ι fun F =>
    IsAlgebraicSpace B S hS F)
  have hQpre : ∀ {X Y Z : C} (e : X ⟶ Y) (f : Y ⟶ Z),
      IsIso e → Q f → Q (e ≫ f) := by
    intro X Y Z e f he hf
    change P (e.hom ≫ f.hom)
    change P f.hom at hf
    refine (hP.iff_forall_exists_smooth_neighborhood X.property Z.property
      (e.hom ≫ f.hom)).2 fun x => ?_
    have hpoint : pointsMap B S hS Y.obj (inv e).hom (pointsMap B S hS X.obj e.hom x) = x := by
      rw [← pointsMap_comp_apply B S hS e.hom (inv e).hom x,
        show e.hom ≫ (inv e).hom = 𝟙 X.obj by simp, pointsMap_id_apply]
    have : IsIso (inv e).hom := by
      refine ⟨e.hom, ?_, ?_⟩ <;> simp [← InducedCategory.comp_hom]
    exact ⟨Y.obj, Z.obj, Y.property, Z.property, (inv e).hom, 𝟙 Z.obj,
      f.hom, _, isSmooth_of_isIso B S hS Y.property X.property (inv e).hom,
      isSmooth_id B S hS Z.property, hpoint, by simp, hf⟩
  have hQpost : ∀ {X Y Z : C} (f : X ⟶ Y) (e : Y ⟶ Z),
      IsIso e → Q f → Q (f ≫ e) := by
    intro X Y Z f e he hf
    change P (f.hom ≫ e.hom)
    change P f.hom at hf
    refine (hP.iff_forall_exists_smooth_neighborhood X.property Z.property
      (f.hom ≫ e.hom)).2 fun x => ?_
    have : IsIso e.hom := by
      refine ⟨(inv e).hom, ?_, ?_⟩ <;> simp [← InducedCategory.comp_hom]
    exact ⟨X.obj, Y.obj, X.property, Y.property, 𝟙 X.obj, e.hom, f.hom,
      x, isSmooth_id B S hS X.property,
      isSmooth_of_isIso B S hS Y.property Z.property e.hom,
      pointsMap_id_apply B S hS x, by simp, hf⟩
  exact MorphismProperty.RespectsIso.mk Q
    (fun e f hf => hQpre e.hom f (by infer_instance) hf)
    (fun e f hf => hQpost f e.hom (by infer_instance) hf)

/-- **Stacks 06F9**, smooth locality on the source. A property of morphisms of algebraic spaces
over `S` which is smooth local on the source-and-target is local at the source for the smooth
precoverage. -/
@[stacks 06F9 "smooth_local_source"]
theorem isSmoothLocalAtSource
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : IsSmoothLocalOnSourceAndTarget B S hS P) :
    (P.inverseImage (ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))).IsLocalAtSource
      (Topology.precoverage.{u, v} .smooth B S hS) := by
  let C := AlgebraicSpaces B S hS
  let Q : MorphismProperty C := P.inverseImage (ObjectProperty.ι fun F =>
    IsAlgebraicSpace B S hS F)
  have : Q.RespectsIso :=
    respectsIso_inverseImage_of_isSmoothLocalOnSourceAndTarget B S hS P hP
  refine MorphismProperty.IsLocalAtSource.mk_of_iff (P := Q)
    (K := Topology.precoverage.{u, v} .smooth B S hS) ?_
  intro Xsp Ysp fsp Rsp hR
  obtain ⟨I, Yi, g, hR_eq, hcover⟩ := hR
  rw [hR_eq]
  change Q fsp ↔ ∀ {U : C} (g' : U ⟶ Xsp),
    Presieve.ofArrows Yi g g' → Q (g' ≫ fsp)
  constructor
  · rintro hf U g' ⟨i⟩
    change P ((g i).hom ≫ fsp.hom)
    change P fsp.hom at hf
    exact hP.precomp (X := (Yi i).obj) (Y := Xsp.obj) (Z := Ysp.obj)
      (Yi i).property Xsp.property Ysp.property (g i).hom fsp.hom
      (hcover.2.2.smooth i) hf
  · intro hloc
    refine (hP.iff_forall_exists_smooth_neighborhood
      Xsp.property Ysp.property fsp.hom).2 fun x => ?_
    have hx : x ∈ ⋃ i, Set.range (pointsMap B S hS (Yi i).obj (g i).hom) := by
      rw [hcover.2.2.jointly_surjective]; trivial
    obtain ⟨i, xi, hmap⟩ := Set.mem_iUnion.mp hx
    have hloc_i := hloc (U := Yi i) (g' := g i) (by exact ⟨i⟩)
    change P ((g i).hom ≫ fsp.hom) at hloc_i
    obtain ⟨U, V, hU, hV, a, b, h, u, ha, hb, hux, hcomm, hPh⟩ :=
      (hP.iff_forall_exists_smooth_neighborhood
        (Yi i).property Ysp.property ((g i).hom ≫ fsp.hom)).1 hloc_i xi
    have hax : pointsMap B S hS U (a ≫ (g i).hom) u = x := by
      rw [pointsMap_comp_apply, hux, hmap]
    have hAsmooth : IsSmooth B S hS (a ≫ (g i).hom) :=
      isSmooth_comp B S hS hU (Yi i).property Xsp.property
        a (g i).hom ha (hcover.2.2.smooth i)
    refine ⟨U, V, hU, hV, a ≫ (g i).hom, b, h, u, hAsmooth, hb, hax, ?_, hPh⟩
    simpa only [Category.assoc] using hcomm

/-- **Stacks 06F9**, smooth locality on the target. A property of morphisms of algebraic spaces
over `S` which is smooth local on the source-and-target is local at the target for the smooth
precoverage. -/
@[stacks 06F9 "smooth_local_target"]
theorem isSmoothLocalAtTarget
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : IsSmoothLocalOnSourceAndTarget B S hS P) :
    (P.inverseImage (ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))).IsLocalAtTarget
      (Topology.precoverage.{u, v} .smooth B S hS) := by
  let C := AlgebraicSpaces B S hS
  let Q : MorphismProperty C := P.inverseImage
    (ObjectProperty.ι fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F)
  have : Q.RespectsIso :=
    respectsIso_inverseImage_of_isSmoothLocalOnSourceAndTarget B S hS P hP
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff (P := Q)
    (K := Topology.precoverage.{u, v} .smooth B S hS) ?_
  intro Xsp Ysp fsp Rsp hR
  obtain ⟨I, Yi, g, hR_eq, hcover⟩ := hR
  rw [hR_eq]
  change Q fsp ↔ ∀ {U : C} (g' : U ⟶ Ysp) [HasPullback fsp g'],
    Presieve.ofArrows Yi g g' → Q (pullback.snd fsp g')
  constructor
  · rintro hf U g' _ ⟨i⟩
    have hpull : P (pullback.snd fsp.hom (g i).hom) :=
      hP.pullbackSnd_of_smooth Xsp.property Ysp.property (Yi i).property fsp.hom (g i).hom
        hf (hcover.2.2.smooth i)
    have hsqPull : IsPullback (pullback.fst fsp (g i))
        (pullback.snd fsp (g i)) fsp (g i) :=
      IsPullback.of_hasPullback fsp (g i)
    let hsqFiber := AlgebraicSpaces.isPullback_fiberProduct B S hS fsp (g i)
    let e := hsqPull.isoIsPullback Xsp (Yi i) hsqFiber
    let fiberSnd : AlgebraicSpaces.fiberProduct B S hS fsp (g i) ⟶ Yi i :=
      ObjectProperty.homMk (pullback.snd fsp.hom (g i).hom)
    have hrel : e.hom ≫ fiberSnd = pullback.snd fsp (g i) :=
      IsPullback.isoIsPullback_hom_snd Xsp (Yi i) hsqPull hsqFiber
    rw [← hrel]
    exact MorphismProperty.RespectsIso.precomp Q e.hom fiberSnd hpull
  · intro hloc
    refine (hP.iff_forall_exists_smooth_neighborhood
      Xsp.property Ysp.property fsp.hom).2 fun x => ?_
    have hxY : pointsMap B S hS Xsp.obj fsp.hom x ∈
        ⋃ i, Set.range (pointsMap B S hS (Yi i).obj (g i).hom) := by
      rw [hcover.2.2.jointly_surjective]
      trivial
    obtain ⟨i, yi, hmap⟩ := Set.mem_iUnion.mp hxY
    obtain ⟨wi, -, hfst⟩ :=
      exists_point_of_isPullback B S hS
        (IsPullback.of_hasPullback fsp (g i)).flip yi x hmap
    exact ⟨(pullback fsp (g i)).obj, (Yi i).obj, (pullback fsp (g i)).property,
      (Yi i).property, (pullback.fst fsp (g i)).hom, (g i).hom,
      (pullback.snd fsp (g i)).hom, wi,
      (isSmooth_isStableUnderBaseChange B S hS).of_isPullback
        (IsPullback.of_hasPullback fsp (g i)).flip (hcover.2.2.smooth i),
      hcover.2.2.smooth i, hfst,
      congrArg InducedCategory.Hom.hom
        (pullback.condition (f := fsp) (g := g i)).symm, hloc (g i) (by exact ⟨i⟩)⟩

/-- **Stacks 06F9**, smooth postcomposition. A property of morphisms of algebraic spaces over
`S` which is smooth local on the source-and-target is preserved by postcomposition with a smooth
morphism. -/
@[stacks 06F9 "smooth_postcomposition"]
theorem comp_smooth
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : IsSmoothLocalOnSourceAndTarget B S hS P)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : P f) (hg : IsSmooth B S hS g) : P (f ≫ g) := by
  apply (hP.iff_forall_exists_smooth_neighborhood hX hZ (f ≫ g)).2
  intro x
  obtain ⟨U, V, hU, hV, a, b, h, u, ha, hb, hax, hcomm, hPh⟩ :=
    (hP.iff_forall_exists_smooth_neighborhood hX hY f).1 hf x
  refine ⟨U, V, hU, hV, a, b ≫ g, h, u, ha,
    isSmooth_comp B S hS hV hY hZ b g hb hg, hax, ?_, hPh⟩
  simp only [← Category.assoc, hcomm]

/-! ### Stacks 06FA -/

/-- The constant family at an algebraic space over `S`, with the identity as every structure
map, is a smooth covering of it. Joint surjectivity is carried by any one member, so the index
type only has to be nonempty. -/
public theorem isSmoothCovering_const_id {I : Type v} [Nonempty I]
    (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z) :
    IsSmoothCovering B S hS (fun _ : I => Z) (fun _ => 𝟙 Z) :=
  ⟨hZ, fun _ => hZ, fun _ => isSmooth_id B S hS hZ, Set.eq_univ_of_forall fun x =>
    Set.mem_iUnion.mpr ⟨Classical.arbitrary I, Set.mem_range.mpr ⟨x, pointsMap_id_apply B S hS x⟩⟩⟩

/-- A point of the source and a point of a smooth cover of the target with the same image in the
target come from a point of the fibre product, whose first projection is smooth. -/
private theorem exists_smooth_pullback_point
    {X Y V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hV : IsAlgebraicSpace B S hS V)
    (f : X ⟶ Y) (b : V ⟶ Y) (hb : IsSmooth B S hS b)
    (x : points B S hS X) (y : points B S hS V)
    (hy : pointsMap B S hS V b y = pointsMap B S hS X f x) :
    ∃ w : points B S hS (pullback f b),
      pointsMap B S hS (pullback f b) (pullback.fst f b) w = x ∧
      IsSmooth B S hS (pullback.fst f b) := by
  let Xsp : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ysp : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Vsp : AlgebraicSpaces B S hS := ⟨V, hV⟩
  let fsp : Xsp ⟶ Ysp := ObjectProperty.homMk f
  let bsp : Vsp ⟶ Ysp := ObjectProperty.homMk b
  let W : AlgebraicSpaces B S hS :=
    ⟨pullback f b, isAlgebraicSpace_pullback B S hS f b hX hV hY⟩
  have hsq : IsPullback
      (ObjectProperty.homMk (pullback.fst f b) : W ⟶ Xsp)
      (ObjectProperty.homMk (pullback.snd f b) : W ⟶ Vsp) fsp bsp := by
    apply IsPullback.of_map (ObjectProperty.ι _)
    · exact ObjectProperty.hom_ext _ pullback.condition
    · simpa [W, fsp, bsp, Xsp, Ysp, Vsp] using (IsPullback.of_hasPullback f b)
  obtain ⟨w, _, hw⟩ := exists_point_of_isPullback B S hS hsq.flip y x hy
  exact ⟨w, hw, (isSmooth_isStableUnderBaseChange B S hS).of_isPullback hsq.flip hb⟩

/-- **Stacks 06FA.** Seven equivalent criteria for a morphism of algebraic spaces over `S` to
have a property which is smooth local on the source-and-target: the property itself; a smooth
neighbourhood of every point of the source on which it holds; one smooth diagram surjective on
the source; every smooth comparison into a fibre product over a smooth base change; a smooth
covering of the target over which the base changes have it; a smooth covering of the source whose
composites have it; and a smooth covering of the target refined by smooth coverings of the
corresponding fibre products. -/
@[stacks 06FA]
theorem smoothLocalOnSourceAndTarget_tfae
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hP : IsSmoothLocalOnSourceAndTarget B S hS P)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE [
      P f,
      (∀ x : points B S hS X,
        ∃ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (_hU : IsAlgebraicSpace B S hS U)
          (_hV : IsAlgebraicSpace B S hS V)
          (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V)
          (u : points B S hS U),
          IsSmooth B S hS a ∧
            IsSmooth B S hS b ∧
            pointsMap B S hS U a u = x ∧
            h ≫ b = a ≫ f ∧ P h),
      (∃ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (_hU : IsAlgebraicSpace B S hS U)
          (_hV : IsAlgebraicSpace B S hS V)
          (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V),
          IsSmooth B S hS a ∧
            IsSurjective B S hS a ∧
            IsSmooth B S hS b ∧
            h ≫ b = a ≫ f ∧ P h),
      (∀ (U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (_hU : IsAlgebraicSpace B S hS U)
          (_hV : IsAlgebraicSpace B S hS V)
          (b : V ⟶ Y) (k : U ⟶ pullback f b),
          IsSmooth B S hS b →
          IsSmooth B S hS k →
          P (k ≫ pullback.snd f b)),
      (∃ (I : Type v)
          (V : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (b : ∀ i, V i ⟶ Y),
          IsSmoothCovering B S hS V b ∧
          ∀ i, P (pullback.snd f (b i))),
      (∃ (I : Type v)
          (U : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (a : ∀ i, U i ⟶ X),
          IsSmoothCovering B S hS U a ∧
          ∀ i, P (a i ≫ f)),
      (∃ (I : Type v)
          (V : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (b : ∀ i, V i ⟶ Y)
          (J : I → Type w)
          (U : ∀ i, J i → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
          (a : ∀ i j, U i j ⟶ pullback f (b i)),
          IsSmoothCovering B S hS V b ∧
          (∀ i, IsSmoothCovering B S hS (U i) (a i)) ∧
          (∀ i j, P (a i j ≫ pullback.snd f (b i))))
    ] := by
  classical
  have hIdY := isSmooth_id B S hS hY
  have hPointwise := hP.iff_forall_exists_smooth_neighborhood hX hY f
  refine List.tfae_of_forall (b := P f) ?_
  intro Q hQ
  simp only [List.mem_cons, List.not_mem_nil] at hQ
  rcases hQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hQ
  · exact Iff.rfl
  · exact hPointwise.symm
  · constructor
    · rintro ⟨U, V, hU, hV, a, b, h, has, hsurj, hbs, hcomm, hph⟩
      refine hPointwise.mpr fun x => ?_
      obtain ⟨u, hu⟩ := hsurj x
      exact ⟨U, V, hU, hV, a, b, h, u, has, hbs, hu, hcomm, hph⟩
    · intro ha
      refine ⟨X, Y, hX, hY, 𝟙 X, 𝟙 Y, f, isSmooth_id B S hS hX, ?_, hIdY, by simp, ha⟩
      change Function.Surjective (pointsMap B S hS X (𝟙 X))
      exact fun x => ⟨x, pointsMap_id_apply B S hS x⟩
  · constructor
    · intro hd
      have hW := isAlgebraicSpace_pullback B S hS f (𝟙 Y) hX hY hY
      have hp : P (pullback.snd f (𝟙 Y)) := by
        simpa using hd (pullback f (𝟙 Y)) Y hW hY (𝟙 Y)
          (𝟙 (pullback f (𝟙 Y))) hIdY (isSmooth_id B S hS hW)
      refine hPointwise.mpr fun x => ?_
      obtain ⟨w, hwX, hfst⟩ := exists_smooth_pullback_point B S hS hX hY hY
        f (𝟙 Y) hIdY x (pointsMap B S hS X f x) (pointsMap_id_apply B S hS _)
      exact ⟨pullback f (𝟙 Y), Y, hW, hY, pullback.fst f (𝟙 Y), 𝟙 Y,
        pullback.snd f (𝟙 Y), w, hfst, hIdY, hwX, by
          simpa using (pullback.condition (f := f) (g := 𝟙 Y)).symm, hp⟩
    · intro ha U V hU hV b k hb hk
      exact hP.precomp hU (isAlgebraicSpace_pullback B S hS f b hX hV hY) hV k
        (pullback.snd f b) hk (hP.pullbackSnd_of_smooth hX hY hV f b ha hb)
  · constructor
    · rintro ⟨I, V, b, hcover, hlocal⟩
      refine hPointwise.mpr fun x => ?_
      have hy : pointsMap B S hS X f x ∈
          ⋃ i, Set.range (pointsMap B S hS (V i) (b i)) := by
        rw [hcover.jointly_surjective]
        trivial
      obtain ⟨i, yi, hyi⟩ := Set.mem_iUnion.mp hy
      obtain ⟨w, hwX, hfst⟩ := exists_smooth_pullback_point B S hS hX hY
        (hcover.source_isAlgebraicSpace i) f (b i) (hcover.smooth i) x yi hyi
      exact ⟨pullback f (b i), V i,
        isAlgebraicSpace_pullback B S hS f (b i) hX
          (hcover.source_isAlgebraicSpace i) hY, hcover.source_isAlgebraicSpace i,
        pullback.fst f (b i), b i, pullback.snd f (b i), w,
        hfst, hcover.smooth i, hwX, (pullback.condition).symm,
        hlocal i⟩
    · intro ha
      exact ⟨PUnit.{v+1}, fun _ => Y, fun _ => 𝟙 Y, isSmoothCovering_const_id B S hS Y hY,
        fun _ => hP.pullbackSnd_of_smooth hX hY hY f (𝟙 Y) ha hIdY⟩
  · constructor
    · rintro ⟨I, U, a, hcover, hlocal⟩
      refine hPointwise.mpr fun x => ?_
      have hx : x ∈ ⋃ i, Set.range (pointsMap B S hS (U i) (a i)) := by
        rw [hcover.jointly_surjective]
        trivial
      obtain ⟨i, ui, hxi⟩ := Set.mem_iUnion.mp hx
      exact ⟨U i, Y, hcover.source_isAlgebraicSpace i, hY, a i, 𝟙 Y,
        a i ≫ f, ui, hcover.smooth i, hIdY, hxi, by simp, hlocal i⟩
    · intro hf
      exact ⟨PUnit.{v+1}, fun _ => X, fun _ => 𝟙 X, isSmoothCovering_const_id B S hS X hX,
        fun _ => by simpa using hf⟩
  · constructor
    · rintro ⟨I, V, b, J, U, a, hV, hU, hlocal⟩
      refine hPointwise.mpr fun x => ?_
      have hy : pointsMap B S hS X f x ∈
          ⋃ i, Set.range (pointsMap B S hS (V i) (b i)) := by
        rw [hV.jointly_surjective]
        trivial
      obtain ⟨i, yi, hyi⟩ := Set.mem_iUnion.mp hy
      obtain ⟨w, hwX, hfst⟩ := exists_smooth_pullback_point B S hS hX hY
        (hV.source_isAlgebraicSpace i) f (b i) (hV.smooth i) x yi hyi
      have hwi : w ∈ ⋃ j, Set.range (pointsMap B S hS (U i j) (a i j)) := by
        rw [(hU i).jointly_surjective]
        trivial
      obtain ⟨j, uj, hju⟩ := Set.mem_iUnion.mp hwi
      exact ⟨U i j, V i, (hU i).source_isAlgebraicSpace j,
        hV.source_isAlgebraicSpace i, a i j ≫ pullback.fst f (b i), b i,
        a i j ≫ pullback.snd f (b i), uj,
        isSmooth_comp B S hS
          ((hU i).source_isAlgebraicSpace j)
          (isAlgebraicSpace_pullback B S hS f (b i) hX
            (hV.source_isAlgebraicSpace i) hY) hX
          (a i j) (pullback.fst f (b i)) ((hU i).smooth j) hfst,
        hV.smooth i,
        by rw [pointsMap_comp_apply, hju, hwX],
        by simp only [Category.assoc, pullback.condition],
        hlocal i j⟩
    · intro ha
      have hW := isAlgebraicSpace_pullback B S hS f (𝟙 Y) hX hY hY
      exact ⟨PUnit.{v+1}, fun _ => Y, fun _ => 𝟙 Y, fun _ => PUnit.{w+1},
        fun _ _ => pullback f (𝟙 Y), fun _ _ => 𝟙 (pullback f (𝟙 Y)),
        isSmoothCovering_const_id B S hS Y hY,
        fun _ => isSmoothCovering_const_id B S hS _ hW,
        fun _ _ => by simpa using hP.pullbackSnd_of_smooth hX hY hY f (𝟙 Y) ha hIdY⟩
  · cases hQ

end AlgebraicGeometry.Space

end
