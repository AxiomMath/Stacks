module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.OverField.Morphisms.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.PointwiseComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint

/-!
# Constant dimension of a groupoid over a field

Let `G` be a groupoid in algebraic spaces over a base algebraic space whose space of objects is
the spectrum of a field `k`, viewed as an algebraic space through Yoneda, and assume the source
and the target of `G` are locally of finite type. Then the space of arrows of `G` has the same
dimension at every one of its points, so that its dimension is that common value; the
transcendence degree over `k` of a point of the arrow space is the same measured through the
source and through the target; and at a point of transcendence degree zero the dimension of the
arrow space is the dimension of the local ring there.

The point of the proof is that for every point `x` of the arrow space there is a cartesian
square identifying the dimension at `x` with the dimension at the identity arrow of the single
point of the object space. Left translation by the family of arrows determined by `x` turns the
square cutting out the arrows with prescribed target into the square cutting out the arrows with
prescribed source, and over a field a relative dimension at a point is an absolute one.

## Main results

* `AlgebraicGeometry.Space.dimension_eq_dimensionAtPoint`: over a field the dimension of the
  arrow space is its dimension at every point.
* `AlgebraicGeometry.Space.hasTranscendenceDegreeAt_source_iff_target`: the transcendence
  degree of a point of the arrow space over the field does not depend on which of the two
  structure morphisms measures it.
* `AlgebraicGeometry.Space.dimension_eq_localRingDimension_of_hasTranscendenceDegreeAt_zero`:
  at a point of transcendence degree zero the dimension of the arrow space is the dimension of
  the local ring.

## Implementation notes

The dimension of an algebraic space and its dimension at a point are the extended values of
Stacks 04N6 and 04N5, taken in `WithBot ℕ∞` through `topologicalKrullDimAt`.

Two facts carry the geometry. Over the spectrum of a field relative dimension at a point is
absolute dimension at that point, which is
`AlgebraicGeometry.Space.relativeDimensionAt_fieldTarget_iff_dimensionAtPoint`; and relative
dimension at a point is invariant under base change along a morphism locally of finite type,
which is part (1) of Stacks 04NS. The only new geometric input is left translation, built here
for a groupoid in functors from the pointwise cartesian square
`Deformation.PointwiseGroupoid.isPullback_comp_fst`.

The source assumes both the source and the target of the groupoid locally of finite type. For
constant dimension only the target hypothesis is used, so it is carried there as `_hs`: over a
field the inverse of the groupoid exchanges the two, and the statement is kept with the
hypotheses the source gives it. The two transcendence degrees are compared on one étale chart
of the arrow space whose chart of the object space is the field spectrum itself, where the
comparison is Stacks 04LU for two morphisms of schemes into the spectrum of a field.

The dimension of the local ring at a point, Stacks 04NA, is the Krull dimension of the local
ring of an étale scheme chart at a point above it, which is what the source writes
`dim 𝒪_{R, r̄}`. That it is the dimension at a point of transcendence degree zero holds for an
arbitrary algebraic space locally of finite type over the spectrum of a field, and is proved in
that generality: such a point is a closed point of a chart by Stacks 01TE, and at a closed
point of a scheme locally of finite type over a field the local dimension is the Krull
dimension of the local ring by Stacks 0A21.

This module is in `AlgebraicGeometry.Space` rather than in
`AlgebraicGeometry.GroupoidInAlgebraicSpaces`, which the majority of its siblings use, because
all of the dimension and point vocabulary it speaks (`points`, `FieldValuedPoint`,
`dimensionAtPoint`, `IsLocallyOfFiniteType`) lives in `AlgebraicGeometry.Space`.

## References

* [Stacks Project, Tag 06FD](https://stacks.math.columbia.edu/tag/06FD)
* [Stacks Project, Tag 04LU](https://stacks.math.columbia.edu/tag/04LU)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 01TE](https://stacks.math.columbia.edu/tag/01TE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

/-- Pullbacks of functors into types, supplied directly: instance search for them times out. -/
private instance (priority := high) hasPullback_functorToTypes {D : Type v} [Category.{w} D]
    {X Y Z : D ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g :=
  have : HasPullbacks (D ⥤ Type u) := functorCategoryHasLimitsOfShape
  inferInstance

/-! ### Left translation in a groupoid in functors -/

/-- The composite of a composable pair whose second arrow is the identity at the source of the
first is the first arrow. -/
private theorem compose_identity {D : Type v} [Category.{w} D]
    (G : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D) (a : G.arrows.obj T)
    (h : G.source.app T a = G.target.app T (G.identity T (G.source.app T a))) :
    G.compose T a (G.identity T (G.source.app T a)) h = a := by
  let f := (G.evaluationArrowEquiv T _ _).symm ⟨a, rfl, rfl⟩
  have hc := G.evaluationArrowEquiv_comp T
    (𝟙 (show G.Evaluation T from G.source.app T a)) f
  simpa [f] using hc.symm

section LeftTranslate

variable {D : Type v} [Category.{w} D] (G : Deformation.GroupoidInFunctors.{v, w, u} D)
  {F : D ⥤ Type u} (a : F ⟶ G.arrows)

/-- Left translation by a family `a` of arrows indexed by `F`: on the space of pairs of a point
`y` of `F` and an arrow whose target is the source of `a y`, compose with `a y`. -/
private noncomputable def leftTranslate :
    pullback G.target (a ≫ G.source) ⟶ G.arrows :=
  (show pullback G.target (a ≫ G.source) ⟶
      Deformation.composableArrows G.objects G.arrows G.source G.target from
    { app := fun T => ↾ fun z =>
        ⟨(a.app T ((pullback.snd G.target (a ≫ G.source)).app T z),
          (pullback.fst G.target (a ≫ G.source)).app T z),
          (congrArg (fun φ => φ.app T z)
            (pullback.condition (f := G.target) (g := a ≫ G.source))).symm⟩
      naturality := by
        intro X Y f
        ext z
        simp [Deformation.composableArrows, NatTrans.naturality_apply] }) ≫ G.comp

/-- Left translation by `a` identifies the arrows with prescribed source with the arrows with
prescribed target: it fits into a cartesian square with the target morphism. -/
private theorem leftTranslate_isPullback :
    IsPullback (leftTranslate G a) (pullback.snd G.target (a ≫ G.source))
      G.target (a ≫ G.target) := by
  classical
  apply IsPullback.of_forall_isPullback_app
  intro T
  let p := (pullback.fst G.target (a ≫ G.source)).app T
  let q := (pullback.snd G.target (a ≫ G.source)).app T
  have hpq : IsPullback p q (G.target.app T) ((a ≫ G.source).app T) :=
    (IsPullback.of_hasPullback G.target (a ≫ G.source)).app T
  have hmem : ∀ z, G.source.app T (a.app T (q z)) = G.target.app T (p z) := fun z =>
    (congrArg (fun φ => φ z) hpq.w).symm
  let H := G.pointwiseData T
  have hcf := H.isPullback_comp_fst
  refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · ext z
    exact H.target_comp (a.app T (q z)) (p z) (hmem z)
  · intro x y hxy
    refine Types.ext_of_isPullback hpq ?_ hxy.2
    have hcp : (⟨(a.app T (q x), p x), hmem x⟩ :
        { z : G.arrows.obj T × G.arrows.obj T //
          G.source.app T z.1 = G.target.app T z.2 }) =
        ⟨(a.app T (q y), p y), hmem y⟩ :=
      Types.ext_of_isPullback hcf (congrArg (a.app T) hxy.2) hxy.1
    exact congrArg (fun z => z.1.2) hcp
  · intro b l hbl
    obtain ⟨c, hc₁, hc₂⟩ := Types.exists_of_isPullback hcf (a.app T l) b hbl.symm
    have hc₁' : c.1.1 = a.app T l := hc₁
    have hsrc : G.target.app T c.1.2 = (a ≫ G.source).app T l := by
      change _ = G.source.app T (a.app T l)
      rw [← hc₁']
      exact c.2.symm
    obtain ⟨z, hz, hl⟩ := Types.exists_of_isPullback hpq c.1.2 l hsrc
    refine ⟨z, ?_, hl⟩
    have hcp : (⟨(a.app T (q z), p z), hmem z⟩ :
        { y : G.arrows.obj T × G.arrows.obj T //
          G.source.app T y.1 = G.target.app T y.2 }) = c := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · change a.app T (q z) = c.1.1
        rw [show q z = l from hl, hc₁']
      · exact hz
    exact (congrArg (G.comp.app T) hcp).trans hc₂

/-- The identity arrow at the source of `a y` lifts to the apex of the left translation square,
where left translation sends it to `a y`. -/
private theorem exists_leftTranslate_eq_of_identity (T : D) (y : F.obj T) :
    ∃ w : (pullback G.target (a ≫ G.source)).obj T,
      (pullback.snd G.target (a ≫ G.source)).app T w = y ∧
      (pullback.fst G.target (a ≫ G.source)).app T w =
        G.identity T (G.source.app T (a.app T y)) ∧
      (leftTranslate G a).app T w = a.app T y := by
  obtain ⟨w, hw, hqw⟩ := Types.exists_of_isPullback
    ((IsPullback.of_hasPullback G.target (a ≫ G.source)).app T)
    (G.identity T (G.source.app T (a.app T y))) y
    (by
      change _ = G.source.app T (a.app T y)
      exact (G.evaluationArrowEquiv T _ _
        (𝟙 (show G.Evaluation T from G.source.app T (a.app T y)))).property.2)
  refine ⟨w, hqw, hw, ?_⟩
  change G.compose T (a.app T ((pullback.snd G.target (a ≫ G.source)).app T w))
    ((pullback.fst G.target (a ≫ G.source)).app T w) _ = a.app T y
  simp only [hqw, hw]
  exact compose_identity G T (a.app T y) _

end LeftTranslate

/-! ### The dimension at a point over a field -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism locally of finite type stays locally of finite type after its target is
identified with another presheaf. -/
private theorem isLocallyOfFiniteType_comp_eqToHom
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (h : Y = Y')
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS (f ≫ eqToHom h) := by
  subst h
  simpa using hf

/-- The presheaf represented by the spectrum of a field over the base has exactly one point:
every field-valued point of it dominates the canonical one. -/
private theorem points_subsingleton_of_eq_yoneda_field
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
    (structureMap : Spec (.of k) ⟶ S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : F = yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (y₁ y₂ : points B S hS F) : y₁ = y₂ := by
  classical
  subst hF
  let V : BigFppfOver B S hS := Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)
  let p₀ : FieldValuedPoint B S hS (yoneda.obj V) :=
    { carrier := k, field := inferInstance, contained := hk,
      toBase := structureMap, value := 𝟙 V }
  have key : ∀ p : FieldValuedPoint B S hS (yoneda.obj V),
      p.class B S hS (yoneda.obj V) = p₀.class B S hS (yoneda.obj V) := by
    intro p
    refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _ ?_
    refine ⟨p, FieldValuedPoint.dominates_refl B S hS _ p, p.value, ?_⟩
    change p.value ≫ 𝟙 V = p.value
    exact Category.comp_id p.value
  obtain ⟨p₁, h₁⟩ := Quot.exists_rep y₁
  obtain ⟨p₂, h₂⟩ := Quot.exists_rep y₂
  rw [← h₁, ← h₂]
  exact (key p₁).trans (key p₂).symm

/-- In a cartesian square whose two lower corners are spectra of fields, the dimension at a
point of the upper left corner is the dimension at its image in the upper right corner.

Over a field relative dimension at a point is absolute dimension at that point, and relative
dimension at a point is invariant under base change along a morphism locally of finite type. -/
private theorem dimensionAtPoint_eq_of_isPullback_fieldTarget
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (p' : FieldValuedPoint B S hS Y') (p : FieldValuedPoint B S hS Y)
    {g' : X' ⟶ X} {f' : X' ⟶ yoneda.obj (p'.siteObject B S hS Y')}
    {f : X ⟶ yoneda.obj (p.siteObject B S hS Y)}
    {g : yoneda.obj (p'.siteObject B S hS Y') ⟶ yoneda.obj (p.siteObject B S hS Y)}
    (sq : IsPullback g' f' f g) (hf : IsLocallyOfFiniteType B S hS f)
    (x' : points B S hS X') :
    dimensionAtPoint B S hS X hX (pointsMap B S hS X' g' x') =
      dimensionAtPoint B S hS X' hX' x' := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp
    (dimensionAtPoint_ne_bot B S hS X hX (pointsMap B S hS X' g' x'))
  have h₁ := relativeDimensionAt_fieldTarget_iff_dimensionAtPoint B S hS hX p f
    (pointsMap B S hS X' g' x') d
  have h₂ := hasRelativeDimensionAt_iff_of_isPullback B S hS sq hX
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) hf x' d
  have h₃ := relativeDimensionAt_fieldTarget_iff_dimensionAtPoint B S hS hX' p' f' x' d
  rw [← hd]
  exact (h₃.mp (h₂.mp (h₁.mpr hd.symm))).symm

/-- **Stacks 06FD**, the key step. For a groupoid in algebraic spaces whose object space is the
spectrum of a field and whose target is locally of finite type, the dimension of the arrow space
at a point equals its dimension at the identity arrow over the source of that point.

Left translation by the family of arrows the point determines carries the square cutting out the
arrows with prescribed source onto the square cutting out the arrows with prescribed target;
both squares are cartesian over the spectrum of the field, so both of their apex dimensions
agree with the dimension at the given point. -/
private theorem dimensionAtPoint_eq_identity_image
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
    (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (objects_eq : G.objects = _root_.AlgebraicGeometry.schemeSpace
      (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (ht : IsLocallyOfFiniteType B S hS G.target.hom)
    (e : G.objects.obj ⟶ G.arrows.obj)
    (he : ∀ T x, e.app T x = G.toGroupoidInFunctors.identity T x)
    (p : FieldValuedPoint B S hS G.arrows.obj) :
    dimensionAtPoint B S hS G.arrows.obj G.arrows.property
        (p.class B S hS G.arrows.obj) =
      dimensionAtPoint B S hS G.arrows.obj G.arrows.property
        ((FieldValuedPoint.map B S hS G.objects.obj e
          (FieldValuedPoint.map B S hS G.arrows.obj G.source.hom p)).class B S hS
            G.arrows.obj) := by
  classical
  let H := G.toGroupoidInFunctors
  let V : BigFppfOver B S hS := Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)
  have hU : G.objects.obj = yoneda.obj V := congrArg (fun Z => Z.obj) objects_eq
  let T : BigFppfOver B S hS := p.siteObject B S hS G.arrows.obj
  let a : yoneda.obj T ⟶ G.arrows.obj := yonedaEquiv.symm p.value
  let P := pullback G.target.hom (a ≫ G.source.hom)
  let π := pullback.fst G.target.hom (a ≫ G.source.hom)
  let q := pullback.snd G.target.hom (a ≫ G.source.hom)
  let τ : P ⟶ G.arrows.obj := leftTranslate H a
  have hP : IsAlgebraicSpace B S hS P :=
    isAlgebraicSpace_pullback B S hS G.target.hom (a ≫ G.source.hom) G.arrows.property
      (isAlgebraicSpace_yoneda B S hS T) G.objects.property
  have hπ : IsPullback π q G.target.hom (a ≫ G.source.hom) :=
    IsPullback.of_hasPullback G.target.hom (a ≫ G.source.hom)
  have hτ : IsPullback τ q G.target.hom (a ≫ G.target.hom) :=
    leftTranslate_isPullback H a
  let p₀ : FieldValuedPoint B S hS (yoneda.obj V) :=
    { carrier := k, field := inferInstance, contained := hk,
      toBase := structureMap, value := 𝟙 V }
  let f : G.arrows.obj ⟶ yoneda.obj (p₀.siteObject B S hS (yoneda.obj V)) :=
    G.target.hom ≫ eqToHom hU
  have hf : IsLocallyOfFiniteType B S hS f :=
    isLocallyOfFiniteType_comp_eqToHom B S hS G.target.hom hU ht
  have ha : a.app (Opposite.op T) (𝟙 T) = p.value := yonedaEquiv.apply_symm_apply p.value
  obtain ⟨w, -, hw, hwτ'⟩ := exists_leftTranslate_eq_of_identity H a (Opposite.op T) (𝟙 T)
  let r : FieldValuedPoint B S hS P :=
    { carrier := p.carrier, field := p.field, contained := p.contained,
      toBase := p.toBase, value := w }
  have hwπ : π.app (Opposite.op T) w =
      e.app (Opposite.op T) (G.source.hom.app (Opposite.op T) p.value) := by
    rw [he]
    exact hw.trans (congrArg (fun x => H.identity _ (G.source.hom.app _ x)) ha)
  have hwτ : τ.app (Opposite.op T) w = p.value := hwτ'.trans ha
  have hmapπ : FieldValuedPoint.map B S hS P π r =
      FieldValuedPoint.map B S hS G.objects.obj e
        (FieldValuedPoint.map B S hS G.arrows.obj G.source.hom p) := by
    dsimp [FieldValuedPoint.map, r]
    congr 1
  have hmapτ : FieldValuedPoint.map B S hS P τ r = p := by
    cases p
    dsimp [FieldValuedPoint.map, r]
    congr 1
  have key : ∀ (t : P ⟶ G.arrows.obj) (φ : G.arrows.obj ⟶ G.objects.obj),
      IsPullback t q G.target.hom (a ≫ φ) →
      dimensionAtPoint B S hS G.arrows.obj G.arrows.property
          (pointsMap B S hS P t (r.class B S hS P)) =
        dimensionAtPoint B S hS P hP (r.class B S hS P) := by
    intro t φ sq
    have sq' : IsPullback t q f (a ≫ φ ≫ eqToHom hU) :=
      sq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (eqToIso hU)
        (by simp) (by simp) (by simp [f]) (by simp)
    exact dimensionAtPoint_eq_of_isPullback_fieldTarget B S hS hP G.arrows.property p p₀ sq' hf _
  have dπ := key π _ hπ
  have dτ := key τ _ hτ
  rw [pointsMap_class, hmapπ] at dπ
  rw [pointsMap_class, hmapτ] at dτ
  exact dτ.trans dπ.symm

/-- **Stacks 06FD.** Let `G` be a groupoid in algebraic spaces over `S` whose space of objects
is the spectrum of a field `k`, viewed as an algebraic space through Yoneda, and whose source
and target are locally of finite type. Then the dimension of the space of arrows of `G` equals
its dimension at every one of its points. -/
@[stacks 06FD "constant dimension of the arrow space"]
theorem dimension_eq_dimensionAtPoint
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
    (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (objects_eq : G.objects = _root_.AlgebraicGeometry.schemeSpace
      (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (_hs : IsLocallyOfFiniteType B S hS G.source.hom)
    (ht : IsLocallyOfFiniteType B S hS G.target.hom)
    (r : points B S hS G.arrows.obj) :
    dimension B S hS G.arrows.obj G.arrows.property =
      dimensionAtPoint B S hS G.arrows.obj G.arrows.property r := by
  classical
  obtain ⟨e₀, he₀, -⟩ := Deformation.existsUnique_identity G.toGroupoidInFunctors
  let e : G.objects.obj ⟶ G.arrows.obj := e₀
  have he : ∀ T x, e.app T x = G.toGroupoidInFunctors.identity T x := he₀
  have hU : G.objects.obj =
      yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)) :=
    congrArg (fun Z => Z.obj) objects_eq
  have hsub := points_subsingleton_of_eq_yoneda_field B S hS hk structureMap hU
  have hdim : ∀ x : points B S hS G.arrows.obj,
      dimensionAtPoint B S hS G.arrows.obj G.arrows.property x =
        dimensionAtPoint B S hS G.arrows.obj G.arrows.property
          (pointsMap B S hS G.objects.obj e
            (pointsMap B S hS G.arrows.obj G.source.hom r)) := by
    intro x
    obtain ⟨p, hp⟩ := Quot.exists_rep x
    have hstep : (FieldValuedPoint.map B S hS G.objects.obj e
        (FieldValuedPoint.map B S hS G.arrows.obj G.source.hom p)).class B S hS
          G.arrows.obj =
        pointsMap B S hS G.objects.obj e
          (pointsMap B S hS G.arrows.obj G.source.hom
            (p.class B S hS G.arrows.obj)) := rfl
    rw [← hp, dimensionAtPoint_eq_identity_image B S hS hk structureMap G objects_eq ht
      e he p, hstep]
    exact congrArg (fun y => dimensionAtPoint B S hS G.arrows.obj G.arrows.property
      (pointsMap B S hS G.objects.obj e y)) (hsub _ _)
  exact le_antisymm (iSup_le fun x => ((hdim x).trans (hdim r).symm).le)
    (le_iSup (dimensionAtPoint B S hS G.arrows.obj G.arrows.property) r)

/-! ### The transcendence degree through the source and through the target -/

/-- The pointed étale chart of a morphism to a representable presheaf given by an étale chart of
its source, the chart of the target being the representable presheaf itself. -/
private noncomputable abbrev identityTargetChart {V : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ yoneda.obj V) {x : points B S hS F}
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ F}
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hp : pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x) :
    EtaleChartAtPoint B S hS f x :=
  { U := U, V := V, a := a, b := 𝟙 (yoneda.obj V), h := yoneda.preimage (a ≫ f)
    a_etale := ha, b_etale := presheaf_etale_id B S hS V, comm := by simp
    representative := p, point := IsLocalRing.closedPoint p.carrier, maps_to := hp }

/-- The chart morphism of `identityTargetChart` is locally of finite type when `f` is. -/
private theorem locallyOfFiniteType_identityTargetChart
    {V : BigFppfOver B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ yoneda.obj V}
    (hf : IsLocallyOfFiniteType B S hS f) {x : points B S hS F}
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ F}
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (p : FieldValuedPoint B S hS (yoneda.obj U))
    (hp : pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)) = x) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (identityTargetChart B S hS f ha p hp).h) :=
  hf U V a (𝟙 (yoneda.obj V)) _ ha (presheaf_etale_id B S hS V)
    (identityTargetChart B S hS f ha p hp).comm

/-- Identifying the target of a morphism with another presheaf leaves the transcendence degree
at a point of its source unchanged. -/
private theorem hasTranscendenceDegreeAt_comp_eqToHom_iff
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (h : Y = Y')
    (x : points B S hS X) (n : ℕ∞) :
    HasTranscendenceDegreeAt B S hS (f ≫ eqToHom h) x n ↔
      HasTranscendenceDegreeAt B S hS f x n := by
  subst h
  simp

/-- **Stacks 06FD, part (2).** Let `G` be a groupoid in algebraic spaces over `S` whose space
of objects is the spectrum of a field `k`, viewed as an algebraic space through Yoneda, and
whose source and target are locally of finite type. Then the transcendence degree over `k` of a
point of the space of arrows is the same whether it is measured through the source or through
the target.

Both are read on one étale chart of the arrow space whose chart of the object space is the
field spectrum itself, where they become the two transcendence degrees of the residue field at
a point of a scheme over two morphisms to the spectrum of a field. -/
@[stacks 06FD "part (2): the transcendence degree through the source and through the target"]
theorem hasTranscendenceDegreeAt_source_iff_target
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
    (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (objects_eq : G.objects = _root_.AlgebraicGeometry.schemeSpace
      (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (hs : IsLocallyOfFiniteType B S hS G.source.hom)
    (ht : IsLocallyOfFiniteType B S hS G.target.hom)
    (r : points B S hS G.arrows.obj) (n : ℕ∞) :
    HasTranscendenceDegreeAt B S hS G.source.hom r n ↔
      HasTranscendenceDegreeAt B S hS G.target.hom r n := by
  let V : BigFppfOver B S hS := Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)
  have hU : G.objects.obj = yoneda.obj V := congrArg (fun Z => Z.obj) objects_eq
  obtain ⟨U, a, ha, p, hp⟩ :=
    exists_etale_chart_at_point B S hS G.arrows.obj G.arrows.property r
  let fs : G.arrows.obj ⟶ yoneda.obj V := G.source.hom ≫ eqToHom hU
  let ft : G.arrows.obj ⟶ yoneda.obj V := G.target.hom ≫ eqToHom hU
  let cs := identityTargetChart B S hS fs ha p hp
  let ct := identityTargetChart B S hS ft ha p hp
  have hfs : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map cs.h) :=
    locallyOfFiniteType_identityTargetChart B S hS
      (isLocallyOfFiniteType_comp_eqToHom B S hS G.source.hom hU hs) ha p hp
  have hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ct.h) :=
    locallyOfFiniteType_identityTargetChart B S hS
      (isLocallyOfFiniteType_comp_eqToHom B S hS G.target.hom hU ht) ha p hp
  let e : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (CommRingCat.of k) := Iso.refl _
  have hkey := congrArg Cardinal.toENat (trdeg_residueField_eq_of_target_isSpec_field e
    ((BigFppfOver.toScheme B S hS).map cs.h) ((BigFppfOver.toScheme B S hS).map ct.h)
    (cs.sourcePoint B S hS))
  rw [← hasTranscendenceDegreeAt_comp_eqToHom_iff B S hS G.source.hom hU r n,
    ← hasTranscendenceDegreeAt_comp_eqToHom_iff B S hS G.target.hom hU r n,
    hasTranscendenceDegreeAt_iff_of_chart B S hS n fs r cs,
    hasTranscendenceDegreeAt_iff_of_chart B S hS n ft r ct]
  exact iff_of_eq (congrArg (fun z : ℕ∞ => z = n) hkey)

/-! ### The dimension of the local ring at a point of transcendence degree zero -/

/-- At a point of a scheme locally of finite type over a field whose residue field is algebraic
over the residue field of its image, the local dimension of the scheme is the Krull dimension of
its local ring: such a point is closed, the spectrum of a field having a single point. -/
private theorem topologicalKrullDimAt_eq_ringKrullDim_stalk_of_isAlgebraic (k : Type u) [Field k]
    {U : Scheme.{u}} (f : U ⟶ Spec (.of k)) [LocallyOfFiniteType f] (u : U)
    (halg : letI := (f.residueFieldMap u).hom.toAlgebra
      Algebra.IsAlgebraic ((Spec (.of k)).residueField (f u)) (U.residueField u)) :
    topologicalKrullDimAt U u = ringKrullDim (U.presheaf.stalk u) := by
  have huniv : ({f u} : Set (Spec (.of k))) = Set.univ :=
    Set.eq_univ_of_forall fun z => Subsingleton.elim z (f u)
  have hclosed : IsClosed ({f u} : Set (Spec (.of k))) := huniv ▸ isClosed_univ
  exact topologicalKrullDimAt_eq_krullDimOfRing_stalk k U f u
    (isClosed_of_isAlgebraic_residueField f u halg hclosed)

/-- For an algebraic space locally of finite type over the spectrum of a field, the dimension at
a point whose transcendence degree over that field is zero is the dimension of the local ring
there.

Both sides are read on one pointed étale chart whose chart of the target is the field spectrum
itself: the dimension at the point is the local dimension of that chart, the dimension of the
local ring is the Krull dimension of the chart's stalk, and the two agree because a point of
transcendence degree zero is a closed point of the chart. -/
theorem dimensionAtPoint_eq_localRingDimension_of_hasTranscendenceDegreeAt_zero
    {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (structureMap : Spec (.of k) ⟶ S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (f : F ⟶ yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (hf : IsLocallyOfFiniteType B S hS f) (x : points B S hS F)
    (htr : HasTranscendenceDegreeAt B S hS f x 0) :
    dimensionAtPoint B S hS F hF x = (localRingDimension B S hS x : WithBot ℕ∞) := by
  obtain ⟨U, a, ha, p, hp⟩ := exists_etale_chart_at_point B S hS F hF x
  let V : BigFppfOver B S hS := Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)
  let c := identityTargetChart B S hS f ha p hp
  let g : (BigFppfOver.toScheme B S hS).obj U ⟶ Spec (.of k) :=
    (BigFppfOver.toScheme B S hS).map c.h
  let u : (BigFppfOver.toScheme B S hS).obj U := c.sourcePoint B S hS
  have hft : LocallyOfFiniteType g := locallyOfFiniteType_identityTargetChart B S hS hf ha p hp
  have htr0 := MorphismOfGerms.hasResidueFieldTranscendenceDegree_unique (htr c)
    (MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom g u)
  have halg : let := (g.residueFieldMap u).hom.toAlgebra
      Algebra.IsAlgebraic ((Spec (.of k)).residueField (g u))
        (((BigFppfOver.toScheme B S hS).obj U).residueField u) := by
    let _ := (g.residueFieldMap u).hom.toAlgebra
    exact trdeg_eq_zero_iff.mp (Cardinal.toENat_eq_zero.mp htr0.symm)
  rw [dimensionAtPoint_eq_of_etale_chart B S hS F hF x U a ha p hp,
    localRingDimension_eq_of_chartPoint B S hS hF U a ha u x ⟨p, rfl, hp⟩]
  exact topologicalKrullDimAt_eq_ringKrullDim_stalk_of_isAlgebraic k g u halg

/-- **Stacks 06FD, part (3).** Let `G` be a groupoid in algebraic spaces over `S` whose space of
objects is the spectrum of a field `k`, viewed as an algebraic space through Yoneda, and whose
source and target are locally of finite type. At a point of the space of arrows whose
transcendence degree over `k` is zero, the dimension of the space of arrows is the dimension of
the local ring there. -/
@[stacks 06FD "part (3): the dimension of the local ring at a point of transcendence degree 0"]
theorem dimension_eq_localRingDimension_of_hasTranscendenceDegreeAt_zero
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k)))
    (structureMap : Spec (.of k) ⟶ S)
    {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
    (objects_eq : G.objects = _root_.AlgebraicGeometry.schemeSpace
      (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)))
    (hs : IsLocallyOfFiniteType B S hS G.source.hom)
    (ht : IsLocallyOfFiniteType B S hS G.target.hom)
    (r : points B S hS G.arrows.obj)
    (htr : HasTranscendenceDegreeAt B S hS G.source.hom r 0) :
    dimension B S hS G.arrows.obj G.arrows.property =
      (localRingDimension B S hS r : WithBot ℕ∞) := by
  have hU : G.objects.obj = yoneda.obj (Over.mk (⟨structureMap⟩ : B.obj hk ⟶ B.obj hS)) :=
    congrArg (fun Z => Z.obj) objects_eq
  exact (dimension_eq_dimensionAtPoint B S hS hk structureMap G objects_eq hs ht r).trans <|
    dimensionAtPoint_eq_localRingDimension_of_hasTranscendenceDegreeAt_zero B S hS hk
      structureMap G.arrows.property (G.source.hom ≫ eqToHom hU)
      (isLocallyOfFiniteType_comp_eqToHom B S hS G.source.hom hU hs) r
      ((hasTranscendenceDegreeAt_comp_eqToHom_iff B S hS G.source.hom hU r 0).mpr htr)

end AlgebraicGeometry.Space

end
