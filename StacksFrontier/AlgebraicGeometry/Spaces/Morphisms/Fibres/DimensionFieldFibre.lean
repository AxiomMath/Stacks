module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Bounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The fibre dimension is the dimension of the fibre

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is of finite type, and
let `p` be a field-valued point of `Y` with field `k`. The fibre dimension of `f` at the point of
`|Y|` represented by `p`, that is the least bound for the relative dimension of `f` at the points
of `|X|` above it, is the dimension of the algebraic space `X_k = Spec k ×_Y X`. Moreover it is
never `⊤`: either the fibre is empty, and the value is `⊥`, or it is a natural number.

## Main results

* `AlgebraicGeometry.Space.fiberDimension_eq_dimension_pullback` is **Stacks 0D4M**: both halves
  of the above, for a field-valued representative of the point of the target.
* `AlgebraicGeometry.Space.fiberDimension_ne_top` is the finiteness at an arbitrary point of the
  target.

## Implementation notes

The fibre `X_k` is the presheaf pullback of `f` along the morphism `yoneda.obj (Spec k) ⟶ Y`
which `p` represents through the Yoneda lemma; the field spectrum is an object of the site by the
`contained` field of `p`, so that morphism exists.

The first half compares the two sides pointwise. Over a field-valued target the relative dimension
at a point is the absolute dimension there
(`AlgebraicGeometry.Space.relativeDimensionAt_fieldTarget_iff_dimensionAtPoint`), and relative
dimension is invariant under base change (part (1) of Stacks 04NS), so the set whose infimum is
the fibre dimension is bounded below exactly by the supremum defining the dimension of `X_k`.
Only an empty fibre produces the value `⊥`, by
`AlgebraicGeometry.Space.dimensionAtPoint_ne_bot`.

The finiteness is the bounded-fibre-dimension theorem for schemes (Stacks 0A3V). A finite type
morphism has quasi-compact fibres, so `X_k` has an affine surjective étale cover `U` (Stacks
03H6); passing to it does not change the dimension (Stacks 0A4H), which is the Krull dimension of
the representing scheme. That scheme is affine and of finite type over the affine scheme
`Spec k`, which has one point, so the whole of it is a fibre of the induced morphism of schemes
and Stacks 0A3V bounds its dimension by a natural number.

## References

* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)

/-- The presheaf pullback of two morphisms of algebraic spaces is cartesian in the category of
algebraic spaces. -/
private theorem isPullback_homMk_fiberProduct {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ Y)
    (f : X ⟶ Y) (hT : IsAlgebraicSpace B S hS T) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) :
    IsPullback
      (ObjectProperty.homMk (pullback.fst a f) :
        AlgebraicSpaces.fiberProduct B S hS
          (ObjectProperty.homMk a : (⟨T, hT⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
          (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) ⟶ ⟨T, hT⟩)
      (ObjectProperty.homMk (pullback.snd a f) :
        AlgebraicSpaces.fiberProduct B S hS
          (ObjectProperty.homMk a : (⟨T, hT⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
          (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk a : (⟨T, hT⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS _ _

/-- The fibre dimension of a finite type morphism of algebraic spaces at a field-valued point of
its target is the dimension of the fibre over that point.

Both sides are read off the points of the fibre: on the left through the invariance of the
relative dimension under base change, on the right through the identification of the relative
dimension over a field with the absolute dimension. -/
private theorem fiberDimension_class_eq_dimension_pullback
    (hf : IsFiniteType B S hS f) (p : FieldValuedPoint B S hS Y) :
    fiberDimension B S hS f (p.class B S hS Y) =
      dimension B S hS (pullback (yonedaEquiv.symm p.value) f)
        (isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm p.value) f
          (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y)) hX hY) := by
  classical
  set T := p.siteObject B S hS Y with hTdef
  set a : yoneda.obj T ⟶ Y := yonedaEquiv.symm p.value with hadef
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hP : IsAlgebraicSpace B S hS (pullback a f) :=
    isAlgebraicSpace_pullback B S hS a f hT hX hY
  have hBaseChange (w : points B S hS (pullback a f)) (e : ℕ∞) :
      HasRelativeDimensionAt e B S hS f
          (pointsMap B S hS (pullback a f) (pullback.snd a f) w) ↔
        HasRelativeDimensionAt e B S hS (pullback.fst a f) w :=
    hasRelativeDimensionAt_iff_of_isPullback B S hS
      (IsPullback.of_hasPullback a f).flip hX hT hY hf.1 w e
  have hPointDim (w : points B S hS (pullback a f)) (e : ℕ∞) :
      HasRelativeDimensionAt e B S hS (pullback.fst a f) w ↔
        dimensionAtPoint B S hS (pullback a f) hP w = (e : WithBot ℕ∞) :=
    relativeDimensionAt_fieldTarget_iff_dimensionAtPoint B S hS hP
      (fieldPointOfYoneda B S hS p) (pullback.fst a f) w e
  have hover (w : points B S hS (pullback a f)) :
      pointsMap B S hS X f (pointsMap B S hS (pullback a f) (pullback.snd a f) w) =
        p.class B S hS Y := by
    rw [← pointsMap_apply_comm B S hS (pullback.condition (f := a) (g := f)) w]
    exact FieldValuedPoint.pointsMap_eq_class B S hS p _
  refine le_antisymm (sInf_le fun x hx ↦ ?_) (le_sInf fun d hd ↦ iSup_le fun w ↦ ?_)
  · obtain ⟨w, -, hwx⟩ := exists_point_of_isPullback B S hS
      (isPullback_homMk_fiberProduct B S hS a f hT hX hY)
      ((fieldPointOfYoneda B S hS p).class B S hS (yoneda.obj T)) x
      ((FieldValuedPoint.pointsMap_eq_class B S hS p _).trans hx.symm)
    have hne := dimensionAtPoint_ne_bot B S hS (pullback a f) hP w
    refine ⟨(dimensionAtPoint B S hS (pullback a f) hP w).unbot hne, ?_, ?_⟩
    · rw [← hwx]
      exact (hBaseChange w _).mpr ((hPointDim w _).2 (WithBot.coe_unbot _ hne).symm)
    · rw [WithBot.coe_unbot]
      exact le_iSup (fun z ↦ dimensionAtPoint B S hS (pullback a f) hP z) w
  · obtain ⟨e, he, hed⟩ := hd _ (hover w)
    rw [(hPointDim w e).mp ((hBaseChange w e).mp he)]
    exact hed

/-- The dimension of the fibre of a finite type morphism of algebraic spaces over a field-valued
point of its target is not `⊤`.

An affine surjective étale cover `U` of the fibre has the same dimension as the fibre, namely the
Krull dimension of the representing scheme; that scheme is the whole of a fibre of a finite type
morphism to the one-point affine scheme `Spec k`, so Stacks 0A3V bounds its dimension. -/
private theorem dimension_pullback_ne_top
    (hf : IsFiniteType B S hS f) (p : FieldValuedPoint B S hS Y) :
    dimension B S hS (pullback (yonedaEquiv.symm p.value) f)
        (isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm p.value) f
          (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y)) hX hY) ≠ ⊤ := by
  classical
  set T := p.siteObject B S hS Y with hTdef
  set a : yoneda.obj T ⟶ Y := yonedaEquiv.symm p.value with hadef
  have hT : IsAlgebraicSpace B S hS (yoneda.obj T) := isAlgebraicSpace_yoneda B S hS T
  have hP : IsAlgebraicSpace B S hS (pullback a f) :=
    isAlgebraicSpace_pullback B S hS a f hT hX hY
  have hTcompact : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) :=
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of p.carrier)))
  have hTaffine : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))
  have hTsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj T) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  obtain ⟨t⟩ : Nonempty ((BigFppfOver.toScheme B S hS).obj T) :=
    ⟨(IsLocalRing.closedPoint p.carrier : Spec (CommRingCat.of p.carrier))⟩
  have hPqc : IsQuasiCompactSpace B S hS (pullback a f) :=
    hf.2 (yoneda.obj T) hT (isQuasiCompactSpace_yoneda_obj B S hS hTcompact) a
  obtain ⟨U, q, hUaff, hqsurj, hqet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (pullback a f) hP).mp hPqc
  have hfst : IsFiniteType B S hS (pullback.fst a f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃F G : AlgebraicSpaces B S hS⦄ (k : F ⟶ G) ↦ IsFiniteType B S hS k.hom)
      (isPullback_homMk_fiberProduct B S hS a f hT hX hY).flip hf
  set h : U ⟶ T := yoneda.preimage (q ≫ pullback.fst a f) with hhdef
  have hmap : yoneda.map h = q ≫ pullback.fst a f := yoneda.map_preimage _
  have hUaffine : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUaff
  have hloc : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map h) :=
    hfst.1 U T q (𝟙 (yoneda.obj T)) h (presheaf_etale_of_isEtale B S hS hqet)
      (presheaf_etale_id B S hS T) (by rw [hmap, Category.comp_id])
  have hqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map h) := inferInstance
  obtain ⟨n, hn⟩ :=
    exists_topologicalKrullDim_fiber_le ((BigFppfOver.toScheme B S hS).map h)
  have hfibre : topologicalKrullDim (((BigFppfOver.toScheme B S hS).map h).fiber t) =
      topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj U) := by
    have hpre : ((BigFppfOver.toScheme B S hS).map h) ⁻¹' {t} = Set.univ := by
      ext z
      simpa only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true] using
        Subsingleton.elim _ _
    exact IsHomeomorph.topologicalKrullDim_eq _
      (Homeomorph.isHomeomorph ((((BigFppfOver.toScheme B S hS).map h).fiberHomeo t).trans
        ((Homeomorph.setCongr hpre).trans
          (Homeomorph.Set.univ ((BigFppfOver.toScheme B S hS).obj U)))))
  have hbound : dimension B S hS (pullback a f) hP ≤ (n : WithBot ℕ∞) := by
    rw [← dimension_eq_of_isEtale_of_isSurjective B S hS (isAlgebraicSpace_yoneda B S hS U) hP
        q hqet ((surjective_iff_surjective_pointsMap B S hS (pullback a f) hP U q).mp hqsurj),
      dimension_yoneda_eq_topologicalKrullDim B S hS U, ← hfibre]
    exact hn t
  exact ne_top_of_le_ne_top (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top n)).ne hbound

/-- **Stacks 0D4M.** For a morphism of algebraic spaces over `S` of finite type and a field-valued
point `p` of its target, the fibre dimension at the point `p` represents is the dimension of the
fibre of `f` over `p`, and it is not `⊤`. -/
@[stacks 0D4M]
theorem fiberDimension_eq_dimension_pullback
    (hf : IsFiniteType B S hS f) (p : FieldValuedPoint B S hS Y) :
    fiberDimension B S hS f (p.class B S hS Y) =
      dimension B S hS (pullback (yonedaEquiv.symm p.value) f)
        (isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm p.value) f
          (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y)) hX hY) ∧
      fiberDimension B S hS f (p.class B S hS Y) ≠ ⊤ :=
  ⟨fiberDimension_class_eq_dimension_pullback B S hS f hX hY hf p,
    (fiberDimension_class_eq_dimension_pullback B S hS f hX hY hf p).trans_ne
      (dimension_pullback_ne_top B S hS f hX hY hf p)⟩

end

/-- The fibre dimension of a finite type morphism of algebraic spaces is never `⊤`: at a point
of the target it is the dimension of the fibre over any field-valued representative. -/
theorem fiberDimension_ne_top {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsFiniteType B S hS f) (y : points B S hS Y) :
    fiberDimension B S hS f y ≠ ⊤ := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep y
  exact (fiberDimension_eq_dimension_pullback B S hS f hX hY hf p).2

end AlgebraicGeometry.Space

end
