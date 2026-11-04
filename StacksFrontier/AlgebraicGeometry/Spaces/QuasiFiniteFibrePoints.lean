module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Fibre
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# A finite-type morphism of algebraic spaces is quasi-finite at finitely many points of a fibre

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite type, and
let `W` sit in a cartesian square over `f` and the morphism presented by a field-valued point of
`Y`. If `W` is a quasi-compact algebraic space, then only finitely many points of `|X|` above the
point represented by that field-valued point are points at which `f` is quasi-finite.

## Main results

* `AlgebraicGeometry.Space.finite_setOf_pointsMap_eq_and_isQuasiFiniteAt_of_isPullback`: for
  an arbitrary cartesian square presenting the fibre, only finitely many points of the fibre are
  points at which `f` is quasi-finite.
* `AlgebraicGeometry.Space.finite_setOf_isQuasiFiniteAt_of_isQuasiCompactSpace`: a morphism
  locally of finite type from a quasi-compact algebraic space to a representable presheaf
  whose underlying scheme has at most one point is quasi-finite at only finitely many points.
* `AlgebraicGeometry.Space.range_pointsMap_of_isPullback_fieldValuedPoint`: the projection to
  `X` of the fibre of `f` over a field-valued point of `Y` has image exactly the
  set-theoretic fibre over the point that field-valued point represents.

## References

* [Stacks Project, Tag 0ABN](https://stacks.math.columbia.edu/tag/0ABN)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 0AAY](https://stacks.math.columbia.edu/tag/0AAY)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre over a field-valued point, on points -/

/-- If `W` sits in a cartesian square over the morphism `f : X ⟶ Y` and the morphism presented
by a field-valued point `p` of `Y`, then the projection `W ⟶ X` has image on points exactly the
fibre of `f` over the point represented by `p`. -/
theorem range_pointsMap_of_isPullback_fieldValuedPoint
    {W X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (p : FieldValuedPoint B S hS Y)
    {pr : W ⟶ yoneda.obj p.siteObject} {q : W ⟶ X}
    (sq : IsPullback pr q (yonedaEquiv.symm p.value) f) :
    Set.range (pointsMap B S hS W q) =
      {x | pointsMap B S hS X f x = p.class B S hS Y} := by
  ext x
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    show pointsMap B S hS X f (pointsMap B S hS W q w) = _
    rw [← pointsMap_apply_comm B S hS sq.w w]
    exact FieldValuedPoint.pointsMap_eq_class B S hS p _
  · obtain ⟨w, -, hw⟩ := exists_points_of_isPullback B S hS sq
      ((p.tautological B S hS).class B S hS (yoneda.obj p.siteObject)) x
      ((FieldValuedPoint.pointsMap_eq_class B S hS p _).trans hx.symm)
    exact ⟨w, hw⟩

/-! ### The quasi-finite locus over a one-point target -/

/-- A morphism locally of finite type from a quasi-compact algebraic space over `S` to a
representable presheaf whose underlying scheme has at most one point is quasi-finite at only
finitely many points of its source. -/
theorem finite_setOf_isQuasiFiniteAt_of_isQuasiCompactSpace
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}
    (hW : IsAlgebraicSpace B S hS W) (hWqc : IsQuasiCompactSpace B S hS W)
    (hVsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj V))
    (f : W ⟶ yoneda.obj V) (hf : IsLocallyOfFiniteType B S hS f) :
    {w | IsQuasiFiniteAt B S hS f w}.Finite := by
  obtain ⟨U, a, hUaff, hasurj, haetale⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS W hW).mp hWqc
  have hap : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a := presheaf_etale_of_isEtale B S hS haetale
  have hmul := isMultiplicative_presheaf_etale B S hS
  have hbp : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj V)) :=
    MorphismProperty.id_mem _ _
  have hcomm : yoneda.map (yoneda.preimage (a ≫ f)) ≫ 𝟙 (yoneda.obj V) = a ≫ f := by
    rw [Category.comp_id, yoneda.map_preimage]
  set g := (BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f))
  have hft : LocallyOfFiniteType g :=
    hf U V a (𝟙 (yoneda.obj V)) (yoneda.preimage (a ≫ f)) hap hbp hcomm
  have hUaff' : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hUaff
  have hqc : QuasiCompact g :=
    ⟨fun O _ _ ↦ by
      rcases O.eq_empty_or_nonempty with rfl | ⟨s, hs⟩
      · simp
      · have hO : O = Set.univ := Set.eq_univ_of_forall fun t ↦ Subsingleton.elim t s ▸ hs
        rw [hO, Set.preimage_univ]
        exact isCompact_univ⟩
  have hfinU : {u : (BigFppfOver.toScheme B S hS).obj U | quasiFiniteAt g u}.Finite := by
    rcases isEmpty_or_nonempty ((BigFppfOver.toScheme B S hS).obj U) with _ | hne
    · exact Set.toFinite _
    · obtain ⟨u₀⟩ := hne
      refine Set.Finite.subset (finite_setOf_mapsTo_and_quasiFiniteAt g (g u₀)) ?_
      exact fun u hu ↦ ⟨Subsingleton.elim _ _, hu⟩
  have hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj U) a) :=
    isSurjective_of_presheafSurjective B S hS a hasurj
  refine Set.Finite.subset (hfinU.image (fun u ↦ pointsMap B S hS (yoneda.obj U) a
    ((pointsEquivScheme B S hS U).symm u))) ?_
  intro w hw
  obtain ⟨w₀, rfl⟩ := hsurj w
  refine ⟨pointsEquivScheme B S hS U w₀, ?_, by simp⟩
  have hzero : ((0 : ℕ∞) : WithBot ℕ∞) = 0 := rfl
  have hd : HasRelativeDimensionAt 0 B S hS f (pointsMap B S hS (yoneda.obj U) a w₀) :=
    (isQuasiFiniteAt_iff_hasRelativeDimensionAt_zero B S hS hW
      (isAlgebraicSpace_yoneda B S hS V) f hf _).mp hw
  show quasiFiniteAt _ _
  rw [quasiFiniteAt_iff_fiberDimensionAt_eq_zero, ← hzero]
  refine (hasRelativeDimensionAt_pointsMap_iff B S hS 0 f U V a (𝟙 (yoneda.obj V))
    (yoneda.preimage (a ≫ f)) hap hbp hcomm (pointsEquivScheme B S hS U w₀)).mp ?_
  rwa [Equiv.symm_apply_apply]

/-! ### Finiteness for an arbitrary cartesian square -/

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite type,
let `p` be a field-valued point of `Y`, and let `W` sit in a cartesian square over `f` and the
morphism presented by `p`. If `W` is a quasi-compact algebraic space, then only finitely many
points of `|X|` above the point represented by `p` are points at which `f` is quasi-finite. -/
theorem finite_setOf_pointsMap_eq_and_isQuasiFiniteAt_of_isPullback
    {W X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS Y)
    {pr : W ⟶ yoneda.obj p.siteObject} {q : W ⟶ X}
    (sq : IsPullback pr q (yonedaEquiv.symm p.value) f)
    (hW : IsAlgebraicSpace B S hS W) (hWqc : IsQuasiCompactSpace B S hS W) :
    {x | pointsMap B S hS X f x = p.class B S hS Y ∧
      IsQuasiFiniteAt B S hS f x}.Finite := by
  have hVsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have hpr : IsLocallyOfFiniteType B S hS pr :=
    IsLocallyOfFiniteType.of_isPullback B S hS sq hX hY hf
  have hfin := finite_setOf_isQuasiFiniteAt_of_isQuasiCompactSpace B S hS hW hWqc hVsub pr hpr
  have hkey : {x | pointsMap B S hS X f x = p.class B S hS Y ∧ IsQuasiFiniteAt B S hS f x} =
      pointsMap B S hS W q '' {w | IsQuasiFiniteAt B S hS pr w} := by
    rw [setOf_isQuasiFiniteAt_eq_preimage_of_isPullback' B S hS sq hX hY
        (isAlgebraicSpace_yoneda B S hS p.siteObject) hf,
      Set.image_preimage_eq_inter_range,
      range_pointsMap_of_isPullback_fieldValuedPoint B S hS p sq]
    exact Set.ext fun x ↦ and_comm
  rw [hkey]
  exact hfin.image _

end AlgebraicGeometry.Space

end
