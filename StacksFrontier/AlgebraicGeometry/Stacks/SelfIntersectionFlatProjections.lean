module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeSmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionPresentation
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.RingTheory.Smooth.Reduced

/-!
# Projections of a flat presentation of an algebraic stack (Stacks 04WY)

Let `F : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, representable by algebraic spaces, with `𝒰` represented by an algebraic space `U` and
the self-intersection `ℛ = 𝒰 ×_{F, 𝒳, F} 𝒰` represented by an algebraic space `R`. Stacks 04T4 (4)
builds from these choices a groupoid in algebraic spaces with object space `U` and arrow space
`R`, carried by `AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionPresentation`.

Stacks 04T5 (1) says that if `F` is smooth then the source and target morphisms `R ⟶ U` of that
groupoid are smooth. Stacks 04WY observes that the same argument needs nothing of smoothness: if
`F` is only flat, or only locally of finite presentation, then so are the two projections — and
that this is genuinely weaker, since for the dual-number cover of a point the two projections of
the self-fibre product are not smooth.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.isFlat_selfIntersectionPresentation_source` and
  `…_target`: the two projections are flat when `F` is.
* `AlgebraicGeometry.Stack.SelfIntersection`'s
  `isLocallyOfFinitePresentation_selfIntersectionPresentation_source` and `…_target`: the two
  projections are locally of finite presentation when `F` is.
* `AlgebraicGeometry.dualNumbers_projections_not_smooth`: the cover of a point by its dual
  numbers is surjective, flat and locally of finite presentation, and neither projection of its
  self-fibre product is smooth. So the two conclusions above cannot be strengthened to
  smoothness.

## Implementation notes

Each projection is the first leg of a 2-fibre product square over the cospan `F`, `F` — the
canonical square `CategoryTheory.CatFiberedInGroupoids.twoFibreProductSquare` for the target, and
its leg exchange of Stacks 003Q for the source — so each conclusion is Stacks 04XC, read at the
property in question, exactly as in the smooth case of Stacks 04T5 (1). Nothing transports along
the identifications of the groupoid's object and arrow spaces with `U` and `R`: those are
identities, as recorded for the smooth siblings.

`AlgebraicGeometry.Stack.HasRelativeProperty` of Stacks 03YK carries two instance hypotheses on
the property, stability under base change and locality at the target for the fppf precoverage.
For flatness they are Stacks 03MO and Stacks 041W, and for being locally of finite presentation
Stacks 03XR and Stacks 041T; all four are formalized. Only 041W lacks a stated fppf form, which
`AlgebraicGeometry.Space.isFlat_isLocalAtTarget_fppf` below supplies from the fpqc form by
`CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le`. Its proper home is
`StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison`, beside the identical
`AlgebraicGeometry.Space.smooth_isLocalAtTarget_fppf`; it is stated here, and carried as a local
instance only, so that no module's global instance set changes.

The counterexample is the inclusion `k → k[ε]` of a field into its dual numbers. It is flat and
of finite presentation, and surjective on spectra because `k[ε]` is faithfully flat; it is not
smooth because a smooth algebra over a reduced ring is reduced while `k[ε]` is not. Each
projection of the self-fibre product has the morphism itself as a base change along the retraction
`k[ε] → k`, so smoothness of either would give smoothness of the morphism.

## References

* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/-- **Stacks 041W** at the fppf precoverage: flatness of morphisms of algebraic spaces over `S`
is local at the target for the fppf topology. It follows from the fpqc form
`AlgebraicGeometry.Space.isFlat_isLocalAtTarget_fpqc` through
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`, and it is the form in
which the relative properties of Stacks 03YK ask for it; it is the exact analogue of
`AlgebraicGeometry.Space.isLocallyOfFinitePresentation_isLocalAtTarget_fppf` and of
`AlgebraicGeometry.Space.smooth_isLocalAtTarget_fppf`. -/
@[stacks 041W "the fppf precoverage"]
theorem isFlat_isLocalAtTarget_fppf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    MorphismProperty.IsLocalAtTarget
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => IsFlat B S hS g.hom)
      (Topology.fppf.precoverage.{u, v} B S hS) :=
  (isFlat_isLocalAtTarget_fpqc B S hS).of_le (fppfPrecoverage_le_fpqcPrecoverage B S hS)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.SelfIntersection

attribute [local instance] Space.isFlat_isLocalAtTarget_fppf
  Space.isFlat_isStableUnderBaseChange
  Space.isLocallyOfFinitePresentation_isStableUnderBaseChange

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {F : 𝒰 ⟶ 𝒳}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 F.hom).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- The source projection of the self-intersection presentation has any property `P` for which
the presenting 1-morphism has the relative property: Stacks 04XC at the leg exchange of the
canonical 2-fibre product square. -/
private theorem prop_selfIntersectionPresentation_source
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS P F hF)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    P (ObjectProperty.homMk (selfIntersectionPresentation eU eR h𝒳).groupoid.source.hom) :=
  (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS P F hF).mp
    hP 𝒰 ⟨U.obj, U.property, ⟨eU⟩⟩ F
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} F F).swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} F F))
    R.obj U.obj R.property U.property eR eU

/-- The target projection of the self-intersection presentation has any property `P` for which
the presenting 1-morphism has the relative property: Stacks 04XC at the canonical 2-fibre product
square. -/
private theorem prop_selfIntersectionPresentation_target
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hP : HasRelativeProperty.{u, u, u + 1, u} B S hS P F hF)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    P (ObjectProperty.homMk (selfIntersectionPresentation eU eR h𝒳).groupoid.target.hom) :=
  (hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS P F hF).mp
    hP 𝒰 ⟨U.obj, U.property, ⟨eU⟩⟩ F
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} F F)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} F F)
    R.obj U.obj R.property U.property eR eU

/-- **Stacks 04WY for the source projection, flatness.** The source morphism `R ⟶ U` of the
groupoid in algebraic spaces of Stacks 04T4 (4) is flat when the presenting 1-morphism is.

The source morphism is induced by the second projection `pr₁` of the self-intersection, which is
the first leg of the leg exchange (Stacks 003Q) of the canonical 2-fibre product square over the
cospan `F`, `F`; so this is Stacks 04XC at flatness, read at that square. -/
@[stacks 04WY "the source projection of a flat presentation is flat"]
theorem isFlat_selfIntersectionPresentation_source
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hflat : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => Space.IsFlat B S hS g.hom) F hF)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    Space.IsFlat B S hS (selfIntersectionPresentation eU eR h𝒳).groupoid.source.hom :=
  prop_selfIntersectionPresentation_source eU eR _ hF hflat h𝒳

/-- **Stacks 04WY for the target projection, flatness.** The target morphism `R ⟶ U` of the
groupoid in algebraic spaces of Stacks 04T4 (4) is flat when the presenting 1-morphism is.

The target morphism is induced by the first projection `pr₀` of the self-intersection, which is
the first leg of the canonical 2-fibre product square over the cospan `F`, `F`; so this is Stacks
04XC at flatness, read at that square, with no leg exchange. -/
@[stacks 04WY "the target projection of a flat presentation is flat"]
theorem isFlat_selfIntersectionPresentation_target
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hflat : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => Space.IsFlat B S hS g.hom) F hF)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    Space.IsFlat B S hS (selfIntersectionPresentation eU eR h𝒳).groupoid.target.hom :=
  prop_selfIntersectionPresentation_target eU eR _ hF hflat h𝒳

/-- **Stacks 04WY for the source projection, local finite presentation.** The source morphism
`R ⟶ U` of the groupoid in algebraic spaces of Stacks 04T4 (4) is locally of finite presentation
when the presenting 1-morphism is.

This is Stacks 04XC at local finite presentation, read at the leg exchange (Stacks 003Q) of the
canonical 2-fibre product square over the cospan `F`, `F`. -/
@[stacks 04WY "the source projection is locally of finite presentation"]
theorem isLocallyOfFinitePresentation_selfIntersectionPresentation_source
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hlfp : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) F hF)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    Space.IsLocallyOfFinitePresentation B S hS
      (selfIntersectionPresentation eU eR h𝒳).groupoid.source.hom :=
  prop_selfIntersectionPresentation_source eU eR _ hF hlfp h𝒳

/-- **Stacks 04WY for the target projection, local finite presentation.** The target morphism
`R ⟶ U` of the groupoid in algebraic spaces of Stacks 04T4 (4) is locally of finite presentation
when the presenting 1-morphism is.

This is Stacks 04XC at local finite presentation, read at the canonical 2-fibre product square
over the cospan `F`, `F`, with no leg exchange. -/
@[stacks 04WY "the target projection is locally of finite presentation"]
theorem isLocallyOfFinitePresentation_selfIntersectionPresentation_target
    (hF : IsRepresentableByAlgebraicSpaces B S hS F.hom)
    (hlfp : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) F hF)
    (h𝒳 : IsAlgebraicStack B S hS 𝒳.val) :
    Space.IsLocallyOfFinitePresentation B S hS
      (selfIntersectionPresentation eU eR h𝒳).groupoid.target.hom :=
  prop_selfIntersectionPresentation_target eU eR _ hF hlfp h𝒳

end AlgebraicGeometry.Stack.SelfIntersection

namespace AlgebraicGeometry

/-- The retraction `k[ε] → k` of the dual numbers onto the base field is a section of the
inclusion, read on spectra. -/
private theorem dualNumbers_section (k : Type u) [Field k] :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k k)) =
      𝟙 (Spec (.of k)) := by
  rw [← Spec.map_comp]
  have hcomp : CommRingCat.ofHom (TrivSqZeroExt.inlHom k k) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom =
        𝟙 (CommRingCat.of k) := by
    ext x
    rfl
  rw [hcomp, Spec.map_id]

/-- The dual-number cover of a point is not smooth: a smooth algebra over a reduced ring is
reduced, and `k[ε]` is not. -/
private theorem dualNumbers_not_smooth (k : Type u) [Field k] :
    ¬ Smooth (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k k))) := by
  intro hs
  have hring : (CommRingCat.ofHom (TrivSqZeroExt.inlHom k k)).hom.Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs
  have hred : _root_.IsReduced (TrivSqZeroExt k k) := by
    have hsm : Algebra.Smooth k (TrivSqZeroExt k k) := by
      have hmap : (algebraMap k (TrivSqZeroExt k k)).Smooth := by
        convert hring using 1
        ext x <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
      exact (RingHom.smooth_algebraMap).mp hmap
    exact Algebra.isReduced_of_smooth k _
  let z : TrivSqZeroExt k k := TrivSqZeroExt.inr (1 : k)
  have hz0 : z = 0 := _root_.IsReduced.eq_zero _ ⟨2, by simp [z, pow_two]⟩
  simpa [z] using congrArg TrivSqZeroExt.snd hz0

/-- A morphism with a section is a base change of the first projection of its self-fibre product
along that section. -/
private theorem isPullback_fst_of_section {C : Type*} [Category C] {X U : C} [HasPullbacks C]
    (f : U ⟶ X) (e : X ⟶ U) (he : e ≫ f = 𝟙 X) :
    IsPullback f (pullback.lift (f ≫ e) (𝟙 U) (by simp [he])) e (pullback.fst f f) := by
  refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_snd]
  convert IsPullback.id_vert _ using 1

/-- A morphism with a section is a base change of the second projection of its self-fibre product
along that section. -/
private theorem isPullback_snd_of_section {C : Type*} [Category C] {X U : C} [HasPullbacks C]
    (f : U ⟶ X) (e : X ⟶ U) (he : e ≫ f = 𝟙 X) :
    IsPullback f (pullback.lift (𝟙 U) (f ≫ e) (by simp [he])) e (pullback.snd f f) :=
  (isPullback_fst_of_section f e he).of_iso (Iso.refl _) (Iso.refl _) (pullbackSymmetry f f)
    (Iso.refl _) (by simp) (by ext <;> simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullbackSymmetry_hom_comp_snd, pullback.lift_fst, pullback.lift_snd, Iso.refl_hom,
      Category.id_comp])
    (by simp) (by simp)

/-- The inclusion of a field into its dual numbers is the algebra map. -/
private theorem dualNumbers_inlHom_eq (k : Type u) [Field k] :
    TrivSqZeroExt.inlHom k k = algebraMap k (TrivSqZeroExt k k) := by
  ext x <;> simp [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.inlHom,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl]

/-- The dual-number cover of a point is locally of finite presentation. -/
private theorem dualNumbers_locallyOfFinitePresentation (k : Type u) [Field k] :
    LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k k))) := by
  have hft : Algebra.FiniteType k (TrivSqZeroExt k k) := by
    rw [Algebra.FiniteType.iff_quotient_mvPolynomial'']
    refine ⟨1, MvPolynomial.aeval (fun _ => TrivSqZeroExt.inr (1 : k)), fun x => ?_⟩
    refine ⟨MvPolynomial.C x.fst + MvPolynomial.C x.snd * MvPolynomial.X 0, ?_⟩
    apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hr : (TrivSqZeroExt.inlHom k k).FinitePresentation := by
    rw [dualNumbers_inlHom_eq, RingHom.finitePresentation_algebraMap]
    exact (Algebra.FinitePresentation.of_finiteType (R := k)
      (A := TrivSqZeroExt k k)).mp hft
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr hr

/-- The dual-number cover of a point is flat. -/
private theorem dualNumbers_flat (k : Type u) [Field k] :
    Flat (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k k))) := by
  refine (HasRingHomProperty.Spec_iff (P := @Flat)).mpr ?_
  have hr : (TrivSqZeroExt.inlHom k k).Flat := by
    rw [dualNumbers_inlHom_eq, RingHom.flat_algebraMap_iff]
    infer_instance
  exact hr

/-- The dual-number cover of a point is surjective. -/
private theorem dualNumbers_surjective (k : Type u) [Field k] :
    Surjective (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k k))) := by
  have h : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.inlHom k k)) := by
    rw [dualNumbers_inlHom_eq]
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  exact (surjective_iff _).2 h

/-- **Stacks 04WY, the dual-number counterexample.** The cover of a point by the spectrum of its
dual numbers is surjective, flat and locally of finite presentation, and neither projection of its
self-fibre product is smooth. So the two projections of a flat presentation locally of finite
presentation are not smooth in general, unlike the smooth case of Stacks 04T5 (1). -/
@[stacks 04WY "the projections of a flat presentation need not be smooth"]
theorem dualNumbers_projections_not_smooth (k : Type u) [Field k] :
    let U := Spec (.of (TrivSqZeroExt k k))
    let X := Spec (.of k)
    let f : U ⟶ X := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom k k))
    Surjective f ∧ Flat f ∧ LocallyOfFinitePresentation f ∧
      ¬ Smooth (pullback.fst f f) ∧ ¬ Smooth (pullback.snd f f) :=
  ⟨dualNumbers_surjective k, dualNumbers_flat k,
    dualNumbers_locallyOfFinitePresentation k,
    fun hs => dualNumbers_not_smooth k
      (MorphismProperty.of_isPullback
        (isPullback_fst_of_section _ _ (dualNumbers_section k)).flip hs),
    fun hs => dualNumbers_not_smooth k
      (MorphismProperty.of_isPullback
        (isPullback_snd_of_section _ _ (dualNumbers_section k)).flip hs)⟩

end AlgebraicGeometry

end
