module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange

/-!
# Universal closedness of morphisms of algebraic spaces is fpqc local on the base

A morphism of algebraic spaces over `S` is *closed* when the map it induces on the space of
points of Stacks 03BX is a closed map, and *universally closed* when all of its base changes
are (Stacks 03HI). This file proves that universal closedness is local on the base for the fpqc
topology of Stacks 03YH, which is **Stacks 041O**.

The geometric input is the descent of closedness along an fpqc covering: a morphism to a
*representable* algebraic space is closed as soon as its base changes along the members of an
fpqc covering family of the representing scheme are.

Two observations carry the argument. First, closedness of a subset of a scheme is detected by an
fpqc covering family, because the presheaf of continuous maps to the Sierpiński space is an fpqc
sheaf; that is `AlgebraicGeometry.Space.isOpen_of_fpqc_preimages`, applied to the complement.
Second, for a cartesian square of algebraic spaces the preimage of the image of a set of points
is the image of its preimage — points of two corners with the same image downstairs come from a
point of the fibre product, which is Stacks 03H4. Together they reduce closedness of the image
of a closed set of points to closedness of its preimages along the covering family, and each of
those is the image computed in the corresponding base change.

The remaining ingredient is bookkeeping about base changes: if the base change of `f` along `g`
has a property stable under base change, and a morphism `b` into a second base `h` is refined by
`g` in the sense that `a ≫ g = b ≫ h`, then the base change of the base change of `f` along `h`
along `b` has the property too. That is stated for an arbitrary category.

## Main results

* `CategoryTheory.MorphismProperty.pullback_snd_of_refines`: a base change along a morphism
  refined by `g` inherits a property that the base change along `g` has.
* `AlgebraicGeometry.Scheme.isClosed_of_fpqc_preimages`: a subset of a scheme is closed as soon
  as its preimage along every member of an fpqc covering family is closed.
* `AlgebraicGeometry.Space.pointsMap_preimage_image_of_isPullback`: for a cartesian square of
  algebraic spaces, taking images and preimages of sets of points commutes with the square.
* `AlgebraicGeometry.Space.isClosedMorphism_of_fpqc_schemeCover`: a morphism of algebraic spaces
  to a representable one is closed as soon as its base changes along an fpqc covering family of
  the representing scheme are closed.
* `AlgebraicGeometry.Space.universallyClosed_isLocalAtTarget_fpqc`: **Stacks 041O**.

## Implementation notes

`AlgebraicGeometry.Space.IsClosedMorphism` is a statement about the topology
`AlgebraicGeometry.Space.pointTopology` on `AlgebraicGeometry.Space.points`, which is not an
instance; it is made a local instance here, as in the files where that topology is introduced.
The identification of the points of a representable algebraic space with the points of the
representing scheme is the homeomorphism
`AlgebraicGeometry.Space.schemePointsHomeomorph` of Stacks 03BX, clause (1); it is used in the
direction from points to the scheme, so the covering family of the scheme is pulled back to a
family of subsets of the space of points through its inverse.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03IT](https://stacks.math.columbia.edu/tag/03IT)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041O](https://stacks.math.columbia.edu/tag/041O)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.MorphismProperty

/-- Let `g : V ⟶ Y` refine `b : U ⟶ T` over `h : T ⟶ Y`, in the sense that `a ≫ g = b ≫ h` for
some `a : U ⟶ V`, and let `q : W ⟶ T` be a base change of `f : X ⟶ Y` along `h`. A property of
morphisms stable under base change which holds of the base change of `f` along `g` then holds of
the base change of `q` along `b`: the latter is a base change of `f` along `a ≫ g`, hence a base
change of the former. -/
theorem pullback_snd_of_refines {C : Type*} [Category C] [HasPullbacks C]
    (P : MorphismProperty C) [P.IsStableUnderBaseChange]
    {X Y T U V : C} (f : X ⟶ Y) (g : V ⟶ Y) (h : T ⟶ Y) (b : U ⟶ T) (a : U ⟶ V)
    (hab : a ≫ g = b ≫ h) {W : C} {p : W ⟶ X} {q : W ⟶ T} (sq : IsPullback p q f h)
    (hf : P (pullback.snd f g)) : P (pullback.snd q b) := by
  have outer := (IsPullback.of_hasPullback q b).paste_horiz sq
  have outer' : IsPullback (pullback.fst q b ≫ p) (pullback.snd q b) f (a ≫ g) := by
    rwa [hab]
  exact P.of_isPullback (outer'.of_right' (IsPullback.of_hasPullback f g)) hf

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry.Scheme

/-- A subset of a scheme whose preimage along every member of an fpqc covering family is closed
is itself closed: its complement has open preimages, so it is open by
`AlgebraicGeometry.Space.isOpen_of_fpqc_preimages`. -/
theorem isClosed_of_fpqc_preimages {Y : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ Y) (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage Y)
    (W : Set Y) (hW : ∀ i, IsClosed ((f i) ⁻¹' W)) : IsClosed W :=
  isOpen_compl_iff.mp
    (AlgebraicGeometry.Space.isOpen_of_fpqc_preimages f hf Wᶜ fun i ↦ (hW i).isOpen_compl)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_UniversallyClosed :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_UniversallyClosed
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_UniversallyClosed B S hS).has_limit _

/-- **Stacks 03H4**, read on subsets. For a cartesian square of algebraic spaces over `S`, the
preimage along `f` of the image under `g` of a set of points is the image under `q` of its
preimage along `p`. -/
theorem pointsMap_preimage_image_of_isPullback {W Z X Y : AlgebraicSpaces B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (A : Set (points B S hS Z.obj)) :
    pointsMap B S hS X.obj f.hom ⁻¹' (pointsMap B S hS Z.obj g.hom '' A) =
      pointsMap B S hS W.obj q.hom '' (pointsMap B S hS W.obj p.hom ⁻¹' A) := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    obtain ⟨w, rfl, hwx⟩ := exists_point_of_isPullback B S hS sq z x hzx
    exact ⟨w, hz, hwx⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨pointsMap B S hS W.obj p.hom w, hw, ?_⟩
    have h : pointsMap B S hS W.obj (p.hom ≫ g.hom) =
        pointsMap B S hS W.obj (q.hom ≫ f.hom) :=
      congrArg (fun k : W ⟶ Y ↦ pointsMap B S hS W.obj k.hom) sq.w
    simpa only [pointsMap_comp, Function.comp_apply] using congrFun h w

/-- A morphism of algebraic spaces over `S` whose target is representable is closed as soon as
its base changes along the members of an fpqc covering family of the representing scheme are
closed. -/
theorem isClosedMorphism_of_fpqc_schemeCover {X : AlgebraicSpaces B S hS}
    {T : BigFppfOver B S hS} (f : X ⟶ schemeSpace T)
    {I : Type v} (Tᵢ : I → BigFppfOver B S hS) (g : ∀ i, Tᵢ i ⟶ T)
    (hcover : Presieve.ofArrows (fun i ↦ (BigFppfOver.toScheme B S hS).obj (Tᵢ i))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map (g i)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj T))
    (hf : ∀ i, isClosedMorphismProperty B S hS
      (pullback.snd f (schemeSpaceMap (g i)))) :
    isClosedMorphismProperty B S hS f := by
  intro A hA
  have key : ∀ i, IsClosed ((BigFppfOver.toScheme B S hS).map (g i) ⁻¹'
      ((schemePointsHomeomorph B S hS T).symm ⁻¹'
        (pointsMap B S hS X.obj f.hom '' A))) := by
    intro i
    set gi := schemeSpaceMap (g i)
    have hpre : IsClosed (pointsMap B S hS (yoneda.obj (Tᵢ i)) (yoneda.map (g i)) ⁻¹'
        (pointsMap B S hS X.obj f.hom '' A)) := by
      have h := hf i _ (hA.preimage (continuous_pointsMap B S hS (pullback.fst f gi).hom))
      rwa [← pointsMap_preimage_image_of_isPullback B S hS
        (IsPullback.of_hasPullback f gi) A] at h
    have hnat : ∀ x : (BigFppfOver.toScheme B S hS).obj (Tᵢ i),
        (schemePointsHomeomorph B S hS T).symm
            ((BigFppfOver.toScheme B S hS).map (g i) x) =
          pointsMap B S hS (yoneda.obj (Tᵢ i)) (yoneda.map (g i))
            ((schemePointsHomeomorph B S hS (Tᵢ i)).symm x) := by
      intro x
      refine (schemePointsHomeomorph B S hS T).injective ?_
      rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply,
        pointsToScheme_pointsMap, ← schemePointsHomeomorph_apply,
        Homeomorph.apply_symm_apply]
    have heq : (BigFppfOver.toScheme B S hS).map (g i) ⁻¹'
          ((schemePointsHomeomorph B S hS T).symm ⁻¹'
            (pointsMap B S hS X.obj f.hom '' A)) =
        (schemePointsHomeomorph B S hS (Tᵢ i)).symm ⁻¹'
          (pointsMap B S hS (yoneda.obj (Tᵢ i)) (yoneda.map (g i)) ⁻¹'
            (pointsMap B S hS X.obj f.hom '' A)) := by
      ext x
      simp only [Set.mem_preimage, hnat]
    rw [heq]
    exact hpre.preimage (schemePointsHomeomorph B S hS (Tᵢ i)).symm.continuous
  exact ((schemePointsHomeomorph B S hS T).symm.isClosed_preimage).mp
    (Scheme.isClosed_of_fpqc_preimages _ hcover _ key)

/-! ### Stacks 041O -/

/-- **Stacks 03IS at the packaged spelling**: universal closedness, as a morphism property of
algebraic spaces over `S`, is stable under base change. -/
instance universallyClosedMorphismProperty_isStableUnderBaseChange :
    (universallyClosedProperty B S hS).IsStableUnderBaseChange := by
  have heq : universallyClosedProperty B S hS =
      (isClosedMorphismProperty B S hS).universally := by
    funext X T g
    exact propext (universallyClosed_iff_universally_isClosedMorphism B S hS g)
  rw [heq]
  infer_instance

/-- **Stacks 03IU at the packaged spelling**: universal closedness, as a morphism property of
algebraic spaces over `S`, is stable under composition. -/
instance universallyClosedMorphismProperty_isStableUnderComposition :
    (universallyClosedProperty B S hS).IsStableUnderComposition where
  comp_mem := fun {_ Y' Z'} k l hk hl =>
    universallyClosed_comp B S hS Y'.property Z'.property k.hom l.hom hk hl

/-- **Stacks 041O.** Universal closedness of morphisms of algebraic spaces over `S` is local on
the base for the fpqc topology.

Universal closedness is being universally a closed morphism, so the ascent half is formal. For
the descent half, condition (3) of Stacks 03IT reduces the assertion to closedness of the base
changes along morphisms from the *affine* objects of the site; over such an affine `T` the fpqc
condition of Stacks 03MQ supplies a finite affine family covering `T` and refining the given
covering, and closedness of a morphism to a representable algebraic space descends along it. -/
@[stacks 041O]
instance universallyClosed_isLocalAtTarget_fpqc :
    (universallyClosedProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have heq : universallyClosedProperty B S hS =
      (isClosedMorphismProperty B S hS).universally := by
    funext X T g
    exact propext (universallyClosed_iff_universally_isClosedMorphism B S hS g)
  rw [heq]
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff ?_
  intro X Y f R hR
  refine ⟨fun hf U g _ _ ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f g) hf, fun hlocal ↦ ?_⟩
  refine (universallyClosed_iff_universally_isClosedMorphism B S hS f).mp
    (((universallyClosed_tfae B S hS X.property Y.property f.hom).out 3 1).mp ?_)
  intro T h hT
  obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
  obtain ⟨U, hfinite, hU, hfactor⟩ := hcover.2.2.2 ⟨T, hT⟩ h
  let h' : schemeSpace T ⟶ Y := ObjectProperty.homMk h
  change isClosedMorphismProperty B S hS
    (ObjectProperty.homMk (pullback.fst h f.hom) :
      AlgebraicSpaces.fiberProduct B S hS h' f ⟶ schemeSpace T)
  refine isClosedMorphism_of_fpqc_schemeCover B S hS _
    (fun j ↦ (BigAffineFppf.inclusion B S hS).obj (U.X j))
    (fun j ↦ (BigAffineFppf.inclusion B S hS).map (U.f j)) ?_ fun j ↦ ?_
  · simp only [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hU
    exact hU
  · obtain ⟨i, a, ha⟩ := hfactor j
    apply MorphismProperty.universally_le
    exact MorphismProperty.pullback_snd_of_refines
      ((isClosedMorphismProperty B S hS).universally) f (gi i) h'
      (schemeSpaceMap ((BigAffineFppf.inclusion B S hS).map (U.f j)))
      (ObjectProperty.homMk a) (ObjectProperty.hom_ext _ ha)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS h' f).flip (hlocal (gi i) (.mk i))

end AlgebraicGeometry.Space

end
