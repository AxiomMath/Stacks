module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Submersive

/-!
# Universal submersiveness of morphisms of algebraic spaces is fpqc local on the base

A morphism of algebraic spaces over `S` is *submersive* when the map it induces on the space of
points of Stacks 03BX is a quotient map, and *universally submersive* when all of its base
changes are (Stacks 0412). This file proves that universal submersiveness is local on the base
for the fpqc topology of Stacks 03YH, which is **Stacks 0CFW**.

## Main definitions

* `AlgebraicGeometry.Space.isSubmersiveProperty`: submersiveness of a morphism as a
  `CategoryTheory.MorphismProperty` on `AlgebraicGeometry.AlgebraicSpaces`.
* `AlgebraicGeometry.Space.universallySubmersiveMorphismProperty`: universal submersiveness as a
  `CategoryTheory.MorphismProperty` on `AlgebraicGeometry.AlgebraicSpaces`.

## Main results

* `AlgebraicGeometry.Space.universallySubmersive_iff_universally_isSubmersive`: universal
  submersiveness is being universally submersive.
* `AlgebraicGeometry.Space.isSubmersive_of_fpqcCovering`: submersiveness descends along an fpqc
  covering family of the target.
* `AlgebraicGeometry.Space.universallySubmersive_isLocalAtTarget_fpqc`: universal submersiveness is
  local on the base for the fpqc topology.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03MR](https://stacks.math.columbia.edu/tag/03MR)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 0412](https://stacks.math.columbia.edu/tag/0412)
* [Stacks Project, Tag 0CFW](https://stacks.math.columbia.edu/tag/0CFW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_UniversallySubmersive :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_UniversallySubmersive
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_UniversallySubmersive B S hS).has_limit _

/-! ### Submersiveness as a property of morphisms of algebraic spaces -/

/-- Submersiveness of a morphism of algebraic spaces over `S` is unchanged by precomposing with
an isomorphism. -/
theorem isSubmersive_iso_hom_comp {F G H : AlgebraicSpaces B S hS} (e : F ≅ G) (f : G ⟶ H)
    (hf : IsSubmersive B S hS f.hom) :
    IsSubmersive B S hS (e.hom ≫ f).hom := by
  exact hf.comp B S hS (pointsMapHomeomorph B S hS e).isQuotientMap

/-- Submersiveness of a morphism of algebraic spaces over `S` is unchanged by postcomposing with
an isomorphism. -/
theorem isSubmersive_comp_iso_hom {F G H : AlgebraicSpaces B S hS} (e : G ≅ H) (f : F ⟶ G)
    (hf : IsSubmersive B S hS f.hom) :
    IsSubmersive B S hS (f ≫ e.hom).hom := by
  exact IsSubmersive.comp B S hS (pointsMapHomeomorph B S hS e).isQuotientMap hf

/-- Submersiveness (**Stacks 0412**, part (1)), as a property of morphisms in the category of
algebraic spaces over `S`. -/
abbrev isSubmersiveProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f ↦ IsSubmersive B S hS f.hom

/-- Submersiveness of a morphism of algebraic spaces over `S` respects isomorphisms. -/
instance isSubmersiveProperty_respectsIso :
    (isSubmersiveProperty B S hS).RespectsIso :=
  MorphismProperty.RespectsIso.mk _
    (fun e f hf ↦ isSubmersive_iso_hom_comp B S hS e f hf)
    (fun e f hf ↦ isSubmersive_comp_iso_hom B S hS e f hf)

/-- Universal submersiveness (**Stacks 0412**, part (2)), as a property of morphisms in the
category of algebraic spaces over `S`. -/
abbrev universallySubmersiveMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f ↦ UniversallySubmersive B S hS f.hom

/-- Being universally submersive (**Stacks 0412**, part (2)) is being universally submersive in
the sense of `CategoryTheory.MorphismProperty.universally`. -/
theorem universallySubmersive_iff_universally_isSubmersive {X T : AlgebraicSpaces B S hS}
    (g : X ⟶ T) :
    UniversallySubmersive B S hS g.hom ↔ (isSubmersiveProperty B S hS).universally g := by
  refine ⟨fun hg Y' T' i₁ i₂ k sq ↦ ?_, fun hg Z hZ k ↦ hg _ _ _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk (X := (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) k) g)⟩
  have hP := AlgebraicSpaces.isPullback_fiberProduct B S hS i₂ g
  exact ((isSubmersiveProperty B S hS).arrow_mk_iso_iff
    (Arrow.isoMk (f := Arrow.mk (ObjectProperty.homMk (pullback.fst i₂.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS i₂ g ⟶ T')) (g := Arrow.mk k)
      (hP.isoIsPullback T' X sq) (Iso.refl _)
      (by exact hP.isoIsPullback_hom_fst T' X sq))).mp (hg T'.obj T'.property i₂.hom)

/-! ### Descent of submersiveness along an fpqc covering -/

/-- Submersiveness of a morphism of algebraic spaces over `S` descends along an fpqc covering
family of its target: if every base change of `f : X ⟶ Y` along a member of an fpqc covering
`{Y i ⟶ Y}` is submersive, then so is `f`. -/
theorem isSubmersive_of_fpqcCovering {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {I : Type v} (Yi : I → AlgebraicSpaces B S hS) (g : ∀ i, Yi i ⟶ Y)
    (hg : IsFpqcCovering B S hS fun i ↦ (g i).hom)
    (hf : ∀ i, isSubmersiveProperty B S hS
      (ObjectProperty.homMk (pullback.fst (g i).hom f.hom) :
        AlgebraicSpaces.fiberProduct B S hS (g i) f ⟶ Yi i)) :
    isSubmersiveProperty B S hS f := by
  let Xi : I → AlgebraicSpaces B S hS := fun i ↦ AlgebraicSpaces.fiberProduct B S hS (g i) f
  let p : ∀ i, Xi i ⟶ Yi i := fun i ↦ ObjectProperty.homMk (pullback.fst (g i).hom f.hom)
  let q : ∀ i, Xi i ⟶ X := fun i ↦ ObjectProperty.homMk (pullback.snd (g i).hom f.hom)
  have hcomm (i : I) :
      pointsMap B S hS (Yi i).obj (g i).hom ∘ pointsMap B S hS (Xi i).obj (p i).hom =
        pointsMap B S hS X.obj f.hom ∘ pointsMap B S hS (Xi i).obj (q i).hom := by
    rw [← pointsMap_comp, ← pointsMap_comp]
    exact congrArg (pointsMap B S hS (Xi i).obj) pullback.condition
  change Topology.IsQuotientMap (pointsMap B S hS X.obj f.hom)
  rw [Topology.isQuotientMap_iff]
  refine ⟨Topology.isCoinducing_iff.mpr fun V ↦ ⟨fun hV ↦ ?_, fun hV ↦ ?_⟩, fun y ↦ ?_⟩
  · refine isOpen_of_fpqcCovering_preimages B S hS Y.property (fun i ↦ (g i).hom) hg V fun i ↦ ?_
    refine (hf i).isOpen_preimage.mp ?_
    rw [← Set.preimage_comp, hcomm i, Set.preimage_comp]
    exact hV.preimage (continuous_pointsMap B S hS (q i).hom)
  · exact hV.preimage (continuous_pointsMap B S hS f.hom)
  · obtain ⟨i, z, hz⟩ :=
      jointly_surjective_points_of_fpqcCovering B S hS (fun i ↦ (g i).hom) hg y
    obtain ⟨w, hw⟩ := (hf i).surjective z
    exact ⟨pointsMap B S hS (Xi i).obj (q i).hom w, (congrFun (hcomm i) w).symm.trans
      ((congrArg (pointsMap B S hS (Yi i).obj (g i).hom) hw).trans hz)⟩

/-! ### Fpqc locality on the base -/

/-- Universal submersiveness of morphisms of algebraic spaces over `S` is local on the base for the
fpqc topology. -/
@[stacks 0CFW]
instance universallySubmersive_isLocalAtTarget_fpqc :
    (universallySubmersiveMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have heq : universallySubmersiveMorphismProperty B S hS =
      (isSubmersiveProperty B S hS).universally := by
    funext X T g
    exact propext (universallySubmersive_iff_universally_isSubmersive B S hS g)
  rw [heq]
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff fun X Y f R hR ↦ ?_
  refine ⟨fun hf U g _ _ ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f g) hf, fun hlocal ↦ ?_⟩
  obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
  intro X' Y' p a f' sq
  let Z : I → AlgebraicSpaces B S hS := fun i ↦ AlgebraicSpaces.fiberProduct B S hS (gi i) a
  let k : ∀ i, Z i ⟶ Y' := fun i ↦ ObjectProperty.homMk (pullback.snd (gi i).hom a.hom)
  let r : ∀ i, Z i ⟶ Yi i := fun i ↦ ObjectProperty.homMk (pullback.fst (gi i).hom a.hom)
  refine isSubmersive_of_fpqcCovering B S hS f' Z k
    (isFpqcCovering_pullback B S hS gi a hcover.2.2) fun i ↦ ?_
  exact MorphismProperty.universally_of_factorization (isSubmersiveProperty B S hS)
    ((AlgebraicSpaces.isPullback_fiberProduct B S hS (k i) f').paste_vert sq) (gi i) (r i)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (gi i) a).w (hlocal (gi i) (.mk i))

end AlgebraicGeometry.Space

end
