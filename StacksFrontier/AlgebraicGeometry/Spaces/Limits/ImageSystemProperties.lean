module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FieldBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.NoetherianQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericPointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteTypeModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageValuativePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Properties of the system of scheme-theoretic images of a good diagram

Let `B = lim_i B_i` be the limit of a directed inverse system of Noetherian algebraic spaces
over a scheme `S` with affine transition morphisms — an
`AlgebraicGeometry.Space.NoetherianLimitSystem`, Stacks 0CP6 — and let `G` be a diagram

```
X ⟶ W
↓    ↓
B ⟶ B_i
```

as in Stacks 0CP8, that is, an `AlgebraicGeometry.Space.GoodDiagram`. Its inverse system
`AlgebraicGeometry.Space.GoodDiagram.imageSystem` sends a stage `i' ≥ i` to the
scheme-theoretic image `X_{i'}` of `X ⟶ B_{i'} ×_{B_i} W`, and Stacks 0CP9 identifies `X` with
its limit.

This file records the finiteness and separation properties of that system: each `X_{i'}` is a
quasi-compact, locally Noetherian algebraic space over `S` and the transition morphisms
`X_{i'} ⟶ X_{i''}` are affine. These are the hypotheses under which an inverse system of
algebraic spaces with affine transition morphisms may be fed to the limit criteria for
morphisms out of a limit, so they are what makes the system of images usable.

Each `X_{i'}` is a closed subspace of the base change `B_{i'} ×_{B_i} W` of the model, and
`B_{i'} ×_{B_i} W ⟶ B_{i'}` is a base change of the finite-type morphism `W ⟶ B_i`. All four
properties are read off from that: quasi-compactness because `B_{i'}` is quasi-compact and both
morphisms are quasi-compact; local Noetherianity because `B_{i'}` is locally Noetherian and both
morphisms are locally of finite type, which is Stacks 04ZK; affineness of the transitions
because the transition `B_{i'} ⟶ B_{i''}` of the system is affine and the square expressing
`B_{i'} ×_{B_i} W` as its base change is cartesian.

## Main results

The names below live in the namespace `AlgebraicGeometry.Space`, and those concerning a good
diagram in `AlgebraicGeometry.Space.GoodDiagram`; the namespace is omitted where a name is too
long to spell with it.

* `isQuasiSeparated_of_isAffineHom`: an affine morphism of algebraic spaces over `S` is
  quasi-separated.
* `isAbsolutelyQuasiSeparated_limitCone_pt` and
  `isAbsolutelyQuasiSeparated_of_isQuasiSeparated_limitCone`: the limit `B` of the system is
  quasi-separated, and so is any algebraic space quasi-separated over it.
* `GoodDiagram.isPullback_stageTargetMap`: the transition morphism of the base-changed models
  is the base change of the transition morphism of the system.
* `GoodDiagram.imageSystem_isAlgebraicSpace`, `GoodDiagram.imageSystem_isQuasiCompactSpace`
  and `GoodDiagram.imageSystem_isLocallyNoetherian`: each `X_{i'}` is a quasi-compact, locally
  Noetherian algebraic space over `S`.
* `GoodDiagram.imageSystem_map_isAffineHom`: the transition morphisms of the system of images
  are affine.
* `GoodDiagram.imageSystem_hasFiniteEtaleIrreducibleComponents`: every quasi-compact scheme
  étale over `X_{i'}` has finitely many irreducible components.
* `GoodDiagram.imageSystem_hasMonomorphicCodimensionZeroPoints`: if `X` is quasi-separated then
  the points of `X_{i'}` of codimension zero are represented by monomorphisms from spectra of
  fields.
* `GoodDiagram.imageSystem_isAbsolutelyQuasiSeparated` and
  `imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated`: each `X_{i'}` is
  quasi-separated as soon as `X` is quasi-separated, respectively as soon as `X ⟶ B` is.
* `imageSystem_isAbsolutelyQuasiSeparated_of_modelMap` and
  `GoodDiagram.imageSystem_isAbsolutelyQuasiSeparated_of_mono`: two further sufficient
  hypotheses for the same conclusion — that the model be quasi-separated over its stage, and
  that the points of `X_{i'}` of codimension zero be represented by monomorphisms from spectra
  of fields.

## Implementation notes

`AlgebraicGeometry.Space.isQuasiSeparated_of_isAffineHom` repeats a private lemma of
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/FinitePresentationDescent.lean`; it is restated
here, as the two-line composite of Stacks 0CZ1 and Stacks 03KK, rather than exported, so that
no other file is touched.

Quasi-separatedness of `X_{i'}` is the one property that does not follow from the data of a
good diagram alone: the structure records that `W ⟶ B_i` is of finite type, and a finite-type
morphism onto a Noetherian algebraic space has locally Noetherian quasi-compact source but need
not have quasi-separated source — `𝐀¹_k/𝐙` is locally Noetherian, quasi-compact and of finite
type over `k` and is not quasi-separated. Taking the system indexed by a one-point preorder,
the model `W = 𝐀¹_k/𝐙` and `X ⟶ W` the identity gives a good diagram whose only stage image is
`W` itself, so no hypothesis-free statement is available.

The hypothesis under which Stacks 0CP7 produces a good diagram is that `X ⟶ B` be
quasi-separated and of finite type, and that is the hypothesis carried here: the points of
`X_{i'}` of codimension zero are reached from `X` by Stacks 089B, the morphism from the
spectrum of a field reaching such a point is quasi-compact because `X` is quasi-separated, and
condition (5) of Stacks 03JV then supplies a monomorphic representative. Together with the
finiteness of the irreducible components of the quasi-compact schemes étale over `X_{i'}` this
gives reasonableness by Stacks 0BB8, hence decency, and then quasi-separatedness by
Stacks 0BB6. Two variants are offered as well: that `W ⟶ B_i` be quasi-separated, which makes
`X_{i'} ⟶ B_{i'}` quasi-separated and lets Stacks 04ZH, part (2), conclude, and that the points
of `X_{i'}` of codimension zero be represented by monomorphisms from spectra of fields, which
is the third clause of condition (2) of Stacks 0BB9 and is implied by decency of `X_{i'}`.

The route through Stacks 089B needs the stage maps `X ⟶ B_{i'} ×_{B_i} W` to be quasi-compact,
which is `AlgebraicGeometry.Space.GoodDiagram.isQuasiCompact_stageMap`. That lemma — like the
affineness of the projections `B ⟶ B_{i'}` behind it, and like Stacks 0CP9 itself — asks the
index type to be small for the site, so the statements using it live in a section with
`I : Type u` and a hypothesis `Cardinal.mk I < B.cutoff.ord.cof`. The two variants of the
previous paragraph carry neither restriction, which is why they are kept.

## References

* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 03WH](https://stacks.math.columbia.edu/tag/03WH)
* [Stacks Project, Tag 03XH](https://stacks.math.columbia.edu/tag/03XH)
* [Stacks Project, Tag 04CG](https://stacks.math.columbia.edu/tag/04CG)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 06ED](https://stacks.math.columbia.edu/tag/06ED)
* [Stacks Project, Tag 07U2](https://stacks.math.columbia.edu/tag/07U2)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 089B](https://stacks.math.columbia.edu/tag/089B)
* [Stacks Project, Tag 0BB6](https://stacks.math.columbia.edu/tag/0BB6)
* [Stacks Project, Tag 0BB8](https://stacks.math.columbia.edu/tag/0BB8)
* [Stacks Project, Tag 0BB9](https://stacks.math.columbia.edu/tag/0BB9)
* [Stacks Project, Tag 0CP6](https://stacks.math.columbia.edu/tag/0CP6)
* [Stacks Project, Tag 0CP7](https://stacks.math.columbia.edu/tag/0CP7)
* [Stacks Project, Tag 0CP8](https://stacks.math.columbia.edu/tag/0CP8)
* [Stacks Project, Tag 0CP9](https://stacks.math.columbia.edu/tag/0CP9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_ImageSystemProperties
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Affine morphisms are quasi-separated -/

/-- **An affine morphism of algebraic spaces over `S` is quasi-separated.** It is separated by
Stacks 0CZ1, and a separated morphism is quasi-separated by Stacks 03KK. -/
theorem isQuasiSeparated_of_isAffineHom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hf : IsAffineHom B S hS f) : IsQuasiSeparated B S hS f :=
  isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_isAffineHom B S hS f hF hG hf)

/-! ### The limit of a Noetherian limit system -/

section SmallIndex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I]

/-- **The limit of a directed inverse system of Noetherian algebraic spaces with affine
transition morphisms is quasi-separated.** Its projection to a stage is affine, hence
quasi-separated, and that stage is Noetherian, hence quasi-separated. -/
theorem isAbsolutelyQuasiSeparated_limitCone_pt (D : NoetherianLimitSystem B S hS hZ I)
    (hSize : Cardinal.mk I < B.cutoff.ord.cof) :
    IsAbsolutelyQuasiSeparated B S hS hZ D.limitCone.pt := by
  obtain ⟨i⟩ : Nonempty I := inferInstance
  exact isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ D.limit_isAlgebraicSpace
    (D.noetherian i).2.1
    (isQuasiSeparated_of_isAffineHom B S hS (D.limitCone.π.app (op i))
      D.limit_isAlgebraicSpace (D.system_isAlgebraicSpace i)
      (isAffineHom_limitCone_π B S hS D hSize (op i)))

/-- **An algebraic space quasi-separated over the limit of a directed inverse system of
Noetherian algebraic spaces with affine transition morphisms is quasi-separated.** The limit
is quasi-separated, so this is Stacks 04ZH, part (2). -/
theorem isAbsolutelyQuasiSeparated_of_isQuasiSeparated_limitCone
    {D : NoetherianLimitSystem B S hS hZ I} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hSize : Cardinal.mk I < B.cutoff.ord.cof)
    {f : X ⟶ D.limitCone.pt} (hf : IsQuasiSeparated B S hS f) :
    IsAbsolutelyQuasiSeparated B S hS hZ X :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX
    (isAbsolutelyQuasiSeparated_limitCone_pt D hSize) hf

end SmallIndex

namespace GoodDiagram

section Properties

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ D.limitCone.pt}
    (G : GoodDiagram B S hS hZ D f)

/-! ### The base-changed models -/

/-- The transition morphism `B_{i'} ×_{B_i} W ⟶ B_{i''} ×_{B_i} W` of the base-changed models
is the base change of the transition morphism `B_{i'} ⟶ B_{i''}` of the system along the
projection of the base-changed model to its stage. -/
lemma isPullback_stageTargetMap {j k : Over (op G.index)} (a : j ⟶ k) :
    IsPullback (stageTargetMap G a) (pullback.fst (D.system.map j.hom) G.modelMap)
      (pullback.fst (D.system.map k.hom) G.modelMap) (D.system.map a.left) := by
  refine IsPullback.of_right ?_ (stageTargetMap_fst G a)
    (IsPullback.of_hasPullback (D.system.map k.hom) G.modelMap).flip
  have hcomp : D.system.map a.left ≫ D.system.map k.hom = D.system.map j.hom := by
    rw [← D.system.map_comp, Over.w a]
  rw [stageTargetMap_snd, hcomp]
  exact (IsPullback.of_hasPullback (D.system.map j.hom) G.modelMap).flip

/-- The projection `B_{i'} ×_{B_i} W ⟶ B_{i'}` of a base-changed model is quasi-compact with
quasi-compact target, so the base-changed model is a quasi-compact algebraic space over `S`. -/
lemma isQuasiCompactSpace_stageTarget (j : Over (op G.index)) :
    IsQuasiCompactSpace B S hS (pullback (D.system.map j.hom) G.modelMap) :=
  G.isFiniteType.2 (D.system.obj j.left) (D.system_isAlgebraicSpace j.left.unop)
    (D.noetherian j.left.unop).1 (D.system.map j.hom)

/-- The projection `B_{i'} ×_{B_i} W ⟶ B_{i'}` of a base-changed model is locally of finite
type, being a base change of the finite-type morphism `W ⟶ B_i`. -/
lemma isLocallyOfFiniteType_stageTarget_fst (j : Over (op G.index)) :
    IsLocallyOfFiniteType B S hS (pullback.fst (D.system.map j.hom) G.modelMap) :=
  isLocallyOfFiniteType_pullback_fst' B S hS G.model_isAlgebraicSpace
    (D.system_isAlgebraicSpace G.index) (D.system_isAlgebraicSpace j.left.unop) G.modelMap
    (D.system.map j.hom) G.isFiniteType.1

/-! ### The system of scheme-theoretic images -/

/-- Every member `X_{i'}` of the system of scheme-theoretic images of a good diagram is an
algebraic space over `S`, being a closed subspace of the base-changed model. -/
theorem imageSystem_isAlgebraicSpace (j : Over (op G.index)) :
    IsAlgebraicSpace B S hS ((imageSystem G).obj j) :=
  (isClosedSubspace_stageImage G j).1

/-- Every member `X_{i'}` of the system of scheme-theoretic images of a good diagram is a
quasi-compact algebraic space over `S`: it is a closed subspace of the base-changed model
`B_{i'} ×_{B_i} W`, which is quasi-compact over the quasi-compact stage `B_{i'}`. -/
theorem imageSystem_isQuasiCompactSpace (j : Over (op G.index)) :
    IsQuasiCompactSpace B S hS ((imageSystem G).obj j) :=
  isQuasiCompactSpace_source_of_isQuasiCompact B S hS (isAlgebraicSpace_stageTarget G j)
    (isQuasiCompactSpace_stageTarget G j)
    (isQuasiCompact_of_isClosedImmersion' B S hS (isClosedSubspace_stageImage G j).2)

/-- **The transition morphisms of the system of scheme-theoretic images are affine.** The
composite `X_{i'} ⟶ X_{i''} ⟶ B_{i''} ×_{B_i} W` is the inclusion of `X_{i'}` followed by the
transition morphism of the base-changed models, which are affine respectively as a closed
immersion and as a base change of an affine transition morphism of the system; the inclusion of
`X_{i''}` is a monomorphism, so the transition morphism is a base change of that composite. -/
theorem imageSystem_map_isAffineHom {j k : Over (op G.index)} (a : j ⟶ k) :
    IsAffineHom B S hS ((imageSystem G).map a) := by
  have hstage : IsAffineHom B S hS (stageTargetMap G a) :=
    isAffineHom_of_isPullback (isPullback_stageTargetMap G a).flip
      (D.transition_affine a.left)
  have hι : IsAffineHom B S hS (stageImage G j).ι :=
    isAffineHom_of_isClosedImmersion B S hS _ (isClosedSubspace_stageImage G j).2
  have hcomp : IsAffineHom B S hS ((imageSystem G).map a ≫ (stageImage G k).ι) := by
    rw [show (imageSystem G).map a = imageTransition G a from rfl, imageTransition_ι]
    exact isAffineHom_comp B S hS _ _ hι hstage
  exact isAffineHom_of_isPullback
    (IsPullback.of_vert_isIso_mono (fst := (imageSystem G).map a) (snd := 𝟙 _)
      (f := (stageImage G k).ι) (g := (imageSystem G).map a ≫ (stageImage G k).ι)
      ⟨by rw [Category.id_comp]⟩).flip hcomp

/-- **Every member `X_{i'}` of the system of scheme-theoretic images of a good diagram is
locally Noetherian.** The composite `X_{i'} ⟶ B_{i'} ×_{B_i} W ⟶ B_{i'}` is locally of finite
type, being a closed immersion followed by a base change of the finite-type morphism `W ⟶ B_i`,
and the stage `B_{i'}` is locally Noetherian; this is Stacks 04ZK. -/
theorem imageSystem_isLocallyNoetherian (j : Over (op G.index)) :
    HasEtaleLocalProperty B S hS ((imageSystem G).obj j)
      (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
  isLocallyNoetherian_of_isLocallyOfFiniteType B S hS (imageSystem_isAlgebraicSpace G j)
    (D.system_isAlgebraicSpace j.left.unop)
    ((stageImage G j).ι ≫ pullback.fst (D.system.map j.hom) G.modelMap)
    (isLocallyOfFiniteType_comp B S hS (imageSystem_isAlgebraicSpace G j)
      (isAlgebraicSpace_stageTarget G j) (D.system_isAlgebraicSpace j.left.unop) _ _
      (isLocallyOfFiniteType_of_isImmersion B S hS _
        (isImmersion_of_isClosedImmersion B S hS (isClosedSubspace_stageImage G j).2))
      (isLocallyOfFiniteType_stageTarget_fst G j))
    (D.noetherian j.left.unop).2.2

/-- **Every quasi-compact scheme étale over a member `X_{i'}` of the system of scheme-theoretic
images of a good diagram has finitely many irreducible components.** Such a scheme is locally
Noetherian because `X_{i'}` is, hence Noetherian, and the underlying space of a Noetherian
scheme has finitely many irreducible components. This is the first clause of condition (2) of
Stacks 0BB9. -/
theorem imageSystem_hasFiniteEtaleIrreducibleComponents (j : Over (op G.index)) :
    HasFiniteEtaleIrreducibleComponents B S hS ((imageSystem G).obj j) := by
  intro U a hUcompact ha
  have hloc : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    (exists_atlas_iff_forall_etale B S hS ((imageSystem G).obj j)
        (fun T : Scheme.{u} => IsLocallyNoetherian T)
        (imageSystem_isAlgebraicSpace G j)).1 (imageSystem_isLocallyNoetherian G j) U a
      ((isEtale_iff_presheaf_of_yoneda B S hS a).1 ha)
  have : _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj U) := {}
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- **A member `X_{i'}` of the system of scheme-theoretic images of a good diagram whose model
is quasi-separated over its stage is quasi-separated.** The composite
`X_{i'} ⟶ B_{i'} ×_{B_i} W ⟶ B_{i'}` is quasi-separated, being a closed immersion followed by a
base change of `W ⟶ B_i`, and the Noetherian stage `B_{i'}` is quasi-separated; this is
Stacks 04ZH, part (2). -/
theorem imageSystem_isAbsolutelyQuasiSeparated_of_modelMap
    (hmodel : IsQuasiSeparated B S hS G.modelMap) (j : Over (op G.index)) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((imageSystem G).obj j) :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ (imageSystem_isAlgebraicSpace G j)
    (D.noetherian j.left.unop).2.1
    (isQuasiSeparated_comp B S hS (imageSystem_isAlgebraicSpace G j)
      (isAlgebraicSpace_stageTarget G j) (stageImage G j).ι
      (pullback.fst (D.system.map j.hom) G.modelMap)
      (isQuasiSeparated_of_isClosedImmersion B S hS (isClosedSubspace_stageImage G j).2)
      (isQuasiSeparated_of_isPullback B S hS
        (IsPullback.of_hasPullback (D.system.map j.hom) G.modelMap).flip hmodel))

/-- **A member `X_{i'}` of the system of scheme-theoretic images of a good diagram all of whose
points of codimension zero are represented by a monomorphism from the spectrum of a field is
quasi-separated.** Those monomorphisms are the third clause of condition (2) of Stacks 0BB9 and
`AlgebraicGeometry.Space.GoodDiagram.imageSystem_hasFiniteEtaleIrreducibleComponents` is the
first, so `X_{i'}` is reasonable by Stacks 0BB8 and hence decent; it is also locally
Noetherian, so Stacks 0BB6 applies. -/
theorem imageSystem_isAbsolutelyQuasiSeparated_of_mono (j : Over (op G.index))
    (hmono : HasMonomorphicCodimensionZeroPoints B S hS ((imageSystem G).obj j)) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((imageSystem G).obj j) :=
  isAbsolutelyQuasiSeparated_of_isLocallyNoetherian_of_isDecentSpace B S hS hZ _
    (imageSystem_isAlgebraicSpace G j) (imageSystem_isLocallyNoetherian G j)
    (isDecentSpace_of_isReasonableSpace B S hS (imageSystem_isAlgebraicSpace G j)
      (isReasonableSpace_of_finite_irreducibleComponents_of_mono B S hS _
        (imageSystem_isAlgebraicSpace G j)
        (fun U hU a ha => imageSystem_hasFiniteEtaleIrreducibleComponents G j U a hU
          (isEtale_of_presheaf_etale B S hS ha))
        hmono))

end Properties

section SmallIndex

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type u} [Preorder I] [Nonempty I]
    [IsDirectedOrder I] {D : NoetherianLimitSystem B S hS hZ I}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ D.limitCone.pt}
    (G : GoodDiagram B S hS hZ D f)

/-- **The points of codimension zero of a member `X_{i'}` of the system of scheme-theoretic
images of a good diagram with quasi-separated source are represented by monomorphisms from
spectra of fields.** The stage map `X ⟶ B_{i'} ×_{B_i} W` is quasi-compact, so by Stacks 089B
its scheme-theoretic image `X_{i'}` receives a field-valued point of `X` above any point of
codimension zero; the morphism representing it is `Spec k ⟶ X ⟶ X_{i'}`, which is
quasi-compact because `X` is quasi-separated and `Spec k` is affine, and a point with a
quasi-compact field-valued representative has a monomorphic one by Stacks 03JV. -/
theorem imageSystem_hasMonomorphicCodimensionZeroPoints
    (hSize : Cardinal.mk I < B.cutoff.ord.cof) (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) (j : Over (op G.index)) :
    HasMonomorphicCodimensionZeroPoints B S hS ((imageSystem G).obj j) := by
  intro z hz
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_toSchemeTheoreticImage_of_localRingDimension_eq_zero
    B S hS (stageMap G j) hX (isAlgebraicSpace_stageTarget G j)
    (isQuasiCompact_stageMap G hSize j) z hz
  have hqcp : IsQuasiCompact B S hS (fieldMorphism B S hS X p) :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS (hZ := hZ) hX hqs
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS (p.siteObject B S hS X)
        (inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))))
      (fieldMorphism B S hS X p)
  have hqci : IsQuasiCompact B S hS (toSchemeTheoreticImage B S hS (stageMap G j)) :=
    isQuasiCompact_of_comp_mono B S hS _ _
      (by rw [toSchemeTheoreticImage_ι]; exact isQuasiCompact_stageMap G hSize j)
  refine (hasQuasiCompactMonomorphicFieldRepresentative_of_hasQuasiCompactFieldRepresentative
      B S hS _ (imageSystem_isAlgebraicSpace G j)
      ⟨FieldValuedPoint.map B S hS X (toSchemeTheoreticImage B S hS (stageMap G j)) p, ?_,
        ?_⟩).hasMonomorphicFieldRepresentative B S hS _
  · rwa [← pointsMap_class]
  · rw [fieldMorphism_map]
    exact isQuasiCompact_comp B S hS hX (imageSystem_isAlgebraicSpace G j) _ _ hqcp hqci

/-- **A member `X_{i'}` of the system of scheme-theoretic images of a good diagram with
quasi-separated source is quasi-separated.** The points of `X_{i'}` of codimension zero are
represented by monomorphisms from spectra of fields, so Stacks 0BB8 makes `X_{i'}` reasonable,
hence decent, and Stacks 0BB6 applies. -/
theorem imageSystem_isAbsolutelyQuasiSeparated
    (hSize : Cardinal.mk I < B.cutoff.ord.cof) (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) (j : Over (op G.index)) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((imageSystem G).obj j) :=
  imageSystem_isAbsolutelyQuasiSeparated_of_mono G j
    (imageSystem_hasMonomorphicCodimensionZeroPoints G hSize hX hqs j)

/-- **A member `X_{i'}` of the system of scheme-theoretic images of a good diagram whose
source is quasi-separated over the limit is quasi-separated.** The limit is quasi-separated,
so the source is, and
`AlgebraicGeometry.Space.GoodDiagram.imageSystem_isAbsolutelyQuasiSeparated` applies. This is
the hypothesis under which Stacks 0CP7 produces a good diagram. -/
theorem imageSystem_isAbsolutelyQuasiSeparated_of_isQuasiSeparated
    (hSize : Cardinal.mk I < B.cutoff.ord.cof) (hX : IsAlgebraicSpace B S hS X)
    (hqs : IsQuasiSeparated B S hS f) (j : Over (op G.index)) :
    IsAbsolutelyQuasiSeparated B S hS hZ ((imageSystem G).obj j) :=
  imageSystem_isAbsolutelyQuasiSeparated G hSize hX
    (isAbsolutelyQuasiSeparated_of_isQuasiSeparated_limitCone hX hSize hqs) j

end SmallIndex

end GoodDiagram


end AlgebraicGeometry.Space

end
