module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open

/-!
# Openness of morphisms of algebraic spaces is fppf local on the source

Let `S` be a scheme contained in a big fppf site `B`. Being open and being universally open
(**Stacks 03Z2**) are local on the source for the fppf topology of **Stacks 03YH** on the
algebraic spaces over `S`: a morphism `f : X ⟶ Y` is open, respectively universally open,
exactly when `g ≫ f` is for every member `g : Xᵢ ⟶ X` of one fppf covering of its source.

Both directions rest on one fact: a member of an fppf covering is flat and locally of finite
presentation, hence universally open by **Stacks 042S**. Ascent is then immediate from
**Stacks 03Z4**, the composition of two (universally) open morphisms. Descent for openness is
the statement that a map which becomes open after composing with each member of a jointly
surjective family of continuous maps into its source is open, applied to the maps on points;
descent for universal openness reduces to it, because the fppf covering of the source
base-changes to an fppf covering of the base-changed source by **Stacks 03Y9**, so that the
source locality of openness already proved applies to each base change.

## Main results

* `AlgebraicGeometry.Space.isOpenMorphism_isLocalAtSource_fppf`: **Stacks 06EX**.
* `AlgebraicGeometry.Space.universallyOpen_isLocalAtSource_fppf`: **Stacks 06EY**.

## Implementation notes

Both are registered as instances, in the shape in which
`CategoryTheory.MorphismProperty.IsLocalAtSource`'s API consumes them, as the finiteness
properties of **Stacks 06EV** and **Stacks 06EW** are. Unlike those two, neither predicate is
of the form `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`, so neither is an instance of the
transfer `AlgebraicGeometry.Space.Topology.isLocalAtSource_of_schemes` of **Stacks 06ER**; the
argument is carried out on the point topology of **Stacks 03BX** directly.

The index universe `v` of a covering family is independent of the universe `u` of the schemes,
as in `AlgebraicGeometry.Space.Topology.precoverage`.

## References

* [Stacks Project, Tag 06EX](https://stacks.math.columbia.edu/tag/06EX)
* [Stacks Project, Tag 06EY](https://stacks.math.columbia.edu/tag/06EY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

section

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance (priority := high) hasPullback_presheaf_openSourceLocality
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- An isomorphism of algebraic spaces over `S` is universally open: each of its base changes
is again an isomorphism, and the map on points of an isomorphism is a homeomorphism. -/
private theorem universallyOpen_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G)
    [IsIso e] : UniversallyOpen B S hS e := by
  intro Z _ g
  have : IsIso (pullback.fst g e) := (IsPullback.of_hasPullback g e).isIso_fst_of_isIso
  exact (pointsHomeomorphOfIso B S hS (asIso (pullback.fst g e))).isOpenMap

/-- Being open is invariant under pre- and postcomposition with an isomorphism of algebraic
spaces over `S`, so it is a morphism property of the category of **Stacks 02X2** respecting
isomorphisms. This is what `CategoryTheory.MorphismProperty.IsLocalAtSource` asks of it. -/
private theorem isOpenMorphism_respectsIso :
    MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) ↦ IsOpenMorphism B S hS f.hom) :=
  MorphismProperty.RespectsIso.mk _
    (fun e _ hf ↦ isOpenMap_pointsMap_of_comp_isIso B S hS
      ((ObjectProperty.ι _).mapIso e).hom rfl hf)
    (fun e _ hf ↦ IsOpenMorphism.comp B S hS
      (pointsHomeomorphOfIso B S hS ((ObjectProperty.ι _).mapIso e)).isOpenMap hf)

/-- Being universally open is invariant under pre- and postcomposition with an isomorphism of
algebraic spaces over `S`, by Stacks 03Z4 and the universal openness of an isomorphism. -/
private theorem universallyOpen_respectsIso :
    MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) ↦ UniversallyOpen B S hS f.hom) :=
  MorphismProperty.RespectsIso.mk _
    (fun {A C D} e _ hf ↦ universallyOpen_comp B S hS A.property C.property D.property _ _
      (universallyOpen_of_isIso B S hS ((ObjectProperty.ι _).mapIso e).hom) hf)
    (fun {A C D} e _ hf ↦ universallyOpen_comp B S hS A.property C.property D.property _ _ hf
      (universallyOpen_of_isIso B S hS ((ObjectProperty.ι _).mapIso e).hom))

/-- A member of an fppf covering family of algebraic spaces over `S` is universally open: it is
flat and locally of finite presentation, so Stacks 042S applies. -/
private theorem universallyOpen_of_isFppfCovering {I : Type v}
    {X : AlgebraicSpaces B S hS} (Xi : I → AlgebraicSpaces B S hS) (gi : ∀ i, Xi i ⟶ X)
    (h : IsFppfCovering B S hS (fun i ↦ (Xi i).obj) (fun i ↦ (gi i).hom)) (i : I) :
    UniversallyOpen B S hS (gi i).hom :=
  universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation B S hS (Xi i).property X.property
    (gi i).hom (h.flat i) (h.locallyOfFinitePresentation i)

/-- **Stacks 06EX.** Being open, for a morphism of algebraic spaces over `S`, is local on the
source for the fppf topology. -/
@[stacks 06EX]
instance isOpenMorphism_isLocalAtSource_fppf :
    MorphismProperty.IsLocalAtSource
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) ↦ IsOpenMorphism B S hS f.hom)
      (Topology.fppf.precoverage.{u, v} B S hS) := by
  have := isOpenMorphism_respectsIso B S hS
  refine MorphismProperty.IsLocalAtSource.mk_of_iff fun {A C f R} hR ↦ ?_
  obtain ⟨I, Xi, gi, rfl, -, -, hfppf⟩ := hR
  constructor
  · rintro hf _ _ ⟨i⟩
    exact IsOpenMorphism.comp B S hS hf (isOpen_of_universallyOpen B S hS A.property _
      (universallyOpen_of_isFppfCovering B S hS Xi gi hfppf i))
  · intro hall
    refine isOpenMap_of_iUnion_range
      (fun i ↦ pointsMap B S hS (Xi i).obj (gi i).hom) (pointsMap B S hS A.obj f.hom)
      hfppf.jointly_surjective (fun i ↦ continuous_pointsMap B S hS _) fun i ↦ ?_
    have h : IsOpenMap (pointsMap B S hS (Xi i).obj ((gi i).hom ≫ f.hom)) :=
      hall (g := gi i) ⟨i⟩
    rwa [pointsMap_comp] at h

/-- **Stacks 06EY.** Being universally open, for a morphism of algebraic spaces over `S`, is
local on the source for the fppf topology. -/
@[stacks 06EY]
instance universallyOpen_isLocalAtSource_fppf :
    MorphismProperty.IsLocalAtSource
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y) ↦ UniversallyOpen B S hS f.hom)
      (Topology.fppf.precoverage.{u, v} B S hS) := by
  have := universallyOpen_respectsIso B S hS
  refine MorphismProperty.IsLocalAtSource.mk_of_iff fun {A C f R} hR ↦ ?_
  obtain ⟨I, Xi, gi, rfl, -, -, hfppf⟩ := hR
  constructor
  · rintro hf _ _ ⟨i⟩
    exact universallyOpen_comp B S hS (Xi i).property A.property C.property _ _
      (universallyOpen_of_isFppfCovering B S hS Xi gi hfppf i) hf
  · intro hall Z hZ g
    -- The base change `Z ×_C A` of `f` along `g`, with its two projections.
    let P : AlgebraicSpaces B S hS := ⟨pullback g f.hom,
      isAlgebraicSpace_pullback B S hS g f.hom hZ A.property C.property⟩
    let x : P ⟶ A := ObjectProperty.homMk (pullback.snd g f.hom)
    let p : P ⟶ (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) :=
      ObjectProperty.homMk (pullback.fst g f.hom)
    -- Stacks 03Y9: the covering base-changes to a covering of `Z ×_C A`.
    -- Stacks 06EX: openness of `Z ×_C A ⟶ Z` may be checked on that covering.
    refine (isOpenMorphism_isLocalAtSource_fppf.{u, v} B S hS).of_forall_comp
      (f := p) (R := Presieve.ofArrows (fun i ↦ AlgebraicSpaces.fiberProduct B S hS x (gi i))
        fun i ↦ ObjectProperty.homMk (pullback.fst x.hom (gi i).hom))
      ⟨I, _, _, rfl, P.property,
        fun i ↦ (AlgebraicSpaces.fiberProduct B S hS x (gi i)).property,
        isFppfCovering_fibreProduct B S hS Xi gi x hfppf⟩ ?_
    rintro _ _ ⟨i⟩
    -- Each composite `(Z ×_C A) ×_A Xᵢ ⟶ Z ×_C A ⟶ Z` is a base change of `gᵢ ≫ f`.
    exact isOpenMap_pointsMap_of_comp_isIso B S hS
      (pullbackLeftPullbackSndIso g f.hom (gi i).hom).hom
      (pullbackLeftPullbackSndIso_hom_fst g f.hom (gi i).hom)
      (hall (g := gi i) ⟨i⟩ Z hZ g)

end

end AlgebraicGeometry.Space

end
