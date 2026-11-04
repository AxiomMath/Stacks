module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Proper

/-!
# Closed immersions of algebraic spaces are proper

A closed immersion of algebraic spaces over a scheme `S` is proper: it is separated, of
finite type and universally closed.

## Main results

* `AlgebraicGeometry.Space.isProper_of_isClosedImmersion` is properness of a closed
  immersion of algebraic spaces.
* `AlgebraicGeometry.Space.inverseImage_isClosedImmersion_le_monomorphisms`: a morphism of
  the big fppf category over `S` whose underlying morphism of schemes is a closed immersion
  is a monomorphism.
* `AlgebraicGeometry.Space.mono_of_isClosedImmersion` and
  `AlgebraicGeometry.Space.isSeparated_of_isClosedImmersion`: a closed immersion is a
  monomorphism of presheaves, hence separated. The latter is Tag 04CH.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isClosedImmersion` and
  `AlgebraicGeometry.Space.isFiniteType_of_isClosedImmersion`: a closed immersion is
  locally of finite type and of finite type.
* `AlgebraicGeometry.Space.universallyClosed_of_presheafIsClosedMap` and
  `AlgebraicGeometry.Space.universallyClosed_of_isClosedImmersion`: a morphism each of
  whose represented base changes is a closed map of schemes is universally closed, and a
  closed immersion is such a morphism.

## Implementation notes

Each of the three conjuncts of `AlgebraicGeometry.Space.IsProper` is proved separately and
they are assembled by `AlgebraicGeometry.Space.IsProper.mk'`.

Separatedness is the formal half. A closed immersion of schemes is a monomorphism, and
`AlgebraicGeometry.BigFppfOver.toScheme` is faithful, so each represented base change of a
closed immersion of algebraic spaces is a monomorphism of the site; by
`CategoryTheory.MorphismProperty.presheaf_monomorphisms_le_monomorphisms` the morphism of
presheaves is then itself a monomorphism, its relative diagonal is an isomorphism, and an
isomorphism of presheaves is a closed immersion by
`CategoryTheory.MorphismProperty.presheaf_of_isIso`.

Finite type splits as local finite type and quasi-compactness. Quasi-compactness is
`AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion'` of Tag 04CG. Local finite
type is stated on the étale charts rather than on the represented base changes, so it goes
through the implication of Tag 03MJ in the form
`AlgebraicGeometry.Space.presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType`, applied
to the represented base changes of the closed immersion: those are closed immersions of
schemes, hence locally of finite type.

Universal closedness is the substantial half, and is the points-versus-base-change bridge of
`StacksFrontier/AlgebraicGeometry/Spaces/PointsBaseChange.lean`: a morphism each of whose
represented base changes is a closed map of schemes has closed map on points after every base
change, which is exactly the quantified condition of Tag 03HI, and a closed immersion of
schemes is a closed map because it is a closed embedding on underlying spaces.

The two algebraicity hypotheses of the tagged statement record that Tag 04XZ is a statement
about algebraic spaces. Neither the statement nor the proof needs them: the universally
closed condition of Tag 03HI is stated for an arbitrary morphism of presheaves, because
`AlgebraicGeometry.Space.pointTopology` is, and representability is already part of
`AlgebraicGeometry.Space.IsClosedImmersion`. They are passed down to
`AlgebraicGeometry.Space.universallyClosed_of_presheafIsClosedMap`, where they are named with
a leading underscore to record that its body does not inspect them.

Instance synthesis does not find `CategoryTheory.MorphismProperty.ContainsIdentities` or
`CategoryTheory.MorphismProperty.RespectsIso` for an inverse-image property, nor
`CategoryTheory.MorphismProperty.ContainsIdentities` for
`AlgebraicGeometry.IsClosedImmersion` through
`CategoryTheory.MorphismProperty.IsMultiplicative`, so the chain of four facts is spelled
out as explicit terms in `AlgebraicGeometry.Space.isSeparated_of_isClosedImmersion`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionQC.lean`.

## References

* [Stacks Project, Tag 03HI](https://stacks.math.columbia.edu/tag/03HI)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 04CH](https://stacks.math.columbia.edu/tag/04CH)
* [Stacks Project, Tag 04XZ](https://stacks.math.columbia.edu/tag/04XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### A closed immersion is separated -/

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is a closed
immersion is a monomorphism: a closed immersion of schemes is a monomorphism and
`AlgebraicGeometry.BigFppfOver.toScheme` is faithful. -/
theorem inverseImage_isClosedImmersion_le_monomorphisms :
    MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.monomorphisms (BigFppfOver B S hS) := by
  intro U V h hh
  have : _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map h) := hh
  exact (BigFppfOver.toScheme B S hS).mono_of_mono_map
    (inferInstanceAs (Mono ((BigFppfOver.toScheme B S hS).map h)))

/-- A closed immersion of algebraic spaces over `S` is a monomorphism of presheaves: each of
its represented base changes is a monomorphism of the site, and a morphism of presheaves all
of whose represented base changes are monomorphisms is a monomorphism. -/
theorem mono_of_isClosedImmersion (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) : Mono f :=
  MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone
      (inverseImage_isClosedImmersion_le_monomorphisms B S hS) _ hf)

/-- **Stacks 04CH.** A closed immersion of algebraic spaces over `S` is separated. Its
relative diagonal is an isomorphism, because the morphism is a monomorphism, and an
isomorphism of presheaves is a closed immersion. -/
@[stacks 04CH]
theorem isSeparated_of_isClosedImmersion (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) :
    IsSeparated B S hS f := by
  have hmono : Mono f := mono_of_isClosedImmersion B S hS f hf
  have hC₁ : MorphismProperty.ContainsIdentities
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have hC₂ : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.respectsIso
  have hI₁ : MorphismProperty.ContainsIdentities
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
  have hI₂ : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
  exact MorphismProperty.presheaf_of_isIso _ (pullback.diagonal f)

/-! ### A closed immersion is of finite type -/

/-- A closed immersion of algebraic spaces over `S` has every represented base change in any
property of schemes satisfied by all closed immersions. -/
private theorem presheaf_inverseImage_of_isClosedImmersion {P : MorphismProperty Scheme.{u}}
    (hP : (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) ≤ P)
    (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf f :=
  MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) hP) _ hf

/-- **A closed immersion of algebraic spaces over `S` is locally of finite type.** Each of
its represented base changes is a closed immersion of schemes, hence locally of finite type,
and being locally of finite type passes from the represented base changes to the étale charts
by the implication of Tag 03MJ. -/
theorem isLocallyOfFiniteType_of_isClosedImmersion (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f) :
    IsLocallyOfFiniteType B S hS f :=
  presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType B S hS f
    (presheaf_inverseImage_of_isClosedImmersion B S hS
      (P := @LocallyOfFiniteType.{u}) (fun _ _ _ _ ↦ inferInstance) f hf)

/-- **A closed immersion of algebraic spaces over `S` is of finite type.** It is locally of
finite type, and quasi-compact by Tag 04CG. -/
theorem isFiniteType_of_isClosedImmersion (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) :
    IsFiniteType B S hS f :=
  ⟨isLocallyOfFiniteType_of_isClosedImmersion B S hS f hf,
    isQuasiCompact_of_isClosedImmersion' B S hS hf⟩

/-! ### A closed immersion is universally closed -/

/-- A morphism of algebraic spaces over `S` each of whose represented base changes is a
closed map of schemes is universally closed: the bridge
`AlgebraicGeometry.Space.isClosedMap_pointsMap_pullback_fst_of_presheafIsClosedMap` is
precisely the closed-map condition after an arbitrary base change. -/
theorem universallyClosed_of_presheafIsClosedMap
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : (MorphismProperty.inverseImage
      (topologically @IsClosedMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    UniversallyClosed B S hS f :=
  fun _ _ g ↦ isClosedMap_pointsMap_pullback_fst_of_presheafIsClosedMap B S hS f hf g

/-- **A closed immersion of algebraic spaces over `S` is universally closed.** Each of its
represented base changes is a closed immersion of schemes, hence a closed embedding on
underlying spaces and in particular a closed map. -/
theorem universallyClosed_of_isClosedImmersion
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f) :
    UniversallyClosed B S hS f := by
  exact universallyClosed_of_presheafIsClosedMap B S hS hX hY f
    (presheaf_inverseImage_of_isClosedImmersion B S hS
      (P := topologically @IsClosedMap) (fun _ _ _ h ↦ h.isClosedEmbedding.isClosedMap) f hf)

/-! ### Properness -/

/-- **Stacks 04XZ.** A closed immersion of algebraic spaces over `S` is proper. -/
@[stacks 04XZ]
theorem isProper_of_isClosedImmersion
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) :
    IsProper B S hS f :=
  IsProper.mk' B S hS (isSeparated_of_isClosedImmersion B S hS f hf)
    (isFiniteType_of_isClosedImmersion B S hS f hf)
    (universallyClosed_of_isClosedImmersion B S hS hX hY f hf)

end AlgebraicGeometry.Space

end

