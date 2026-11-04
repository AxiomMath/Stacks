module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# Affine algebraic spaces

An algebraic space over `S` is *affine* when it is represented by an object of the big fppf
site of `S` whose underlying scheme is affine. This is the object-level counterpart of the
affineness of a *morphism* of algebraic spaces, `AlgebraicGeometry.Space.IsAffineHom`, and
it is the vocabulary in which the affineness statements of Stacks 07VP, 07VS and 0GHL are
phrased.

## Main definitions

* `AlgebraicGeometry.Space.IsAffineSpace` is affineness of an algebraic space over `S`.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_yoneda`: a presheaf represented by an affine
  object of the site is affine.
* `AlgebraicGeometry.Space.IsAffineSpace.of_iso`: affineness is invariant under
  isomorphism of presheaves.
* `AlgebraicGeometry.Space.IsAffineSpace.isAlgebraicSpace`: an affine presheaf is an
  algebraic space.
* `AlgebraicGeometry.Space.IsAffineSpace.isQuasiCompactSpace`: an affine algebraic space is
  quasi-compact.
* `AlgebraicGeometry.Space.IsFinite.isAffineHom`: a finite morphism of algebraic spaces is
  affine.
* `AlgebraicGeometry.Space.IsAffineHom.isAffineSpace_source` and
  `AlgebraicGeometry.Space.IsFinite.isAffineSpace_source`: the source of an affine, in
  particular of a finite, morphism with affine target is affine.

## Implementation notes

Affineness of a presheaf needs neither the sheaf condition nor an atlas, so it is stated
for an arbitrary presheaf on the big fppf category over `S`; algebraicity then follows from
Stacks 025Z and is `AlgebraicGeometry.Space.IsAffineSpace.isAlgebraicSpace`. The
representing object is required to lie in the chosen big fppf site, exactly as in the
source, where affineness of an algebraic space is representability by an affine scheme of
the fixed big site.

The identification of the presheaf with the one it represents is recorded as
`Nonempty (F ≅ yoneda.obj T)` rather than as an equality: the representing object is only
determined up to isomorphism, and every consumer uses the isomorphism rather than its
choice.

Both source-affineness results are instances of the same observation: an affine morphism
has, by definition, an affine representing object over every affine test object of the
site, and the base change along an *isomorphism* of the target with a representable
presheaf is the source itself, because a pullback square one of whose legs is an
isomorphism has the opposite leg an isomorphism.

Finiteness of a morphism of algebraic spaces, `AlgebraicGeometry.Space.IsFinite`, is the
affine-base-change condition of Stacks 03ZP with the extra requirement that the projection
of the representing object be a finite morphism of schemes; forgetting that requirement is
affineness in the sense of Stacks 03WF, up to the passage between an affine object of the
big fppf category over `S` and an object of the big affine fppf category over `S`.

## References

* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A presheaf on the big fppf category over `S` is an *affine* algebraic space when it is
isomorphic to the presheaf represented by an object of the site whose underlying scheme is
affine.

Many predicates of this library share this signature; the nearest,
`AlgebraicGeometry.Space.IsQuasiAffineSpace` of
`StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffine`, asks
`AlgebraicGeometry.Scheme.IsQuasiAffine` of the representing scheme where this asks
`AlgebraicGeometry.IsAffine`, so the two are not interchangeable. -/
abbrev IsAffineSpace (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop :=
  ∃ T : BigFppfOver B S hS,
    IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧ Nonempty (F ≅ yoneda.obj T)

/-- The presheaf represented by an object of the big fppf site of `S` with affine underlying
scheme is an affine algebraic space. -/
theorem isAffineSpace_yoneda (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) :
    IsAffineSpace B S hS (yoneda.obj T) :=
  ⟨T, hT, ⟨Iso.refl _⟩⟩

variable {B S hS}

/-- A presheaf isomorphic to an affine algebraic space is an affine algebraic space. -/
theorem IsAffineSpace.of_iso {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : IsAffineSpace B S hS F) (e : F ≅ F') : IsAffineSpace B S hS F' := by
  obtain ⟨T, hT, ⟨i⟩⟩ := h
  exact ⟨T, hT, ⟨e.symm.trans i⟩⟩

/-- An affine algebraic space is an algebraic space: by Stacks 025Z the presheaf it is
isomorphic to is one, and being an algebraic space is invariant under isomorphism. -/
theorem IsAffineSpace.isAlgebraicSpace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : IsAffineSpace B S hS F) : IsAlgebraicSpace B S hS F := by
  obtain ⟨T, -, ⟨e⟩⟩ := h
  exact (isAlgebraicSpace_yoneda B S hS T).of_iso e.symm

/-- An affine algebraic space is quasi-compact in the sense of Stacks 03E3: the
isomorphism with the presheaf represented by the affine object is itself a surjective étale
chart, and an affine scheme is quasi-compact. -/
theorem IsAffineSpace.isQuasiCompactSpace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : IsAffineSpace B S hS F) : IsQuasiCompactSpace B S hS F := by
  obtain ⟨T, hT, ⟨e⟩⟩ := h
  have hP (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] [P.IsMultiplicative] :
      (P.inverseImage (BigFppfOver.toScheme B S hS)).ContainsIdentities ∧
        (P.inverseImage (BigFppfOver.toScheme B S hS)).RespectsIso :=
    ⟨MorphismProperty.ContainsIdentities.inverseImage _,
      MorphismProperty.RespectsIso.inverseImage _ _⟩
  have := (hP (@Surjective.{u})).1
  have := (hP (@Surjective.{u})).2
  have := (hP (@Etale.{u})).1
  have := (hP (@Etale.{u})).2
  have := hT
  exact ⟨T, e.inv, inferInstance, MorphismProperty.presheaf_of_isIso _ e.inv,
    isEtale_of_presheaf_etale B S hS (MorphismProperty.presheaf_of_isIso _ e.inv)⟩

/-- A finite morphism of algebraic spaces is affine: the representing object its definition
provides over an affine test object is affine, and its finiteness is not needed. -/
theorem IsFinite.isAffineHom {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : IsFinite B S hS f) : IsAffineHom B S hS f := by
  intro Z g
  obtain ⟨V, p, i, hV, -, hpb⟩ := hf ((BigAffineFppf.inclusion B S hS).obj Z) Z.property g
  exact ⟨⟨V, hV⟩, i, p, hpb⟩

/-- The source of an affine morphism of algebraic spaces with affine target is affine: the
target is represented by an affine object of the site, and the base change of the morphism
along the isomorphism with that representable presheaf is the source. -/
theorem IsAffineHom.isAffineSpace_source {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : IsAffineHom B S hS f) (hY : IsAffineSpace B S hS Y) : IsAffineSpace B S hS X := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hY
  obtain ⟨W, p, q, hpb⟩ := hf ⟨T, hT⟩ e.inv
  have : IsIso p := hpb.isIso_fst_of_isIso
  exact ⟨(BigAffineFppf.inclusion B S hS).obj W, W.property, ⟨(asIso p).symm⟩⟩

/-- The source of a finite morphism of algebraic spaces with affine target is affine. This
is the converse direction of Stacks 07VS, which asserts the affineness of the *target* of a
finite surjective morphism with affine source. -/
theorem IsFinite.isAffineSpace_source {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hf : IsFinite B S hS f) (hY : IsAffineSpace B S hS Y) : IsAffineSpace B S hS X :=
  hf.isAffineHom.isAffineSpace_source hY

end AlgebraicGeometry.Space

end
