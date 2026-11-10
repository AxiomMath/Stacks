module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedLocallyClosed
import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.ReducedInducedIrreducible

/-!
# The reduced induced scheme on a locally closed subset

A locally closed subset `T` of a scheme `X` carries a canonical reduced induced scheme
structure together with a canonical immersion into `X`. This file records the basic
recognition principle for that pair: if *some* affine scheme maps to `X` by an affine
immersion with image exactly `T`, then the reduced induced scheme on `T` is affine and its
canonical inclusion is an affine morphism.

## Main results

* `AlgebraicGeometry.range_reducedInducedInclusion`: the canonical inclusion of the reduced
  induced scheme on `T` has image `T`.
* `AlgebraicGeometry.exists_lift_reducedInduced`: a morphism from a reduced scheme whose image
  lies in `T` factors through the reduced induced scheme on `T`.
* `AlgebraicGeometry.isAffine_reducedInduced_of_range_eq`: the recognition principle above.
* `AlgebraicGeometry.isAffine_reducedInduced_of_isClosed` and
  `AlgebraicGeometry.isAffine_reducedInduced_of_isAffineOpen`: the two basic instances of it,
  for a closed subset of an affine scheme and for an affine open with affine inclusion.

## Implementation notes

The recognition principle is first proved for a *reduced* affine source, where the lift
supplied by `exists_lift_reducedInduced` is a closed immersion and surjective, hence an
isomorphism. The general case follows by replacing the source by its reduction, which is the
closed subscheme cut out by the vanishing ideal sheaf of the whole space.

## References

* [Stacks Project, Tag 0F2L](https://stacks.math.columbia.edu/tag/0F2L)
* [Stacks Project, Tag 0F2S](https://stacks.math.columbia.edu/tag/0F2S)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u

namespace AlgebraicGeometry

/-- The canonical inclusion of the reduced induced scheme on a locally closed subset `T` has
image exactly `T`.

See [Stacks, Tag 0F2L]. -/
alias range_reducedInducedInclusion :=
  Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed.range_inclusion

/-- If `g ≫ h = f`, then `h (g y) = f y` on points. -/
private theorem apply_eq_of_comp_eq {X Y Z : Scheme.{u}} {g : X ⟶ Y} {h : Y ⟶ Z} {f : X ⟶ Z}
    (hg : g ≫ h = f) (y : X) : h (g y) = f y := by
  rw [← hg]
  rfl

/-- The subscheme of an affine scheme cut out by the vanishing ideal of a closed subset is
affine. -/
private theorem isAffine_subscheme_vanishingIdeal {X : Scheme.{u}} [IsAffine X] (C : Closeds X) :
    IsAffine (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
  isAffine_of_isAffineHom (Scheme.IdealSheafData.vanishingIdeal C).subschemeι

/-- A morphism from a reduced scheme whose image lies in a locally closed subset `T` factors
through the reduced induced scheme on `T`.

See [Stacks, Tag 0F2L]. -/
theorem exists_lift_reducedInduced {X Y : Scheme.{u}} (T : Set X)
    (hT : IsLocallyClosed T) [IsReduced Y] (f : Y ⟶ X)
    (hf : Set.range f ⊆ T) :
    ∃ g : Y ⟶ reducedInducedScheme T hT, g ≫ reducedInducedInclusion T hT = f := by
  let O := reducedInducedOpen T hT
  let C := reducedInducedClosed T hT
  let J := Scheme.IdealSheafData.vanishingIdeal C
  have hsub : Set.range f ⊆ Set.range O.ι := by
    rintro x ⟨y, rfl⟩
    exact ⟨⟨f y, subset_coborder (hf ⟨y, rfl⟩)⟩, rfl⟩
  let fO : Y ⟶ O.toScheme := IsOpenImmersion.lift O.ι f hsub
  have hfac : fO ≫ O.ι = f := IsOpenImmersion.lift_fac _ _ _
  have hsupport : Set.range fO ⊆ (J.support : Set O.toScheme) := by
    change Set.range fO ⊆ Set.preimage Subtype.val T
    rintro x ⟨y, rfl⟩
    change O.ι (fO y) ∈ T
    rw [apply_eq_of_comp_eq hfac]
    exact hf ⟨y, rfl⟩
  obtain ⟨g, hg⟩ :=
    (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support J fO).2 hsupport
  refine ⟨g, ?_⟩
  change g ≫ J.subschemeι ≫ O.ι = f
  rw [← Category.assoc, hg, hfac]

private lemma isAffine_reducedInduced_of_range_eq_of_isReduced {X Y : Scheme.{u}}
    (T : Set X) (hT : IsLocallyClosed T) [IsAffine Y] [IsReduced Y]
    (f : Y ⟶ X) [IsImmersion f] [IsAffineHom f] (hrange : Set.range f = T) :
    IsAffine (reducedInducedScheme T hT) ∧ IsAffineHom (reducedInducedInclusion T hT) := by
  let incl := reducedInducedInclusion T hT
  have : IsImmersion incl := by
    dsimp [incl, reducedInducedInclusion]
    infer_instance
  have : IsReduced (reducedInducedScheme T hT) := by
    change IsReduced (Scheme.IdealSheafData.vanishingIdeal (reducedInducedClosed T hT)).subscheme
    infer_instance
  obtain ⟨g, hg⟩ := exists_lift_reducedInduced T hT f hrange.le
  have hgPre : IsPreimmersion g := by
    have : IsPreimmersion (g ≫ incl) := by
      rw [hg]
      infer_instance
    exact IsPreimmersion.of_comp g incl
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨y, hy⟩ := hrange.ge ((range_reducedInducedInclusion T hT).le ⟨z, rfl⟩)
    refine ⟨y, incl.isEmbedding.injective ?_⟩
    exact (apply_eq_of_comp_eq hg y).trans hy
  have : IsClosedImmersion g :=
    IsClosedImmersion.of_isPreimmersion g (Set.range_eq_univ.mpr hgsurj ▸ isClosed_univ)
  have : Surjective g := ⟨hgsurj⟩
  have : IsIso g := isIso_of_isClosedImmersion_of_surjective g
  let e : Y ≅ reducedInducedScheme T hT := asIso g
  have hcomp : e.inv ≫ f = incl := by
    rw [← hg]
    simp [e, incl]
  refine ⟨IsAffine.of_isIso e.inv, ?_⟩
  change IsAffineHom incl
  rw [← hcomp]
  infer_instance

/-- **Recognition of the reduced induced scheme on a locally closed subset.** If an affine
scheme maps to `X` by an affine immersion whose image is the locally closed subset `T`, then
the reduced induced scheme on `T` is affine and its canonical inclusion into `X` is affine.

See [Stacks, Tag 0F2S]. -/
theorem isAffine_reducedInduced_of_range_eq {X Y : Scheme.{u}}
    (T : Set X) (hT : IsLocallyClosed T) [IsAffine Y]
    (f : Y ⟶ X) [IsImmersion f] [IsAffineHom f] (hrange : Set.range f = T) :
    IsAffine (reducedInducedScheme T hT) ∧ IsAffineHom (reducedInducedInclusion T hT) := by
  let J := Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y)
  have := isAffine_subscheme_vanishingIdeal (⊤ : Closeds Y)
  have hJrange : Set.range (J.subschemeι ≫ f) = T := by
    change Set.range (f.base ∘ J.subschemeι.base) = T
    rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    simpa using hrange
  exact isAffine_reducedInduced_of_range_eq_of_isReduced T hT (J.subschemeι ≫ f) hJrange

/-- The reduced induced scheme on a closed subset of an affine scheme is affine, and its
canonical inclusion is an affine morphism.

See [Stacks, Tag 0F2S]. -/
theorem isAffine_reducedInduced_of_isClosed {X : Scheme.{u}} [IsAffine X] (C : Closeds X) :
    IsAffine (reducedInducedScheme (C : Set X) C.2.isLocallyClosed) ∧
      IsAffineHom (reducedInducedInclusion (C : Set X) C.2.isLocallyClosed) := by
  let J := Scheme.IdealSheafData.vanishingIdeal C
  have := isAffine_subscheme_vanishingIdeal C
  exact isAffine_reducedInduced_of_range_eq (C : Set X) C.2.isLocallyClosed J.subschemeι
    (Scheme.IdealSheafData.range_subschemeι_vanishingIdeal C)

/-- The reduced induced scheme on an affine open whose inclusion is an affine morphism is
affine, and its canonical inclusion is an affine morphism.

See [Stacks, Tag 0F2S]. -/
theorem isAffine_reducedInduced_of_isAffineOpen {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) [IsAffineHom U.ι] :
    IsAffine (reducedInducedScheme (U : Set X) U.isOpen.isLocallyClosed) ∧
      IsAffineHom (reducedInducedInclusion (U : Set X) U.isOpen.isLocallyClosed) := by
  have : IsAffine U.toScheme := hU
  exact isAffine_reducedInduced_of_range_eq _ _ U.ι (by simp)

end AlgebraicGeometry

end
