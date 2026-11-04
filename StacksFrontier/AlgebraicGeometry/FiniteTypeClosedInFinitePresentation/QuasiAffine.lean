module

public import StacksFrontier.AlgebraicGeometry.AffineSpaceImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteTypeClosedInFinitePresentation.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite type in finite presentation, for a quasi-affine source

A quasi-affine scheme locally of finite type over a base admits an immersion over that base into a
scheme of finite presentation over it, and, when the base is quasi-separated, a closed immersion
into one.

The ambient scheme is relative affine space. A quasi-affine scheme locally of finite type over `S`
immerses into `𝔸ⁿ_S` over `S` for some finite `n`, and `𝔸ⁿ_S ⟶ S` is affine and locally of finite
presentation, hence of finite presentation. The closed immersion is then obtained by replacing the
immersion by a closed immersion into a quasi-compact open of its target.

## Main results

* `AlgebraicGeometry.exists_finitePresentation_isImmersion_of_isQuasiAffine`: the immersion into a
  scheme of finite presentation over the base.
* `AlgebraicGeometry.exists_finitePresentation_isClosedImmersion_of_isQuasiAffine`: the closed
  immersion into one, over a quasi-separated base.

## Implementation notes

Tag 01ZE asserts the first conclusion for every `X` that is quasi-compact and quasi-separated, and
Tag 01ZG asserts the second for the same class of sources; being quasi-affine is strictly stronger
than being quasi-compact and quasi-separated, so what is proved here is a special case of each.
The general case does not reduce to this one, because the conclusion is not local on `X` — a
quasi-compact quasi-separated scheme admits no immersion into any relative affine space in
general — and the general argument presents `X` as a limit of schemes of finite type over the
integers instead, which is absolute Noetherian approximation, Tag 01ZA.

`AlgebraicGeometry.FinitePresentation` is the bundled notion from
`StacksFrontier/AlgebraicGeometry/Morphisms/FinitePresentationPoint.lean`, the conjunction of
`AlgebraicGeometry.LocallyOfFinitePresentation` with quasi-compactness and quasi-separatedness of
the morphism; the last two hold for `𝔸ⁿ_S ⟶ S` because that morphism is affine.

The two tags recorded here by `add_to_stacks` are inputs of Tag 01ZE whose content is declared
elsewhere. Tag 01T2, the
characterisation of local finiteness of type by the ring maps on affine opens, is the statement of
Mathlib's `AlgebraicGeometry.locallyOfFiniteType_iff`, which is the `mk_iff` lemma of the class
`AlgebraicGeometry.LocallyOfFiniteType` and so holds by definition; it is what
`AlgebraicGeometry.exists_immersion_affineSpace` consumes. Tag 01TS, the stability of finite
presentation under base change, holds for the local notion by Mathlib's
`AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange` and for the bundled notion
by `AlgebraicGeometry.FinitePresentation.of_isPullback` of
`StacksFrontier/AlgebraicGeometry/LimitDescentGlueing/Glueing.lean`, which carries no attribute of
its own, its proof using only Mathlib's base-change stability of the three components of the
bundled notion.

## References

* [Stacks Project, Tag 01ZE](https://stacks.math.columbia.edu/tag/01ZE)
* [Stacks Project, Tag 01ZG](https://stacks.math.columbia.edu/tag/01ZG)
* [Stacks Project, Tag 04II](https://stacks.math.columbia.edu/tag/04II)
* [Stacks Project, Tag 01T2](https://stacks.math.columbia.edu/tag/01T2)
* [Stacks Project, Tag 01TS](https://stacks.math.columbia.edu/tag/01TS)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

add_to_stacks 01T2 "(1) implies (2) and conversely"
  AlgebraicGeometry.locallyOfFiniteType_iff
add_to_sga "3 VIB 1.3" "locally of finite type" AlgebraicGeometry.locallyOfFiniteType_iff

add_to_stacks 01TS "locally of finite presentation"
  AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange
add_to_sga "3 VIB 5.6.1.0" "partial"
  AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange
add_to_ega "IV 1.4.3" AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange
add_to_ega "IV 2.7.1" "(iv)" AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange
add_to_ega "IV 20.6.9" "partial"
  AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange
add_to_ega "IV 21.15.9" "partial"
  AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange
add_to_ega "IV 8.6.2" "partial"
  AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange

/-- **Relative affine space is of finite presentation over its base.** It is affine over the base,
hence quasi-compact and quasi-separated, and locally of finite presentation when the index type is
finite. -/
theorem finitePresentation_affineSpace_over (n : Type u) [Finite n] (S : Scheme.{u}) :
    FinitePresentation (𝔸(n; S) ↘ S) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- A quasi-affine scheme locally of finite type over a base admits an immersion over that base
into a scheme of finite presentation over it.

This is the conclusion of Tag 01ZE for a quasi-affine source; the ambient scheme is a relative
affine space, and the immersion is the one of Tag 04II. -/
theorem exists_finitePresentation_isImmersion_of_isQuasiAffine {X S : Scheme.{u}} (f : X ⟶ S)
    [X.IsQuasiAffine] [LocallyOfFiniteType f] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ S) (i : X ⟶ Y),
      FinitePresentation g ∧ IsImmersion i ∧ i ≫ g = f := by
  obtain ⟨n, i, hi, hover⟩ := exists_immersion_affineSpace f
  exact ⟨𝔸(ULift.{u} (Fin n); S), 𝔸(ULift.{u} (Fin n); S) ↘ S, i,
    finitePresentation_affineSpace_over _ S, hi, hover⟩

/-- A quasi-affine scheme locally of finite type over a quasi-separated base admits a closed
immersion over that base into a scheme of finite presentation over it.

This is the conclusion of Tag 01ZG for a quasi-affine source. It is the immersion above fed to the
passage from an immersion to a closed immersion, which is
`AlgebraicGeometry.exists_finitePresentation_isClosedImmersion_of_exists_immersion`. -/
theorem exists_finitePresentation_isClosedImmersion_of_isQuasiAffine {X S : Scheme.{u}}
    (f : X ⟶ S) [X.IsQuasiAffine] [QuasiSeparatedSpace S] [LocallyOfFiniteType f] :
    ∃ (X' : Scheme.{u}) (p : X' ⟶ S) (ι : X ⟶ X'),
      FinitePresentation p ∧ IsClosedImmersion ι ∧ ι ≫ p = f :=
  exists_finitePresentation_isClosedImmersion_of_exists_immersion f
    (exists_finitePresentation_isImmersion_of_isQuasiAffine f)

end AlgebraicGeometry

end
