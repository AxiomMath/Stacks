module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism

/-!
# Quasi-separated morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` with relative diagonal `Δ : X ⟶ X ×_Y X`. **Stacks 0ARN,
part (2)** declares `f` *quasi-separated* when `Δ` is a quasi-compact morphism of formal
algebraic spaces, quasi-compactness being Stacks 0AJC.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasQuasiCompactDiagonal`: **Stacks 0ARN, part (2)**, the
  relative diagonal is quasi-compact in the sense of
  `AlgebraicGeometry.FormalSpace.IsQuasiCompact`.

## Main results

* `AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_iff`: the condition spelled out, so
  that a consumer never has to unfold the definition by hand: every fibre product of the
  relative diagonal with an affine scheme over `S` in the site mapping to the relative
  self-product is a quasi-compact formal algebraic space over `S`.
* `AlgebraicGeometry.FormalSpace.HasQuasiCompactDiagonal.of_isPullback`: **Stacks 0ARP** for
  the quasi-separatedness axiom, a base change of a quasi-separated morphism is
  quasi-separated.
* `AlgebraicGeometry.FormalSpace.isQuasiCompact_mapDesc`: **Stacks 0ARQ, part (3)**, the
  comparison `X ×_Z Y ⟶ X ×_T Y` of two fibre products is a quasi-compact morphism of formal
  algebraic spaces as soon as `Z ⟶ T` is quasi-separated.

## Implementation notes

The relative diagonal is the categorical diagonal
`CategoryTheory.Limits.pullback.diagonal` of the category of fppf sheaves, which has fibre
products, exactly as in
`StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism`; and quasi-compactness of it is
`AlgebraicGeometry.FormalSpace.IsQuasiCompact`, the condition of Stacks 0AJC recorded in
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism` in the form of condition (3)
of Stacks 0AJB. So both halves of the source's definition are the notions this library
attaches to those names, and nothing about the definition is weakened: the diagonal is the
diagonal of `f`, and quasi-compactness is quasi-compactness of a morphism of formal algebraic
spaces, not of the underlying morphism of algebraic spaces.

As for the separatedness axiom, neither the witnesses that the source and the target are
formal algebraic spaces nor any representability of the diagonal is used, so the condition is
stated for an arbitrary morphism of fppf sheaves on the big fppf site of `S`, as
`AlgebraicGeometry.FormalSpace.IsQuasiCompact` itself is. It is an `abbrev`, so the
quantified fibre product condition is available to downstream arguments directly;
`AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_iff` is that unfolding stated for
reference and holds by `Iff.rfl`.

This is not, as it is written, the condition
`AlgebraicGeometry.FormalSpace.IsQuasiSeparatedMorphism` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism`, which asks instead that the
morphism of presheaves underlying the diagonal be quasi-compact in the sense of
`AlgebraicGeometry.Space.IsQuasiCompactULift`, a condition on base changes along
quasi-compact *algebraic spaces* with quasi-compactness of the fibre product read in the
sense of algebraic spaces. That one is a priori the stronger. The two are nevertheless the
same condition as soon as the relative diagonal is representable by algebraic spaces
over `S`, which by **Stacks 0AN2** and **Stacks 0AIP** it is whenever the source is a formal
algebraic space — so under the hypotheses of Stacks 0ARN itself the two never differ. That
comparison is
`AlgebraicGeometry.FormalSpace.hasQuasiCompactDiagonal_iff_isQuasiSeparatedMorphism` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiSeparatedMorphismComparison`, which is also
where **Stacks 0ARS** is proved for the quasi-separatedness axiom. It is not proved here
because this file sits below both of its inputs in the import order: the equivalence of
conditions (2) and (3) of **Stacks 0AJB**,
`AlgebraicGeometry.FormalSpace.isQuasiCompact_iff_isQuasiCompactOnSchemeBaseChanges` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismDecomposition`, and the
agreement of the two notions of a quasi-compact space on an algebraic space,
`AlgebraicGeometry.FormalSpace.quasiCompactSpaceAgreesOnAlgebraicSpaces` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria`.

Stability under base change is the categorical fact that the relative diagonal of a base
change is itself a base change of the relative diagonal, Mathlib's
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.diagonal`, applied to
quasi-compactness of morphisms of fppf sheaves read as a
`CategoryTheory.MorphismProperty`; that it is stable under base change is
`AlgebraicGeometry.FormalSpace.IsQuasiCompact.of_isPullback`. The square is taken in the form
`CategoryTheory.IsPullback`, so no chosen fibre product is imposed on the caller.

## References

* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AJB](https://stacks.math.columbia.edu/tag/0AJB)
* [Stacks Project, Tag 0AJC](https://stacks.math.columbia.edu/tag/0AJC)
* [Stacks Project, Tag 0AN2](https://stacks.math.columbia.edu/tag/0AN2)
* [Stacks Project, Tag 0ARN](https://stacks.math.columbia.edu/tag/0ARN)
* [Stacks Project, Tag 0ARP](https://stacks.math.columbia.edu/tag/0ARP)
* [Stacks Project, Tag 0ARS](https://stacks.math.columbia.edu/tag/0ARS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0ARN, part (2).** A morphism of formal algebraic spaces over `S` is
*quasi-separated* when its relative diagonal `X ⟶ X ×_Y X` is a quasi-compact morphism of
formal algebraic spaces, quasi-compactness being `AlgebraicGeometry.FormalSpace.IsQuasiCompact`,
the condition of Stacks 0AJC. The condition makes sense, and is stated, for an arbitrary
morphism of fppf sheaves on the big fppf site of `S`. -/
@[stacks 0ARN "part (2): quasi-separated, the relative diagonal quasi-compact in the sense of \
Stacks 0AJC"]
abbrev HasQuasiCompactDiagonal {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  IsQuasiCompact B S hS (pullback.diagonal f)

/-- Quasi-separatedness of a morphism of fppf sheaves on the big fppf site of `S` spelled
out: every fibre product of the relative diagonal with an affine scheme over `S` in the site
mapping to the relative self-product is a quasi-compact formal algebraic space over `S`. -/
theorem hasQuasiCompactDiagonal_iff {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    HasQuasiCompactDiagonal B S hS f ↔
      ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
        ∀ (g : yonedaSheaf B S hS T ⟶ pullback f f) (W : FppfSheaf B S hS)
          (p : W ⟶ yonedaSheaf B S hS T) (q : W ⟶ X),
          IsPullback p q g (pullback.diagonal f) → IsQuasiCompactSpace B S hS W :=
  Iff.rfl

/-- **Stacks 0ARP** for the quasi-separatedness axiom of Stacks 0ARN: a base change of a
quasi-separated morphism of formal algebraic spaces over `S` is quasi-separated. In a
cartesian square of fppf sheaves on the big fppf site of `S` whose right-hand column `f` is
quasi-separated, the left-hand column `snd` is quasi-separated, since the relative diagonal of
`snd` is a base change of the relative diagonal of `f` and quasi-compact morphisms are stable
under base change. As with the definition itself, no hypothesis that the four sheaves are
formal algebraic spaces is needed. -/
@[stacks 0ARP "quasi-separated"]
theorem HasQuasiCompactDiagonal.of_isPullback {X Y Y' W : FppfSheaf B S hS}
    {fst : W ⟶ X} {snd : W ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback fst snd f g)
    (hf : HasQuasiCompactDiagonal B S hS f) : HasQuasiCompactDiagonal B S hS snd := by
  let Q : MorphismProperty (FppfSheaf B S hS) := fun _ _ h ↦ IsQuasiCompact B S hS h
  have hQ : Q.IsStableUnderBaseChange :=
    ⟨fun sq' hg ↦ IsQuasiCompact.of_isPullback B S hS sq'.flip hg⟩
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := Q.diagonal) sq hf

/-- **Stacks 0ARQ, part (3).** For morphisms `f : X ⟶ Z`, `g : Y ⟶ Z` and `h : Z ⟶ T` of
formal algebraic spaces over `S` with `h` quasi-separated, the comparison
`X ×_Z Y ⟶ X ×_T Y` of the two fibre products is a quasi-compact morphism of formal algebraic
spaces.

The whole content is one cartesian square, the *magic diagram* of Mathlib's
`CategoryTheory.Limits.pullback_map_diagonal_isPullback`: the comparison is a base change of
the relative diagonal of `h`, along the morphism `X ×_T Y ⟶ Z ×_T Z` induced by `f` and `g`.
Quasi-separatedness of `h` says that relative diagonal is quasi-compact, and quasi-compactness
is stable under base change by
`AlgebraicGeometry.FormalSpace.IsQuasiCompact.of_isPullback`. No hypothesis on `f`, `g` or the
four sheaves is needed, so the statement is made for arbitrary fppf sheaves, as both conditions
occurring in it are. -/
@[stacks 0ARQ "part (3), for Z ⟶ T quasi-separated. Both notions are the source's own: the \
hypothesis is quasi-separatedness as Stacks 0ARN, part (2) declares it, the relative diagonal \
quasi-compact in the sense of Stacks 0AJC (HasQuasiCompactDiagonal of this file), and the \
conclusion is quasi-compactness of a morphism of formal algebraic spaces in that same sense of \
Stacks 0AJC (IsQuasiCompact of QuasiCompactMorphism.lean). Nothing is carried and nothing is \
assumed beyond the tag's own hypothesis on Z ⟶ T; in particular this is independent of \
Stacks 0AN2 and of Stacks 0AIP, which parts (1) and (2) of the tag need. Parts (1) and (2) are \
registered in SeparatedMorphism.lean"]
theorem isQuasiCompact_mapDesc {X Y Z T : FppfSheaf B S hS} (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : Z ⟶ T) (hh : HasQuasiCompactDiagonal B S hS h) :
    IsQuasiCompact B S hS (pullback.mapDesc f g h) :=
  IsQuasiCompact.of_isPullback B S hS (pullback_map_diagonal_isPullback f g h).flip hh

end AlgebraicGeometry.FormalSpace

end
