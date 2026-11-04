module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionExtra
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpDualizing
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurveSections
import StacksCore.Tactic.StacksAttribute

/-!
# The twisted inverse image across the square `g ≫ j = i ≫ f`

In Situation [Stacks, Tag 0B4W] with `X` the blowup of `Spec(A)` in the maximal ideal, let
`i : E ⟶ X` be the exceptional divisor, `f : X ⟶ Spec(A)` the blowup morphism,
`j : Spec(κ) ⟶ Spec(A)` the closed point and `g : E ⟶ Spec(κ)` the structure morphism of `E` over
the centre. These form a commutative square,
`AlgebraicGeometry.BlowUpDualizing.exceptionalDivisorToCentre_comp`, and the source's proof of
clauses (2) and (3) of [Stacks, Tag 0B64] propagates the normalization of [Stacks, Remark 0B4R]
around it:

`i^!(f^!(ω_A)) ≅ (i ≫ f)^!(ω_A) = (g ≫ j)^!(ω_A) ≅ g^!(j^!(ω_A))`.

This file proves that identification of functors. It is two applications of [Stacks, Tag 0ATX] —
`Stacks.Duality.twistedInverseImageCompIso`, the comparison `(f ≫ g)^× ≅ g^× ⋙ f^×` of right
adjoints — glued by the fact that the two composites around the square are the *same morphism*,
hence have the same derived direct image, hence the same right adjoint up to the canonical
isomorphism.

## Main definitions

* `Stacks.Duality.twistedInverseImageSquareIso` — for a commutative square of quasi-compact
  quasi-separated morphisms with quasi-compact targets, `f^× ⋙ i^× ≅ j^× ⋙ g^×`.
* `AlgebraicGeometry.BlowUpDualizing.twistedInverseImageExceptionalSquareIso` — that at the
  blowup square.

## Why both composites give the same adjoint

`Stacks.Duality.twistedInverseImageCompAdjunction` exhibits `f^× ⋙ i^×` as a right adjoint of
`R(i ≫ f)_*` and `j^× ⋙ g^×` as one of `R(g ≫ j)_*`. The square says `g ≫ j = i ≫ f`; the
restricted derived direct image depends on nothing else — its quasi-coherence argument is a
proof of a proposition and the `IsLeftAdjoint` instances likewise — so the two left adjoints are
*equal*, by `Stacks.Duality.quasiCoherentDerivedPushforwardCongr`, which substitutes the morphism.
`CategoryTheory.Adjunction.rightAdjointUniq` then compares the two right adjoints, and the
comparison it produces is canonical rather than chosen.

## Implementation notes

*Where this belongs.* `twistedInverseImageSquareIso` is generic and could sit beside
`Stacks.Duality.twistedInverseImageCompAdjunction` in
`…/AlgebraicGeometry/Duality/TwistedInverseImage/CompositionExtra.lean`; nothing in it depends on
the blowup. The substitution step is `Stacks.Duality.quasiCoherentDerivedPushforwardCongr` from
`…/AlgebraicGeometry/Duality/TwistedInverseImage/Composition.lean`.

*Which model.* Everything is at the locally small model of [Stacks, Tag 079Q], which is the only
model at which [Stacks, Tag 0A9E] produces the right adjoints: the instance is
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward`, whose Brown-representability
input needs `HasCoproducts` at the morphism universe. No `HasDerivedCategory` argument is spelled
below because the locally small instances are global and are the ones wanted.

*No `@[stacks]` attribute is attached.* [Stacks, Tag 0ATX] is registered on
`Stacks.Duality.twistedInverseImageCompIso`, which this applies twice; the gluing across a
commutative square is not a separate assertion of the source.

## References

* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Duality

/-- **[Stacks, Tag 0ATX] across a commutative square.** Let

`E --i--> X`, `E --g--> Z`, `X --f--> B`, `Z --j--> B`

be quasi-compact quasi-separated morphisms of schemes with `X`, `Z` and `B` quasi-compact, and
suppose the square commutes: `g ≫ j = i ≫ f`. Then

`f^× ⋙ i^× ≅ j^× ⋙ g^×`,

which in the source's order of composition is `i^!(f^!(-)) ≅ g^!(j^!(-))`.

Both sides are right adjoints of the derived direct image along the common composite — the
left-hand one by `Stacks.Duality.twistedInverseImageCompAdjunction` at `(i, f)`, the right-hand
one by the same at `(g, j)` read along `Stacks.Duality.quasiCoherentDerivedPushforwardCongr` —
and a right adjoint is unique up to a canonical isomorphism. -/
def twistedInverseImageSquareIso {E X Z B : Scheme.{u}} (i : E ⟶ X) (f : X ⟶ B) (g : E ⟶ Z)
    (j : Z ⟶ B) (hsq : g ≫ j = i ≫ f)
    [QuasiCompact i] [QuasiSeparated i] [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact j] [QuasiSeparated j]
    [CompactSpace X] [CompactSpace Z] [CompactSpace B] :
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward i
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward g
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward j
    twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f) ⋙
        twistedInverseImage i (isQuasicoherent_homology_derivedPushforward_of_qcqs i) ≅
      twistedInverseImage j (isQuasicoherent_homology_derivedPushforward_of_qcqs j) ⋙
        twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g) := by
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward i
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward f
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward g
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward j
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (i ≫ f)
  letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward (g ≫ j)
  exact Adjunction.rightAdjointUniq
    (twistedInverseImageCompAdjunction i f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (i ≫ f)))
    ((twistedInverseImageCompAdjunction g j
        (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ j))).ofNatIsoLeft
      (quasiCoherentDerivedPushforwardCongr hsq
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ j))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (i ≫ f))))

end Stacks.Duality

namespace AlgebraicGeometry.BlowUpDualizing

variable (S : RationalSingularitySituation.{u})

/-- **The blowup square is commutative**, `g ≫ j = i ≫ f`: the structure morphism of the
exceptional divisor over the closed point followed by the closed point is the exceptional
immersion followed by the blowup morphism. This is
`AlgebraicGeometry.exceptionalDivisorToCentre_comp` at the closed point of `Spec(A)`. -/
theorem exceptionalSquare_comm :
    exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A) ≫
        Stacks.Blowup.residuePoint S.A =
      exceptionalImmersion S.A ≫ blowUpToBase (centre S.A) :=
  exceptionalDivisorToCentre_comp (Stacks.Blowup.residuePoint S.A)

/-- `X`, the blowup of `Spec(A)` in the maximal ideal, is quasi-compact: it is proper, hence
quasi-compact, over the quasi-compact `Spec(A)`. -/
theorem compactSpace_blowUpScheme : CompactSpace (blowUpScheme S.A) :=
  QuasiCompact.compactSpace_of_compactSpace (blowUpToBase (centre S.A))

/-- **The twisted inverse image around the blowup square**, `i^!(f^!(-)) ≅ g^!(j^!(-))`.

This is `Stacks.Duality.twistedInverseImageSquareIso` at the square
`AlgebraicGeometry.BlowUpDualizing.exceptionalSquare_comm`. All eleven of its hypotheses are
discharged: `i` is a closed immersion, `f` is the blowup morphism of a modification, `j` is a
morphism of affine schemes and `g` is proper by
`AlgebraicGeometry.isProper_exceptionalDivisorToCentre_residuePoint`, which is the properness
field of Situation [Stacks, Tag 0B5D] at the exceptional curve; `Spec(A)` and `Spec(κ)` are
affine, hence quasi-compact, and the blowup is quasi-compact by
`AlgebraicGeometry.BlowUpDualizing.compactSpace_blowUpScheme`.

It is the geometric half of the source's propagation of the normalization of
[Stacks, Remark 0B4R] from `Spec(A)` to `E`: composed with
`AlgebraicGeometry.RationalSingularitySituation`
`.nonempty_twistedInverseImage_residuePoint_iso_single`, which evaluates `j^!(ω_A[-2])` as
`𝒪_{Spec κ}`, it identifies `i^!(ω_X)` with a shift of `g^!(𝒪_{Spec κ})`, the dualizing complex
of `E` over `κ`. -/
def twistedInverseImageExceptionalSquareIso :
    letI : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
      (cohenMacaulayCurveSituationExceptionalDivisor S).proper
    letI := compactSpace_blowUpScheme S
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (exceptionalImmersion S.A)
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (blowUpToBase (centre S.A))
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
    letI := AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward
      (Stacks.Blowup.residuePoint S.A)
    Stacks.Duality.twistedInverseImage (blowUpToBase (centre S.A))
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
        Stacks.Duality.twistedInverseImage (exceptionalImmersion S.A)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≅
      Stacks.Duality.twistedInverseImage (Stacks.Blowup.residuePoint S.A)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
        Stacks.Duality.twistedInverseImage
          (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _) :=
  letI : IsProper (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A)) :=
    (cohenMacaulayCurveSituationExceptionalDivisor S).proper
  letI := compactSpace_blowUpScheme S
  Stacks.Duality.twistedInverseImageSquareIso (exceptionalImmersion S.A)
    (blowUpToBase (centre S.A))
    (exceptionalDivisorToCentre (Stacks.Blowup.residuePoint S.A))
    (Stacks.Blowup.residuePoint S.A) (exceptionalSquare_comm S)

end AlgebraicGeometry.BlowUpDualizing

end
