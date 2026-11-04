module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphismComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeVariants
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFromRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautOfRepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExampleUnconditional

/-!
# Stacks 0ANT without a restriction on the scheme-valued points

Let `S` be a scheme and let `φ : A → C` be a continuous homomorphism of weakly admissible
topological rings over `S`. **Stacks 0ANT** says that `Spf (φ) : Spf C → Spf A` is of finite
type exactly when `φ` is taut and `C` is topologically of finite type over `A`. This file
proves both implications with their conclusions unrestricted — the quasi-compact
scheme-valued points of `Spf A` are a step in the source's argument, not a restriction on what
it concludes.

## Main results

* `isLocallyOfFiniteTypeAndQuasiCompact_formalSpectrumMap_of_finiteTypeModuloEveryWeakIdeal`:
  **Stacks 0ANT**, the implication (2) ⟹ (1), with no side condition: `Spf (φ)` is of finite
  type in the sense of Definition 0AM4, part (2), the base change being taken along an
  arbitrary scheme-valued point of `Spf A`.
* `isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap'`:
  **Stacks 0ANT**, the implication (1) ⟹ (2), with both halves of condition (2) deduced.
* `isFiniteType_formalSpectrumMap_iff_isTaut_and_isTopologicallyOfFiniteType`:
  the equivalence of Stacks 0ANT, with both conditions read verbatim and no countability
  assumption.

## Which reading of "of finite type" each implication carries

Condition (1) of Stacks 0ANT is "of finite type", Definition 0AM4, part (2): locally of
finite type together with quasi-compact in the sense of Definition 0AJC, which is
`AlgebraicGeometry.FormalSpace.IsFiniteType`. Both implications are stated with that reading,
and so is the equivalence.

What the argument for (2) ⟹ (1) produces is condition (2) of Stacks 0AJJ,
`AlgebraicGeometry.FormalSpace.IsBootstrapFiniteType` — the base change over a quasi-compact
point is quasi-compact as an algebraic space, which is the Bootstrap notion and not
Definition 0AJC — and Stacks 0AJJ itself,
`AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`, carries it to
Definition 0AM4, part (2); that equivalence is unconditional. The implication (1) ⟹ (2) uses
only the locally-of-finite-type half of condition (1).

## Implementation notes

### The implication (2) ⟹ (1)

The source's argument runs over the quasi-compact points of `Spf A`: such a point factors
through a thickening stage `Spec (A ⧸ I) ⟶ Spf A` by Stacks 0AIA, and the base change along
the factorization is `T ×_{Spec (A ⧸ I)} Spec (C ⧸ J(I))`, whose projection is a base change
of the finite type morphism `Spec (C ⧸ J(I)) ⟶ Spec (A ⧸ I)`. That is
`AlgebraicGeometry.FormalSpace.compactPullbackRepresentable_formalSpectrumMap`.

The step from there to an arbitrary scheme-valued point is the locality on the target of
representability and of the two halves of being of finite type, which is
`StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFromAffinePoints`: an arbitrary point
is covered, surjectively and étale, by the coproduct of its affine opens, over which the base
change is the coproduct of the base changes over those affine opens. The same three criteria
carry Stacks 0ANM in
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionFiniteTypeExample`.

The hypothesis of the standalone implication is condition (a) of Stacks 0ANU,
`TopologicalRing.FiniteTypeModuloEveryWeakIdeal` — tautness together with finite type of
`A ⧸ I → C ⧸ J(I)` for every weak ideal of definition `I` — which is what the source's proof
of (2) ⟹ (1) establishes in its first sentence and then uses.

Condition (a) and condition (2) verbatim imply one another with no countability assumption,
so the equivalence below is stated at condition (2) itself. Condition (2) implies condition
(a) by `TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType`, and
condition (a) implies condition (2) for a weakly pre-admissible source by
`TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal`. Nothing in
this file assumes the neighbourhood filters of zero countably generated.

`TopologicalRing.finiteType_tfae` (Stacks 0ANU) does assume it, of the source's filter alone,
and spends it on the two conditions of Stacks 0ANU that play no part here: condition (b), the
cofinal form of condition (a), and condition (d), the presentation as a quotient of a
restricted power series ring by a closed ideal — each reached by a private step of that proof
which consumes it. Condition (c) of Stacks 0ANU is condition (2) of Stacks 0ANT itself, which
is why no countability enters here. Stacks 0ANV,
`AlgebraicGeometry.FormalSpace.formalSpectrumMap_finiteType_tfae`, assumes it of `A` alone,
as its own source does, and does not go through `TopologicalRing.finiteType_tfae` at all:
membership of `C` in `WAdm^count` is asserted by its conditions rather than assumed, and
follows from tautness by Stacks 0GX6,
`RingHom.isCountablyGenerated_nhds_zero_of_isTaut`.

### The implication (1) ⟹ (2)

Being locally of finite type contains representability by algebraic spaces, which is condition
(1) of Stacks 0AN5, and tautness is its condition (3). The arrow between them is
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap`,
and it carries no side condition: the library's Stacks 0AKN consumes of each of the two formal
spectra only its presentation as a directed colimit of affine objects of the site along
thickenings, and for a formal spectrum that presentation is its construction
(`AlgebraicGeometry.FormalSpace.hasThickeningPresentation_formalSpectrum`). With tautness in
hand the ring-theoretic half is finite type of the stage quotient maps,
`AlgebraicGeometry.FormalSpace.finiteType_quotientMap_of_isFiniteType_formalSpectrumMap`,
carried to the density condition of condition (2) by
`TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal`.

Nothing in this file is assumed beyond the source's hypotheses. In particular no bound on the
size of the site is needed. The set-theoretic condition of Stacks 0AIS, the other half of
being an affine formal algebraic space, is such a bound — it asks the site to contain the
coproduct of all the quotient spectra — and no step here consumes it.

## References

* [Stacks Project, Tag 0ANT](https://stacks.math.columbia.edu/tag/0ANT)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AJK](https://stacks.math.columbia.edu/tag/0AJK)
* [Stacks Project, Tag 0AJJ](https://stacks.math.columbia.edu/tag/0AJJ)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AM2](https://stacks.math.columbia.edu/tag/0AM2)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANM](https://stacks.math.columbia.edu/tag/0ANM)
* [Stacks Project, Tag 0ANU](https://stacks.math.columbia.edu/tag/0ANU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-! ### The implication (2) ⟹ (1) -/

/-- **Stacks 0ANT, the implication (2) ⟹ (1).** Let `φ : A ⟶ C` be a continuous homomorphism
of weakly admissible topological rings over `S` which is taut and of finite type modulo every
weak ideal of definition. Then `Spf (φ) : Spf C ⟶ Spf A` is of finite type in the sense of
Definition 0AM4, part (2): locally of finite type — representable by algebraic spaces, with
its base change along *every* scheme-valued point of `Spf A` a morphism of algebraic spaces
which is locally of finite type — and quasi-compact in the sense of Definition 0AJC.

What the argument produces is condition (2) of Stacks 0AJJ: representability by algebraic
spaces together with every base change along a scheme-valued point of `Spf A` being a
morphism of algebraic spaces of finite type. Stacks 0AJJ,
`AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`, carries that to
Definition 0AM4, part (2), and is unconditional.

Over a point whose source is quasi-compact the Bootstrap condition is the source's own
computation, `AlgebraicGeometry.FormalSpace.compactPullbackRepresentable_formalSpectrumMap`;
the passage to an arbitrary point is the locality of the three conditions on the target. -/
@[stacks 0ANT "the implication (2) ⟹ (1) with its conclusion unrestricted: the base change \
of the formal spectrum map is taken along an arbitrary scheme-valued point of `Spf A`, not \
only along one factoring through a thickening stage. Condition (1) is concluded as \
Definition 0AM4, part (2), verbatim; what the argument produces is condition (2) of \
Stacks 0AJJ — representable by algebraic spaces plus of finite type in the Bootstrap sense \
of Stacks 03XZ — and Stacks 0AJJ, \
`AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`, carries it to \
Definition 0AM4, part (2), unconditionally. \
Condition (2) is taken in the form of \
condition (a) of Stacks 0ANU, `TopologicalRing.FiniteTypeModuloEveryWeakIdeal`, which is what \
the source's proof of this implication derives from condition (2) in its first sentence; that \
derivation is \
`TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType` and assumes no \
countability, so this implication is the source's with its hypothesis weakened. Condition (a) \
implies condition (2) back, with no countability assumption either, by \
`TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal`; condition (2) \
verbatim is the hypothesis of this implication as it appears in \
`AlgebraicGeometry.FormalSpace.isFiniteType_formalSpectrumMap_iff_isTaut_and_isTopologicallyOfFiniteType`"]
theorem isLocallyOfFiniteTypeAndQuasiCompact_formalSpectrumMap_of_finiteTypeModuloEveryWeakIdeal
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (h : TopologicalRing.FiniteTypeModuloEveryWeakIdeal f.toRingHom) :
    IsFiniteType' B S hS (formalSpectrumMap hA f) := by
  refine (isFiniteType_iff_isBootstrapFiniteType B S hS (formalSpectrumMap hA f)).mpr ?_
  have hcpr := compactPullbackRepresentable_formalSpectrumMap hA hC D E f h
  refine ⟨isRepresentableByAlgebraicSpacesULift_of_affine_pullback B S hS
    (formalSpectrumMap hA f) hcpr, ?_⟩
  intro U ξ
  change Space.IsFiniteTypeULift.{u + 1} B S hS
    (pullback.fst ξ (formalSpectrumMap hA f).hom)
  refine ⟨isLocallyOfFiniteTypeULift_pullback_of_compact_pullback B S hS
    (formalSpectrumMap hA f) hcpr U ξ, ?_⟩
  intro Z hZ hZqc γ
  exact Space.isQuasiCompactSpaceULift_of_iso B S hS
    (pullbackRightPullbackFstIso ξ (formalSpectrumMap hA f).hom γ).symm
    (isQuasiCompactULift_of_compact_pullback B S hS (formalSpectrumMap hA f) hcpr Z hZ hZqc
      (γ ≫ ξ))

/-- **Stacks 0ANT, the implication (2) ⟹ (1)**, read for the local condition: a continuous
homomorphism of weakly admissible topological rings over `S` which is taut and of finite type
modulo every weak ideal of definition has formal spectrum map locally of finite type, with the
base change taken along an arbitrary scheme-valued point of `Spf A`. -/
@[stacks 0ANT "the implication (2) ⟹ (1) for the local condition of Stacks 0AM4 part (1), \
with the base change taken along an arbitrary scheme-valued point of `Spf A`; condition (2) is \
taken in the form of condition (a) of Stacks 0ANU, as on \
`AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeAndQuasiCompact_formalSpectrumMap_of_finiteTypeModuloEveryWeakIdeal`"]
theorem isLocallyOfFiniteType_formalSpectrumMap_of_finiteTypeModuloEveryWeakIdeal
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (h : TopologicalRing.FiniteTypeModuloEveryWeakIdeal f.toRingHom) :
    IsLocallyOfFiniteType B S hS (formalSpectrumMap hA f) :=
  (isLocallyOfFiniteTypeAndQuasiCompact_formalSpectrumMap_of_finiteTypeModuloEveryWeakIdeal
    hA hC D E f h).1

/-! ### The implication (1) ⟹ (2) -/

/-- **Stacks 0ANT, the implication (1) ⟹ (2).** Let `φ : A ⟶ C` be a continuous homomorphism
of weakly admissible topological rings over `S`. If `Spf (φ)` is of finite type — Definition
0AM4, part (2), verbatim — then `φ` is taut and `C` is topologically of finite type over `A`.

Tautness is the implication (1) ⟹ (3) of Stacks 0AN5 applied to the representability that
being locally of finite type contains, and that implication carries no side condition. Only
the locally-of-finite-type half of condition (1) is used, here and in the ring-theoretic half
`AlgebraicGeometry.FormalSpace.finiteType_quotientMap_of_isFiniteType_formalSpectrumMap`, so
no comparison with condition (2) of Stacks 0AJJ is needed. -/
@[stacks 0ANT "the implication (1) ⟹ (2) in full, with condition (1) read as Definition 0AM4, \
part (2), verbatim: both halves of condition (2) are deduced \
from condition (1). Tautness is the implication (1) ⟹ (3) of Stacks 0AN5, \
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap`, \
applied to the representability by algebraic spaces that being locally of finite type \
contains. No hypothesis beyond the source's: that implication of Stacks 0AN5 carries no side \
condition, because the library's Stacks 0AKN consumes of a formal spectrum only its \
presentation by affine thickenings, which is its construction"]
theorem isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap'
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E)
    (hFT : IsFiniteType' B S hS (formalSpectrumMap hA f)) :
    RingHom.IsTaut f.toRingHom ∧
      TopologicalRing.IsTopologicallyOfFiniteType f.toRingHom := by
  have htaut : RingHom.IsTaut f.toRingHom :=
    isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap B S hS hA hC D E f hFT.1.1
  exact ⟨htaut, TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal'
    f.toRingHom hA.1
    ⟨htaut, fun I hI ↦ finiteType_quotientMap_of_isFiniteType_formalSpectrumMap'
      hA hC D E f htaut hFT I hI⟩⟩

add_to_stacks 0AJK "part (4), both of its conclusions, for a finite type `f : Y → X` with `Y` \
McQuillan: the homomorphism `f` comes from is taut, and its target is topologically of finite \
type over its source -- `φ : A → B` in the source's letters, `φ : A ⟶ C` here, the formal \
spectrum of a weakly admissible topological ring being McQuillan by construction. With the \
second goes part (4)'s restatement that `f` factors as `Y → A^r_X → X` with the first arrow a \
closed immersion: the conclusion `TopologicalRing.IsTopologicallyOfFiniteType` produces the \
integer `r` together with a homomorphism `A[x_1, ..., x_r] → C` restricting to `φ` on \
constants and having dense image, which is that factorization and the dense image of its \
first arrow. Neither conclusion is carried as a hypothesis: tautness is deduced from finite \
type, by the implication (1) ⟹ (3) of Stacks 0AN5. Part (4) closes by observing that \
questions (1) and (2) are then in force for `Y → A^r_X`; those are questions and are \
asserted nowhere."
  isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap'

/-- **Stacks 0ANT, the equivalence**, with both conditions read verbatim. Let `φ : A ⟶ C` be a
continuous homomorphism of weakly admissible topological rings over `S`. Then `Spf (φ)` is of
finite type — Definition 0AM4, part (2) — exactly when `φ` is taut and topologically of finite
type.

The forward implication is
`isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap'` and uses only the
locally-of-finite-type half of condition (1). The backward implication
passes through condition (a) of Stacks 0ANU by
`TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType` and then
produces condition (2) of Stacks 0AJJ, reaching Definition 0AM4, part (2), through
Stacks 0AJJ, `AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`, which is
unconditional.

Condition (2) and condition (a) of Stacks 0ANU are interchangeable here with no countability
assumption, in both directions: condition (a) implies condition (2) by
`TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal`, for which
weak pre-admissibility of the source suffices, and condition (2) implies condition (a) by
`TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType`. Condition (2)
*is* condition (c) of Stacks 0ANU, so this identification is the half of that lemma which
needs no countability; what the countable generation in the hypothesis of Stacks 0ANU —
a morphism of `WAdm^count` — is spent on in `TopologicalRing.finiteType_tfae` are its
conditions (b), the cofinal form of condition (a), and (d), the restricted power series
presentation, and neither appears here. Both of those uses are of the source's filter, so
`TopologicalRing.finiteType_tfae` assumes countable generation of that filter only.

Nothing beyond the source's hypotheses is assumed. The forward implication needs the
implication (1) ⟹ (3) of Stacks 0AN5, which carries no side condition because the library's
Stacks 0AKN consumes of a formal spectrum only its presentation by affine thickenings,
`AlgebraicGeometry.FormalSpace.hasThickeningPresentation_formalSpectrum`. -/
@[stacks 0ANT "the equivalence, with condition (1) read as Definition 0AM4, part (2), \
verbatim and condition (2) read verbatim as tautness together with being topologically of \
finite type. The forward \
implication is \
`AlgebraicGeometry.FormalSpace.isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap'` \
and uses only the locally-of-finite-type half of condition (1); the backward implication \
goes through condition (a) of Stacks 0ANU by \
`TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType` and then \
produces condition (2) of Stacks 0AJJ — representable by algebraic spaces plus of finite \
type in the Bootstrap sense of Stacks 03XZ — and reaches Definition 0AM4, part (2), through \
Stacks 0AJJ, `AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`, which \
is unconditional. No countability assumption is made: condition (2) and condition (a) of \
Stacks 0ANU imply one another outright, by \
`TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal` and \
`TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType`. \
No hypothesis beyond the source's: the implication (1) ⟹ (3) of Stacks 0AN5 that the forward \
direction needs carries no side condition, the library's Stacks 0AKN consuming of a formal \
spectrum only its presentation by affine thickenings"]
theorem isFiniteType_formalSpectrumMap_iff_isTaut_and_isTopologicallyOfFiniteType
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (f : ContinuousHom D E) :
    IsFiniteType' B S hS (formalSpectrumMap hA f) ↔
      RingHom.IsTaut f.toRingHom ∧
        TopologicalRing.IsTopologicallyOfFiniteType f.toRingHom :=
  ⟨isTaut_and_isTopologicallyOfFiniteType_of_isFiniteType_formalSpectrumMap' hA hC D E f,
    fun h ↦ isLocallyOfFiniteTypeAndQuasiCompact_formalSpectrumMap_of_finiteTypeModuloEveryWeakIdeal
      hA hC D E f
      (TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType'
        f.toRingHom f.continuous h.1 h.2)⟩

end AlgebraicGeometry.FormalSpace

end
