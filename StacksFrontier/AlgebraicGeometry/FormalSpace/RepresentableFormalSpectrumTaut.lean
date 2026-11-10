module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineOfRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ThickeningClassification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.WeakIdealPresentation
public import StacksFrontier.Topology.Algebra.AdicTopology.Completion
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut

/-!
# Tautness of a homomorphism whose formal spectrum is representable

Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings over a
scheme `S` and suppose `Spf φ : Spf C ⟶ Spf A` is representable by algebraic spaces, which is
condition (1) of Stacks 0AN5. This file proves that `φ` is taut, condition (3) of Stacks 0AN5,
under two set-theoretic conditions on the site.

## Main results

* `FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`: the
  implication itself.

Its two halves,
`AlgebraicGeometry.FormalSpace.isWeakIdealOfDefinition_closure_map_of_isPullback` — the heart
of the implication — and
`AlgebraicGeometry.FormalSpace.exists_isWeakIdealOfDefinition_map_le`, live in
`StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange`, beside the stage lemmas about
ideal comparison that their proofs use.

## Implementation notes

*The shape of tautness.* `RingHom.IsTaut φ` asks that the closure of the extension of every
open ideal be open and that those closed extended ideals form a neighbourhood basis of zero.
Through `RingHom.isTaut_iff_hasBasis_isWeakIdealOfDefinition` this is the conjunction of two
statements about weak ideals of definition, and only one of them has geometric content:

* the closure of `φ(I)C` is a weak ideal of definition of `C`, for `I` a weak ideal of
  definition of `A`, and
* the family of those closures is cofinal among the weak ideals of definition of `C`.

The second is soft and is proved here without any hypothesis on `Spf φ`: a stage
`Spec (C ⧸ L)` of `Spf C` is an affine scheme, so the morphism `Spec (C ⧸ L) ⟶ Spf A` it
induces factors through a stage `Spec (A ⧸ I)` of `Spf A` by Stacks 0AIA, and the resulting
commuting square forces `φ(I)C ⊆ L`. So the whole content of
the implication is the *openness* of the closure of `φ(I)C`.

*Where representability enters.* The stage inclusion `Spec (A ⧸ I) ⟶ Spf A` is a representable
thickening by Stacks 0AIC, so its base change along `Spf φ` is a representable thickening into
`Spf C`. Representability of `Spf φ` makes the source of that base change an affine scheme of
the site — this is the affine-test-scheme case of Stacks 0AKN,
`AlgebraicGeometry.FormalSpace.exists_isAffineHom_isPullback_of_isRepresentable` — and a
representable thickening from an object of the site into `Spf C` is cut out by a unique weak
ideal of definition `J` of `C`, again by Stacks 0AIC
(`AlgebraicGeometry.FormalSpace.existsUnique_weakIdeal_quotient`). Identifying `J` with the
closure of `φ(I)C` is then an inclusion in each direction:

* `φ(I)C ⊆ J` is read off the commuting square, and `J` is open hence closed, so the closure is
  contained in `J`.
* conversely, for every weak ideal of definition `L` of `C` containing `φ(I)C` the stage
  `Spec (C ⧸ L)` maps to the fibre product by the universal property, hence `J ⊆ L`. Taking
  `L = φ(I)C + L₀` with
  `L₀` an arbitrary weak ideal of definition of `C` — such a sum is again one, its elements
  being topologically nilpotent — gives `J ⊆ φ(I)C + L₀` for all `L₀`, which is membership in
  the closure by Stacks 0AMS,
  `TopologicalRing.mem_closure_iff_forall_sup_isOpen`.

The source instead identifies the fibre product with `Spf (C ⊗̂_A A ⧸ I)` by Stacks 0AN3 and
then uses Stacks 0AMZ; the argument above avoids the completed tensor product entirely.

*What is assumed.* Two hypotheses beyond those of the source appear: the set-theoretic
conditions `D.HasLargeSite` and `E.HasLargeSite`, which make the two formal spectra affine
formal algebraic spaces by Stacks 0AIF. They are carried in exactly the place and for exactly
the reason that the converse implication
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut`
carries `hE`, which is the second of them; the source states Stacks 0AN5 over an arbitrary
scheme `S` and with no condition on the site, so the tag attached here names the implication and
the two conditions. No separatedness hypothesis on `Spf A` is needed: the affine-test-scheme
case of Stacks 0AKN holds with none, by
`AlgebraicGeometry.FormalSpace.relative_isAffineHom_of_isAffine_source`.

Because the conditions on the site remain, this does *not* discharge
`AlgebraicGeometry.FormalSpace.IsTautOfRepresentableFormalSpectrumMap`, the hypothesis form of
the implication carried in
`StacksFrontier.AlgebraicGeometry.FormalSpace.SharpnessOfRepresentability`, which quantifies over
all quotient systems with no side condition.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AMS](https://stacks.math.columbia.edu/tag/0AMS)
* [Stacks Project, Tag 0AMX](https://stacks.math.columbia.edu/tag/0AMX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- **The implication (1) ⟹ (3) of Stacks 0AN5**, for formal spectra which are affine formal
algebraic spaces. Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological
rings over `S` whose formal spectra are affine formal algebraic spaces over `S` and whose formal
spectrum map `Spf φ : Spf C ⟶ Spf A` is representable by algebraic spaces over `S`. Then the
underlying ring map of `φ` is taut.

The affineness of the two formal spectra is the only thing the argument uses of the site; the
set-theoretic conditions `D.HasLargeSite` and `E.HasLargeSite` of
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`
are one way of supplying it (Stacks 0AIF), and an identification of the formal spectra with
given affine formal algebraic spaces is another. -/
theorem isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C)
    (hDaff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
    (hEaff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum E))
    (f : ContinuousHom D E)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hA f).hom) :
    RingHom.IsTaut f.toRingHom := by
  classical
  have hwid : ∀ I : Ideal A, TopologicalRing.IsWeakIdealOfDefinition I →
      TopologicalRing.IsWeakIdealOfDefinition (Ideal.closure (I.map f.toRingHom)) := by
    intro I hI
    have hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (D.stage ⟨I, hI⟩))) := by
      change IsAffine ((BigAffineFppf.toScheme B S hS).obj (D.stage ⟨I, hI⟩))
      exact (D.stage ⟨I, hI⟩).property
    obtain ⟨W, q, p, -, -, hpb⟩ := exists_isAffineHom_isPullback_of_isRepresentable'
      B S hS (formalSpectrumMap hA f) hEaff hDaff hrep
      ((BigAffineFppf.inclusion B S hS).obj (D.stage ⟨I, hI⟩)) hTaff
      (formalSpectrumInclusion D ⟨I, hI⟩)
    exact isWeakIdealOfDefinition_closure_map_of_isPullback B S hS hA hC D E f ⟨I, hI⟩ W q p hpb
  rw [RingHom.isTaut_iff_hasBasis_isWeakIdealOfDefinition f.toRingHom f.continuous hA]
  refine ⟨hwid, (TopologicalRing.hasBasis_nhds_zero_isWeakIdealOfDefinition hC).to_hasBasis
    ?_ ?_⟩
  · intro L hL
    obtain ⟨I, hIL⟩ := exists_isWeakIdealOfDefinition_map_le B S hS hA D E f ⟨L, hL⟩
    exact ⟨(I : Ideal A), I.2,
      closure_minimal hIL (L.toAddSubgroup.isClosed_of_isOpen hL.1)⟩
  · intro I hI
    exact ⟨Ideal.closure (I.map f.toRingHom), hwid I hI, subset_rfl⟩

/-- **The implication (1) ⟹ (3) of Stacks 0AN5**, with the hypotheses this library needs. Let
`φ : A ⟶ C` be a continuous homomorphism of weakly admissible topological rings over `S` whose
formal spectrum `Spf φ : Spf C ⟶ Spf A` is representable by algebraic spaces over `S`. Then the
underlying ring map of `φ` is taut.

Two hypotheses beyond those of the source are carried, the set-theoretic conditions
`D.HasLargeSite` and `E.HasLargeSite` on the site; they are named in the tag. See the
implementation notes of this file. -/
@[stacks 0AN5 "(1) implies (3), under the set-theoretic conditions \
`AlgebraicGeometry.FormalSpace.QuotientSystem.HasLargeSite` on both quotient systems, which are \
what make the two formal spectra affine formal algebraic spaces by Stacks 0AIF; the converse \
implication (3) implies (1) carries the second of them"]
theorem isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C)
    (hD : D.HasLargeSite) (hE : E.HasLargeSite)
    (f : ContinuousHom D E)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (formalSpectrumMap hA f).hom) :
    RingHom.IsTaut f.toRingHom :=
  isTaut_of_isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isAffine B S hS hA hC
    D E (isAffineFormalAlgebraicSpace_formalSpectrum hA D hD)
    (isAffineFormalAlgebraicSpace_formalSpectrum hC E hE) f hrep

end AlgebraicGeometry.FormalSpace

end
