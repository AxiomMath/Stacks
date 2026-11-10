module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSourceFormalSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFiniteTypeVariants
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TypeTransferVariants

/-!
# Variants of `StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterization`

The declarations below extend the results of
`StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeCharacterization`. A primed name `X'` is a
variant of the declaration `X` there.

## Main declarations

* `formalSpectrumMap_finiteType_tfae_countablyWeaklyAdmissible`
* `isLocallyOfFiniteType_tfae'`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

/-- **Stacks 0ANV.** Let `φ : A ⟶ C` be a continuous homomorphism of weakly admissible
topological rings over `S` and assume the neighbourhood filter of zero of `A` — the target
`Spf A` — countably generated. Then `Spf (φ) : Spf C → Spf A` being locally of finite type,
`Spf (φ)` being of finite type in the sense of Definition 0AM4, part (2), `φ` being a
morphism of `WAdm^{count}` of finite type modulo every weak ideal of definition, and `φ`
being a morphism of `WAdm^{count}` which is taut and topologically of finite type are all
equivalent.

Only the target is assumed countably indexed, as in the source. That the source `Spf C` is
countably indexed is part of what condition (3) asserts — membership of `φ` in
`WAdm^{count}` — and so is a conclusion of conditions (1) and (2), not a hypothesis; the
target's own membership is the standing hypothesis `hAcount` together with `hA`. The step
that produces it is Stacks 0GX6,
`RingHom.isCountablyGenerated_nhds_zero_of_isTaut`: a taut continuous homomorphism carries a
countable fundamental system of open ideals from source ring to target ring, and every one of
the four conditions supplies tautness. This replaces the appeal to Stacks 0AKN and Stacks
0AKP that the source makes, and like them it needs no affineness of the two formal spectra.

The last two conditions are conditions (a) and (c) of Stacks 0ANU, each conjoined with
membership in `WAdm^{count}`. They are identified here without any countability assumption,
by `TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal` — for
which weak pre-admissibility of `A` suffices — and
`TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType`, so Stacks
0ANU's own countability hypotheses are not needed. With `hAcount` and the `WAdm^{count}`
conjunct in hand, Stacks 0ANU identifies these two with its remaining conditions (b) and (d)
as well, which is why reading condition (3) off either form is faithful.

The implication from locally of finite type to condition (a) splits into tautness, which is
the implication (1) ⟹ (3) of Stacks 0AN5, and finite type of the stage quotient maps, which
is the ring-theoretic half of Stacks 0ANT; the implication from condition (a) back is the
implication (2) ⟹ (1) of Stacks 0ANT, and being locally of finite type is the first half of
the conjunction that being of finite type is.

The quasi-compactness of Definition 0AJC that the second condition contains is not
established directly anywhere in the cycle: the implication (2) ⟹ (1) of Stacks 0ANT
produces condition (2) of Stacks 0AJJ,
`AlgebraicGeometry.FormalSpace.IsBootstrapFiniteType`, whose quasi-compactness assertion is
the Bootstrap one, and Stacks 0AJJ identifies that condition with Definition 0AM4, part (2),
unconditionally; see
`AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`.

Nothing beyond the source's hypotheses is assumed. The tautness step is the implication
(1) ⟹ (3) of Stacks 0AN5,
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap`,
which carries no side condition of its own. -/
@[stacks 0ANV "the equivalence, under the source's hypotheses exactly: only the target \
`Spf A` is assumed countably indexed, by `hAcount`. Condition (3) is taken in the two forms \
(a) and (c) of Stacks 0ANU, each conjoined with membership of the source ring in \
`WAdm^count`, which is what `f corresponds to a morphism of WAdm^count` still asserts once \
the target ring's membership is the standing hypothesis. That membership is a conclusion of \
conditions (1) and (2) rather than an assumption: every one of the four conditions supplies \
tautness, and a taut continuous homomorphism carries a countable fundamental system of open \
ideals from source ring to target ring by Stacks 0GX6, \
`RingHom.isCountablyGenerated_nhds_zero_of_isTaut` — which replaces the source's appeal to \
Stacks 0AKN and Stacks 0AKP and, like the library's Stacks 0AKN, needs no affineness of the \
two formal spectra. The finite type condition is Definition 0AM4, part (2), verbatim; the \
implication (2) ⟹ (1) of Stacks 0ANT concludes it through condition (2) of Stacks 0AJJ — \
representable by algebraic spaces plus of finite type in the Bootstrap sense of \
Stacks 03XZ — which Stacks 0AJJ, \
`AlgebraicGeometry.FormalSpace.isFiniteType_iff_isBootstrapFiniteType`, identifies with \
Definition 0AM4, part (2), unconditionally. The two forms of condition (3) are identified \
with no countability assumption, by \
`TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal` and \
`TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType`, so Stacks \
0ANU's own countability hypotheses are not needed here; the implication (1) ⟹ (3) of \
Stacks 0AN5 that supplies tautness, \
`AlgebraicGeometry.FormalSpace.isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap`, \
carries no side condition either"]
theorem formalSpectrumMap_finiteType_tfae_countablyWeaklyAdmissible {A C : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [CommRing C]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (hAcount : (nhds (0 : A)).IsCountablyGenerated)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (g : ContinuousHom D E) :
    List.TFAE
      [IsLocallyOfFiniteType B S hS (formalSpectrumMap hA g),
        IsFiniteType' B S hS (formalSpectrumMap hA g),
        TopologicalRing.IsCountablyWeaklyAdmissible C ∧
          TopologicalRing.FiniteTypeModuloEveryWeakIdeal g.toRingHom,
        TopologicalRing.IsCountablyWeaklyAdmissible C ∧
          RingHom.IsTaut g.toRingHom ∧
            TopologicalRing.IsTopologicallyOfFiniteType g.toRingHom] := by
  have hWAdm : RingHom.IsTaut g.toRingHom →
      TopologicalRing.IsCountablyWeaklyAdmissible C := fun htaut ↦
    ⟨hC, RingHom.isCountablyGenerated_nhds_zero_of_isTaut g.toRingHom htaut hAcount⟩
  tfae_have 1 → 3 := fun h ↦ by
    have htaut : RingHom.IsTaut g.toRingHom :=
      isTaut_of_isRepresentableByAlgebraicSpaces_formalSpectrumMap B S hS hA hC D E g h.1
    exact ⟨hWAdm htaut, htaut, fun J hJ ↦
      finiteType_quotientMap_of_isLocallyOfFiniteType_formalSpectrumMap hA hC D E g htaut h J hJ⟩
  tfae_have 3 → 2 := fun h ↦
    isLocallyOfFiniteTypeAndQuasiCompact_formalSpectrumMap_of_finiteTypeModuloEveryWeakIdeal
      hA hC D E g h.2
  tfae_have 2 → 1 := fun h ↦ h.1
  tfae_have 3 → 4 := fun h ↦
    ⟨h.1, h.2.1, TopologicalRing.isTopologicallyOfFiniteType_of_finiteTypeModuloEveryWeakIdeal'
      g.toRingHom hA.1 h.2⟩
  tfae_have 4 → 3 := fun h ↦
    ⟨h.1, TopologicalRing.finiteTypeModuloEveryWeakIdeal_of_topologicallyOfFiniteType'
      g.toRingHom h.2.1 h.2.2⟩
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
