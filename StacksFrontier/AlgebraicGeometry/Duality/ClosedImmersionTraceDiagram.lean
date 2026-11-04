module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTraceSheafHom
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# The trace diagram of a closed immersion, with its quasi-coherence hypothesis discharged

Let `i : Z ⟶ W` be a closed immersion of schemes and let `a` be a right adjoint of
`Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`. The trace map `Ri_* a(K) ⟶ K`, that is the counit of `a`,
agrees with the composite

`Ri_* a(K) ⟶ Ri_* R ℰom(𝒪_Z, K) = R ℰom_{𝒪_W}(i_* 𝒪_Z, K) ⟶ K`

whose first arrow is the comparison map of [Stacks, Tag 0A9X], whose middle identification is
[Stacks, Tag 0A77], and whose last arrow is induced by the unit `𝒪_W ⟶ i_* 𝒪_Z`.

## Main results

* `Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_isClosedImmersion`:
  [Stacks, Tag 08D5] part (1) for a closed immersion, which is quasi-compact and
  quasi-separated, so that `Ri_*` restricts to `D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)` with no hypothesis.
* `Stacks.Duality.closedImmersionQuasiCoherentDerivedPushforward`: that restriction.
* `Stacks.Duality.rightAdjointToDerivedSheafHom_comp_derivedEvaluationAtOne_of_isClosedImmersion`:
  **[Stacks, Tag 0B6M]**, the commutativity of the trace diagram, with no hypothesis beyond the
  closed immersion and the right adjoint.
* `Stacks.Duality.isIso_rightAdjointToDerivedSheafHom_app_of_isLocallyNoetherian`:
  [Stacks, Tag 0A9X] for a closed immersion of locally Noetherian schemes, which is the input
  making the first arrow of the composite the equality sign the source writes.

## Implementation notes

The triangle itself is
`Stacks.Duality.rightAdjointToDerivedSheafHom_comp_derivedEvaluationAtOne`, proved for an
arbitrary right adjoint `a` of a restriction of `Ri_*` cut out by a quasi-coherence hypothesis
`hpush`. What is done here is to discharge `hpush`: a closed immersion of schemes is affine,
hence quasi-compact and quasi-separated, so [Stacks, Tag 08D5] part (1) in the form
`AlgebraicGeometry.isQuasicoherent_derivedPushforward` applies with no further hypothesis.

[Stacks, Tag 0B6M] is stated in the source for a closed immersion of Noetherian schemes and for
`K` in `D⁺_QCoh(𝒪_W)`. Neither hypothesis is needed for the commutativity: the first arrow of
the composite is the comparison map of [Stacks, Tag 0A9X] rather than its inverse, so the
identity holds for every `K` in `D_QCoh(𝒪_W)`. The Noetherian hypothesis and the boundedness
enter only where the source's diagram writes an equality sign on that arrow, that is in
`isIso_rightAdjointToDerivedSheafHom_app_of_isLocallyNoetherian`, which discharges the
pseudo-coherence hypothesis of
`Stacks.Duality.isIso_rightAdjointToDerivedSheafHom_app` by [Stacks, Tag 0684].

## References

* [Stacks Project, Tag 0B6M](https://stacks.math.columbia.edu/tag/0B6M)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0684](https://stacks.math.columbia.edu/tag/0684)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

variable {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i]

/-- **[Stacks, Tag 08D5] part (1) for a closed immersion.** The unbounded derived direct image
along a closed immersion preserves quasi-coherence of the cohomology sheaves: a closed immersion
is affine, hence quasi-compact and quasi-separated, so
`AlgebraicGeometry.isQuasicoherent_derivedPushforward` applies. -/
theorem isQuasicoherent_homology_derivedPushforward_of_isClosedImmersion
    (K : quasiCoherentDerivedCategory Z) (n : ℤ) :
    ((DerivedCategory.homologyFunctor W.Modules n).obj
      ((derivedPushforward i).obj K.obj)).IsQuasicoherent :=
  AlgebraicGeometry.isQuasicoherent_derivedPushforward i K n

/-- **`Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)` for a closed immersion.** That `Ri_*` carries
`D_QCoh(𝒪_Z)` into `D_QCoh(𝒪_W)` is [Stacks, Tag 08D5] part (1), so no hypothesis is left. -/
abbrev closedImmersionQuasiCoherentDerivedPushforward :
    quasiCoherentDerivedCategory Z ⥤ quasiCoherentDerivedCategory W :=
  quasiCoherentDerivedPushforward i
    (isQuasicoherent_homology_derivedPushforward_of_isClosedImmersion i)

/-- **Stacks Project, Tag 0B6M (Example 48.9.8).** Let `i : Z ⟶ W` be a closed immersion and let
`a` be a right adjoint of `Ri_* : D_QCoh(𝒪_Z) ⥤ D_QCoh(𝒪_W)`. Then the trace `Ri_* a(K) ⟶ K` —
the counit of `a` — is the comparison map of [Stacks, Tag 0A9X] pushed forward, followed by the
identification of [Stacks, Tag 0A77], followed by the map
`R ℰom_{𝒪_W}(i_* 𝒪_Z, K) ⟶ K` induced by the unit `𝒪_W ⟶ i_* 𝒪_Z`.

This is the diagram of the source with its quasi-coherence hypothesis discharged by
[Stacks, Tag 08D5] part (1). -/
@[stacks 0B6M "the example, with no hypothesis beyond the closed immersion and the right \
adjoint: that Ri_* carries D_QCoh(O_Z) into D_QCoh(O_W) is Tag 08D5 part (1), and the \
commutativity holds for every K in D_QCoh(O_W), so neither the Noetherian hypothesis of the \
source nor boundedness of K appears"]
theorem rightAdjointToDerivedSheafHom_comp_derivedEvaluationAtOne_of_isClosedImmersion
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : closedImmersionQuasiCoherentDerivedPushforward i ⊣ a)
    (K : quasiCoherentDerivedCategory W) :
    (modulePushforward (closedQuotient i).i).mapDerivedCategory.map
          ((rightAdjointToDerivedSheafHom i
            (isQuasicoherent_homology_derivedPushforward_of_isClosedImmersion i) a adj).app K) ≫
        (closedQuotient i).derivedModulePushforwardDerivedSheafHomExactSupportIso.hom.app K.obj ≫
          (closedQuotient i).derivedEvaluationAtOne.app K.obj =
      (closedImmersionPushforwardModelIso i).hom.app ((a.obj K).obj) ≫
        (adj.counit.app K).hom :=
  rightAdjointToDerivedSheafHom_comp_derivedEvaluationAtOne i
    (isQuasicoherent_homology_derivedPushforward_of_isClosedImmersion i) a adj K

/-- **Stacks Project, Tag 0A9X** for a closed immersion of locally Noetherian schemes: on a
bounded-below complex with quasi-coherent cohomology the comparison map
`a(K) ⟶ R𝓗om_{𝒪_W}(𝒪_Z, K)` is invertible. This is the equality sign the diagram of
[Stacks, Tag 0B6M] writes on the first arrow of its lower composite.

The pseudo-coherence hypothesis of `Stacks.Duality.isIso_rightAdjointToDerivedSheafHom_app` is
discharged by [Stacks, Tag 0684]: over a locally Noetherian target a morphism is pseudo-coherent
as soon as it is locally of finite type, which a closed immersion is. -/
theorem isIso_rightAdjointToDerivedSheafHom_app_of_isLocallyNoetherian [IsLocallyNoetherian W]
    (a : quasiCoherentDerivedCategory W ⥤ quasiCoherentDerivedCategory Z)
    (adj : closedImmersionQuasiCoherentDerivedPushforward i ⊣ a)
    (K : (isBoundedBelowQuasiCoherent W).FullSubcategory) :
    IsIso ((rightAdjointToDerivedSheafHom i
      (isQuasicoherent_homology_derivedPushforward_of_isClosedImmersion i) a adj).app K.obj) :=
  isIso_rightAdjointToDerivedSheafHom_app i
    (isQuasicoherent_homology_derivedPushforward_of_isClosedImmersion i) a adj
    ((AlgebraicGeometry.pseudoCoherent_iff_locallyOfFiniteType i).2 inferInstance) K

end Stacks.Duality

end
