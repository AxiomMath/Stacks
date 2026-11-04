module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniJacobianDivisor
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.AvoidingLines

/-!
# Hypothesis (3) of [Stacks, Tag 0FD6] makes `X` quasi-compact

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]). That situation
assumes of `X` only that it is a scheme over `k`, and [Stacks, Tag 0FD6] adds to it that `X` is
smooth over `k`, that the image of `ψ` generates `L`, and that `φ_{L,ψ} : X → 𝐏(V)` is an
immersion. Smoothness gives `X` locally of finite presentation, hence locally of finite type, but
**not** quasi-compact; so quasi-compactness of `X` over `k` is not among the three hypotheses, and
the chain proving the tag had been carrying it as an extra binder, needed for the generic
flatness of `q : H_univ → 𝔸^r_k` and for the Noetherianness of `H_univ`.

It is not an extra hypothesis: **the immersion hypothesis already implies it.** The linear system
`V` is finite dimensional, so `𝐏(V)` is proper over `Spec k`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.isProper_projectiveSpaceOfModuleToSpec`), hence both
quasi-compact over it and locally of finite type over it; a scheme locally of finite type over a
field is locally Noetherian, and a quasi-compact locally Noetherian scheme is Noetherian, so
`𝐏(V)` has a Noetherian underlying space. An immersion is in particular an embedding of
underlying spaces, and a space inducing its topology from a Noetherian one is Noetherian, so `X`
has a Noetherian space. Every open of a Noetherian space is compact, so every morphism out of `X`
is quasi-compact (`AlgebraicGeometry.quasiCompact_of_noetherianSpace_source`).

## Main results

* `Stacks.Bertini.FamilyDivisors.noetherianSpace_of_isImmersive`: hypothesis (3) makes the
  underlying space of `X` Noetherian.
* `Stacks.Bertini.FamilyDivisors.quasiCompact_of_isImmersive`: hypothesis (3) makes `X`
  quasi-compact over `k`.
* `Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates_pointwise_`
  `of_basis'`: [Stacks, Tag 0FD6] with quasi-compactness of `X` no longer assumed, leaving
  `[IsAlgClosed D.k]` as the only hypothesis of the statement that the source does not make.

## Implementation notes

The conclusion is drawn as `TopologicalSpace.NoetherianSpace D.X` rather than as
`AlgebraicGeometry.QuasiCompact D.toBase` directly, because that is the form the consumers want:
`AlgebraicGeometry.quasiCompact_of_noetherianSpace_source` is an instance, so a `NoetherianSpace`
hypothesis in scope discharges every quasi-compactness binder in the chain, including the ones on
intermediate morphisms, and `AlgebraicGeometry.IsNoetherian` for `H_univ` follows as well.

`Nontrivial D.V` is not part of the standing situation; it is read off the basis the hypothesis
is taken at, whose index type `Fin (m + 1)` is nonempty. This is the only use made of that basis
here — the statement would hold for any basis of `V`, `𝐏(V)` being independent of it.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 01OZ](https://stacks.math.columbia.edu/tag/01OZ)
* [Stacks Project, Tag 01P0](https://stacks.math.columbia.edu/tag/01P0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, u})

/-- A basis of the linear system indexed by `Fin (m + 1)` exhibits a nonzero vector, so `V` is
nontrivial. -/
theorem nontrivial_of_basis {m : ℕ} (b : Module.Basis (Fin (m + 1)) D.k D.V) :
    Nontrivial D.V :=
  nontrivial_of_ne _ _ (b.ne_zero 0)

/-- **The projective space of the linear system has a Noetherian underlying space.** It is proper
over `Spec k`, so locally of finite type over a field and quasi-compact; the first makes it
locally Noetherian and the two together make it Noetherian. -/
theorem noetherianSpace_projectiveSpaceOfModule {m : ℕ}
    (b : Module.Basis (Fin (m + 1)) D.k D.V) :
    NoetherianSpace (projectiveSpaceOfModule D.k D.V) := by
  have : Nontrivial D.V := D.nontrivial_of_basis b
  have : IsLocallyNoetherian (projectiveSpaceOfModule D.k D.V) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveSpaceOfModuleToSpec D.k D.V)
  have : CompactSpace (projectiveSpaceOfModule D.k D.V) :=
    QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOfModuleToSpec D.k D.V)
  have : IsNoetherian (projectiveSpaceOfModule D.k D.V) := {}
  infer_instance

/-- **Hypothesis (3) of [Stacks, Tag 0FD6] makes the underlying space of `X` Noetherian.** The
morphism `φ_{L,ψ} : X → 𝐏(V)` is an immersion, hence an embedding of underlying spaces, and
`𝐏(V)` has a Noetherian space. -/
theorem noetherianSpace_of_isImmersive {m : ℕ} {b : Module.Basis (Fin (m + 1)) D.k D.V}
    {hb : D.GeneratesBy b} (himm : D.IsImmersive b hb) : NoetherianSpace D.X :=
  have : IsImmersion (D.toProjectiveSpace b hb) := himm
  have := D.noetherianSpace_projectiveSpaceOfModule b
  (Scheme.Hom.isEmbedding (D.toProjectiveSpace b hb)).isInducing.noetherianSpace

/-- **Hypothesis (3) of [Stacks, Tag 0FD6] makes `X` quasi-compact over `k`.** It is not an
addition to the standing situation of [Stacks, Tag 0G47], which assumes of `X` only that it is a
scheme over `k`: `X` has a Noetherian space by
`Stacks.Bertini.FamilyDivisors.noetherianSpace_of_isImmersive`, and every morphism out of a
scheme with a Noetherian space is quasi-compact. -/
theorem quasiCompact_of_isImmersive {m : ℕ} {b : Module.Basis (Fin (m + 1)) D.k D.V}
    {hb : D.GeneratesBy b} (himm : D.IsImmersive b hb) : QuasiCompact D.toBase :=
  have := D.noetherianSpace_of_isImmersive himm
  inferInstance

/-- **[Stacks, Tag 0FD6].** In the standing situation of [Stacks, Tag 0G47] with `X` smooth over
an algebraically closed field `k`, if the image of `ψ` generates `L` and the morphism
`φ_{L,ψ} : X → 𝐏(V)` it determines is an immersion, then the divisor `H_v` is smooth over `k'`
for general `v ∈ V ⊗_k k'`.

This is
`Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_of_generates_pointwise_of_`
`basis` with `[QuasiCompact D.toBase]` removed. That binder was not a hypothesis of the source:
[Stacks, Tag 0G47] assumes of `X` only that it is a scheme over `k`, and [Stacks, Tag 0FD6] adds
only smoothness, generation and the immersion — and smoothness gives `X` locally of finite
presentation, hence locally of finite type, but not quasi-compact. It is discharged rather than
dropped, from the immersion hypothesis itself: see
`Stacks.Bertini.FamilyDivisors.quasiCompact_of_isImmersive`.

`[IsAlgClosed D.k]` is then the only hypothesis of this statement that the source does not make.
It is the case the source reduces to by [Stacks, Tag 02FY]; that reduction is a development of
its own rather than a loose end. Its first half is done: the base change of the whole standing
situation along `k → k̄` is `Stacks.Bertini.FamilyDivisors.baseChangeAlgebraicClosure`, all three
hypotheses transfer to it — the third by
`Stacks.Bertini.FamilyDivisors.isImmersive_baseChangeFamily` — and
`Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_baseChangeAlgebraicClosure`
draws the conclusion of this statement over `k̄` from the source's three hypotheses over `k`.
What is still owed is the descent of that conclusion: a nonempty open of `𝔸^r_k` whose points
lift into the nonempty open of `𝔸^r_{k̄}` the conclusion over `k̄` provides, and the
identification of `H_v` on `X_{k'}` with its own base change along an extension of `k'`.
Hypothesis (3) is also still spelled at a basis of `V` rather than on the intrinsic
morphism `φ_{L,ψ}` — but that is now only a spelling, the two agreeing by
`Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis`, so hypothesis (3) does not depend on
which basis it is read at. What is not yet proved is its agreement with the source's canonical
`φ_{L,ψ}` as characterised by an isomorphism `θ : φ^*𝒪(1) ≅ ℒ` through which `ψ` factors — the
same input [Stacks, Tag 01ND] is registered without. -/
@[stacks 0FD6 "the conclusion from hypotheses (2) and (3) with no proof obligation and no \
dimension data assumed, with (3) at an arbitrary basis of the linear system, and with \
quasi-compactness of X no longer assumed -- it is derived from hypothesis (3), P(V) having a \
Noetherian space. ONE hypothesis here is not the source's: that k is algebraically closed, the \
case Tag 02FY reduces to. (3) is also still spelled at a basis rather than on the intrinsic \
morphism phi_(L, psi), but that is now only a spelling: they agree by \
Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis, so the hypothesis is independent of the \
basis it is read at; what is still unproved is its agreement with the source's canonical \
phi_(L, psi) as characterised by theta : phi^*O(1) = L, the same input Tag 01ND is registered \
without"]
theorem forGeneral_smooth_specializedDivisor_of_generates_pointwise_of_basis' [IsAlgClosed D.k]
    [Smooth D.toBase] (hgen : D.Generates) {m : ℕ}
    (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (himm : D.IsImmersive b (D.generatesBy_basis hgen b)) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) :=
  have := D.noetherianSpace_of_isImmersive himm
  D.forGeneral_smooth_specializedDivisor_of_generates_pointwise_of_basis hgen b himm

end Stacks.Bertini.FamilyDivisors

end
