module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFieldBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.BaseChange

/-!
# Hypothesis (3) of [Stacks, Tag 0FD6] transfers to a base change of the base field

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]) and let `K/k` be a
field extension. `Stacks.Bertini.FamilyDivisors.baseChangeFamily` is the situation base changed
along `K/k`, and hypotheses (1) and (2) of [Stacks, Tag 0FD6] were already known to transfer to
it (`Stacks.Bertini.FamilyDivisors.smooth_baseChangeFamily`,
`Stacks.Bertini.FamilyDivisors.generates_baseChangeFamily`). This file transfers the third, that
`φ_{L,ψ}` is an immersion, which is what the reduction of [Stacks, Tag 02FY] to an algebraically
closed base field was missing.

The morphism of the base-changed situation is the base change of the morphism. Indeed
`φ_{L_K, ψ_K}` is built from the sections of the base-changed basis, which are the pullbacks of
the sections of the original basis
(`Stacks.Bertini.FamilyDivisors.sectionOf_baseChangeFamily_basis`), and the morphism to
projective space attached to a module with generating sections is stable under base change of the
situation (`Stacks.ProjectiveFromSections.isPullback_toProjectiveSpaceOver`). Since
`X_K = X ×_{Spec k} Spec K` (`Stacks.Bertini.FamilyDivisors.isPullback_baseChange`), the two
morphisms sit in a cartesian square over `ℙⁿ_K ⟶ ℙⁿ_k` and `AlgebraicGeometry.IsImmersion` is
stable under base change.

## Main results

* `Stacks.Bertini.FamilyDivisors.isImmersive_baseChangeFamily`: **hypothesis (3) transfers to the
  base change.** Taken at the base change of a basis of `V`, which is the basis whose sections
  are the pullbacks of the sections of the original basis.
* `Stacks.Bertini.FamilyDivisors.forGeneral_smooth_specializedDivisor_baseChangeAlgebraicClosure`:
  [Stacks, Tag 0FD6] for the situation base changed to an algebraic closure of `k`, from
  hypotheses (1), (2) and (3) **for the original situation** alone. This is the conclusion of the
  tag over `k̄`, with no hypothesis beyond the source's three; it is the whole of the reduction of
  [Stacks, Tag 02FY] except for the descent of the conclusion back to `k`.

## Implementation notes

The basis of `K ⊗_k V` that the hypothesis is transferred to is `Module.Basis.baseChange`, not
`Stacks.Bertini.FamilyDivisors.baseChangeBasis`: the two differ by the reindexing along
`dim_K (K ⊗_k V) = dim_k V`, and the statements of [Stacks, Tag 0FD6] take the immersion
hypothesis at an arbitrary basis indexed by `Fin (m + 1)`, so no reindexing is needed. Both read
`φ` through the sections of `1 ⊗ vᵢ`, which are the pullbacks of the sections of the `vᵢ`.

What is *not* done here is the last step of [Stacks, Tag 02FY]: the conclusion of
[Stacks, Tag 0FD6] over `k̄` is an assertion about a nonempty open of the parameter space
`𝔸^r_{k̄}` and about every extension of `k̄`, and returning it to one about a nonempty open of
`𝔸^r_k` and every extension of `k` is a separate matter — it needs a nonempty open of `𝔸^r_k`
whose points lift into the given open of `𝔸^r_{k̄}`, which is not a consequence of anything in
this file. Smoothness itself descends (`AlgebraicGeometry.smooth_of_smooth_pullback_snd_spec_`
`algebraMap`), so that open is the only thing between the result below and [Stacks, Tag 0FD6]
over an arbitrary field.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, u}) (K : Type u) [Field K] [Algebra D.k K]

/-- The sections of the base change of a basis of the linear system are the pullbacks of the
sections of that basis. -/
theorem sectionOf_baseChangeFamily_comp_baseChange {m : ℕ}
    (b : Module.Basis (Fin (m + 1)) D.k D.V) :
    (fun i => (D.baseChangeFamily K).sectionOf (b.baseChange K i)) =
      fun i => pullbackGlobalSections (D.baseChangeToX K) D.L (D.sectionOf (b i)) := by
  refine funext fun i => ?_
  rw [Module.Basis.baseChange_apply]
  exact D.sectionOf_baseChangeFamily_one_tmul K (b i)

/-- **Hypothesis (3) of [Stacks, Tag 0FD6] transfers to a base change of the base field**: if
`φ_{L,ψ} : X → 𝐏(V)` is an immersion, so is `φ_{L_K, ψ_K} : X_K → 𝐏(K ⊗_k V)`, read at the base
change of the basis.

The second morphism is the base change of the first along `ℙⁿ_K ⟶ ℙⁿ_k`: the sections of the
base-changed basis are the pullbacks of the sections of the basis, and the morphism to projective
space attached to a generating family of sections is stable under base change
(`Stacks.ProjectiveFromSections.isPullback_toProjectiveSpaceOver`). Immersions are stable under
base change. -/
theorem isImmersive_baseChangeFamily {m : ℕ} (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (hb : D.GeneratesBy b) (himm : D.IsImmersive b hb)
    (hb' : (D.baseChangeFamily K).GeneratesBy (b.baseChange K)) :
    (D.baseChangeFamily K).IsImmersive (b.baseChange K) hb' := by
  have : IsImmersion (Stacks.ProjectiveFromSections.toProjectiveSpaceOver
      (fun i => D.sectionOf (b i)) hb D.toBase) :=
    (D.isImmersive_iff_isImmersion_toProjectiveSpaceOver b hb).mp himm
  refine ((D.baseChangeFamily K).isImmersive_iff_isImmersion_toProjectiveSpaceOver
    (b.baseChange K) hb').mpr ?_
  suffices h : ∀ (t : Fin (m + 1) → Γ((D.baseChangeFamily K).L, ⊤))
      (ht : Stacks.ProjectiveFromSections.GeneratesStalks t),
      t = (fun i => pullbackGlobalSections (D.baseChangeToX K) D.L (D.sectionOf (b i))) →
      IsImmersion (Stacks.ProjectiveFromSections.toProjectiveSpaceOver t ht
        (D.baseChangeFamily K).toBase) from
    h _ hb' (D.sectionOf_baseChangeFamily_comp_baseChange K b)
  intro t ht hteq
  subst hteq
  exact Stacks.ProjectiveFromSections.isImmersion_toProjectiveSpaceOver_of_isPullback
    (fun i => D.sectionOf (b i)) hb D.toBase (D.isPullback_baseChange K) ht

/-- **[Stacks, Tag 0FD6] for the situation base changed to an algebraic closure of the base
field, from the source's three hypotheses for the original situation.** `X` smooth over `k`, the
image of `ψ` generating `L`, and `φ_{L,ψ}` an immersion: then over `k̄` the divisor `H_v` is
smooth for general `v`.

All three hypotheses transfer to `D.baseChangeAlgebraicClosure`
(`Stacks.Bertini.FamilyDivisors.smooth_baseChangeFamily`,
`Stacks.Bertini.FamilyDivisors.generates_baseChangeFamily` and
`Stacks.Bertini.FamilyDivisors.isImmersive_baseChangeFamily`), and `k̄` is algebraically closed,
so the carrier of the tag applies to the base-changed situation.

The registration is **qualified**: the conclusion drawn is the tag's conclusion for
`D.baseChangeAlgebraicClosure`, not for `D`, and the passage between the two is what
[Stacks, Tag 02FY] still owes — a nonempty open of `𝔸^r_k` whose points lift into the given
nonempty open of `𝔸^r_{k̄}`, together with the identification of `H_v` on `X_{k'}` with its own
base change. -/
@[stacks 0FD6 "the conclusion of the tag for the standing situation base changed to an \
algebraic closure of the base field, with hypotheses (1), (2) and (3) assumed only for the \
original situation over k -- hypothesis (3) transfers by isImmersive_baseChangeFamily. This is \
NOT the tag for an arbitrary base field: the descent of the conclusion from kbar back to k (the \
reduction of Tag 02FY) needs a nonempty open of A^r_k whose points lift into the given nonempty \
open of A^r_kbar, which is not proved. Hypothesis (3) is also still spelled at a basis of the \
linear system rather than on the intrinsic morphism phi_(L, psi)"]
theorem forGeneral_smooth_specializedDivisor_baseChangeAlgebraicClosure [Smooth D.toBase]
    (hgen : D.Generates) {m : ℕ} (b : Module.Basis (Fin (m + 1)) D.k D.V)
    (himm : D.IsImmersive b (D.generatesBy_basis hgen b)) :
    D.baseChangeAlgebraicClosure.ForGeneral (fun K' _ _ w =>
      ∀ a : Fin (Module.finrank D.baseChangeAlgebraicClosure.k
          D.baseChangeAlgebraicClosure.V) → K',
        w = ∑ i, TensorProduct.tmul D.baseChangeAlgebraicClosure.k
            (D.baseChangeAlgebraicClosure.basis i) (a i) →
          Smooth ((D.baseChangeAlgebraicClosure.specializedDivisor K' a).subschemeι ≫
            D.baseChangeAlgebraicClosure.baseChangeToSpec K')) :=
  D.forGeneral_smooth_specializedDivisor_baseChangeFamily (AlgebraicClosure D.k) hgen
    (b.baseChange (AlgebraicClosure D.k))
    (D.isImmersive_baseChangeFamily (AlgebraicClosure D.k) b (D.generatesBy_basis hgen b) himm _)

end Stacks.Bertini.FamilyDivisors

end
