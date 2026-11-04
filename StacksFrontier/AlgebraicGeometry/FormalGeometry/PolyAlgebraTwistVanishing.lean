module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDevissage
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxEpiAssembly
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxPresentation

/-!
# Uniform twisted vanishing for graded modules over a polynomial algebra

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` proper, `L` an ample invertible `𝒪_X`-module and
`𝓟 = 𝒪_X[x_i : i ∈ ι]` the polynomial algebra on a finite set of variables. For every
quasi-coherent graded `𝓟`-module `N` of finite type there is one `d₀` with

  `Hᵖ(X, Nₙ ⊗ L ^⊗ d) = 0` for all `p > 0`, all `d ≥ d₀` and all degrees `n`.

This is part (2) of [Stacks, Tag 0897] for `B = A[x_i]`. The library proves it inside the proof of
`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_epi_over_polyAlgebra`, where it is used only
after restricting scalars from the associated graded algebra of an ideal; here it is stated for an
arbitrary graded `𝓟`-module, which is the form the proof of [Stacks, Tag 089A] needs: there the
graded module is built from the transition kernels of a tower of thickenings, which is not the
associated graded module of any ideal sheaf on a single scheme.

The proof is the dévissage `Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_devissage`
fed by the degreewise epimorphic presentation
`Stacks.Coherent.exists_epi_degreePresentation_polyAlgebra`, whose graded kernel is quasi-coherent
(`Stacks.Coherent.isQuasicoherent_gradedKer_piece`) and of finite type
(`Stacks.Coherent.isFiniteTypeOnAffine_ker`, the sections of `𝓟` over an affine open forming a
Noetherian ring).

## Main results

* `Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_polyAlgebra`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple

universe u

namespace Stacks.Coherent

/-- **Part (2) of [Stacks, Tag 0897] over a polynomial algebra.** For `A` Noetherian,
`f : X ⟶ Spec A` proper, `L` ample invertible and `N` a quasi-coherent graded module of finite type
over `𝒪_X[x_i : i ∈ ι]` with `ι` finite, one `d₀` kills the higher cohomology of every
`Nₙ ⊗ L ^⊗ d` with `d ≥ d₀`, in every positive degree and for every homogeneous degree `n`. -/
public theorem exists_isZero_Hgroup_piece_tensorPowModule_polyAlgebra (A : Type u) [CommRing A]
    [IsNoetherianRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] (L : X.Modules)
    [IsInvertibleModule X L] (hL : IsAmple X L) (ι : Type u) [Finite ι]
    (N : SheafOfModules.GradedModule (polyAlgebra X ι))
    (hqc : ∀ n : ℤ, (N.piece n).IsQuasicoherent) (hft : IsFiniteTypeOnAffine N) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℤ,
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (N.piece n) (tensorPowModule X L d))) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine exists_isZero_Hgroup_piece_tensorPowModule_of_devissage A f L
    (Stacks.SymmetricFree.forall_moduleFinite_symmetricAlgebraPiece X ι)
    (fun M hMqc hMft p hp => ?_) N hqc hft
  obtain ⟨Q, π, hπ, hQqc, hQft, d₁, hd₁⟩ :=
    exists_epi_degreePresentation_polyAlgebra A f L hL ι M hMqc hMft
  exact ⟨SheafOfModules.GradedModule.ker π, kerShortComplex π,
    fun n => shortExact_kerShortComplex π hπ n, fun _ => rfl, fun _ => rfl,
    isQuasicoherent_gradedKer_piece π hQqc hMqc,
    isFiniteTypeOnAffine_ker π hQft (isNoetherianRing_total_polyAlgebra ι), d₁, hd₁⟩

end Stacks.Coherent

end
