module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ClosedImmersionAdicSystem

/-!
# Ascent of membership in `Coh(-, -)` along a closed-immersion direct image

Let `i : Z ⟶ X` be a closed immersion of locally Noetherian schemes and `ℐ ⊆ 𝒪_X` a quasi-coherent
sheaf of ideals, with inverse image `ℐ 𝒪_Z = ℐ.comap i`. Termwise direct image carries
`Coh(Z, ℐ 𝒪_Z)` into `Coh(X, ℐ)`; together with the converse
`Stacks.Coherent.isCoherentAdicSystem_of_pushforward`, a system of coherent `𝒪_Z`-modules lies in
`Coh(Z, ℐ 𝒪_Z)` if and only if its termwise direct image lies in `Coh(X, ℐ)`.

## Main results

* `Stacks.Coherent.isCoherentAdicSystem_pushforward_closedImmersion`: the termwise direct image of
  a coherent adic system along `ℐ 𝒪_Z` is a coherent adic system along `ℐ`.
* `Stacks.Coherent.isCoherentAdicSystem_pushforward_closedImmersion_iff`: the two memberships are
  equivalent.

## References

* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

open Stacks.Algebraization

section ClosedImmersion

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
  [IsLocallyNoetherian X] [IsLocallyNoetherian Z]

/-- **The termwise direct image of a coherent adic system along a closed immersion is a coherent
adic system.** If `(F_n)` is a coherent adic system along `ℐ 𝒪_Z = ℐ.comap i` on the closed
subscheme `Z`, then `(i_* F_n)` is a coherent adic system along `ℐ` on `X`. -/
public theorem isCoherentAdicSystem_pushforward_closedImmersion (I : X.IdealSheafData)
    (Q : ℕᵒᵖ ⥤ Z.Modules) (h : IsCoherentAdicSystem (I.comap i) Q) :
    IsCoherentAdicSystem I (Q ⋙ Scheme.Modules.pushforward i) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · have _ : (Q.obj (op n)).IsCoherent := h.1 n
    exact isCoherent_pushforward_closedImmersion i (Q.obj (op n))
  · exact (idealPowerMultiple_pushforward_eq_bot_iff i I (n + 1) (Q.obj (op n))).mpr (h.2.1 n)
  · obtain ⟨e, he⟩ := h.2.2 n
    have _ : (Q.obj (op (n + 1))).IsCoherent := h.1 (n + 1)
    have _ := isIso_pushforwardAdicQuotientMap i I n (Q.obj (op (n + 1)))
    refine ⟨asIso (pushforwardAdicQuotientMap i I (n + 1) (Q.obj (op (n + 1)))) ≪≫
      (Scheme.Modules.pushforward i).mapIso e, ?_⟩
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (Scheme.Modules.pushforward i).map e.hom)
          (pushforwardAdicQuotientMap_π i I (n + 1) (Q.obj (op (n + 1))))).trans
        (((Scheme.Modules.pushforward i).map_comp _ _).symm.trans
          (congrArg (Scheme.Modules.pushforward i).map he)))

/-- **Termwise direct image along a closed immersion detects coherent adic systems exactly.** A
system of coherent `𝒪_Z`-modules is a coherent adic system along `ℐ 𝒪_Z` if and only if its
termwise direct image is a coherent adic system along `ℐ`. -/
public theorem isCoherentAdicSystem_pushforward_closedImmersion_iff (I : X.IdealSheafData)
    (Q : ℕᵒᵖ ⥤ Z.Modules) (hQ : ∀ n : ℕᵒᵖ, (Q.obj n).IsCoherent) :
    IsCoherentAdicSystem I (Q ⋙ Scheme.Modules.pushforward i) ↔
      IsCoherentAdicSystem (I.comap i) Q :=
  ⟨isCoherentAdicSystem_of_pushforward i I Q hQ,
    isCoherentAdicSystem_pushforward_closedImmersion i I Q⟩

end ClosedImmersion

end Stacks.Coherent

end
