module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveSerreVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistSectionsDegreeOne

/-!
# Finiteness of the twisted global sections of the pushforward of the structure sheaf of a blowup

Let `A` be a Noetherian ring, `I ⊆ A` an ideal with a chosen finite generating family `x₀, …, x_m`,
and `X = Proj(⨁ₙ Iⁿ)` the blowup of `Spec A` in `I`. Write `i : X ⟶ 𝐏 = Proj A[T₀, …, T_m]` for the
closed immersion of `X` into projective space coming from the polynomial presentation of the Rees
algebra (`Stacks.Blowup.isClosedImmersion_blowUpSpecToProjSpace`). This file proves that the graded
`A[T₀, …, T_m]`-module

`⨁_{d ≥ k} Γ(𝐏, (i_*𝒪_X)(d))`

is finite, for every `k`. This is [Stacks, Tag 01YS] clause (5) applied to the *pushforward* sheaf
`i_*𝒪_X`, which is coherent on the locally Noetherian `𝐏` because `𝒪_X` is coherent on the locally
Noetherian `X` and the direct image along a closed immersion into a locally Noetherian scheme is
coherent ([Stacks, Tag 087T]); clause (5) itself holds for an arbitrary coherent sheaf on
projective space,
`Stacks.ProjectiveSpace.Cohomology.moduleFinite_truncation_twistedGlobalSectionsModule`.

The statement concerns `i_*𝒪_X` on `𝐏`, not `𝒪_X` on the blowup `X` itself.

## Main results

* `Stacks.Blowup.moduleFinite_truncation_pushforward_of_span`: the finiteness, for a blowup
  presented by a finite generating family of `I`.

## References

* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.ProjectiveCohomology (polyGrading)
open Stacks.AlgebraicGeometry.ProjTwistedSections

universe u

namespace Stacks.Blowup

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **[Stacks, Tag 01YS] clause (5) for the pushforward of the structure sheaf of the blowup**, for
a blowup presented by a finite generating family of `I`: for every `k` the graded
`A[T₀, …, T_m]`-module `⨁_{d ≥ k} Γ(𝐏, (i_*𝒪_X)(d))` is a finite module, where
`i : X ⟶ 𝐏 = Proj A[T₀, …, T_m]` is the closed immersion of the blowup into projective space coming
from the chosen generating family. -/
theorem moduleFinite_truncation_pushforward_of_span {A : Type u} [CommRing A]
    [IsNoetherianRing A] {I : Ideal A} {n : ℕ} (x : Fin (n + 1) → A) (hx : ∀ j, x j ∈ I)
    (hspan : I = Ideal.span (Set.range x)) (k : ℤ) :
    letI := (twistedGlobalSectionsModule (polyGrading A n)
      ((Scheme.Modules.pushforward (blowUpSpecToProjSpace I x hx hspan)).obj
        (SheafOfModules.unit (blowUpSpec I).ringCatSheaf))).moduleInst
    Module.Finite (MvPolynomial (Fin (n + 1)) A)
      (TwistedGlobalSectionsModule.truncation (polyGrading A n)
        ((Scheme.Modules.pushforward (blowUpSpecToProjSpace I x hx hspan)).obj
          (SheafOfModules.unit (blowUpSpec I).ringCatSheaf))
        (twistedGlobalSectionsModule (polyGrading A n)
          ((Scheme.Modules.pushforward (blowUpSpecToProjSpace I x hx hspan)).obj
            (SheafOfModules.unit (blowUpSpec I).ringCatSheaf))) k) := by
  have : IsLocallyNoetherian (blowUpSpec I) :=
    isLocallyNoetherian_of_isClosedImmersion (blowUpSpecToProjSpace I x hx hspan)
  have : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit (blowUpSpec I).ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit (blowUpSpec I)
  exact Stacks.ProjectiveSpace.Cohomology.moduleFinite_truncation_twistedGlobalSectionsModule A n
    ((Scheme.Modules.pushforward (blowUpSpecToProjSpace I x hx hspan)).obj
      (SheafOfModules.unit (blowUpSpec I).ringCatSheaf))
    (isCoherent_pushforward_of_isClosedImmersion (blowUpSpecToProjSpace I x hx hspan)
      (SheafOfModules.unit (blowUpSpec I).ringCatSheaf)) k

end Stacks.Blowup

end
