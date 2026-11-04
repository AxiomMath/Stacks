module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.FactorizationIndependence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.NoetherianRegularKoszul
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Regularity of the immersion of a factorization of an lci morphism

Let `f : X ⟶ Y` be a local complete intersection morphism and `f = g ∘ i` a factorization with
`i : X ⟶ P` an immersion and `g : P ⟶ Y` smooth (`Stacks.Chow.SmoothFactorization`). This file
proves that `i` is a Koszul-regular immersion with no hypothesis beyond the lci hypothesis on `f`,
and a regular immersion when `P` is locally Noetherian.

## Main results

* `Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion_of_lci` — `i` is a Koszul-regular
  immersion. This is `Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion` (Stacks 069G at
  the top open) with its Koszul-case input, Stacks 0693, discharged by
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_comp_of_smooth`.
* `Stacks.Chow.SmoothFactorization.isRegularImmersion` — over a locally Noetherian `P`, `i` is a
  regular immersion (Stacks 063L). This is the regularity of `i` that the section on Gysin maps
  for local complete intersection morphisms uses to form `i^! = c(X ⟶ P, 𝒩_{X/P})`.

## References

* [Stacks Project, Tag 0FF2](https://stacks.math.columbia.edu/tag/0FF2)
* [Stacks Project, Tag 069G](https://stacks.math.columbia.edu/tag/069G)
* [Stacks Project, Tag 0693](https://stacks.math.columbia.edu/tag/0693)
* [Stacks Project, Tag 063L](https://stacks.math.columbia.edu/tag/063L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- **The immersion of a factorization of a local complete intersection morphism is a
Koszul-regular immersion**, with no hypothesis beyond the lci hypothesis: the Koszul case of
Stacks 0693 that `Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion` takes as an argument
is `Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_comp_of_smooth`. -/
@[sga "6 0 3.2"]
theorem SmoothFactorization.isKoszulRegularImmersion_of_lci (F : SmoothFactorization f)
    (hf : IsLocalCompleteIntersectionMorphism f) : IsKoszulRegularImmersion F.imm :=
  SmoothFactorization.isKoszulRegularImmersion
    (fun a p _ _ _ ha ↦ isKoszulRegularImmersion_comp_of_smooth a p ha) F hf

/-- The immersion `i : X ⟶ P` of a factorization `f = g ∘ i` of a local complete intersection
morphism `f` into a locally Noetherian scheme `P` is a regular immersion: it is Koszul-regular by
`Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion_of_lci`, and over a locally Noetherian
scheme the two notions agree (Stacks 063L). This is the regularity of `i` that the section on
Gysin maps for local complete intersection morphisms uses to form `i^! = c(X ⟶ P, 𝒩_{X/P})`. -/
@[sga "5 III 6.8" "partial",
  sga "6 0 3.2" "special case",
  sga "6 VII 1.10" "special case",
  sga "6 VIII 1.1" "partial",
  sga "6 VIII 1.2" "special case",
  sga "6 VIII 1.3" "(i), special case",
  sga "6 VIII 1.8" "partial",
  sga "6 VIII 2.4" "special case",
  sga "6 VIII 3.1" "partial"]
theorem SmoothFactorization.isRegularImmersion (F : SmoothFactorization f)
    [IsLocallyNoetherian F.ambient] (hf : IsLocalCompleteIntersectionMorphism f) :
    IsRegularImmersion F.imm :=
  (isRegularImmersion_iff_isKoszulRegularImmersion F.imm).2 (F.isKoszulRegularImmersion_of_lci hf)

end Stacks.Chow

end
