module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.CompletedLocalPuncturedSpectrum
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.SectionsFunctionField

/-!
# Enlarging an open subset preserves finiteness of its sections on an integral scheme

On an integral scheme the restriction map between the sections over two nested nonempty opens is
injective, because both factor injectively through the function field. Consequently, over a
Noetherian base ring, finiteness of the sections over the **smaller** open forces finiteness of
the sections over the **larger** one: the latter is a submodule of the former.

## Main results

Both in the namespace `Stacks.AlgebraicGeometry.CodimensionOneObstruction`.

* `moduleFinite_sections_of_le`: for nested opens `U' ≤ U ≤ V₀` with `U'` nonempty and
  `Γ(X, V₀)` Noetherian, finiteness of `Γ(X, U')` over `Γ(X, V₀)` gives finiteness of `Γ(X, U)`.
* `moduleFinite_sections_puncturedSpectrum_of_le`: the case where `X = Spec R` for a Noetherian
  local domain `R`, the larger open is the punctured spectrum and the base is the top open.

## Implementation notes

The scalar structures are the restriction algebras
`Stacks.AlgebraicGeometry.CodimensionOneObstruction.resAlgebra`, which is also how the
finiteness statements of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.SectionsFunctionField`
are phrased; Mathlib carries an `Algebra Γ(X, U) Γ(X, V)` instance only when `V` is a basic open
of `U`.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.LocalCohomology (puncturedSpectrum)

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

/-- Restriction of sections is transitive: restricting from `V₀` to `U` and then to `U'` is
restricting from `V₀` to `U'`. -/
theorem presheaf_map_homOfLE_trans {X : Scheme.{u}} {V₀ U U' : X.Opens} (hU'U : U' ≤ U)
    (hUV : U ≤ V₀) (c : Γ(X, V₀)) :
    X.presheaf.map (homOfLE hU'U).op (X.presheaf.map (homOfLE hUV).op c)
      = X.presheaf.map (homOfLE (hU'U.trans hUV)).op c := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  congr 1

/-- **Finiteness of the sections over a nonempty open passes to every larger open on an integral
scheme.** Let `X` be integral, let `U' ≤ U ≤ V₀` be opens with `U'` nonempty, and suppose
`Γ(X, V₀)` is Noetherian. If `Γ(X, U')` is a finite `Γ(X, V₀)`-module, so is `Γ(X, U)`.

The scalar actions are restriction of sections. -/
theorem moduleFinite_sections_of_le {X : Scheme.{u}} [IsIntegral X] {V₀ U U' : X.Opens}
    [IsNoetherianRing Γ(X, V₀)] [Nonempty U'.toScheme] (hU'U : U' ≤ U) (hUV : U ≤ V₀)
    (h : letI := resAlgebra (hU'U.trans hUV); Module.Finite Γ(X, V₀) Γ(X, U')) :
    letI := resAlgebra hUV; Module.Finite Γ(X, V₀) Γ(X, U) := by
  let := resAlgebra hUV
  let := resAlgebra (hU'U.trans hUV)
  have hfin := h
  obtain ⟨y, hy⟩ : (U' : Set X).Nonempty := by simpa using ‹Nonempty U'.toScheme›
  have : Nonempty U.toScheme := ⟨⟨y, hU'U hy⟩⟩
  let r : Γ(X, U) →ₗ[Γ(X, V₀)] Γ(X, U') :=
    { toFun := fun s => X.presheaf.map (homOfLE hU'U).op s
      map_add' := fun a b => map_add _ a b
      map_smul' := fun c s => by
        change X.presheaf.map (homOfLE hU'U).op
            (X.presheaf.map (homOfLE hUV).op c * s)
          = X.presheaf.map (homOfLE (hU'U.trans hUV)).op c
              * X.presheaf.map (homOfLE hU'U).op s
        rw [map_mul, presheaf_map_homOfLE_trans] }
  refine Module.Finite.of_injective r (fun a b hab => ?_)
  have hga : X.germToFunctionField U' (X.presheaf.map (homOfLE hU'U).op a)
      = X.germToFunctionField U' (X.presheaf.map (homOfLE hU'U).op b) := congrArg _ hab
  rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hga
  exact X.germToFunctionField_injective U hga

/-- **Finiteness of the sections over a nonempty open passes to the punctured spectrum.** Let
`R` be a Noetherian local domain and let `U'` be a nonempty open of `Spec R` contained in the
punctured spectrum. If the sections over `U'` are a finite module over the sections over the
whole of `Spec R`, so are the sections over the punctured spectrum. -/
theorem moduleFinite_sections_puncturedSpectrum_of_le (R : CommRingCat.{u}) [IsNoetherianRing R]
    [IsLocalRing R] [IsDomain R] {U' : (Spec R).Opens} [Nonempty U'.toScheme]
    (hU' : U' ≤ puncturedSpectrum R)
    (h : letI := resAlgebra (le_top (a := U')); Module.Finite Γ(Spec R, ⊤) Γ(Spec R, U')) :
    letI := resAlgebra (le_top (a := puncturedSpectrum R));
      Module.Finite Γ(Spec R, ⊤) Γ(Spec R, puncturedSpectrum R) := by
  have : IsNoetherianRing Γ(Spec R, ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
  exact moduleFinite_sections_of_le hU' le_top h

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
