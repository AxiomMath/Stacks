module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.SpecTransport
public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.DedekindSituation
public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.DedekindTraceSection

/-!
# The generalized different when the Dedekind different is defined

Let `A → B` be a ring map for which the Dedekind different is defined, and let
`f : Y = Spec(B) → X = Spec(A)`.  Then `f` satisfies the first condition of the generalization of
the different (Remark 0BWM), and the trace element `τ_{V/X}` of the flat locus `V` comes from a
global section of `ω_{Y/X}` exactly when `1` lies in the complementary module `L_{B/A}` — for
instance when `A` is normal.  In this case the Dedekind different `𝔇_{B/A}` is an ideal of `B`,
and the generalized different `𝔇_f` is the coherent sheaf of ideals `(𝔇_{B/A})~` on `Y`.

## Main results

* `Stacks.Discriminant.generalizedDifferent_spec_eq_tilde_dedekindDifferent`: Tag 0BWN.

## Implementation notes

The relative dualizing module of `f` is any chart datum `ω` for it in the sense of Tag 0BVG (one
exists, see `Stacks.Discriminant.nonempty_relativeDualizingModuleData`); the statement holds for
each of them.  "The generalization applies" is the conjunction of the two conditions of Remark
0BWM: an open of `Y` over which `f` is flat contains `Ass(𝒪_Y)` and `f⁻¹(Ass(𝒪_X))`
(`Stacks.Discriminant.GeneralizedDifferentSituation`), and a global section of `ω_{Y/X}` is the
trace element on every flat chart (`Stacks.Discriminant.GeneralizedTraceSection`).  The sheaf of
ideals `(𝔇_{B/A})~` is the ideal sheaf of `Spec B` attached to the image of `𝔇_{B/A}` in
`Γ(Spec B, ⊤)` (`AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop`), read as a subsheaf of
`𝒪_Y`.

The proof reduces to the global sections `Γ(X, ⊤) → Γ(Y, ⊤)`, to which the Dedekind setup is
transported along `A ≅ Γ(Spec A, ⊤)` and `B ≅ Γ(Spec B, ⊤)`; there the statement is
`Stacks.Discriminant.nonempty_generalizedTraceSection_iff_of_isAffine` and
`Stacks.Discriminant.generalizedDifferent_eq_unitSubmodule_of_isAffine`.

## References

* [Stacks Project, Tag 0BWN](https://stacks.math.columbia.edu/tag/0BWN)
* [Stacks Project, Tag 0BWM](https://stacks.math.columbia.edu/tag/0BWM)
* [Stacks Project, Tag 0BW1](https://stacks.math.columbia.edu/tag/0BW1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace Stacks.Discriminant

section Affine

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] [IsAffine X] [IsAffine Y]

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] [IsAffine X]
  [IsAffine Y] in
/-- For a morphism of schemes `f : Y ⟶ X`, the map `f.appLE ⊤ ⊤ _ : Γ(X, ⊤) ⟶ Γ(Y, ⊤)` on global
sections is `f.appTop`. -/
theorem appLE_top_top (f : Y ⟶ X) : f.appLE ⊤ ⊤ le_top = f.appTop :=
  f.appLE_eq_app

/-- `Stacks.Discriminant.nonempty_generalizedTraceSection_iff_of_isAffine` for the algebra
structure given by `f.appTop`. -/
theorem nonempty_generalizedTraceSection_iff_of_isAffine' (ω : RelativeDualizingModuleData f)
    (setup : letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
      DedekindDifferentSetup Γ(X, ⊤) Γ(Y, ⊤)) :
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
    Nonempty (GeneralizedTraceSection ω) ↔
      (1 : Γ(Y, ⊤) ⊗[Γ(X, ⊤)] FractionRing Γ(X, ⊤)) ∈ setup.complementaryModule := by
  revert setup
  rw [← appLE_top_top]
  exact nonempty_generalizedTraceSection_iff_of_isAffine ω

/-- `Stacks.Discriminant.generalizedDifferent_eq_unitSubmodule_of_isAffine` for the algebra
structure given by `f.appTop`. -/
theorem generalizedDifferent_eq_unitSubmodule_of_isAffine' (ω : RelativeDualizingModuleData f)
    (setup : letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
      DedekindDifferentSetup Γ(X, ⊤) Γ(Y, ⊤))
    (h1 : letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
      (1 : Γ(Y, ⊤) ⊗[Γ(X, ⊤)] FractionRing Γ(X, ⊤)) ∈ setup.complementaryModule)
    (τ : GeneralizedTraceSection ω) :
    letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
    generalizedDifferent ω τ =
      (Scheme.IdealSheafData.ofIdealTop (dedekindDifferentIdeal setup)).unitSubmodule := by
  revert setup
  rw [← appLE_top_top]
  exact fun setup h1 => generalizedDifferent_eq_unitSubmodule_of_isAffine ω setup h1 τ

end Affine

/-- For a finite ring map `A → B`, the morphism `Spec B ⟶ Spec A` is locally quasi-finite. -/
theorem locallyQuasiFinite_spec_map {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  infer_instance

/-- **[Stacks, Tag 0BWN].** Assume the Dedekind different is defined for `A → B`, and set
`X = Spec(A)`, `Y = Spec(B)` and `f : Y → X`.  Then, for the relative dualizing module `ω` of
`f`, the generalization of the different (Remark 0BWM) applies to `f` — an open of `Y` over which
`f` is flat contains `Ass(𝒪_Y)` and `f⁻¹(Ass(𝒪_X))`, and the trace element of the flat locus
comes from a global section of `ω_{Y/X}` — if and only if `1 ∈ L_{B/A}`; this is the case for
instance if `A` is normal.  In this case the Dedekind different `𝔇_{B/A}` is an ideal of `B`,
and the generalized different `𝔇_f` is the coherent sheaf of ideals `(𝔇_{B/A})~` on `Y`. -/
@[stacks 0BWN "the generalized different of `Spec B → Spec A` is defined iff `1 ∈ L_{B/A}` (e.g.
for normal `A`), and then `𝔇_{B/A}` is an ideal of `B` and `𝔇_f = (𝔇_{B/A})~`"]
theorem generalizedDifferent_spec_eq_tilde_dedekindDifferent {A B : Type u} [CommRing A]
    [CommRing B] [Algebra A B] (setup : DedekindDifferentSetup A B) :
    letI : IsNoetherianRing A := setup.isNoetherianRing
    letI : Module.Finite A B := setup.finite
    letI : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    letI := locallyQuasiFinite_spec_map (A := A) (B := B)
    ∀ ω : RelativeDualizingModuleData (Spec.map (CommRingCat.ofHom (algebraMap A B))),
      ((Nonempty (GeneralizedDifferentSituation (Spec.map (CommRingCat.ofHom (algebraMap A B)))) ∧
          Nonempty (GeneralizedTraceSection ω)) ↔
        (1 : B ⊗[A] FractionRing A) ∈ setup.complementaryModule) ∧
      (IsNormalRing A → (1 : B ⊗[A] FractionRing A) ∈ setup.complementaryModule) ∧
      ((1 : B ⊗[A] FractionRing A) ∈ setup.complementaryModule →
        setup.dedekindDifferent =
            Submodule.map (Algebra.linearMap B (B ⊗[A] FractionRing A))
              (dedekindDifferentIdeal setup : Submodule B B) ∧
          ∀ τ : GeneralizedTraceSection ω,
            Stacks.SheafOfModules.IsCoherent (generalizedDifferent ω τ).toSheafOfModules ∧
            generalizedDifferent ω τ =
              (Scheme.IdealSheafData.ofIdealTop ((dedekindDifferentIdeal setup).map
                (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)).unitSubmodule) := by
  let : IsNoetherianRing A := setup.isNoetherianRing
  let : Module.Finite A B := setup.finite
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  let := locallyQuasiFinite_spec_map (A := A) (B := B)
  intro ω
  refine ⟨⟨fun ⟨_, hτ⟩ => ?_, fun h1 => ⟨⟨generalizedDifferentSituationOfDedekind setup.toSpec⟩,
    (nonempty_generalizedTraceSection_iff_of_isAffine' ω setup.toSpec).mpr
      ((setup.one_mem_complementaryModule_toSpec_iff).mpr h1)⟩⟩,
    one_mem_complementaryModule_of_isNormalRing setup, fun h1 =>
      ⟨dedekindDifferent_eq_map_ideal setup h1, fun τ => ⟨isCoherent_generalizedDifferent ω τ, ?_⟩⟩⟩
  · exact setup.one_mem_complementaryModule_toSpec_iff.mp
      ((nonempty_generalizedTraceSection_iff_of_isAffine' ω setup.toSpec).mp hτ)
  · rw [generalizedDifferent_eq_unitSubmodule_of_isAffine' ω setup.toSpec
      ((setup.one_mem_complementaryModule_toSpec_iff).mpr h1) τ,
      DedekindDifferentSetup.dedekindDifferentIdeal_toSpec]

end Stacks.Discriminant
