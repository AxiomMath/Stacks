module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexStandardModel
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DualizingNoetherianReduction
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TraceExistence
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TraceOrbit
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TraceUniqueness
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Duality.SmoothProper.RelativeDualizingComplex

/-!
# The trace of relative Poincaré duality, from `Ω^n[n] ≅ a(𝒪_S)` at the locally small model

In the situation of relative Poincaré duality ([Stacks, Tag 0G8G]), an isomorphism
`Ω^n_{X/S}[n] ≅ a(𝒪_S)` at the locally small model of the derived categories, the model of
[Stacks, Tag 0BRT] and of flat base change, gives one at the standard model, where
`AlgebraicGeometry.RelativeDualitySituation.isRelativePoincareTrace_of_iso` turns it into a trace
with the property of [Stacks, Tag 0G8I]; that trace is unique up to a unit of `Γ(X, 𝒪_X)` by
`AlgebraicGeometry.RelativeDualitySituation.IsRelativePoincareTrace.exists_units`. Over a
Noetherian base the isomorphism at the locally small model is [Stacks, Tag 0BRT]; over a
quasi-compact quasi-separated base it follows by Noetherian approximation
(`Stacks.Duality.nonempty_singleFunctor_exteriorPower_iso_relativeDualizingComplex_of_noetherian`).

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.formsShiftIsoRelativeDualizingComplexOfModel`
* `AlgebraicGeometry.RelativeDualitySituation.existsUnique_isRelativePoincareTrace_of_model`
* `AlgebraicGeometry.RelativeDualitySituation.existsUnique_isRelativePoincareTrace`:
  [Stacks, Tag 0G8I].
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Stacks.StandardDerivedModel

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- **`Ω^n_{X/S}[n] ≅ a(𝒪_S)` at the standard model**, from the same isomorphism at the locally
small model: `Ω^n` in degree zero shifted by `n` is `Ω^n` placed in degree `-n`. -/
def formsShiftIsoRelativeDualizingComplexOfModel
    (ψ₀ : (@DerivedCategory.singleFunctor D.X.Modules _ _ (Scheme.Modules.hasDerivedCategory D.X)
      (-(D.n : ℤ))).obj (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials D.f) D.n) ≅
      (@Stacks.Duality.relativeDualizingComplex D.X D.S D.f
          (Scheme.Modules.hasDerivedCategory D.X) (Scheme.Modules.hasDerivedCategory D.S)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs D.f)
          (Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
            D.f) (Stacks.Duality.DerivedPushforward.derivedStructureSheaf D.S)).obj) :
    (D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧ ≅ (Stacks.Duality.relativeDualizingComplex D.f
      (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0)).obj :=
  (shiftFunctor _ (D.n : ℤ)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ D.X.Modules 0).app _).symm ≪≫
    ((DerivedCategory.singleFunctors D.X.Modules).shiftIso (D.n : ℤ) (-(D.n : ℤ)) 0
      (by simp)).app _ ≪≫
    Stacks.Duality.StandardModel.singleFunctorIsoRelativeDualizingComplexOfModel D.f
      (-(D.n : ℤ)) _ ψ₀

/-- **[Stacks, Tag 0G8I] from `Ω^n_{X/S}[n] ≅ a(𝒪_S)` at the locally small model**: there is a
trace `t : Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S` all of whose pairings are perfect pairings of perfect
complexes, and the traces with this property are exactly the `t ∘ u` for `u` a unit of
`Γ(X, 𝒪_X)`. -/
theorem existsUnique_isRelativePoincareTrace_of_model
    (ψ₀ : Nonempty ((@DerivedCategory.singleFunctor D.X.Modules _ _
      (Scheme.Modules.hasDerivedCategory D.X)
      (-(D.n : ℤ))).obj (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials D.f) D.n) ≅
      (@Stacks.Duality.relativeDualizingComplex D.X D.S D.f
          (Scheme.Modules.hasDerivedCategory D.X) (Scheme.Modules.hasDerivedCategory D.S)
          (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs D.f)
          (Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs
            D.f) (Stacks.Duality.DerivedPushforward.derivedStructureSheaf D.S)).obj)) :
    ∃ t : (Stacks.Duality.derivedPushforward D.f).obj ((D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧) ⟶
        (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj,
      D.IsRelativePoincareTrace t ∧ ∀ t', D.IsRelativePoincareTrace t' ↔
        ∃ u : (Γ(D.X, ⊤))ˣ, t' = D.f.formsShiftSMul D.n u ≫ t := by
  obtain ⟨ψ₀⟩ := ψ₀
  have ht := D.isRelativePoincareTrace_of_iso (D.formsShiftIsoRelativeDualizingComplexOfModel ψ₀)
  refine ⟨_, ht, fun t' => ⟨fun ht' => ht.exists_units ht', ?_⟩⟩
  rintro ⟨u, rfl⟩
  exact ht.formsShiftSMul u

/-- In the situation of relative Poincaré duality ([Stacks, Tag 0G8G]), `f : X ⟶ S` proper and
smooth over a quasi-compact quasi-separated base, all of whose fibres are nonempty and
equidimensional of dimension `n`, there is an `𝒪_S`-module map
`t : Rf_*Ω^n_{X/S}[n] ⟶ 𝒪_S` such that for all `p` the pairing
`Rf_*Ω^p_{X/S} ⊗^L Rf_*Ω^{n-p}_{X/S}[n] ⟶ 𝒪_S` given by the relative cup product composed with
`t` is a perfect pairing of perfect complexes, and `t` is unique up to precomposing with
multiplication by a unit of `H^0(X, 𝒪_X)`: the maps with this property are exactly the
`t ∘ u` for `u` a unit of `Γ(X, 𝒪_X)`. -/
@[stacks 0G8I "relative Poincaré duality trace: there is t : Rf_*Omega^n[n] -> O_S, unique up to \
a unit of H^0(X, O_X), all of whose pairings Rf_*Omega^p (x)^L Rf_*Omega^{n-p}[n] -> O_S are \
perfect pairings of perfect complexes"]
theorem existsUnique_isRelativePoincareTrace :
    ∃ t : (Stacks.Duality.derivedPushforward D.f).obj ((D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧) ⟶
        (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj,
      D.IsRelativePoincareTrace t ∧ ∀ t', D.IsRelativePoincareTrace t' ↔
        ∃ u : (Γ(D.X, ⊤))ˣ, t' = D.f.formsShiftSMul D.n u ≫ t :=
  D.existsUnique_isRelativePoincareTrace_of_model
    (Stacks.Duality.nonempty_singleFunctor_exteriorPower_iso_relativeDualizingComplex_of_noetherian
      D.f D.n (fun h =>
        ⟨Stacks.Duality.singleFunctorExteriorPowerIsoRelativeDualizingComplex h D.n⟩))

end AlgebraicGeometry.RelativeDualitySituation

end
