module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedPoincareCurvature
public import StacksFrontier.AlgebraicGeometry.Crystalline.FinitePerturbation

/-!
# The crystalline Poincaré lemma for a module with an integrable connection

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, and let
`P = B⟨x_w : w ∈ W⟩` be the divided power polynomial ring over `B` on an arbitrary family of
variables, with divided power ideal `J = IP + B⟨x_w⟩₊`.  For a `B`-module `M` with an integrable
connection `∇ : M → M ⊗_B Ω¹_{B/A,δ}`, the first clause of [Stacks, Lemma 60.19.2, Tag 07LD]
asserts that the canonical map of de Rham complexes

`M ⊗_B Ω^*_{B/A,δ} ⟶ M ⊗_P Ω^*_{P/A,δ}`

is a quasi-isomorphism.  The target is the de Rham complex of the base change
`(P ⊗_B M, ∇')` of the connection to `P`, whose terms are `(P ⊗_B M) ⊗_P Ω^i_{P/A,δ}`, and the map
is the canonical one of [Stacks, Tag 07PY].  This module sets up the two complexes and the map;
the assertion is `Crystalline.DividedPowerPolynomial.quasiIso_polyDeRhamComparison` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/RelativePoincareModuleQuasiIso.lean`,
where the map is shown to have a homotopy inverse on the underlying complexes of abelian groups.

The proof needs the target in the form `M ⊗_B Ω^*_{P/A,δ}`, with differential
`m ⊗ ω ↦ ψ(∇ m) ∧ ω + m ⊗ d ω`; `Crystalline.DividedPowerPolynomial.polyTermEquiv` is the
identification `(P ⊗_B M) ⊗_P Ω^n_{P/A,δ} ≅ M ⊗_B Ω^n_{P/A,δ}`, under which the canonical map
becomes `1_M ⊗ ψ` (`Crystalline.DividedPowerPolynomial.polyTermEquiv_polyComparison`).

## Main definitions

* `Crystalline.DividedPowerPolynomial.polyProjection`, `…polySource` — the divided power
  differentials of `P` as the quotient of the Kähler differentials that descent consumes.
* `Crystalline.DividedPowerPolynomial.oneFormComparison` — the comparison
  `Ω¹_{B/A,δ} → Ω¹_{P/A,δ}` along `B → P`.
* `Crystalline.DividedPowerPolynomial.polyBaseChangeConnection` — the base change `∇'` of a
  connection to `P ⊗_B M`.
* `Crystalline.DividedPowerPolynomial.polyTargetDeRhamComplex` — the de Rham complex
  `M ⊗_P Ω^*_{P/A,δ}`.
* `Crystalline.DividedPowerPolynomial.polyDeRhamComparison` — the canonical map of de Rham
  complexes.

## Main results

* `Crystalline.DividedPowerPolynomial.extendedConnection_deRhamDifferential` — the de Rham
  differential an extended connection on `P` uses is the divided power de Rham differential.
* `Crystalline.DividedPowerPolynomial.polyTermEquiv_polyComparison` — the canonical map is
  `1_M ⊗ ψ` once the base change is cancelled.

## References

* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07PY](https://stacks.math.columbia.edu/tag/07PY)
-/

@[expose] public noncomputable section

open CategoryTheory
open DividedPowers
open scoped TensorProduct
open Stacks.DeRham.DifferentialDescent

universe u w

namespace Crystalline

namespace DividedPowerPolynomial

/-! ### The divided power polynomial algebra as a target of base change -/

section Setup

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B] (W : Type u)

/-- The quotient `π' : Ω_{P/A} → Ω¹_{P/A,δ'}` onto the divided power differentials of
`P = B⟨x_w : w ∈ W⟩`. -/
abbrev polyProjection :
    Ω[setIndexedDividedPowerPolynomialAlgebra B W⁄A] →ₗ[setIndexedDividedPowerPolynomialAlgebra B W]
      dividedPowerDifferentials (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W) :=
  (dividedPowerDifferentialRelations (A := A)
    (setIndexedDividedPowerPolynomialDividedPowers B W)).mkQ

/-- The de Rham complex of `P` over `A`, as the data that divided power descent consumes. -/
abbrev polySource : SourceDeRham A (setIndexedDividedPowerPolynomialAlgebra B W) :=
  sourceDeRhamOfKaehler A (setIndexedDividedPowerPolynomialAlgebra B W)

/-- The divided power relations of `P` are spanned by good generators, so the de Rham
differential descends to `Ω^*_{P/A,δ'}`. -/
theorem polyGenerationHypothesis :
    (polySource A B W).GenerationHypothesis (polyProjection A B W) :=
  generationHypothesis_of_ker_eq_relations (setIndexedDividedPowerPolynomialDividedPowers B W) _ _
    (Submodule.ker_mkQ _)

/-- **The comparison `ψ : Ω¹_{B/A,δ} → Ω¹_{P/A,δ'}` of one-forms** along the coefficient
inclusion `B → P`, which is a morphism of divided power rings. -/
def oneFormComparison :
    dividedPowerDifferentials (A := A) B.dividedPowers →ₛₗ[algebraMap (B : Type u)
        (setIndexedDividedPowerPolynomialAlgebra B W)]
      dividedPowerDifferentials (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W) :=
  mapDifferentialsOfDPMorphismₛₗ (A := A) (J := B.ideal) (delta := B.dividedPowers)
    (setIndexedDividedPowerPolynomialDividedPowers B W) (coefficientAlgHom A B W)
    (coefficientAlgHom_isDPMorphism A B W)

/-- The comparison of one-forms is compatible with the two Kähler differentials. -/
theorem oneFormComparison_compatible (b : (B : Type u)) :
    oneFormComparison A B W
        (oneVariableBaseProjection A B (KaehlerDifferential.D A (B : Type u) b)) =
      polyProjection A B W (KaehlerDifferential.D A (setIndexedDividedPowerPolynomialAlgebra B W)
        (algebraMap (B : Type u) (setIndexedDividedPowerPolynomialAlgebra B W) b)) :=
  mapDifferentialsOfDPMorphism_d (A := A) (J := B.ideal) (delta := B.dividedPowers)
    (setIndexedDividedPowerPolynomialDividedPowers B W) (coefficientAlgHom A B W)
    (coefficientAlgHom_isDPMorphism A B W) b

/-- The comparison of forms in every degree carries a wedge of one-forms to the wedge of their
images under `ψ`. -/
theorem coefficientFormsMap_ιMulti_oneFormComparison (p : ℕ)
    (omega : Fin p → dividedPowerDifferentials (A := A) B.dividedPowers) :
    coefficientFormsMap A B W p (exteriorPower.ιMulti (B : Type u) p omega) =
      exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) p
        (oneFormComparison A B W ∘ omega) :=
  mapDifferentialFormsOfDPMorphism_ιMulti (A := A) (J := B.ideal) (delta := B.dividedPowers)
    (setIndexedDividedPowerPolynomialDividedPowers B W) (coefficientAlgHom A B W)
    (coefficientAlgHom_isDPMorphism A B W) p omega

variable {M : Type w} [AddCommGroup M] [Module (B : Type u) M]

/-- **The base change `∇'` to `P ⊗_B M` of a connection on `M`**, by
`∇'(f ⊗ m) = f · (ψ ∘ ∇) m + (1 ⊗ m) ⊗ d f`. -/
def polyBaseChangeConnection
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M) :
    Connection A (setIndexedDividedPowerPolynomialAlgebra B W) (polyProjection A B W)
      (setIndexedDividedPowerPolynomialAlgebra B W ⊗[(B : Type u)] M) :=
  Connection.baseChange (oneFormComparison A B W) nabla (oneFormComparison_compatible A B W)

/-- The base change of an integrable connection is integrable. -/
theorem polyBaseChangeConnection_isIntegrable
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla) :
    Connection.IsIntegrable (polySource A B W) (polyProjection A B W)
      (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
      (polyBaseChangeConnection A B W nabla) :=
  baseChange_isIntegrable (oneVariableBaseSource A B) (polySource A B W)
    (oneVariableBaseProjection A B) (polyProjection A B W)
    (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B)
    (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
    (oneFormComparison A B W) (oneFormComparison_compatible A B W) nabla hint

variable (M) in
/-- The degree-`p` term `(P ⊗_B M) ⊗_P Ω^p_{P/A,δ'}` of the de Rham complex of the base change. -/
abbrev polyTargetTerm (p : ℕ) : Type (max u w) :=
  RestrictScalars A (setIndexedDividedPowerPolynomialAlgebra B W)
    ((setIndexedDividedPowerPolynomialAlgebra B W ⊗[(B : Type u)] M) ⊗[
      setIndexedDividedPowerPolynomialAlgebra B W]
      (⋀[setIndexedDividedPowerPolynomialAlgebra B W]^p
        (dividedPowerDifferentials (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W))))

/-- **The de Rham complex `M ⊗_P Ω^*_{P/A,δ'} = (P ⊗_B M) ⊗_P Ω^*_{P/A,δ'}`** of the base change
of an integrable connection. -/
abbrev polyTargetDeRhamComplex
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla) :
    CochainComplex (ModuleCat.{max u w} A) ℕ :=
  connectionDeRhamComplex (polySource A B W) (polyProjection A B W)
    (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
    (polyBaseChangeConnection A B W nabla) (polyBaseChangeConnection_isIntegrable A B W nabla hint)

/-- The canonical degreewise map of [Stacks, Tag 07PY], with its two characterising
properties. -/
theorem existsUnique_polyComparison
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla) :
    ∃! c : ∀ p : ℕ, oneVariableSourceTerm A B M p →ₗ[A] polyTargetTerm A B W M p,
      (∀ (p : ℕ) (m : M) (omega : Fin p → dividedPowerDifferentials (A := A) B.dividedPowers),
        c p (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p omega) =
          ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type u)] m) ⊗ₜ[
            setIndexedDividedPowerPolynomialAlgebra B W]
            exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) p
              (oneFormComparison A B W ∘ omega)) ∧
      (∀ (p : ℕ) (x : oneVariableSourceTerm A B M p),
        c (p + 1) ((extendedConnection (oneVariableBaseSource A B)
            (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
            (oneVariableBaseGenerationHypothesis A B) nabla).toLinearMap p x) =
          (extendedConnection (polySource A B W) (polyProjection A B W)
            (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
            (polyBaseChangeConnection A B W nabla)).toLinearMap p (c p x)) :=
  existsUnique_baseChangeDeRhamMap (S := oneVariableBaseSource A B) (S' := polySource A B W)
    (pi := oneVariableBaseProjection A B) (pi' := polyProjection A B W)
    (hpi := Submodule.mkQ_surjective _) (hgen := oneVariableBaseGenerationHypothesis A B)
    (hpi' := Submodule.mkQ_surjective _) (hgen' := polyGenerationHypothesis A B W)
    (psi := oneFormComparison A B W) (hpsi := oneFormComparison_compatible A B W)
    (nabla := nabla) hint

/-- **The canonical degreewise map `M ⊗_B Ω^p_{B/A,δ} → (P ⊗_B M) ⊗_P Ω^p_{P/A,δ'}`**,
`m ⊗ (ω₁ ∧ ⋯ ∧ ω_p) ↦ (1 ⊗ m) ⊗ (ψ ω₁ ∧ ⋯ ∧ ψ ω_p)`. -/
def polyComparison
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla) :
    ∀ p : ℕ, oneVariableSourceTerm A B M p →ₗ[A] polyTargetTerm A B W M p :=
  (existsUnique_polyComparison A B W nabla hint).exists.choose

/-- The canonical degreewise map on a wedge of one-forms. -/
theorem polyComparison_ιMulti
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (p : ℕ) (m : M) (omega : Fin p → dividedPowerDifferentials (A := A) B.dividedPowers) :
    polyComparison A B W nabla hint p
        (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p omega) =
      ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type u)] m) ⊗ₜ[
        setIndexedDividedPowerPolynomialAlgebra B W]
        exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) p
          (oneFormComparison A B W ∘ omega) :=
  (existsUnique_polyComparison A B W nabla hint).exists.choose_spec.1 p m omega

/-- The canonical degreewise map commutes with the two differentials. -/
theorem polyComparison_comm
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (p : ℕ) (x : oneVariableSourceTerm A B M p) :
    polyComparison A B W nabla hint (p + 1) ((extendedConnection (oneVariableBaseSource A B)
        (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
        (oneVariableBaseGenerationHypothesis A B) nabla).toLinearMap p x) =
      (extendedConnection (polySource A B W) (polyProjection A B W)
        (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W)
        (polyBaseChangeConnection A B W nabla)).toLinearMap p
          (polyComparison A B W nabla hint p x) :=
  (existsUnique_polyComparison A B W nabla hint).exists.choose_spec.2 p x

/-- **The canonical map of de Rham complexes `M ⊗_B Ω^*_{B/A,δ} ⟶ M ⊗_P Ω^*_{P/A,δ'}`** of
[Stacks, Tag 07PY]. -/
def polyDeRhamComparison
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla) :
    oneVariableSourceDeRhamComplex A B nabla hint ⟶ polyTargetDeRhamComplex A B W nabla hint where
  f p := ConcreteCategory.ofHom (C := ModuleCat A) (polyComparison A B W nabla hint p)
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      oneVariableSourceDeRhamComplex_hom_d, connectionDeRhamComplex_hom_d]
    exact (polyComparison_comm A B W nabla hint p x).symm

end Setup

/-! ### The descended de Rham differential of `P` is the divided power de Rham differential -/

section DeRham

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B] (W : Type u)
  {M : Type w} [AddCommGroup M] [Module (B : Type u) M]

/-- **The de Rham differential that an extended connection on `P` uses is the divided power de
Rham differential of `P`**: both satisfy the defining rule on the generators
`f₀ d f₁ ∧ ⋯ ∧ d f_p`, which determines the divided power de Rham complex. -/
theorem extendedConnection_deRhamDifferential {N : Type w} [AddCommGroup N]
    [Module (setIndexedDividedPowerPolynomialAlgebra B W) N]
    {nabla : Connection A (setIndexedDividedPowerPolynomialAlgebra B W) (polyProjection A B W) N}
    (E : ExtendedConnection (polySource A B W) (polyProjection A B W) nabla) :
    E.deRhamDifferential =
      (dividedPowerDeRhamComplex (A := A)
        (setIndexedDividedPowerPolynomialDividedPowers B W)).differential := by
  have h := Classical.choose_spec (exists_unique_quotient_deRhamDifferential (polySource A B W)
    (polyProjection A B W) (Submodule.mkQ_surjective _) (polyGenerationHypothesis A B W))
  have hE := h.2.2.1 _ E.commutes
  let C : DividedPowerDeRhamComplex (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W) :=
    { differential := E.deRhamDifferential
      differential_generator := fun i f ↦ by
        rw [hE]
        exact h.2.1 i f
      differential_squared := fun i ↦ by
        rw [hE]
        exact h.2.2.2 i }
  exact congrArg DividedPowerDeRhamComplex.differential C.unique

end DeRham

/-! ### Cancelling the base change -/

section Cancel

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B] (W : Type u)
  (M : Type w) [AddCommGroup M] [Module (B : Type u) M]

/-- `(P ⊗_B M) ⊗_P Ω^p_{P/A,δ'} ≅ M ⊗_B Ω^p_{P/A,δ'}`, `(f ⊗ m) ⊗ ω ↦ m ⊗ f ω`. -/
def polyCancel (p : ℕ) :
    (setIndexedDividedPowerPolynomialAlgebra B W ⊗[(B : Type u)] M) ⊗[
        setIndexedDividedPowerPolynomialAlgebra B W] dividedPowerPolynomialForms A B W p ≃+
      M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W p :=
  ((TensorProduct.comm (setIndexedDividedPowerPolynomialAlgebra B W) _ _).toAddEquiv.trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (B : Type u)
      (setIndexedDividedPowerPolynomialAlgebra B W) (setIndexedDividedPowerPolynomialAlgebra B W)
      (dividedPowerPolynomialForms A B W p) M).toAddEquiv).trans
    (TensorProduct.comm (B : Type u) (dividedPowerPolynomialForms A B W p) M).toAddEquiv

/-- The cancellation on a pure tensor. -/
theorem polyCancel_tmul (p : ℕ) (f : setIndexedDividedPowerPolynomialAlgebra B W) (m : M)
    (x : dividedPowerPolynomialForms A B W p) :
    polyCancel A B W M p ((f ⊗ₜ[(B : Type u)] m) ⊗ₜ x) = m ⊗ₜ (f • x) :=
  rfl

/-- The inverse of the cancellation on a pure tensor. -/
theorem polyCancel_symm_tmul (p : ℕ) (m : M) (x : dividedPowerPolynomialForms A B W p) :
    (polyCancel A B W M p).symm (m ⊗ₜ x) =
      ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type u)] m) ⊗ₜ x :=
  rfl

/-- The terms of the target complex, with the base change cancelled. -/
def polyTermEquiv (p : ℕ) :
    polyTargetTerm A B W M p ≃+ M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W p :=
  (RestrictScalars.addEquiv A (setIndexedDividedPowerPolynomialAlgebra B W) _).trans
    (polyCancel A B W M p)

/-- The terms of the source complex, without the restriction of scalars. -/
def baseTermEquiv (p : ℕ) :
    oneVariableSourceTerm A B M p ≃+
      M ⊗[(B : Type u)] dividedPowerDifferentialForms (A := A) B.dividedPowers p :=
  RestrictScalars.addEquiv A (B : Type u) _

end Cancel

/-! ### The two complexes, with the base change cancelled -/

section Formulas

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B] (W : Type u)
  {M : Type w} [AddCommGroup M] [Module (B : Type u) M]

/-- Wedging a one-form of `B`, read in `P` through `ψ`, with a fixed `p`-form of `P`:
`η ↦ ψ η ∧ ω`, as a `B`-linear map `Ω¹_{B/A,δ} → Ω^{p+1}_{P/A,δ'}`. -/
def polyWedgeOne (p : ℕ) (omega : dividedPowerPolynomialForms A B W p) :
    dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerPolynomialForms A B W (p + 1) :=
  ((dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) p omega).restrictScalars
      (B : Type u)) ∘ₗ coefficientFormsMap A B W 1 ∘ₗ
    (exteriorPower.oneEquiv (B : Type u)
      (dividedPowerDifferentials (A := A) B.dividedPowers)).symm.toLinearMap


/-- The comparison of forms in degree one is the comparison of one-forms. -/
theorem oneEquiv_coefficientFormsMap (eta : dividedPowerDifferentials (A := A) B.dividedPowers) :
    exteriorPower.oneEquiv (setIndexedDividedPowerPolynomialAlgebra B W) _
        (coefficientFormsMap A B W 1
          ((exteriorPower.oneEquiv (B : Type u) _).symm eta)) =
      oneFormComparison A B W eta := by
  rw [exteriorPower.oneEquiv_symm_apply, coefficientFormsMap_ιMulti_oneFormComparison,
    exteriorPower.oneEquiv_ιMulti, Function.comp_apply]

/-- `ψ η ∧ ω`, written with the one-form `ψ η` itself. -/
theorem polyWedgeOne_apply (p : ℕ) (omega : dividedPowerPolynomialForms A B W p)
    (eta : dividedPowerDifferentials (A := A) B.dividedPowers) :
    polyWedgeOne A B W p omega eta = leftWedge p (oneFormComparison A B W eta) omega := by
  simp only [polyWedgeOne, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe]
  rw [dividedPowerWedge_apply]
  exact congrArg (fun y ↦ leftWedge p y omega) (oneEquiv_coefficientFormsMap A B W eta)


/-- **The canonical map, read with the base change cancelled, is `1_M ⊗ ψ`.** -/
theorem polyTermEquiv_polyComparison
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (p : ℕ) (y : M ⊗[(B : Type u)] dividedPowerDifferentialForms (A := A) B.dividedPowers p) :
    polyTermEquiv A B W M p (polyComparison A B W nabla hint p ((baseTermEquiv A B M p).symm y)) =
      LinearMap.lTensor M (coefficientFormsMap A B W p) y := by
  let F : M ⊗[(B : Type u)] dividedPowerDifferentialForms (A := A) B.dividedPowers p →+
      M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W p :=
    (polyTermEquiv A B W M p).toAddMonoidHom.comp
      ((polyComparison A B W nabla hint p).toAddMonoidHom.comp
        (baseTermEquiv A B M p).symm.toAddMonoidHom)
  let G : M ⊗[(B : Type u)] dividedPowerDifferentialForms (A := A) B.dividedPowers p →+
      M ⊗[(B : Type u)] dividedPowerPolynomialForms A B W p :=
    (LinearMap.lTensor M (coefficientFormsMap A B W p)).toAddMonoidHom
  have hgen : ∀ (m : M) (omega : Fin p → dividedPowerDifferentials (A := A) B.dividedPowers),
      F (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p omega) =
        G (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p omega) := by
    intro m omega
    calc F (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p omega)
        = polyCancel A B W M p
            (((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type u)] m) ⊗ₜ[
            setIndexedDividedPowerPolynomialAlgebra B W]
            exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) p
              (oneFormComparison A B W ∘ omega)) :=
            congrArg (polyTermEquiv A B W M p) (polyComparison_ιMulti A B W nabla hint p m omega)
      _ = m ⊗ₜ[(B : Type u)] ((1 : setIndexedDividedPowerPolynomialAlgebra B W) •
            exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) p
              (oneFormComparison A B W ∘ omega)) := polyCancel_tmul A B W M p _ _ _
      _ = m ⊗ₜ[(B : Type u)]
            coefficientFormsMap A B W p (exteriorPower.ιMulti (B : Type u) p omega) :=
            congrArg (m ⊗ₜ[(B : Type u)] ·) ((one_smul _ _).trans
              (coefficientFormsMap_ιMulti_oneFormComparison A B W p omega).symm)
      _ = G (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p omega) :=
            (LinearMap.lTensor_tmul _ _ _ _).symm
  have hspan : ∀ eta : dividedPowerDifferentialForms (A := A) B.dividedPowers p, ∀ m : M,
      F (m ⊗ₜ[(B : Type u)] eta) = G (m ⊗ₜ[(B : Type u)] eta) := by
    intro eta
    have hmem : eta ∈ Submodule.span (B : Type u)
        (Set.range (exteriorPower.ιMulti (B : Type u) p :
          (Fin p → dividedPowerDifferentials (A := A) B.dividedPowers) →
            dividedPowerDifferentialForms (A := A) B.dividedPowers p)) := by
      rw [exteriorPower.ιMulti_span]
      exact Submodule.mem_top
    induction hmem using Submodule.span_induction with
    | mem eta heta =>
      obtain ⟨omega, rfl⟩ := heta
      exact fun m ↦ hgen m omega
    | zero =>
      intro m
      simp only [TensorProduct.tmul_zero, map_zero]
    | add x y _ _ hx hy =>
      intro m
      simp only [TensorProduct.tmul_add, map_add, hx m, hy m]
    | smul b x _ hx =>
      intro m
      rw [← TensorProduct.smul_tmul]
      exact hx (b • m)
  suffices hFG : ∀ y, F y = G y from hFG y
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact (map_zero F).trans (map_zero G).symm
  | add a b ha hb =>
    exact (map_add F a b).trans ((congrArg₂ (· + ·) ha hb).trans (map_add G a b).symm)
  | tmul m eta => exact hspan eta m

/-- The base change of a connection, evaluated at `1 ⊗ m`, is `(1 ⊗ −) ⊗ ψ` of `∇ m`. -/
theorem polyBaseChangeConnection_one_tmul
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M) (m : M) :
    polyBaseChangeConnection A B W nabla
        ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[(B : Type u)] m) =
      Connection.baseChangeValues (oneFormComparison A B W) (nabla m) := by
  rw [polyBaseChangeConnection, Connection.baseChange_tmul, one_smul,
    Derivation.map_one_eq_zero, map_zero, TensorProduct.tmul_zero, add_zero]


end Formulas

end DividedPowerPolynomial

end Crystalline

end
