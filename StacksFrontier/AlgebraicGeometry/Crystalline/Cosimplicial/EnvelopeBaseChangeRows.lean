module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedBaseChangeTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BaseChangeConnectionsCurvature
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamRowRetraction
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeDegreePolynomial
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.CompletedPoincareCurvature

/-!
# The rows of the double complex of a cosimplicial envelope are quasi-isomorphic to the row zero

Let `D(•)` be the cosimplicial completed divided power envelope of a polynomial presentation
`P = A[x_i] → C`, `M(•)` a cosimplicial module over it, `∇` an integrable completed connection on
`M(0)`, and suppose `M(b)` is the completed base change of `M(0)` along the coprojection
`σ_b : ⦋0⦌ ⟶ ⦋b⦌` (`β_b : (D(b) ⊗_{D(0)} M(0))^∧ ≃ M(b)`), carrying the base-changed connection
`Crystalline.CosimplicialCompletedModule.baseChangeConnection`.

This module provides the pair, and the identifications of forms, on which the row half of the
proof of [Stacks, Proposition 60.21.3, Tag 07LG] rests: the
coprojection `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} ⟶ M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` is a quasi-isomorphism.
The source's argument is: `D(b)` is the completed divided power polynomial algebra
`D(0)⟨ξ_i(j)⟩^∧` over `D(0)` ([Stacks, Lemma 60.17.5, Tag 07L2], here
`Crystalline.envelopeDegreeCompletedRingEquiv`), the row is the base change of `M(0)` to it, and
[Stacks, Lemma 60.21.2, Tag 07LD]
(`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison`)
says that this base change is a quasi-isomorphism on de Rham complexes.  The base change is
compared with the form `M ⊗^∧_D Ω^*_{D'}` in which the library proves 07LD by
`Crystalline.baseChangePushedEquiv`.

## Main definitions and results

* `Crystalline.CosimplicialCompletedModule.baseChangePair` — the cosimplicial pair of a
  cosimplicial module with base-change connections, given the horizontality of the coface
  `⦋0⦌ ⟶ ⦋1⦌, 0 ↦ 1` and the integrability of `∇`.
* `Crystalline.envelopeDegreeFormsMapₛₗ`, `Crystalline.envelopeDegreeFormsInvₛₗ` — the
  identification of the forms of `D(b)` with those of `D(0)⟨ξ⟩^∧`, as mutually inverse semilinear
  maps over `Crystalline.envelopeDegreeCompletedRingEquiv`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Lemma 60.17.5, Tag 07L2](https://stacks.math.columbia.edu/tag/07L2)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Simplicial DividedPowers
open scoped TensorProduct

namespace Crystalline

namespace CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, u} A} {p : ℕ}
  (V : CosimplicialCompletedModule.{u, u, u} E p)
  (nabla : CompletedConnection p (E.completedRing p 0) (E.forms p 1 0) (E.differential p 0)
    (V.carrier 0))
  (beta : ∀ b : ℕ, letI := E.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
      (V.carrier 0) ≃ₗ[E.completedRing p b] V.carrier b)
  (hbeta : ∀ (b : ℕ) (x : E.completedRing p b) (m : V.carrier 0),
    letI := E.coprojectionAlgebra p b
    beta b (AdicCompletion.of (pAdicIdeal (A := E.completedRing p b) p)
        (E.completedRing p b ⊗[E.completedRing p 0] V.carrier 0) (x ⊗ₜ[E.completedRing p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)
  (hδ : ∀ x : V.carrier 0,
    V.baseChangeConnection nabla beta 1 (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) x) =
      V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1 (nabla x))
  (hint : CompletedDeRham.HasIntegrableConnection p (E.completedRing p 0)
    (fun a => E.forms p a 0) (E.wedge p 0) (E.deRham p 0) (V.carrier 0) nabla
    (E.isGradedLeibniz p 0))

/-- **The cosimplicial pair of base-change connections**: `M(•)` with the connection of each
degree the base change of `∇` along the coprojection.  Its compatibility with the cosimplicial
direction is `Crystalline.CosimplicialCompletedModule.baseChangeConnection_map_of_horizontal`, and
its square-zero condition
`Crystalline.CosimplicialCompletedModule.isSquareZero_baseChangeConnection`.
-/
def baseChangePair : CosimplicialCompletedPair.{u, u, u} E p where
  toCosimplicialCompletedModule := V
  nabla := V.baseChangeConnection nabla beta
  nabla_tensorMap φ x := V.baseChangeConnection_map_of_horizontal nabla beta hbeta hδ φ x
  isSquareZero := V.isSquareZero_baseChangeConnection nabla beta hbeta hint

/-- The underlying cosimplicial module of `baseChangePair` is `V`. -/
theorem baseChangePair_toCosimplicialCompletedModule :
    (V.baseChangePair nabla beta hbeta hδ hint).toCosimplicialCompletedModule = V := rfl

/-- The connection of `baseChangePair` in degree `b` is the base change of `∇` along the
coprojection `⦋0⦌ ⟶ ⦋b⦌`. -/
theorem baseChangePair_nabla (b : ℕ) :
    (V.baseChangePair nabla beta hbeta hδ hint).nabla b = V.baseChangeConnection nabla beta b :=
  rfl

end CosimplicialCompletedModule

/-! ### The rows of the cosimplicial envelope of a presentation -/

section Envelope

variable (s : AffineCrystallineSituation.{u, u}) {ι : Type u}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

attribute [local instance] tensorPowerEnvelopeAlgebraInstance

/-- **`D(0)⟨ξ⟩^∧` as a `D(0)`-algebra** along the completed coefficient inclusion. -/
abbrev envelopeCoefficientAlgebra (b : ℕ) :
    Algebra (completedDividedPowerRing s.p (B := (tensorPowerEnvelope s f 0).object))
      (DividedPowerPolynomial.completedDividedPowerPolynomialRing
        (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p) :=
  (DividedPowerPolynomial.completedCoefficientRingHom s.A (tensorPowerEnvelope s f 0).object
    (ι × Fin b) s.p).toAlgebra

/-- The `D(0)`-action on the forms of `D(0)⟨ξ⟩^∧` is the action through the coefficient
inclusion. -/
theorem envelopeCoefficient_isScalarTower (b i : ℕ) :
    letI := envelopeCoefficientAlgebra s f b
    IsScalarTower (completedDividedPowerRing s.p (B := (tensorPowerEnvelope s f 0).object))
      (DividedPowerPolynomial.completedDividedPowerPolynomialRing
        (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p)
      (DividedPowerPolynomial.completedPolynomialForms s.A (tensorPowerEnvelope s f 0).object
        (ι × Fin b) s.p i) :=
  let := envelopeCoefficientAlgebra s f b
  ⟨fun x y z => mul_smul (DividedPowerPolynomial.completedCoefficientRingHom s.A
    (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p x) y z⟩

/-- The identification of the forms of `D(b)` with those of `D(0)⟨ξ⟩^∧`, as a semilinear map. -/
def envelopeDegreeFormsMapₛₗ (b i : ℕ) :
    (envelopeDPAlgebra s f).forms s.p i b →ₛₗ[(envelopeDegreeCompletedRingEquiv s f b :
      (envelopeDPAlgebra s f).completedRing s.p b →+*
        DividedPowerPolynomial.completedDividedPowerPolynomialRing
          (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p)]
      DividedPowerPolynomial.completedPolynomialForms s.A (tensorPowerEnvelope s f 0).object
        (ι × Fin b) s.p i where
  toFun := envelopeDegreeFormsEquiv s f b i
  map_add' := map_add _
  map_smul' := envelopeDegreeFormsEquiv_smul s f b i

/-- **The inverse identification of the forms is semilinear over the inverse identification of
the rings.** -/
theorem envelopeDegreeFormsEquiv_symm_smul (b a : ℕ)
    (r : DividedPowerPolynomial.completedDividedPowerPolynomialRing
      (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p)
    (y : DividedPowerPolynomial.completedPolynomialForms s.A (tensorPowerEnvelope s f 0).object
      (ι × Fin b) s.p a) :
    (envelopeDegreeFormsEquiv s f b a).symm (r • y) =
      (envelopeDegreeCompletedRingEquiv s f b).symm r • (envelopeDegreeFormsEquiv s f b a).symm y :=
  (envelopeDegreeFormsEquiv_symm_apply s f b a (r • y)).trans
    ((adicCompletionMapₛₗ_smul _ _ r y).trans
      (congrArg ((envelopeDegreeCompletedRingEquiv s f b).symm r • ·)
        (envelopeDegreeFormsEquiv_symm_apply s f b a y).symm))

/-- Its inverse, as a semilinear map. -/
def envelopeDegreeFormsInvₛₗ (b i : ℕ) :
    DividedPowerPolynomial.completedPolynomialForms s.A (tensorPowerEnvelope s f 0).object
        (ι × Fin b) s.p i →ₛₗ[((envelopeDegreeCompletedRingEquiv s f b).symm :
      DividedPowerPolynomial.completedDividedPowerPolynomialRing
          (tensorPowerEnvelope s f 0).object (ι × Fin b) s.p →+*
        (envelopeDPAlgebra s f).completedRing s.p b)]
      (envelopeDPAlgebra s f).forms s.p i b where
  toFun := (envelopeDegreeFormsEquiv s f b i).symm
  map_add' := map_add _
  map_smul' r y := envelopeDegreeFormsEquiv_symm_smul s f b i r y

end Envelope

end Crystalline

end
