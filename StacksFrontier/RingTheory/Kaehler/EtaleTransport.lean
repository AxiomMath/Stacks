module

public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Transport of a map out of the module of differentials along an étale square

Let `R₁ → R₂` and `A₁ → A₂` be ring maps, with `A₂` an algebra over both `A₁` and `R₂` and the
two routes `R₁ → A₁ → A₂` and `R₁ → R₂ → A₂` agreeing. Assume `A₂` is formally étale over `A₁`
and `R₂` is formally unramified over `R₁`. Then
```
A₂ ⊗_{A₁} Ω[A₁⁄R₁] ≅ Ω[A₂⁄R₁] ≅ Ω[A₂⁄R₂],
```
the first because a formally étale algebra extension is a base change for the module of
differentials, the second because a formally unramified base extension does not change the
differentials. Hence an `A₁`-linear map `Ω[A₁⁄R₁] →ₗ M` into an `A₂`-module extends to an
`A₂`-linear map `Ω[A₂⁄R₂] →ₗ M`.

## Main definitions

* `Stacks.KaehlerDifferential.baseEquiv`: the isomorphism `Ω[A₂⁄R₁] ≃ₗ[A₂] Ω[A₂⁄R₂]`.
* `Stacks.KaehlerDifferential.etaleTransport`: the extension of an `A₁`-linear map out of
  `Ω[A₁⁄R₁]` to an `A₂`-linear map out of `Ω[A₂⁄R₂]`.

## Main results

* `Stacks.KaehlerDifferential.baseEquiv_D`: the isomorphism carries the universal derivation over
  `R₁` to the universal derivation over `R₂`.
* `Stacks.KaehlerDifferential.etaleTransport_D`: the extension carries
  `d_{A₂/R₂}(algebraMap A₁ A₂ y)` to the value of the original map at `d_{A₁/R₁} y`.

## Implementation notes

The isomorphism `Ω[A₂⁄R₁] ≅ Ω[A₂⁄R₂]` is `KaehlerDifferential.map R₁ R₂ A₂ A₂`, surjective by
`KaehlerDifferential.map_surjective` and injective because the preceding term
`A₂ ⊗_{R₂} Ω[R₂⁄R₁]` of the Jacobi–Zariski sequence
`KaehlerDifferential.exact_mapBaseChange_map` vanishes: `Ω[R₂⁄R₁]` is a subsingleton, `R₂` being
formally unramified over `R₁`. Only formal unramifiedness of `R₂` is used, not formal étaleness.

The extension itself is `IsBaseChange.lift` against
`KaehlerDifferential.isBaseChange_of_formallyEtale`, so no tensor product is written out.

## References

* [Stacks Project, Tag 04BX](https://stacks.math.columbia.edu/tag/04BX)
-/

@[expose] public section

open TensorProduct

namespace Stacks.KaehlerDifferential

variable (R₁ R₂ A₁ A₂ : Type*) [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
  [Algebra R₁ R₂] [Algebra R₁ A₁] [Algebra R₁ A₂] [Algebra R₂ A₂] [Algebra A₁ A₂]
  [IsScalarTower R₁ A₁ A₂] [IsScalarTower R₁ R₂ A₂]

/-! ### A formally unramified base extension does not change the differentials -/

/-- **Differentials are insensitive to a formally unramified base extension.** For `R₂` formally
unramified over `R₁` and `A₂` an `R₂`-algebra, the canonical map `Ω[A₂⁄R₁] → Ω[A₂⁄R₂]` is an
isomorphism of `A₂`-modules. -/
noncomputable def baseEquiv [Algebra.FormallyUnramified R₁ R₂] :
    Ω[A₂⁄R₁] ≃ₗ[A₂] Ω[A₂⁄R₂] :=
  LinearEquiv.ofBijective (_root_.KaehlerDifferential.map R₁ R₂ A₂ A₂)
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ :=
        (_root_.KaehlerDifferential.exact_mapBaseChange_map R₁ R₂ A₂ x).mp hx
      rw [Subsingleton.elim y 0, map_zero],
      _root_.KaehlerDifferential.map_surjective R₁ R₂ A₂⟩

/-- `Stacks.KaehlerDifferential.baseEquiv` carries the universal derivation over `R₁` to the
universal derivation over `R₂`. -/
theorem baseEquiv_D [Algebra.FormallyUnramified R₁ R₂] (x : A₂) :
    baseEquiv R₁ R₂ A₂ (_root_.KaehlerDifferential.D R₁ A₂ x) =
      _root_.KaehlerDifferential.D R₂ A₂ x :=
  _root_.KaehlerDifferential.map_D R₁ R₂ A₂ A₂ x

/-! ### The transport along a formally étale algebra extension -/

variable {M : Type*} [AddCommGroup M] [Module A₁ M] [Module A₂ M] [IsScalarTower A₁ A₂ M]

/-- **The transport of a map out of the module of differentials along an étale square.** For `A₂`
formally étale over `A₁` and `R₂` formally unramified over `R₁`, an `A₁`-linear map
`θ : Ω[A₁⁄R₁] → M` into an `A₂`-module `M` extends to the `A₂`-linear map `Ω[A₂⁄R₂] → M`
obtained by identifying `Ω[A₂⁄R₂]` with `Ω[A₂⁄R₁]` and then with `A₂ ⊗_{A₁} Ω[A₁⁄R₁]`. -/
noncomputable def etaleTransport [Algebra.FormallyUnramified R₁ R₂]
    [Algebra.FormallyEtale A₁ A₂] (θ : Ω[A₁⁄R₁] →ₗ[A₁] M) : Ω[A₂⁄R₂] →ₗ[A₂] M :=
  (_root_.KaehlerDifferential.isBaseChange_of_formallyEtale R₁ A₁ A₂).lift θ ∘ₗ
    (baseEquiv R₁ R₂ A₂).symm.toLinearMap

/-- **The defining property of `Stacks.KaehlerDifferential.etaleTransport`.** On the differential
of an element coming from `A₁` the transport takes the value of the original map. -/
theorem etaleTransport_D [Algebra.FormallyUnramified R₁ R₂] [Algebra.FormallyEtale A₁ A₂]
    (θ : Ω[A₁⁄R₁] →ₗ[A₁] M) (y : A₁) :
    etaleTransport R₁ R₂ A₁ A₂ θ
        (_root_.KaehlerDifferential.D R₂ A₂ (algebraMap A₁ A₂ y)) =
      θ (_root_.KaehlerDifferential.D R₁ A₁ y) := by
  have hsymm : (baseEquiv R₁ R₂ A₂).symm
        (_root_.KaehlerDifferential.D R₂ A₂ (algebraMap A₁ A₂ y)) =
      _root_.KaehlerDifferential.D R₁ A₂ (algebraMap A₁ A₂ y) := by
    rw [LinearEquiv.symm_apply_eq, baseEquiv_D]
  rw [etaleTransport, LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm,
    ← _root_.KaehlerDifferential.map_D R₁ R₁ A₁ A₂ y]
  exact (_root_.KaehlerDifferential.isBaseChange_of_formallyEtale R₁ A₁ A₂).lift_eq θ _

end Stacks.KaehlerDifferential

end
