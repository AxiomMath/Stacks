module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.Connection

/-!
# Transport of a connection along an isomorphism of the one-forms

Let `A → B` be a map of commutative rings and let `π : Ω[B⁄A] → Ω`, `π' : Ω[B⁄A] → Ω'` be two
presentations of modules of one-forms which differ by an isomorphism `e : Ω ≅ Ω'` of `B`-modules,
`e ∘ π = π'`.  A connection `∇ : M → M ⊗_B Ω` relative to `π` becomes the connection
`(1 ⊗ e) ∘ ∇ : M → M ⊗_B Ω'` relative to `π'` (`Crystalline.Connection.transport`).

The extensions of the two connections to differential forms correspond under `1 ⊗ ⋀ e`
(`Crystalline.Connection.extendedConnection_transport`), and the transported connection of an
integrable connection is integrable (`Crystalline.Connection.IsIntegrable.transport`).

## Main definitions

* `Crystalline.Connection.transport` — the connection `(1 ⊗ e) ∘ ∇` relative to `π' = e ∘ π`.

## Main results

* `Crystalline.Connection.descendedDifferential_transport` — the descended de Rham differentials
  correspond under `⋀ e`.
* `Crystalline.Connection.extendedConnection_transport` — the extended connections correspond
  under `1 ⊗ ⋀ e`.
* `Crystalline.Connection.IsIntegrable.transport` — integrability is preserved.

## References

* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Stacks.DeRham.DifferentialDescent

universe u v

namespace Crystalline

section LeftWedge

variable {B Omega Omega' : Type*} [CommRing B] [AddCommGroup Omega] [Module B Omega]
  [AddCommGroup Omega'] [Module B Omega']

/-- **Left exterior multiplication commutes with the exterior powers of a linear map**:
`f η ∧ (⋀^p f) ω = (⋀^{p+1} f) (η ∧ ω)`. -/
theorem leftWedge_exteriorPowerMap (f : Omega →ₗ[B] Omega') (p : ℕ) (η : Omega)
    (ω : ⋀[B]^p Omega) :
    leftWedge p (f η) (exteriorPower.map p f ω) =
      exteriorPower.map (p + 1) f (leftWedge p η ω) := by
  have key : ∀ ω ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B p (M := Omega))),
      leftWedge p (f η) (exteriorPower.map p f ω) =
        exteriorPower.map (p + 1) f (leftWedge p η ω) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [exteriorPower.map_apply_ιMulti, leftWedge_ιMulti, leftWedge_ιMulti,
        exteriorPower.map_apply_ιMulti]
      congr 1
      funext i
      cases i using Fin.cases <;> rfl
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul c x _ hx => simp only [map_smul, hx]
  exact key ω (by rw [exteriorPower.ιMulti_span]; trivial)

end LeftWedge

namespace Connection

variable {A B Omega Omega' : Type u} {M : Type v}
  [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup Omega] [Module B Omega] [AddCommGroup Omega'] [Module B Omega']
  [AddCommGroup M] [Module B M]
  {pi : Ω[B⁄A] →ₗ[B] Omega} {pi' : Ω[B⁄A] →ₗ[B] Omega'}

/-- **The transport of a connection along an isomorphism of the one-forms**: for `e : Ω ≅ Ω'`
with `e ∘ π = π'`, the connection `(1 ⊗ e) ∘ ∇` relative to `π'`. -/
def transport (nabla : Connection A B pi M) (e : Omega ≃ₗ[B] Omega')
    (he : ∀ x, e (pi x) = pi' x) : Connection A B pi' M where
  toAddMonoidHom :=
    (TensorProduct.map LinearMap.id e.toLinearMap).toAddMonoidHom.comp nabla.toAddMonoidHom
  leibniz' b m := by
    change TensorProduct.map LinearMap.id e.toLinearMap (nabla (b • m)) =
      b • TensorProduct.map LinearMap.id e.toLinearMap (nabla m) +
        m ⊗ₜ[B] pi' (KaehlerDifferential.D A B b)
    rw [nabla.leibniz, _root_.map_add, map_smul, TensorProduct.map_tmul, LinearMap.id_apply,
      LinearEquiv.coe_coe, he]

/-- The value of the transported connection. -/
theorem transport_apply (nabla : Connection A B pi M) (e : Omega ≃ₗ[B] Omega')
    (he : ∀ x, e (pi x) = pi' x) (m : M) :
    nabla.transport e he m = TensorProduct.map LinearMap.id e.toLinearMap (nabla m) := rfl

/-- **The descended de Rham differentials of two presentations differing by an isomorphism `e`
correspond under `⋀ e`.** -/
theorem descendedDifferential_transport (S : SourceDeRham A B) (hpi : Function.Surjective pi)
    (dΩ : ∀ p, TgtA A B Omega p →ₗ[A] TgtA A B Omega (p + 1))
    (dΩ' : ∀ p, TgtA A B Omega' p →ₗ[A] TgtA A B Omega' (p + 1))
    (hc : S.Commutes pi dΩ) (hc' : S.Commutes pi' dΩ')
    (e : Omega ≃ₗ[B] Omega') (he : ∀ x, e (pi x) = pi' x) (p : ℕ) (ω : ⋀[B]^p Omega) :
    descendedDifferential dΩ' p (exteriorPower.map p e.toLinearMap ω) =
      exteriorPower.map (p + 1) e.toLinearMap (descendedDifferential dΩ p ω) := by
  have hcomp : e.toLinearMap ∘ₗ pi = pi' := LinearMap.ext he
  obtain ⟨x, rfl⟩ := exteriorPower.map_surjective (n := p) hpi ω
  rw [descendedDifferential_commutes S pi dΩ hc, ← LinearMap.comp_apply
    (exteriorPower.map p e.toLinearMap), ← exteriorPower.map_comp, hcomp,
    descendedDifferential_commutes S pi' dΩ' hc', ← hcomp, exteriorPower.map_comp,
    LinearMap.comp_apply]

variable (S : SourceDeRham A B) (hpi : Function.Surjective pi)
  (hgen : S.GenerationHypothesis pi) (hpi' : Function.Surjective pi')
  (hgen' : S.GenerationHypothesis pi') (nabla : Connection A B pi M)
  (e : Omega ≃ₗ[B] Omega') (he : ∀ x, e (pi x) = pi' x)

/-- The wedge of the connection term with a form commutes with transport. -/
theorem map_leftWedge_transport (p : ℕ) (ω : ⋀[B]^p Omega) (z : M ⊗[B] Omega) :
    TensorProduct.map LinearMap.id ((leftWedge p).flip (exteriorPower.map p e.toLinearMap ω))
        (TensorProduct.map LinearMap.id e.toLinearMap z) =
      TensorProduct.map LinearMap.id (exteriorPower.map (p + 1) e.toLinearMap)
        (TensorProduct.map LinearMap.id ((leftWedge p).flip ω) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | tmul n η =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.flip_apply,
      LinearEquiv.coe_coe]
    rw [← LinearEquiv.coe_coe, leftWedge_exteriorPowerMap]
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

/-- **The extended connections of a connection and of its transport correspond under
`1 ⊗ ⋀ e`.** -/
theorem extendedConnection_transport (p : ℕ) (y : M ⊗[B] ⋀[B]^p Omega) :
    RestrictScalars.addEquiv A B _
        ((extendedConnection S pi' hpi' hgen' (nabla.transport e he)).toLinearMap p
          ((RestrictScalars.addEquiv A B _).symm
            (TensorProduct.map LinearMap.id (exteriorPower.map p e.toLinearMap) y))) =
      TensorProduct.map LinearMap.id (exteriorPower.map (p + 1) e.toLinearMap)
        (RestrictScalars.addEquiv A B _
          ((extendedConnection S pi hpi hgen nabla).toLinearMap p
            ((RestrictScalars.addEquiv A B _).symm y))) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | add x y hx hy => simp only [_root_.map_add, hx, hy]
  | tmul m ω =>
    have h1 := (extendedConnection S pi hpi hgen nabla).map_tmul p m ω
    have h2 := (extendedConnection S pi' hpi' hgen' (nabla.transport e he)).map_tmul p m
      (exteriorPower.map p e.toLinearMap ω)
    rw [TensorProduct.map_tmul, LinearMap.id_apply]
    show RestrictScalars.addEquiv A B _
        ((extendedConnection S pi' hpi' hgen' (nabla.transport e he)).toLinearMap p
          (m ⊗ₜ[B] exteriorPower.map p e.toLinearMap ω)) =
      TensorProduct.map LinearMap.id (exteriorPower.map (p + 1) e.toLinearMap)
        (RestrictScalars.addEquiv A B _
          ((extendedConnection S pi hpi hgen nabla).toLinearMap p (m ⊗ₜ[B] ω)))
    rw [h1, h2, _root_.map_add, TensorProduct.map_tmul, LinearMap.id_apply, transport_apply,
      map_leftWedge_transport, ← descendedDifferential_apply, ← descendedDifferential_apply,
      descendedDifferential_transport S hpi _ _
        (extendedConnection S pi hpi hgen nabla).commutes
        (extendedConnection S pi' hpi' hgen' (nabla.transport e he)).commutes e he]

/-- `(⋀^1)⁻¹` commutes with `e`. -/
theorem map_oneEquiv_symm_transport (z : M ⊗[B] Omega) :
    TensorProduct.map LinearMap.id (exteriorPower.oneEquiv B Omega').symm.toLinearMap
        (TensorProduct.map LinearMap.id e.toLinearMap z) =
      TensorProduct.map LinearMap.id (exteriorPower.map 1 e.toLinearMap)
        (TensorProduct.map LinearMap.id (exteriorPower.oneEquiv B Omega).symm.toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | tmul n η =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
      exteriorPower.oneEquiv_symm_apply, exteriorPower.map_apply_ιMulti]
    rfl
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

/-- **The transport of an integrable connection is integrable.** -/
theorem IsIntegrable.transport (h : IsIntegrable S pi hpi hgen nabla) :
    IsIntegrable S pi' hpi' hgen' (nabla.transport e he) := by
  refine isIntegrable_of_comp_eq_zero fun m ↦ ?_
  have h0 : (extendedConnection S pi hpi hgen nabla).toLinearMap 1
      ((RestrictScalars.addEquiv A B _).symm (TensorProduct.map LinearMap.id
        (exteriorPower.oneEquiv B Omega).symm.toLinearMap (nabla m))) = 0 :=
    h.comp_eq_zero m
  have key := extendedConnection_transport S hpi hgen hpi' hgen' nabla e he 1
    (TensorProduct.map LinearMap.id (exteriorPower.oneEquiv B Omega).symm.toLinearMap (nabla m))
  rw [h0, _root_.map_zero, _root_.map_zero, ← map_oneEquiv_symm_transport] at key
  exact (RestrictScalars.addEquiv A B _).injective (key.trans (_root_.map_zero _).symm)

end Connection

end Crystalline
