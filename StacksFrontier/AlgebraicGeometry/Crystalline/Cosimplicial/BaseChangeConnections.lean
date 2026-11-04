module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialStructurePair

/-!
# The connections of a cosimplicial module, by base change from the degree zero

Let `E` be a cosimplicial divided power algebra with completed rings `D(b)`, and `V` a
cosimplicial module over them with modules `M(b)`.  Suppose given a completed connection `∇` on
`M = M(0)`, and for every `b` an identification

`β_b : (D(b) ⊗_{D(0)} M)^∧ ≃ M(b)`

of `M(b)` with the base change of `M` along the coprojection `σ_b : ⦋0⦌ ⟶ ⦋b⦌` onto the vertex
`0`.  For the cosimplicial module `M(•)` of a crystal in quasi-coherent modules this is the
crystal property.

This module puts on each `M(b)` the connection obtained by base change of `∇` along `σ_b`,
`Crystalline.CompletedConnection.baseChange`, transported along `β_b`.  This is the only
connection on `M(b)` for which `β_b` is horizontal.

## Main definitions

* `Crystalline.CosimplicialDPAlgebra.coprojection` — the coprojection `σ_b : ⦋0⦌ ⟶ ⦋b⦌`.
* `Crystalline.CosimplicialDPAlgebra.coprojectionAlgebra` — `D(b)` as a `D(0)`-algebra along
  `σ_b`.
* `Crystalline.CosimplicialDPAlgebra.coprojectionConnection` — the base-changed connection of
  `∇` on `(D(b) ⊗_{D(0)} M)^∧`.
* `Crystalline.CosimplicialCompletedModule.baseChangeConnection` — **the connection on `M(b)`**,
  the transport of the previous one along `β_b`.

## Main results

* `Crystalline.CosimplicialCompletedModule.baseChangeConnection_apply` — its value at `β_b x`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Remark 60.17.6, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Simplicial

namespace Crystalline

namespace CosimplicialDPAlgebra

variable {A : Type u} [CommRing A] (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ)

/-- **The coprojection `σ_b : ⦋0⦌ ⟶ ⦋b⦌` onto the vertex `0`.** -/
abbrev coprojection (b : ℕ) : (⦋0⦌ : SimplexCategory) ⟶ ⦋b⦌ :=
  SimplexCategory.const ⦋0⦌ ⦋b⦌ 0

/-- **`D(b)` as a `D(0)`-algebra along the coprojection `σ_b`.** -/
abbrev coprojectionAlgebra (b : ℕ) : Algebra (E.completedRing p 0) (E.completedRing p b) :=
  (E.completedRingMap p (coprojection b)).toAlgebra

/-- The forms map `Ω^1_{D(0)} → Ω^1_{D(b)}` of the coprojection, semilinear over the algebra map
of `Crystalline.CosimplicialDPAlgebra.coprojectionAlgebra`. -/
def coprojectionFormsMap (b a : ℕ) :
    letI := E.coprojectionAlgebra p b
    E.forms p a 0 →ₛₗ[algebraMap (E.completedRing p 0) (E.completedRing p b)] E.forms p a b :=
  E.formsMapCompleted p (coprojection b) a

/-- The forms map of the coprojection carries the universal differential to the universal
differential. -/
theorem coprojectionFormsMap_differential (b : ℕ) (x : E.completedRing p 0) :
    letI := E.coprojectionAlgebra p b
    E.coprojectionFormsMap p b 1 (E.differential p 0 x) =
      E.differential p b (algebraMap (E.completedRing p 0) (E.completedRing p b) x) :=
  E.formsMap_differential p (coprojection b) x

/-- **The base change of a completed connection on `M(0)` along the coprojection `σ_b`**, a
completed connection on `(D(b) ⊗_{D(0)} M(0))^∧` with values in `Ω^1_{D(b)}`. -/
def coprojectionConnection (b : ℕ) {M : Type w} [AddCommGroup M] [Module (E.completedRing p 0) M]
    (nabla : CompletedConnection p (E.completedRing p 0) (E.forms p 1 0) (E.differential p 0) M) :
    letI := E.coprojectionAlgebra p b
    CompletedConnection p (E.completedRing p b) (E.forms p 1 b) (E.differential p b)
      (CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b) M) :=
  letI := E.coprojectionAlgebra p b
  CompletedConnection.baseChange p (E.completedRing p 0) (E.completedRing p b) M
    (E.forms p 1 0) (E.forms p 1 b) (E.differential p b) (E.coprojectionFormsMap p b 1) nabla
    (E.differential_add p b) (E.differential_mul p b) (E.coprojectionFormsMap_differential p b)

end CosimplicialDPAlgebra

namespace CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (V : CosimplicialCompletedModule.{u, v, v} E p)
  (nabla : CompletedConnection p (E.completedRing p 0) (E.forms p 1 0) (E.differential p 0)
    (V.carrier 0))
  (beta : ∀ b : ℕ, letI := E.coprojectionAlgebra p b
    CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
      (V.carrier 0) ≃ₗ[E.completedRing p b] V.carrier b)

/-- **The connection on `M(b)` obtained from `∇` on `M(0)` by base change along the coprojection
`σ_b`**, read through the identification `β_b : (D(b) ⊗_{D(0)} M(0))^∧ ≃ M(b)`. -/
def baseChangeConnection (b : ℕ) :
    CompletedConnection p (E.completedRing p b) (E.forms p 1 b) (E.differential p b)
      (V.carrier b) :=
  letI := E.coprojectionAlgebra p b
  CompletedDeRham.transportConnection p (RingEquiv.refl (E.completedRing p b))
    (beta b).toLinearMap (beta b).symm.toLinearMap (fun _ => LinearMap.id)
    (E.differential p b) (E.differential p b) (E.coprojectionConnection p b nabla)
    (fun m => (beta b).apply_symm_apply m) (fun _ => rfl)

/-- **The value of the base-change connection at `β_b x`** is the image of the base-changed
connection at `x`. -/
theorem baseChangeConnection_apply (b : ℕ)
    (x : letI := E.coprojectionAlgebra p b
      CompletedConnection.baseChangeCarrier p (E.completedRing p 0) (E.completedRing p b)
        (V.carrier 0)) :
    letI := E.coprojectionAlgebra p b
    V.baseChangeConnection nabla beta b (beta b x) =
      CompletedDeRham.isoValuesFwd p (RingEquiv.refl (E.completedRing p b)) (beta b).toLinearMap
        (fun _ => LinearMap.id) 1 (E.coprojectionConnection p b nabla x) :=
  let := E.coprojectionAlgebra p b
  CompletedDeRham.transportConnection_apply p (RingEquiv.refl (E.completedRing p b))
    (beta b).toLinearMap (beta b).symm.toLinearMap (fun _ => LinearMap.id)
    (E.differential p b) (E.differential p b) (E.coprojectionConnection p b nabla)
    (fun m => (beta b).symm_apply_apply m) (fun m => (beta b).apply_symm_apply m) (fun _ => rfl) x

end CosimplicialCompletedModule

end Crystalline

end
