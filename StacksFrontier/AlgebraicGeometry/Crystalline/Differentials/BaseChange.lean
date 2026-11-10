module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham

/-!
# Base change of a connection and of its de Rham complex

Let `A → B` and `A' → B'` sit in a commutative square of rings, with `B'` an algebra over both `B`
and `A'`, and let `ψ : Ω → Ω'` be a map of the two quotient modules of Kähler differentials that is
semilinear over `B → B'` and compatible with the quotient maps, i.e.

`ψ (π (d b)) = π' (d (b mod B'))` for all `b : B`.

A connection `∇` on a `B`-module `M` then base-changes to a connection on `B' ⊗[B] M`, whose value
on a pure tensor is

`∇' (b' ⊗ m) = b' · (ψ ∘ ∇) m + (1 ⊗ m) ⊗ π' (d b')`,

the sum of the base-changed old connection and the differential of the new scalar.  The second term
is what makes `∇'` satisfy the Leibniz rule over `B'`; since a connection is additive and not
linear, `∇'` has to be produced from a balanced biadditive map rather than from a tensor-product
lift of linear maps.

Base change preserves integrability, and it induces a canonical degreewise map

`M ⊗[B] ⋀^p Ω → (B' ⊗[B] M) ⊗[B'] ⋀^p Ω'`

of the two de Rham complexes, uniquely determined by its value `m ⊗ (ω₁ ∧ ⋯ ∧ ω_p) ↦
(1 ⊗ m) ⊗ (ψ ω₁ ∧ ⋯ ∧ ψ ω_p)` on pure wedges.  That the map commutes with the extended
differentials comes down to three compatibilities: `ψ ∘ π = π' ∘ Ω(B/A → B'/A')`, which holds
because both sides are `B`-linear and agree on the generators `d b`; the commutation of `⋀^p ψ`
with the two de Rham differentials of the rings themselves; and the defining formula for the
extension of a connection.  Integrability after base change then follows from the degree-one case
of that commutation, together with the computation that the curvature of `∇'` on `b' • n` differs
from `b'` times the curvature on `n` by the two-form `π' (d b') ∧ π' (d b')`, which vanishes.

## Main definitions

* `Crystalline.Connection.baseChangeInclusion` — the semilinear inclusion `m ↦ 1 ⊗ m`.
* `Crystalline.Connection.baseChangeValues` — the map induced on the values of a connection.
* `Crystalline.Connection.baseChange` — the base change of a connection.

## Main results

* `Crystalline.Connection.baseChange_tmul` — the defining formula on pure tensors.
* `Crystalline.baseChange_isIntegrable` — base change preserves integrability.
* `Crystalline.existsUnique_baseChangeDeRhamMap` — the canonical map of de Rham complexes, with
  its characterisation on pure wedges and its commutation with the differentials.

## Implementation notes

We use the canonically isomorphic presentation `B' ⊗[B] M` of the source's `M ⊗[B] B'`, and
`(B' ⊗[B] M) ⊗[B'] ⋀^p Ω'` for the base-changed forms; that order of the factors carries Mathlib's
standard `B'`-module structure directly.

## References

* [Stacks Project, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
* [Stacks Project, Tag 07PY](https://stacks.math.columbia.edu/tag/07PY)
-/

@[expose] public section

namespace Crystalline

/-! ### Base change of a connection -/

section BaseChangeConnection

open scoped TensorProduct

namespace Connection

variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
  {Omega : Type*} [AddCommGroup Omega] [Module B Omega]
  {Omega' : Type*} [AddCommGroup Omega'] [Module B' Omega']
  {pi : Ω[B⁄A] →ₗ[B] Omega} {pi' : Ω[B'⁄A'] →ₗ[B'] Omega'}
  (psi : Omega →ₛₗ[algebraMap B B'] Omega')
  {M : Type*} [AddCommGroup M] [Module B M]

/-- The semilinear inclusion of a module into its extension of scalars. -/
public def baseChangeInclusion : M →ₛₗ[algebraMap B B'] (B' ⊗[B] M) where
  toFun m := 1 ⊗ₜ[B] m
  map_add' m n := TensorProduct.tmul_add _ _ _
  map_smul' b m := by rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul]

/-- Apply the scalar-extension maps to both factors of a tensor occurring as a value of a
connection. -/
public def baseChangeValues : (M ⊗[B] Omega) →+ ((B' ⊗[B] M) ⊗[B'] Omega') :=
  (TensorProduct.map (baseChangeInclusion (B' := B') (M := M)) psi).toAddMonoidHom

@[simp]
public theorem baseChangeValues_tmul (m : M) (omega : Omega) :
    baseChangeValues psi (m ⊗ₜ[B] omega) = (1 ⊗ₜ[B] m) ⊗ₜ[B'] psi omega :=
  TensorProduct.map_tmul _ _ _ _

public theorem baseChangeValues_smul (b : B) (x : M ⊗[B] Omega) :
    baseChangeValues psi (b • x) = algebraMap B B' b • baseChangeValues psi x :=
  (TensorProduct.map (baseChangeInclusion (B' := B') (M := M)) psi).map_smulₛₗ b x

/-- The balanced biadditive formula whose lift is the base-changed connection. -/
public noncomputable def baseChangePair (nabla : Connection A B pi M) :
    B' →+ M →+ ((B' ⊗[B] M) ⊗[B'] Omega') where
  toFun b' := {
    toFun := fun m ↦
      b' • baseChangeValues psi (nabla m) +
        (1 ⊗ₜ[B] m) ⊗ₜ[B'] pi' (KaehlerDifferential.D A' B' b')
    map_zero' := by simp [baseChangeValues]
    map_add' := by
      intro m n
      rw [nabla.map_add, _root_.map_add, smul_add, TensorProduct.tmul_add,
        TensorProduct.add_tmul]
      abel }
  map_zero' := by ext m; simp [baseChangeValues]
  map_add' b c := by
    apply AddMonoidHom.ext; intro m
    simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_smul,
      _root_.map_add, TensorProduct.tmul_add]
    abel

omit [Algebra A A'] [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B']
  [SMulCommClass A' B B'] in
public theorem baseChangePair_balanced (nabla : Connection A B pi M)
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b))) :
    ∀ (b : B) (b' : B') (m : M),
      (baseChangePair (A' := A') (pi' := pi') psi nabla) (b • b') m =
        (baseChangePair (A' := A') (pi' := pi') psi nabla) b' (b • m) := by
  intro b b' m
  simp only [baseChangePair, _root_.map_add, Connection.leibniz, baseChangeValues_tmul,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  simp only [Algebra.smul_def]
  rw [Derivation.leibniz, _root_.map_add, _root_.map_smul, hpsi]
  simp only [_root_.map_smul, smul_add, mul_smul, TensorProduct.smul_tmul',
    IsScalarTower.algebraMap_smul, baseChangeValues_smul, TensorProduct.tmul_add,
    TensorProduct.tmul_smul]
  simp only [smul_eq_mul, mul_one]; rw [smul_comm b b']; abel

/-- Base change of a connection through a compatible commutative square of rings and modules of
differentials. -/
@[stacks 07KJ "base_change_connection"]
public noncomputable def baseChange (nabla : Connection A B pi M)
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b))) :
    Connection A' B' pi' (B' ⊗[B] M) where
  toAddMonoidHom :=
    TensorProduct.liftAddHom (baseChangePair (A' := A') (pi' := pi') psi nabla)
      (baseChangePair_balanced psi nabla hpsi)
  leibniz' := by
    intro b' x; induction x using TensorProduct.inductionOn with
    | tmul c m =>
      simp only [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul]
      change ((baseChangePair (A' := A') (pi' := pi') psi nabla) (b' * c)) m = _
      simp only [baseChangePair, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [Derivation.leibniz, _root_.map_add, _root_.map_smul, _root_.map_smul]
      simp only [smul_add, mul_smul, TensorProduct.tmul_add, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
      simp only [smul_eq_mul, mul_one]; abel
    | add x y hx hy =>
      rw [smul_add, _root_.map_add, hx, hy, _root_.map_add, TensorProduct.add_tmul,
        smul_add]
      abel

omit [Algebra A A'] [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B']
  [SMulCommClass A' B B'] in
/-- The defining formula for the base-changed connection on pure tensors. -/
@[simp]
public theorem baseChange_tmul (nabla : Connection A B pi M)
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b))) (b' : B') (m : M) :
    baseChange psi nabla hpsi (b' ⊗ₜ[B] m) =
      b' • baseChangeValues psi (nabla m) +
        (1 ⊗ₜ[B] m) ⊗ₜ[B'] pi' (KaehlerDifferential.D A' B' b') :=
  TensorProduct.liftAddHom_tmul _ (baseChangePair_balanced psi nabla hpsi) _ _

end Connection

end BaseChangeConnection

/-! ### Base change of the de Rham complex of a connection -/

section BaseChangeDeRham

open scoped TensorProduct

open Stacks.DeRham.DifferentialDescent

universe u u' w

variable {A B Omega : Type u} {A' B' Omega' : Type u'} {M : Type w}
  [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A A'] [Algebra A' B'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A B B'] [IsScalarTower A A' B'] [SMulCommClass A' B B']
  [AddCommGroup Omega] [Module B Omega]
  [AddCommGroup Omega'] [Module B' Omega']
  [AddCommGroup M] [Module B M]
  (S : SourceDeRham A B) (S' : SourceDeRham A' B')
  (pi : Ω[B⁄A] →ₗ[B] Omega) (pi' : Ω[B'⁄A'] →ₗ[B'] Omega')
  (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
  (hpi' : Function.Surjective pi') (hgen' : S'.GenerationHypothesis pi')
  (psi : Omega →ₛₗ[algebraMap B B'] Omega')
  (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
    pi' (KaehlerDifferential.D A' B' (algebraMap B B' b)))
  (nabla : Connection A B pi M)

private noncomputable def baseChangeExteriorPowerMap (p : ℕ) :
    (⋀[B]^p Omega) →ₛₗ[algebraMap B B'] (⋀[B']^p Omega') := by
  letI : Module B Omega' := Module.compHom Omega' (algebraMap B B')
  letI : Module B (⋀[B']^p Omega') :=
    Module.compHom (⋀[B']^p Omega') (algebraMap B B')
  let alt : Omega [⋀^Fin p]→ₗ[B] (⋀[B']^p Omega') :=
    ⟨{ toFun := fun v => exteriorPower.ιMulti B' p (psi ∘ v)
       map_update_add' := by
         intro _ v i x y
         rw [Function.comp_update, Function.comp_update, Function.comp_update, psi.map_add]
         exact (exteriorPower.ιMulti B' p).map_update_add (psi ∘ v) i (psi x) (psi y)
       map_update_smul' := by
         intro _ v i b x
         rw [Function.comp_update, Function.comp_update, map_smulₛₗ]
         have hx := (exteriorPower.ιMulti B' p).map_update_smul (psi ∘ v) i
           (algebraMap B B' b) (psi x)
         change exteriorPower.ιMulti B' p
             (Function.update (psi ∘ v) i (algebraMap B B' b • psi x)) =
           algebraMap B B' b • exteriorPower.ιMulti B' p
             (Function.update (psi ∘ v) i (psi x))
         exact hx },
      by
        intro v i j hij hij'
        exact (exteriorPower.ιMulti B' p).map_eq_zero_of_eq (psi ∘ v) (congrArg psi hij) hij'⟩
  let f := exteriorPower.alternatingMapLinearEquiv alt
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro b x
        change f (b • x) = algebraMap B B' b • f x
        exact f.map_smul b x }

private theorem baseChangeExteriorPowerMap_ιMulti (p : ℕ) (omega : Fin p → Omega) :
    baseChangeExteriorPowerMap psi p
      (exteriorPower.ιMulti B p omega) = exteriorPower.ιMulti B' p (psi ∘ omega) := by
  classical
  simp [baseChangeExteriorPowerMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

private theorem baseChangeExteriorPowerMap_leftWedge (p : ℕ) (a : Omega)
    (omega : ⋀[B]^p Omega) :
    baseChangeExteriorPowerMap psi (p + 1) (leftWedge p a omega) =
      leftWedge p (psi a) (baseChangeExteriorPowerMap psi p omega) := by
  let _ : Module B (⋀[B']^p Omega') := Module.compHom _ (algebraMap B B')
  let _ : Module B (⋀[B']^(p + 1) Omega') := Module.compHom _ (algebraMap B B')
  let f : (⋀[B]^p Omega) →ₗ[B] (⋀[B']^(p + 1) Omega') :=
    { toFun := fun x => baseChangeExteriorPowerMap psi (p + 1) (leftWedge p a x)
      map_add' := by simp
      map_smul' := by
        intro b x
        change baseChangeExteriorPowerMap psi (p + 1) (leftWedge p a (b • x)) =
          algebraMap B B' b • baseChangeExteriorPowerMap psi (p + 1) (leftWedge p a x)
        rw [map_smul, map_smulₛₗ] }
  let g : (⋀[B]^p Omega) →ₗ[B] (⋀[B']^(p + 1) Omega') :=
    { toFun := fun x => leftWedge p (psi a) (baseChangeExteriorPowerMap psi p x)
      map_add' := by simp
      map_smul' := by
        intro b x
        change leftWedge p (psi a) (baseChangeExteriorPowerMap psi p (b • x)) =
          algebraMap B B' b • leftWedge p (psi a) (baseChangeExteriorPowerMap psi p x)
        rw [map_smulₛₗ, map_smul] }
  have hfg : f = g := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span B p Omega)
    rintro _ ⟨v, rfl⟩
    change baseChangeExteriorPowerMap psi (p + 1)
        (leftWedge p a (exteriorPower.ιMulti B p v)) =
      leftWedge p (psi a) (baseChangeExteriorPowerMap psi p (exteriorPower.ιMulti B p v))
    rw [leftWedge_ιMulti, baseChangeExteriorPowerMap_ιMulti,
      baseChangeExteriorPowerMap_ιMulti, leftWedge_ιMulti]
    apply congrArg (exteriorPower.ιMulti B' (p + 1))
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  exact LinearMap.congr_fun hfg omega

private noncomputable def baseChangeDeRhamMap (p : ℕ) :
    RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
      RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')) := by
  let f := TensorProduct.map
    (Connection.baseChangeInclusion (B' := B') (M := M)) (baseChangeExteriorPowerMap psi p)
  exact
    { toFun := fun x =>
        (RestrictScalars.addEquiv A B'
          ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))).symm
          (f (RestrictScalars.addEquiv A B (M ⊗[B] (⋀[B]^p Omega)) x))
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply]
        rw [RestrictScalars.addEquiv_map_smul, map_smulₛₗ]
        conv_rhs => rw [RestrictScalars.smul_def]
        rw [← IsScalarTower.algebraMap_apply A B B' a]
        simp }

private theorem baseChangeDeRhamMap_equiv (p : ℕ)
    (x : M ⊗[B] (⋀[B]^p Omega)) :
    RestrictScalars.addEquiv A B'
        ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
      (baseChangeDeRhamMap psi p x) =
    TensorProduct.map
      (Connection.baseChangeInclusion (B' := B') (M := M))
      (baseChangeExteriorPowerMap psi p)
      (RestrictScalars.addEquiv A B (M ⊗[B] (⋀[B]^p Omega)) x) := rfl

/-- The de Rham base change map on a pure tensor `m ⊗ ω`. -/
private theorem baseChangeDeRhamMap_tmul (p : ℕ) (m : M) (omega : ⋀[B]^p Omega) :
    baseChangeDeRhamMap (A := A) (B := B) (B' := B') psi p (m ⊗ₜ[B] omega) =
      (1 ⊗ₜ[B] m) ⊗ₜ[B'] baseChangeExteriorPowerMap psi p omega := rfl

private noncomputable def baseChangeExteriorPowerMapA (p : ℕ) :
    RestrictScalars A B (⋀[B]^p Omega) →ₗ[A]
      RestrictScalars A B' (⋀[B']^p Omega') := by
  exact
    { toFun := fun x =>
        (RestrictScalars.addEquiv A B' (⋀[B']^p Omega')).symm
          (baseChangeExteriorPowerMap psi p (RestrictScalars.addEquiv A B (⋀[B]^p Omega) x))
      map_add' := by simp
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply]
        rw [RestrictScalars.addEquiv_map_smul, map_smulₛₗ]
        conv_rhs => rw [RestrictScalars.smul_def]
        rw [← IsScalarTower.algebraMap_apply A B B' a]
        simp }

private theorem baseChangeCompatibility_differentials
    (hpsi : ∀ b : B, psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b))) :
    ∀ (x : Ω[B⁄A]), psi (pi x) = pi' (KaehlerDifferential.map A A' B B' x) := by
  let _ : Module B Omega' := Module.compHom Omega' (algebraMap B B')
  let _ : IsScalarTower B B' Omega' := ⟨by
    intro b b' x
    calc
      (b • b') • x = (algebraMap B B' b * b') • x := by rw [Algebra.smul_def]
      _ = algebraMap B B' b • (b' • x) := by rw [mul_smul]
      _ = b • (b' • x) := rfl⟩
  let f : Ω[B⁄A] →ₗ[B] Omega' :=
    { toFun := fun x => psi (pi x)
      map_add' := by intro x y; simp
      map_smul' := by
        intro b x
        change psi (pi (b • x)) = algebraMap B B' b • psi (pi x)
        rw [map_smul, map_smulₛₗ] }
  let g : Ω[B⁄A] →ₗ[B] Omega' :=
    { toFun := fun x => pi' (KaehlerDifferential.map A A' B B' x)
      map_add' := by intro x y; simp
      map_smul' := by
        intro b x
        change pi' (KaehlerDifferential.map A A' B B' (b • x)) =
          algebraMap B B' b • pi' (KaehlerDifferential.map A A' B B' x)
        rw [map_smul]
        rw [← IsScalarTower.algebraMap_smul B' b]
        exact pi'.map_smul _ _ }
  have hfg : f = g := by
    refine LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B) ?_
    rintro _ ⟨b, rfl⟩
    change psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.map A A' B B' (KaehlerDifferential.D A B b))
    rw [KaehlerDifferential.map_D]
    exact hpsi b
  intro x
  exact LinearMap.congr_fun hfg x

private noncomputable def kaehlerBaseChangeMap :
    Ω[B⁄A] →ₛₗ[algebraMap B B'] Ω[B'⁄A'] := by
  let f := KaehlerDifferential.map A A' B B'
  exact
    { toFun := f
      map_add' := f.map_add
      map_smul' := by
        intro b x
        rw [f.map_smul, ← IsScalarTower.algebraMap_smul B' b] }

private theorem baseChangeExteriorPowerMap_comp_pi (hpsi : ∀ b : B,
    psi (pi (KaehlerDifferential.D A B b)) =
      pi' (KaehlerDifferential.D A' B' (algebraMap B B' b))) (p : ℕ) :
    ∀ x : ⋀[B]^p (Ω[B⁄A]),
      baseChangeExteriorPowerMap psi p (exteriorPower.map p pi x) =
        exteriorPower.map p pi'
          (baseChangeExteriorPowerMap kaehlerBaseChangeMap p x) := by
  classical
  let _ : Module B (⋀[B']^p Omega') := Module.compHom _ (algebraMap B B')
  let f : (⋀[B]^p (Ω[B⁄A])) →ₗ[B] (⋀[B']^p Omega') :=
    { toFun := fun x => baseChangeExteriorPowerMap psi p (exteriorPower.map p pi x)
      map_add' := by intro x y; simp
      map_smul' := by
        intro b x
        rw [map_smulₛₗ, map_smulₛₗ]
        rfl }
  let g : (⋀[B]^p (Ω[B⁄A])) →ₗ[B] (⋀[B']^p Omega') :=
    { toFun := fun x => exteriorPower.map p pi'
        (baseChangeExteriorPowerMap kaehlerBaseChangeMap p x)
      map_add' := by intro x y; simp
      map_smul' := by
        intro b x
        rw [map_smulₛₗ, map_smul]
        rfl }
  have hfg : f = g := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span B p (Ω[B⁄A]))
    rintro _ ⟨omega, rfl⟩
    change baseChangeExteriorPowerMap psi p
        (exteriorPower.map p pi (exteriorPower.ιMulti B p omega)) =
      exteriorPower.map p pi'
        (baseChangeExteriorPowerMap kaehlerBaseChangeMap p
          (exteriorPower.ιMulti B p omega))
    rw [exteriorPower.map_apply_ιMulti, baseChangeExteriorPowerMap_ιMulti,
      baseChangeExteriorPowerMap_ιMulti, exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    exact baseChangeCompatibility_differentials (pi := pi) (pi' := pi')
      (psi := psi) hpsi (omega i)
  intro x
  exact LinearMap.congr_fun hfg x

private theorem baseChangeSourceDeRhamDifferential_commutes (p : ℕ) :
    ∀ x : ⋀[B]^p (Ω[B⁄A]),
      baseChangeExteriorPowerMap kaehlerBaseChangeMap (p + 1) (sourceDifferential S p x) =
        sourceDifferential S' p (baseChangeExteriorPowerMap kaehlerBaseChangeMap p x) := by
  classical
  let eA := RestrictScalars.addEquiv A B' (⋀[B']^p (Ω[B'⁄A']))
  let eAprime := RestrictScalars.addEquiv A' B' (⋀[B']^p (Ω[B'⁄A']))
  let eAprimeOut := RestrictScalars.addEquiv A' B' (⋀[B']^(p + 1) (Ω[B'⁄A']))
  let eSrc : (⋀[B]^p (Ω[B⁄A])) →ₗ[A] SrcA A B p :=
    { toFun := (RestrictScalars.addEquiv A B (⋀[B]^p (Ω[B⁄A]))).symm
      map_add' := by simp
      map_smul' := by
        intro a x
        rfl }
  let f : RestrictScalars A B (⋀[B]^p (Ω[B⁄A])) →ₗ[A]
      RestrictScalars A B' (⋀[B']^(p + 1) (Ω[B'⁄A'])) :=
    (baseChangeExteriorPowerMapA kaehlerBaseChangeMap (p + 1)).comp (S.d p)
  let g : RestrictScalars A B (⋀[B]^p (Ω[B⁄A])) →ₗ[A]
      RestrictScalars A B' (⋀[B']^(p + 1) (Ω[B'⁄A'])) :=
    { toFun := fun x => eAprimeOut (S'.d p (eAprime.symm (eA
        (baseChangeExteriorPowerMapA kaehlerBaseChangeMap p x))))
      map_add' := by
        intro x y
        change eAprimeOut (S'.d p (eAprime.symm (eA
          (baseChangeExteriorPowerMapA kaehlerBaseChangeMap p (x + y))))) =
            eAprimeOut (S'.d p (eAprime.symm (eA
              (baseChangeExteriorPowerMapA kaehlerBaseChangeMap p x)))) +
            eAprimeOut (S'.d p (eAprime.symm (eA
              (baseChangeExteriorPowerMapA kaehlerBaseChangeMap p y))))
        simp only [_root_.map_add, (S'.d p).map_add, eAprimeOut.map_add,
          eAprime.symm.map_add, eA.map_add]
      map_smul' := by
        intro a x
        let y := eAprime.symm (eA
          (baseChangeExteriorPowerMapA kaehlerBaseChangeMap p x))
        have hy : eAprime.symm (eA
            (baseChangeExteriorPowerMapA kaehlerBaseChangeMap p (a • x))) =
            (algebraMap A A' a) • y := by
          rw [(baseChangeExteriorPowerMapA kaehlerBaseChangeMap p).map_smul,
            RestrictScalars.addEquiv_map_smul]
          change eAprime.symm (algebraMap A B' a • eA
              (baseChangeExteriorPowerMapA kaehlerBaseChangeMap p x)) = _
          rw [IsScalarTower.algebraMap_apply A A' B' a,
            RestrictScalars.addEquiv_symm_map_algebraMap_smul]
        change eAprimeOut (S'.d p
            (eAprime.symm (eA (baseChangeExteriorPowerMapA kaehlerBaseChangeMap p
              (a • x))))) =
          algebraMap A B' a • eAprimeOut (S'.d p y)
        rw [hy, (S'.d p).map_smul, RestrictScalars.addEquiv_map_smul,
          IsScalarTower.algebraMap_apply A A' B' a] }
  have hfg : f.comp eSrc = g.comp eSrc := by
    apply LinearMap.ext_on (span_range_smul_ιMulti_eq_top (R := A)
      (KaehlerDifferential.D A B) (KaehlerDifferential.span_range_derivation A B) p)
    rintro _ ⟨b, rfl⟩
    change baseChangeExteriorPowerMapA kaehlerBaseChangeMap (p + 1)
        (S.d p (eSrc (srcGen p b))) =
      eAprimeOut (S'.d p (eAprime.symm (eA
        (baseChangeExteriorPowerMapA kaehlerBaseChangeMap p
          (eSrc (srcGen p b))))))
    have hgen : S.d p (eSrc (srcGen p b)) =
        (RestrictScalars.addEquiv A B (⋀[B]^(p + 1) (Ω[B⁄A]))).symm
          (srcGenRes p b) := by
      change S.d p (srcGen p b) =
        (RestrictScalars.addEquiv A B (⋀[B]^(p + 1) (Ω[B⁄A]))).symm
          (srcGenRes p b)
      rw [S.gen]
      rfl
    rw [hgen]
    have harg : eAprime.symm (eA
        (baseChangeExteriorPowerMapA kaehlerBaseChangeMap p
          (eSrc (srcGen p b)))) =
        srcGen p (fun i => algebraMap B B' (b i)) := by
      change baseChangeExteriorPowerMap kaehlerBaseChangeMap p (srcGen p b) =
        srcGen p (fun i => algebraMap B B' (b i))
      rw [srcGen, map_smulₛₗ, baseChangeExteriorPowerMap_ιMulti, srcGen]
      apply congrArg (fun z : ⋀[B']^p (Ω[B'⁄A']) =>
        algebraMap B B' (b 0) • z)
      apply congrArg (exteriorPower.ιMulti B' p)
      funext i
      exact KaehlerDifferential.map_D A A' B B' (b i.succ)
    rw [harg, S'.gen]
    change baseChangeExteriorPowerMap kaehlerBaseChangeMap (p + 1)
        (srcGenRes p b) =
      srcGenRes p (fun i => algebraMap B B' (b i))
    rw [srcGenRes, baseChangeExteriorPowerMap_ιMulti]
    congr 1
    funext i
    exact KaehlerDifferential.map_D A A' B B' (b i)
  intro x
  have hx := LinearMap.congr_fun hfg
    ((RestrictScalars.addEquiv A B (⋀[B]^p (Ω[B⁄A])) x))
  change baseChangeExteriorPowerMap kaehlerBaseChangeMap (p + 1)
      (sourceDifferential S p x) =
    sourceDifferential S' p (baseChangeExteriorPowerMap kaehlerBaseChangeMap p x) at hx
  exact hx

private theorem baseChangeExtendedDeRhamDifferential
    (E : ExtendedConnection S pi nabla)
    (E' : ExtendedConnection S' pi' (Connection.baseChange psi nabla hpsi))
    (hpi : Function.Surjective pi) (p : ℕ) (omega : ⋀[B]^p Omega) :
    baseChangeExteriorPowerMap psi (p + 1)
        (descendedDifferential E.deRhamDifferential p omega) =
      descendedDifferential E'.deRhamDifferential p
        (baseChangeExteriorPowerMap psi p omega) := by
  obtain ⟨x, rfl⟩ := exteriorPower.map_surjective hpi omega
  let FK (q : ℕ) : (⋀[B]^q (Ω[B⁄A])) →ₛₗ[algebraMap B B'] (⋀[B']^q (Ω[B'⁄A'])) :=
    baseChangeExteriorPowerMap
      (kaehlerBaseChangeMap (A := A) (A' := A') (B := B) (B' := B')) q
  have hE := descendedDifferential_commutes S pi E.deRhamDifferential E.commutes p x
  have hE' := descendedDifferential_commutes S' pi' E'.deRhamDifferential E'.commutes p (FK p x)
  have hcomp := baseChangeExteriorPowerMap_comp_pi
    (pi := pi) (pi' := pi') (psi := psi) hpsi (p + 1) (sourceDifferential S p x)
  have hcompX := baseChangeExteriorPowerMap_comp_pi
    (pi := pi) (pi' := pi') (psi := psi) hpsi p x
  have hsource := baseChangeSourceDeRhamDifferential_commutes
    (S := S) (S' := S') p x
  rw [hE, hcomp, hsource, ← hE', hcompX]

private theorem baseChangeTensorWedge (p : ℕ) (omega : ⋀[B]^p Omega)
    (t : M ⊗[B] Omega) :
    TensorProduct.map
        (Connection.baseChangeInclusion (B' := B') (M := M))
        (baseChangeExteriorPowerMap psi (p + 1))
        (TensorProduct.map LinearMap.id ((leftWedge p).flip omega) t) =
      TensorProduct.map LinearMap.id
        ((leftWedge p).flip (baseChangeExteriorPowerMap psi p omega))
        (Connection.baseChangeValues psi t) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m a =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply,
        Connection.baseChangeValues_tmul]
      change ((1 : B') ⊗ₜ[B] m) ⊗ₜ[B']
          baseChangeExteriorPowerMap psi (p + 1) (leftWedge p a omega) =
        ((1 : B') ⊗ₜ[B] m) ⊗ₜ[B']
          leftWedge (B := B') p (psi a) (baseChangeExteriorPowerMap psi p omega)
      rw [baseChangeExteriorPowerMap_leftWedge]

private theorem baseChangeMap_intertwines_extendedConnection
    (E : ExtendedConnection S pi nabla)
    (E' : ExtendedConnection S' pi' (Connection.baseChange psi nabla hpsi))
    (hpi : Function.Surjective pi) (p : ℕ) :
    ∀ x : M ⊗[B] (⋀[B]^p Omega),
      RestrictScalars.addEquiv A B'
          ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
        (baseChangeDeRhamMap psi (p + 1)
            (E.toLinearMap p
              ((RestrictScalars.addEquiv A B (M ⊗[B] (⋀[B]^p Omega))).symm x))) =
        RestrictScalars.addEquiv A' B'
          ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
          (E'.toLinearMap p
            ((RestrictScalars.addEquiv A' B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))).symm
              (RestrictScalars.addEquiv A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
                (baseChangeDeRhamMap psi p
                  ((RestrictScalars.addEquiv A B (M ⊗[B] (⋀[B]^p Omega))).symm x))))) := by
  let eIn := RestrictScalars.addEquiv A B (M ⊗[B] (⋀[B]^p Omega))
  let eOut := RestrictScalars.addEquiv A B'
    ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
  let eIn' := RestrictScalars.addEquiv A' B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
  let eMid := RestrictScalars.addEquiv A B'
    ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega'))
  let eOut' := RestrictScalars.addEquiv A' B'
    ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
  intro x
  change eOut (baseChangeDeRhamMap psi (p + 1)
      (E.toLinearMap p (eIn.symm x))) =
    eOut' (E'.toLinearMap p (eIn'.symm
      (eMid (baseChangeDeRhamMap psi p (eIn.symm x)))))
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      rw [eIn.symm.map_add, (E.toLinearMap p).map_add,
        (baseChangeDeRhamMap psi (p + 1)).map_add, eOut.map_add,
        (baseChangeDeRhamMap psi p).map_add, eMid.map_add,
        eIn'.symm.map_add, (E'.toLinearMap p).map_add, eOut'.map_add]
      rw [hx, hy]
  | tmul m omega =>
      change RestrictScalars.addEquiv A B'
            ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
          (baseChangeDeRhamMap psi (p + 1)
            (E.toLinearMap p (eIn.symm (m ⊗ₜ[B] omega)))) =
        RestrictScalars.addEquiv A' B'
          ((B' ⊗[B] M) ⊗[B'] (⋀[B']^(p + 1) Omega'))
          (E'.toLinearMap p (eIn'.symm
            (eMid (baseChangeDeRhamMap psi p (eIn.symm (m ⊗ₜ[B] omega))))))
      have hbase :
          eMid (baseChangeDeRhamMap psi p (eIn.symm (m ⊗ₜ[B] omega))) =
            (Connection.baseChangeInclusion
              (B' := B') (M := M) m) ⊗ₜ[B'] baseChangeExteriorPowerMap psi p omega :=
        baseChangeDeRhamMap_tmul (A := A) psi p m omega
      let eInPlus := RestrictScalars.addEquiv A B
        (M ⊗[B] (⋀[B]^(p + 1) Omega))
      have hleft :
          eOut (baseChangeDeRhamMap psi (p + 1)
            (E.toLinearMap p (eIn.symm (m ⊗ₜ[B] omega)))) =
          TensorProduct.map
            (Connection.baseChangeInclusion (B' := B') (M := M))
            (baseChangeExteriorPowerMap psi (p + 1))
            (eInPlus (E.toLinearMap p (eIn.symm (m ⊗ₜ[B] omega)))) := by
        change eOut (baseChangeDeRhamMap psi (p + 1)
          (eInPlus (E.toLinearMap p (eIn.symm (m ⊗ₜ[B] omega))))) =
          TensorProduct.map
            (Connection.baseChangeInclusion (B' := B') (M := M))
            (baseChangeExteriorPowerMap psi (p + 1))
            (eInPlus (E.toLinearMap p (eIn.symm (m ⊗ₜ[B] omega))))
        exact baseChangeDeRhamMap_equiv (A := A) (B := B) (B' := B')
          (psi := psi) (p := p + 1)
          (eInPlus (E.toLinearMap p (eIn.symm (m ⊗ₜ[B] omega))))
      have hE : eInPlus (E.toLinearMap p (eIn.symm (m ⊗ₜ[B] omega))) =
          TensorProduct.map LinearMap.id ((leftWedge p).flip omega) (nabla m) +
            m ⊗ₜ[B] descendedDifferential E.deRhamDifferential p omega := by
        change RestrictScalars.addEquiv A B _ (E.toLinearMap p (m ⊗ₜ[B] omega)) = _
        exact E.map_tmul p m omega
      have hDiff : baseChangeExteriorPowerMap psi (p + 1)
            (descendedDifferential E.deRhamDifferential p omega) =
          descendedDifferential E'.deRhamDifferential p
            (baseChangeExteriorPowerMap psi p omega) :=
        baseChangeExtendedDeRhamDifferential
          (S := S) (S' := S') (pi := pi) (pi' := pi') (psi := psi)
          (hpsi := hpsi) (nabla := nabla) (E := E) (E' := E')
          (hpi := hpi) (p := p) (omega := omega)
      rw [hE] at hleft
      rw [map_add, baseChangeTensorWedge] at hleft
      rw [TensorProduct.map_tmul, hDiff] at hleft
      let m' : B' ⊗[B] M := Connection.baseChangeInclusion (B' := B') (M := M) m
      let eta' := baseChangeExteriorPowerMap psi p omega
      have hE' : eOut' (E'.toLinearMap p (eIn'.symm (m' ⊗ₜ[B'] eta'))) =
            TensorProduct.map LinearMap.id ((leftWedge p).flip eta')
              (Connection.baseChange psi nabla hpsi m') +
            m' ⊗ₜ[B'] descendedDifferential E'.deRhamDifferential p eta' := by
        change RestrictScalars.addEquiv A' B' _
            (E'.toLinearMap p (m' ⊗ₜ[B'] eta')) = _
        exact E'.map_tmul p m' eta'
      rw [hleft, hbase, hE']
      have hconn :
          Connection.baseChange psi nabla hpsi
              (Connection.baseChangeInclusion (B' := B') (M := M) m) =
            Connection.baseChangeValues psi (nabla m) := by
        simp [Connection.baseChangeInclusion, Connection.baseChange_tmul]
      rw [hconn]

private noncomputable def baseChangeLiftOne
    {N : Type*} [AddCommGroup N] [Module B' N]
    (t : N ⊗[B'] Omega') : RestrictScalars A' B' (N ⊗[B'] (⋀[B']^1 Omega')) :=
  (RestrictScalars.addEquiv A' B' _).symm
    (TensorProduct.map LinearMap.id (exteriorPower.oneEquiv B' Omega').symm.toLinearMap t)

omit [CommRing A'] [Algebra A' B'] in
private theorem baseChangeLiftOne_eq_input
    {N : Type*} [AddCommGroup N] [Module B' N]
    (t : N ⊗[B'] Omega') :
    baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega') (N := N) t =
      TensorProduct.map LinearMap.id
        (exteriorPower.oneEquiv B' Omega').symm.toLinearMap t := by
  apply (RestrictScalars.addEquiv A' B' (N ⊗[B'] (⋀[B']^1 Omega'))).injective
  simp [baseChangeLiftOne]
  rfl

omit [CommRing A'] [Algebra A' B'] in
private theorem baseChangeLiftOne_add
    {N : Type*} [AddCommGroup N] [Module B' N]
    (x y : N ⊗[B'] Omega') :
    baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega') (N := N) (x + y) =
      baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega') (N := N) x +
        baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega') (N := N) y := by
  apply (RestrictScalars.addEquiv A' B' (N ⊗[B'] (⋀[B']^1 Omega'))).injective
  simp [baseChangeLiftOne]

omit [CommRing A'] [Algebra A' B'] in
private theorem baseChangeLiftOne_tmul
    {N : Type*} [AddCommGroup N] [Module B' N]
    (n : N) (a : Omega') :
    baseChangeLiftOne (B' := B') (A' := A') (Omega' := Omega') (N := N)
        (n ⊗ₜ[B'] a) = n ⊗ₜ[B'] (exteriorPower.oneEquiv B' Omega').symm a := by
  apply (RestrictScalars.addEquiv A' B' (N ⊗[B'] (⋀[B']^1 Omega'))).injective
  simp [baseChangeLiftOne, RestrictScalars.addEquiv]
  rfl

private noncomputable def baseChangeWedgeCorrection (b : B') :
    ((B' ⊗[B] M) ⊗[B'] Omega') →ₗ[B']
      ((B' ⊗[B] M) ⊗[B'] (⋀[B']^2 Omega')) :=
  TensorProduct.map LinearMap.id
    ((leftWedge 1 (pi' (KaehlerDifferential.D A' B' b))).comp
      (exteriorPower.oneEquiv B' Omega').symm.toLinearMap)

omit [SMulCommClass A' B B'] in
private theorem baseChangeWedgeCorrection_zero (b : B') :
    baseChangeWedgeCorrection (pi' := pi') (M := M) b
      (0 : (B' ⊗[B] M) ⊗[B'] Omega') =
      (0 : (B' ⊗[B] M) ⊗[B'] (⋀[B']^2 Omega')) := by
  simp [baseChangeWedgeCorrection]

private theorem baseChangeLeftWedge_swap (a b : Omega') :
    leftWedge 1 a ((exteriorPower.oneEquiv B' Omega').symm b) +
      leftWedge 1 b ((exteriorPower.oneEquiv B' Omega').symm a) = 0 := by
  apply Subtype.ext
  change ((leftWedge 1 a
      ((exteriorPower.oneEquiv B' Omega').symm b) : ⋀[B']^2 Omega') :
        ExteriorAlgebra B' Omega') +
    ((leftWedge 1 b
      ((exteriorPower.oneEquiv B' Omega').symm a) : ⋀[B']^2 Omega') :
        ExteriorAlgebra B' Omega') = 0
  rw [leftWedge_coe, leftWedge_coe,
    exteriorPower.oneEquiv_symm_apply, exteriorPower.oneEquiv_symm_apply,
    coe_ιMulti_one, coe_ιMulti_one]
  exact ExteriorAlgebra.ι_add_mul_swap a b

omit [Algebra A A'] [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B']
  [SMulCommClass A' B B'] in
private theorem extendedDeRhamDifferential_differential_zero
    (E' : ExtendedConnection S' pi' (Connection.baseChange psi nabla hpsi))
    (b : B') :
    descendedDifferential E'.deRhamDifferential 1
      ((exteriorPower.oneEquiv B' Omega').symm
        (pi' (KaehlerDifferential.D A' B' b))) = 0 := by
  let eSrc := exteriorPower.oneEquiv B' (Ω[B'⁄A'])
  let eTgt := exteriorPower.oneEquiv B' Omega'
  have hsrc : sourceDifferential S' 1 (eSrc.symm (KaehlerDifferential.D A' B' b)) = 0 := by
    rw [exteriorPower.oneEquiv_symm_apply]
    have h := sourceDifferential_srcGen S' 1 (Fin.cons (1 : B') (fun _ : Fin 1 => b))
    simp only [srcGen, Fin.cons_zero, Fin.cons_succ, one_smul] at h
    rw [h, srcGenRes]
    exact (exteriorPower.ιMulti B' 2).map_coord_zero (i := 0) (by simp)
  have hmap : exteriorPower.map 1 pi' (eSrc.symm (KaehlerDifferential.D A' B' b)) =
      eTgt.symm (pi' (KaehlerDifferential.D A' B' b)) := by
    apply eTgt.injective
    have hnat := LinearMap.congr_fun (exteriorPower.oneEquiv_naturality pi')
      (eSrc.symm (KaehlerDifferential.D A' B' b))
    simpa [eSrc, eTgt] using hnat
  have hcomm := descendedDifferential_commutes S' pi' E'.deRhamDifferential E'.commutes 1
    (eSrc.symm (KaehlerDifferential.D A' B' b))
  rw [hmap, hsrc] at hcomm
  exact hcomm.trans (map_zero _)

omit [Algebra A A'] [Algebra A B'] [IsScalarTower A B B'] [IsScalarTower A A' B']
  [SMulCommClass A' B B'] in
private theorem baseChangeExtendedCurvature_smul
    (E' : ExtendedConnection S' pi' (Connection.baseChange psi nabla hpsi))
    (b : B') (n : B' ⊗[B] M) :
    RestrictScalars.addEquiv A' B' _ (E'.toLinearMap 1
        (baseChangeLiftOne (Connection.baseChange psi nabla hpsi (b • n)))) =
      b • RestrictScalars.addEquiv A' B' _ (E'.toLinearMap 1
        (baseChangeLiftOne (Connection.baseChange psi nabla hpsi n))) := by
  let nabla' := Connection.baseChange psi nabla hpsi
  let e := exteriorPower.oneEquiv B' Omega'
  let eOut := RestrictScalars.addEquiv A' B'
    ((B' ⊗[B] M) ⊗[B'] (⋀[B']^2 Omega'))
  let eOmegaOut := RestrictScalars.addEquiv A' B' (⋀[B']^2 Omega')
  have hproduct (t : (B' ⊗[B] M) ⊗[B'] Omega') :
      eOut (E'.toLinearMap 1 (baseChangeLiftOne (b • t))) =
        b • eOut (E'.toLinearMap 1 (baseChangeLiftOne t)) +
          baseChangeWedgeCorrection (pi' := pi') b t := by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy =>
        rw [smul_add, baseChangeLiftOne_add, map_add, eOut.map_add, hx, hy,
          baseChangeLiftOne_add, map_add]
        simp only [smul_add, map_add]
        abel
    | tmul n a =>
        have hb := E'.map_tmul 1 (b • n) (e.symm a)
        have h0 := E'.map_tmul 1 n (e.symm a)
        have hL1 : baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega')
            (N := B' ⊗[B] M) (b • (n ⊗ₜ[B'] a)) =
            (b • n) ⊗ₜ[B'] (e.symm a) := by
          rw [TensorProduct.smul_tmul', baseChangeLiftOne_tmul]
        have hL0 : baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega')
            (N := B' ⊗[B] M) (n ⊗ₜ[B'] a) = n ⊗ₜ[B'] (e.symm a) :=
          baseChangeLiftOne_tmul n a
        rw [hL1, hL0, hb, h0, nabla'.leibniz]
        simp only [map_add, map_smul, smul_add, TensorProduct.smul_tmul']
        simp [baseChangeWedgeCorrection, e]
        abel
  have hdb :
      eOut (E'.toLinearMap 1
        (baseChangeLiftOne (n ⊗ₜ[B'] pi' (KaehlerDifferential.D A' B' b)))) =
        -baseChangeWedgeCorrection (pi' := pi') b (nabla' n) := by
    have hmtRaw := E'.map_tmul 1 n (e.symm (pi' (KaehlerDifferential.D A' B' b)))
    have hmt : eOut (E'.toLinearMap 1
        (baseChangeLiftOne (n ⊗ₜ[B'] pi' (KaehlerDifferential.D A' B' b)))) =
      TensorProduct.map LinearMap.id
          ((leftWedge 1).flip
            (e.symm (pi' (KaehlerDifferential.D A' B' b)))) (nabla' n) +
        n ⊗ₜ[B'] eOmegaOut (E'.deRhamDifferential 1
          (e.symm (pi' (KaehlerDifferential.D A' B' b)))) := by
      rw [baseChangeLiftOne_tmul]
      exact hmtRaw
    have hzero : eOmegaOut (E'.deRhamDifferential 1
        (e.symm (pi' (KaehlerDifferential.D A' B' b)))) = 0 :=
      extendedDeRhamDifferential_differential_zero (E' := E') (b := b)
    rw [hzero] at hmt
    have hcancel : ∀ t : (B' ⊗[B] M) ⊗[B'] Omega',
        TensorProduct.map LinearMap.id
            ((leftWedge 1).flip
              (e.symm (pi' (KaehlerDifferential.D A' B' b)))) t =
          -baseChangeWedgeCorrection (pi' := pi') b t := by
      intro t
      induction t using TensorProduct.inductionOn with
      | add x y hx hy => simp [hx, hy]; abel
      | tmul m a =>
        simp only [TensorProduct.map_tmul, LinearMap.id_apply,
          baseChangeWedgeCorrection, LinearMap.comp_apply, LinearMap.flip_apply]
        have hswap := baseChangeLeftWedge_swap (B' := B') a
          (pi' (KaehlerDifferential.D A' B' b))
        have hneg : leftWedge 1 a
            (e.symm (pi' (KaehlerDifferential.D A' B' b))) =
            -leftWedge 1 (pi' (KaehlerDifferential.D A' B' b)) (e.symm a) :=
          eq_neg_of_add_eq_zero_left hswap
        change m ⊗ₜ[B']
            leftWedge 1 a (e.symm (pi' (KaehlerDifferential.D A' B' b))) =
          -m ⊗ₜ[B'] leftWedge 1
            (pi' (KaehlerDifferential.D A' B' b)) (e.symm a)
        rw [hneg, TensorProduct.tmul_neg]
    rw [hcancel (nabla' n)] at hmt
    simp only [hmt, TensorProduct.tmul_zero, add_zero]
  have hleibniz := nabla'.leibniz b n
  change eOut (E'.toLinearMap 1
      (baseChangeLiftOne (nabla' (b • n)))) = _
  rw [hleibniz]
  rw [baseChangeLiftOne_add, map_add, eOut.map_add, hproduct (nabla' n), hdb]
  abel

private theorem baseChangeDeRhamMap_one_input
    (t : M ⊗[B] Omega) :
    RestrictScalars.addEquiv A B'
        ((B' ⊗[B] M) ⊗[B'] (⋀[B']^1 Omega'))
      (baseChangeDeRhamMap (A := A) (B := B) (B' := B') (M := M) psi 1
        (TensorProduct.map LinearMap.id (exteriorPower.oneEquiv B Omega).symm.toLinearMap t)) =
    TensorProduct.map LinearMap.id
      (exteriorPower.oneEquiv B' Omega').symm.toLinearMap
      (Connection.baseChangeValues psi t) := by
  let e := RestrictScalars.addEquiv A B (M ⊗[B] (⋀[B]^1 Omega))
  let eOmega := exteriorPower.oneEquiv B Omega
  let eOmega' := exteriorPower.oneEquiv B' Omega'
  let L : (M ⊗[B] Omega) →ₗ[B] M ⊗[B] (⋀[B]^1 Omega) :=
    TensorProduct.map LinearMap.id eOmega.symm.toLinearMap
  let F :=
    TensorProduct.map
      (Connection.baseChangeInclusion (B' := B') (M := M))
      (baseChangeExteriorPowerMap psi 1)
  let f : (M ⊗[B] Omega) →+ ((B' ⊗[B] M) ⊗[B'] (⋀[B']^1 Omega')) := {
    toFun := fun t => F (e (e.symm (L t)))
    map_zero' := by
      change F (e (e.symm (L 0))) = 0
      rw [L.map_zero, e.symm.map_zero, e.map_zero, F.map_zero]
    map_add' := by
      intro x y
      change F (e (e.symm (L (x + y)))) = F (e (e.symm (L x))) + F (e (e.symm (L y)))
      rw [L.map_add, e.symm.map_add, e.map_add, F.map_add]
  }
  let g : (M ⊗[B] Omega) →+ ((B' ⊗[B] M) ⊗[B'] (⋀[B']^1 Omega')) := {
    toFun := fun t => TensorProduct.map LinearMap.id eOmega'.symm.toLinearMap
      (Connection.baseChangeValues psi t)
    map_zero' := by simp
    map_add' := by simp
  }
  have hfg : f = g := by
    apply AddMonoidHom.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [f.map_add, g.map_add, hx, hy]
    | tmul m a =>
        have hpow : baseChangeExteriorPowerMap psi 1 (eOmega.symm a) =
            eOmega'.symm (psi a) := by
          rw [exteriorPower.oneEquiv_symm_apply, baseChangeExteriorPowerMap_ιMulti,
            exteriorPower.oneEquiv_symm_apply]
          exact congrArg (exteriorPower.ιMulti B' 1) (by funext i; simp)
        change F (e (e.symm (L (m ⊗ₜ[B] a)))) =
          TensorProduct.map LinearMap.id eOmega'.symm.toLinearMap
            (Connection.baseChangeValues psi (m ⊗ₜ[B] a))
        rw [e.apply_symm_apply]
        simp only [L, TensorProduct.map_tmul, LinearMap.id_apply]
        simp only [F, TensorProduct.map_tmul, LinearMap.id_apply,
          Connection.baseChangeValues_tmul, Connection.baseChangeInclusion]
        congr 2
  rw [baseChangeDeRhamMap_equiv]
  change f t = g t
  exact congrArg (fun h : (M ⊗[B] Omega) →+ _ => h t) hfg

/-- An integrable connection remains integrable after the compatible base change. -/
@[stacks 07PY "integrability after base change"]
public theorem baseChange_isIntegrable
    (hintegrable : Connection.IsIntegrable S pi hpi hgen nabla) :
    Connection.IsIntegrable S' pi' hpi' hgen'
      (Connection.baseChange psi nabla hpsi) := by
  let nabla' := Connection.baseChange psi nabla hpsi
  let E := extendedConnection S pi hpi hgen nabla
  let E' := extendedConnection S' pi' hpi' hgen' nabla'
  let eOut := RestrictScalars.addEquiv A' B'
    ((B' ⊗[B] M) ⊗[B'] (⋀[B']^2 Omega'))
  change ∀ n : B' ⊗[B] M,
    E'.toLinearMap 1
      (TensorProduct.map LinearMap.id
        (exteriorPower.oneEquiv B' Omega').symm.toLinearMap (nabla' n)) = 0
  have hcurv_add (x y : B' ⊗[B] M) :
      eOut (E'.toLinearMap 1
        (baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega')
          (N := B' ⊗[B] M) (nabla' (x + y)))) =
      eOut (E'.toLinearMap 1
        (baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega')
          (N := B' ⊗[B] M) (nabla' x))) +
      eOut (E'.toLinearMap 1
        (baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega')
          (N := B' ⊗[B] M) (nabla' y))) := by
    rw [nabla'.map_add, baseChangeLiftOne_add,
      (E'.toLinearMap 1).map_add, eOut.map_add]
  have hcurv_inclusion (m : M) :
      eOut (E'.toLinearMap 1
        (baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega')
          (N := B' ⊗[B] M)
          (nabla' (Connection.baseChangeInclusion (B' := B') (M := M) m)))) = 0 := by
    let x0 := TensorProduct.map LinearMap.id
      (exteriorPower.oneEquiv B Omega).symm.toLinearMap (nabla m)
    let eIn := RestrictScalars.addEquiv A B
      (M ⊗[B] (⋀[B]^1 Omega))
    let x := eIn x0
    have hbridge0 := baseChangeMap_intertwines_extendedConnection
      (S := S) (S' := S') (pi := pi) (pi' := pi') (psi := psi)
      (hpsi := hpsi) (nabla := nabla) (E := E) (E' := E')
      (hpi := hpi) (p := 1) x
    have hcancel : eIn.symm (eIn x0) = x0 := eIn.symm_apply_apply x0
    have hbridge := hbridge0
    rw [hcancel] at hbridge
    have hmap :
        RestrictScalars.addEquiv A B'
          ((B' ⊗[B] M) ⊗[B'] (⋀[B']^1 Omega'))
          (baseChangeDeRhamMap (A := A) (B := B) (B' := B')
            (M := M) psi 1 x0) =
        TensorProduct.map LinearMap.id
          (exteriorPower.oneEquiv B' Omega').symm.toLinearMap
          (Connection.baseChangeValues psi (nabla m)) := by
      simpa [x0] using
        (baseChangeDeRhamMap_one_input (A := A) (B := B) (B' := B')
          (M := M) (Omega := Omega) (Omega' := Omega') (psi := psi) (nabla m))
    rw [hmap] at hbridge
    have hsourcezero : E.toLinearMap 1 x0 = 0 := by
      simpa [x0] using hintegrable.comp_eq_zero m
    have hbasecurv :
        eOut (E'.toLinearMap 1
          (baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega')
            (N := B' ⊗[B] M)
            (Connection.baseChangeValues psi (nabla m)))) = 0 := by
      have hbridge' := hbridge
      rw [hsourcezero] at hbridge'
      simp only [map_zero] at hbridge'
      have hbridge'' := hbridge'.symm
      simpa [baseChangeLiftOne] using hbridge''
    simpa [nabla', Connection.baseChangeInclusion] using hbasecurv
  have hcurv : ∀ n : B' ⊗[B] M,
      eOut (E'.toLinearMap 1
        (baseChangeLiftOne (A' := A') (B' := B') (Omega' := Omega')
          (N := B' ⊗[B] M) (nabla' n))) = 0 := by
    intro n
    induction n using TensorProduct.inductionOn with
    | add x y hx hy =>
        rw [hcurv_add, hx, hy, add_zero]
    | tmul b m =>
        have htmul : b ⊗ₜ[B] m = b •
            Connection.baseChangeInclusion (B' := B') (M := M) m := by
          calc
            b ⊗ₜ[B] m = (b • (1 : B')) ⊗ₜ[B] m := by simp
            _ = b • ((1 : B') ⊗ₜ[B] m) := by rw [TensorProduct.smul_tmul']
            _ = b • Connection.baseChangeInclusion
                (B' := B') (M := M) m := rfl
        rw [htmul, baseChangeExtendedCurvature_smul (E' := E') (b := b)
            (n := Connection.baseChangeInclusion (B' := B') (M := M) m),
          hcurv_inclusion, smul_zero]
  intro n
  apply eOut.injective
  rw [← baseChangeLiftOne_eq_input (A' := A') (B' := B')
    (Omega' := Omega') (N := B' ⊗[B] M) (nabla' n)]
  simpa using hcurv n

/-- The canonical degreewise map from a connection's de Rham complex to that of its base
change is uniquely specified by its value on wedges of one-forms, and commutes with the
extended differentials. -/
@[stacks 07PY "canonical map of complexes"]
public theorem existsUnique_baseChangeDeRhamMap
    (_hintegrable : Connection.IsIntegrable S pi hpi hgen nabla) :
    ∃! c : ∀ p : ℕ,
      RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
        RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')),
      (∀ (p : ℕ) (m : M) (omega : Fin p → Omega),
        c p (m ⊗ₜ[B] exteriorPower.ιMulti B p omega) =
          (1 ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ omega)) ∧
      (∀ (p : ℕ) (x : M ⊗[B] (⋀[B]^p Omega)),
        c (p + 1) ((extendedConnection S pi hpi hgen nabla).toLinearMap p x) =
          (extendedConnection S' pi' hpi' hgen'
            (Connection.baseChange psi nabla hpsi)).toLinearMap p (c p x)) := by
  let E := extendedConnection S pi hpi hgen nabla
  let E' := extendedConnection S' pi' hpi' hgen'
    (Connection.baseChange psi nabla hpsi)
  have hformula : ∀ (p : ℕ) (m : M) (omega : Fin p → Omega),
      baseChangeDeRhamMap (A := A) (B := B) (B' := B') (M := M)
        psi p (m ⊗ₜ[B] exteriorPower.ιMulti B p omega) =
        (1 ⊗ₜ[B] m) ⊗ₜ[B'] exteriorPower.ιMulti B' p (psi ∘ omega) := by
    intro p m omega
    rw [baseChangeDeRhamMap_tmul, baseChangeExteriorPowerMap_ιMulti]
  have hchain : ∀ (p : ℕ) (x : M ⊗[B] (⋀[B]^p Omega)),
      baseChangeDeRhamMap (A := A) (B := B) (B' := B') (M := M)
        psi (p + 1) (E.toLinearMap p x) =
        E'.toLinearMap p (baseChangeDeRhamMap (A := A) (B := B) (B' := B') (M := M)
          psi p x) := by
    intro p x
    exact baseChangeMap_intertwines_extendedConnection
      (S := S) (S' := S') (pi := pi) (pi' := pi') (psi := psi)
      (hpsi := hpsi) (nabla := nabla) (E := E) (E' := E')
      (hpi := hpi) (p := p) (RestrictScalars.addEquiv A B (M ⊗[B] (⋀[B]^p Omega)) x)
  let c : ∀ p : ℕ,
      RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
        RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')) :=
    fun p => baseChangeDeRhamMap psi p
  refine ⟨c, ⟨hformula, fun p x => hchain p x⟩, ?_⟩
  intro d hd
  funext p
  apply LinearMap.ext
  intro x
  let eSrc := RestrictScalars.addEquiv A B (M ⊗[B] (⋀[B]^p Omega))
  let f : (M ⊗[B] (⋀[B]^p Omega)) →+
      RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')) :=
    { toFun := fun x => d p (eSrc.symm x)
      map_zero' := by simp [eSrc]
      map_add' := by intro x y; simp [eSrc] }
  let g : (M ⊗[B] (⋀[B]^p Omega)) →+
      RestrictScalars A B' ((B' ⊗[B] M) ⊗[B'] (⋀[B']^p Omega')) :=
    { toFun := fun x => c p (eSrc.symm x)
      map_zero' := by simp [c, eSrc]
      map_add' := by intro x y; simp [c, eSrc] }
  have hgen : ∀ (m : M) (omega : Fin p → Omega),
      f (m ⊗ₜ[B] exteriorPower.ιMulti B p omega) =
        g (m ⊗ₜ[B] exteriorPower.ιMulti B p omega) := by
    intro m omega
    have h₁ := hd.1 p m omega
    have h₂ := hformula p m omega
    change d p (m ⊗ₜ[B] exteriorPower.ιMulti B p omega) =
      c p (m ⊗ₜ[B] exteriorPower.ιMulti B p omega)
    rw [h₁, h₂]
  have hfg : f = g := by
    apply AddMonoidHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul m eta =>
        have heta : ∀ (m : M) (eta : ⋀[B]^p Omega),
            f (m ⊗ₜ[B] eta) = g (m ⊗ₜ[B] eta) := by
          intro m eta
          have hmem : eta ∈ Submodule.span B
              (Set.range (exteriorPower.ιMulti B p : (Fin p → Omega) → ⋀[B]^p Omega)) := by
            rw [exteriorPower.ιMulti_span]
            exact Submodule.mem_top
          revert m
          induction hmem using Submodule.span_induction with
          | mem eta heta =>
              obtain ⟨omega, rfl⟩ := heta
              intro m
              exact hgen m omega
          | zero => intro m; simp [f, g, c, eSrc]
          | add eta y hη hy hfy hgy =>
              intro m
              rw [TensorProduct.tmul_add, map_add, map_add, hfy m, hgy m]
          | smul b eta hη hη' =>
              intro m
              rw [TensorProduct.tmul_smul]
              exact hη' (b • m)
        exact heta m eta
  have hh := congrArg (fun F : (M ⊗[B] (⋀[B]^p Omega)) →+ _ => F (eSrc x)) hfg
  simpa [f, g, c, eSrc] using hh

end BaseChangeDeRham

end Crystalline

end

add_to_stacks 07KJ "integrability after base change" Crystalline.baseChange_isIntegrable
add_to_stacks 07KJ "canonical map of de Rham complexes"
  Crystalline.existsUnique_baseChangeDeRhamMap
