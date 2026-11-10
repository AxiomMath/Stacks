module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamExterior
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincareModuleQuasiIso

/-!
# Functoriality of the de Rham complex of a module with integrable connection

Let `A` be a ring and let `(B, I, δ)`, `(C, K, ε)` be divided power rings which are
`A`-algebras.  A *morphism of pairs* from `(M, ∇)` over `B` to `(N, ∇')` over `C` is a divided
power morphism `f : B → C` of `A`-algebras together with an `f`-semilinear map `μ : M → N` which
is *horizontal*: `∇'(μ m) = (μ ⊗ Ω_f)(∇ m)`.  It induces a map of de Rham complexes

`M ⊗_B Ω^*_{B/A,δ} ⟶ N ⊗_C Ω^*_{C/A,ε}`,   `m ⊗ ω ↦ μ m ⊗ Ω_f(ω)`,

of complexes of `A`-modules (`Crystalline.DeRhamPair.deRhamMap`), functorially
(`deRhamMap_id`, `deRhamMap_comp`).  This is the functoriality the Čech–de Rham double complex of
a crystal runs on: its cosimplicial structure maps are the maps induced by the projections of the
Čech nerve.

## Main definitions

* `Crystalline.DeRhamPair.termMap` — the degreewise map `m ⊗ ω ↦ μ m ⊗ Ω_f(ω)`.
* `Crystalline.DeRhamPair.deRhamMap` — the induced map of de Rham complexes.

## Main results

* `Crystalline.DeRhamPair.deRhamDifferential_eq` — the de Rham differential the extension of a
  connection uses is the divided power de Rham differential.
* `Crystalline.DeRhamPair.termMap_comm` — the degreewise map commutes with the differentials.
* `Crystalline.DeRhamPair.deRhamMap_id`, `Crystalline.DeRhamPair.deRhamMap_comp` — functoriality.

## References

* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
-/

@[expose] public noncomputable section

open CategoryTheory
open DividedPowers
open scoped TensorProduct
open Stacks.DeRham.DifferentialDescent

universe u w

namespace Crystalline.DeRhamPair

variable (A : Type u) [CommRing A]

/-- **The de Rham differential an extension of a connection uses is the divided power de Rham
differential**: both are determined by the rule on the standard generators. -/
theorem deRhamDifferential_eq (B : DividedPowerRing.{u}) [Algebra A B] {M : Type w}
    [AddCommGroup M] [Module (B : Type u) M]
    {nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M}
    (E : ExtendedConnection (oneVariableBaseSource A B) (oneVariableBaseProjection A B) nabla) :
    E.deRhamDifferential = (dividedPowerDeRhamComplex (A := A) B.dividedPowers).differential := by
  have h := Classical.choose_spec (exists_unique_quotient_deRhamDifferential
    (oneVariableBaseSource A B) (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
    (oneVariableBaseGenerationHypothesis A B))
  have hE := h.2.2.1 _ E.commutes
  let C : DividedPowerDeRhamComplex (A := A) B.dividedPowers :=
    { differential := E.deRhamDifferential
      differential_generator := fun i f ↦ by
        rw [hE]
        exact h.2.1 i f
      differential_squared := fun i ↦ by
        rw [hE]
        exact h.2.2.2 i }
  exact congrArg DividedPowerDeRhamComplex.differential C.unique

variable {A} {B C : DividedPowerRing.{u}} [Algebra A B] [Algebra A C]
  (f : (B : Type u) →ₐ[A] C) (hf : IsDPMorphism B.dividedPowers C.dividedPowers f.toRingHom)
  {M : Type w} [AddCommGroup M] [Module (B : Type u) M]
  {N : Type w} [AddCommGroup N] [Module (C : Type u) N]
  (μ : M →ₛₗ[f.toRingHom] N)

/-- The map of divided power differential forms induced by `f`, in degree `p`. -/
abbrev formsMap (p : ℕ) :
    dividedPowerDifferentialForms (A := A) B.dividedPowers p →ₛₗ[f.toRingHom]
      dividedPowerDifferentialForms (A := A) C.dividedPowers p :=
  mapDifferentialFormsOfDPMorphism (A := A) (J := B.ideal) (delta := B.dividedPowers)
    C.dividedPowers f hf p

/-- The map of divided power differentials induced by `f`. -/
abbrev oneFormsMap :
    dividedPowerDifferentials (A := A) B.dividedPowers →ₛₗ[f.toRingHom]
      dividedPowerDifferentials (A := A) C.dividedPowers :=
  mapDifferentialsOfDPMorphismₛₗ (A := A) (J := B.ideal) (delta := B.dividedPowers)
    C.dividedPowers f hf

/-- The tensor product of two `f`-semilinear maps, `m ⊗ x ↦ μ m ⊗ ν x`, as an additive map. -/
def tensorMap {P : Type*} [AddCommGroup P] [Module (B : Type u) P] {Q : Type*} [AddCommGroup Q]
    [Module (C : Type u) Q] (ν : P →ₛₗ[f.toRingHom] Q) :
    M ⊗[(B : Type u)] P →+ N ⊗[(C : Type u)] Q :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m ↦ (TensorProduct.mk (C : Type u) N Q (μ m)).toAddMonoidHom.comp
        ν.toAddMonoidHom)
      (fun m m' ↦ by
        ext x
        change μ (m + m') ⊗ₜ[(C : Type u)] ν x = μ m ⊗ₜ ν x + μ m' ⊗ₜ ν x
        rw [map_add, TensorProduct.add_tmul]))
    (fun b m x ↦ by
      change μ (b • m) ⊗ₜ[(C : Type u)] ν x = μ m ⊗ₜ[(C : Type u)] ν (b • x)
      rw [map_smulₛₗ, map_smulₛₗ, TensorProduct.smul_tmul])

/-- `tensorMap` on a pure tensor. -/
@[simp]
theorem tensorMap_tmul {P : Type*} [AddCommGroup P] [Module (B : Type u) P] {Q : Type*}
    [AddCommGroup Q] [Module (C : Type u) Q] (ν : P →ₛₗ[f.toRingHom] Q) (m : M) (x : P) :
    tensorMap f μ ν (m ⊗ₜ x) = μ m ⊗ₜ ν x := rfl

/-- The tensor product of two semilinear maps is semilinear. -/
theorem tensorMap_smul {P : Type*} [AddCommGroup P] [Module (B : Type u) P] {Q : Type*}
    [AddCommGroup Q] [Module (C : Type u) Q] (ν : P →ₛₗ[f.toRingHom] Q) (b : (B : Type u))
    (z : M ⊗[(B : Type u)] P) : tensorMap f μ ν (b • z) = f b • tensorMap f μ ν z := by
  induction z using TensorProduct.inductionOn with
  | tmul m x =>
    rw [TensorProduct.smul_tmul', tensorMap_tmul, tensorMap_tmul, map_smulₛₗ,
      TensorProduct.smul_tmul']
    rfl
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **Horizontality** of `μ`: it carries the connection of `M` to the connection of `N`. -/
def IsHorizontal (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (nabla' : Connection A (C : Type u) (oneVariableBaseProjection A C) N) : Prop :=
  ∀ m : M, nabla' (μ m) = tensorMap f μ (oneFormsMap f hf) (nabla m)

/-- **The degreewise map of de Rham complexes**, `m ⊗ ω ↦ μ m ⊗ Ω_f(ω)`, as an `A`-linear map
between the terms read as `A`-modules. -/
def termMap (p : ℕ) :
    RestrictScalars A (B : Type u)
        (M ⊗[(B : Type u)] ⋀[(B : Type u)]^p (dividedPowerDifferentials (A := A) B.dividedPowers))
      →ₗ[A] RestrictScalars A (C : Type u)
        (N ⊗[(C : Type u)] ⋀[(C : Type u)]^p
          (dividedPowerDifferentials (A := A) C.dividedPowers)) where
  toFun x := (RestrictScalars.addEquiv A (C : Type u) _).symm
    (tensorMap f μ (formsMap f hf p) (RestrictScalars.addEquiv A (B : Type u) _ x))
  map_add' x y := by simp
  map_smul' a x := by
    apply (RestrictScalars.addEquiv A (C : Type u) _).injective
    simp only [AddEquiv.apply_symm_apply, RestrictScalars.addEquiv_map_smul, RingHom.id_apply]
    rw [tensorMap_smul]
    congr 1
    exact f.commutes a

/-- `termMap` read through the restriction of scalars. -/
theorem termMap_apply (p : ℕ) (x) :
    RestrictScalars.addEquiv A (C : Type u) _ (termMap f hf μ p x) =
      tensorMap f μ (formsMap f hf p) (RestrictScalars.addEquiv A (B : Type u) _ x) :=
  AddEquiv.apply_symm_apply _ _

/-- The extension of a connection over a divided power ring to all degrees. -/
abbrev ext (D : DividedPowerRing.{u}) [Algebra A D] {L : Type w} [AddCommGroup L]
    [Module (D : Type u) L] (nabla : Connection A (D : Type u) (oneVariableBaseProjection A D) L) :
    ExtendedConnection (oneVariableBaseSource A D) (oneVariableBaseProjection A D) nabla :=
  extendedConnection (oneVariableBaseSource A D) (oneVariableBaseProjection A D)
    (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A D) nabla

/-- The maps of forms respect left exterior multiplication by a one-form, on the values of a
connection. -/
theorem tensorMap_map_leftWedge (p : ℕ)
    (ω : ⋀[(B : Type u)]^p (dividedPowerDifferentials (A := A) B.dividedPowers))
    (z : M ⊗[(B : Type u)] dividedPowerDifferentials (A := A) B.dividedPowers) :
    tensorMap f μ (formsMap f hf (p + 1))
        (TensorProduct.map LinearMap.id ((leftWedge p).flip ω) z) =
      TensorProduct.map LinearMap.id ((leftWedge p).flip (formsMap f hf p ω))
        (tensorMap f μ (oneFormsMap f hf) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul m η =>
    rw [TensorProduct.map_tmul, tensorMap_tmul, tensorMap_tmul, TensorProduct.map_tmul]
    simp only [LinearMap.id_apply, LinearMap.flip_apply]
    congr 1
    exact mapDifferentialFormsOfDPMorphism_leftWedge (A := A) (J := B.ideal)
      (hJ := B.dividedPowers) C.dividedPowers f hf p η ω
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Induction principle for `RestrictScalars` of a tensor product, on pure tensors. -/
private theorem restrictScalars_tensor_induction {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {M P : Type*} [AddCommGroup M] [Module S M] [AddCommGroup P] [Module S P]
    {motive : RestrictScalars R S (M ⊗[S] P) → Prop}
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (tmul : ∀ m ω, motive ((RestrictScalars.addEquiv R S _).symm (m ⊗ₜ ω))) (x) : motive x := by
  obtain ⟨y, rfl⟩ := (RestrictScalars.addEquiv R S _).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | tmul m ω => exact tmul m ω
  | add y z hy hz => rw [map_add]; exact add _ _ hy hz

/-- **The degreewise map commutes with the de Rham differentials** of a horizontal map. -/
theorem termMap_comm (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (nabla' : Connection A (C : Type u) (oneVariableBaseProjection A C) N)
    (hμ : IsHorizontal f hf μ nabla nabla') (p : ℕ) (x) :
    termMap f hf μ (p + 1) ((ext B nabla).toLinearMap p x) =
      (ext C nabla').toLinearMap p (termMap f hf μ p x) := by
  apply (RestrictScalars.addEquiv A (C : Type u) _).injective
  rw [termMap_apply]
  induction x using restrictScalars_tensor_induction with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul m ω =>
    change tensorMap f μ (formsMap f hf (p + 1))
        (RestrictScalars.addEquiv A (B : Type u) _ ((ext B nabla).toLinearMap p (m ⊗ₜ ω))) =
      RestrictScalars.addEquiv A (C : Type u) _
        ((ext C nabla').toLinearMap p (μ m ⊗ₜ formsMap f hf p ω))
    rw [(ext B nabla).map_tmul p m ω, (ext C nabla').map_tmul p (μ m) (formsMap f hf p ω),
      map_add, tensorMap_tmul, tensorMap_map_leftWedge, hμ m, deRhamDifferential_eq,
      deRhamDifferential_eq]
    congr 2
    exact mapDifferentialFormsOfDPMorphism_deRham (A := A) (J := B.ideal)
      (hJ := B.dividedPowers) C.dividedPowers f hf p ω

/-- **The map of de Rham complexes induced by a morphism of pairs.** -/
def deRhamMap (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (nabla' : Connection A (C : Type u) (oneVariableBaseProjection A C) N)
    (hint' : Connection.IsIntegrable (oneVariableBaseSource A C) (oneVariableBaseProjection A C)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A C) nabla')
    (hμ : IsHorizontal f hf μ nabla nabla') :
    oneVariableSourceDeRhamComplex A B nabla hint ⟶
      oneVariableSourceDeRhamComplex A C nabla' hint' where
  f p := ConcreteCategory.ofHom (C := ModuleCat A) (termMap f hf μ p)
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      oneVariableSourceDeRhamComplex_hom_d, oneVariableSourceDeRhamComplex_hom_d]
    exact (termMap_comm f hf μ nabla nabla' hμ p x).symm

/-- The degree `p` component of `deRhamMap`. -/
theorem deRhamMap_f (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (nabla' : Connection A (C : Type u) (oneVariableBaseProjection A C) N)
    (hint' : Connection.IsIntegrable (oneVariableBaseSource A C) (oneVariableBaseProjection A C)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A C) nabla')
    (hμ : IsHorizontal f hf μ nabla nabla') (p : ℕ) :
    ((deRhamMap f hf μ nabla hint nabla' hint' hμ).f p).hom = termMap f hf μ p := rfl

/-! ### Functoriality -/

omit [Algebra A C] in
/-- The degreewise map of the identity morphism of pairs is the identity. -/
theorem termMap_id (hid : IsDPMorphism B.dividedPowers B.dividedPowers (AlgHom.id A B).toRingHom)
    (κ : M →ₛₗ[(AlgHom.id A (B : Type u)).toRingHom] M) (hκ : ∀ m, κ m = m) (p : ℕ) (x) :
    termMap (AlgHom.id A (B : Type u)) hid κ p x = x := by
  apply (RestrictScalars.addEquiv A (B : Type u) _).injective
  rw [termMap_apply]
  induction x using restrictScalars_tensor_induction with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul m ω =>
    rw [AddEquiv.apply_symm_apply, tensorMap_tmul, hκ]
    congr 1
    exact mapDifferentialFormsOfDPMorphism_id (A := A) (J := B.ideal) (delta := B.dividedPowers)
      p hid ω

/-- The degreewise maps compose. -/
theorem termMap_comp {D : DividedPowerRing.{u}} [Algebra A D] (g : (C : Type u) →ₐ[A] D)
    (hg : IsDPMorphism C.dividedPowers D.dividedPowers g.toRingHom)
    (hgf : IsDPMorphism B.dividedPowers D.dividedPowers (g.comp f).toRingHom)
    {L : Type w} [AddCommGroup L] [Module (D : Type u) L] (ν : N →ₛₗ[g.toRingHom] L)
    (κ : M →ₛₗ[(g.comp f).toRingHom] L) (hκ : ∀ m, κ m = ν (μ m)) (p : ℕ) (x) :
    termMap (g.comp f) hgf κ p x = termMap g hg ν p (termMap f hf μ p x) := by
  apply (RestrictScalars.addEquiv A (D : Type u) _).injective
  rw [termMap_apply, termMap_apply, termMap_apply]
  induction x using restrictScalars_tensor_induction with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul m ω =>
    rw [AddEquiv.apply_symm_apply, tensorMap_tmul, tensorMap_tmul, tensorMap_tmul, hκ]
    congr 1
    exact mapDifferentialFormsOfDPMorphism_comp (A := A) (J := B.ideal) (delta := B.dividedPowers)
      C.dividedPowers D.dividedPowers f g hf hg hgf p ω

end Crystalline.DeRhamPair
