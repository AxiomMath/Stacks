module

public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatBaseChange

/-!
# Trace elements of relative dualizing modules

Let `A → B` be a flat quasi-finite map of Noetherian rings. An element `τ` of the relative
dualizing module `ω_{B/A}` is a *trace element* when, for every Noetherian `A`-algebra `A₁` such
that `B₁ = A₁ ⊗_A B` decomposes as a product `C × D` with `A₁ → C` finite, the image of `τ` in
`ω_{C/A₁}` is `Trace_{C/A₁}`.

Two ingredients are needed to say this. The passage `ω_{B/A} → ω_{B₁/A₁}` is the base-change map
of Tag 0BVB. The passage `ω_{B₁/A₁} → ω_{C/A₁}` is the first component of the product
decomposition of Tag 0BT5; it is built here directly as
`Stacks.Discriminant.finiteFactorRestriction`, characterized on pure tensors by the
finite-projective trace of the intermediate algebra, so that the map does not depend on any
auxiliary choice.

## Main definitions

* `Stacks.Discriminant.finiteFactorRestriction` is the canonical restriction of a relative
  dualizing element to a finite direct factor after base change, bundled with its pure-tensor
  characterization.
* `Stacks.Discriminant.IsTraceElement` is the trace-element predicate of Tag 0BT6.

## Implementation notes

The finite-open factorization used to represent the dualizing module stays explicit. A product
decomposition is an algebra equivalence `A₁ ⊗_A B ≃ C × D`, not a literal equality of rings, and
the restriction map is pinned down by the equation

`h (f ⊗ b) c = f (Trace_{C/B'₁} ((e b)₁ · c))`

on pure tensors, where `B'₁` is the intermediate algebra of the base-changed factorization. This
is the content of the subtype in `finiteFactorRestriction`: the map is not merely asserted to
exist, it is asserted to satisfy that formula, so `IsTraceElement` is a statement about the
trace and not about an arbitrary linear map.

The scalar tower `A₁ → B'₁ → C` is not a hypothesis: it follows from the compatibility
`hcompat` between the algebra structure on `C` over `B'₁` and the decomposition `e`, together
with the scalar tower of the base-changed factorization.

## References

* [Stacks Project, Tag 0BT6](https://stacks.math.columbia.edu/tag/0BT6)
* [Stacks Project, Tag 0BT5](https://stacks.math.columbia.edu/tag/0BT5)
* [Stacks Project, Tag 0BVB](https://stacks.math.columbia.edu/tag/0BVB)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v w x y z

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-- The canonical restriction of a relative dualizing element to a finite direct factor of the
target, together with the pure-tensor formula that characterizes it. This is the general form,
stated for an arbitrary finite-open factorization `G` of `A₁ → B₁` and a product decomposition
`B₁ ≃ C × D`; `finiteFactorRestriction` is its instance at a base-changed factorization. -/
def factorRestriction
    {A₁ : Type x} {B₁ : Type v} [CommRing A₁] [CommRing B₁] [Algebra A₁ B₁]
    (G : FiniteOpenFactorization.{x, v, w} A₁ B₁)
    (C : Type y) (D : Type z) [CommRing C] [CommRing D]
    [Algebra A₁ C] [Algebra A₁ D]
    (e : B₁ ≃ₐ[A₁] (C × D))
    [Algebra G.middle C]
    (hcompat : ∀ a : G.middle, algebraMap G.middle C a = (e (algebraMap G.middle B₁ a)).1)
    [Module.Finite G.middle C] [Module.Projective G.middle C] :
    letI : Module A₁ (dualizingModule G) := Module.compHom _ (algebraMap A₁ B₁)
    { h : dualizingModule G →ₗ[A₁] Module.Dual A₁ C //
      ∀ (f : Module.Dual A₁ G.middle) (b : B₁) (c : C),
        h (dualizingModule.tmul G f b) c =
          f ((finiteProjectiveTrace G.middle C)
            (Algebra.lmul G.middle C ((e b).1 * c))) } := by
  letI : Module A₁ (dualizingModule G) := Module.compHom _ (algebraMap A₁ B₁)
  -- The scalar tower `A₁ → B'₁ → C` is forced by `hcompat`; it is not a hypothesis.
  have htower : ∀ a₁ : A₁,
      algebraMap A₁ C a₁ = algebraMap G.middle C (algebraMap A₁ G.middle a₁) := by
    intro a₁
    rw [hcompat, ← IsScalarTower.algebraMap_apply A₁ G.middle B₁ a₁, AlgEquiv.commutes]
    rfl
  letI : IsScalarTower A₁ G.middle C := IsScalarTower.of_algebraMap_eq htower
  letI : Module G.middle (Module.Dual A₁ C) := Module.compHom _ (algebraMap G.middle C)
  -- `T` is the `B'₁`-valued trace of multiplication on the finite projective factor `C`.
  let T : C →ₗ[G.middle] G.middle :=
    (finiteProjectiveTrace G.middle C).comp (Algebra.lmul G.middle C).toLinearMap
  have hT (c₁ : G.middle) (c : C) : T (algebraMap G.middle C c₁ * c) = c₁ * T c := by
    have h := T.map_smul c₁ c
    rwa [Algebra.smul_def, smul_eq_mul] at h
  -- `mk f b` is the functional `c ↦ f (T ((e b).1 * c))`.
  let mk : Module.Dual A₁ G.middle → B₁ → Module.Dual A₁ C := fun f b =>
    f.comp ((T.restrictScalars A₁).comp (Algebra.lmul A₁ C ((e b).1)))
  have hmk (f : Module.Dual A₁ G.middle) (b : B₁) (c : C) :
      mk f b c = f (T ((e b).1 * c)) := rfl
  let inner : Module.Dual A₁ G.middle → (B₁ →ₗ[G.middle] Module.Dual A₁ C) := fun f =>
    { toFun := mk f
      map_add' := by
        intro b b'
        ext c
        simp only [hmk, LinearMap.add_apply, map_add, Prod.fst_add, add_mul]
      map_smul' := by
        intro c₁ b
        ext c
        have hc₁ : (e (c₁ • b)).1 = algebraMap G.middle C c₁ * (e b).1 := by
          rw [Algebra.smul_def, map_mul, Prod.fst_mul, ← hcompat]
        change f (T ((e (c₁ • b)).1 * c)) =
          f (T ((e b).1 * (algebraMap G.middle C c₁ * c)))
        rw [hc₁]
        ring_nf }
  let bil : Module.Dual A₁ G.middle →ₗ[G.middle] B₁ →ₗ[G.middle] Module.Dual A₁ C :=
    { toFun := inner
      map_add' := by
        intro f g
        ext b c
        change (f + g) (T ((e b).1 * c)) = f (T ((e b).1 * c)) + g (T ((e b).1 * c))
        rfl
      map_smul' := by
        intro c₁ f
        ext b c
        change f (c₁ * T ((e b).1 * c)) = f (T ((e b).1 * (algebraMap G.middle C c₁ * c)))
        rw [show (e b).1 * (algebraMap G.middle C c₁ * c) =
          algebraMap G.middle C c₁ * ((e b).1 * c) by ring, hT] }
  letI : Module G.middle (dualizingModule G) := TensorProduct.leftModule
  let h0 : dualizingModule G →ₗ[G.middle] Module.Dual A₁ C := TensorProduct.lift bil
  have hh0 (f : Module.Dual A₁ G.middle) (b : B₁) (c : C) :
      h0 (dualizingModule.tmul G f b) c = f (T ((e b).1 * c)) := rfl
  refine ⟨{ toFun := h0, map_add' := h0.map_add, map_smul' := ?_ }, hh0⟩
  intro a₁ u
  induction u using dualizingModule.induction_on with
  | add u u' hu hu' =>
      change h0 (a₁ • (u + u')) = a₁ • h0 (u + u')
      rw [smul_add, map_add, map_add, hu, hu', smul_add]
      rfl
  | tmul f b =>
      ext c
      change h0 ((algebraMap A₁ B₁ a₁) • dualizingModule.tmul G f b) c =
        a₁ • h0 (dualizingModule.tmul G f b) c
      rw [dualizingModule.smul_tmul, hh0, hh0, smul_eq_mul]
      have halg : (e (algebraMap A₁ B₁ a₁ * b)).1 =
          algebraMap G.middle C (algebraMap A₁ G.middle a₁) * (e b).1 := by
        rw [map_mul, Prod.fst_mul, AlgEquiv.commutes, ← htower]
        rfl
      rw [halg, show algebraMap G.middle C (algebraMap A₁ G.middle a₁) * (e b).1 * c =
        algebraMap G.middle C (algebraMap A₁ G.middle a₁) * ((e b).1 * c) by ring, hT]
      have h := f.map_smul a₁ (T ((e b).1 * c))
      rwa [Algebra.smul_def, smul_eq_mul] at h

/-- The canonical restriction of a relative dualizing element to a finite direct factor
after base change, together with the pure-tensor formula that characterizes it. The formula
is the first component of the product map of Tag 0BT5, written through the finite-projective
trace of the factor over the intermediate algebra. -/
@[stacks 0BT6 "the restriction of a dualizing element to a finite direct factor"]
def finiteFactorRestriction
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁]
    (C : Type y) (D : Type z) [CommRing C] [CommRing D]
    [Algebra A₁ C] [Algebra A₁ D]
    (e : (A₁ ⊗[A] B) ≃ₐ[A₁] (C × D))
    [Algebra (FiniteOpenFactorization.baseChange F A₁).middle C]
    (hcompat : ∀ a : (FiniteOpenFactorization.baseChange F A₁).middle,
      algebraMap _ C a =
        (e (algebraMap _ (A₁ ⊗[A] B) a)).1)
    (hfinite : Module.Finite A₁ C)
    (hprojective : Module.Projective A₁ C)
    (hmfinite : Module.Finite
      (FiniteOpenFactorization.baseChange F A₁).middle C)
    (hmprojective : Module.Projective
      (FiniteOpenFactorization.baseChange F A₁).middle C) :
    let F₁ := FiniteOpenFactorization.baseChange F A₁
    letI : Module A₁ (dualizingModule F₁) :=
      Module.compHom _ (algebraMap A₁ (A₁ ⊗[A] B))
    { h : dualizingModule F₁ →ₗ[A₁] Module.Dual A₁ C //
      letI : Module.Finite F₁.middle C := hmfinite
      letI : Module.Projective F₁.middle C := hmprojective
      ∀ (f : Module.Dual A₁ F₁.middle) (b : A₁ ⊗[A] B) (c : C),
        h (dualizingModule.tmul F₁ f b) c =
          f ((finiteProjectiveTrace F₁.middle C)
            (Algebra.lmul F₁.middle C ((e b).1 * c))) } :=
  letI := hfinite
  letI := hprojective
  letI := hmfinite
  letI := hmprojective
  factorRestriction (FiniteOpenFactorization.baseChange F A₁) C D e hcompat

/-- **Stacks Project, Tag 0BT6.** A trace element is an element of the relative dualizing
module whose image in every finite direct factor, after an arbitrary Noetherian base change,
is the finite-projective trace of that factor. -/
@[stacks 0BT6 "trace_element_property"]
def IsTraceElement
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Flat A B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (τ : dualizingModule F) : Prop :=
  ∀ (A₁ : Type x) [CommRing A₁] [Algebra A A₁] [IsNoetherianRing A₁]
    (C : Type y) (D : Type z) [CommRing C] [CommRing D]
    [Algebra A₁ C] [Algebra A₁ D]
    (e : (A₁ ⊗[A] B) ≃ₐ[A₁] (C × D))
    (hfinite : Module.Finite A₁ C),
    let F₁ := FiniteOpenFactorization.baseChange F A₁
    letI : Algebra F₁.middle C :=
      ((RingHom.fst C D).comp
        (e.toRingEquiv.toRingHom.comp F₁.algebraTarget.algebraMap)).toAlgebra
    ∃ (hprojective : Module.Projective A₁ C),
    letI : Module.Projective A₁ C := hprojective
    letI : Module A₁ (dualizingModule F₁) :=
      Module.compHom _ (algebraMap A₁ (A₁ ⊗[A] B))
    ∃ (hmfinite : Module.Finite F₁.middle C)
      (hmprojective : Module.Projective F₁.middle C),
    (finiteFactorRestriction F A₁ C D e (by intro; rfl) hfinite hprojective
      hmfinite hmprojective).1
        (dualizingModule.baseChange F A₁ τ) =
        (finiteProjectiveTrace A₁ C).comp
          (Algebra.lmul A₁ C).toLinearMap

end Stacks.Discriminant

end
