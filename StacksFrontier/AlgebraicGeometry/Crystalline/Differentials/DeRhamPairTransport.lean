module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.ConnectionTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamPairFunctoriality

/-!
# Horizontality of transported connections

Let `f : (B, I, δ) → (C, K, ε)` be a divided power morphism of `A`-algebras and let `∇`, `∇'` be
connections on a `B`-module `M` and a `C`-module `N`, relative to presentations
`π_B : Ω[B⁄A] → Ω_B` and `π_C : Ω[C⁄A] → Ω_C` of some modules of one-forms which are identified
with the divided power differentials by isomorphisms `e_B`, `e_C`.  If an `f`-semilinear map
`μ : M → N` carries `∇` to `∇'` along a map `ρ : Ω_B → Ω_C` which `e_B`, `e_C` turn into the map
`Ω_f` of divided power differentials, then `μ` is horizontal, in the sense of
`Crystalline.DeRhamPair.IsHorizontal`, for the transported connections
(`Crystalline.DeRhamPair.isHorizontal_transport`).

## References

* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe u w

namespace Crystalline.DeRhamPair

section Transport

variable {A : Type u} [CommRing A] {B C : DividedPowerRing.{u}} [Algebra A B] [Algebra A C]
  (f : (B : Type u) →ₐ[A] C) (hf : IsDPMorphism B.dividedPowers C.dividedPowers f.toRingHom)
  {M : Type w} [AddCommGroup M] [Module (B : Type u) M]
  {N : Type w} [AddCommGroup N] [Module (C : Type u) N]
  (μ : M →ₛₗ[f.toRingHom] N)
  {ΩB ΩC : Type u} [AddCommGroup ΩB] [Module (B : Type u) ΩB] [AddCommGroup ΩC]
  [Module (C : Type u) ΩC]
  {πB : Ω[(B : Type u)⁄A] →ₗ[(B : Type u)] ΩB} {πC : Ω[(C : Type u)⁄A] →ₗ[(C : Type u)] ΩC}
  (eB : ΩB ≃ₗ[(B : Type u)] dividedPowerDifferentials (A := A) B.dividedPowers)
  (heB : ∀ x, eB (πB x) = oneVariableBaseProjection A B x)
  (eC : ΩC ≃ₗ[(C : Type u)] dividedPowerDifferentials (A := A) C.dividedPowers)
  (heC : ∀ x, eC (πC x) = oneVariableBaseProjection A C x)

/-- **A map of pairs which is horizontal for two connections is horizontal for their transports
to the divided power differentials**: if `μ` carries `∇` to `∇'` along an additive map `R` of
the coefficient modules acting as `m ⊗ η ↦ μ m ⊗ ρ η`, and `ρ` corresponds to the map `Ω_f` of
divided power differentials under `e_B`, `e_C`, then `μ` is horizontal for the transported
connections. -/
theorem isHorizontal_transport (ρ : ΩB → ΩC)
    (hρ : ∀ η, eC (ρ η) = oneFormsMap f hf (eB η))
    (R : M ⊗[(B : Type u)] ΩB →+ N ⊗[(C : Type u)] ΩC)
    (hR : ∀ m η, R (m ⊗ₜ η) = μ m ⊗ₜ ρ η)
    (nabla : Connection A (B : Type u) πB M) (nabla' : Connection A (C : Type u) πC N)
    (hnat : ∀ m, nabla' (μ m) = R (nabla m)) :
    IsHorizontal f hf μ (nabla.transport eB heB) (nabla'.transport eC heC) := by
  intro m
  rw [Connection.transport_apply, Connection.transport_apply, hnat m]
  induction nabla m using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul n η =>
    rw [hR, TensorProduct.map_tmul, TensorProduct.map_tmul, tensorMap_tmul, LinearMap.id_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, hρ]

end Transport

/-! ### Composites, restriction of scalars, and degree zero -/

section Degreewise

variable {A : Type u} [CommRing A] {B C : DividedPowerRing.{u}} [Algebra A B] [Algebra A C]
  (f : (B : Type u) →ₐ[A] C) (hf : IsDPMorphism B.dividedPowers C.dividedPowers f.toRingHom)
  {M : Type w} [AddCommGroup M] [Module (B : Type u) M]
  {N : Type w} [AddCommGroup N] [Module (C : Type u) N]
  (μ : M →ₛₗ[f.toRingHom] N)

/-- The degreewise map of a morphism of pairs whose ring map agrees pointwise with a composite
`g ∘ f` is the composite of the degreewise maps. -/
theorem termMap_comp_of_eq {D : DividedPowerRing.{u}} [Algebra A D] (g : (C : Type u) →ₐ[A] D)
    (hg : IsDPMorphism C.dividedPowers D.dividedPowers g.toRingHom)
    (h : (B : Type u) →ₐ[A] D) (hh : IsDPMorphism B.dividedPowers D.dividedPowers h.toRingHom)
    (hgf : ∀ b, h b = g (f b))
    {L : Type w} [AddCommGroup L] [Module (D : Type u) L] (ν : N →ₛₗ[g.toRingHom] L)
    (κ : M →ₛₗ[h.toRingHom] L) (hκ : ∀ m, κ m = ν (μ m)) (p : ℕ) (x) :
    termMap h hh κ p x = termMap g hg ν p (termMap f hf μ p x) := by
  obtain rfl : h = g.comp f := AlgHom.ext hgf
  exact termMap_comp f hf μ g hg hh ν κ hκ p x

/-- An `f`-semilinear map, read as an `A`-linear map between the restrictions of scalars. -/
def restrictScalarsMap :
    RestrictScalars A (B : Type u) M →ₗ[A] RestrictScalars A (C : Type u) N where
  toFun x := (RestrictScalars.addEquiv A (C : Type u) N).symm
    (μ (RestrictScalars.addEquiv A (B : Type u) M x))
  map_add' x y := (congrArg _ ((congrArg μ (map_add _ x y)).trans (map_add μ _ _))).trans
    (map_add _ _ _)
  map_smul' a x := by
    apply (RestrictScalars.addEquiv A (C : Type u) N).injective
    simp only [AddEquiv.apply_symm_apply, RestrictScalars.addEquiv_map_smul, RingHom.id_apply,
      map_smulₛₗ]
    congr 1
    exact f.commutes a

/-- `restrictScalarsMap` read through the restriction of scalars. -/
theorem restrictScalarsMap_apply (x : RestrictScalars A (B : Type u) M) :
    RestrictScalars.addEquiv A (C : Type u) N (restrictScalarsMap f μ x) =
      μ (RestrictScalars.addEquiv A (B : Type u) M x) :=
  AddEquiv.apply_symm_apply _ _

omit [Algebra A B] in
/-- A linear equivalence of `B`-modules, read as an `A`-linear equivalence between the
restrictions of scalars. -/
def restrictScalarsEquiv {R : Type u} [CommRing R] [Algebra A R] {X Y : Type*} [AddCommGroup X]
    [Module R X] [AddCommGroup Y] [Module R Y] (e : X ≃ₗ[R] Y) :
    RestrictScalars A R X ≃ₗ[A] RestrictScalars A R Y where
  toFun x := (RestrictScalars.addEquiv A R Y).symm (e (RestrictScalars.addEquiv A R X x))
  invFun y := (RestrictScalars.addEquiv A R X).symm (e.symm (RestrictScalars.addEquiv A R Y y))
  map_add' x y := by simp
  map_smul' a x := by
    apply (RestrictScalars.addEquiv A R Y).injective
    simp only [AddEquiv.apply_symm_apply, RestrictScalars.addEquiv_map_smul, RingHom.id_apply,
      map_smul]
  left_inv x := by simp
  right_inv y := by simp

/-- `restrictScalarsEquiv` read through the restriction of scalars. -/
theorem restrictScalarsEquiv_apply {R : Type u} [CommRing R] [Algebra A R] {X Y : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (e : X ≃ₗ[R] Y)
    (x : RestrictScalars A R X) :
    RestrictScalars.addEquiv A R Y (restrictScalarsEquiv e x) =
      e (RestrictScalars.addEquiv A R X x) :=
  AddEquiv.apply_symm_apply _ _

variable (A) in
/-- **The degree-zero term of the de Rham complex of a module with connection is the module**:
`M ⊗_B ⋀^0 Ω¹_{B/A,δ} ≅ M`, `m ⊗ ω ↦ ω · m`, read as `A`-modules. -/
def degreeZeroEquiv (D : DividedPowerRing.{u}) [Algebra A D] (L : Type w) [AddCommGroup L]
    [Module (D : Type u) L] :
    RestrictScalars A (D : Type u) (L ⊗[(D : Type u)]
        ⋀[(D : Type u)]^0 (dividedPowerDifferentials (A := A) D.dividedPowers)) ≃ₗ[A]
      RestrictScalars A (D : Type u) L :=
  restrictScalarsEquiv ((TensorProduct.congr (LinearEquiv.refl (D : Type u) L)
    (exteriorPower.zeroEquiv (D : Type u) _)).trans (TensorProduct.rid (D : Type u) L))

/-- `degreeZeroEquiv` on a pure tensor. -/
theorem degreeZeroEquiv_tmul (D : DividedPowerRing.{u}) [Algebra A D] {L : Type w}
    [AddCommGroup L] [Module (D : Type u) L] (m : L)
    (ω : ⋀[(D : Type u)]^0 (dividedPowerDifferentials (A := A) D.dividedPowers)) :
    RestrictScalars.addEquiv A (D : Type u) L (degreeZeroEquiv A D L
        ((RestrictScalars.addEquiv A (D : Type u) _).symm (m ⊗ₜ ω))) =
      exteriorPower.zeroEquiv (D : Type u) _ ω • m := by
  rw [degreeZeroEquiv, restrictScalarsEquiv_apply, AddEquiv.apply_symm_apply,
    LinearEquiv.trans_apply, TensorProduct.congr_tmul, TensorProduct.rid_tmul,
    LinearEquiv.refl_apply]

/-- The map of divided power differential forms in degree zero is the ring map. -/
theorem zeroEquiv_formsMap
    (ω : ⋀[(B : Type u)]^0 (dividedPowerDifferentials (A := A) B.dividedPowers)) :
    exteriorPower.zeroEquiv (C : Type u) _ (formsMap f hf 0 ω) =
      f (exteriorPower.zeroEquiv (B : Type u) _ ω) := by
  have key : ∀ ω ∈ Submodule.span (B : Type u) (Set.range (exteriorPower.ιMulti (B : Type u) 0
      (M := dividedPowerDifferentials (A := A) B.dividedPowers))),
      exteriorPower.zeroEquiv (C : Type u) _ (formsMap f hf 0 ω) =
        f (exteriorPower.zeroEquiv (B : Type u) _ ω) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [formsMap, mapDifferentialFormsOfDPMorphism_ιMulti, exteriorPower.zeroEquiv_ιMulti,
        exteriorPower.zeroEquiv_ιMulti, map_one]
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul c x _ hx =>
      rw [map_smulₛₗ, map_smul, map_smul, hx, smul_eq_mul, smul_eq_mul, map_mul]
      rfl
  exact key ω (by rw [exteriorPower.ιMulti_span]; trivial)

/-- **The degree-zero identification is natural** for the maps of de Rham complexes. -/
theorem degreeZeroEquiv_termMap (x) :
    degreeZeroEquiv A C N (termMap f hf μ 0 x) =
      restrictScalarsMap f μ (degreeZeroEquiv A B M x) := by
  apply (RestrictScalars.addEquiv A (C : Type u) N).injective
  rw [restrictScalarsMap_apply]
  obtain ⟨y, rfl⟩ := (RestrictScalars.addEquiv A (B : Type u) _).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul m ω =>
    have hx : termMap f hf μ 0 ((RestrictScalars.addEquiv A (B : Type u) _).symm (m ⊗ₜ ω)) =
        (RestrictScalars.addEquiv A (C : Type u) _).symm (μ m ⊗ₜ formsMap f hf 0 ω) := rfl
    rw [hx, degreeZeroEquiv_tmul, degreeZeroEquiv_tmul, map_smulₛₗ, zeroEquiv_formsMap]
    rfl

end Degreewise

end Crystalline.DeRhamPair
