module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamPairFunctoriality

/-!
# Endomorphisms of the de Rham complex induced by endomorphisms of the one-forms

Let `A` be a ring, `(B, J, δ)` a divided power ring which is an `A`-algebra and `M` a
`B`-module.  A `B`-linear endomorphism `ε` of `Ω_B = Ω_{B/A,δ}` induces, in every degree `p`, the
`A`-linear endomorphism

`M ⊗_B Ω^p_{B/A,δ} → M ⊗_B Ω^p_{B/A,δ}`,   `m ⊗ ω ↦ m ⊗ (⋀^p ε)(ω)`

of the degree-`p` term of the de Rham complex (`Crystalline.DeRhamPair.formsEndo`).  It is the
identity for `ε = 1` and zero for `ε = 0` in positive degrees, and it commutes with the maps of
de Rham complexes induced by a morphism of pairs whenever `ε` commutes with the map of one-forms
(`Crystalline.DeRhamPair.termMap_formsEndo`).

Applied to the projections of `Ω_B` onto the parts of a decomposition indexed by the vertices of a
simplex, these are the support projections of the columns of the Čech–de Rham double complex of
a crystal ([Stacks, Tag 07LA]).

## Main definitions

* `Crystalline.DeRhamPair.formsEndo` — `m ⊗ ω ↦ m ⊗ (⋀^p ε)(ω)`.
* `Crystalline.DeRhamPair.formsEndoHom` — the same, as an endomorphism of the degree-`p` term of
  `Crystalline.DeRhamPair.oneVariableSourceDeRhamComplex` in `ModuleCat A`.

## Main results

* `Crystalline.DeRhamPair.formsEndo_id`, `Crystalline.DeRhamPair.formsEndo_zero`.
* `Crystalline.DeRhamPair.termMap_formsEndo` — compatibility with the maps of morphisms of pairs.

## References

* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
-/

@[expose] public noncomputable section

open CategoryTheory
open DividedPowers
open scoped TensorProduct
open Stacks.DeRham.DifferentialDescent

universe u w

namespace Crystalline.DeRhamPair

variable {A : Type u} [CommRing A]

section Endo

variable {B : DividedPowerRing.{u}} [Algebra A B] {M : Type w} [AddCommGroup M]
  [Module (B : Type u) M]

/-- **The endomorphism `m ⊗ ω ↦ m ⊗ (⋀^p ε)(ω)` of the degree-`p` term of the de Rham complex**
induced by a `B`-linear endomorphism `ε` of the divided power one-forms, as an `A`-linear map. -/
def formsEndo
    (ε : dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers) (p : ℕ) :
    RestrictScalars A (B : Type u)
        (M ⊗[(B : Type u)] ⋀[(B : Type u)]^p (dividedPowerDifferentials (A := A) B.dividedPowers))
      →ₗ[A] RestrictScalars A (B : Type u)
        (M ⊗[(B : Type u)] ⋀[(B : Type u)]^p
          (dividedPowerDifferentials (A := A) B.dividedPowers)) where
  toFun x := (RestrictScalars.addEquiv A (B : Type u) _).symm
    (LinearMap.lTensor M (exteriorPower.map p ε) (RestrictScalars.addEquiv A (B : Type u) _ x))
  map_add' x y := by simp
  map_smul' a x := by
    apply (RestrictScalars.addEquiv A (B : Type u) _).injective
    simp only [AddEquiv.apply_symm_apply, RestrictScalars.addEquiv_map_smul, RingHom.id_apply,
      map_smul]

/-- `formsEndo` read through the restriction of scalars. -/
theorem formsEndo_apply
    (ε : dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers) (p : ℕ) (x) :
    RestrictScalars.addEquiv A (B : Type u) _ (formsEndo (M := M) ε p x) =
      LinearMap.lTensor M (exteriorPower.map p ε) (RestrictScalars.addEquiv A (B : Type u) _ x) :=
  AddEquiv.apply_symm_apply _ _

/-- `formsEndo ε p x = y` can be checked after passing to the tensor product. -/
private theorem formsEndo_eq_iff
    {ε : dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers} {p : ℕ} {x y} :
    formsEndo (M := M) ε p x = y ↔
      LinearMap.lTensor M (exteriorPower.map p ε) (RestrictScalars.addEquiv A (B : Type u) _ x) =
        RestrictScalars.addEquiv A (B : Type u) _ y := by
  rw [← (RestrictScalars.addEquiv A (B : Type u) _).apply_eq_iff_eq, formsEndo_apply]

/-- `formsEndo` of the identity is the identity. -/
theorem formsEndo_id (p : ℕ) :
    formsEndo (A := A) (B := B) (M := M) LinearMap.id p = LinearMap.id :=
  LinearMap.ext fun x ↦ by
    rw [formsEndo_eq_iff, exteriorPower.map_id, LinearMap.lTensor_id]; rfl

/-- The `p`-th exterior power of the zero map vanishes in positive degree. -/
theorem _root_.exteriorPower.map_zero_of_pos {R N N' : Type*} [CommRing R] [AddCommGroup N]
    [Module R N] [AddCommGroup N'] [Module R N'] {p : ℕ} (hp : 0 < p) :
    exteriorPower.map p (0 : N →ₗ[R] N') = 0 := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun m ↦ ?_)
  rw [LinearMap.compAlternatingMap_apply, LinearMap.compAlternatingMap_apply,
    exteriorPower.map_apply_ιMulti, LinearMap.zero_apply]
  exact AlternatingMap.map_coord_zero _ ⟨0, hp⟩ rfl

/-- `formsEndo` of the zero map is zero in positive degree. -/
theorem formsEndo_zero {p : ℕ} (hp : 0 < p) : formsEndo (A := A) (B := B) (M := M) 0 p = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  rw [formsEndo_eq_iff, exteriorPower.map_zero_of_pos hp, LinearMap.lTensor_zero]; rfl

/-- `formsEndo` is compatible with composition of endomorphisms. -/
theorem formsEndo_comp
    (ε ε' : dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers) (p : ℕ) (x) :
    formsEndo (M := M) (ε ∘ₗ ε') p x = formsEndo ε p (formsEndo ε' p x) := by
  refine (RestrictScalars.addEquiv A (B : Type u) _).injective ?_
  rw [formsEndo_apply, formsEndo_apply, formsEndo_apply, exteriorPower.map_comp,
    LinearMap.lTensor_comp, LinearMap.comp_apply]

end Endo

section Compat

variable {B C : DividedPowerRing.{u}} [Algebra A B] [Algebra A C]
  (f : (B : Type u) →ₐ[A] C) (hf : IsDPMorphism B.dividedPowers C.dividedPowers f.toRingHom)
  {M : Type w} [AddCommGroup M] [Module (B : Type u) M]
  {N : Type w} [AddCommGroup N] [Module (C : Type u) N]
  (μ : M →ₛₗ[f.toRingHom] N)
  {ε : dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
    dividedPowerDifferentials (A := A) B.dividedPowers}
  {ε' : dividedPowerDifferentials (A := A) C.dividedPowers →ₗ[(C : Type u)]
    dividedPowerDifferentials (A := A) C.dividedPowers}

/-- The map of forms induced by `f` commutes with the exterior powers of two endomorphisms of the
one-forms which commute with the map of one-forms. -/
theorem formsMap_map (hε : ∀ ω, oneFormsMap f hf (ε ω) = ε' (oneFormsMap f hf ω)) (p : ℕ)
    (ω : ⋀[(B : Type u)]^p (dividedPowerDifferentials (A := A) B.dividedPowers)) :
    formsMap f hf p (exteriorPower.map p ε ω) =
      exteriorPower.map p ε' (formsMap f hf p ω) := by
  have h : (formsMap f hf p).comp (exteriorPower.map p ε) =
      (exteriorPower.map p ε').comp (formsMap f hf p) :=
    ExteriorAlgebra.powMapₛₗ_ext fun v ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
        formsMap, mapDifferentialFormsOfDPMorphism_ιMulti,
        mapDifferentialFormsOfDPMorphism_ιMulti, exteriorPower.map_apply_ιMulti]
      exact congrArg _ (funext fun j ↦ hε (v j))
  exact DFunLike.congr_fun h ω

/-- **The maps of de Rham complexes induced by a morphism of pairs commute with `formsEndo`** of
two endomorphisms of the one-forms which commute with the map of one-forms. -/
theorem termMap_formsEndo (hε : ∀ ω, oneFormsMap f hf (ε ω) = ε' (oneFormsMap f hf ω))
    (p : ℕ) (x) :
    termMap f hf μ p (formsEndo ε p x) = formsEndo ε' p (termMap f hf μ p x) := by
  apply (RestrictScalars.addEquiv A (C : Type u) _).injective
  rw [termMap_apply, formsEndo_apply, formsEndo_apply, termMap_apply]
  obtain ⟨y, rfl⟩ := (RestrictScalars.addEquiv A (B : Type u) _).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul m ω =>
    rw [LinearMap.lTensor_tmul, tensorMap_tmul, tensorMap_tmul, LinearMap.lTensor_tmul,
      formsMap_map f hf hε]

/-- `termMap_formsEndo` as an equation of linear maps. -/
theorem termMap_comp_formsEndo (hε : ∀ ω, oneFormsMap f hf (ε ω) = ε' (oneFormsMap f hf ω))
    (p : ℕ) :
    termMap f hf μ p ∘ₗ formsEndo ε p = formsEndo ε' p ∘ₗ termMap f hf μ p :=
  LinearMap.ext (termMap_formsEndo f hf μ hε p)

end Compat

section Complex

variable (A) (B : DividedPowerRing.{u}) [Algebra A B] {M : Type w} [AddCommGroup M]
  [Module (B : Type u) M]

/-- **`formsEndo` as an endomorphism of the degree-`p` term of the de Rham complex** of a module
with integrable connection, in `ModuleCat A`. -/
def formsEndoHom (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (ε : dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers) (p : ℕ) :
    (oneVariableSourceDeRhamComplex A B nabla hint).X p ⟶
      (oneVariableSourceDeRhamComplex A B nabla hint).X p :=
  ConcreteCategory.ofHom (C := ModuleCat A) (formsEndo ε p)

/-- The underlying linear map of `formsEndoHom`. -/
theorem formsEndoHom_hom (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (ε : dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers) (p : ℕ) :
    (formsEndoHom A B nabla hint ε p).hom = formsEndo ε p := rfl

/-- `formsEndoHom` of the identity is the identity. -/
theorem formsEndoHom_id (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla) (p : ℕ) :
    formsEndoHom A B nabla hint LinearMap.id p = 𝟙 _ :=
  ModuleCat.hom_ext (formsEndo_id (B := B) p)

/-- `formsEndoHom` of the zero map is zero in positive degree. -/
theorem formsEndoHom_zero (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    {p : ℕ} (hp : 0 < p) :
    formsEndoHom A B nabla hint 0 p = 0 :=
  ModuleCat.hom_ext (formsEndo_zero (B := B) hp)

variable {A B} {C : DividedPowerRing.{u}} [Algebra A C]
  {N : Type w} [AddCommGroup N] [Module (C : Type u) N]

/-- **The maps of de Rham complexes induced by a horizontal morphism of pairs commute with
`formsEndoHom`** of endomorphisms of the one-forms commuting with the map of one-forms. -/
theorem deRhamMap_f_formsEndoHom (f : (B : Type u) →ₐ[A] C)
    (hf : IsDPMorphism B.dividedPowers C.dividedPowers f.toRingHom)
    (μ : M →ₛₗ[f.toRingHom] N)
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (nabla' : Connection A (C : Type u) (oneVariableBaseProjection A C) N)
    (hint' : Connection.IsIntegrable (oneVariableBaseSource A C) (oneVariableBaseProjection A C)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A C) nabla')
    (hμ : IsHorizontal f hf μ nabla nabla')
    {ε : dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers}
    {ε' : dividedPowerDifferentials (A := A) C.dividedPowers →ₗ[(C : Type u)]
      dividedPowerDifferentials (A := A) C.dividedPowers}
    (hε : ∀ ω, oneFormsMap f hf (ε ω) = ε' (oneFormsMap f hf ω)) (p : ℕ) :
    formsEndoHom A B nabla hint ε p ≫ (deRhamMap f hf μ nabla hint nabla' hint' hμ).f p =
      (deRhamMap f hf μ nabla hint nabla' hint' hμ).f p ≫ formsEndoHom A C nabla' hint' ε' p :=
  ModuleCat.hom_ext (termMap_comp_formsEndo f hf μ hε p)

end Complex

end Crystalline.DeRhamPair
