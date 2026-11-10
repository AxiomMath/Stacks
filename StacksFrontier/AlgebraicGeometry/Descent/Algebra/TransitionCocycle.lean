module

public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.SchemeEffective
public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.SpecOverFullyFaithful

/-!
# The cocycle condition for an algebra transition, reduced to one generator

In `Stacks.AlgebraDescent.exists_subalgebra_tensorEquiv` the cocycle condition on a transition
`θ : B ⊗[R] A ≃ₐ[R] A ⊗[R] B` is an equality of `R`-**linear** maps on `(B ⊗[R] A) ⊗[R] A`,
namely `cocycle12 θ ∘ₗ cocycle01 θ = cocycle02 θ`. This file relates it to an equality of
morphisms of schemes. The three maps of the cocycle triangle are realized as `R`-algebra maps,
and then:

* an equality of `R`-algebra maps out of `(B ⊗[R] A) ⊗[R] A` only has to be checked on the three
  families of generators `(b ⊗ 1) ⊗ 1`, `(1 ⊗ a) ⊗ 1`, `(1 ⊗ 1) ⊗ a`;
* two of those three families are discharged outright by the hypotheses `hleft` and `hright`
  saying that `θ` is a morphism over `A ⊗[R] A`.

So the whole cocycle condition follows from the single equation on `(b ⊗ 1) ⊗ 1`
(`Stacks.AlgebraDescent.cocycle_of_flipGenerator`), and that equation is an identity of
`R`-algebra maps `B →ₐ[R] (A ⊗[R] A) ⊗[R] B`, hence — through
`AlgebraicGeometry.specOverMap_injective` — an identity of morphisms of spectra
(`Stacks.AlgebraDescent.cocycle_of_specOverMapGenerator`).

This is the algebra-level counterpart of `Stacks.SchemeDescent.cocycle_of_transition`, which
cuts the *scheme*-level cocycle condition down to one equation in the same way.

## Main definitions

* `Stacks.AlgebraDescent.rightCommAlg` — swapping the last two factors of a threefold tensor
  product, as an algebra isomorphism.
* `Stacks.AlgebraDescent.cocycleAlg01`, `...cocycleAlg12`, `...cocycleAlg02` — the three maps of
  the cocycle triangle as `R`-algebra maps, and `...cocycleAlgEquiv01`, `...cocycleAlgEquiv12`,
  `...cocycleAlgEquiv02` — the same three as isomorphisms.
* `Stacks.AlgebraDescent.tripleIncludeB` — the inclusion `b ↦ (b ⊗ 1) ⊗ 1` of `B` into the
  triple tensor product.

## Main results

* `Stacks.AlgebraDescent.algHom_ext_tripleTensor` — an `R`-algebra map out of
  `(B ⊗[R] A) ⊗[R] A` is determined by its values on the three families of generators.
* `Stacks.AlgebraDescent.cocycle_mid` and `Stacks.AlgebraDescent.cocycle_right` — the second and
  third generator families satisfy the cocycle equation for formal reasons, given only that `θ`
  is a morphism over `A ⊗[R] A`.
* `Stacks.AlgebraDescent.cocycle_of_flipGenerator` — **the cocycle condition reduces to the
  single equation on `(b ⊗ 1) ⊗ 1`.**
* `Stacks.AlgebraDescent.cocycle_of_cocycleAlg` and
  `Stacks.AlgebraDescent.cocycleAlg_comp_of_cocycle` — the linear and the algebra-map forms of the
  cocycle condition agree.
* `Stacks.AlgebraDescent.cocycle_of_specOverMap` and
  `Stacks.AlgebraDescent.cocycle_of_specOverMapGenerator` — the same two statements with the
  remaining algebra identity replaced by an identity of morphisms of spectra over `Spec R`.
* `Stacks.AlgebraDescent.trivialTransition_flipGenerator` — the remaining equation holds for the
  canonical transition of the identity covering, so the reduction is not vacuous.

## Implementation notes

`Stacks.AlgebraDescent.cocycle01` is `LinearMap.rTensor`, and `...cocycle12`, `...cocycle02` are
conjugates of `LinearMap.lTensor` respectively `LinearMap.rTensor` by the associator and by
`TensorProduct.rightComm`.  Each has an algebra-map realization built from
`Algebra.TensorProduct.map` and `Algebra.TensorProduct.assoc`; `TensorProduct.rightComm` has no
algebra counterpart in Mathlib at this pin, so `Stacks.AlgebraDescent.rightCommAlg` supplies one
as `assoc⁻¹ ∘ (1 ⊗ comm) ∘ assoc`.

The reduction to generators is `Algebra.TensorProduct.ext'` for the outer tensor factor followed
by the factorization
`(b ⊗ a) ⊗ a' = ((b ⊗ 1) ⊗ 1) * ((1 ⊗ a) ⊗ 1) * ((1 ⊗ 1) ⊗ a')`, which is where
multiplicativity — the only thing the linear statement does not see — is used.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
-/

@[expose] public section

noncomputable section

universe u

namespace Stacks.AlgebraDescent

open TensorProduct AlgebraicGeometry

variable (R : Type u) [CommRing R]

/-! ### Swapping the last two factors of a threefold tensor product -/

/-- Swapping the last two factors of a threefold tensor product, as an algebra isomorphism.
The underlying linear map is `TensorProduct.rightComm`. -/
def rightCommAlg (X Y Z : Type u) [CommRing X] [CommRing Y] [CommRing Z]
    [Algebra R X] [Algebra R Y] [Algebra R Z] :
    (X ⊗[R] Y) ⊗[R] Z ≃ₐ[R] (X ⊗[R] Z) ⊗[R] Y :=
  (Algebra.TensorProduct.assoc R R R X Y Z).trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := X))
      (Algebra.TensorProduct.comm R Y Z)).trans
      (Algebra.TensorProduct.assoc R R R X Z Y).symm)

/-- `rightCommAlg` sends `(x ⊗ y) ⊗ z` to `(x ⊗ z) ⊗ y`. -/
@[simp]
lemma rightCommAlg_tmul (X Y Z : Type u) [CommRing X] [CommRing Y] [CommRing Z]
    [Algebra R X] [Algebra R Y] [Algebra R Z] (x : X) (y : Y) (z : Z) :
    rightCommAlg R X Y Z ((x ⊗ₜ[R] y) ⊗ₜ[R] z) = (x ⊗ₜ[R] z) ⊗ₜ[R] y := rfl

/-- The underlying linear map of `rightCommAlg` is `TensorProduct.rightComm`. -/
lemma rightCommAlg_toLinearMap (X Y Z : Type u) [CommRing X] [CommRing Y] [CommRing Z]
    [Algebra R X] [Algebra R Y] [Algebra R Z] :
    (rightCommAlg R X Y Z).toAlgHom.toLinearMap =
      (TensorProduct.rightComm R X Y Z).toLinearMap := by
  exact TensorProduct.ext_threefold fun _ _ _ ↦ rfl

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-! ### An algebra map out of a threefold tensor product is determined on generators -/

/-- **An `R`-algebra map out of `(B ⊗[R] A) ⊗[R] A` is determined by its values on the three
families of generators** `(b ⊗ 1) ⊗ 1`, `(1 ⊗ a) ⊗ 1` and `(1 ⊗ 1) ⊗ a`. -/
theorem algHom_ext_tripleTensor {D : Type u} [CommRing D] [Algebra R D]
    {F G : (B ⊗[R] A) ⊗[R] A →ₐ[R] D}
    (h₀ : ∀ b : B, F ((b ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A)) = G ((b ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A)))
    (h₁ : ∀ a : A, F (((1 : B) ⊗ₜ[R] a) ⊗ₜ[R] (1 : A)) = G (((1 : B) ⊗ₜ[R] a) ⊗ₜ[R] (1 : A)))
    (h₂ : ∀ a : A, F (((1 : B) ⊗ₜ[R] (1 : A)) ⊗ₜ[R] a) = G (((1 : B) ⊗ₜ[R] (1 : A)) ⊗ₜ[R] a)) :
    F = G := by
  apply Algebra.TensorProduct.ext'
  intro x a
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [add_tmul, map_add, map_add, hx, hy]
  | tmul b a' =>
    have hdec : ((b ⊗ₜ[R] a') ⊗ₜ[R] a : (B ⊗[R] A) ⊗[R] A) =
        ((b ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A)) * (((1 : B) ⊗ₜ[R] a') ⊗ₜ[R] (1 : A)) *
          (((1 : B) ⊗ₜ[R] (1 : A)) ⊗ₜ[R] a) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [hdec, map_mul, map_mul, map_mul, map_mul, h₀, h₁, h₂]

/-- The inclusion `b ↦ (b ⊗ 1) ⊗ 1` of `B` into `(B ⊗[R] A) ⊗[R] A`. -/
def tripleIncludeB : B →ₐ[R] (B ⊗[R] A) ⊗[R] A :=
  (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B ⊗[R] A) (B := A)).comp
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := A))

/-- `tripleIncludeB` sends `b` to `(b ⊗ 1) ⊗ 1`. -/
@[simp]
lemma tripleIncludeB_apply (b : B) :
    tripleIncludeB R A B b = (b ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A) := rfl

/-! ### The three maps of the cocycle triangle as algebra maps -/

section Cocycle

variable (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))

/-- `Stacks.AlgebraDescent.cocycle01` as an `R`-algebra map. -/
def cocycleAlg01 : (B ⊗[R] A) ⊗[R] A →ₐ[R] (A ⊗[R] B) ⊗[R] A :=
  Algebra.TensorProduct.map θ.toAlgHom (AlgHom.id R A)

/-- `Stacks.AlgebraDescent.cocycle12` as an `R`-algebra map. -/
def cocycleAlg12 : (A ⊗[R] B) ⊗[R] A →ₐ[R] (A ⊗[R] A) ⊗[R] B :=
  (Algebra.TensorProduct.assoc R R R A A B).symm.toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id R A) θ.toAlgHom).comp
      (Algebra.TensorProduct.assoc R R R A B A).toAlgHom)

/-- `Stacks.AlgebraDescent.cocycle02` as an `R`-algebra map. -/
def cocycleAlg02 : (B ⊗[R] A) ⊗[R] A →ₐ[R] (A ⊗[R] A) ⊗[R] B :=
  (rightCommAlg R A B A).toAlgHom.comp
    ((Algebra.TensorProduct.map θ.toAlgHom (AlgHom.id R A)).comp (rightCommAlg R B A A).toAlgHom)

/-- `Stacks.AlgebraDescent.cocycleAlg01` is an isomorphism. -/
def cocycleAlgEquiv01 : (B ⊗[R] A) ⊗[R] A ≃ₐ[R] (A ⊗[R] B) ⊗[R] A :=
  Algebra.TensorProduct.congr θ (AlgEquiv.refl (R := R) (A₁ := A))

/-- `Stacks.AlgebraDescent.cocycleAlg12` is an isomorphism. -/
def cocycleAlgEquiv12 : (A ⊗[R] B) ⊗[R] A ≃ₐ[R] (A ⊗[R] A) ⊗[R] B :=
  ((Algebra.TensorProduct.assoc R R R A B A).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := A)) θ)).trans
    (Algebra.TensorProduct.assoc R R R A A B).symm

/-- `Stacks.AlgebraDescent.cocycleAlg02` is an isomorphism. -/
def cocycleAlgEquiv02 : (B ⊗[R] A) ⊗[R] A ≃ₐ[R] (A ⊗[R] A) ⊗[R] B :=
  ((rightCommAlg R B A A).trans
    (Algebra.TensorProduct.congr θ (AlgEquiv.refl (R := R) (A₁ := A)))).trans
    (rightCommAlg R A B A)

/-- The algebra map underlying `cocycleAlgEquiv01` is `cocycleAlg01`. -/
@[simp]
lemma cocycleAlgEquiv01_toAlgHom :
    (cocycleAlgEquiv01 R A B θ).toAlgHom = cocycleAlg01 R A B θ := rfl

/-- The algebra map underlying `cocycleAlgEquiv12` is `cocycleAlg12`. -/
@[simp]
lemma cocycleAlgEquiv12_toAlgHom :
    (cocycleAlgEquiv12 R A B θ).toAlgHom = cocycleAlg12 R A B θ := rfl

/-- The algebra map underlying `cocycleAlgEquiv02` is `cocycleAlg02`. -/
@[simp]
lemma cocycleAlgEquiv02_toAlgHom :
    (cocycleAlgEquiv02 R A B θ).toAlgHom = cocycleAlg02 R A B θ := rfl

/-- The underlying linear map of `cocycleAlg01` is `cocycle01`. -/
lemma cocycleAlg01_toLinearMap :
    (cocycleAlg01 R A B θ).toLinearMap = cocycle01 R A B θ.toLinearMap := by
  exact TensorProduct.ext_threefold fun _ _ _ ↦ rfl

/-- The underlying linear map of `cocycleAlg12` is `cocycle12`. -/
lemma cocycleAlg12_toLinearMap :
    (cocycleAlg12 R A B θ).toLinearMap = cocycle12 R A B θ.toLinearMap := by
  exact TensorProduct.ext_threefold fun _ _ _ ↦ rfl

/-- The underlying linear map of `cocycleAlg02` is `cocycle02`. -/
lemma cocycleAlg02_toLinearMap :
    (cocycleAlg02 R A B θ).toLinearMap = cocycle02 R A B θ.toLinearMap := by
  rw [cocycleAlg02, AlgHom.comp_toLinearMap, AlgHom.comp_toLinearMap,
    rightCommAlg_toLinearMap, rightCommAlg_toLinearMap,
    show (Algebra.TensorProduct.map θ.toAlgHom (AlgHom.id R A)).toLinearMap =
      cocycle01 R A B θ.toLinearMap from cocycleAlg01_toLinearMap R A B θ,
    cocycle01, cocycle02]

/-- `cocycleAlg01` agrees pointwise with `cocycle01`. -/
lemma cocycleAlg01_apply (x : (B ⊗[R] A) ⊗[R] A) :
    cocycleAlg01 R A B θ x = cocycle01 R A B θ.toLinearMap x :=
  congrFun (congrArg DFunLike.coe (cocycleAlg01_toLinearMap R A B θ)) x

/-- `cocycleAlg12` agrees pointwise with `cocycle12`. -/
lemma cocycleAlg12_apply (x : (A ⊗[R] B) ⊗[R] A) :
    cocycleAlg12 R A B θ x = cocycle12 R A B θ.toLinearMap x :=
  congrFun (congrArg DFunLike.coe (cocycleAlg12_toLinearMap R A B θ)) x

/-- `cocycleAlg02` agrees pointwise with `cocycle02`. -/
lemma cocycleAlg02_apply (x : (B ⊗[R] A) ⊗[R] A) :
    cocycleAlg02 R A B θ x = cocycle02 R A B θ.toLinearMap x :=
  congrFun (congrArg DFunLike.coe (cocycleAlg02_toLinearMap R A B θ)) x

/-- The cocycle condition in its algebra-map form implies its linear form. -/
lemma cocycle_of_cocycleAlg
    (h : (cocycleAlg12 R A B θ).comp (cocycleAlg01 R A B θ) = cocycleAlg02 R A B θ) :
    cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap := by
  have h' := congrArg AlgHom.toLinearMap h
  rw [AlgHom.comp_toLinearMap, cocycleAlg01_toLinearMap, cocycleAlg12_toLinearMap,
    cocycleAlg02_toLinearMap] at h'
  exact h'

/-- The converse of `Stacks.AlgebraDescent.cocycle_of_cocycleAlg`: the linear form of the
cocycle condition implies the algebra-map form. -/
lemma cocycleAlg_comp_of_cocycle
    (h : cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap) :
    (cocycleAlg12 R A B θ).comp (cocycleAlg01 R A B θ) = cocycleAlg02 R A B θ := by
  refine AlgHom.ext fun x ↦ ?_
  have hx := LinearMap.congr_fun h x
  rw [LinearMap.comp_apply] at hx
  rw [AlgHom.comp_apply, cocycleAlg01_apply, cocycleAlg12_apply, cocycleAlg02_apply]
  exact hx

/-- **The cocycle condition from an equality of morphisms of spectra.**  The triangle of the
cocycle condition commutes as soon as it commutes after applying `Spec`, because `Spec` is
faithful on algebra maps over the base. -/
theorem cocycle_of_specOverMap
    (h : specOverMap ((cocycleAlg12 R A B θ).comp (cocycleAlg01 R A B θ)) =
      specOverMap (cocycleAlg02 R A B θ)) :
    cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap :=
  cocycle_of_cocycleAlg R A B θ (specOverMap_injective h)

end Cocycle

/-! ### Reduction to the single generator `(b ⊗ 1) ⊗ 1` -/

section Flip

variable [Algebra A B] (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
  (hleft : ∀ a : A, θ (algebraMap A B a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B))
  (hright : ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A B a)

include hleft hright in
/-- The cocycle equation holds on the generators `(1 ⊗ a) ⊗ 1`, for the formal reason that `θ`
is a morphism over `A ⊗[R] A`. -/
lemma cocycle_mid (a : A) :
    cocycle12 R A B θ.toLinearMap
        (cocycle01 R A B θ.toLinearMap (((1 : B) ⊗ₜ[R] a) ⊗ₜ[R] (1 : A))) =
      cocycle02 R A B θ.toLinearMap (((1 : B) ⊗ₜ[R] a) ⊗ₜ[R] (1 : A)) := by
  simp only [cocycle01, cocycle12, cocycle02, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul, TensorProduct.rightComm_tmul,
    map_one, hright, hleft]

include hright in
/-- The cocycle equation holds on the generators `(1 ⊗ 1) ⊗ a`, for the formal reason that `θ`
is a morphism over the second factor of `A ⊗[R] A`. -/
lemma cocycle_right (a : A) :
    cocycle12 R A B θ.toLinearMap
        (cocycle01 R A B θ.toLinearMap (((1 : B) ⊗ₜ[R] (1 : A)) ⊗ₜ[R] a)) =
      cocycle02 R A B θ.toLinearMap (((1 : B) ⊗ₜ[R] (1 : A)) ⊗ₜ[R] a) := by
  simp only [cocycle01, cocycle12, cocycle02, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe,
    TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul, TensorProduct.rightComm_tmul,
    map_one, hright]

include hleft hright in
/-- **The cocycle condition on a transition over `A ⊗[R] A` reduces to one equation.**  Two of
the three generator families of `(B ⊗[R] A) ⊗[R] A` are handled by the hypotheses that `θ` is a
morphism over `A ⊗[R] A`; what remains is the displayed equation on `(b ⊗ 1) ⊗ 1`, and that is
the whole content of the cocycle condition. -/
theorem cocycle_of_flipGenerator
    (hgen : ∀ b : B, cocycle12 R A B θ.toLinearMap
        (cocycle01 R A B θ.toLinearMap ((b ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A))) =
      cocycle02 R A B θ.toLinearMap ((b ⊗ₜ[R] (1 : A)) ⊗ₜ[R] (1 : A))) :
    cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap := by
  have key : ∀ x, cocycle12 R A B θ.toLinearMap (cocycle01 R A B θ.toLinearMap x) =
      cocycle02 R A B θ.toLinearMap x →
      ((cocycleAlg12 R A B θ).comp (cocycleAlg01 R A B θ)) x = cocycleAlg02 R A B θ x := by
    intro x hx
    rw [AlgHom.comp_apply, cocycleAlg01_apply, cocycleAlg12_apply, cocycleAlg02_apply]
    exact hx
  exact cocycle_of_cocycleAlg R A B θ (algHom_ext_tripleTensor R A B (fun b ↦ key _ (hgen b))
    (fun a ↦ key _ (cocycle_mid R A B θ hleft hright a))
    (fun a ↦ key _ (cocycle_right R A B θ hright a)))

include hleft hright in
/-- **The cocycle condition from a single equality of morphisms of spectra.**  Combining the
reduction to one generator with faithfulness of `Spec`, the cocycle condition holds as soon as
the two threefold transports of the `Spec B`-component agree. -/
theorem cocycle_of_specOverMapGenerator
    (h : specOverMap ((cocycleAlg12 R A B θ).comp
          ((cocycleAlg01 R A B θ).comp (tripleIncludeB R A B))) =
      specOverMap ((cocycleAlg02 R A B θ).comp (tripleIncludeB R A B))) :
    cocycle12 R A B θ.toLinearMap ∘ₗ cocycle01 R A B θ.toLinearMap =
      cocycle02 R A B θ.toLinearMap := by
  refine cocycle_of_flipGenerator R A B θ hleft hright fun b ↦ ?_
  have h' := specOverMap_injective h
  have := congrArg (fun k ↦ (k : B →ₐ[R] (A ⊗[R] A) ⊗[R] B) b) h'
  rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, tripleIncludeB_apply,
    cocycleAlg01_apply, cocycleAlg12_apply, cocycleAlg02_apply] at this
  exact this

end Flip

/-! ### The remaining equation is satisfiable -/

section Nonvacuity

variable (B : Type u) [CommRing B] [Algebra R B]

/-- **The single generator equation left by
`Stacks.AlgebraDescent.cocycle_of_flipGenerator` is satisfiable, so the reduction is not
vacuous.**  It holds for the identity covering `R → R` and the canonical transition
`Stacks.SchemeDescent.trivialTransition`. -/
theorem trivialTransition_flipGenerator (b : B) :
    cocycle12 R R B (Stacks.SchemeDescent.trivialTransition R B).toLinearMap
        (cocycle01 R R B (Stacks.SchemeDescent.trivialTransition R B).toLinearMap
          ((b ⊗ₜ[R] (1 : R)) ⊗ₜ[R] (1 : R))) =
      cocycle02 R R B (Stacks.SchemeDescent.trivialTransition R B).toLinearMap
        ((b ⊗ₜ[R] (1 : R)) ⊗ₜ[R] (1 : R)) :=
  congrFun
    (congrArg DFunLike.coe (Stacks.SchemeDescent.trivialTransition_cocycle R B))
    ((b ⊗ₜ[R] (1 : R)) ⊗ₜ[R] (1 : R))

end Nonvacuity

end Stacks.AlgebraDescent

end

end
