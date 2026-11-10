module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.ANCModuleSplitting
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DivisibleMaps
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullback
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.FibreDimensionBound
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.ThickeningPullback
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwistDown
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# The module situations of Tags 0GAA and 0GAC on the blowup

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `p : X → Spec(A)` the blowing up of `Spec(A)` in
`I` and `Yₙ ⊆ X` the `n`-th thickening of the exceptional divisor. The proofs of [Stacks, Tag 0GAA]
and [Stacks, Tag 0GAC] work with the cohomology of the twists `p^*M(q)` of the pullbacks of
`(A, n, c)`-modules `M`, and of the sheaves `𝒢`, `ℱ` obtained by pulling back a finite free
presentation `0 → K → (A/Iⁿ)^{⊕r} → M → 0`. This file supplies, on the actual blowup, the data the
abstract structures `ModuleSituation`, `TwistedModuleSituation` and `DualSituation` record.

Here `p^*M` is `Stacks.LocalCohomology.UniformityIII.thickeningPullback`, the twists are the
integer twists `blowupTwistInt`, and the cohomology is the `A`-module valued `blowupHmod`.

The geometric inputs are: the vanishing of `Hⁱ` of quasi-coherent sheaves above `d(S)`
(`subsingleton_blowupHmod_of_fibreDim_lt`), the long exact sequences of the δ-functor
`blowupDeltaMod`, the exactness of twisting (`shortExact_whiskerRight_blowupTwistInt`), the right
exactness and additivity of `p^*`, `𝒪_{Yₙ} = p^*(A/Iⁿ)`, Tag 0GA8 for `ℱ`
(`globalSmulCenter_app_blowupSupported`, from `IsANCModule.exists_comp_eq_smul_of_exact`) and
Tag 0GA9 (`whiskerLeft_blowupTwistLE_eq_zero`), which together give the dotted arrow.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.blowupImage`, `blowupKernelLift`, `blowupSupported`:
  the sheaves `𝒢`, `ℱ` and the epimorphism `p^*K ⟶ 𝒢` attached to a presentation.
* `Stacks.LocalCohomology.UniformityIII.blowupDottedSheaf`: the dotted arrow `𝒢(t) ⟶ p^*K(t - c)`.
* `Stacks.LocalCohomology.UniformityIII.blowupSecM`: the canonical map
  `I^q ⊗_A N → H⁰(X, p^*N(q))`.
* `Stacks.LocalCohomology.UniformityIII.blowupDualEv`: the evaluation dictionary
  `H⁰(X, p^*(N^∨)(q)) → Hom_A(N, I^q/I^{q+n})` of the proof of Tag 0GAC.
* `Stacks.LocalCohomology.UniformityIII.blowupModuleSituation`,
  `blowupTwistedModuleSituation`, `blowupDualSituation`: the three structures on the blowup, at
  any threshold `q₀` with the defining property of `q(S)`; the suffix `QS` specializes to
  `q₀ = q(S)`, where `d = d(S) = fibreDim I`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.blowupDottedSheaf_comp`: the dotted arrow factors
  `𝒢(t) ⟶ 𝒢(t - c)` through `p^*K(t - c)`.
* `Stacks.LocalCohomology.UniformityIII.blowupDualEv_whiskerLeft`,
  `blowupDualEv_blowupSecM`: the evaluation dictionary is natural in the twist and is the
  evaluation pairing on canonical sections.

## References

* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 0GAC](https://stacks.math.columbia.edu/tag/0GAC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry
open Stacks.RegularSequence (globalSmulCenter)
open scoped TensorProduct

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] (I : Ideal A)

/-! ### Degree zero and scalars -/

/-- On `H⁰(X, -)`, multiplication by the global function `a` pulls back to is the scalar `a`. -/
theorem blowupHmodMap_zero_globalSmulCenter (a : A) (F : (blowupScheme I).Modules)
    (y : blowupHmod I 0 F) :
    blowupHmodMap I 0 ((globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app F) y =
      a • y := by
  obtain ⟨x, rfl⟩ := surjective_blowupΓmodToH0 I F y
  exact (blowupΓmodToH0_naturality I _ x).symm.trans
    ((congrArg (blowupΓmodToH0 I F) (blowupΓmod_map_globalSmulCenter I a F x)).trans
      ((blowupΓmodToH0 I F).hom.map_smul a x))

/-! ### The evaluation dictionary -/

/-- Evaluation at an element `z` of an `A/Iⁿ`-module `N`, as a morphism `N^∨ ⟶ A/Iⁿ`. -/
def dualEvalAt {n : ℕ} (N : ModuleCat.{u} (A ⧸ I ^ n)) (z : N) :
    ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) N) ⟶
      ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n) :=
  ModuleCat.ofHom (Module.Dual.eval (A ⧸ I ^ n) N z)

/-- Evaluation at a sum is the sum of the evaluations. -/
theorem dualEvalAt_add {n : ℕ} (N : ModuleCat.{u} (A ⧸ I ^ n)) (z w : N) :
    dualEvalAt I N (z + w) = dualEvalAt I N z + dualEvalAt I N w :=
  ModuleCat.hom_ext (LinearMap.ext fun lam => map_add lam z w)

/-- Evaluation at a multiple is the multiple of the evaluation. -/
theorem dualEvalAt_smul {n : ℕ} (N : ModuleCat.{u} (A ⧸ I ^ n)) (a : A ⧸ I ^ n) (z : N) :
    dualEvalAt I N (a • z) = a • dualEvalAt I N z :=
  ModuleCat.hom_ext (LinearMap.ext fun lam => map_smul lam a z)

/-- `Hⁱ(X, -)` is additive. -/
instance additive_blowupHmod (i : ℕ) : ((blowupΓmod I).rightDerived i).Additive :=
  (blowupDeltaMod I).additive i

/-- `Hⁱ(X, -)` of a sum of morphisms, elementwise. -/
theorem blowupHmodMap_add (i : ℕ) {F G : (blowupScheme I).Modules} (φ ψ : F ⟶ G)
    (y : blowupHmod I i F) :
    blowupHmodMap I i (φ + ψ) y = blowupHmodMap I i φ y + blowupHmodMap I i ψ y :=
  (ConcreteCategory.congr_hom
    (Functor.map_add ((blowupΓmod I).rightDerived i) (f := φ) (g := ψ)) y).trans rfl

/-- `Hⁱ(X, -)` of a composite, elementwise. -/
theorem blowupHmodMap_comp_apply (i : ℕ) {F G H : (blowupScheme I).Modules} (φ : F ⟶ G)
    (ψ : G ⟶ H) (y : blowupHmod I i F) :
    blowupHmodMap I i (φ ≫ ψ) y = blowupHmodMap I i ψ (blowupHmodMap I i φ y) :=
  (ConcreteCategory.congr_hom (((blowupΓmod I).rightDerived i).map_comp φ ψ) y).trans rfl

/-- Twisting a sum of morphisms. -/
theorem add_whiskerRight_blowupTwistInt {F G : (blowupScheme I).Modules} (φ ψ : F ⟶ G) (t : ℤ) :
    (φ + ψ) ▷ blowupTwistInt I t = φ ▷ blowupTwistInt I t + ψ ▷ blowupTwistInt I t :=
  (MonoidalCategory.tensorRight (blowupTwistInt I t)).map_add

variable {I} in
/-- On `H⁰`, the image under `p^*` of a scalar multiple of a morphism of `A/Iⁿ`-modules, twisted,
is the scalar multiple of the image. -/
theorem blowupHmodMap_zero_thickeningPullback_map_smul {n : ℕ}
    {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N') {E : (blowupScheme I).Modules}
    (g : (thickeningPullback I n).obj N' ⟶ E) (a : A) (t : ℤ)
    (y : blowupHmod I 0 ((thickeningPullback I n).obj N ⊗ blowupTwistInt I t)) :
    blowupHmodMap I 0
        (((thickeningPullback I n).map (Ideal.Quotient.mk (I ^ n) a • f) ≫ g) ▷
          blowupTwistInt I t) y =
      a • blowupHmodMap I 0 (((thickeningPullback I n).map f ≫ g) ▷ blowupTwistInt I t) y := by
  rw [thickeningPullback_map_smul, Category.assoc, MonoidalCategory.comp_whiskerRight,
    globalSmulCenter_app_whiskerRight, blowupHmodMap_comp_apply]
  exact (congrArg _ (blowupHmodMap_zero_globalSmulCenter I a _ y)).trans (map_smul _ a _)

variable {I} in
/-- On `Hⁱ`, the image under `p^*` of a sum of morphisms of `A/Iⁿ`-modules, twisted, is the sum
of the images. -/
theorem blowupHmodMap_thickeningPullback_map_add {n : ℕ} (i : ℕ)
    {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f f' : N ⟶ N') {E : (blowupScheme I).Modules}
    (g : (thickeningPullback I n).obj N' ⟶ E) (t : ℤ)
    (y : blowupHmod I i ((thickeningPullback I n).obj N ⊗ blowupTwistInt I t)) :
    blowupHmodMap I i (((thickeningPullback I n).map (f + f') ≫ g) ▷ blowupTwistInt I t) y =
      blowupHmodMap I i (((thickeningPullback I n).map f ≫ g) ▷ blowupTwistInt I t) y +
        blowupHmodMap I i (((thickeningPullback I n).map f' ≫ g) ▷ blowupTwistInt I t) y := by
  rw [Functor.map_add, Preadditive.add_comp, add_whiskerRight_blowupTwistInt, blowupHmodMap_add]

variable [IsNoetherianRing A]

/-- **The evaluation dictionary of Tag 0GAC.** For `n = m + 1`, `q ≥ q₀` with `q₀` having the
defining property of `q(S)`, and an `A/Iⁿ`-module `N`, a section `σ` of `p^*(N^∨)(q)` and an
element `z ∈ N` give the element of `I^q/I^{q+n}` obtained by applying `p^*` of the evaluation
`N^∨ → A/Iⁿ` at `z`, reading `p^*(A/Iⁿ)(q) = 𝒪_{Yₙ}(q)` (`thickeningPullbackUnitIso`) and
inverting the bijection `I^q/I^{q+n} → H⁰(X, 𝒪_{Yₙ}(q))` of Tag 0GA7(2). -/
def blowupDualEv (m : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀) {q : ℕ} (hq : q₀ ≤ q)
    (N : ModuleCat.{u} (A ⧸ I ^ (m + 1))) :
    blowupHmod I 0 ((thickeningPullback I (m + 1)).obj
        (ModuleCat.of _ (Module.Dual (A ⧸ I ^ (m + 1)) N)) ⊗ blowupTwistInt I q) →ₗ[A]
      (resModule I (m + 1) N →ₗ[A] powQuot I q (m + 1)) :=
  LinearMap.mk₂' A A
    (fun σ z => (LinearEquiv.ofBijective (cdivMod I m q) (bijective_cdivMod_of_le I h hq)).symm
      (blowupHmodMap I 0 (((thickeningPullback I (m + 1)).map (dualEvalAt I N z) ≫
        (thickeningPullbackUnitIso I (m + 1)).hom) ▷ blowupTwistInt I q) σ))
    (fun σ σ' z => by rw [map_add, map_add])
    (fun a σ z => by rw [map_smul, map_smul])
    (fun σ z z' => by
      rw [show dualEvalAt I N (z + z') = dualEvalAt I N z + dualEvalAt I N z' from
        dualEvalAt_add I N z z', blowupHmodMap_thickeningPullback_map_add, map_add])
    (fun a σ z => by
      rw [show dualEvalAt I N (a • z) = Ideal.Quotient.mk (I ^ (m + 1)) a • dualEvalAt I N z from
        dualEvalAt_smul I N _ z, blowupHmodMap_zero_thickeningPullback_map_smul, map_smul])

/-- The defining formula of `blowupDualEv`. -/
theorem blowupDualEv_apply (m : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀) {q : ℕ} (hq : q₀ ≤ q)
    (N : ModuleCat.{u} (A ⧸ I ^ (m + 1)))
    (σ : blowupHmod I 0 ((thickeningPullback I (m + 1)).obj
        (ModuleCat.of _ (Module.Dual (A ⧸ I ^ (m + 1)) N)) ⊗ blowupTwistInt I q))
    (z : resModule I (m + 1) N) :
    blowupDualEv I m h hq N σ z =
      (LinearEquiv.ofBijective (cdivMod I m q) (bijective_cdivMod_of_le I h hq)).symm
        (blowupHmodMap I 0 (((thickeningPullback I (m + 1)).map (dualEvalAt I N z) ≫
          (thickeningPullbackUnitIso I (m + 1)).hom) ▷ blowupTwistInt I q) σ) :=
  rfl

omit [IsNoetherianRing A] in
/-- `𝒪_{Y₀}(q) = 0`, so all its cohomology vanishes. -/
theorem subsingleton_blowupHmod_thickeningTwist_zero (i q : ℕ) :
    Subsingleton (blowupHmod I i (thickeningTwist I 0 q)) :=
  ModuleCat.subsingleton_of_isZero (((blowupΓmod I).rightDerived i).map_isZero
    (isZero_tensor_blowupTwistInt I (isZero_thickeningSheaf_zero I) (q : ℤ)))

/-! ### Cohomology of the twisted pullbacks -/

section PullbackTwist

variable {I} {n : ℕ}

omit [IsNoetherianRing A]

variable (I n) in
/-- `Hⁱ(X, p^*f(t))` for a morphism `f` of `A/Iⁿ`-modules, as an `A`-linear map
`Hⁱ(X, p^*N(t)) → Hⁱ(X, p^*N'(t))`. -/
def pullbackTwistMap (i : ℕ) (t : ℤ) {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N') :
    blowupHmod I i ((thickeningPullback I n).obj N ⊗ blowupTwistInt I t) →ₗ[A]
      blowupHmod I i ((thickeningPullback I n).obj N' ⊗ blowupTwistInt I t) :=
  (blowupHmodMap I i ((thickeningPullback I n).map f ▷ blowupTwistInt I t)).hom

/-- The defining formula of `pullbackTwistMap`. -/
theorem pullbackTwistMap_apply (i : ℕ) (t : ℤ) {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N')
    (y : blowupHmod I i ((thickeningPullback I n).obj N ⊗ blowupTwistInt I t)) :
    pullbackTwistMap I n i t f y =
      blowupHmodMap I i ((thickeningPullback I n).map f ▷ blowupTwistInt I t) y :=
  rfl

/-- `pullbackTwistMap` is functorial. -/
theorem pullbackTwistMap_comp (i : ℕ) (t : ℤ) {N N' N'' : ModuleCat.{u} (A ⧸ I ^ n)}
    (f : N ⟶ N') (g : N' ⟶ N'')
    (y : blowupHmod I i ((thickeningPullback I n).obj N ⊗ blowupTwistInt I t)) :
    pullbackTwistMap I n i t (f ≫ g) y =
      pullbackTwistMap I n i t g (pullbackTwistMap I n i t f y) := by
  rw [pullbackTwistMap_apply, Functor.map_comp, MonoidalCategory.comp_whiskerRight,
    blowupHmodMap_comp_apply]
  rfl

/-- `pullbackTwistMap` of the identity. -/
theorem pullbackTwistMap_id (i : ℕ) (t : ℤ) (N : ModuleCat.{u} (A ⧸ I ^ n))
    (y : blowupHmod I i ((thickeningPullback I n).obj N ⊗ blowupTwistInt I t)) :
    pullbackTwistMap I n i t (𝟙 N) y = y := by
  rw [pullbackTwistMap_apply, CategoryTheory.Functor.map_id, MonoidalCategory.id_whiskerRight]
  exact (ConcreteCategory.congr_hom (((blowupΓmod I).rightDerived i).map_id _) y).trans rfl

/-- `pullbackTwistMap` is additive. -/
theorem pullbackTwistMap_add (i : ℕ) (t : ℤ) {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f g : N ⟶ N')
    (y : blowupHmod I i ((thickeningPullback I n).obj N ⊗ blowupTwistInt I t)) :
    pullbackTwistMap I n i t (f + g) y =
      pullbackTwistMap I n i t f y + pullbackTwistMap I n i t g y := by
  rw [pullbackTwistMap_apply, Functor.map_add, add_whiskerRight_blowupTwistInt, blowupHmodMap_add]
  rfl

/-- `pullbackTwistMap` of zero. -/
theorem pullbackTwistMap_zero (i : ℕ) (t : ℤ) (N N' : ModuleCat.{u} (A ⧸ I ^ n))
    (y : blowupHmod I i ((thickeningPullback I n).obj N ⊗ blowupTwistInt I t)) :
    pullbackTwistMap I n i t (0 : N ⟶ N') y = 0 := by
  simpa using pullbackTwistMap_add i t (0 : N ⟶ N') 0 y

/-- `pullbackTwistMap` of a finite sum. -/
theorem pullbackTwistMap_sum (i : ℕ) (t : ℤ) {N N' : ModuleCat.{u} (A ⧸ I ^ n)} {ι : Type*}
    (s : Finset ι) (f : ι → (N ⟶ N'))
    (y : blowupHmod I i ((thickeningPullback I n).obj N ⊗ blowupTwistInt I t)) :
    pullbackTwistMap I n i t (∑ j ∈ s, f j) y = ∑ j ∈ s, pullbackTwistMap I n i t (f j) y := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, pullbackTwistMap_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, pullbackTwistMap_add, ih]

/-- On `H⁰`, `pullbackTwistMap` takes the scalar `a` on a morphism to the scalar `a`. -/
theorem pullbackTwistMap_zero_smul (t : ℤ) {N N' : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ N')
    (a : A) (y : blowupHmod I 0 ((thickeningPullback I n).obj N ⊗ blowupTwistInt I t)) :
    pullbackTwistMap I n 0 t (Ideal.Quotient.mk (I ^ n) a • f) y =
      a • pullbackTwistMap I n 0 t f y := by
  simpa only [Category.comp_id, pullbackTwistMap_apply] using
    blowupHmodMap_zero_thickeningPullback_map_smul f (𝟙 _) a t y

variable (I n) in
/-- `p^*(A/Iⁿ)(t) ≅ 𝒪_{Yₙ}(t)` on cohomology, from `thickeningPullbackUnitIso`. -/
def pullbackTwistUnitEquiv (i : ℕ) (t : ℤ) :
    blowupHmod I i ((thickeningPullback I n).obj (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n)) ⊗
        blowupTwistInt I t) ≃ₗ[A]
      blowupHmod I i (thickeningSheaf I n ⊗ blowupTwistInt I t) :=
  (((blowupΓmod I).rightDerived i).mapIso
    (MonoidalCategory.whiskerRightIso (thickeningPullbackUnitIso I n)
      (blowupTwistInt I t))).toLinearEquiv

/-- The `j`-th inclusion followed by the `k`-th projection of `(A/Iⁿ)^{⊕r}`. -/
theorem finFreeIncl_comp_finFreeProj (r : ℕ) (j k : Fin r) :
    finFreeIncl (A ⧸ I ^ n) r j ≫ finFreeProj (A ⧸ I ^ n) r k = if j = k then 𝟙 _ else 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [hjk, Ne.symm hjk]

variable (I n) in
/-- **Cohomology commutes with finite direct sums of pullbacks**:
`Hⁱ(X, p^*((A/Iⁿ)^{⊕r})(t)) = Hⁱ(X, p^*(A/Iⁿ)(t))^{⊕r}`, by additivity of `N ↦ Hⁱ(X, p^*N(t))`. -/
def pullbackTwistFinFreeEquiv (i : ℕ) (t : ℤ) (r : ℕ) :
    blowupHmod I i ((thickeningPullback I n).obj (finFreeModule (A ⧸ I ^ n) r) ⊗
        blowupTwistInt I t) ≃ₗ[A]
      (Fin r → blowupHmod I i ((thickeningPullback I n).obj
        (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n)) ⊗ blowupTwistInt I t)) :=
  LinearEquiv.ofLinearMap
    (LinearMap.pi fun j => pullbackTwistMap I n i t (finFreeProj (A ⧸ I ^ n) r j))
    (∑ j : Fin r, pullbackTwistMap I n i t (finFreeIncl (A ⧸ I ^ n) r j) ∘ₗ LinearMap.proj j)
    (LinearMap.ext fun w => funext fun k => by
      change pullbackTwistMap I n i t (finFreeProj (A ⧸ I ^ n) r k)
        ((∑ j : Fin r, pullbackTwistMap I n i t (finFreeIncl (A ⧸ I ^ n) r j) ∘ₗ
          LinearMap.proj j) w) = w k
      rw [LinearMap.sum_apply, map_sum]
      refine (Finset.sum_eq_single k (fun j _ hjk => ?_)
        (fun h => absurd (Finset.mem_univ k) h)).trans ?_
      · change pullbackTwistMap I n i t _ (pullbackTwistMap I n i t _ (w j)) = 0
        rw [← pullbackTwistMap_comp, finFreeIncl_comp_finFreeProj, ite_eq_right hjk,
          pullbackTwistMap_zero]
      · change pullbackTwistMap I n i t _ (pullbackTwistMap I n i t _ (w k)) = w k
        rw [← pullbackTwistMap_comp, finFreeIncl_comp_finFreeProj, ite_eq_left rfl,
          pullbackTwistMap_id])
    (LinearMap.ext fun y => by
      change (∑ j : Fin r, pullbackTwistMap I n i t (finFreeIncl (A ⧸ I ^ n) r j) ∘ₗ
          LinearMap.proj j) (fun j => pullbackTwistMap I n i t (finFreeProj (A ⧸ I ^ n) r j) y) = y
      rw [LinearMap.sum_apply]
      change ∑ j : Fin r, pullbackTwistMap I n i t _ (pullbackTwistMap I n i t _ y) = y
      simp_rw [← pullbackTwistMap_comp]
      rw [← pullbackTwistMap_sum, sum_finFreeProj_comp_finFreeIncl, pullbackTwistMap_id])

/-- The inverse of `pullbackTwistFinFreeEquiv` is the sum of the images of the inclusions. -/
theorem pullbackTwistFinFreeEquiv_symm_apply (i : ℕ) (t : ℤ) (r : ℕ)
    (w : Fin r → blowupHmod I i ((thickeningPullback I n).obj
      (ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n)) ⊗ blowupTwistInt I t)) :
    (pullbackTwistFinFreeEquiv I n i t r).symm w =
      ∑ j, pullbackTwistMap I n i t (finFreeIncl (A ⧸ I ^ n) r j) (w j) := by
  change (∑ j : Fin r, pullbackTwistMap I n i t (finFreeIncl (A ⧸ I ^ n) r j) ∘ₗ
    LinearMap.proj j) w = _
  rw [LinearMap.sum_apply]
  rfl

end PullbackTwist

/-! ### The sheaves `𝒢` and `ℱ` attached to a presentation -/

section Presentation

variable {I} {n c : ℕ} {M : ANCModule I n c} (p : ANCPresentation I n c M)

omit [IsNoetherianRing A]

/-- The surjection `(A/Iⁿ)^{⊕r} ⟶ M` of a presentation, as a morphism of modules. -/
abbrev presProj : finFreeModule (A ⧸ I ^ n) p.rank ⟶ M.1 :=
  ModuleCat.ofHom p.proj

/-- The inclusion `K ⟶ (A/Iⁿ)^{⊕r}` of a presentation, as a morphism of modules. -/
abbrev presIncl : p.kernel ⟶ finFreeModule (A ⧸ I ^ n) p.rank :=
  ModuleCat.ofHom p.incl

/-- `K ⟶ (A/Iⁿ)^{⊕r} ⟶ M` is zero. -/
theorem presIncl_comp_presProj : presIncl p ≫ presProj p = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun k => ?_)
  exact (p.range_incl_eq_ker_proj ▸ ⟨k, rfl⟩ : p.incl k ∈ LinearMap.ker p.proj)

/-- `K ⟶ (A/Iⁿ)^{⊕r} ⟶ M` is exact. -/
theorem exact_presIncl_presProj :
    (ShortComplex.mk (presIncl p) (presProj p) (presIncl_comp_presProj p)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact p.range_incl_eq_ker_proj

/-- `(A/Iⁿ)^{⊕r} ⟶ M` is an epimorphism. -/
instance epi_presProj : Epi (presProj p) :=
  (ModuleCat.epi_iff_surjective _).2 p.proj_surjective

variable (I) in
/-- The sheaf `𝒢` of the proof of Tag 0GAA: the kernel of `p^*((A/Iⁿ)^{⊕r}) ⟶ p^*M`, i.e. the
image of `p^*K ⟶ p^*((A/Iⁿ)^{⊕r})`. -/
abbrev blowupImage : (blowupScheme I).Modules :=
  kernel ((thickeningPullback I n).map (presProj p))

variable (I) in
/-- The map `p^*K ⟶ 𝒢`, the corestriction of `p^*K ⟶ p^*((A/Iⁿ)^{⊕r})`. -/
def blowupKernelLift : (thickeningPullback I n).obj p.kernel ⟶ blowupImage I p :=
  kernel.lift _ ((thickeningPullback I n).map (presIncl p)) (by
    rw [← CategoryTheory.Functor.map_comp, presIncl_comp_presProj, Functor.map_zero])

/-- `p^*K ⟶ 𝒢 ⟶ p^*((A/Iⁿ)^{⊕r})` is `p^*` of the inclusion. -/
@[reassoc (attr := simp)]
theorem blowupKernelLift_ι :
    blowupKernelLift I p ≫ kernel.ι _ = (thickeningPullback I n).map (presIncl p) :=
  kernel.lift_ι _ _ _

/-- **`p^*K ⟶ 𝒢` is an epimorphism**: `p^*` is right exact, so
`p^*K ⟶ p^*((A/Iⁿ)^{⊕r}) ⟶ p^*M ⟶ 0` is exact. -/
instance epi_blowupKernelLift : Epi (blowupKernelLift I p) :=
  ((exact_presIncl_presProj p).map_of_epi_of_preservesCokernel (thickeningPullback I n)
    (epi_presProj p) inferInstance).epi_kernelLift

variable (I) in
/-- The sheaf `ℱ` of the proof of Tag 0GAA: the kernel of `p^*K ⟶ 𝒢`. -/
abbrev blowupSupported : (blowupScheme I).Modules :=
  kernel (blowupKernelLift I p)

/-- `0 → kernel g → X → Y → 0` is short exact for an epimorphism `g`. -/
private theorem shortExact_kernel_ι_of_epi {C : Type*} [Category C] [Abelian C] {X Y : C}
    (g : X ⟶ Y) [Epi g] : (ShortComplex.mk (kernel.ι g) g (kernel.condition g)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _))
    inferInstance inferInstance

/-- `0 → 𝒢 → p^*((A/Iⁿ)^{⊕r}) → p^*M → 0` is short exact. -/
theorem shortExact_blowupImage :
    (ShortComplex.mk (kernel.ι ((thickeningPullback I n).map (presProj p)))
      ((thickeningPullback I n).map (presProj p)) (kernel.condition _)).ShortExact :=
  shortExact_kernel_ι_of_epi _

/-- `0 → ℱ → p^*K → 𝒢 → 0` is short exact. -/
theorem shortExact_blowupSupported :
    (ShortComplex.mk (kernel.ι (blowupKernelLift I p)) (blowupKernelLift I p)
      (kernel.condition _)).ShortExact :=
  shortExact_kernel_ι_of_epi _

/-- The twist of `0 → 𝒢 → p^*((A/Iⁿ)^{⊕r}) → p^*M → 0` by `𝒪_X(t)` is short exact. -/
theorem shortExact_blowupImage_twist (t : ℤ) :
    (ShortComplex.mk (kernel.ι ((thickeningPullback I n).map (presProj p)) ▷ blowupTwistInt I t)
      ((thickeningPullback I n).map (presProj p) ▷ blowupTwistInt I t)
      (whiskerRight_comp_whiskerRight_eq_zero I _ _ (kernel.condition _) _)).ShortExact :=
  shortExact_whiskerRight_blowupTwistInt I _ _ _ (shortExact_blowupImage p) t

/-- The twist of `0 → ℱ → p^*K → 𝒢 → 0` by `𝒪_X(t)` is short exact. -/
theorem shortExact_blowupSupported_twist (t : ℤ) :
    (ShortComplex.mk (kernel.ι (blowupKernelLift I p) ▷ blowupTwistInt I t)
      (blowupKernelLift I p ▷ blowupTwistInt I t)
      (whiskerRight_comp_whiskerRight_eq_zero I _ _ (kernel.condition _) _)).ShortExact :=
  shortExact_whiskerRight_blowupTwistInt I _ _ _ (shortExact_blowupSupported p) t

/-! #### Twisting down -/

/-- Twisting down `𝒪_X(t) ⟶ 𝒪_X(t')` is a morphism of the twisted sequences
`0 → 𝒢(t) → p^*((A/Iⁿ)^{⊕r})(t) → p^*M(t) → 0`. -/
def blowupImageTwistHom {t t' : ℤ} (h : t' ≤ t) :
    ShortComplex.mk (kernel.ι ((thickeningPullback I n).map (presProj p)) ▷ blowupTwistInt I t)
      ((thickeningPullback I n).map (presProj p) ▷ blowupTwistInt I t)
      (whiskerRight_comp_whiskerRight_eq_zero I _ _ (kernel.condition _) _) ⟶
    ShortComplex.mk (kernel.ι ((thickeningPullback I n).map (presProj p)) ▷ blowupTwistInt I t')
      ((thickeningPullback I n).map (presProj p) ▷ blowupTwistInt I t')
      (whiskerRight_comp_whiskerRight_eq_zero I _ _ (kernel.condition _) _) where
  τ₁ := blowupImage I p ◁ blowupTwistLE I h
  τ₂ := (thickeningPullback I n).obj (finFreeModule (A ⧸ I ^ n) p.rank) ◁ blowupTwistLE I h
  τ₃ := (thickeningPullback I n).obj M.1 ◁ blowupTwistLE I h
  comm₁₂ := whisker_exchange _ _
  comm₂₃ := whisker_exchange _ _

/-- **The connecting map `Hⁱ(X, p^*M(t)) → Hⁱ⁺¹(X, 𝒢(t))` is natural in the twist.** -/
theorem blowupHmodMap_whiskerLeft_δ_blowupImage (i : ℕ) {t t' : ℤ} (h : t' ≤ t)
    (x : blowupHmod I i ((thickeningPullback I n).obj M.1 ⊗ blowupTwistInt I t)) :
    blowupHmodMap I (i + 1) (blowupImage I p ◁ blowupTwistLE I h)
        ((blowupDeltaMod I).δ (shortExact_blowupImage_twist p t) i x) =
      (blowupDeltaMod I).δ (shortExact_blowupImage_twist p t') i
        (blowupHmodMap I i ((thickeningPullback I n).obj M.1 ◁ blowupTwistLE I h) x) :=
  (ConcreteCategory.congr_hom ((blowupDeltaMod I).δ_naturality (shortExact_blowupImage_twist p t)
    (shortExact_blowupImage_twist p t') (blowupImageTwistHom p h) i) x).symm

/-- **`Hⁱ(X, p^*K(t)) → Hⁱ(X, 𝒢(t))` is natural in the twist.** -/
theorem blowupHmodMap_whiskerLeft_blowupKernelLift (i : ℕ) {t t' : ℤ} (h : t' ≤ t)
    (x : blowupHmod I i ((thickeningPullback I n).obj p.kernel ⊗ blowupTwistInt I t)) :
    blowupHmodMap I i (blowupImage I p ◁ blowupTwistLE I h)
        (blowupHmodMap I i (blowupKernelLift I p ▷ blowupTwistInt I t) x) =
      blowupHmodMap I i (blowupKernelLift I p ▷ blowupTwistInt I t')
        (blowupHmodMap I i ((thickeningPullback I n).obj p.kernel ◁ blowupTwistLE I h) x) := by
  rw [← blowupHmodMap_comp_apply, ← blowupHmodMap_comp_apply, whisker_exchange]

/-- Twisting down on `Hⁱ(X, E(t))` is functorial. -/
theorem blowupHmodMap_whiskerLeft_blowupTwistLE_trans (E : (blowupScheme I).Modules) (i : ℕ)
    {t t' t'' : ℤ} (h : t' ≤ t) (h' : t'' ≤ t') (h'' : t'' ≤ t)
    (x : blowupHmod I i (E ⊗ blowupTwistInt I t)) :
    blowupHmodMap I i (E ◁ blowupTwistLE I h') (blowupHmodMap I i (E ◁ blowupTwistLE I h) x) =
      blowupHmodMap I i (E ◁ blowupTwistLE I h'') x := by
  rw [← blowupHmodMap_comp_apply, ← MonoidalCategory.whiskerLeft_comp, blowupTwistLE_trans]

variable [IsNoetherianRing A] in
omit [IsNoetherianRing A] in
/-- **Tag 0GA8 for the pulled back presentation**: every `a ∈ I^c` kills `ℱ`. An `a`-retraction
`r` of `K ⟶ (A/Iⁿ)^{⊕r}` (`IsANCModule.exists_comp_eq_smul_of_exact`) gives
`p^*K ⟶ p^*((A/Iⁿ)^{⊕r}) ⟶ p^*K = a`, and `p^*K ⟶ p^*((A/Iⁿ)^{⊕r})` vanishes on `ℱ`. -/
theorem globalSmulCenter_app_blowupSupported {a : A} (ha : a ∈ I ^ c) :
    (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app (blowupSupported I p) = 0 := by
  obtain ⟨r, hr⟩ := M.2.exists_comp_eq_smul_of_exact (presIncl p) (presProj p) p.incl_injective
    p.proj_surjective p.range_incl_eq_ker_proj (Ideal.mem_map_of_mem (Ideal.Quotient.mk _) ha)
  have hP : (thickeningPullback I n).map (presIncl p) ≫ (thickeningPullback I n).map r =
      (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).app _ := by
    rw [← CategoryTheory.Functor.map_comp, hr, thickeningPullback_map_smul,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have h0 : kernel.ι (blowupKernelLift I p) ≫ (thickeningPullback I n).map (presIncl p) = 0 := by
    rw [← blowupKernelLift_ι, kernel.condition_assoc, zero_comp]
  refine (cancel_mono (kernel.ι (blowupKernelLift I p))).1 ?_
  rw [zero_comp, ← (globalSmulCenter (blowupScheme I) (pullbackCoeff I a)).naturality
    (kernel.ι (blowupKernelLift I p)), ← hP, reassoc_of% h0, zero_comp]

/-- **The dotted arrow of the proof of Tag 0GAA, clause (3)**, as a map of sheaves
`𝒢(t) ⟶ p^*K(t - c)`: twisting down `p^*K(t) ⟶ p^*K(t - c)` kills `ℱ(t)` (Tag 0GA9, as `ℱ` is
killed by `I^c`), so it descends along the epimorphism `p^*K(t) ⟶ 𝒢(t)`. -/
def blowupDottedSheaf (t : ℤ) :
    blowupImage I p ⊗ blowupTwistInt I t ⟶
      (thickeningPullback I n).obj p.kernel ⊗ blowupTwistInt I (t - c) :=
  (CokernelCofork.IsColimit.desc' (shortExact_blowupSupported_twist p t).gIsCokernel
    ((thickeningPullback I n).obj p.kernel ◁
      blowupTwistLE I (sub_le_self t (Int.natCast_nonneg c))) (by
      change kernel.ι (blowupKernelLift I p) ▷ blowupTwistInt I t ≫ _ = 0
      rw [← whisker_exchange, whiskerLeft_blowupTwistLE_eq_zero I _
        (fun a ha => globalSmulCenter_app_blowupSupported p ha) _ (by lia), zero_comp])).1

/-- The dotted arrow lifts twisting down on `p^*K`. -/
theorem whiskerRight_blowupKernelLift_blowupDottedSheaf [IsNoetherianRing A] (t : ℤ) :
    blowupKernelLift I p ▷ blowupTwistInt I t ≫ blowupDottedSheaf p t =
      (thickeningPullback I n).obj p.kernel ◁
        blowupTwistLE I (sub_le_self t (Int.natCast_nonneg c)) :=
  (CokernelCofork.IsColimit.desc' (shortExact_blowupSupported_twist p t).gIsCokernel _ _).2

/-- **The dotted arrow factors twisting down on `𝒢`**: `𝒢(t) ⟶ p^*K(t - c) ⟶ 𝒢(t - c)` is
`𝒢(t) ⟶ 𝒢(t - c)`. -/
theorem blowupDottedSheaf_comp [IsNoetherianRing A] (t : ℤ) (h : t - c ≤ t) :
    blowupDottedSheaf p t ≫ blowupKernelLift I p ▷ blowupTwistInt I (t - c) =
      blowupImage I p ◁ blowupTwistLE I h := by
  have : Epi (blowupKernelLift I p ▷ blowupTwistInt I t) :=
    epi_whiskerRight_of_epi I _ inferInstance _
  refine (cancel_epi (blowupKernelLift I p ▷ blowupTwistInt I t)).1 ?_
  rw [reassoc_of% (whiskerRight_blowupKernelLift_blowupDottedSheaf p t), whisker_exchange]

end Presentation

/-! ### The `ModuleSituation` -/

section Situation

variable {n c : ℕ}

/-- **The `ModuleSituation` of Tag 0GAA on the blowup**, at any threshold `q₀` with the defining
property of `q(S)`. The cohomology groups are those of the twists of `p^*M`, of
`p^*((A/Iⁿ)^{⊕r})`, of `𝒢` and of `ℱ` on the blowup; the comparison maps are those of the long
exact sequences of `0 → 𝒢 → p^*((A/Iⁿ)^{⊕r}) → p^*M → 0` and `0 → ℱ → p^*K → 𝒢 → 0`, twisted.

The presentation is the chosen one `affinePres` (`(nonempty_ANCPresentation M).some`), the same
choice the affine witness makes. -/
def blowupModuleSituation (n c : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀) (hcn : c ≤ n) :
    ModuleSituation A I n c where
  toSituation := blowupSituationAt I q₀ h
  exponent_le := hcn
  pres := affinePres I n c
  H M i q := blowupHmod I i ((thickeningPullback I n).obj M.1 ⊗ blowupTwistInt I q)
  Hfree M i q := blowupHmod I i ((thickeningPullback I n).obj
    (finFreeModule (A ⧸ I ^ n) (affinePres I n c M).rank) ⊗ blowupTwistInt I q)
  HG M i q := blowupHmod I i (blowupImage I (affinePres I n c M) ⊗ blowupTwistInt I q)
  HF M i q := blowupHmod I i (blowupSupported I (affinePres I n c M) ⊗ blowupTwistInt I q)
  freeIso _ i q := (pullbackTwistFinFreeEquiv I n i q _).trans
    (LinearEquiv.piCongrRight fun _ => pullbackTwistUnitEquiv I n i q)
  subsingleton_Hdiv_zero i q := subsingleton_blowupHmod_thickeningTwist_zero I i q
  vanishing_H _ _ _ hi := subsingleton_blowupHmod_of_fibreDim_lt I _ hi
  vanishing_HG _ _ _ hi := subsingleton_blowupHmod_of_fibreDim_lt I _ hi
  vanishing_HF _ _ _ hi := subsingleton_blowupHmod_of_fibreDim_lt I _ hi
  freeToPullback M i q := pullbackTwistMap I n i q (presProj (affinePres I n c M))
  pullbackToImage M i q :=
    ((blowupDeltaMod I).δ (shortExact_blowupImage_twist (affinePres I n c M) q) i).hom
  exact_pullback M i q := exact_blowupHmodMap_δ I _ _ _
    (shortExact_blowupImage_twist (affinePres I n c M) q) i
  kernelToImage M i q :=
    (blowupHmodMap I i (blowupKernelLift I (affinePres I n c M) ▷ blowupTwistInt I q)).hom
  imageToSupported M i q :=
    ((blowupDeltaMod I).δ (shortExact_blowupSupported_twist (affinePres I n c M) q) i).hom
  exact_image M i q := exact_blowupHmodMap_δ I _ _ _
    (shortExact_blowupSupported_twist (affinePres I n c M) q) i

omit [IsNoetherianRing A] in
/-- `quotPointMap` is additive in the point. -/
theorem quotPointMap_add {n : ℕ} (N : ModuleCat.{u} (A ⧸ I ^ n)) (m m' : N) :
    quotPointMap I n N (m + m') = quotPointMap I n N m + quotPointMap I n N m' :=
  ModuleCat.hom_ext (LinearMap.toSpanSingleton_add (R := A ⧸ I ^ n) (M := N) m m')

omit [IsNoetherianRing A] in
/-- `quotPointMap` is linear in the point. -/
theorem quotPointMap_smul {n : ℕ} (N : ModuleCat.{u} (A ⧸ I ^ n)) (a : A ⧸ I ^ n) (m : N) :
    quotPointMap I n N (a • m) = a • quotPointMap I n N m :=
  ModuleCat.hom_ext (LinearMap.toSpanSingleton_smul (R := A ⧸ I ^ n) (M := N) a m)

omit [IsNoetherianRing A] in
/-- The `j`-th basis vector of `(A/Iⁿ)^{⊕r}` followed by `(A/Iⁿ)^{⊕r} ⟶ M` is the point map of
the image of the basis vector. -/
theorem finFreeIncl_comp_presProj {M : ANCModule I n c} (p : ANCPresentation I n c M)
    (j : Fin p.rank) :
    finFreeIncl (A ⧸ I ^ n) p.rank j ≫ presProj p = quotPointMap I n M.1 (p.proj (Pi.single j 1)) :=
  ModuleCat.hom_ext (LinearMap.ext_ring (by
    change p.proj (Pi.single j 1) = (1 : A ⧸ I ^ n) • p.proj (Pi.single j 1)
    rw [one_smul]))

/-- The canonical map `I^q/I^{q+n} → H⁰(X, 𝒪_{Yₙ}(q))` of the Situation (zero for `n = 0`, where
the target vanishes), with its target written as the cohomology of `𝒪_{Yₙ} ⊗ 𝒪_X(q)`. -/
def blowupCdiv {q₀ : ℕ} (h : IsBaseThreshold I q₀) (n q : ℕ) :
    powQuot I q n →ₗ[A] blowupHmod I 0 (thickeningSheaf I n ⊗ blowupTwistInt I q) :=
  (blowupSituationAt I q₀ h).cdiv n q

/-- **The canonical map `I^q ⊗_A N → H⁰(X, p^*N(q))`** for an `A/Iⁿ`-module `N`: `x ⊗ m` goes to
the image of the canonical section `x` of `𝒪_{Yₙ}(q) = p^*(A/Iⁿ)(q)` under `p^*` of
`A/Iⁿ → N`, `1 ↦ m`. It is well defined on `I^q/I^{q+n}`, because `I^q/I^{q+n} → H⁰(X, 𝒪_{Yₙ}(q))`
is. -/
def blowupSecM (n : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀) (N : ModuleCat.{u} (A ⧸ I ^ n))
    (q : ℕ) :
    powTensor I n q N →ₗ[A] blowupHmod I 0 ((thickeningPullback I n).obj N ⊗ blowupTwistInt I q) :=
  TensorProduct.lift (LinearMap.mk₂ A
    (fun x m => pullbackTwistMap I n 0 q (quotPointMap I n N m)
      ((pullbackTwistUnitEquiv I n 0 q).symm (blowupCdiv I h n q x)))
    (fun x x' m => by rw [map_add, map_add, map_add])
    (fun a x m => by rw [map_smul, map_smul, map_smul])
    (fun x m m' => by
      rw [show quotPointMap I n N (m + m') = quotPointMap I n N m + quotPointMap I n N m' from
        quotPointMap_add I N m m', pullbackTwistMap_add])
    (fun a x m => by
      rw [show quotPointMap I n N (a • m) = Ideal.Quotient.mk (I ^ n) a • quotPointMap I n N m from
        quotPointMap_smul I N _ m, pullbackTwistMap_zero_smul]))

/-- The defining formula of `blowupSecM` on pure tensors. -/
theorem blowupSecM_tmul (n : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀)
    (N : ModuleCat.{u} (A ⧸ I ^ n)) (q : ℕ) (x : powQuot I q n) (m : resModule I n N) :
    blowupSecM I n h N q (x ⊗ₜ m) = pullbackTwistMap I n 0 q (quotPointMap I n N m)
      ((pullbackTwistUnitEquiv I n 0 q).symm (blowupCdiv I h n q x)) :=
  rfl

/-- **The `TwistedModuleSituation` of Tag 0GAA on the blowup.** The twisting-down maps are
induced by `𝒪_X(q) ⟶ 𝒪_X(q')`, the dotted arrow is `blowupDottedSheaf` (Tags 0GA8, 0GA9), and the
canonical map `I^q ⊗_A M → H⁰(X, p^*M(q))` is `blowupSecM`. -/
def blowupTwistedModuleSituation (n c : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀) (hcn : c ≤ n) :
    TwistedModuleSituation A I n c where
  toModuleSituation := blowupModuleSituation I n c h hcn
  Htr M i q q' hq :=
    (blowupHmodMap I i ((thickeningPullback I n).obj M.1 ◁ blowupTwistLE I hq)).hom
  HGtr M i q q' hq :=
    (blowupHmodMap I i (blowupImage I (affinePres I n c M) ◁ blowupTwistLE I hq)).hom
  HGtr_trans M i q q' q'' hq hq' hq'' x :=
    blowupHmodMap_whiskerLeft_blowupTwistLE_trans _ i hq hq' hq'' x
  pullbackToImage_tr M i q q' hq x :=
    blowupHmodMap_whiskerLeft_δ_blowupImage (affinePres I n c M) i hq x
  kernelToImage_tr M i q q' hq x :=
    blowupHmodMap_whiskerLeft_blowupKernelLift (affinePres I n c M) i hq x
  dotted M i q := (blowupHmodMap I i (blowupDottedSheaf (affinePres I n c M) q)).hom
  kernelToImage_dotted M i q hq x :=
    (blowupHmodMap_comp_apply I i _ _ x).symm.trans
      (congrArg (fun φ => blowupHmodMap I i φ x) (blowupDottedSheaf_comp _ q hq))
  secM M q := blowupSecM I n h M.1 q
  secM_freeSections M q v := by
    change blowupSecM I n h M.1 q _ = pullbackTwistMap I n 0 q (presProj (affinePres I n c M))
      ((pullbackTwistFinFreeEquiv I n 0 q _).symm
        (fun j => (pullbackTwistUnitEquiv I n 0 q).symm (blowupCdiv I h n q (v j))))
    rw [pullbackTwistFinFreeEquiv_symm_apply, ANCPresentation.freeTensor_apply, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (blowupSecM_tmul I n h M.1 q (v j) _).trans
      ((congrArg (fun f => pullbackTwistMap I n 0 q f
          ((pullbackTwistUnitEquiv I n 0 q).symm (blowupCdiv I h n q (v j))))
        (finFreeIncl_comp_presProj I (affinePres I n c M) j).symm).trans
        (pullbackTwistMap_comp _ _ _ _ _))

/-! ### The `DualSituation` -/

omit [IsNoetherianRing A] in
/-- Applying `p^*` of a map into `A/Iⁿ` and then `p^*(A/Iⁿ) ≅ 𝒪_{Yₙ}` on twisted cohomology. -/
theorem blowupHmodMap_whiskerRight_comp_unitIso {n : ℕ} (i : ℕ) (t : ℤ)
    {N : ModuleCat.{u} (A ⧸ I ^ n)} (f : N ⟶ ModuleCat.of (A ⧸ I ^ n) (A ⧸ I ^ n))
    (y : blowupHmod I i ((thickeningPullback I n).obj N ⊗ blowupTwistInt I t)) :
    blowupHmodMap I i (((thickeningPullback I n).map f ≫ (thickeningPullbackUnitIso I n).hom) ▷
        blowupTwistInt I t) y =
      pullbackTwistUnitEquiv I n i t (pullbackTwistMap I n i t f y) := by
  rw [MonoidalCategory.comp_whiskerRight, blowupHmodMap_comp_apply]
  rfl

omit [IsNoetherianRing A] in
/-- **Twisting down on the canonical sections of `𝒪_{Yₙ}(q)`**: the composite
`I^q/I^{q+n} → H⁰(X, 𝒪_{Yₙ}(q)) → H⁰(X, 𝒪_{Yₙ}(q'))` is
`I^q/I^{q+n} → I^{q'}/I^{q'+n} → H⁰(X, 𝒪_{Yₙ}(q'))`. -/
theorem blowupHmodMap_whiskerLeft_cdivMod (m : ℕ) {q q' : ℕ} (h : (q' : ℤ) ≤ q) (hle : q' ≤ q)
    (w : powQuot I q (m + 1)) :
    blowupHmodMap I 0 (thickeningSheaf I (m + 1) ◁ blowupTwistLE I h) (cdivMod I m q w) =
      cdivMod I m q' (powQuotLe I hle w) := by
  induction w using Submodule.Quotient.induction_on with
  | H x =>
    rw [powQuotLe_mk, cdivMod_mk, cdivMod_mk]
    exact (blowupΓmodToH0_naturality I _ _).symm.trans (congrArg (blowupΓmodToH0 I _)
      (blowupΓMap_whiskerLeft_blowupTwistLE_thickeningSections I (m + 1) h x))

omit [IsNoetherianRing A] in
/-- `1 ↦ λ` followed by evaluation at `z` is multiplication by `λ(z)`. -/
theorem quotPointMap_comp_dualEvalAt {n : ℕ} (N : ModuleCat.{u} (A ⧸ I ^ n))
    (lam : resModule I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) N)))
    (z : resModule I n N) :
    quotPointMap I n (ModuleCat.of (A ⧸ I ^ n) (Module.Dual (A ⧸ I ^ n) N)) lam ≫
        dualEvalAt I N z = (show Module.Dual (A ⧸ I ^ n) N from lam) z • 𝟙 _ :=
  ModuleCat.hom_ext (LinearMap.ext_ring (by
    change ((1 : A ⧸ I ^ n) • (show Module.Dual (A ⧸ I ^ n) N from lam)) z =
      (show Module.Dual (A ⧸ I ^ n) N from lam) z • (1 : A ⧸ I ^ n)
    rw [one_smul, smul_eq_mul, mul_one]))

/-- **The evaluation dictionary is natural in the twist.** -/
theorem blowupDualEv_whiskerLeft (m : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀) {q q' : ℕ}
    (hq : q₀ ≤ q) (hq' : q₀ ≤ q') (hle : q' ≤ q) (h' : (q' : ℤ) ≤ q)
    (N : ModuleCat.{u} (A ⧸ I ^ (m + 1)))
    (x : blowupHmod I 0 ((thickeningPullback I (m + 1)).obj
        (ModuleCat.of _ (Module.Dual (A ⧸ I ^ (m + 1)) N)) ⊗ blowupTwistInt I q)) :
    blowupDualEv I m h hq' N (blowupHmodMap I 0 ((thickeningPullback I (m + 1)).obj
        (ModuleCat.of _ (Module.Dual (A ⧸ I ^ (m + 1)) N)) ◁ blowupTwistLE I h') x) =
      (powQuotLe I hle).comp (blowupDualEv I m h hq N x) := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.comp_apply, blowupDualEv_apply, blowupDualEv_apply, ← blowupHmodMap_comp_apply,
    whisker_exchange, blowupHmodMap_comp_apply]
  obtain ⟨w, hw⟩ := (bijective_cdivMod_of_le I h hq).2
    (blowupHmodMap I 0 (((thickeningPullback I (m + 1)).map (dualEvalAt I N z) ≫
      (thickeningPullbackUnitIso I (m + 1)).hom) ▷ blowupTwistInt I q) x)
  rw [← hw, blowupHmodMap_whiskerLeft_cdivMod I m h' hle,
    LinearEquiv.ofBijective_symm_apply_apply, LinearEquiv.ofBijective_symm_apply_apply]

/-- **On the canonical sections the evaluation dictionary is the evaluation pairing**: the
section attached to `x ⊗ λ` evaluates on `z` to `λ(z)·x`. -/
theorem blowupDualEv_blowupSecM (m : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀) {q : ℕ}
    (hq : q₀ ≤ q) (N : ModuleCat.{u} (A ⧸ I ^ (m + 1))) (x : powQuot I q (m + 1))
    (lam : resModule I (m + 1) (ModuleCat.of _ (Module.Dual (A ⧸ I ^ (m + 1)) N))) :
    blowupDualEv I m h hq N
        (blowupSecM I (m + 1) h (ModuleCat.of _ (Module.Dual (A ⧸ I ^ (m + 1)) N)) q
          (x ⊗ₜ lam)) =
      dualHom I (m + 1) q lam x := by
  refine LinearMap.ext fun z => ?_
  rw [blowupDualEv_apply, blowupSecM_tmul, blowupHmodMap_whiskerRight_comp_unitIso,
    ← pullbackTwistMap_comp, quotPointMap_comp_dualEvalAt]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective
    ((show Module.Dual (A ⧸ I ^ (m + 1)) N from lam) z)
  rw [← hb, pullbackTwistMap_zero_smul, pullbackTwistMap_id, map_smul,
    LinearEquiv.apply_symm_apply, map_smul]
  refine (congrArg (b • ·) (LinearEquiv.ofBijective_symm_apply_apply _ x)).trans ?_
  change b • x = powQuotScalar I (m + 1) q x ((show Module.Dual (A ⧸ I ^ (m + 1)) N from lam) z)
  rw [← hb, powQuotScalar_apply_mk]

/-- **The `DualSituation` of Tag 0GAC on the blowup**, for `n = m + 1` and any threshold `q₀`
with the defining property of `q(S)`: the evaluation dictionary is `blowupDualEv`. -/
def blowupDualSituation (m c : ℕ) (hcn : c ≤ m + 1) {q₀ : ℕ} (h : IsBaseThreshold I q₀) :
    DualSituation A I (m + 1) c where
  toTwistedModuleSituation := blowupTwistedModuleSituation I (m + 1) c h hcn
  ev M _ hq := blowupDualEv I m h hq M.1
  ev_Htr M _ _ hq hq' hle h' x := blowupDualEv_whiskerLeft I m h hq hq' hle h' M.1 x
  ev_secM M _ hq x lam := blowupDualEv_blowupSecM I m h hq M.1 x lam

/-- The Situation underlying `blowupModuleSituation` is `blowupSituationAt`. -/
@[simp] theorem blowupModuleSituation_toSituation (n c : ℕ) {q₀ : ℕ} (h : IsBaseThreshold I q₀)
    (hcn : c ≤ n) : (blowupModuleSituation I n c h hcn).toSituation = blowupSituationAt I q₀ h :=
  rfl

/-! ### At `q₀ = q(S)` -/

/-- `blowupModuleSituation` at `q₀ = q(S)`. -/
def blowupModuleSituationQS (n c : ℕ) (hcn : c ≤ n) : ModuleSituation A I n c :=
  blowupModuleSituation I n c (isBaseThreshold_qS I) hcn

/-- `blowupTwistedModuleSituation` at `q₀ = q(S)`. -/
def blowupTwistedModuleSituationQS (n c : ℕ) (hcn : c ≤ n) : TwistedModuleSituation A I n c :=
  blowupTwistedModuleSituation I n c (isBaseThreshold_qS I) hcn

/-- `blowupDualSituation` at `q₀ = q(S)`. -/
def blowupDualSituationQS (m c : ℕ) (hcn : c ≤ m + 1) : DualSituation A I (m + 1) c :=
  blowupDualSituation I m c hcn (isBaseThreshold_qS I)

/-- The Situation underlying `blowupModuleSituationQS` is `blowupSituationQS`. -/
@[simp] theorem blowupModuleSituationQS_toSituation (n c : ℕ) (hcn : c ≤ n) :
    (blowupModuleSituationQS I n c hcn).toSituation = blowupSituationQS I :=
  rfl

/-- The integer `d` of `blowupModuleSituationQS` is `d(S)`. -/
@[simp] theorem blowupModuleSituationQS_d (n c : ℕ) (hcn : c ≤ n) :
    (blowupModuleSituationQS I n c hcn).d = fibreDim I :=
  rfl

/-- The threshold of `blowupModuleSituationQS` is `q(S)`. -/
@[simp] theorem blowupModuleSituationQS_q₀ (n c : ℕ) (hcn : c ≤ n) :
    (blowupModuleSituationQS I n c hcn).q₀ = qS I :=
  rfl

/-- `blowupTwistedModuleSituationQS` extends `blowupModuleSituationQS`. -/
@[simp] theorem blowupTwistedModuleSituationQS_toModuleSituation (n c : ℕ) (hcn : c ≤ n) :
    (blowupTwistedModuleSituationQS I n c hcn).toModuleSituation =
      blowupModuleSituationQS I n c hcn :=
  rfl

/-- The integer `d` of `blowupTwistedModuleSituationQS` is `d(S)`. -/
@[simp] theorem blowupTwistedModuleSituationQS_d (n c : ℕ) (hcn : c ≤ n) :
    (blowupTwistedModuleSituationQS I n c hcn).d = fibreDim I :=
  rfl

/-- The threshold of `blowupTwistedModuleSituationQS` is `q(S)`. -/
@[simp] theorem blowupTwistedModuleSituationQS_q₀ (n c : ℕ) (hcn : c ≤ n) :
    (blowupTwistedModuleSituationQS I n c hcn).q₀ = qS I :=
  rfl

/-- `blowupDualSituationQS` extends `blowupTwistedModuleSituationQS`. -/
@[simp] theorem blowupDualSituationQS_toTwistedModuleSituation (m c : ℕ) (hcn : c ≤ m + 1) :
    (blowupDualSituationQS I m c hcn).toTwistedModuleSituation =
      blowupTwistedModuleSituationQS I (m + 1) c hcn :=
  rfl

/-- The integer `d` of `blowupDualSituationQS` is `d(S)`. -/
@[simp] theorem blowupDualSituationQS_d (m c : ℕ) (hcn : c ≤ m + 1) :
    (blowupDualSituationQS I m c hcn).d = fibreDim I :=
  rfl

/-- The threshold of `blowupDualSituationQS` is `q(S)`. -/
@[simp] theorem blowupDualSituationQS_q₀ (m c : ℕ) (hcn : c ≤ m + 1) :
    (blowupDualSituationQS I m c hcn).q₀ = qS I :=
  rfl

/-- The evaluation dictionary of `blowupDualSituationQS` is `blowupDualEv`. -/
theorem blowupDualSituationQS_ev (m c : ℕ) (hcn : c ≤ m + 1) (M : ANCModule I (m + 1) c) (q : ℕ)
    (hq : (blowupDualSituationQS I m c hcn).q₀ ≤ q) :
    (blowupDualSituationQS I m c hcn).ev M q hq = blowupDualEv I m (isBaseThreshold_qS I) hq M.1 :=
  rfl

end Situation

end Stacks.LocalCohomology.UniformityIII

end
