module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamPairFunctoriality

/-!
# The de Rham map of a morphism of pairs presenting a divided power polynomial algebra

Let `f : (B, I, δ) → (C, K, ε)` be a divided power morphism of `A`-algebras and suppose that `C`
*is* a divided power polynomial algebra over `B`: there is an isomorphism of divided power
`A`-algebras `e : B⟨x_w : w ∈ W⟩ ≅ C` with `e ∘ (B → B⟨x_w⟩) = f`.  Let `(M, ∇)` be a `B`-module
with integrable connection and `(N, ∇')` a `C`-module with integrable connection, and let
`μ : M → N` be a horizontal `f`-semilinear map whose linearisation `C ⊗_B M → N` is bijective (for
the values of a crystal in quasi-coherent modules this is the crystal property).  Then the map of
de Rham complexes

`M ⊗_B Ω^*_{B/A,δ} ⟶ N ⊗_C Ω^*_{C/A,ε}`

of `Crystalline.DeRhamPair.deRhamMap` is a quasi-isomorphism
(`Crystalline.DeRhamPair.quasiIso_deRhamMap_of_dpPolynomial`).  This is the first clause of
[Stacks, Lemma 60.19.2, Tag 07LD]
(`Crystalline.DividedPowerPolynomial.quasiIso_polyDeRhamComparison`) transported along the
isomorphism `e`, in the form the row comparisons of the Čech–de Rham double complex of a crystal
use: there `f` is the map induced by a projection of the Čech nerve, and `e`
presents the divided power envelope of the diagonal as a divided power polynomial algebra.

## Main definitions

* `Crystalline.DeRhamPair.polyRing` — `B⟨x_w⟩` as a divided power ring.
* `Crystalline.DeRhamPair.polyModuleMap` — `C ⊗_B M ⟵ B⟨x_w⟩ ⊗_B M ⟶ N`, `q ⊗ m ↦ e(q) μ(m)`.

## Main results

* `Crystalline.DeRhamPair.deRhamMap_eq_comp` — the de Rham map of `(f, μ)` is the canonical
  comparison of [Stacks, Tag 07PY] followed by the de Rham map of `(e, polyModuleMap)`.
* `Crystalline.DeRhamPair.quasiIso_deRhamMap_of_dpPolynomial` — **the de Rham map is a
  quasi-isomorphism.**

## References

* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 07PY](https://stacks.math.columbia.edu/tag/07PY)
-/

@[expose] public noncomputable section

open CategoryTheory
open DividedPowers
open scoped TensorProduct
open Stacks.DeRham.DifferentialDescent
open Crystalline.DividedPowerPolynomial

universe u w

namespace Crystalline.DeRhamPair

variable {A : Type u} [CommRing A] {B : DividedPowerRing.{u}} [Algebra A B] (W : Type u)

variable (B) in
/-- The divided power polynomial algebra `B⟨x_w : w ∈ W⟩` as a divided power ring. -/
abbrev polyRing : DividedPowerRing.{u} :=
  DividedPowerRing.of (setIndexedDividedPowerPolynomialAlgebra B W)
    (dividedPowerPolynomialIdeal B.ideal W) (setIndexedDividedPowerPolynomialDividedPowers B W)

variable {C : DividedPowerRing.{u}} [Algebra A C]
  (f : (B : Type u) →ₐ[A] C) (hf : IsDPMorphism B.dividedPowers C.dividedPowers f.toRingHom)
  {M : Type (max u w)} [AddCommGroup M] [Module (B : Type u) M]
  {N : Type (max u w)} [AddCommGroup N] [Module (C : Type u) N]
  (μ : M →ₛₗ[f.toRingHom] N)
  (e : (polyRing B W : Type u) →ₐ[A] C)
  (he : IsDPMorphism (polyRing B W).dividedPowers C.dividedPowers e.toRingHom)
  (hfe : ∀ b : (B : Type u), e (coefficientAlgHom A B W b) = f b)

/-- The additive map underlying `polyModuleMap`. -/
def polyModuleAdd : (setIndexedDividedPowerPolynomialAlgebra B W ⊗[(B : Type u)] M) →+ N :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun q ↦ AddMonoidHom.mk' (fun m ↦ e q • μ m)
        (fun m m' ↦ by rw [map_add, smul_add]))
      (fun q q' ↦ by
        ext m
        change e (q + q') • μ m = e q • μ m + e q' • μ m
        rw [map_add, add_smul]))
    (fun b q m ↦ by
      simp only [AddMonoidHom.mk'_apply]
      rw [Algebra.smul_def, map_mul, mul_smul, map_smulₛₗ, smul_comm]
      congr 1
      change e (coefficientAlgHom A B W b) • μ m = f b • μ m
      rw [hfe])

/-- `polyModuleAdd` on a pure tensor. -/
theorem polyModuleAdd_tmul (q : setIndexedDividedPowerPolynomialAlgebra B W) (m : M) :
    polyModuleAdd W f μ e hfe (q ⊗ₜ m) = e q • μ m := rfl

/-- The linearisation `B⟨x_w⟩ ⊗_B M → N`, `q ⊗ m ↦ e(q) μ(m)`, semilinear over `e`. -/
def polyModuleMap :
    (setIndexedDividedPowerPolynomialAlgebra B W ⊗[(B : Type u)] M) →ₛₗ[e.toRingHom] N where
  toFun := polyModuleAdd W f μ e hfe
  map_add' := map_add _
  map_smul' q z := by
    induction z using TensorProduct.inductionOn with
    | tmul q' m =>
      rw [TensorProduct.smul_tmul', polyModuleAdd_tmul, polyModuleAdd_tmul, smul_eq_mul,
        map_mul, mul_smul]
      rfl
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `polyModuleMap` on a pure tensor. -/
theorem polyModuleMap_tmul (q : setIndexedDividedPowerPolynomialAlgebra B W) (m : M) :
    polyModuleMap W f μ e hfe (q ⊗ₜ m) = e q • μ m := rfl

include hfe in
/-- The map of one-forms induced by `e` restricts to the one induced by `f`. -/
theorem oneFormsMap_oneFormComparison
    (ω : dividedPowerDifferentials (A := A) B.dividedPowers) :
    oneFormsMap e he (oneFormComparison A B W ω) = oneFormsMap f hf ω := by
  have key : ∀ x ∈ Submodule.span (B : Type u)
      (Set.range (dividedPowerDifferential (A := A) B.dividedPowers)),
      oneFormsMap e he (oneFormComparison A B W x) = oneFormsMap f hf x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      change mapDifferentialsOfDPMorphism (A := A) (J := (polyRing B W).ideal)
          (delta := (polyRing B W).dividedPowers) C.dividedPowers e he
          (mapDifferentialsOfDPMorphism (A := A) (J := B.ideal) (delta := B.dividedPowers)
            (setIndexedDividedPowerPolynomialDividedPowers B W) (coefficientAlgHom A B W)
            (coefficientAlgHom_isDPMorphism A B W)
            (dividedPowerDifferential (A := A) B.dividedPowers b)) =
        mapDifferentialsOfDPMorphism (A := A) (J := B.ideal) (delta := B.dividedPowers)
          C.dividedPowers f hf (dividedPowerDifferential (A := A) B.dividedPowers b)
      rw [mapDifferentialsOfDPMorphism_d, mapDifferentialsOfDPMorphism_d,
        mapDifferentialsOfDPMorphism_d, hfe]
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul b x _ hx =>
      rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hx]
      congr 1
      exact hfe b
  exact key ω (by simp [dividedPowerDifferentials_span (A := A) B.dividedPowers])

variable (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
  (nabla' : Connection A (C : Type u) (oneVariableBaseProjection A C) N)

include he hfe in
/-- `polyModuleMap` carries the base change of `μ`'s coefficients to the map `μ`. -/
theorem tensorMap_baseChangeValues
    (y : M ⊗[(B : Type u)] dividedPowerDifferentials (A := A) B.dividedPowers) :
    tensorMap e (polyModuleMap W f μ e hfe) (oneFormsMap e he)
        (Connection.baseChangeValues (oneFormComparison A B W) y) =
      tensorMap f μ (oneFormsMap f hf) y := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m η =>
    rw [Connection.baseChangeValues_tmul, tensorMap_tmul, tensorMap_tmul, polyModuleMap_tmul,
      map_one, one_smul, oneFormsMap_oneFormComparison W f hf e he hfe]

include hf in
/-- **`polyModuleMap` is horizontal** for the base change of `∇` to `B⟨x_w⟩ ⊗_B M`, when `μ` is
horizontal. -/
theorem isHorizontal_polyModuleMap (hμ : IsHorizontal f hf μ nabla nabla') :
    IsHorizontal (B := polyRing B W) e he (polyModuleMap W f μ e hfe)
      (polyBaseChangeConnection A B W nabla) nabla' := by
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, Connection.map_add, Connection.map_add, hx, hy, map_add]
  | tmul q m =>
    rw [polyModuleMap_tmul, Connection.leibniz, hμ m]
    change _ = tensorMap e (polyModuleMap W f μ e hfe) (oneFormsMap e he)
      (Connection.baseChange (oneFormComparison A B W) nabla
        (oneFormComparison_compatible A B W) (q ⊗ₜ m))
    rw [Connection.baseChange_tmul, map_add, tensorMap_smul,
      tensorMap_baseChangeValues W f hf μ e he hfe, tensorMap_tmul, polyModuleMap_tmul, map_one,
      one_smul]
    congr 2
    exact (mapDifferentialsOfDPMorphism_d (A := A) (J := (polyRing B W).ideal)
      (delta := (polyRing B W).dividedPowers) C.dividedPowers e he q).symm

/-! ### The comparison of de Rham complexes -/

omit [Algebra A B] in
/-- **Additive maps out of `M ⊗_B ⋀^p Ω` are determined by their values on `m ⊗ ω₁ ∧ ⋯ ∧ ω_p`**,
these elements spanning additively. -/
theorem addMonoidHom_ext_tmul_ιMulti {R : Type*} [CommRing R] {L Q : Type*} [AddCommGroup L]
    [Module R L] [AddCommGroup Q] [Module R Q] {P : Type*} [AddCommGroup P] {p : ℕ}
    {F G : L ⊗[R] ⋀[R]^p Q →+ P}
    (h : ∀ (m : L) (ω : Fin p → Q),
      F (m ⊗ₜ exteriorPower.ιMulti R p ω) = G (m ⊗ₜ exteriorPower.ιMulti R p ω)) : F = G := by
  have key : ∀ y : ⋀[R]^p Q, ∀ m : L, F (m ⊗ₜ y) = G (m ⊗ₜ y) := by
    intro y
    have hy : y ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R p)) := by
      simp [exteriorPower.ιMulti_span]
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨ω, rfl⟩ := hz
      exact fun m => h m ω
    | zero => intro m; simp only [TensorProduct.tmul_zero, map_zero]
    | add x z _ _ hx hz => intro m; simp only [TensorProduct.tmul_add, map_add, hx, hz]
    | smul b x _ hx => intro m; rw [← TensorProduct.smul_tmul, hx]
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul m y => exact key y m
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The canonical comparison of [Stacks, Tag 07PY] on a pure wedge, read in the spelling of
`polyRing`. -/
theorem polyComparison_tmul_ιMulti (hint : Connection.IsIntegrable (oneVariableBaseSource A B)
      (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
      (oneVariableBaseGenerationHypothesis A B) nabla) (p : ℕ) (m : M)
    (ω : Fin p → dividedPowerDifferentials (A := A) B.dividedPowers) :
    RestrictScalars.addEquiv A (polyRing B W : Type u) _
        (polyComparison A B W nabla hint p
          ((RestrictScalars.addEquiv A (B : Type u) _).symm
            (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p ω))) =
      ((1 : (polyRing B W : Type u)) ⊗ₜ[(B : Type u)] m) ⊗ₜ[(polyRing B W : Type u)]
        exteriorPower.ιMulti (polyRing B W : Type u) p (oneFormComparison A B W ∘ ω) :=
  polyComparison_ιMulti A B W nabla hint p m ω

/-- The de Rham map of `(e, polyModuleMap)` on `(1 ⊗ m) ⊗ ω`. -/
theorem tensorMap_polyModuleMap_one_tmul (p : ℕ) (m : M)
    (ω : ⋀[(polyRing B W : Type u)]^p
      (dividedPowerDifferentials (A := A) (polyRing B W).dividedPowers)) :
    tensorMap (B := polyRing B W) e (polyModuleMap W f μ e hfe) (formsMap e he p)
        (((1 : (polyRing B W : Type u)) ⊗ₜ[(B : Type u)] m) ⊗ₜ[(polyRing B W : Type u)] ω) =
      μ m ⊗ₜ[(C : Type u)] formsMap (B := polyRing B W) e he p ω := by
  change (e 1 • μ m) ⊗ₜ[(C : Type u)] _ = _
  rw [map_one, one_smul]
  rfl

include hf hfe in
/-- The forms maps of `f` and of `e` agree on a wedge of one-forms of `B`. -/
theorem formsMap_ιMulti_oneFormComparison (p : ℕ)
    (ω : Fin p → dividedPowerDifferentials (A := A) B.dividedPowers) :
    formsMap f hf p (exteriorPower.ιMulti (B : Type u) p ω) =
      formsMap (B := polyRing B W) e he p
        (exteriorPower.ιMulti (polyRing B W : Type u) p (oneFormComparison A B W ∘ ω)) := by
  rw [formsMap, formsMap, mapDifferentialFormsOfDPMorphism_ιMulti,
    mapDifferentialFormsOfDPMorphism_ιMulti]
  exact congrArg _ (funext fun j => (oneFormsMap_oneFormComparison W f hf e he hfe (ω j)).symm)

include hf in
/-- `termMap_eq_comp` on a pure wedge. -/
theorem termMap_eq_comp_tmul (hint : Connection.IsIntegrable (oneVariableBaseSource A B)
      (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
      (oneVariableBaseGenerationHypothesis A B) nabla) (p : ℕ) (m : M)
    (ω : Fin p → dividedPowerDifferentials (A := A) B.dividedPowers) :
    RestrictScalars.addEquiv A (C : Type u) _ (termMap f hf μ p
        ((RestrictScalars.addEquiv A (B : Type u) _).symm
          (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p ω))) =
      RestrictScalars.addEquiv A (C : Type u) _
        (termMap (B := polyRing B W) e he (polyModuleMap W f μ e hfe) p
          (polyComparison A B W nabla hint p
            ((RestrictScalars.addEquiv A (B : Type u) _).symm
              (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p ω)))) := by
  rw [termMap_apply, termMap_apply, polyComparison_tmul_ιMulti W nabla hint p m ω,
    tensorMap_polyModuleMap_one_tmul W f μ e he hfe p m,
    ← formsMap_ιMulti_oneFormComparison W f hf e he hfe p ω]
  rfl

include hf in
/-- **The de Rham map of `(f, μ)` factors through the canonical comparison of
[Stacks, Tag 07PY]**: degreewise it is `polyComparison` followed by the de Rham map of
`(e, polyModuleMap)`. -/
theorem termMap_eq_comp (hint : Connection.IsIntegrable (oneVariableBaseSource A B)
      (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
      (oneVariableBaseGenerationHypothesis A B) nabla) (p : ℕ) (x : oneVariableSourceTerm A B M p) :
    termMap f hf μ p x = termMap (B := polyRing B W) e he (polyModuleMap W f μ e hfe) p
      (polyComparison A B W nabla hint p x) := by
  obtain ⟨y, rfl⟩ := (RestrictScalars.addEquiv A (B : Type u) _).symm.surjective x
  let eB := RestrictScalars.addEquiv A (B : Type u)
    (M ⊗[(B : Type u)] ⋀[(B : Type u)]^p (dividedPowerDifferentials (A := A) B.dividedPowers))
  let eC := RestrictScalars.addEquiv A (C : Type u)
    (N ⊗[(C : Type u)] ⋀[(C : Type u)]^p (dividedPowerDifferentials (A := A) C.dividedPowers))
  exact eC.injective (DFunLike.congr_fun (addMonoidHom_ext_tmul_ιMulti (R := (B : Type u))
    (F := eC.toAddMonoidHom.comp ((termMap f hf μ p).toAddMonoidHom.comp eB.symm.toAddMonoidHom))
    (G := eC.toAddMonoidHom.comp
      (((termMap (B := polyRing B W) e he (polyModuleMap W f μ e hfe) p).toAddMonoidHom.comp
      (polyComparison A B W nabla hint p).toAddMonoidHom).comp eB.symm.toAddMonoidHom))
    fun m ω => termMap_eq_comp_tmul W f hf μ e he hfe nabla hint p m ω) y)

include hf in
/-- **The de Rham map of `(f, μ)` is the canonical comparison of [Stacks, Tag 07PY] followed by
the de Rham map of `(e, polyModuleMap)`.** -/
theorem deRhamMap_eq_comp (hint : Connection.IsIntegrable (oneVariableBaseSource A B)
      (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
      (oneVariableBaseGenerationHypothesis A B) nabla)
    (hint' : Connection.IsIntegrable (oneVariableBaseSource A C) (oneVariableBaseProjection A C)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A C) nabla')
    (hμ : IsHorizontal f hf μ nabla nabla') :
    deRhamMap f hf μ nabla hint nabla' hint' hμ =
      polyDeRhamComparison A B W nabla hint ≫
        deRhamMap (B := polyRing B W) e he (polyModuleMap W f μ e hfe)
          (polyBaseChangeConnection A B W nabla)
          (polyBaseChangeConnection_isIntegrable A B W nabla hint) nabla' hint'
          (isHorizontal_polyModuleMap W f hf μ e he hfe nabla nabla' hμ) := by
  ext p x
  exact termMap_eq_comp W f hf μ e he hfe nabla hint p x

/-! ### Isomorphisms of pairs, and the quasi-isomorphism -/

section Iso

variable {B' C' : DividedPowerRing.{u}} [Algebra A B'] [Algebra A C']
  {M' N' : Type (max u w)} [AddCommGroup M'] [Module (B' : Type u) M'] [AddCommGroup N']
  [Module (C' : Type u) N']

/-- The degreewise map of a morphism of pairs whose ring map is the identity pointwise and whose
module map is the identity is the identity. -/
theorem termMap_eq_self (g : (B' : Type u) →ₐ[A] B')
    (hg : IsDPMorphism B'.dividedPowers B'.dividedPowers g.toRingHom) (hgid : ∀ b, g b = b)
    (κ : M' →ₛₗ[g.toRingHom] M') (hκ : ∀ m, κ m = m) (p : ℕ) (x) :
    termMap g hg κ p x = x := by
  obtain rfl : g = AlgHom.id A (B' : Type u) := AlgHom.ext hgid
  exact termMap_id hg κ hκ p x

/-- Applying a morphism of pairs and then one with inverse ring map and inverse module map on
the nose is the identity on degreewise maps. -/
private theorem termMap_termMap_eq_self (g : (B' : Type u) →ₐ[A] C')
    (hg : IsDPMorphism B'.dividedPowers C'.dividedPowers g.toRingHom)
    (g' : (C' : Type u) →ₐ[A] B')
    (hg' : IsDPMorphism C'.dividedPowers B'.dividedPowers g'.toRingHom)
    (hg'g : ∀ b, g' (g b) = b) (κ : M' →ₛₗ[g.toRingHom] N') (κ' : N' →ₛₗ[g'.toRingHom] M')
    (hκ'κ : ∀ m, κ' (κ m) = m) (p : ℕ) (x) :
    termMap g' hg' κ' p (termMap g hg κ p x) = x := by
  let ι : M' →ₛₗ[(g'.comp g).toRingHom] M' :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun b m => by
        change b • m = g' (g b) • m
        rw [hg'g] }
  rw [← termMap_comp g hg κ g' hg' (IsDPMorphism.comp _ hg' hg) κ' ι (fun m => (hκ'κ m).symm)]
  exact termMap_eq_self (g'.comp g) _ hg'g ι (fun _ => rfl) p x

/-- **The degreewise map of an isomorphism of pairs is bijective**: a divided power isomorphism
`g : B' ≅ C'` and an `g`-semilinear bijection `κ : M' ≅ N'`. -/
theorem bijective_termMap_of_inverse (g : (B' : Type u) →ₐ[A] C')
    (hg : IsDPMorphism B'.dividedPowers C'.dividedPowers g.toRingHom)
    (g' : (C' : Type u) →ₐ[A] B')
    (hg' : IsDPMorphism C'.dividedPowers B'.dividedPowers g'.toRingHom)
    (hgg' : ∀ c, g (g' c) = c) (hg'g : ∀ b, g' (g b) = b)
    (κ : M' →ₛₗ[g.toRingHom] N') (κ' : N' →ₛₗ[g'.toRingHom] M')
    (hκκ' : ∀ n, κ (κ' n) = n) (hκ'κ : ∀ m, κ' (κ m) = m) (p : ℕ) :
    Function.Bijective (termMap g hg κ p) :=
  ⟨Function.LeftInverse.injective (g := termMap g' hg' κ' p)
      (termMap_termMap_eq_self g hg g' hg' hg'g κ κ' hκ'κ p),
    Function.RightInverse.surjective (g := termMap g' hg' κ' p)
      (termMap_termMap_eq_self g' hg' g hg hgg' κ' κ hκκ' p)⟩

end Iso

variable (e' : (C : Type u) →ₐ[A] (polyRing B W : Type u))
  (he' : IsDPMorphism C.dividedPowers (polyRing B W).dividedPowers e'.toRingHom)
  (hee' : ∀ c, e (e' c) = c) (he'e : ∀ q, e' (e q) = q)
  (hbij : Function.Bijective (polyModuleMap W f μ e hfe))

include hee' hbij in
/-- The inverse of `polyModuleMap`, semilinear over the inverse of `e`. -/
theorem exists_polyModuleMap_inverse :
    ∃ ν' : N →ₛₗ[e'.toRingHom] (setIndexedDividedPowerPolynomialAlgebra B W ⊗[(B : Type u)] M),
      (∀ n, polyModuleMap W f μ e hfe (ν' n) = n) ∧
        (∀ z, ν' (polyModuleMap W f μ e hfe z) = z) := by
  let E := Equiv.ofBijective _ hbij
  have hE : ∀ n, polyModuleMap W f μ e hfe (E.symm n) = n := E.apply_symm_apply
  refine ⟨{ toFun := E.symm, map_add' := fun x y => ?_, map_smul' := fun c n => ?_ },
    hE, fun z => E.symm_apply_apply z⟩
  · apply hbij.1
    rw [map_add (polyModuleMap W f μ e hfe), hE, hE, hE]
  · apply hbij.1
    rw [map_smulₛₗ (polyModuleMap W f μ e hfe), hE, hE]
    change c • n = e (e' c) • n
    rw [hee']

include hf he he' hee' he'e hbij in
/-- **[Stacks, Lemma 60.19.2, Tag 07LD] for a morphism of pairs presenting a divided power
polynomial algebra.**  If `e : B⟨x_w⟩ ≅ C` is an isomorphism of divided power `A`-algebras with
`e ∘ (B → B⟨x_w⟩) = f`, and the linearisation `B⟨x_w⟩ ⊗_B M → N` of the horizontal map `μ` is
bijective, then the map of de Rham complexes `M ⊗_B Ω^*_{B/A,δ} ⟶ N ⊗_C Ω^*_{C/A,ε}` induced by
`(f, μ)` is a quasi-isomorphism. -/
theorem quasiIso_deRhamMap_of_dpPolynomial
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (hint' : Connection.IsIntegrable (oneVariableBaseSource A C) (oneVariableBaseProjection A C)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A C) nabla')
    (hμ : IsHorizontal f hf μ nabla nabla') :
    QuasiIso (deRhamMap f hf μ nabla hint nabla' hint' hμ) := by
  obtain ⟨ν', h1, h2⟩ := exists_polyModuleMap_inverse W f μ e hfe e' hee' hbij
  rw [deRhamMap_eq_comp W f hf μ e he hfe nabla nabla' hint hint' hμ]
  have : IsIso (deRhamMap (B := polyRing B W) e he (polyModuleMap W f μ e hfe)
      (polyBaseChangeConnection A B W nabla)
      (polyBaseChangeConnection_isIntegrable A B W nabla hint) nabla' hint'
      (isHorizontal_polyModuleMap W f hf μ e he hfe nabla nabla' hμ)) := by
    have hc : ∀ p, IsIso ((deRhamMap (B := polyRing B W) e he (polyModuleMap W f μ e hfe)
        (polyBaseChangeConnection A B W nabla)
        (polyBaseChangeConnection_isIntegrable A B W nabla hint) nabla' hint'
        (isHorizontal_polyModuleMap W f hf μ e he hfe nabla nabla' hμ)).f p) := fun p => by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact bijective_termMap_of_inverse e he e' he' hee' he'e _ ν' h1 h2 p
    exact HomologicalComplex.Hom.isIso_of_components _
  have := quasiIso_polyDeRhamComparison A B W nabla hint
  infer_instance

end Crystalline.DeRhamPair
