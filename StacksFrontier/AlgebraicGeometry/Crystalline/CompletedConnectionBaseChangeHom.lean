module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamDoubleComplex

/-!
# The base change of a horizontal map, and the functors `F` and `G` of [Stacks, Tag 07L5]

The base change of a `D`-linear map `f : M → N` along a map of rings `D → D'` is the completion
of `1 ⊗ f : D' ⊗_D M → D' ⊗_D N`, a `D'`-linear map `M ⊗̂_D D' → N ⊗̂_D D'`. If `f` is horizontal
for completed connections `∇_M` and `∇_N`, its base change is horizontal for the base-changed
connections. This gives the action on morphisms of the base change functors

`F : (M, ∇) ↦ (M ⊗^∧_{D, a} D', ∇')`   and   `G : (M', ∇') ↦ (M' ⊗^∧_{D', b} D, ∇)`

of [Stacks, Lemma 60.17.5, Tag 07L5].

## Main definitions

* `Crystalline.CompletedConnection.valuesMap` — the map `M ⊗̂_D Ω → N ⊗̂_D Ω` induced on the values
  of a completed connection by a `D`-linear map `f : M → N`.
* `Crystalline.CompletedConnection.baseChangeModuleMap` — **the base change of a `D`-linear map**,
  `M ⊗̂_D D' → N ⊗̂_D D'`.
* `Crystalline.Pair.baseChangeHom` — the base change of a morphism of pairs over `D` to a morphism
  of the base-changed pairs over `D'`.

## Main results

* `Crystalline.CompletedConnection.baseChangeModuleMap_inclusion` — the base change of `f`
  carries `1 ⊗ m` to `1 ⊗ f m`.
* `Crystalline.CompletedConnection.valuesMap_comp` — the map induced on the values of a
  connection by a composite is the composite of the induced maps.
* `Crystalline.CompletedConnection.baseChangeValues_valuesMap` — `ψ_*` commutes with the map
  induced on the values of a connection by `f`.
* `Crystalline.CompletedConnection.rawBaseChange_baseChangeModuleMap` — the horizontality square
  on the uncompleted tensor product `D' ⊗_D M`.
* `Crystalline.CompletedConnection.baseChange_baseChangeModuleMap` — **the base change of a
  horizontal map is horizontal**.
* `Crystalline.Pair.baseChangeHom_id` and `Crystalline.Pair.baseChangeHom_comp` — the base change
  of morphisms of pairs preserves identities and composites.

## References

* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07KJ](https://stacks.math.columbia.edu/tag/07KJ)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers
open scoped TensorProduct

universe u u' v v' w w₂ w₃ uI uI'

namespace Crystalline

namespace CompletedConnection

/-! ### The map induced on the values of a connection -/

section ValuesMap

variable (p : ℕ) (D : Type u) [CommRing D] (Omega : Type v) [AddCommGroup Omega]
  [Module D Omega] (M : Type w) [AddCommGroup M] [Module D M] (N : Type w₂) [AddCommGroup N]
  [Module D N]

/-- **The map `M ⊗̂_D Ω → N ⊗̂_D Ω` induced on the values of a completed connection** by a
`D`-linear map `f : M → N`: the completion of `f ⊗ 1`. -/
public def valuesMap (f : M →ₗ[D] N) :
    CompletedTensor p D Omega M →ₗ[D] CompletedTensor p D Omega N :=
  adicCompletionMapLinear (TensorProduct.map f (LinearMap.id (R := D) (M := Omega)))
    (pAdicIdeal (A := D) p)

/-- The induced map on the image of an uncompleted pure tensor: `m ⊗ ω ↦ f m ⊗ ω`. -/
@[simp] public theorem valuesMap_of_tmul (f : M →ₗ[D] N) (m : M) (omega : Omega) :
    valuesMap p D Omega M N f (toCompletedTensor p D Omega M (m ⊗ₜ[D] omega)) =
      toCompletedTensor p D Omega N (f m ⊗ₜ[D] omega) :=
  adicCompletionMapLinear_of _ _ _

/-- The induced map is Mathlib's `AdicCompletion.map` of the same uncompleted map. -/
public theorem valuesMap_eq (f : M →ₗ[D] N) (x : CompletedTensor p D Omega M) :
    valuesMap p D Omega M N f x =
      AdicCompletion.map (pAdicIdeal (A := D) p)
        (TensorProduct.map f (LinearMap.id (R := D) (M := Omega))) x :=
  (adicCompletionMap_eq_mapₛₗ _ _ x).symm

/-- The induced map is computed level by level. -/
public theorem valuesMap_val (f : M →ₗ[D] N) (x : CompletedTensor p D Omega M) (n : ℕ) :
    (valuesMap p D Omega M N f x).val n =
      adicQuotientMap (TensorProduct.map f (LinearMap.id (R := D) (M := Omega)))
        (le_of_eq (Ideal.map_id (pAdicIdeal (A := D) p))) n (x.val n) :=
  rfl

/-- **Functoriality of the induced map on the values of a connection**: the map induced by a
composite is the composite of the induced maps. -/
public theorem valuesMap_comp (R : Type w₃) [AddCommGroup R] [Module D R] (f : M →ₗ[D] N)
    (g : N →ₗ[D] R) (x : CompletedTensor p D Omega M) :
    valuesMap p D Omega M R (g ∘ₗ f) x =
      valuesMap p D Omega N R g (valuesMap p D Omega M N f x) := by
  refine adicCompletionMapₛₗ_comp_apply
    (TensorProduct.map f (LinearMap.id (R := D) (M := Omega)))
    (TensorProduct.map g (LinearMap.id (R := D) (M := Omega)))
    (TensorProduct.map (g ∘ₗ f) (LinearMap.id (R := D) (M := Omega))) _ _ _ (fun y ↦ ?_) x
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]

end ValuesMap

/-! ### The base change of a linear map -/

section BaseChangeMap

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u') [CommRing D'] [Algebra D D']
  (M : Type w) [AddCommGroup M] [Module D M] (N : Type w₂) [AddCommGroup N] [Module D N]

/-- **The base change of a `D`-linear map** `f : M → N` along `D → D'`: the `p`-adic completion
of `1 ⊗ f : D' ⊗_D M → D' ⊗_D N`, a `D'`-linear map `M ⊗̂_D D' → N ⊗̂_D D'`. -/
public def baseChangeModuleMap (f : M →ₗ[D] N) :
    baseChangeCarrier p D D' M →ₗ[D'] baseChangeCarrier p D D' N :=
  adicCompletionMapLinear (f.baseChange D') (pAdicIdeal (A := D') p)

/-- The base change of `f` on the image of an element of the uncompleted tensor product. -/
public theorem baseChangeModuleMap_of (f : M →ₗ[D] N) (y : D' ⊗[D] M) :
    baseChangeModuleMap p D D' M N f
        (AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] M) y) =
      AdicCompletion.of (pAdicIdeal (A := D') p) (D' ⊗[D] N) (f.baseChange D' y) :=
  adicCompletionMapLinear_of _ _ _

/-- The base change of `f` is computed level by level. -/
public theorem baseChangeModuleMap_val (f : M →ₗ[D] N) (x : baseChangeCarrier p D D' M)
    (n : ℕ) :
    (baseChangeModuleMap p D D' M N f x).val n =
      adicQuotientMap (f.baseChange D')
        (le_of_eq (Ideal.map_id (pAdicIdeal (A := D') p))) n (x.val n) :=
  rfl

/-- **The base change of `f` carries `1 ⊗ m` to `1 ⊗ f m`.** -/
@[simp] public theorem baseChangeModuleMap_inclusion (f : M →ₗ[D] N) (m : M) :
    baseChangeModuleMap p D D' M N f (baseChangeInclusion p D D' M m) =
      baseChangeInclusion p D D' N (f m) := by
  rw [baseChangeInclusion_apply, baseChangeModuleMap_of, baseChangeInclusion_apply]
  rfl

/-- The base change of the identity is the identity. -/
@[simp] public theorem baseChangeModuleMap_id :
    baseChangeModuleMap p D D' M M (LinearMap.id (R := D) (M := M)) = LinearMap.id := by
  rw [baseChangeModuleMap, LinearMap.baseChange_id]
  exact adicCompletionMapLinear_id _

/-- The base change of a composite is the composite of the base changes. -/
public theorem baseChangeModuleMap_comp (R : Type w₃) [AddCommGroup R] [Module D R]
    (f : M →ₗ[D] N) (g : N →ₗ[D] R) (x : baseChangeCarrier p D D' M) :
    baseChangeModuleMap p D D' M R (g ∘ₗ f) x =
      baseChangeModuleMap p D D' N R g (baseChangeModuleMap p D D' M N f x) := by
  refine adicCompletionMapₛₗ_comp_apply (f.baseChange D') (g.baseChange D')
    ((g ∘ₗ f).baseChange D') _ _ _ (fun y ↦ ?_) x
  rw [LinearMap.baseChange_comp]
  rfl

end BaseChangeMap

/-! ### The base change of a horizontal map -/

section Horizontal

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u') [CommRing D'] [Algebra D D']
  (M : Type w) [AddCommGroup M] [Module D M] (N : Type w₂) [AddCommGroup N] [Module D N]
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega]
  (Omega' : Type v') [AddCommGroup Omega'] [Module D' Omega']
  {d : D → Omega} (d' : D' → Omega') (psi : Omega →ₛₗ[algebraMap D D'] Omega')

/-- **The comparison of forms commutes with the map induced on the values of a connection**:
`ψ_* ∘ (f ⊗ 1) = (F f ⊗ 1) ∘ ψ_*`, where `F f` is the base change of `f`. -/
public theorem baseChangeValues_valuesMap (f : M →ₗ[D] N) (z : CompletedTensor p D Omega M) :
    baseChangeValues p D D' N Omega Omega' psi (valuesMap p D Omega M N f z) =
      valuesMap p D' Omega' (baseChangeCarrier p D D' M) (baseChangeCarrier p D D' N)
        (baseChangeModuleMap p D D' M N f)
        (baseChangeValues p D D' M Omega Omega' psi z) := by
  have hmid (w : M ⊗[D] Omega) :
      TensorProduct.map (baseChangeModuleMap p D D' M N f)
          (LinearMap.id (R := D') (M := Omega'))
          (baseChangeTensor p D D' M Omega Omega' psi w) =
        baseChangeTensor p D D' N Omega Omega' psi
          (TensorProduct.map f (LinearMap.id (R := D) (M := Omega)) w) := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m omega =>
      change TensorProduct.map (baseChangeModuleMap p D D' M N f) LinearMap.id
          (baseChangeInclusion p D D' M m ⊗ₜ[D'] psi omega) = _
      rw [TensorProduct.map_tmul, baseChangeModuleMap_inclusion]
      rfl
    | add x y hx hy => simp only [_root_.map_add, hx, hy]
  let L := TensorProduct.map (baseChangeModuleMap p D D' M N f)
      (LinearMap.id (R := D') (M := Omega')) ∘ₛₗ
    baseChangeTensor p D D' M Omega Omega' psi
  exact (adicCompletionMapₛₗ_comp_apply
    (TensorProduct.map f (LinearMap.id (R := D) (M := Omega)))
    (baseChangeTensor p D D' N Omega Omega' psi) L
    (le_of_eq (Ideal.map_id (pAdicIdeal (A := D) p))) (pAdicIdeal_map_le p D D')
    (pAdicIdeal_map_le p D D') hmid z).symm.trans
    (adicCompletionMapₛₗ_comp_apply (baseChangeTensor p D D' M Omega Omega' psi)
      (TensorProduct.map (baseChangeModuleMap p D D' M N f)
        (LinearMap.id (R := D') (M := Omega'))) L
      (pAdicIdeal_map_le p D D') (le_of_eq (Ideal.map_id (pAdicIdeal (A := D') p)))
      (pAdicIdeal_map_le p D D') (fun _ ↦ rfl) z)

variable (nablaM : CompletedConnection p D Omega d M) (nablaN : CompletedConnection p D Omega d N)
  (hadd' : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hleib' : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi : ∀ x : D, psi (d x) = d' (algebraMap D D' x))

/-- **The horizontality square on the uncompleted tensor product.** For a horizontal `f` the
base change of `f` carries the defining formula of the base-changed connection on `D' ⊗_D M` to
the one on `D' ⊗_D N`. -/
public theorem rawBaseChange_baseChangeModuleMap (f : M →ₗ[D] N)
    (hf : ∀ m : M, nablaN (f m) = valuesMap p D Omega M N f (nablaM m)) (y : D' ⊗[D] M) :
    rawBaseChange p D D' N Omega Omega' d' psi nablaN hadd' hleib' hpsi (f.baseChange D' y) =
      valuesMap p D' Omega' (baseChangeCarrier p D D' M) (baseChangeCarrier p D D' N)
        (baseChangeModuleMap p D D' M N f)
        (rawBaseChange p D D' M Omega Omega' d' psi nablaM hadd' hleib' hpsi y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b' m =>
    rw [LinearMap.baseChange_tmul, rawBaseChange_tmul, rawBaseChange_tmul, _root_.map_add,
      _root_.map_smul, hf m, ← baseChangeValues_valuesMap, correction_apply, correction_apply,
      valuesMap_of_tmul, baseChangeModuleMap_inclusion]
  | add x y hx hy => simp only [_root_.map_add, hx, hy]

/-- **The base change of a horizontal map is horizontal**: if `f : M → N` is horizontal for `∇_M`
and `∇_N`, its base change is horizontal for the base-changed connections. -/
public theorem baseChange_baseChangeModuleMap (f : M →ₗ[D] N)
    (hf : ∀ m : M, nablaN (f m) = valuesMap p D Omega M N f (nablaM m))
    (x : baseChangeCarrier p D D' M) :
    baseChange p D D' N Omega Omega' d' psi nablaN hadd' hleib' hpsi
        (baseChangeModuleMap p D D' M N f x) =
      valuesMap p D' Omega' (baseChangeCarrier p D D' M) (baseChangeCarrier p D D' N)
        (baseChangeModuleMap p D D' M N f)
        (baseChange p D D' M Omega Omega' d' psi nablaM hadd' hleib' hpsi x) := by
  refine AdicCompletion.ext fun n ↦ ?_
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective
    ((pAdicIdeal (A := D') p) ^ n • ⊤ : Submodule D' (D' ⊗[D] M)) (x.val n)
  have hbm : (baseChangeModuleMap p D D' M N f x).val n =
      Submodule.Quotient.mk (f.baseChange D' y) := by
    rw [baseChangeModuleMap_val, ← hy]
    rfl
  rw [baseChange_val, hbm, levelBaseChange_mk, valuesMap_val, baseChange_val, ← hy,
    levelBaseChange_mk,
    rawBaseChange_baseChangeModuleMap p D D' M N Omega Omega' d' psi nablaM nablaN hadd'
      hleib' hpsi f hf y]
  rfl

end Horizontal

end CompletedConnection

/-! ### The base change of a morphism of pairs -/

namespace Pair

variable (p : ℕ) (D : Type u) [CommRing D] (D' : Type u') [CommRing D'] [Algebra D D']
  (Omega : Type v) [AddCommGroup Omega] [Module D Omega]
  (Omega' : Type v') [AddCommGroup Omega'] [Module D' Omega']
  {ι : Type uI} (dx : ι → Omega) {ι' : Type uI'} (dx' : ι' → Omega')
  {d : D → Omega} (d' : D' → Omega') (psi : Omega →ₛₗ[algebraMap D D'] Omega')
  (hadd' : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hleib' : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi : ∀ x : D, psi (d x) = d' (algebraMap D D' x))

/-- **The base change of a morphism of pairs** over `D` to a morphism of the base-changed pairs
over `D'`, with underlying map `Crystalline.CompletedConnection.baseChangeModuleMap`. -/
public def baseChangeHom {P Q : Pair.{u, v, uI, w} p D Omega dx d} (f : P ⟶ Q)
    (hcoordP) (hintP) (hqnP) (hcoordQ) (hintQ) (hqnQ) :
    baseChange p D D' Omega Omega' dx dx' d' psi P hadd' hleib' hpsi hcoordP hintP hqnP ⟶
      baseChange p D D' Omega Omega' dx dx' d' psi Q hadd' hleib' hpsi hcoordQ hintQ hqnQ where
  toLinearMap := CompletedConnection.baseChangeModuleMap p D D' P.carrier Q.carrier f.toLinearMap
  horizontal x := by
    have h := CompletedConnection.baseChange_baseChangeModuleMap p D D' P.carrier Q.carrier Omega
      Omega' d' psi P.nabla Q.nabla hadd' hleib' hpsi f.toLinearMap
      (fun m ↦ by rw [f.horizontal m, CompletedConnection.valuesMap_eq]) x
    rwa [CompletedConnection.valuesMap_eq] at h

/-- The underlying map of the base change of a morphism of pairs. -/
@[simp] public theorem baseChangeHom_toLinearMap {P Q : Pair.{u, v, uI, w} p D Omega dx d}
    (f : P ⟶ Q) (hcoordP) (hintP) (hqnP) (hcoordQ) (hintQ) (hqnQ) :
    (baseChangeHom p D D' Omega Omega' dx dx' d' psi hadd' hleib' hpsi f hcoordP hintP hqnP
        hcoordQ hintQ hqnQ).toLinearMap =
      CompletedConnection.baseChangeModuleMap p D D' P.carrier Q.carrier f.toLinearMap :=
  rfl

/-- **The base change of the identity morphism of a pair is the identity.** -/
public theorem baseChangeHom_id (P : Pair.{u, v, uI, w} p D Omega dx d)
    (hcoordP) (hintP) (hqnP) :
    baseChangeHom p D D' Omega Omega' dx dx' d' psi hadd' hleib' hpsi (𝟙 P) hcoordP hintP hqnP
        hcoordP hintP hqnP =
      𝟙 (baseChange p D D' Omega Omega' dx dx' d' psi P hadd' hleib' hpsi hcoordP hintP hqnP) :=
  PairHom.ext (CompletedConnection.baseChangeModuleMap_id p D D' P.carrier)

/-- **The base change of a composite of morphisms of pairs is the composite of the base
changes.** -/
public theorem baseChangeHom_comp {P Q R : Pair.{u, v, uI, w} p D Omega dx d} (f : P ⟶ Q)
    (g : Q ⟶ R) (hcoordP) (hintP) (hqnP) (hcoordQ) (hintQ) (hqnQ) (hcoordR) (hintR) (hqnR) :
    baseChangeHom p D D' Omega Omega' dx dx' d' psi hadd' hleib' hpsi (f ≫ g) hcoordP hintP hqnP
        hcoordR hintR hqnR =
      baseChangeHom p D D' Omega Omega' dx dx' d' psi hadd' hleib' hpsi f hcoordP hintP hqnP
          hcoordQ hintQ hqnQ ≫
        baseChangeHom p D D' Omega Omega' dx dx' d' psi hadd' hleib' hpsi g hcoordQ hintQ hqnQ
          hcoordR hintR hqnR :=
  PairHom.ext (LinearMap.ext fun x ↦ CompletedConnection.baseChangeModuleMap_comp p D D'
    P.carrier Q.carrier R.carrier f.toLinearMap g.toLinearMap x)

end Pair

end Crystalline

end
