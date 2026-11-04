module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceSectionsLevelQuotient
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionFormsBijective
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceCosimplicialBaseChange

/-!
# The crystal base change on the limit modules of the cosimplicial system

Let `ℱ` be a crystal in quasi-coherent `𝒪_{X/S}`-modules, let `D(b)` be the completed cosimplicial
divided power envelope of the situation's own presentation and let

`M(b) = lim_e Γ((X, T(b)_e, δ(b)), ℱ)`

be the cosimplicial module of [Stacks, Proposition 60.20.1, Tag 07JN]
(`...SmallSite.wholeSpaceCosimplicialModule`).  **This module proves that for every
`φ : m ⟶ n` of the simplex category the transition `φ_* : M(m) → M(n)` induces an isomorphism**

`D(n) ⊗̂_{D(m)} M(m) ≅ M(n)`,  `x ⊗ y ↦ x • φ_* y`,

the completed tensor product being the `p`-adic completion
`Crystalline.CompletedConnection.baseChangeCarrier` of the algebraic one.

## The argument

* At a single level `e` the base change
  `Γ(T(n)_e, 𝒪) ⊗_{Γ(T(m)_e, 𝒪)} Γ(T(m)_e, ℱ) → Γ(T(n)_e, ℱ)` is bijective: this is the crystal
  property, `...SmallSite.bijective_wholeSpaceCosimplicialBaseChange`.
* The reductions `D(b) → Γ(T(b)_e, 𝒪)` and `M(b) → Γ(T(b)_e, ℱ)` are surjective with kernels
  `(p)^{N+e}` and `(p)^{N+e} M(b)`, for the uniform shift `N = Crystalline.uniformLevel`
  (`...SmallSite.levelSectionsScalars_eq_zero_iff` and
  `...SmallSite.mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero`).
* By right exactness of the tensor product, `(D(n) ⊗_{D(m)} M(m)) / (p)^{N+e}` is the tensor
  product of the reductions, so the uncompleted base change is bijective modulo `(p)^{N+e}`.  This
  is stated abstractly as `Crystalline.bijective_adicQuotientMap_tensorLiftₛₗ`, whose inverse is
  `Crystalline.levelTensorLift`.
* Bijectivity at every level from `N` on passes to the completions
  (`Crystalline.adicCompletionMapₛₗ_bijective_of_le`), and `M(n)` is its own completion, being
  `p`-adically complete (`...SmallSite.wholeSpaceCosimplicialModuleIsAdicComplete`).

## Main definitions and results

* `Crystalline.tensorLiftₛₗ` and `Crystalline.completedTensorLiftₛₗ` — the base change
  `B ⊗_A M → M'` of a semilinear map and its completion into a complete module.
* `Crystalline.bijective_adicQuotientMap_tensorLiftₛₗ` and
  `Crystalline.bijective_completedTensorLiftₛₗ` — the abstract level and completion statements.
* `...SmallSite.wholeSpaceBaseChangeEquiv` — **the base-change isomorphism
  `D(n) ⊗̂_{D(m)} M(m) ≅ M(n)`**, with `...SmallSite.wholeSpaceBaseChangeEquiv_of_tmul` and
  `...SmallSite.wholeSpaceBaseChangeEquiv_baseChangeInclusion` pinning it down.

## References

* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Simplicial DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline

/-! ### The base change map of a semilinear map -/

section TensorLift

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M] {M' : Type*} [AddCommGroup M'] [Module B M']
  (f : M →ₛₗ[algebraMap A B] M')

/-- The biadditive map `(b, m) ↦ b • f m` underlying `Crystalline.tensorLiftₛₗ`. -/
def tensorLiftAux : B →+ M →+ M' where
  toFun b := AddMonoidHom.mk' (fun m ↦ b • f m) fun x y ↦ by rw [map_add, smul_add]
  map_zero' := AddMonoidHom.ext fun m ↦ zero_smul B (f m)
  map_add' b b' := AddMonoidHom.ext fun m ↦ add_smul b b' (f m)

/-- The biadditive map of `Crystalline.tensorLiftₛₗ`, as a formula. -/
@[simp] theorem tensorLiftAux_apply (b : B) (m : M) : tensorLiftAux f b m = b • f m := rfl

/-- **The `B`-linear map `B ⊗_A M → M'`, `b ⊗ m ↦ b • f m`, induced by a semilinear map
`f : M → M'` over `A → B`.** -/
def tensorLiftₛₗ : B ⊗[A] M →ₗ[B] M' where
  toFun := TensorProduct.liftAddHom (tensorLiftAux f) fun a b m ↦ by
    rw [tensorLiftAux_apply, tensorLiftAux_apply, f.map_smulₛₗ, Algebra.smul_def, mul_smul]
    exact smul_comm _ _ _
  map_add' := map_add _
  map_smul' c t := by
    induction t using TensorProduct.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | tmul b m =>
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul,
        TensorProduct.liftAddHom_tmul, tensorLiftAux_apply, tensorLiftAux_apply, smul_eq_mul,
        mul_smul, RingHom.id_apply]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- `Crystalline.tensorLiftₛₗ` on a pure tensor. -/
@[simp] theorem tensorLiftₛₗ_tmul (b : B) (m : M) : tensorLiftₛₗ f (b ⊗ₜ m) = b • f m := rfl

end TensorLift

/-! ### Bijectivity at one level of the `p`-adic filtration -/

section LevelBijective

variable (p k : ℕ) {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M] {M' : Type*} [AddCommGroup M'] [Module B M']
  (f : M →ₛₗ[algebraMap A B] M')

/-- A pure tensor `b ⊗ (a • m)` with `a ∈ (p)^k` lies in `(p)^k (B ⊗_A M)`. -/
theorem tmul_mem_pow_smul_top_of_mem (b : B) {m : M}
    (hm : m ∈ (pAdicIdeal (A := A) p) ^ k • (⊤ : Submodule A M)) :
    b ⊗ₜ[A] m ∈ (pAdicIdeal (A := B) p) ^ k • (⊤ : Submodule B (B ⊗[A] M)) := by
  refine Submodule.smul_induction_on hm (fun a ha x _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · have hb : b ⊗ₜ[A] (a • x) = algebraMap A B a • (b ⊗ₜ[A] x) := by
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', algebraMap_smul]
    rw [hb]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [← CompletedConnection.pAdicIdeal_map_eq p A B, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  · rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ hx hy

/-- A pure tensor `c ⊗ m` with `c ∈ (p)^k` lies in `(p)^k (B ⊗_A M)`. -/
theorem tmul_mem_pow_smul_top_of_mem_left {c : B} (hc : c ∈ (pAdicIdeal (A := B) p) ^ k)
    (m : M) :
    c ⊗ₜ[A] m ∈ (pAdicIdeal (A := B) p) ^ k • (⊤ : Submodule B (B ⊗[A] M)) := by
  have h : c ⊗ₜ[A] m = c • ((1 : B) ⊗ₜ[A] m) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact Submodule.smul_mem_smul hc Submodule.mem_top

variable {R₀ : Type*} [CommRing R₀] {P : Type*} [AddCommGroup P] [Module R₀ P]
  {L : Type*} [AddCommGroup L] [Module R₀ L] {L' : Type*} [AddCommGroup L']
  (πA : A →+* R₀) (πB : B →+ P) (ρ : M →+ L) (ρ' : M' →+ L')
  (hπB : ∀ (a : A) (b : B), πA a • πB b = πB (algebraMap A B a * b))
  (hρ : ∀ (a : A) (m : M), ρ (a • m) = πA a • ρ m)

/-- The biadditive map `(πB b, ρ m) ↦ b ⊗ ρ m` underlying `Crystalline.levelTensorReduce`. -/
def levelTensorReduceAux : B →+ M →+ P ⊗[R₀] L where
  toFun b := AddMonoidHom.mk' (fun m ↦ πB b ⊗ₜ[R₀] ρ m) fun x y ↦ by
    rw [map_add, TensorProduct.tmul_add]
  map_zero' := AddMonoidHom.ext fun m ↦ by
    simp only [map_zero, TensorProduct.zero_tmul, AddMonoidHom.mk'_apply,
      AddMonoidHom.zero_apply]
  map_add' b b' := AddMonoidHom.ext fun m ↦ by
    simp only [map_add, TensorProduct.add_tmul, AddMonoidHom.mk'_apply,
      AddMonoidHom.add_apply]

include hπB hρ in
/-- **The reduction `B ⊗_A M → P ⊗_{R₀} L`, `b ⊗ m ↦ πB b ⊗ ρ m`.** -/
def levelTensorReduce : B ⊗[A] M →+ P ⊗[R₀] L :=
  TensorProduct.liftAddHom (levelTensorReduceAux πB ρ) fun a b m ↦ by
    change πB (a • b) ⊗ₜ[R₀] ρ m = πB b ⊗ₜ[R₀] ρ (a • m)
    rw [Algebra.smul_def, ← hπB, hρ, TensorProduct.smul_tmul]

/-- `Crystalline.levelTensorReduce` on a pure tensor. -/
@[simp] theorem levelTensorReduce_tmul (b : B) (m : M) :
    levelTensorReduce πA πB ρ hπB hρ (b ⊗ₜ[A] m) = πB b ⊗ₜ[R₀] ρ m := rfl

variable {πA πB ρ}

include hπB hρ in
/-- The reduction `B ⊗_A M → P ⊗_{R₀} L` is surjective when `πB` and `ρ` are. -/
theorem surjective_levelTensorReduce (hπBs : Function.Surjective πB)
    (hρs : Function.Surjective ρ) :
    Function.Surjective (levelTensorReduce πA πB ρ hπB hρ) := by
  intro w
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x y =>
    obtain ⟨b, rfl⟩ := hπBs x
    obtain ⟨m, rfl⟩ := hρs y
    exact ⟨b ⊗ₜ[A] m, rfl⟩
  | add x y hx hy =>
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨t', rfl⟩ := hy
    exact ⟨t + t', map_add _ t t'⟩

variable (hπAs : Function.Surjective πA) (hπBs : Function.Surjective πB)
  (hρs : Function.Surjective ρ)
  (hπBk : ∀ b, πB b = 0 → b ∈ (pAdicIdeal (A := B) p) ^ k)
  (hρk : ∀ m, ρ m = 0 → m ∈ (pAdicIdeal (A := A) p) ^ k • (⊤ : Submodule A M))

include hπBk hρk in
/-- The class of `b ⊗ m` modulo `(p)^k` depends only on `πB b` and `ρ m`. -/
theorem mk_tmul_eq_of_eq {b b' : B} {m m' : M} (hb : πB b = πB b') (hm : ρ m = ρ m') :
    (Submodule.Quotient.mk (b ⊗ₜ[A] m) :
        (B ⊗[A] M) ⧸ (pAdicIdeal (A := B) p) ^ k • (⊤ : Submodule B (B ⊗[A] M))) =
      Submodule.Quotient.mk (b' ⊗ₜ[A] m') := by
  rw [Submodule.Quotient.eq]
  have h : b ⊗ₜ[A] m - b' ⊗ₜ[A] m' = (b - b') ⊗ₜ[A] m + b' ⊗ₜ[A] (m - m') := by
    rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  rw [h]
  refine Submodule.add_mem _ (tmul_mem_pow_smul_top_of_mem_left p k (hπBk _ ?_) m)
    (tmul_mem_pow_smul_top_of_mem p k b' (hρk _ ?_))
  · rw [map_sub, hb, sub_self]
  · rw [map_sub, hm, sub_self]

/-- The function `(πB b, ρ m) ↦ [b ⊗ m]` underlying `Crystalline.levelTensorLift`, through
chosen preimages. -/
def levelTensorLiftFun (x : P) (y : L) :
    (B ⊗[A] M) ⧸ (pAdicIdeal (A := B) p) ^ k • (⊤ : Submodule B (B ⊗[A] M)) :=
  Submodule.Quotient.mk (Function.surjInv hπBs x ⊗ₜ[A] Function.surjInv hρs y)

include hπBk hρk in
/-- `Crystalline.levelTensorLiftFun` on reductions: `(πB b, ρ m) ↦ [b ⊗ m]`. -/
theorem levelTensorLiftFun_apply (b : B) (m : M) :
    levelTensorLiftFun p k hπBs hρs (πB b) (ρ m) = Submodule.Quotient.mk (b ⊗ₜ[A] m) :=
  mk_tmul_eq_of_eq p k hπBk hρk (Function.surjInv_eq hπBs _) (Function.surjInv_eq hρs _)

include hπBk hρk in
/-- The biadditive map `(πB b, ρ m) ↦ [b ⊗ m]` underlying `Crystalline.levelTensorLift`. -/
def levelTensorLiftAux : P →+ L →+
    (B ⊗[A] M) ⧸ (pAdicIdeal (A := B) p) ^ k • (⊤ : Submodule B (B ⊗[A] M)) where
  toFun x := AddMonoidHom.mk' (levelTensorLiftFun p k hπBs hρs x) fun y y' ↦ by
    obtain ⟨b, rfl⟩ := hπBs x
    obtain ⟨m, rfl⟩ := hρs y
    obtain ⟨m', rfl⟩ := hρs y'
    rw [← map_add, levelTensorLiftFun_apply p k hπBs hρs hπBk hρk,
      levelTensorLiftFun_apply p k hπBs hρs hπBk hρk,
      levelTensorLiftFun_apply p k hπBs hρs hπBk hρk, TensorProduct.tmul_add,
      Submodule.Quotient.mk_add]
  map_zero' := AddMonoidHom.ext fun y ↦ by
    obtain ⟨m, rfl⟩ := hρs y
    rw [AddMonoidHom.mk'_apply, ← map_zero πB, levelTensorLiftFun_apply p k hπBs hρs hπBk hρk,
      TensorProduct.zero_tmul, Submodule.Quotient.mk_zero, AddMonoidHom.zero_apply]
  map_add' x x' := AddMonoidHom.ext fun y ↦ by
    obtain ⟨b, rfl⟩ := hπBs x
    obtain ⟨b', rfl⟩ := hπBs x'
    obtain ⟨m, rfl⟩ := hρs y
    rw [AddMonoidHom.add_apply, AddMonoidHom.mk'_apply, AddMonoidHom.mk'_apply,
      AddMonoidHom.mk'_apply, ← map_add, levelTensorLiftFun_apply p k hπBs hρs hπBk hρk,
      levelTensorLiftFun_apply p k hπBs hρs hπBk hρk,
      levelTensorLiftFun_apply p k hπBs hρs hπBk hρk, TensorProduct.add_tmul,
      Submodule.Quotient.mk_add]

include hπB hρ hπAs in
/-- **The inverse of the reduction modulo `(p)^k`: `P ⊗_{R₀} L → (B ⊗_A M)/(p)^k`,
`πB b ⊗ ρ m ↦ [b ⊗ m]`.** -/
def levelTensorLift : P ⊗[R₀] L →+
    (B ⊗[A] M) ⧸ (pAdicIdeal (A := B) p) ^ k • (⊤ : Submodule B (B ⊗[A] M)) :=
  TensorProduct.liftAddHom (levelTensorLiftAux p k hπBs hρs hπBk hρk) fun r x y ↦ by
    obtain ⟨a, rfl⟩ := hπAs r
    obtain ⟨b, rfl⟩ := hπBs x
    obtain ⟨m, rfl⟩ := hρs y
    change levelTensorLiftFun p k hπBs hρs (πA a • πB b) (ρ m) =
      levelTensorLiftFun p k hπBs hρs (πB b) (πA a • ρ m)
    rw [hπB, ← hρ, levelTensorLiftFun_apply p k hπBs hρs hπBk hρk,
      levelTensorLiftFun_apply p k hπBs hρs hπBk hρk, ← Algebra.smul_def,
      TensorProduct.smul_tmul]

/-- **`Crystalline.levelTensorLift` inverts the reduction modulo `(p)^k`**: composed with
`Crystalline.levelTensorReduce` it is the quotient map. -/
theorem levelTensorLift_levelTensorReduce (t : B ⊗[A] M) :
    levelTensorLift p k hπB hρ hπAs hπBs hρs hπBk hρk (levelTensorReduce πA πB ρ hπB hρ t) =
      Submodule.Quotient.mk t := by
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, Submodule.Quotient.mk_zero]
  | tmul b m => exact levelTensorLiftFun_apply p k hπBs hρs hπBk hρk b m
  | add x y hx hy => rw [map_add, map_add, hx, hy, Submodule.Quotient.mk_add]

/-- The ideal `(p)` of `B` maps into itself under the identity, the hypothesis of
`Crystalline.adicCompletionMapₛₗ` for a linear map. -/
theorem pAdicIdeal_map_id_le :
    (pAdicIdeal (A := B) p).map (RingHom.id B) ≤ pAdicIdeal (A := B) p := by
  rw [Ideal.map_id]

include hπB hρ hπAs hπBs hρs hπBk hρk in
/-- **The base change `B ⊗_A M → M'` is bijective modulo `(p)^k`** as soon as, after the
reductions `πB`, `ρ`, `ρ'`, it becomes a bijective base change `β : P ⊗_{R₀} L → L'`: that is,
`πA : A → R₀` is surjective, `πB : B → P` and `ρ : M → L` are surjective semilinear reductions
killing exactly `(p)^k`, `ρ'` has kernel exactly `(p)^k M'`, and `β (πB b ⊗ ρ m) = ρ' (b • f m)`.

The reduction `B ⊗_A M → P ⊗_{R₀} L` is right exact: `Crystalline.levelTensorLift` inverts it
modulo `(p)^k`. -/
theorem bijective_adicQuotientMap_tensorLiftₛₗ (β : P ⊗[R₀] L →+ L')
    (hβ : Function.Bijective β)
    (hβt : ∀ (b : B) (m : M), β (πB b ⊗ₜ[R₀] ρ m) = ρ' (b • f m))
    (hρ' : ∀ y, ρ' y = 0 ↔ y ∈ (pAdicIdeal (A := B) p) ^ k • (⊤ : Submodule B M')) :
    Function.Bijective (adicQuotientMap (tensorLiftₛₗ f) (pAdicIdeal_map_id_le p) k) := by
  have hFχ : ∀ t, ρ' (tensorLiftₛₗ f t) = β (levelTensorReduce πA πB ρ hπB hρ t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero]
    | tmul b m => exact (hβt b m).symm
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨t, rfl⟩ := Submodule.mkQ_surjective _ x
    have hmem : tensorLiftₛₗ f t ∈ (pAdicIdeal (A := B) p) ^ k • (⊤ : Submodule B M') :=
      (Submodule.Quotient.mk_eq_zero _).1 hx
    have h1 : β (levelTensorReduce πA πB ρ hπB hρ t) = 0 := (hFχ t).symm.trans ((hρ' _).2 hmem)
    have h2 : levelTensorReduce πA πB ρ hπB hρ t = 0 := hβ.1 (h1.trans (map_zero β).symm)
    show Submodule.Quotient.mk t = 0
    rw [← levelTensorLift_levelTensorReduce p k hπB hρ hπAs hπBs hρs hπBk hρk t, h2, map_zero]
  · intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨w, hw⟩ := hβ.2 (ρ' y)
    obtain ⟨t, rfl⟩ := surjective_levelTensorReduce hπB hρ hπBs hρs w
    refine ⟨Submodule.Quotient.mk t, ?_⟩
    show Submodule.Quotient.mk (tensorLiftₛₗ f t) = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq, ← hρ', map_sub, hFχ, hw, sub_self]

end LevelBijective

/-! ### Passing to the completion -/

section Completion

variable (p : ℕ) {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M] {M' : Type*} [AddCommGroup M'] [Module B M']
  (f : M →ₛₗ[algebraMap A B] M') [IsAdicComplete (pAdicIdeal (A := B) p) M']

/-- **The completed base change `(B ⊗_A M)^∧ → M'`** of a semilinear map into a `p`-adically
complete module: the completion of `Crystalline.tensorLiftₛₗ` followed by the inverse of the
structure map `M' → M'^∧`, which is bijective because `M'` is complete. -/
def completedTensorLiftₛₗ :
    AdicCompletion (pAdicIdeal (A := B) p) (B ⊗[A] M) →ₗ[B] M' :=
  (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := B) p) M').symm.toLinearMap ∘ₗ
    adicCompletionMapₛₗ (tensorLiftₛₗ f) (pAdicIdeal_map_id_le p)

/-- The completed base change on the image of an uncompleted tensor. -/
theorem completedTensorLiftₛₗ_of (t : B ⊗[A] M) :
    completedTensorLiftₛₗ p f (AdicCompletion.of _ _ t) = tensorLiftₛₗ f t := by
  rw [completedTensorLiftₛₗ, LinearMap.comp_apply, adicCompletionMapₛₗ_of]
  exact AdicCompletion.ofLinearEquiv_symm_of _ _

/-- **The completed base change is bijective as soon as the uncompleted one is bijective modulo
`(p)^{N+e}` for every `e`.** -/
theorem bijective_completedTensorLiftₛₗ (N : ℕ)
    (hlev : ∀ e : ℕ,
      Function.Bijective (adicQuotientMap (tensorLiftₛₗ f) (pAdicIdeal_map_id_le p) (N + e))) :
    Function.Bijective (completedTensorLiftₛₗ p f) :=
  (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := B) p) M').symm.bijective.comp
    (adicCompletionMapₛₗ_bijective_of_le _ _ N fun n hn ↦ by
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hn
      exact hlev e)

end Completion

/-! ### Additivity of the base change of ambient sections -/

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} {A A' : Thickening S} (g : A' ⟶ A)
  (NA : SheafOfModules.{u} A.ringRestrictionSheaf)
  (NA' : SheafOfModules.{u} A'.ringRestrictionSheaf)
  (fmap : NA ⟶ (SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g)).obj NA')
  [IsAffine A.thickening.target.scheme] [IsAffine A'.thickening.target.scheme]
  [(ambientSchemeOf A NA).IsQuasicoherent]

/-- The base change of ambient sections is additive. -/
theorem ambientBaseChangeTensorFun_add
    (x y : ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeOf A NA, ⊤)) :
    ambientBaseChangeTensorFun g NA NA' fmap (x + y) =
      ambientBaseChangeTensorFun g NA NA' fmap x + ambientBaseChangeTensorFun g NA NA' fmap y := by
  show ambientComparisonAbstractTop g NA NA' fmap
      ((affineBaseChangeTopIsoAbstract g NA).hom (ambientCrossAbstract g NA (x + y))) = _
  rw [show ambientCrossAbstract g NA (x + y) =
    ambientCrossAbstract g NA x + ambientCrossAbstract g NA y from rfl, map_add, map_add]
  rfl

/-- The base change of ambient sections, as an additive map. -/
def ambientBaseChangeTensorHom :
    ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeOf A NA, ⊤) →+
      Γ(ambientSchemeOf A' NA', ⊤) :=
  AddMonoidHom.mk' (ambientBaseChangeTensorFun g NA NA' fmap)
    (ambientBaseChangeTensorFun_add g NA NA' fmap)

/-- `...GlobalCrystallineSituation.ambientBaseChangeTensorHom` is
`...GlobalCrystallineSituation.ambientBaseChangeTensorFun`. -/
@[simp] theorem ambientBaseChangeTensorHom_apply
    (x : ringAlong g ⊗[Γ(A.thickening.target.scheme, ⊤)] Γ(ambientSchemeOf A NA, ⊤)) :
    ambientBaseChangeTensorHom g NA NA' fmap x = ambientBaseChangeTensorFun g NA NA' fmap x :=
  rfl

end GlobalCrystallineSituation

/-! ### The concrete reductions -/

namespace GlobalCrystallineSituation.SmallSite

open CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- A section of the structure sheaf of `Cris(X/S)` over an object, read as a section of the
structure sheaf of `CRIS(X/S)` over the underlying object.  The identity. -/
def bigRingSection (B : CrystallineThickening S) (r : (structureSheaf S).obj.obj (op B)) :
    crysSheafRing S B.obj := r

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- Reading a section on the big site commutes with restriction along a morphism. -/
theorem crysSheafRingMap_bigRingSection {B B' : CrystallineThickening S} (g : B' ⟶ B)
    (r : (structureSheaf S).obj.obj (op B)) :
    crysSheafRingMap g.hom (bigRingSection B r) =
      bigRingSection B' (((structureSheaf S).obj.map g.op).hom r) := rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- Reading a section on the big site is multiplicative. -/
theorem bigRingSection_mul (B : CrystallineThickening S)
    (r r' : (structureSheaf S).obj.obj (op B)) :
    bigRingSection B (r * r') = bigRingSection B r * bigRingSection B r' := rfl

omit [IsAffine S.X] [IsAffine S.S.scheme] in
/-- **The restriction of a section to the whole of the ambient scheme is semilinear** over the
identification of the sections of `𝒪_{X/S}` over an object with the sections of the structure
sheaf of its ambient scheme. -/
theorem crysSectionTop_smul (F : SheafOfModules.{u} (structureSheaf S))
    (B : CrystallineThickening S) (r : (structureSheaf S).obj.obj (op B))
    (x : F.val.obj (op B)) :
    crysSectionTop F B (r • x) =
      ambientRingSection B.obj (bigRingSection B r) • crysSectionTop F B x := by
  unfold crysSectionTop
  rw [map_smulₛₗ]
  rfl

/-- The reduction `D(n) → Γ(T(n)_e, 𝒪)` is surjective. -/
theorem surjective_levelSectionsScalars (n : SimplexCategory) (e : ℕ) :
    Function.Surjective (levelSectionsScalars hp n e) :=
  (wholeSpaceEnvelopeRingLevelEquiv hp n.len e).symm.surjective.comp
    Ideal.Quotient.mk_surjective

/-- **The kernel of the reduction `D(n) → Γ(T(n)_e, 𝒪)` is `(p)^{N+e}`.** -/
theorem levelSectionsScalars_eq_zero_iff (n : SimplexCategory) (e : ℕ)
    (b : ((wholeSpaceEnvelopeRing hp).obj n : Type u)) :
    levelSectionsScalars hp n e b = 0 ↔
      b ∈ pAdicIdeal (A := ((wholeSpaceEnvelopeRing hp).obj n : Type u)) S.p ^
        (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) := by
  rw [levelSectionsScalars_apply, RingEquiv.map_eq_zero_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

section Levels

variable (Fc : QuasiCoherentCrystal S)

/-- **The reduction `D(n) → Γ(T(n)_e, 𝒪_{T(n)_e})`**, `...SmallSite.levelSectionsScalars` with
its target read as the sections of the structure sheaf of the ambient scheme. -/
def levelAmbientScalars (n e : ℕ) :
    ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u) →+*
      Γ((levelObj hp n e).obj.thickening.target.scheme, ⊤) :=
  levelSectionsScalars hp ⦋n⦌ e

/-- **The reduction `M(n) → Γ(T(n)_e, ℱ_{T(n)_e})`** of the limit to the sections of the
restriction of `ℱ` to the ambient scheme of a level. -/
def levelSectionsTopReduce (n e : ℕ) :
    wholeSpaceSections hp Fc ⦋n⦌ →+
      Γ(ambientSchemeOf (levelObj hp n e).obj
        (moduleRestrictionSheaf Fc.obj (levelObj hp n e)), ⊤) :=
  (crysSectionTopHom Fc.obj (levelObj hp n e)).comp
    (AddMonoidHom.mk' (fun x ↦ wholeSpaceSectionsVal hp Fc x e) fun x y ↦
      wholeSpaceSectionsVal_add hp Fc x y e)

/-- `...SmallSite.levelSectionsTopReduce` is the restriction to the whole of the ambient scheme
of the component at the level. -/
@[simp] theorem levelSectionsTopReduce_apply (n e : ℕ) (x : wholeSpaceSections hp Fc ⦋n⦌) :
    levelSectionsTopReduce hp Fc n e x =
      crysSectionTop Fc.obj (levelObj hp n e) (wholeSpaceSectionsVal hp Fc x e) := rfl

variable {m n : ℕ} (φ : (⦋m⦌ : SimplexCategory) ⟶ ⦋n⦌) (e : ℕ)

/-- **The reduction `D(n) → Γ(T(n)_e, 𝒪)`, landing in the sections over the source of the
transition `T(n)_e ⟶ T(m)_e`** with their two scalar actions of the sections over the target. -/
def levelRingAlongReduce :
    ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u) →+ ringAlong (wholeSpaceTrans hp φ e).hom :=
  AddMonoidHom.mk' (fun b ↦ ringAlongSection _ (bigRingSection _ (levelSectionsScalars hp ⦋n⦌ e b)))
    fun x y ↦ by
      rw [map_add]
      rfl

attribute [local instance] isAffineTargetWholeSpaceSystem

/-- The restriction of a quasi-coherent crystal to the ambient scheme of a level is
quasi-coherent (`...SmallSite.isQuasicoherent_ambientWholeSpaceSystem`). -/
local instance isQuasicoherentAmbientWholeSpaceLevel (k l : ℕ) :
    (ambientSchemeOf (levelObj hp k l).obj
      (moduleRestrictionSheaf Fc.obj (levelObj hp k l))).IsQuasicoherent :=
  isQuasicoherent_ambientWholeSpaceSystem hp Fc.obj
    (isLocallyQuasiCoherent_of_isQuasicoherentOnSite Fc.obj Fc.property.1) k l

/-- **The base change of the ambient sections of `ℱ` along the transition `T(n)_e ⟶ T(m)_e`**,
`Γ(T(n)_e, 𝒪) ⊗_{Γ(T(m)_e, 𝒪)} Γ(T(m)_e, ℱ) → Γ(T(n)_e, ℱ)`, as an additive map. -/
def levelAmbientBaseChange :
    ringAlong (wholeSpaceTrans hp φ e).hom ⊗[
        Γ((levelObj hp m e).obj.thickening.target.scheme, ⊤)]
        Γ(ambientSchemeOf (levelObj hp m e).obj
          (moduleRestrictionSheaf Fc.obj (levelObj hp m e)), ⊤) →+
      Γ(ambientSchemeOf (levelObj hp n e).obj
        (moduleRestrictionSheaf Fc.obj (levelObj hp n e)), ⊤) :=
  ambientBaseChangeTensorHom (wholeSpaceTrans hp φ e).hom
    (moduleRestrictionSheaf Fc.obj (levelObj hp m e))
    (moduleRestrictionSheaf Fc.obj (levelObj hp n e))
    (moduleFMapSheaf Fc.obj (wholeSpaceTrans hp φ e))

/-- **The base change at a level is bijective**, which is the crystal property:
`...SmallSite.bijective_wholeSpaceCosimplicialBaseChange`. -/
theorem bijective_levelAmbientBaseChange :
    Function.Bijective (levelAmbientBaseChange hp Fc φ e) := by
  have hc : IsSheafCrystal Fc.obj := Fc.property.2
  have h := bijective_wholeSpaceCosimplicialBaseChange hp Fc.obj φ e hc
  have h2 : Function.Bijective (ambientBaseChangeTensorFun (wholeSpaceTrans hp φ e).hom
    (moduleRestrictionSheaf Fc.obj (levelObj hp m e))
    (moduleRestrictionSheaf Fc.obj (levelObj hp n e))
    (moduleFMapSheaf Fc.obj (wholeSpaceTrans hp φ e))) := h
  exact h2

/-- The reduction of the scalars is compatible with the transition `D(m) → D(n)`. -/
theorem levelAmbientScalars_smul_levelRingAlongReduce
    (a : ((wholeSpaceEnvelopeRing hp).obj ⦋m⦌ : Type u))
    (b : ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u)) :
    levelAmbientScalars hp m e a • levelRingAlongReduce hp φ e b =
      levelRingAlongReduce hp φ e (((wholeSpaceEnvelopeRing hp).map φ).hom a * b) := by
  show ambientRingSection (levelObj hp m e).obj
        (bigRingSection _ (levelSectionsScalars hp ⦋m⦌ e a)) •
      ringAlongSection _ (bigRingSection _ (levelSectionsScalars hp ⦋n⦌ e b)) =
    ringAlongSection _ (bigRingSection _
      (levelSectionsScalars hp ⦋n⦌ e (((wholeSpaceEnvelopeRing hp).map φ).hom a * b)))
  rw [ambientRingSection_smul_ringAlong, map_mul, bigRingSection_mul,
    crysSheafRingMap_bigRingSection, siteRingAlong_ringAlongSection]
  exact congrArg (fun z ↦ ringAlongSection _ (bigRingSection _ z *
    bigRingSection _ (levelSectionsScalars hp ⦋n⦌ e b)))
    (levelSectionsScalars_restriction hp φ e a)

/-- The reduction of the limit to the ambient sections of a level is semilinear. -/
theorem levelSectionsTopReduce_smul (k : ℕ) (a : ((wholeSpaceEnvelopeRing hp).obj ⦋k⦌ : Type u))
    (x : wholeSpaceSections hp Fc ⦋k⦌) :
    levelSectionsTopReduce hp Fc k e (a • x) =
      levelAmbientScalars hp k e a • levelSectionsTopReduce hp Fc k e x := by
  rw [levelSectionsTopReduce_apply, levelSectionsTopReduce_apply, wholeSpaceSectionsVal_smul,
    crysSectionTop_smul]
  rfl

/-- **The base change at a level, on the reductions of a pure tensor**: `b ⊗ x` goes to the
reduction of `b • φ_* x`. -/
theorem levelAmbientBaseChange_tmul (b : ((wholeSpaceEnvelopeRing hp).obj ⦋n⦌ : Type u))
    (x : wholeSpaceSections hp Fc ⦋m⦌) :
    levelAmbientBaseChange hp Fc φ e
        (levelRingAlongReduce hp φ e b ⊗ₜ levelSectionsTopReduce hp Fc m e x) =
      levelSectionsTopReduce hp Fc n e (b • wholeSpaceSectionsTrans hp Fc φ x) := by
  have ha : levelRingAlongReduce hp φ e b =
      ringAlongSection _ (bigRingSection _ (levelSectionsScalars hp ⦋n⦌ e b)) := rfl
  have hb : levelSectionsTopReduce hp Fc m e x =
      crysSectionTop Fc.obj (levelObj hp m e) (wholeSpaceSectionsVal hp Fc x e) := rfl
  rw [ha, hb]
  unfold levelAmbientBaseChange
  rw [ambientBaseChangeTensorHom_apply, ambientBaseChangeTensorFun_tmul]
  rw [fmapTopSection_crysSectionTop, siteRingAlong_ringAlongSection, levelSectionsTopReduce_apply,
    wholeSpaceSectionsVal_smul, crysSectionTop_smul, wholeSpaceSectionsVal_trans]
  rfl

variable {Fc} in
/-- **The kernel of the reduction of `M(k)` to the ambient sections of the level `e` is
`(p)^{N+e} M(k)`.** -/
theorem levelSectionsTopReduce_eq_zero_iff (hM : IsSurjectiveComparison Fc.obj.val) (k : ℕ)
    (y : wholeSpaceSections hp Fc ⦋k⦌) :
    levelSectionsTopReduce hp Fc k e y = 0 ↔
      y ∈ pAdicIdeal (A := ((wholeSpaceEnvelopeRing hp).obj ⦋k⦌ : Type u)) S.p ^
          (_root_.Crystalline.uniformLevel (affineSituation S hp) + e) •
        (⊤ : Submodule ((wholeSpaceEnvelopeRing hp).obj ⦋k⦌ : Type u)
          (wholeSpaceSections hp Fc ⦋k⦌)) := by
  rw [levelSectionsTopReduce_apply, crysSectionTop_eq_zero_iff,
    mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero hp Fc hM k e y]

variable {Fc} in
/-- The reduction of `M(k)` to the ambient sections of a level is surjective. -/
theorem surjective_levelSectionsTopReduce (hM : IsSurjectiveComparison Fc.obj.val) (k : ℕ) :
    Function.Surjective (levelSectionsTopReduce hp Fc k e) :=
  (bijective_crysSectionTop Fc.obj (levelObj hp k e)).2.comp
    (surjective_wholeSpaceSectionsVal hp Fc hM k e)

end Levels

/-! ### The completed base change on the limit modules -/

section Completed

variable (Fc : QuasiCoherentCrystal S) {m n : SimplexCategory} (φ : m ⟶ n)

/-- The transition `M(m) → M(n)` of the cosimplicial module, read as semilinear over the algebra
map of `(E.completedRingMap S.p φ).toAlgebra`. -/
def wholeSpaceTransAlgebraMap :
    letI : Algebra ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
        ((wholeSpaceDPAlgebra hp).completedRing S.p n.len) :=
      ((wholeSpaceDPAlgebra hp).completedRingMap S.p φ).toAlgebra
    (wholeSpaceCosimplicialModule hp Fc).carrier m.len →ₛₗ[algebraMap
        ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
        ((wholeSpaceDPAlgebra hp).completedRing S.p n.len)]
      (wholeSpaceCosimplicialModule hp Fc).carrier n.len :=
  (wholeSpaceCosimplicialModule hp Fc).map φ

/-- The algebra structure of `D(n)` over `D(m)` along the transition `φ`. -/
private abbrev completedRingAlgebra :
    Algebra ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
      ((wholeSpaceDPAlgebra hp).completedRing S.p n.len) :=
  ((wholeSpaceDPAlgebra hp).completedRingMap S.p φ).toAlgebra

/-- **The uncompleted base change `D(n) ⊗_{D(m)} M(m) → M(n)` is bijective modulo `(p)^{N+e}`**,
for every level `e`.  This is `Crystalline.bijective_adicQuotientMap_tensorLiftₛₗ` at the
reductions to the level `e`: the scalars `...SmallSite.levelAmbientScalars` and
`...SmallSite.levelRingAlongReduce` (surjective with kernel `(p)^{N+e}`), the modules
`...SmallSite.levelSectionsTopReduce` (surjective with kernel `(p)^{N+e} M`, by
`...SmallSite.mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero`), and the base change of
sections over the level, bijective by the crystal property. -/
theorem bijective_adicQuotientMap_wholeSpaceTrans (e : ℕ) :
    letI : Algebra ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
        ((wholeSpaceDPAlgebra hp).completedRing S.p n.len) :=
      ((wholeSpaceDPAlgebra hp).completedRingMap S.p φ).toAlgebra
    Function.Bijective (adicQuotientMap (tensorLiftₛₗ (wholeSpaceTransAlgebraMap hp Fc φ))
      (pAdicIdeal_map_id_le S.p)
      (_root_.Crystalline.uniformLevel (affineSituation S hp) + e)) := by
  let := completedRingAlgebra hp φ
  have hM : IsSurjectiveComparison Fc.obj.val :=
    isSurjectiveComparison_of_isSheafCrystal Fc.property.2
  exact bijective_adicQuotientMap_tensorLiftₛₗ S.p _ (wholeSpaceTransAlgebraMap hp Fc φ)
    (πA := levelAmbientScalars hp m.len e) (πB := levelRingAlongReduce hp φ e)
    (ρ := levelSectionsTopReduce hp Fc m.len e) (ρ' := levelSectionsTopReduce hp Fc n.len e)
    (levelAmbientScalars_smul_levelRingAlongReduce hp φ e)
    (levelSectionsTopReduce_smul hp Fc e m.len)
    (surjective_levelSectionsScalars hp _ e) (surjective_levelSectionsScalars hp _ e)
    (surjective_levelSectionsTopReduce hp e hM m.len)
    (fun b hb ↦ (levelSectionsScalars_eq_zero_iff hp _ e b).1 hb)
    (fun y hy ↦ (levelSectionsTopReduce_eq_zero_iff hp e hM m.len y).1 hy)
    (levelAmbientBaseChange hp Fc φ e) (bijective_levelAmbientBaseChange hp Fc φ e)
    (fun b x ↦ (levelAmbientBaseChange_tmul hp Fc φ e b x))
    (fun y ↦ levelSectionsTopReduce_eq_zero_iff hp e hM n.len y)

/-- **The crystal base change on the limit modules**, the forward map
`D(n) ⊗̂_{D(m)} M(m) → M(n)` extending `x ⊗ y ↦ x • φ_* y` to the `p`-adic completion. -/
def wholeSpaceBaseChangeHom :
    letI : Algebra ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
        ((wholeSpaceDPAlgebra hp).completedRing S.p n.len) :=
      ((wholeSpaceDPAlgebra hp).completedRingMap S.p φ).toAlgebra
    CompletedConnection.baseChangeCarrier S.p ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
        ((wholeSpaceDPAlgebra hp).completedRing S.p n.len)
        ((wholeSpaceCosimplicialModule hp Fc).carrier m.len) →ₗ[
        (wholeSpaceDPAlgebra hp).completedRing S.p n.len]
      (wholeSpaceCosimplicialModule hp Fc).carrier n.len :=
  letI : Algebra ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
      ((wholeSpaceDPAlgebra hp).completedRing S.p n.len) :=
    ((wholeSpaceDPAlgebra hp).completedRingMap S.p φ).toAlgebra
  completedTensorLiftₛₗ S.p (wholeSpaceTransAlgebraMap hp Fc φ)

/-- **The crystal base change on the limit modules is bijective.**  Modulo `(p)^{N+e}` it is the
base change of sections over the level `e`, which is bijective for a crystal
(`...SmallSite.bijective_wholeSpaceCosimplicialBaseChange`), the levels of the limit modules being
their quotients by `(p)^{N+e}` (`...SmallSite.mem_pow_smul_top_iff_wholeSpaceSectionsVal_eq_zero`);
bijectivity at the levels from `N` on passes to the completion. -/
theorem bijective_wholeSpaceBaseChangeHom :
    Function.Bijective (wholeSpaceBaseChangeHom hp Fc φ) := by
  let := completedRingAlgebra hp φ
  exact bijective_completedTensorLiftₛₗ S.p (wholeSpaceTransAlgebraMap hp Fc φ)
    (_root_.Crystalline.uniformLevel (affineSituation S hp))
    (bijective_adicQuotientMap_wholeSpaceTrans hp Fc φ)

/-- **The crystal base-change isomorphism on the limit modules of the cosimplicial system of
[Stacks, Tag 07JN]**: for `φ : m ⟶ n` in the simplex category,

`D(n) ⊗̂_{D(m)} M(m) ≅ M(n)`,  `x ⊗ y ↦ x • φ_* y`,

where `D(b)` is the completed cosimplicial envelope, `M(b) = lim_e Γ((X, T(b)_e, δ(b)), ℱ)` for a
crystal `ℱ` in quasi-coherent `𝒪_{X/S}`-modules, and `⊗̂` is the `p`-adically completed tensor
product `Crystalline.CompletedConnection.baseChangeCarrier`. -/
def wholeSpaceBaseChangeEquiv :
    letI : Algebra ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
        ((wholeSpaceDPAlgebra hp).completedRing S.p n.len) :=
      ((wholeSpaceDPAlgebra hp).completedRingMap S.p φ).toAlgebra
    CompletedConnection.baseChangeCarrier S.p ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
        ((wholeSpaceDPAlgebra hp).completedRing S.p n.len)
        ((wholeSpaceCosimplicialModule hp Fc).carrier m.len) ≃ₗ[
        (wholeSpaceDPAlgebra hp).completedRing S.p n.len]
      (wholeSpaceCosimplicialModule hp Fc).carrier n.len :=
  letI : Algebra ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
      ((wholeSpaceDPAlgebra hp).completedRing S.p n.len) :=
    ((wholeSpaceDPAlgebra hp).completedRingMap S.p φ).toAlgebra
  LinearEquiv.ofBijective (wholeSpaceBaseChangeHom hp Fc φ)
    (bijective_wholeSpaceBaseChangeHom hp Fc φ)

/-- **The base-change isomorphism on the image of a pure tensor**: `x ⊗ y ↦ x • φ_* y`. -/
theorem wholeSpaceBaseChangeEquiv_of_tmul
    (x : (wholeSpaceDPAlgebra hp).completedRing S.p n.len)
    (y : (wholeSpaceCosimplicialModule hp Fc).carrier m.len) :
    letI : Algebra ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
        ((wholeSpaceDPAlgebra hp).completedRing S.p n.len) :=
      ((wholeSpaceDPAlgebra hp).completedRingMap S.p φ).toAlgebra
    wholeSpaceBaseChangeEquiv hp Fc φ (AdicCompletion.of _ _ (x ⊗ₜ y)) =
      x • (wholeSpaceCosimplicialModule hp Fc).map φ y := by
  let := completedRingAlgebra hp φ
  exact completedTensorLiftₛₗ_of S.p (wholeSpaceTransAlgebraMap hp Fc φ) (x ⊗ₜ y)

/-- **On the inclusion `y ↦ 1 ⊗ y` the base-change isomorphism is the transition map** of the
cosimplicial module. -/
theorem wholeSpaceBaseChangeEquiv_baseChangeInclusion
    (y : (wholeSpaceCosimplicialModule hp Fc).carrier m.len) :
    letI : Algebra ((wholeSpaceDPAlgebra hp).completedRing S.p m.len)
        ((wholeSpaceDPAlgebra hp).completedRing S.p n.len) :=
      ((wholeSpaceDPAlgebra hp).completedRingMap S.p φ).toAlgebra
    wholeSpaceBaseChangeEquiv hp Fc φ
        (CompletedConnection.baseChangeInclusion S.p _ _ _ y) =
      (wholeSpaceCosimplicialModule hp Fc).map φ y := by
  let := completedRingAlgebra hp φ
  rw [CompletedConnection.baseChangeInclusion_apply, wholeSpaceBaseChangeEquiv_of_tmul, one_smul]

end Completed

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
