module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation

/-!
# The relative Koszul complex of a short exact sequence of flat modules

Let `B` be a commutative ring and let `0 → A --f--> M --g--> Q → 0` be a short exact sequence of
`B`-modules with `A`, `M` and `Q` flat. For every `k` the *relative Koszul complex* in total
degree `k`,

`0 → ⋀ᵏA ⊗ Sym⁰M → ⋀ᵏ⁻¹A ⊗ Sym¹M → ⋯ → ⋀¹A ⊗ Symᵏ⁻¹M → ⋀⁰A ⊗ SymᵏM → SymᵏQ → 0`,

whose differential sends `x ⊗ s` to `∑ᵢ (-1)ⁱ (x with its i-th factor removed) ⊗ f(xᵢ)·s`, is
exact. The differential in bidegree `(p, q)` is
`Stacks.ChaoticSite.koszulDifferential (SymPow.symMulMapBil q f) p`.

## Main results

* `SymPow.relativeKoszul_exact`: exactness in the interior of the complex.
* `SymPow.relativeKoszul_injective`: injectivity of the leftmost map `⋀^{p+1}A ⊗ Sym⁰M → ⋯`.
* `SymPow.relativeKoszul_exact_zero`: exactness at the right end, against `Symᵏ(g)`.

## Implementation notes

Everything is deduced from the *ungraded* relative Koszul differential
`SymPow.relSymKoszulDifferential f p : (⋀^{p+1}A) ⊗ Sym(M) → (⋀^p A) ⊗ Sym(M)`, obtained from
`Stacks.ChaoticSite.koszulDifferential` applied to the action of `A` on `Sym(M)` by
multiplication by `ι (f a)`. Its exactness, `SymPow.relSymKoszul_exact`, is proved in three
steps, mirroring the absolute case in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing`:

* for the split sequence `0 → A → A × Q → Q → 0` the symmetric algebra of `A × Q` is
  `Sym(A) ⊗ Sym(Q)` (`SymPow.prodSymEquiv`), the relative differential becomes the absolute
  Koszul differential of `A` tensored with `Sym(Q)`, and the absolute exactness
  `Stacks.ChaoticSite.symmetricKoszul_exact_of_flat` propagates through the flat module
  `Sym(Q)`;
* a short exact sequence admitting a splitting is isomorphic to the split one;
* in general `Q` is flat, hence a filtered colimit of finite free modules `Qᵢ` by Lazard's
  theorem, and `M` is the filtered colimit of the pullbacks `Mᵢ = M ×_Q Qᵢ`, each of which sits
  in a short exact sequence `0 → A → Mᵢ → Qᵢ → 0` that splits because `Qᵢ` is free. Exactness
  passes to the colimit because `Sym` and `- ⊗ -` commute with filtered colimits.

The graded statements are deduced from the ungraded one through the splitting
`Sym(M) → Symᵏ(M)` of `Stacks.ChaoticSite.symmetricPowerProjection`, exactly as in
`Stacks.ChaoticSite.homogeneousKoszul_exact_of_symmetricKoszul_exact`. Injectivity of the
leftmost map uses in addition that the ungraded differential *strictly raises* the symmetric
degree, so that nothing in its image has a component in symmetric degree zero. Exactness at the
right end is the right-exactness of `Sym` from
`StacksFrontier.LinearAlgebra.SymmetricPower.Presentation`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

open Stacks.ChaoticSite

namespace SymPow

universe u

/-! ## The ungraded relative Koszul differential -/

section Ungraded

variable {B A M N : Type*} [CommRing B] [AddCommGroup A] [Module B A]
  [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]

/-- The action of `A` on the symmetric algebra of `M` along `f : A →ₗ[B] M`: the element `a`
acts as multiplication by the degree-one element `ι (f a)`. -/
public def relSymKoszulAction (f : A →ₗ[B] M) :
    A →ₗ[B] SymmetricAlgebra B M →ₗ[B] SymmetricAlgebra B M :=
  (LinearMap.mul B (SymmetricAlgebra B M)).comp ((SymmetricAlgebra.ι B M).comp f)

/-- The relative action of `A` on `Sym(M)` is multiplication by `ι (f a)`. -/
public lemma relSymKoszulAction_apply (f : A →ₗ[B] M) (a : A) (z : SymmetricAlgebra B M) :
    relSymKoszulAction f a z = SymmetricAlgebra.ι B M (f a) * z := rfl

/-- The relative Koszul differential of `f : A →ₗ[B] M`, in its ungraded form
`(⋀^{p+1}A) ⊗ Sym(M) → (⋀^p A) ⊗ Sym(M)`. -/
public def relSymKoszulDifferential (f : A →ₗ[B] M) (p : ℕ) :
    ((⋀[B]^(p + 1) A) ⊗[B] SymmetricAlgebra B M) →ₗ[B]
      ((⋀[B]^p A) ⊗[B] SymmetricAlgebra B M) :=
  koszulDifferential (relSymKoszulAction f) p

/-- The ungraded relative Koszul differential squares to zero. -/
public lemma relSymKoszulDifferential_comp (f : A →ₗ[B] M) (p : ℕ) :
    (relSymKoszulDifferential f p).comp (relSymKoszulDifferential f (p + 1)) = 0 :=
  koszulDifferential_comp _ _
    (fun x y z => mul_left_comm (SymmetricAlgebra.ι B M (f y)) (SymmetricAlgebra.ι B M (f x)) z) p

/-- The ungraded relative Koszul differential is natural in the target module. -/
public lemma relSymKoszulDifferential_naturality (f : A →ₗ[B] M) (uu : M →ₗ[B] N) (p : ℕ) :
    ((symmetricAlgebraMap uu).toLinearMap.lTensor (⋀[B]^p A)).comp
        (relSymKoszulDifferential f p) =
      (relSymKoszulDifferential (uu.comp f) p).comp
        ((symmetricAlgebraMap uu).toLinearMap.lTensor (⋀[B]^(p + 1) A)) := by
  have hab : ∀ (x : A) (z : SymmetricAlgebra B M),
      (symmetricAlgebraMap uu).toLinearMap (relSymKoszulAction f x z) =
        relSymKoszulAction (uu.comp f) x ((symmetricAlgebraMap uu).toLinearMap z) := by
    intro x z
    show symmetricAlgebraMap uu (SymmetricAlgebra.ι B M (f x) * z) =
      SymmetricAlgebra.ι B N (uu (f x)) * symmetricAlgebraMap uu z
    rw [map_mul, symmetricAlgebraMap_ι]
  simpa only [exteriorPower.map_id, relSymKoszulDifferential, LinearMap.lTensor_def] using
    koszulDifferential_naturality (relSymKoszulAction f) (relSymKoszulAction (uu.comp f))
      LinearMap.id (symmetricAlgebraMap uu).toLinearMap
      (symmetricAlgebraMap uu).toLinearMap hab p

/-- Exactness of two families of maps `⋀^{n+1}A ⊗ S → ⋀^n A ⊗ S` and `⋀^{n+1}A ⊗ T → ⋀^n A ⊗ T`
at degree `p` agree when they are intertwined by `id ⊗ e` for an equivalence `e : S ≃ T`. -/
private theorem exact_iff_of_tensor_equiv {S T : Type*} [AddCommGroup S] [Module B S]
    [AddCommGroup T] [Module B T] (e : S ≃ₗ[B] T)
    (F : ∀ n : ℕ, ((⋀[B]^(n + 1) A) ⊗[B] S) →ₗ[B] ((⋀[B]^n A) ⊗[B] S))
    (G : ∀ n : ℕ, ((⋀[B]^(n + 1) A) ⊗[B] T) →ₗ[B] ((⋀[B]^n A) ⊗[B] T)) (p : ℕ)
    (h : ∀ n, (G n).comp (TensorProduct.congr (LinearEquiv.refl B (⋀[B]^(n + 1) A)) e).toLinearMap =
      (TensorProduct.congr (LinearEquiv.refl B (⋀[B]^n A)) e).toLinearMap.comp (F n)) :
    Function.Exact (G (p + 1)) (G p) ↔ Function.Exact (F (p + 1)) (F p) :=
  Function.Exact.iff_of_ladder_linearEquiv (h (p + 1)) (h p)

/-- Exactness of the ungraded relative Koszul complex only depends on `f` up to an isomorphism
of its target. -/
public lemma relSymKoszul_exact_of_equiv (f : A →ₗ[B] M) (e : M ≃ₗ[B] N) (p : ℕ)
    (h : Function.Exact (relSymKoszulDifferential (e.toLinearMap.comp f) (p + 1))
      (relSymKoszulDifferential (e.toLinearMap.comp f) p)) :
    Function.Exact (relSymKoszulDifferential f (p + 1)) (relSymKoszulDifferential f p) := by
  refine (exact_iff_of_tensor_equiv (symmetricAlgebraEquiv e).toLinearEquiv
    (relSymKoszulDifferential f) (relSymKoszulDifferential (e.toLinearMap.comp f)) p
    fun n => (relSymKoszulDifferential_naturality f e.toLinearMap n).symm).mp h

end Ungraded

/-! ## Tensoring a Koszul complex with a flat module -/

section KoszulRTensor

variable {B M P Q : Type*} [CommRing B] [AddCommGroup M] [Module B M]
  [AddCommGroup P] [Module B P] [AddCommGroup Q] [Module B Q]

/-- The action obtained from `a : M →ₗ[B] P →ₗ[B] Q` by tensoring with a fixed module `L` on
the right. -/
public def rTensorAction (a : M →ₗ[B] P →ₗ[B] Q) (L : Type*) [AddCommGroup L] [Module B L] :
    M →ₗ[B] (P ⊗[B] L) →ₗ[B] (Q ⊗[B] L) :=
  (LinearMap.rTensorHom L).comp a

/-- The right-tensored action acts by right-tensoring the original action. -/
public lemma rTensorAction_apply (a : M →ₗ[B] P →ₗ[B] Q) (L : Type*) [AddCommGroup L]
    [Module B L] (x : M) (w : P ⊗[B] L) :
    rTensorAction a L x w = LinearMap.rTensor L (a x) w := rfl

/-- Up to associativity, the Koszul differential of a right-tensored action is the Koszul
differential of the original action, tensored with the identity. -/
public lemma koszulDifferential_rTensor (a : M →ₗ[B] P →ₗ[B] Q) (L : Type*) [AddCommGroup L]
    [Module B L] (p : ℕ) :
    (TensorProduct.assoc B (⋀[B]^p M) Q L).symm.toLinearMap.comp
        (koszulDifferential (rTensorAction a L) p) =
      (LinearMap.rTensor L (koszulDifferential a p)).comp
        (TensorProduct.assoc B (⋀[B]^(p + 1) M) P L).symm.toLinearMap := by
  apply TensorProduct.ext
  apply LinearMap.ext_on (exteriorPower.ιMulti_span B (p + 1) M)
  rintro _ ⟨v, rfl⟩
  ext z₁ z₂
  show (TensorProduct.assoc B (⋀[B]^p M) Q L).symm
      (koszulDifferential (rTensorAction a L) p
        (exteriorPower.ιMulti B (p + 1) v ⊗ₜ[B] (z₁ ⊗ₜ[B] z₂))) =
    LinearMap.rTensor L (koszulDifferential a p)
      ((TensorProduct.assoc B (⋀[B]^(p + 1) M) P L).symm
        (exteriorPower.ιMulti B (p + 1) v ⊗ₜ[B] (z₁ ⊗ₜ[B] z₂)))
  rw [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, koszulDifferential_tmul,
    koszulDifferential_tmul, map_sum, TensorProduct.sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.smul_tmul', rTensorAction_apply, LinearMap.rTensor_tmul,
    TensorProduct.assoc_symm_tmul, TensorProduct.smul_tmul']

/-- Exactness of a Koszul complex is preserved by tensoring with a flat module. -/
public lemma koszulDifferential_rTensor_exact (a : M →ₗ[B] P →ₗ[B] P) (L : Type*)
    [AddCommGroup L] [Module B L] [Module.Flat B L] (p : ℕ)
    (h : Function.Exact (koszulDifferential a (p + 1)) (koszulDifferential a p)) :
    Function.Exact (koszulDifferential (rTensorAction a L) (p + 1))
      (koszulDifferential (rTensorAction a L) p) := by
  have hrt := Module.Flat.rTensor_exact L h
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (koszulDifferential_rTensor a L (p + 1)).symm
    (koszulDifferential_rTensor a L p).symm).mp hrt

end KoszulRTensor

/-! ## The split sequence `0 → A → A × Q → Q → 0` -/

section Product

variable (B A Q : Type*) [CommRing B] [AddCommGroup A] [Module B A]
  [AddCommGroup Q] [Module B Q]

/-- The linear map `A × Q →ₗ[B] Sym(A) ⊗ Sym(Q)` sending `(a, q)` to `ι a ⊗ 1 + 1 ⊗ ι q`. -/
public def prodSymIota :
    (A × Q) →ₗ[B] SymmetricAlgebra B A ⊗[B] SymmetricAlgebra B Q :=
  ((TensorProduct.mk B (SymmetricAlgebra B A) (SymmetricAlgebra B Q)).flip 1).comp
      ((SymmetricAlgebra.ι B A).comp (LinearMap.fst B A Q)) +
    ((TensorProduct.mk B (SymmetricAlgebra B A) (SymmetricAlgebra B Q)) 1).comp
      ((SymmetricAlgebra.ι B Q).comp (LinearMap.snd B A Q))

/-- The algebra map `Sym(A × Q) → Sym(A) ⊗ Sym(Q)` determined by `prodSymIota`. -/
public def prodSymHom :
    SymmetricAlgebra B (A × Q) →ₐ[B] SymmetricAlgebra B A ⊗[B] SymmetricAlgebra B Q :=
  SymmetricAlgebra.lift (prodSymIota B A Q)

/-- The algebra map `Sym(A) ⊗ Sym(Q) → Sym(A × Q)` induced by the two inclusions. -/
public def prodSymInv :
    SymmetricAlgebra B A ⊗[B] SymmetricAlgebra B Q →ₐ[B] SymmetricAlgebra B (A × Q) :=
  Algebra.TensorProduct.lift (symmetricAlgebraMap (LinearMap.inl B A Q))
    (symmetricAlgebraMap (LinearMap.inr B A Q)) (fun _ _ => Commute.all _ _)

/-- The symmetric algebra of a product is the tensor product of the symmetric algebras. -/
public def prodSymEquiv : SymmetricAlgebra B (A × Q) ≃ₐ[B]
    SymmetricAlgebra B A ⊗[B] SymmetricAlgebra B Q :=
  AlgEquiv.ofAlgHom (prodSymHom B A Q) (prodSymInv B A Q)
    (by
      apply Algebra.TensorProduct.ext
      · apply SymmetricAlgebra.algHom_ext
        apply LinearMap.ext
        intro a
        change prodSymHom B A Q (prodSymInv B A Q
            (SymmetricAlgebra.ι B A a ⊗ₜ[B] (1 : SymmetricAlgebra B Q))) =
          SymmetricAlgebra.ι B A a ⊗ₜ[B] (1 : SymmetricAlgebra B Q)
        rw [prodSymInv, Algebra.TensorProduct.lift_tmul, symmetricAlgebraMap_ι, map_one, mul_one,
          prodSymHom, SymmetricAlgebra.lift_ι_apply]
        simp [prodSymIota]
      · apply SymmetricAlgebra.algHom_ext
        apply LinearMap.ext
        intro q
        change prodSymHom B A Q (prodSymInv B A Q
            ((1 : SymmetricAlgebra B A) ⊗ₜ[B] SymmetricAlgebra.ι B Q q)) =
          (1 : SymmetricAlgebra B A) ⊗ₜ[B] SymmetricAlgebra.ι B Q q
        rw [prodSymInv, Algebra.TensorProduct.lift_tmul, symmetricAlgebraMap_ι, map_one, one_mul,
          prodSymHom, SymmetricAlgebra.lift_ι_apply]
        simp [prodSymIota])
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro x
      change prodSymInv B A Q (prodSymHom B A Q (SymmetricAlgebra.ι B (A × Q) x)) =
        SymmetricAlgebra.ι B (A × Q) x
      rw [prodSymHom, SymmetricAlgebra.lift_ι_apply]
      change prodSymInv B A Q (SymmetricAlgebra.ι B A x.1 ⊗ₜ[B] (1 : SymmetricAlgebra B Q) +
        (1 : SymmetricAlgebra B A) ⊗ₜ[B] SymmetricAlgebra.ι B Q x.2) =
          SymmetricAlgebra.ι B (A × Q) x
      rw [map_add, prodSymInv, Algebra.TensorProduct.lift_tmul,
        Algebra.TensorProduct.lift_tmul, symmetricAlgebraMap_ι, symmetricAlgebraMap_ι, map_one,
        map_one, mul_one, one_mul, ← map_add, LinearMap.inl_apply, LinearMap.inr_apply,
        Prod.mk_add_mk, add_zero, zero_add])

/-- `prodSymEquiv` turns multiplication by `ι (a, 0)` into multiplication by `ι a ⊗ 1`. -/
public lemma prodSymEquiv_mul_inl (a : A) (z : SymmetricAlgebra B (A × Q)) :
    prodSymEquiv B A Q (SymmetricAlgebra.ι B (A × Q) (LinearMap.inl B A Q a) * z) =
      (SymmetricAlgebra.ι B A a ⊗ₜ[B] (1 : SymmetricAlgebra B Q)) * prodSymEquiv B A Q z := by
  have h1 : prodSymEquiv B A Q (SymmetricAlgebra.ι B (A × Q) (LinearMap.inl B A Q a)) =
      SymmetricAlgebra.ι B A a ⊗ₜ[B] (1 : SymmetricAlgebra B Q) := by
    show prodSymHom B A Q (SymmetricAlgebra.ι B (A × Q) (a, 0)) =
      SymmetricAlgebra.ι B A a ⊗ₜ[B] (1 : SymmetricAlgebra B Q)
    rw [prodSymHom, SymmetricAlgebra.lift_ι_apply]
    simp [prodSymIota]
  rw [map_mul, h1]

/-- Multiplication by `ι a ⊗ 1` on `Sym(A) ⊗ Sym(Q)` is the right tensor product of
multiplication by `ι a` on `Sym(A)` with the identity of `Sym(Q)`. -/
public lemma rTensor_symmetricKoszulAction (a : A)
    (w : SymmetricAlgebra B A ⊗[B] SymmetricAlgebra B Q) :
    LinearMap.rTensor (SymmetricAlgebra B Q) (symmetricKoszulAction B A a) w =
      (SymmetricAlgebra.ι B A a ⊗ₜ[B] (1 : SymmetricAlgebra B Q)) * w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, mul_add]

/-- `prodSymEquiv` intertwines the action of `A` on `Sym(A × Q)` along `A → A × Q` with the
action of `A` on `Sym(A) ⊗ Sym(Q)` by multiplication in the first factor. -/
public lemma prodSymEquiv_symm_rTensorAction (a : A)
    (w : SymmetricAlgebra B A ⊗[B] SymmetricAlgebra B Q) :
    (prodSymEquiv B A Q).symm
        (rTensorAction (symmetricKoszulAction B A) (SymmetricAlgebra B Q) a w) =
      relSymKoszulAction (LinearMap.inl B A Q) a ((prodSymEquiv B A Q).symm w) := by
  apply (prodSymEquiv B A Q).injective
  rw [AlgEquiv.apply_symm_apply, relSymKoszulAction_apply, prodSymEquiv_mul_inl,
    AlgEquiv.apply_symm_apply, rTensorAction_apply, rTensor_symmetricKoszulAction]

/-- Under `prodSymEquiv` the Koszul differential of the first-factor action on
`Sym(A) ⊗ Sym(Q)` becomes the relative Koszul differential of `A → A × Q`. -/
public lemma prodSym_ladder (n : ℕ) :
    (relSymKoszulDifferential (LinearMap.inl B A Q) n).comp
        (TensorProduct.map (LinearMap.id : (⋀[B]^(n + 1) A) →ₗ[B] (⋀[B]^(n + 1) A))
          (prodSymEquiv B A Q).symm.toLinearMap) =
      (TensorProduct.map (LinearMap.id : (⋀[B]^n A) →ₗ[B] (⋀[B]^n A))
          (prodSymEquiv B A Q).symm.toLinearMap).comp
        (koszulDifferential (rTensorAction (symmetricKoszulAction B A)
          (SymmetricAlgebra B Q)) n) := by
  symm
  simpa only [exteriorPower.map_id, relSymKoszulDifferential] using
    koszulDifferential_naturality
      (rTensorAction (symmetricKoszulAction B A) (SymmetricAlgebra B Q))
      (relSymKoszulAction (LinearMap.inl B A Q)) LinearMap.id
      (prodSymEquiv B A Q).symm.toLinearMap (prodSymEquiv B A Q).symm.toLinearMap
      (fun x z => prodSymEquiv_symm_rTensorAction B A Q x z) n

/-- **The split case.** The ungraded relative Koszul complex of the inclusion `A → A × Q` is
exact when `A` and `Q` are flat. -/
public lemma relSymKoszul_exact_prod [Module.Flat B A] [Module.Flat B Q] (p : ℕ) :
    Function.Exact (relSymKoszulDifferential (LinearMap.inl B A Q) (p + 1))
      (relSymKoszulDifferential (LinearMap.inl B A Q) p) := by
  have hflat := symmetricAlgebra_flat B Q
  have habs : Function.Exact (koszulDifferential (symmetricKoszulAction B A) (p + 1))
      (koszulDifferential (symmetricKoszulAction B A) p) :=
    symmetricKoszul_exact_of_flat B A p
  have hmid := koszulDifferential_rTensor_exact (symmetricKoszulAction B A)
    (SymmetricAlgebra B Q) p habs
  exact (exact_iff_of_tensor_equiv (prodSymEquiv B A Q).symm.toLinearEquiv
    (koszulDifferential (rTensorAction (symmetricKoszulAction B A) (SymmetricAlgebra B Q)))
    (relSymKoszulDifferential (LinearMap.inl B A Q)) p (prodSym_ladder B A Q)).mpr hmid

end Product

/-! ## Sequences admitting a splitting -/

section Splitting

variable {B A M Q : Type*} [CommRing B] [AddCommGroup A] [Module B A]
  [AddCommGroup M] [Module B M] [AddCommGroup Q] [Module B Q]

/-- **The split case, transported.** A short exact sequence `0 → A → M → Q → 0` admitting a
section of `g` has exact ungraded relative Koszul complex, provided `A` and `Q` are flat. -/
public lemma relSymKoszul_exact_of_splitting [Module.Flat B A] [Module.Flat B Q]
    (f : A →ₗ[B] M) (g : M →ₗ[B] Q) (hf : Function.Injective f) (hfg : Function.Exact f g)
    (t : Q →ₗ[B] M) (ht : g ∘ₗ t = LinearMap.id) (p : ℕ) :
    Function.Exact (relSymKoszulDifferential f (p + 1)) (relSymKoszulDifferential f p) := by
  obtain ⟨e, he, -⟩ := (hfg.splitSurjectiveEquiv hf) ⟨t, ht⟩
  apply relSymKoszul_exact_of_equiv f e p
  have hcomp : e.toLinearMap.comp f = LinearMap.inl B A Q := by
    apply LinearMap.ext
    intro a
    rw [LinearMap.comp_apply, he]
    simp
  rw [hcomp]
  exact relSymKoszul_exact_prod B A Q p

end Splitting

/-! ## Filtered colimits in the target module -/

section KoszulColimit

variable {B A : Type*} [CommRing B] [AddCommGroup A] [Module B A]
  {ι : Type*} [Preorder ι] [DecidableEq ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  {H : ι → Type*} [∀ i, AddCommGroup (H i)] [∀ i, Module B (H i)]

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
/-- The comparison `L ⊗ colim Kᵢ ≅ colim (L ⊗ Kᵢ)` carries `L ⊗ Kᵢ → L ⊗ colim K` to the
structure map of the colimit. -/
public lemma directLimitRight_lTensor_of {K : ι → Type*} [∀ i, AddCommGroup (K i)]
    [∀ i, Module B (K i)] (w : (i j : ι) → i ≤ j → K i →ₗ[B] K j)
    (L : Type*) [AddCommGroup L] [Module B L] (i : ι) :
    (TensorProduct.directLimitRight w L).toLinearMap.comp
        ((Module.DirectLimit.of B ι K w i).lTensor L) =
      Module.DirectLimit.of B ι (fun j => L ⊗[B] K j)
        (fun j k h => (w j k h).lTensor L) i :=
  TensorProduct.ext' fun a b => TensorProduct.directLimitRight_tmul_of w L a b

/-- Every element of `L ⊗ colim Kᵢ` comes from some `L ⊗ Kᵢ`. -/
public lemma lTensor_directLimit_exists {K : ι → Type*} [∀ i, AddCommGroup (K i)]
    [∀ i, Module B (K i)] (w : (i j : ι) → i ≤ j → K i →ₗ[B] K j)
    (L : Type*) [AddCommGroup L] [Module B L] (x : L ⊗[B] Module.DirectLimit K w) :
    ∃ i y, (Module.DirectLimit.of B ι K w i).lTensor L y = x := by
  obtain ⟨i, b, hb⟩ := Module.DirectLimit.exists_of (TensorProduct.directLimitRight w L x)
  refine ⟨i, b, (TensorProduct.directLimitRight w L).injective ?_⟩
  rw [← hb]
  exact LinearMap.congr_fun (directLimitRight_lTensor_of w L i) b

omit [Nonempty ι] in
/-- An element of `L ⊗ Kᵢ` dying in `L ⊗ colim Kᵢ` already dies in some `L ⊗ Kⱼ`. -/
public lemma lTensor_directLimit_zero {K : ι → Type*} [∀ i, AddCommGroup (K i)]
    [∀ i, Module B (K i)] (w : (i j : ι) → i ≤ j → K i →ₗ[B] K j)
    [DirectedSystem K (fun i j h => w i j h)]
    (L : Type*) [AddCommGroup L] [Module B L] (i : ι) (x : L ⊗[B] K i)
    (hx : (Module.DirectLimit.of B ι K w i).lTensor L x = 0) :
    ∃ j, ∃ hij : i ≤ j, (w i j hij).lTensor L x = 0 := by
  have hdsL := lTensor_directedSystem w L
  have hz : Module.DirectLimit.of B ι (fun j => L ⊗[B] K j)
      (fun j k h => (w j k h).lTensor L) i x = 0 := by
    rw [← LinearMap.congr_fun (directLimitRight_lTensor_of w L i) x, LinearMap.comp_apply, hx,
      map_zero]
  exact Module.DirectLimit.of.zero_exact hz

/-- The comparison of symmetric algebras with filtered colimits is compatible with the
structure maps, after tensoring with a fixed module. -/
public lemma symmetricAlgebraDirectLimit_lTensor (vH : (i j : ι) → i ≤ j → H i →ₗ[B] H j)
    [DirectedSystem H (fun i j h => vH i j h)] (L : Type*) [AddCommGroup L] [Module B L]
    (i : ι) (y : L ⊗[B] SymmetricAlgebra B (H i)) :
    (TensorProduct.congr (LinearEquiv.refl B L) (symmetricAlgebraDirectLimitEquiv vH))
        (((Module.DirectLimit.of B ι (fun i => SymmetricAlgebra B (H i))
          (fun i j h => (symmetricAlgebraMap (vH i j h)).toLinearMap) i).lTensor L) y) =
      ((symmetricAlgebraMap (Module.DirectLimit.of B ι H vH i)).toLinearMap.lTensor L) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [symmetricAlgebraDirectLimitEquiv_of]
  | add a b ha hb => simp [ha, hb]

/-- Every element of `L ⊗ Sym(colim Hᵢ)` comes from some `L ⊗ Sym(Hᵢ)`. -/
public lemma relSymKoszul_directLimit_exists (vH : (i j : ι) → i ≤ j → H i →ₗ[B] H j)
    [DirectedSystem H (fun i j h => vH i j h)] (L : Type*) [AddCommGroup L] [Module B L]
    (x : L ⊗[B] SymmetricAlgebra B (Module.DirectLimit H vH)) :
    ∃ i y, ((symmetricAlgebraMap
      (Module.DirectLimit.of B ι H vH i)).toLinearMap.lTensor L) y = x := by
  have hds := symmetricAlgebra_directedSystem vH
  obtain ⟨i, y, hy⟩ := lTensor_directLimit_exists
    (fun i j h => (symmetricAlgebraMap (vH i j h)).toLinearMap) L
    ((TensorProduct.congr (LinearEquiv.refl B L)
      (symmetricAlgebraDirectLimitEquiv vH)).symm x)
  refine ⟨i, y, ?_⟩
  rw [← symmetricAlgebraDirectLimit_lTensor vH L i y, hy, LinearEquiv.apply_symm_apply]

/-- An element of `L ⊗ Sym(Hᵢ)` dying in `L ⊗ Sym(colim Hᵢ)` already dies in some
`L ⊗ Sym(Hⱼ)`. -/
public lemma relSymKoszul_directLimit_zero (vH : (i j : ι) → i ≤ j → H i →ₗ[B] H j)
    [DirectedSystem H (fun i j h => vH i j h)] (L : Type*) [AddCommGroup L] [Module B L]
    (i : ι) (x : L ⊗[B] SymmetricAlgebra B (H i))
    (hx : ((symmetricAlgebraMap
      (Module.DirectLimit.of B ι H vH i)).toLinearMap.lTensor L) x = 0) :
    ∃ j, ∃ hij : i ≤ j,
      ((symmetricAlgebraMap (vH i j hij)).toLinearMap.lTensor L) x = 0 := by
  have hds := symmetricAlgebra_directedSystem vH
  have h0 : ((Module.DirectLimit.of B ι (fun i => SymmetricAlgebra B (H i))
      (fun i j h => (symmetricAlgebraMap (vH i j h)).toLinearMap) i).lTensor L) x = 0 := by
    apply (TensorProduct.congr (LinearEquiv.refl B L)
      (symmetricAlgebraDirectLimitEquiv vH)).injective
    rw [symmetricAlgebraDirectLimit_lTensor vH L i x, hx, map_zero]
  exact lTensor_directLimit_zero
    (fun i j h => (symmetricAlgebraMap (vH i j h)).toLinearMap) L i x h0

/-- Composition of the maps induced on symmetric algebras, after tensoring with a fixed
module. -/
public lemma symAlgLTensor_comp (L : Type*) [AddCommGroup L] [Module B L]
    {M N P : Type*} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    [AddCommGroup P] [Module B P] (a : M →ₗ[B] N) (b : N →ₗ[B] P) :
    ((symmetricAlgebraMap b).toLinearMap.lTensor L).comp
        ((symmetricAlgebraMap a).toLinearMap.lTensor L) =
      (symmetricAlgebraMap (b.comp a)).toLinearMap.lTensor L := by
  rw [← LinearMap.lTensor_comp, ← symmetricAlgebraMap_comp, AlgHom.comp_toLinearMap]

/-- **Passage to a filtered colimit.** If the ungraded relative Koszul complex is exact for
every member of a directed system of maps out of a fixed module `A`, it is exact for the
induced map to the colimit. -/
public lemma relSymKoszul_exact_directLimit (vH : (i j : ι) → i ≤ j → H i →ₗ[B] H j)
    [DirectedSystem H (fun i j h => vH i j h)] (uu : (i : ι) → A →ₗ[B] H i)
    (hu : ∀ (i j : ι) (h : i ≤ j), (vH i j h).comp (uu i) = uu j)
    (U : A →ₗ[B] Module.DirectLimit H vH)
    (hU : ∀ i, (Module.DirectLimit.of B ι H vH i).comp (uu i) = U) (p : ℕ)
    (hex : ∀ i, Function.Exact (relSymKoszulDifferential (uu i) (p + 1))
      (relSymKoszulDifferential (uu i) p)) :
    Function.Exact (relSymKoszulDifferential U (p + 1)) (relSymKoszulDifferential U p) := by
  intro x
  constructor
  · intro hx
    obtain ⟨i, y, hy⟩ := relSymKoszul_directLimit_exists vH (⋀[B]^(p + 1) A) x
    have hz : ((symmetricAlgebraMap (Module.DirectLimit.of B ι H vH i)).toLinearMap.lTensor
        (⋀[B]^p A)) (relSymKoszulDifferential (uu i) p y) = 0 := by
      rw [← LinearMap.comp_apply, relSymKoszulDifferential_naturality, hU i,
        LinearMap.comp_apply, hy, hx]
    obtain ⟨j, hij, hj⟩ := relSymKoszul_directLimit_zero vH (⋀[B]^p A) i _ hz
    have hj' : relSymKoszulDifferential (uu j) p
        (((symmetricAlgebraMap (vH i j hij)).toLinearMap.lTensor (⋀[B]^(p + 1) A)) y) = 0 := by
      rwa [← LinearMap.comp_apply, relSymKoszulDifferential_naturality, hu i j hij,
        LinearMap.comp_apply] at hj
    obtain ⟨z, hz'⟩ := (hex j _).mp hj'
    refine ⟨((symmetricAlgebraMap
      (Module.DirectLimit.of B ι H vH j)).toLinearMap.lTensor (⋀[B]^(p + 1 + 1) A)) z, ?_⟩
    rw [← LinearMap.comp_apply, ← hU j, ← relSymKoszulDifferential_naturality,
      LinearMap.comp_apply, hz', ← LinearMap.comp_apply, symAlgLTensor_comp,
      directLimit_of_comp, hy]
  · rintro ⟨z, rfl⟩
    exact LinearMap.congr_fun (relSymKoszulDifferential_comp U p) z

end KoszulColimit

/-! ## The pullback of a surjection along a filtered colimit -/

section Pullback

variable {B A M : Type*} [CommRing B] [AddCommGroup A] [Module B A]
  [AddCommGroup M] [Module B M]
  {ι : Type*} [Preorder ι] [DecidableEq ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  {G : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, Module B (G i)]
  (fG : (i j : ι) → i ≤ j → G i →ₗ[B] G j) (g : M →ₗ[B] Module.DirectLimit G fG)

/-- The pullback `M ×_{colim G} Gᵢ`, as a submodule of `M × Gᵢ`. -/
public def pullbackSub (i : ι) : Submodule B (M × G i) :=
  LinearMap.ker (g.comp (LinearMap.fst B M (G i)) -
    (Module.DirectLimit.of B ι G fG i).comp (LinearMap.snd B M (G i)))

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
/-- Membership in the pullback submodule. -/
public lemma mem_pullbackSub (i : ι) (z : M × G i) :
    z ∈ pullbackSub fG g i ↔ g z.1 = Module.DirectLimit.of B ι G fG i z.2 := by
  simp [pullbackSub, sub_eq_zero]

/-- The projection of the pullback to `M`. -/
public def pullbackFst (i : ι) : pullbackSub fG g i →ₗ[B] M :=
  (LinearMap.fst B M (G i)).comp (pullbackSub fG g i).subtype

/-- The projection of the pullback to `Gᵢ`. -/
public def pullbackSnd (i : ι) : pullbackSub fG g i →ₗ[B] G i :=
  (LinearMap.snd B M (G i)).comp (pullbackSub fG g i).subtype

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
/-- The projection of the pullback to `Gᵢ` is surjective when `g` is. -/
public lemma pullbackSnd_surjective (hg : Function.Surjective g) (i : ι) :
    Function.Surjective (pullbackSnd fG g i) := by
  intro y
  obtain ⟨x, hx⟩ := hg (Module.DirectLimit.of B ι G fG i y)
  exact ⟨⟨(x, y), (mem_pullbackSub fG g i (x, y)).mpr hx⟩, rfl⟩

/-- The map `A → M ×_{colim G} Gᵢ` induced by a map `A → M` killed by `g`. -/
public def pullbackIncl (f : A →ₗ[B] M) (hgf : ∀ a, g (f a) = 0) (i : ι) :
    A →ₗ[B] pullbackSub fG g i :=
  LinearMap.codRestrict _ ((LinearMap.inl B M (G i)).comp f)
    (fun a => (mem_pullbackSub fG g i _).mpr (by simpa using hgf a))

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
/-- The map `A → M ×_{colim G} Gᵢ` is injective when `A → M` is. -/
public lemma pullbackIncl_injective (f : A →ₗ[B] M) (hgf : ∀ a, g (f a) = 0)
    (hf : Function.Injective f) (i : ι) :
    Function.Injective (pullbackIncl fG g f hgf i) :=
  fun _ _ hab => hf (congrArg Prod.fst (congrArg Subtype.val hab))

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
/-- The sequence `0 → A → M ×_{colim G} Gᵢ → Gᵢ → 0` is exact in the middle. -/
public lemma pullbackExact (f : A →ₗ[B] M) (hgf : ∀ a, g (f a) = 0)
    (hfg : Function.Exact f g) (i : ι) :
    Function.Exact (pullbackIncl fG g f hgf i) (pullbackSnd fG g i) := by
  intro z
  constructor
  · intro hz
    have hz2 : (z : M × G i).2 = 0 := hz
    have hg0 : g (z : M × G i).1 = 0 := by
      rw [(mem_pullbackSub fG g i _).mp z.2, hz2, map_zero]
    obtain ⟨a, ha⟩ := (hfg _).mp hg0
    refine ⟨a, ?_⟩
    apply Subtype.ext
    show (f a, (0 : G i)) = (z : M × G i)
    rw [ha, ← hz2]
  · rintro ⟨a, rfl⟩
    rfl

/-- The transition maps of the directed system of pullbacks. -/
public def pullbackTrans (i j : ι) (hij : i ≤ j) :
    pullbackSub fG g i →ₗ[B] pullbackSub fG g j :=
  LinearMap.codRestrict _
    ((pullbackFst fG g i).prod ((fG i j hij).comp (pullbackSnd fG g i)))
    (fun z => by
      rw [mem_pullbackSub]
      change g (pullbackFst fG g i z) =
        Module.DirectLimit.of B ι G fG j (fG i j hij (pullbackSnd fG g i z))
      rw [Module.DirectLimit.of_f]
      exact (mem_pullbackSub fG g i z.1).mp z.2)

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
/-- The pullbacks form a directed system. -/
public lemma pullback_directedSystem [DirectedSystem G (fun i j h => fG i j h)] :
    DirectedSystem (fun i => pullbackSub fG g i)
      (fun i j h => pullbackTrans fG g i j h) := by
  constructor
  · intro i z
    apply Subtype.ext
    show ((z : M × G i).1, fG i i le_rfl (z : M × G i).2) = (z : M × G i)
    rw [DirectedSystem.map_self (f := fun i j h => fG i j h)]
  · intro k j i hij hjk z
    apply Subtype.ext
    show ((z : M × G i).1, fG j k hjk (fG i j hij (z : M × G i).2)) =
      ((z : M × G i).1, fG i k (hij.trans hjk) (z : M × G i).2)
    rw [DirectedSystem.map_map (f := fun i j h => fG i j h)]

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
/-- The transition maps of the pullback system are compatible with the maps out of `A`. -/
public lemma pullbackTrans_pullbackIncl (f : A →ₗ[B] M) (hgf : ∀ a, g (f a) = 0)
    (i j : ι) (hij : i ≤ j) :
    (pullbackTrans fG g i j hij).comp (pullbackIncl fG g f hgf i) =
      pullbackIncl fG g f hgf j :=
  LinearMap.ext fun _ => Subtype.ext <| Prod.ext rfl (map_zero (fG i j hij))

end Pullback

/-! ## Exactness of the ungraded relative Koszul complex -/

section General

/-- **The general case, for a presented quotient.** If `A` is flat and the quotient of `M` by
`A` is written as a filtered colimit of free modules, the ungraded relative Koszul complex of
`f` is exact. -/
public lemma relSymKoszul_exact_of_directLimit_quotient {B A M : Type u} [CommRing B]
    [AddCommGroup A] [Module B A] [AddCommGroup M] [Module B M] [Module.Flat B A]
    {ι : Type u} [Preorder ι] [DecidableEq ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {G : ι → Type u} [∀ i, AddCommGroup (G i)] [∀ i, Module B (G i)]
    (fG : (i j : ι) → i ≤ j → G i →ₗ[B] G j) [DirectedSystem G (fun i j h => fG i j h)]
    (hfree : ∀ i, Module.Free B (G i)) (f : A →ₗ[B] M)
    (g : M →ₗ[B] Module.DirectLimit G fG) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (p : ℕ) :
    Function.Exact (relSymKoszulDifferential f (p + 1)) (relSymKoszulDifferential f p) := by
  have hgf : ∀ a, g (f a) = 0 := fun a => (hfg (f a)).mpr ⟨a, rfl⟩
  have hpds := pullback_directedSystem fG g
  have hc : ∀ (i j : ι) (h : i ≤ j) (x : pullbackSub fG g i),
      pullbackFst fG g j (pullbackTrans fG g i j h x) = pullbackFst fG g i x :=
    fun _ _ _ _ => rfl
  have hsurj : ∀ x : M, ∃ i y, pullbackFst fG g i y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := Module.DirectLimit.exists_of (g x)
    exact ⟨i, ⟨(x, y), (mem_pullbackSub fG g i (x, y)).mpr hy.symm⟩, rfl⟩
  have hzero : ∀ (i : ι) (y : pullbackSub fG g i), pullbackFst fG g i y = 0 →
      ∃ j, ∃ hij : i ≤ j, pullbackTrans fG g i j hij y = 0 := by
    intro i y hy
    have h1 : (y : M × G i).1 = 0 := hy
    have h2 : Module.DirectLimit.of B ι G fG i (y : M × G i).2 = 0 := by
      rw [← (mem_pullbackSub fG g i _).mp y.2, h1, map_zero]
    obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact h2
    refine ⟨j, hij, ?_⟩
    apply Subtype.ext
    show ((y : M × G i).1, fG i j hij (y : M × G i).2) = (0 : M × G j)
    rw [h1, hj]
    rfl
  obtain ⟨E, hEof⟩ : ∃ E : Module.DirectLimit (fun i => pullbackSub fG g i)
      (fun i j h => pullbackTrans fG g i j h) ≃ₗ[B] M,
      ∀ (i : ι) (x : pullbackSub fG g i),
        E (Module.DirectLimit.of B ι (fun i => pullbackSub fG g i)
          (fun i j h => pullbackTrans fG g i j h) i x) = pullbackFst fG g i x :=
    ⟨directLimitEquivOfRepresentation (fun i j h => pullbackTrans fG g i j h)
        (fun i => pullbackFst fG g i) hc hsurj hzero,
      fun i x => directLimitEquivOfRepresentation_of
        (fun i j h => pullbackTrans fG g i j h) (fun i => pullbackFst fG g i) hc hsurj hzero i x⟩
  apply relSymKoszul_exact_of_equiv f E.symm p
  refine relSymKoszul_exact_directLimit (fun i j h => pullbackTrans fG g i j h)
    (fun i => pullbackIncl fG g f hgf i)
    (fun i j h => pullbackTrans_pullbackIncl fG g f hgf i j h)
    (E.symm.toLinearMap.comp f) ?_ p ?_
  · intro i
    ext a
    apply E.injective
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, E.apply_symm_apply,
      hEof]
    rfl
  · intro i
    have hfreei := hfree i
    obtain ⟨t, ht⟩ := Module.projective_lifting_property (pullbackSnd fG g i)
      (LinearMap.id : G i →ₗ[B] G i) (pullbackSnd_surjective fG g hg i)
    exact relSymKoszul_exact_of_splitting (pullbackIncl fG g f hgf i) (pullbackSnd fG g i)
      (pullbackIncl_injective fG g f hgf hf i) (pullbackExact fG g f hgf hfg i) t ht p

/-- **Exactness of the ungraded relative Koszul complex.** For a short exact sequence
`0 → A → M → Q → 0` with `A` and `Q` flat, the complex
`⋯ → (⋀^{p+1}A) ⊗ Sym(M) → (⋀^p A) ⊗ Sym(M) → ⋯` is exact. -/
public lemma relSymKoszul_exact {B A M Q : Type u} [CommRing B] [AddCommGroup A] [Module B A]
    [AddCommGroup M] [Module B M] [AddCommGroup Q] [Module B Q] [Module.Flat B A]
    [Module.Flat B Q] (f : A →ₗ[B] M) (g : M →ₗ[B] Q) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (p : ℕ) :
    Function.Exact (relSymKoszulDifferential f (p + 1)) (relSymKoszulDifferential f p) := by
  obtain ⟨ι, hpre, hdir, hne, hdec, G, hag, hmod, fG, hds, hfree, -, ⟨eQ⟩⟩ :=
    flat_exists_directLimit_finiteFree B Q
  refine relSymKoszul_exact_of_directLimit_quotient fG hfree f (eQ.symm.toLinearMap.comp g) hf
    (fun x => Iff.trans (map_eq_zero_iff eQ.symm.toLinearMap eQ.symm.injective) (hfg x))
    (eQ.symm.surjective.comp hg) p

end General

/-! ## The graded relative Koszul complex -/

section Graded

variable {B A M : Type*} [CommRing B] [AddCommGroup A] [Module B A]
  [AddCommGroup M] [Module B M]

/-- The graded relative Koszul differential squares to zero. -/
public lemma relKoszul_comp (f : A →ₗ[B] M) (p q : ℕ) :
    (koszulDifferential (symMulMapBil (q + 1) f) p).comp
      (koszulDifferential (symMulMapBil q f) (p + 1)) = 0 := by
  apply koszulDifferential_comp
  intro x y z
  apply Subtype.ext
  show SymmetricAlgebra.ι B M (f y) *
      (SymmetricAlgebra.ι B M (f x) * (z : SymmetricAlgebra B M)) =
    SymmetricAlgebra.ι B M (f x) * (SymmetricAlgebra.ι B M (f y) * (z : SymmetricAlgebra B M))
  exact mul_left_comm _ _ _

/-- The graded relative Koszul differential is the restriction of the ungraded one. -/
public lemma relKoszul_subtype (f : A →ₗ[B] M) (p q : ℕ) :
    ((symmetricPower (q + 1) B M).subtype.lTensor (⋀[B]^p A)).comp
        (koszulDifferential (symMulMapBil q f) p) =
      (relSymKoszulDifferential f p).comp
        ((symmetricPower q B M).subtype.lTensor (⋀[B]^(p + 1) A)) := by
  simpa only [exteriorPower.map_id, relSymKoszulDifferential, LinearMap.lTensor_def] using
    koszulDifferential_naturality (symMulMapBil q f) (relSymKoszulAction f) LinearMap.id
      (symmetricPower q B M).subtype (symmetricPower (q + 1) B M).subtype (fun _ _ => rfl) p

/-- The ungraded relative Koszul differential is compatible with the projections onto the
graded pieces of the symmetric algebra. -/
public lemma relKoszul_projection (f : A →ₗ[B] M) (p q : ℕ) :
    ((symmetricPowerProjection B M (q + 1)).lTensor (⋀[B]^p A)).comp
        (relSymKoszulDifferential f p) =
      (koszulDifferential (symMulMapBil q f) p).comp
        ((symmetricPowerProjection B M q).lTensor (⋀[B]^(p + 1) A)) := by
  simpa only [exteriorPower.map_id, relSymKoszulDifferential, LinearMap.lTensor_def] using
    koszulDifferential_naturality (relSymKoszulAction f) (symMulMapBil q f) LinearMap.id
      (symmetricPowerProjection B M q) (symmetricPowerProjection B M (q + 1))
      (fun x z => symmetricPowerProjection_mul_ι B M q (f x) z) p

/-- A cycle of the graded relative Koszul differential is a cycle of the ungraded one. -/
private theorem relSymKoszulDifferential_subtype_eq_zero (f : A →ₗ[B] M) (p q : ℕ)
    (x : (⋀[B]^(p + 1) A) ⊗[B] symmetricPower q B M)
    (hx : koszulDifferential (symMulMapBil q f) p x = 0) :
    relSymKoszulDifferential f p
      ((symmetricPower q B M).subtype.lTensor (⋀[B]^(p + 1) A) x) = 0 := by
  rw [← LinearMap.comp_apply, ← relKoszul_subtype, LinearMap.comp_apply, hx, map_zero]

/-- Projecting to the `q`-th symmetric power undoes the inclusion, after tensoring with `L`. -/
private theorem lTensor_projection_lTensor_subtype (L : Type*) [AddCommGroup L] [Module B L]
    (q : ℕ) (x : L ⊗[B] symmetricPower q B M) :
    (symmetricPowerProjection B M q).lTensor L
      ((symmetricPower q B M).subtype.lTensor L x) = x := by
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, symmetricPowerProjection_subtype,
    LinearMap.lTensor_id, LinearMap.id_apply]

/-- Exactness of the graded relative Koszul complex follows from exactness of the ungraded
one. -/
public lemma relKoszul_exact_of_relSymKoszul_exact (f : A →ₗ[B] M) (p q : ℕ)
    (h : Function.Exact (relSymKoszulDifferential f (p + 1)) (relSymKoszulDifferential f p)) :
    Function.Exact (koszulDifferential (symMulMapBil q f) (p + 1))
      (koszulDifferential (symMulMapBil (q + 1) f) p) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (h _).mp (relSymKoszulDifferential_subtype_eq_zero f p _ x hx)
    refine ⟨(symmetricPowerProjection B M q).lTensor (⋀[B]^(p + 1 + 1) A) y, ?_⟩
    show ((koszulDifferential (symMulMapBil q f) (p + 1)).comp
      ((symmetricPowerProjection B M q).lTensor (⋀[B]^(p + 1 + 1) A))) y = x
    rw [← relKoszul_projection, LinearMap.comp_apply, hy, lTensor_projection_lTensor_subtype]
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (relKoszul_comp f p q) y

/-- Multiplying by a degree-one element kills the component in symmetric degree zero. -/
public lemma symmetricPowerProjection_zero_mul_ι (x : M) (z : SymmetricAlgebra B M) :
    symmetricPowerProjection B M 0 (SymmetricAlgebra.ι B M x * z) = 0 := by
  apply Subtype.ext
  show (degreeMap (SymmetricAlgebra.ι B M x * z)).coeff 0 = 0
  rw [map_mul, degreeMap_ι]
  simp [Polynomial.mul_coeff_zero]

/-- The ungraded relative Koszul differential raises the symmetric degree, so its composite
with the projection to symmetric degree zero vanishes. -/
public lemma relSymKoszul_projection_zero (f : A →ₗ[B] M) (p : ℕ) :
    ((symmetricPowerProjection B M 0).lTensor (⋀[B]^p A)).comp
      (relSymKoszulDifferential f p) = 0 := by
  apply TensorProduct.ext
  apply exteriorPower.linearMap_ext (R := B) (M := A)
    (N := SymmetricAlgebra B M →ₗ[B] ((⋀[B]^p A) ⊗[B] symmetricPower 0 B M))
  ext v z
  show ((symmetricPowerProjection B M 0).lTensor (⋀[B]^p A))
    (relSymKoszulDifferential f p (exteriorPower.ιMulti B (p + 1) v ⊗ₜ[B] z)) = 0
  rw [relSymKoszulDifferential, koszulDifferential_tmul, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_zsmul, LinearMap.lTensor_tmul,
    show relSymKoszulAction f (v i) z = SymmetricAlgebra.ι B M (f (v i)) * z from rfl,
    symmetricPowerProjection_zero_mul_ι, TensorProduct.tmul_zero, smul_zero]

/-- **Injectivity at the top.** The leftmost map of the graded relative Koszul complex is
injective as soon as the ungraded complex is exact. -/
public lemma relKoszul_injective_zero (f : A →ₗ[B] M) (p : ℕ)
    (h : Function.Exact (relSymKoszulDifferential f (p + 1)) (relSymKoszulDifferential f p)) :
    Function.Injective (koszulDifferential (symMulMapBil 0 f) p) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨Y, hY⟩ := (h _).mp (relSymKoszulDifferential_subtype_eq_zero f p 0 x hx)
  have h0 : ((symmetricPowerProjection B M 0).lTensor (⋀[B]^(p + 1) A))
      ((symmetricPower 0 B M).subtype.lTensor (⋀[B]^(p + 1) A) x) = 0 := by
    rw [← hY, ← LinearMap.comp_apply, relSymKoszul_projection_zero, LinearMap.zero_apply]
  rwa [lTensor_projection_lTensor_subtype] at h0

end Graded

/-! ## The bottom of the complex -/

section Bottom

/-- The identification `(⋀^0 A) ⊗ Symᵏ(M) ≃ Symᵏ(M)`. -/
public def relKoszulZeroIso (B A M : Type*) [CommRing B] [AddCommGroup A] [Module B A]
    [AddCommGroup M] [Module B M] (q : ℕ) :
    ((⋀[B]^0 A) ⊗[B] symmetricPower q B M) ≃ₗ[B] symmetricPower q B M :=
  (TensorProduct.congr (exteriorPower.zeroEquiv B A) (LinearEquiv.refl B _)).trans
    (TensorProduct.lid B _)

/-- `relKoszulZeroIso` on a pure tensor. -/
public lemma relKoszulZeroIso_tmul (B A M : Type*) [CommRing B] [AddCommGroup A] [Module B A]
    [AddCommGroup M] [Module B M] (q : ℕ) (x : ⋀[B]^0 A) (y : symmetricPower q B M) :
    relKoszulZeroIso B A M q (x ⊗ₜ[B] y) = exteriorPower.zeroEquiv B A x • y := by
  simp [relKoszulZeroIso]

variable {B A M Q : Type*} [CommRing B] [AddCommGroup A] [Module B A]
  [AddCommGroup M] [Module B M] [AddCommGroup Q] [Module B Q]

/-- At `p = 0` the relative Koszul differential is the multiplication map of the presentation
of symmetric powers. -/
public lemma relKoszulZeroIso_differential (f : A →ₗ[B] M) (q : ℕ) :
    (relKoszulZeroIso B A M (q + 1)).toLinearMap.comp
        (koszulDifferential (symMulMapBil q f) 0) =
      (symMulMap q f).comp
        (TensorProduct.congr (exteriorPower.oneEquiv B A)
          (LinearEquiv.refl B (symmetricPower q B M))).toLinearMap := by
  apply TensorProduct.ext
  apply LinearMap.ext_on (exteriorPower.ιMulti_span B (0 + 1) A)
  rintro _ ⟨v, rfl⟩
  apply LinearMap.ext
  intro z
  show (relKoszulZeroIso B A M (q + 1))
      (koszulDifferential (symMulMapBil q f) 0
        (exteriorPower.ιMulti B (0 + 1) v ⊗ₜ[B] z)) =
    symMulMap q f ((TensorProduct.congr (exteriorPower.oneEquiv B A)
      (LinearEquiv.refl B (symmetricPower q B M))) (exteriorPower.ιMulti B (0 + 1) v ⊗ₜ[B] z))
  rw [koszulDifferential_tmul]
  simp [relKoszulZeroIso, exteriorPower.zeroEquiv_ιMulti, exteriorPower.oneEquiv_ιMulti,
    symMulMap, symMulMapBil]

/-- **Exactness at the bottom.** The relative Koszul complex ends in `Symᵏ(Q)`. -/
public lemma relKoszul_exact_zero (f : A →ₗ[B] M) (g : M →ₗ[B] Q)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (q : ℕ) :
    Function.Exact (koszulDifferential (symMulMapBil q f) 0)
      ((symMap (q + 1) g).comp (relKoszulZeroIso B A M (q + 1)).toLinearMap) := by
  have hpres := (symmetric_power_presentation f g hg (LinearMap.exact_iff.mp hfg).symm q).2
  have hex : Function.Exact (symMulMap q f) (symMap (q + 1) g) :=
    LinearMap.exact_iff.mpr hpres.symm
  apply (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := TensorProduct.congr (exteriorPower.oneEquiv B A)
      (LinearEquiv.refl B (symmetricPower q B M)))
    (e₂ := relKoszulZeroIso B A M (q + 1))
    (e₃ := LinearEquiv.refl B (symmetricPower (q + 1) B Q))
    (f₁₂ := koszulDifferential (symMulMapBil q f) 0)
    (f₂₃ := (symMap (q + 1) g).comp (relKoszulZeroIso B A M (q + 1)).toLinearMap)
    (g₁₂ := symMulMap q f) (g₂₃ := symMap (q + 1) g) ?_ ?_).mp hex
  · exact (relKoszulZeroIso_differential f q).symm
  · exact (LinearMap.id_comp _).symm

end Bottom

/-! ## The three statements -/

section Main

variable {B A M Q : Type u} [CommRing B] [AddCommGroup A] [Module B A]
  [AddCommGroup M] [Module B M] [AddCommGroup Q] [Module B Q]
  [Module.Flat B A] [Module.Flat B M] [Module.Flat B Q]
  (f : A →ₗ[B] M) (g : M →ₗ[B] Q) (hf : Function.Injective f) (hfg : Function.Exact f g)
  (hg : Function.Surjective g)

include g hf hfg hg

omit [Module.Flat B M] in
/-- **Exactness of the relative Koszul complex.** For a short exact sequence
`0 → A --f--> M --g--> Q → 0` of flat `B`-modules the relative Koszul complex
`⋯ → (⋀^{p+2}A) ⊗ Symᵍ(M) → (⋀^{p+1}A) ⊗ Sym^{q+1}(M) → (⋀^p A) ⊗ Sym^{q+2}(M) → ⋯`
is exact. -/
public theorem relativeKoszul_exact :
    ∀ p q : ℕ, Function.Exact (koszulDifferential (symMulMapBil q f) (p + 1))
      (koszulDifferential (symMulMapBil (q + 1) f) p) :=
  fun p q => relKoszul_exact_of_relSymKoszul_exact f p q
    (relSymKoszul_exact f g hf hfg hg p)

omit [Module.Flat B M] in
/-- **Injectivity at the top of the relative Koszul complex.** The map
`(⋀^{p+1}A) ⊗ Sym⁰(M) → (⋀^p A) ⊗ Sym¹(M)` is injective. -/
public theorem relativeKoszul_injective :
    ∀ p : ℕ, Function.Injective (koszulDifferential (symMulMapBil 0 f) p) :=
  fun p => relKoszul_injective_zero f p (relSymKoszul_exact f g hf hfg hg p)

omit [Module.Flat B A] [Module.Flat B M] [Module.Flat B Q] in
/-- **Exactness at the bottom of the relative Koszul complex.** The complex ends with
`(⋀^1 A) ⊗ Symᵍ(M) → (⋀^0 A) ⊗ Sym^{q+1}(M) → Sym^{q+1}(Q) → 0`. -/
public theorem relativeKoszul_exact_zero :
    ∀ q : ℕ, Function.Exact (koszulDifferential (symMulMapBil q f) 0)
      ((symMap (q + 1) g).comp (relKoszulZeroIso B A M (q + 1)).toLinearMap) :=
  fun q => relKoszul_exact_zero f g hfg hg q

end Main

end SymPow

end
