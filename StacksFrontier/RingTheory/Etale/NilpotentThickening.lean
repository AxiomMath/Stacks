module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksCore.RingTheory.Nakayama
public import StacksFrontier.RingTheory.Etale.Basic

/-!
# Étale algebras and base change across a square-zero thickening

* A homomorphism of formally étale algebras which is bijective modulo a nilpotent ideal of the
  base is bijective: it is surjective by the nilpotent Nakayama lemma, and its kernel, being
  nilpotent, is split off by a lift of the identity which formal unramifiedness makes inverse.
* Let `A' → A` and `B' → B` be surjective ring maps with kernels `I` and `J`, `I ^ 2 = 0`, over a
  commutative square.  If `J`, read as a `B`-module `M`, is the base change along `A → B` of an
  `A`-module `N` identified with `I`, then `J` is the base change of `I` along `A' → B'`.  This
  is the hypothesis `J = I ⊗_A B` of Stacks 05YT.

## Main definitions

* `kerRestrict`

## Main results

* `AlgHom.bijective_of_formallyEtale_of_isNilpotent`
* `isBaseChange_ker_of_isBaseChange`
* `isBaseChange_ker_of_isBaseChange_of_glue`
* `bijective_lift_of_isNilpotent`
* `etale_and_bijective_lift_of_isBaseChange`

## References

* [Stacks Project, Tag 05YT](https://stacks.math.columbia.edu/tag/05YT)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public section

open TensorProduct

/-- **A homomorphism of formally étale algebras which is bijective modulo a nilpotent ideal of
the base is bijective.**  Let `φ : E₁ → E₂` be a homomorphism of `R`-algebras, `E₁` formally
unramified and `E₂` formally smooth over `R`, and `I ⊆ R` a nilpotent ideal.  If every element of
`E₂` is congruent to a value of `φ` modulo `I E₂` and the kernel of `φ` lies in `I E₁`, then `φ`
is bijective. -/
theorem AlgHom.bijective_of_formallyEtale_of_isNilpotent {R E₁ E₂ : Type*} [CommRing R]
    [CommRing E₁] [CommRing E₂] [Algebra R E₁] [Algebra R E₂]
    [Algebra.FormallyUnramified R E₁] [Algebra.FormallySmooth R E₂]
    (I : Ideal R) (hI : IsNilpotent I) (φ : E₁ →ₐ[R] E₂)
    (hsurj : ∀ y : E₂, ∃ x : E₁, y - φ x ∈ I.map (algebraMap R E₂))
    (hker : RingHom.ker (φ : E₁ →+* E₂) ≤ I.map (algebraMap R E₁)) :
    Function.Bijective φ := by
  have hφs : Function.Surjective φ := by
    refine LinearMap.surjective_of_surjective_comp_mkQ_of_isNilpotent I φ.toLinearMap hI fun y ↦ ?_
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨x, hx⟩ := hsurj y'
    refine ⟨x, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      AlgHom.toLinearMap_apply]
    rw [Submodule.Quotient.eq, Ideal.smul_top_eq_map, ← neg_sub]
    exact neg_mem hx
  have hnil : IsNilpotent (RingHom.ker (φ : E₁ →+* E₂)) := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, eq_bot_iff.2 ?_⟩
    calc RingHom.ker (φ : E₁ →+* E₂) ^ n ≤ (I.map (algebraMap R E₁)) ^ n :=
          Ideal.pow_right_mono hker n
      _ = (I ^ n).map (algebraMap R E₁) := (Ideal.map_pow _ _ _).symm
      _ = ⊥ := by rw [hn, Ideal.zero_eq_bot, Ideal.map_bot]
  let σ : E₂ →ₐ[R] E₁ := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R E₂) φ hφs hnil
  have hσφ : σ.comp φ = AlgHom.id R E₁ :=
    Algebra.FormallyUnramified.ext' (φ : E₁ →+* E₂) hnil _ _ fun x ↦
      Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id R E₂) φ hφs hnil (φ x)
  exact ⟨Function.LeftInverse.injective (g := σ) (DFunLike.congr_fun hσφ), hφs⟩

/-- If `A' → B'` is injective, maps `I` into `J` and `J ^ 2 = 0`, then `I ^ 2 = 0`. -/
private theorem sq_eq_bot_of_injective_of_map_mem {A' B' : Type*} [CommRing A'] [CommRing B']
    [Algebra A' B'] {I : Ideal A'} {J : Ideal B'} (hinj : Function.Injective (algebraMap A' B'))
    (hIJ : ∀ x ∈ I, algebraMap A' B' x ∈ J) (hJ : J ^ 2 = ⊥) : I ^ 2 = ⊥ := by
  rw [eq_bot_iff, sq]
  refine Ideal.mul_le.2 fun x hx y hy ↦ ?_
  rw [Ideal.mem_bot]
  apply hinj
  rw [map_mul, map_zero]
  have : algebraMap A' B' x * algebraMap A' B' y ∈ J ^ 2 := by
    rw [sq]; exact Ideal.mul_mem_mul (hIJ x hx) (hIJ y hy)
  rwa [hJ, Ideal.mem_bot] at this

section BaseChange

variable {A' A B' B : Type*} [CommRing A'] [CommRing A] [CommRing B'] [CommRing B]
  [Algebra A' A] [Algebra A' B'] [Algebra A' B] [Algebra A B] [Algebra B' B]
  [IsScalarTower A' A B] [IsScalarTower A' B' B]
  {N M : Type*} [AddCommGroup N] [Module A' N] [Module A N] [IsScalarTower A' A N]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- **`J = I ⊗_A B` from a base change of sections.**  Let `A' → A` and `B' → B` be surjective
with kernels `I` and `J`, over a commutative square, with `I ^ 2 = 0`.  Let `res : N → M` exhibit
the `B`-module `M` as the base change of the `A`-module `N` along `A → B`, let `ρ : N ≃ I` be
additive and `A'`-linear for the action of `A'` on `N` through `A`, and let `Φ : J ≃ M` be
additive and `B'`-linear for the action of `B'` on `M` through `B`, with `Φ ∘ f ∘ ρ = res` for
the map `f : I → J` induced by `A' → B'`.  Then `f` exhibits `J` as the base change of `I` along
`A' → B'`. -/
theorem isBaseChange_ker_of_isBaseChange
    (hA : Function.Surjective (algebraMap A' A)) (hB : Function.Surjective (algebraMap B' B))
    (_hI : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (f : RingHom.ker (algebraMap A' A) →ₗ[A'] RingHom.ker (algebraMap B' B))
    (hf : ∀ x, (f x : B') = algebraMap A' B' (x : A'))
    (res : N →ₗ[A] M) (hres : IsBaseChange B res)
    (ρ : N ≃ₗ[A'] RingHom.ker (algebraMap A' A))
    (Φ : RingHom.ker (algebraMap B' B) ≃+ M)
    (hΦ : ∀ (b : B') (j : RingHom.ker (algebraMap B' B)), Φ (b • j) = algebraMap B' B b • Φ j)
    (hcomp : ∀ n, Φ (f (ρ n)) = res n) :
    IsBaseChange B' f := by
  classical
  let L : B' ⊗[A'] RingHom.ker (algebraMap A' A) →ₗ[B'] RingHom.ker (algebraMap B' B) :=
    f.liftBaseChange B'
  have hL : ∀ (b : B') (i : RingHom.ker (algebraMap A' A)), L (b ⊗ₜ i) = b • f i := fun b i ↦ by
    simp [L, LinearMap.liftBaseChange_tmul]
  have hIN : ∀ (i : RingHom.ker (algebraMap A' A)) (n : N), (i : A') • n = 0 := fun i n ↦ by
    rw [← algebraMap_smul A, show algebraMap A' A i = 0 from i.2, zero_smul]
  have hspan : ∀ (m : M) (j : RingHom.ker (algebraMap B' B)), Φ j = m →
      j ∈ Submodule.span B' (Set.range f) := by
    intro m
    refine hres.inductionOn m ?_ ?_ ?_
    · intro n j hj
      rw [show j = f (ρ n) from Φ.injective (hj.trans (hcomp n).symm)]
      exact Submodule.subset_span ⟨_, rfl⟩
    · intro b m hm j hj
      obtain ⟨b', rfl⟩ := hB b
      obtain ⟨j₀, hj₀⟩ : ∃ j₀, Φ j₀ = m := ⟨Φ.symm m, Φ.apply_symm_apply m⟩
      rw [show j = b' • j₀ from Φ.injective (by rw [hΦ, hj₀, hj])]
      exact Submodule.smul_mem _ _ (hm j₀ hj₀)
    · intro m₁ m₂ h₁ h₂ j hj
      obtain ⟨j₁, hj₁⟩ : ∃ j₁, Φ j₁ = m₁ := ⟨Φ.symm m₁, Φ.apply_symm_apply m₁⟩
      obtain ⟨j₂, hj₂⟩ : ∃ j₂, Φ j₂ = m₂ := ⟨Φ.symm m₂, Φ.apply_symm_apply m₂⟩
      rw [show j = j₁ + j₂ from Φ.injective (by rw [map_add, hj₁, hj₂, hj])]
      exact add_mem (h₁ j₁ hj₁) (h₂ j₂ hj₂)
  have hLsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    intro j _
    refine Submodule.span_le.2 ?_ (hspan _ j rfl)
    rintro _ ⟨i, rfl⟩
    exact ⟨1 ⊗ₜ i, by rw [hL, one_smul]⟩
  have hJN : ∀ (j : RingHom.ker (algebraMap B' B)) (n : N), (j : B') ⊗ₜ[A'] n = 0 := by
    intro j n
    obtain ⟨x, rfl⟩ := hLsurj j
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b i =>
      rw [hL, Submodule.coe_smul, hf, smul_eq_mul, mul_comm, ← Algebra.smul_def, smul_tmul,
        hIN, tmul_zero]
    | add x y hx hy => rw [map_add, Submodule.coe_add, add_tmul, hx, hy, add_zero]
  have : TensorProduct.CompatibleSMul A' A B N := .of_algebraMap_surjective _ _ hA
  let κ₁ : B' ⊗[A'] RingHom.ker (algebraMap A' A) ≃ₗ[A'] B' ⊗[A'] N :=
    LinearEquiv.lTensor B' ρ.symm
  let p : B' →ₗ[A'] B := (IsScalarTower.toAlgHom A' B' B).toLinearMap
  let κ₂ : B' ⊗[A'] N →ₗ[A'] B ⊗[A'] N := LinearMap.rTensor N p
  let κ₃ : B ⊗[A'] N ≃ₗ[A'] B ⊗[A] N := TensorProduct.equivOfCompatibleSMul A A' A' B N
  have hκ₂ : Function.Injective κ₂ := by
    have hex := rTensor_exact N (LinearMap.exact_subtype_ker_map p) hB
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (hex x).1 hx
    clear hx
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul j n => simpa using hJN ⟨j, j.2⟩ n
    | add y z hy hz => rw [map_add, hy, hz, add_zero]
  have hcommute : ∀ x, hres.equiv (κ₃ (κ₂ (κ₁ x))) = Φ (L x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b i =>
      rw [show κ₃ (κ₂ (κ₁ (b ⊗ₜ i))) = algebraMap B' B b ⊗ₜ[A] ρ.symm i from rfl,
        IsBaseChange.equiv_tmul, hL, hΦ, ← hcomp, LinearEquiv.apply_symm_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hLinj : Function.Injective L := fun x y hxy ↦ κ₁.injective
    (hκ₂ (κ₃.injective (hres.equiv.injective (by rw [hcommute, hcommute, hxy]))))
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩) fun i ↦
    (hL 1 i).trans (one_smul B' (f i))

/-- **`J = I ⊗_A B` from gluing of sections.**  Let `A' → B'` be injective, `A' → A` and
`B' → B` surjective with kernels `I` and `J`, over a commutative square, with `A → B` injective
and `J ^ 2 = 0`.  Let `res : N → M` be injective and exhibit the `B`-module `M` as the base change
of the `A`-module `N` along `A → B`, and let `Φ : J ≃ M` be additive and `B'`-linear for the
action of `B'` on `M` through `B`.  If an element `j ∈ J` comes from `A'` exactly when `Φ j` comes
from `N`, then the map `f : I → J` induced by `A' → B'` exhibits `J` as the base change of `I`
along `A' → B'`. -/
theorem isBaseChange_ker_of_isBaseChange_of_glue
    (hinj : Function.Injective (algebraMap A' B')) (hAB : Function.Injective (algebraMap A B))
    (hA : Function.Surjective (algebraMap A' A)) (hB : Function.Surjective (algebraMap B' B))
    (hJ : RingHom.ker (algebraMap B' B) ^ 2 = ⊥)
    (f : RingHom.ker (algebraMap A' A) →ₗ[A'] RingHom.ker (algebraMap B' B))
    (hf : ∀ x, (f x : B') = algebraMap A' B' (x : A'))
    (res : N →ₗ[A] M) (hres : IsBaseChange B res) (hresinj : Function.Injective res)
    (Φ : RingHom.ker (algebraMap B' B) ≃+ M)
    (hΦ : ∀ (b : B') (j : RingHom.ker (algebraMap B' B)), Φ (b • j) = algebraMap B' B b • Φ j)
    (hEq : ∀ j : RingHom.ker (algebraMap B' B),
      (j : B') ∈ (algebraMap A' B').range ↔ ∃ n, res n = Φ j) :
    IsBaseChange B' f := by
  classical
  have hI : RingHom.ker (algebraMap A' A) ^ 2 = ⊥ :=
    sq_eq_bot_of_injective_of_map_mem hinj (fun x hx ↦ hf ⟨x, hx⟩ ▸ (f ⟨x, hx⟩).2) hJ
  have hex : ∀ i : RingHom.ker (algebraMap A' A), ∃ n, res n = Φ (f i) := fun i ↦
    (hEq (f i)).1 ⟨i, (hf i).symm⟩
  let g : RingHom.ker (algebraMap A' A) → N := fun i ↦ (hex i).choose
  have hg : ∀ i, res (g i) = Φ (f i) := fun i ↦ (hex i).choose_spec
  have hfinj : Function.Injective f := fun i i' h ↦
    Subtype.ext (hinj (by rw [← hf, ← hf, h]))
  have hAB' : ∀ a : A', algebraMap A B (algebraMap A' A a) = algebraMap B' B (algebraMap A' B' a) :=
    fun a ↦ by rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  let gl : RingHom.ker (algebraMap A' A) →ₗ[A'] N :=
    { toFun := g
      map_add' := fun i i' ↦ hresinj (by rw [map_add, hg, hg, hg, map_add, map_add])
      map_smul' := fun a i ↦ hresinj (by
        have h1 : f (a • i) = algebraMap A' B' a • f i :=
          (f.map_smul a i).trans (Subtype.ext (Algebra.smul_def a _))
        have h2 : res (a • g i) = algebraMap A' A a • res (g i) := by
          rw [← map_smul, algebraMap_smul]
        rw [RingHom.id_apply, h2, hg, hg, h1, hΦ, ← hAB', algebraMap_smul]) }
  have hglinj : Function.Injective gl := fun i i' h ↦
    hfinj (Φ.injective ((hg i).symm.trans ((congrArg res h).trans (hg i'))))
  have hglsurj : Function.Surjective gl := by
    intro n
    obtain ⟨a, ha⟩ := (hEq (Φ.symm (res n))).2 ⟨n, (Φ.apply_symm_apply _).symm⟩
    have hak : a ∈ RingHom.ker (algebraMap A' A) := by
      rw [RingHom.mem_ker]
      apply hAB
      rw [hAB', ha, map_zero]
      exact (Φ.symm (res n)).2
    refine ⟨⟨a, hak⟩, hresinj ?_⟩
    show res (g _) = res n
    rw [hg, show f ⟨a, hak⟩ = Φ.symm (res n) from Subtype.ext ((hf _).trans ha),
      Φ.apply_symm_apply]
  let e := LinearEquiv.ofBijective gl ⟨hglinj, hglsurj⟩
  refine isBaseChange_ker_of_isBaseChange hA hB hI f hf res hres e.symm Φ hΦ fun n ↦ ?_
  rw [← hg]
  exact congrArg res (e.apply_symm_apply n)

end BaseChange

section Equalizer

variable {R B' C' A B : Type*} [CommRing R] [CommRing B'] [CommRing C'] [CommRing A] [CommRing B]
  [Algebra R B'] [Algebra R C'] [Algebra B' C'] [IsScalarTower R B' C'] [Algebra R A]
  [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- **A pair of étale maps reducing to the two coprojections of `B ⊗_A B` is a tensor
square.**  Let `R → A` be surjective with nilpotent kernel `I`, let `B` be an `A`-algebra and
`p : B' → B` a surjection of `R`-algebras with kernel `I B'`, with `B'` formally étale over `R`,
and let `C'` be a formally smooth `B'`-algebra with a second homomorphism `t : B' → C'` of
`R`-algebras.  If some `ψ : C' → B ⊗_A B` whose kernel lies in `I C'` carries the structure map
and `t` to the two coprojections composed with `p`, then `B' ⊗_R B' → C'`,
`b ⊗ b' ↦ b · t b'`, is bijective. -/
theorem bijective_lift_of_isNilpotent [Algebra.FormallyEtale R B'] [Algebra.FormallySmooth B' C']
    (hA : Function.Surjective (algebraMap R A)) (hI : IsNilpotent (RingHom.ker (algebraMap R A)))
    (p : B' →ₐ[R] B) (hp : Function.Surjective p)
    (hker : RingHom.ker (p : B' →+* B) = (RingHom.ker (algebraMap R A)).map (algebraMap R B'))
    (t : B' →ₐ[R] C') (ψ : C' →ₐ[R] B ⊗[A] B)
    (hψ : RingHom.ker (ψ : C' →+* B ⊗[A] B) ≤
      (RingHom.ker (algebraMap R A)).map (algebraMap R C'))
    (hs : ∀ b, ψ (algebraMap B' C' b) = p b ⊗ₜ 1) (ht : ∀ b, ψ (t b) = 1 ⊗ₜ p b) :
    Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId B' C') t fun _ _ ↦ Commute.all _ _) := by
  classical
  set I := RingHom.ker (algebraMap R A)
  have : TensorProduct.CompatibleSMul R A B B := .of_algebraMap_surjective _ _ hA
  let κ : B ⊗[R] B ≃ₗ[R] B ⊗[A] B := TensorProduct.equivOfCompatibleSMul A R R B B
  let φ := Algebra.TensorProduct.lift (Algebra.ofId B' C') t fun _ _ ↦ Commute.all _ _
  let π : B' ⊗[R] B' →ₐ[R] B ⊗[R] B := Algebra.TensorProduct.map p p
  have hψφ : ∀ x, ψ (φ x) = κ (π x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b b' =>
      have : φ (b ⊗ₜ b') = algebraMap B' C' b * t b' :=
        Algebra.TensorProduct.lift_tmul _ _ _ b b'
      rw [this, map_mul, hs, ht, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hπs : Function.Surjective π := Algebra.TensorProduct.map_surjective p p hp hp
  set 𝔍 : Ideal B' := I.map (algebraMap R B')
  have h𝔍 : IsNilpotent 𝔍 := by
    obtain ⟨n, hn⟩ := hI
    exact ⟨n, by rw [← Ideal.map_pow, hn, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.zero_eq_bot]⟩
  have hC : 𝔍.map (algebraMap B' C') = I.map (algebraMap R C') := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hT : 𝔍.map (algebraMap B' (B' ⊗[R] B')) = I.map (algebraMap R (B' ⊗[R] B')) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine AlgHom.bijective_of_formallyEtale_of_isNilpotent 𝔍 h𝔍 φ (fun y ↦ ?_) ?_
  · obtain ⟨x, hx⟩ := hπs (κ.symm (ψ y))
    refine ⟨x, ?_⟩
    rw [hC]
    refine hψ ?_
    rw [RingHom.mem_ker, map_sub]
    show ψ y - ψ (φ x) = 0
    rw [hψφ, hx, LinearEquiv.apply_symm_apply, sub_self]
  · intro x hx
    rw [hT]
    have h0 : π x = 0 := κ.injective (by rw [← hψφ, show φ x = 0 from hx, map_zero, map_zero])
    have hx' : x ∈ RingHom.ker (Algebra.TensorProduct.map p p) := h0
    rw [Algebra.TensorProduct.map_ker p p hp hp] at hx'
    have key : ∀ g : B' →ₐ[R] B' ⊗[R] B',
        (RingHom.ker p).map g ≤ I.map (algebraMap R (B' ⊗[R] B')) := by
      intro g
      rw [show RingHom.ker p = RingHom.ker (p : B' →+* B) from rfl, hker,
        Ideal.map_le_iff_le_comap]
      show I.map (algebraMap R B') ≤ _
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
      exact Ideal.mem_map_of_mem _ hr
    exact sup_le (key _) (key _) hx'

end Equalizer

section Descent

universe u

open CategoryTheory

variable {A' B' C' A B E : Type u} [CommRing A'] [CommRing B'] [CommRing C'] [CommRing A]
  [CommRing B] [CommRing E]
  [Algebra A' A] [Algebra A' B'] [Algebra A' B] [Algebra A B] [Algebra B' B]
  [IsScalarTower A' A B] [IsScalarTower A' B' B]
  [Algebra B' C'] [Algebra A' C'] [IsScalarTower A' B' C']

/-- The map `ker (A' → A) → ker (B' → B)` induced by `A' → B'` over a commutative square. -/
def kerRestrict : RingHom.ker (algebraMap A' A) →ₗ[A'] RingHom.ker (algebraMap B' B) where
  toFun x := ⟨algebraMap A' B' x, by
    rw [RingHom.mem_ker, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A' A B,
      show algebraMap A' A x = 0 from x.2, map_zero]⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (by simp [Algebra.smul_def])

omit [Algebra B' C'] [Algebra A' C'] [IsScalarTower A' B' C'] in
/-- The underlying element of `kerRestrict x` in `B'` is the image of `x` under `A' → B'`. -/
@[simp] theorem kerRestrict_apply (x : RingHom.ker (algebraMap A' A)) :
    ((kerRestrict (B' := B') (B := B) x : RingHom.ker (algebraMap B' B)) : B') =
      algebraMap A' B' x :=
  rfl

/-- **Deformation of an étale descent datum across a square-zero thickening.**  Let `A' ⊆ B'`
map onto `A` with nilpotent kernel `I`, let `B' → B` be surjective with kernel `J`, of square
zero, over the commutative square `A' → A → B`, `A' → B' → B`, with `A → B` étale and surjective
on spectra.  Let `C'` be a formally smooth `B'`-algebra with a second homomorphism
`σ : B' → C'` of `A'`-algebras, and suppose that `C' → E` reduces `C'` to the pushout
`E = B ⊗_A B`, carrying the two maps `B' → C'` to the two coprojections composed with `B' → B`,
with kernel in `J C'`.  If `J = I ⊗_{A'} B'`, then `A' → B'` is étale and surjective on spectra
and `C' = B' ⊗_{A'} B'`. -/
theorem etale_and_bijective_lift_of_isBaseChange [Algebra.Etale A B]
    (hinj : Function.Injective (algebraMap A' B'))
    (hA : Function.Surjective (algebraMap A' A)) (hB : Function.Surjective (algebraMap B' B))
    (hJ : RingHom.ker (algebraMap B' B) ^ 2 = ⊥)
    (hspec : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)))
    (hbc : IsBaseChange B' (kerRestrict (A' := A') (A := A) (B' := B') (B := B)))
    [Algebra.FormallySmooth B' C'] (σ : B' →ₐ[A'] C')
    (jR : C' →+* E) (f₁ f₂ : B →+* E)
    (hpo : IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom f₁) (CommRingCat.ofHom f₂))
    (h₁ : ∀ b, jR (algebraMap B' C' b) = f₁ (algebraMap B' B b))
    (h₂ : ∀ b, jR (σ b) = f₂ (algebraMap B' B b))
    (hjR : RingHom.ker jR ≤ (RingHom.ker (algebraMap B' B)).map (algebraMap B' C')) :
    Algebra.Etale A' B' ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap A' B')) ∧
      Function.Bijective
        (Algebra.TensorProduct.lift (Algebra.ofId B' C') σ fun _ _ ↦ Commute.all _ _) := by
  classical
  set I := RingHom.ker (algebraMap A' A)
  set J := RingHom.ker (algebraMap B' B)
  have hIJ : ∀ x ∈ I, algebraMap A' B' x ∈ J := fun x hx ↦ (kerRestrict ⟨x, hx⟩).2
  have hI : I ^ 2 = ⊥ := sq_eq_bot_of_injective_of_map_mem hinj hIJ hJ
  have hInil : IsNilpotent I := ⟨2, by rw [hI, Ideal.zero_eq_bot]⟩
  have het : Algebra.Etale A' B' :=
    Algebra.Etale.of_ker_sq_eq_bot_of_isBaseChange hA hB hI kerRestrict (fun _ ↦ rfl) hbc
  refine ⟨het, ?_, ?_⟩
  · -- surjectivity on spectra
    intro P
    have hP : P ∈ PrimeSpectrum.zeroLocus (I : Set A') := by
      intro x hx
      obtain ⟨n, hn⟩ : IsNilpotent x := by
        refine ⟨2, ?_⟩
        have : x ^ 2 ∈ I ^ 2 := Ideal.pow_mem_pow hx 2
        rwa [hI, Ideal.mem_bot] at this
      exact P.isPrime.mem_of_pow_mem n (hn ▸ P.asIdeal.zero_mem)
    rw [← range_comap_of_surjective _ _ hA] at hP
    obtain ⟨Q, rfl⟩ := hP
    obtain ⟨Q', rfl⟩ := hspec Q
    refine ⟨PrimeSpectrum.comap (algebraMap B' B) Q', ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  · -- the tensor square
    have hJI : J = I.map (algebraMap A' B') := by
      refine le_antisymm (fun j hj ↦ ?_) (Ideal.map_le_iff_le_comap.2 fun x hx ↦ hIJ x hx)
      refine hbc.inductionOn (⟨j, hj⟩ : J)
        (motive := fun y : J ↦ (y : B') ∈ I.map (algebraMap A' B'))
        (fun m ↦ Ideal.mem_map_of_mem _ m.2) (fun b y hy ↦ ?_) (fun y z hy hz ↦ ?_)
      · exact Ideal.mul_mem_left _ b hy
      · exact add_mem hy hz
    let iso := (CommRingCat.isPushout_tensorProduct A B B).isoIsPushout _ _ hpo
    let ψr : C' →+* B ⊗[A] B := iso.inv.hom.comp jR
    have hψ₁ : ∀ b, ψr (algebraMap B' C' b) = algebraMap B' B b ⊗ₜ 1 := by
      intro b
      show iso.inv.hom (jR _) = _
      rw [h₁]
      exact congrArg (fun φ : CommRingCat.of B ⟶ CommRingCat.of (B ⊗[A] B) ↦ φ.hom
        (algebraMap B' B b))
        (IsPushout.inl_isoIsPushout_inv _ _ (CommRingCat.isPushout_tensorProduct A B B) hpo)
    have hψ₂ : ∀ b, ψr (σ b) = 1 ⊗ₜ algebraMap B' B b := by
      intro b
      show iso.inv.hom (jR _) = _
      rw [h₂]
      exact congrArg (fun φ : CommRingCat.of B ⟶ CommRingCat.of (B ⊗[A] B) ↦ φ.hom
        (algebraMap B' B b))
        (IsPushout.inr_isoIsPushout_inv _ _ (CommRingCat.isPushout_tensorProduct A B B) hpo)
    let ψ : C' →ₐ[A'] B ⊗[A] B :=
      { ψr with
        commutes' := fun a ↦ by
          show ψr (algebraMap A' C' a) = _
          rw [IsScalarTower.algebraMap_apply A' B' C', hψ₁, ← IsScalarTower.algebraMap_apply,
            Algebra.TensorProduct.algebraMap_apply] }
    have hψker : RingHom.ker (ψ : C' →+* B ⊗[A] B) ≤ I.map (algebraMap A' C') := by
      intro x hx
      have : jR x = 0 := by
        have hx' : iso.inv.hom (jR x) = 0 := hx
        have := congrArg iso.hom.hom hx'
        rwa [← CommRingCat.comp_apply, iso.inv_hom_id, CommRingCat.id_apply, map_zero] at this
      have h := hjR this
      rwa [hJI, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
    exact bijective_lift_of_isNilpotent hA hInil (IsScalarTower.toAlgHom A' B' B) hB
      (by rw [← hJI]; rfl) σ ψ hψker hψ₁ hψ₂

end Descent
