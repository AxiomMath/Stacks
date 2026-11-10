module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.Localization.Finiteness
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituation
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Depth.ShortExact
public import StacksFrontier.RingTheory.Module.FiniteFromAdicReduction

/-!
# The cokernel of a generator map in a bootstrap situation

Let `S` be a bootstrap situation with ring `A`, ideal `I` and finite module `M`, and let
`f₁, …, f_r` generate `I^m`. The proof of [Stacks, Tag 0EIE] uses the cokernel `Q` of the map
`M → M^{⊕ r}`, `x ↦ (f₁x, …, f_rx)`, and observes that `A, I, T, Q` again satisfy the
assumptions of the situation. This file proves that observation.

Both depth assumptions of the situation concern primes outside the adic locus. At such a prime
some `f_j` becomes a unit, and the maps `Q → M^{⊕ (r - 1)}`, `[y] ↦ (f_j yᵢ - fᵢ y_j)_{i ≠ j}`,
and `M^{⊕ (r - 1)} → Q`, extension by zero, compose in both orders to multiplication by `f_j`.
Localizing, and also localizing, completing and localizing again, preserves composition,
sums and multiplication by ring elements, so in both settings the transformed `Q` is isomorphic
to the transformed `M^{⊕ (r - 1)}`, which is a finite power of the transformed `M`; and over a
Noetherian ring the depth of a finite power of a finite module is at least the depth of that
module (Stacks 00LX applied to split short exact sequences).

## Main definitions

* `Stacks.Algebraization.generatorMap` — the map `x ↦ (f₁x, …, f_rx)`.
* `Stacks.Algebraization.BootstrapSituation.cokernel` — the bootstrap situation with module
  `Q = M^{⊕ r}/M`.

## Main results

* `Stacks.Algebraization.depth_localizedModule_le_cokernel` and
  `Stacks.Algebraization.depth_completedLocal_le_cokernel` — the depth of `Q`, after
  localization, respectively after localization, completion and localization, is at least that
  of `M`.
* `Stacks.Algebraization.depth_le_depth_pi` — over a Noetherian ring, a finite power of a finite
  module has depth at least that of the module.

## References

* [Stacks Project, Tag 0EIE](https://stacks.math.columbia.edu/tag/0EIE)
* [Stacks Project, Tag 0EFU](https://stacks.math.columbia.edu/tag/0EFU)
* [Stacks Project, Tag 00LX](https://stacks.math.columbia.edu/tag/00LX)
-/

@[expose] public section

open IsLocalRing

universe u v w

namespace Stacks.Algebraization

/-- The map `M → M^{⊕ r}`, `x ↦ (f₁x, …, f_rx)`, attached to a family `f` of ring elements. -/
def generatorMap {A : Type*} (M : Type*) [CommRing A] [AddCommGroup M] [Module A M] {r : ℕ}
    (f : Fin r → A) : M →ₗ[A] (Fin r → M) :=
  LinearMap.pi fun j => f j • LinearMap.id

/-- The `i`-th coordinate of the generator map is multiplication by `fᵢ`. -/
theorem generatorMap_apply {A : Type*} {M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    {r : ℕ} (f : Fin r → A) (x : M) (i : Fin r) : generatorMap M f x i = f i • x := rfl

section Generic

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] {r : ℕ}
  (f : Fin r → A) (j : Fin r)

/-- The map `M^{⊕ r} / M → M^{⊕ (r - 1)}`, `y ↦ (f_j yᵢ - fᵢ y_j)_{i ≠ j}`; up to
multiplication by `f_j` it inverts `cokernelOfPi`. -/
noncomputable def cokernelToPi :
    ((Fin r → M) ⧸ LinearMap.range (generatorMap M f)) →ₗ[A] ({i // i ≠ j} → M) :=
  (LinearMap.range (generatorMap M f)).liftQ
    (LinearMap.pi fun i => f j • LinearMap.proj (i : Fin r) - f i • LinearMap.proj j)
    (by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker]
      funext i
      simp [generatorMap_apply, smul_smul, mul_comm])

/-- Extension by zero in the `j`-th coordinate, `M^{⊕ (r - 1)} → M^{⊕ r}`. -/
noncomputable def piExtendAt (A : Type*) [CommRing A] [Module A M] (j : Fin r) :
    ({i // i ≠ j} → M) →ₗ[A] (Fin r → M) :=
  LinearMap.pi fun i => if h : i = j then 0 else LinearMap.proj (⟨i, h⟩ : {i // i ≠ j})

/-- The map `M^{⊕ (r - 1)} → M^{⊕ r} / M`, extension by zero followed by the quotient map. -/
noncomputable def cokernelOfPi :
    ({i // i ≠ j} → M) →ₗ[A] ((Fin r → M) ⧸ LinearMap.range (generatorMap M f)) :=
  (LinearMap.range (generatorMap M f)).mkQ ∘ₗ piExtendAt A j

/-- Extension by zero vanishes in the `j`-th coordinate. -/
theorem piExtendAt_apply_self (z : {i // i ≠ j} → M) : piExtendAt A j z j = 0 := by
  simp [piExtendAt]

/-- Extension by zero is the identity away from the `j`-th coordinate. -/
theorem piExtendAt_apply_ne (z : {i // i ≠ j} → M) {i : Fin r} (h : i ≠ j) :
    piExtendAt A j z i = z ⟨i, h⟩ := by
  simp [piExtendAt, h]

/-- `cokernelToPi ∘ cokernelOfPi` is multiplication by `f_j`. -/
theorem cokernelToPi_comp_cokernelOfPi :
    cokernelToPi (M := M) f j ∘ₗ cokernelOfPi f j = f j • LinearMap.id := by
  refine LinearMap.ext fun z => funext fun i => ?_
  simp [cokernelToPi, cokernelOfPi, piExtendAt_apply_self (A := A),
    piExtendAt_apply_ne (A := A) j z i.2]

/-- `cokernelOfPi ∘ cokernelToPi` is multiplication by `f_j`. -/
theorem cokernelOfPi_comp_cokernelToPi :
    cokernelOfPi (M := M) f j ∘ₗ cokernelToPi f j = f j • LinearMap.id := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.smul_apply,
    LinearMap.id_apply, cokernelToPi, Submodule.liftQ_apply, cokernelOfPi]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  refine ⟨-(y j), ?_⟩
  funext i
  by_cases hi : i = j
  · subst hi
    simp [generatorMap_apply, piExtendAt_apply_self (A := A)]
  · simp [generatorMap_apply, piExtendAt_apply_ne (A := A) j _ hi]

end Generic

section DepthTransfer

/-- A module with a finite family of maps to and from `W` satisfying the identities of a direct
sum decomposition is isomorphic to the product `ι → W`. -/
noncomputable def linearEquivPiOfDecomposition {R : Type*} [CommRing R] {Z W : Type*}
    [AddCommGroup Z] [Module R Z] [AddCommGroup W] [Module R W] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → W →ₗ[R] Z) (p : ι → Z →ₗ[R] W)
    (hps : ∀ i k, p i ∘ₗ s k = if i = k then LinearMap.id else 0)
    (hsum : ∑ i, s i ∘ₗ p i = LinearMap.id) : Z ≃ₗ[R] (ι → W) :=
  LinearEquiv.ofLinearMap (LinearMap.pi p) (∑ i, s i ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.ext fun w => funext fun k => ?_
      change p k ((∑ i, s i ∘ₗ LinearMap.proj i) w) = w k
      rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single k]
      · exact (LinearMap.congr_fun (hps k k) (w k)).trans (by simp)
      · intro i _ hik
        exact (LinearMap.congr_fun (hps k i) (w i)).trans (by simp [Ne.symm hik])
      · intro hk
        exact absurd (Finset.mem_univ k) hk)
    (by
      refine LinearMap.ext fun z => ?_
      simpa using LinearMap.congr_fun hsum z)

/-- Over a Noetherian ring the depth of a finite module is at most that of a finite power of
it, by induction along the split short exact sequences `0 → W → W × W^n → W^n → 0` and
Stacks 00LX. -/
theorem depth_le_depth_pi {R : Type*} [CommRing R] [IsNoetherianRing R] (J : Ideal R)
    (W : Type*) [AddCommGroup W] [Module R W] [Module.Finite R W] (ι : Type*) [Finite ι] :
    Module.depth R J W ≤ Module.depth R J (ι → W) := by
  have := Fintype.ofFinite ι
  have hfin : ∀ n : ℕ, Module.depth R J W ≤ Module.depth R J (Fin n → W) := by
    intro n
    induction n with
    | zero =>
        have : Subsingleton (Fin 0 → W) := ⟨fun a b => funext fun i => i.elim0⟩
        exact le_top.trans (Module.depth_eq_top_of_subsingleton J).ge
    | succ n ih =>
        rw [← Module.depth_eq_depth_of_linearEquiv J
          (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => W))]
        exact (le_min le_rfl ih).trans
          (Module.min_depth_le_depth_of_exact J (f := LinearMap.inl R W (Fin n → W))
            (g := LinearMap.snd R W (Fin n → W)) Function.Exact.inl_snd LinearMap.inl_injective
            LinearMap.snd_surjective).1
  rw [Module.depth_eq_depth_of_linearEquiv J
    (LinearEquiv.piCongrLeft' R (fun _ : ι => W) (Fintype.equivFin ι))]
  exact hfin _

/-- **Depth transfer along a quasi-inverse pair.** Let `W` be a finite module over a Noetherian
ring, let `Z` carry the maps of a decomposition `Z ≅ W^ι`, and let `g : Y → Z`, `h : Z → Y`
compose in both orders to multiplication by a unit. Then `depth W ≤ depth Y`. -/
theorem depth_le_depth_of_decomposition {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J : Ideal R) {W Z Y : Type*} [AddCommGroup W] [Module R W] [Module.Finite R W]
    [AddCommGroup Z] [Module R Z] [AddCommGroup Y] [Module R Y] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → W →ₗ[R] Z) (p : ι → Z →ₗ[R] W)
    (hps : ∀ i k, p i ∘ₗ s k = if i = k then LinearMap.id else 0)
    (hsum : ∑ i, s i ∘ₗ p i = LinearMap.id) (g : Y →ₗ[R] Z) (h : Z →ₗ[R] Y) (c : R)
    (hc : IsUnit c) (hgh : ∀ z, g (h z) = c • z) (hhg : ∀ y, h (g y) = c • y) :
    Module.depth R J W ≤ Module.depth R J Y := by
  have hbij : Function.Bijective g := by
    obtain ⟨u, rfl⟩ := hc
    refine ⟨fun y₁ y₂ hy => ?_, fun z => ⟨((u⁻¹ : Rˣ) : R) • h z, ?_⟩⟩
    · exact u.isUnit.smul_left_cancel.1 ((hhg y₁).symm.trans ((congrArg h hy).trans (hhg y₂)))
    · rw [map_smul, hgh, smul_smul, u.inv_mul, one_smul]
  rw [Module.depth_eq_depth_of_linearEquiv J (LinearEquiv.ofBijective g hbij),
    Module.depth_eq_depth_of_linearEquiv J (linearEquivPiOfDecomposition s p hps hsum)]
  exact depth_le_depth_pi J W ι

/-- The coordinate projections and injections of `ι → M` satisfy the identities of a direct sum
decomposition. -/
theorem proj_comp_single {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [DecidableEq ι] (i k : ι) :
    (LinearMap.proj i : (ι → M) →ₗ[R] M) ∘ₗ LinearMap.single R (fun _ : ι => M) k =
      if i = k then LinearMap.id else 0 := by
  refine LinearMap.ext fun x => ?_
  by_cases hik : i = k
  · subst hik
    simp
  · simp [hik]

/-- The sum of the coordinate idempotents of `ι → M` is the identity. -/
theorem sum_single_comp_proj {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∑ i, LinearMap.single R (fun _ : ι => M) i ∘ₗ (LinearMap.proj i : (ι → M) →ₗ[R] M) =
      LinearMap.id := by
  refine LinearMap.ext fun x => funext fun k => ?_
  simp [Finset.sum_apply, Pi.single_apply]

end DepthTransfer

section Localization

variable {R : Type*} [CommRing R] (S : Submonoid R) {X Y Z : Type*} [AddCommGroup X]
  [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]

/-- Localization of linear maps preserves composition. -/
theorem localizedModule_map_comp (g : Y →ₗ[R] Z) (h : X →ₗ[R] Y) :
    LocalizedModule.map S (g ∘ₗ h) = LocalizedModule.map S g ∘ₗ LocalizedModule.map S h := by
  refine LinearMap.ext fun x => ?_
  induction x using LocalizedModule.induction_on with
  | h x s => simp

/-- Localization sends multiplication by `a` to multiplication by its image. -/
theorem localizedModule_map_smul_id_apply (a : R) (x : LocalizedModule S X) :
    LocalizedModule.map S (a • LinearMap.id) x = algebraMap R (Localization S) a • x := by
  rw [map_smul, LocalizedModule.map_id, LinearMap.smul_apply, LinearMap.id_apply,
    algebraMap_smul]

end Localization


section CokernelDepth

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] {r : ℕ}

/-- If the elements `f₁, …, f_r` generate `I^m` and a prime `P` of an `A`-algebra `B` does not
contain the extension of `I`, then the image of some `f_j` lies outside `P`. -/
theorem exists_generator_not_mem {B : Type*} [CommRing B] (φ : A →+* B) {I : Ideal A}
    {f : Fin r → A} {m : ℕ} (hf : Ideal.span (Set.range f) = I ^ m) (P : Ideal B) [P.IsPrime]
    (hP : ¬ I.map φ ≤ P) : ∃ j, φ (f j) ∉ P := by
  by_contra! h
  refine hP (Ideal.IsPrime.le_of_pow_le (n := m) ?_)
  rw [← Ideal.map_pow, ← hf, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact h j

/-- **Depth of the localized cokernel.** If `f_j ∉ P`, the localization at `P` of
`M^{⊕ r}/M` has depth at least that of `M_P`: up to the unit `f_j` it is isomorphic to
`(M_P)^{⊕ (r - 1)}`. -/
theorem depth_localizedModule_le_cokernel [IsNoetherianRing A] [Module.Finite A M]
    (f : Fin r → A) (P : Ideal A) [P.IsPrime] (j : Fin r) (hj : f j ∉ P) :
    Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl M) ≤
      Module.depth (Localization.AtPrime P) (maximalIdeal (Localization.AtPrime P))
        (LocalizedModule P.primeCompl ((Fin r → M) ⧸ LinearMap.range (generatorMap M f))) := by
  refine depth_le_depth_of_decomposition _
    (fun i => LocalizedModule.map P.primeCompl (LinearMap.single A (fun _ : {i // i ≠ j} => M) i))
    (fun i => LocalizedModule.map P.primeCompl (LinearMap.proj i))
    (fun i k => ?_) ?_
    (LocalizedModule.map P.primeCompl (cokernelToPi f j))
    (LocalizedModule.map P.primeCompl (cokernelOfPi f j))
    (algebraMap A (Localization.AtPrime P) (f j))
    (IsLocalization.map_units _ (⟨f j, hj⟩ : P.primeCompl)) (fun z => ?_) (fun y => ?_)
  · rw [← localizedModule_map_comp, proj_comp_single]
    split_ifs <;> simp
  · simp_rw [← localizedModule_map_comp]
    rw [← map_sum, sum_single_comp_proj, LocalizedModule.map_id]
  · rw [← LinearMap.comp_apply, ← localizedModule_map_comp, cokernelToPi_comp_cokernelOfPi,
      localizedModule_map_smul_id_apply]
  · rw [← LinearMap.comp_apply, ← localizedModule_map_comp, cokernelOfPi_comp_cokernelToPi,
      localizedModule_map_smul_id_apply]

end CokernelDepth

section CompletedDepth

variable {A : Type*} [CommRing A] (q : Ideal A) [q.IsPrime] (I : Ideal A)
  (p' : Ideal (AdicCompletion (I.map (algebraMap A (Localization.AtPrime q)))
    (Localization.AtPrime q))) [p'.IsPrime]

/-- The map induced by `g : X → Y` on `((X_q)^∧)_{p'}`: localize at `q`, complete along the
extension of `I`, localize at `p'`. -/
noncomputable def completedLocalMap {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y]
    [Module A Y] (g : X →ₗ[A] Y) :
    LocalizedModule p'.primeCompl
        (AdicCompletion (I.map (algebraMap A (Localization.AtPrime q)))
          (LocalizedModule q.primeCompl X)) →ₗ[Localization.AtPrime p']
      LocalizedModule p'.primeCompl
        (AdicCompletion (I.map (algebraMap A (Localization.AtPrime q)))
          (LocalizedModule q.primeCompl Y)) :=
  LocalizedModule.map p'.primeCompl
    (AdicCompletion.map (I.map (algebraMap A (Localization.AtPrime q)))
      (LocalizedModule.map q.primeCompl g))

variable {X Y Z : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
  [AddCommGroup Z] [Module A Z]

/-- `completedLocalMap` preserves composition. -/
theorem completedLocalMap_comp (g : Y →ₗ[A] Z) (h : X →ₗ[A] Y) :
    completedLocalMap q I p' (g ∘ₗ h) =
      completedLocalMap q I p' g ∘ₗ completedLocalMap q I p' h := by
  unfold completedLocalMap
  rw [localizedModule_map_comp, ← AdicCompletion.map_comp, localizedModule_map_comp]

/-- `completedLocalMap` preserves identities. -/
theorem completedLocalMap_id :
    completedLocalMap q I p' (LinearMap.id : X →ₗ[A] X) = LinearMap.id := by
  unfold completedLocalMap
  rw [LocalizedModule.map_id, AdicCompletion.map_id, LocalizedModule.map_id]

/-- `completedLocalMap` is additive. -/
theorem completedLocalMap_sum {ι : Type*} (s : Finset ι) (g : ι → X →ₗ[A] Y) :
    completedLocalMap q I p' (∑ i ∈ s, g i) = ∑ i ∈ s, completedLocalMap q I p' (g i) := by
  unfold completedLocalMap
  rw [map_sum, map_sum, map_sum]

/-- `completedLocalMap` sends the zero map to zero. -/
theorem completedLocalMap_zero : completedLocalMap q I p' (0 : X →ₗ[A] Y) = 0 := by
  unfold completedLocalMap
  rw [map_zero, map_zero, map_zero]

/-- `completedLocalMap` sends multiplication by `a` to multiplication by the image of `a`. -/
theorem completedLocalMap_smul_id_apply (a : A) (x : LocalizedModule p'.primeCompl
    (AdicCompletion (I.map (algebraMap A (Localization.AtPrime q)))
      (LocalizedModule q.primeCompl X))) :
    completedLocalMap q I p' (a • LinearMap.id) x =
      algebraMap (AdicCompletion (I.map (algebraMap A (Localization.AtPrime q)))
          (Localization.AtPrime q)) (Localization.AtPrime p')
        (algebraMap (Localization.AtPrime q) (AdicCompletion
          (I.map (algebraMap A (Localization.AtPrime q))) (Localization.AtPrime q))
          (algebraMap A (Localization.AtPrime q) a)) • x := by
  have h1 : LocalizedModule.map q.primeCompl (a • LinearMap.id : X →ₗ[A] X) =
      algebraMap A (Localization.AtPrime q) a • LinearMap.id :=
    LinearMap.ext fun y => localizedModule_map_smul_id_apply _ _ y
  have h2 : AdicCompletion.map (I.map (algebraMap A (Localization.AtPrime q)))
      (algebraMap A (Localization.AtPrime q) a • LinearMap.id :
        LocalizedModule q.primeCompl X →ₗ[Localization.AtPrime q] _) =
      algebraMap (Localization.AtPrime q) (AdicCompletion
          (I.map (algebraMap A (Localization.AtPrime q))) (Localization.AtPrime q))
          (algebraMap A (Localization.AtPrime q) a) • LinearMap.id := by
    rw [map_smul, AdicCompletion.map_id]
    exact LinearMap.ext fun y => by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, algebraMap_smul]
      exact (algebraMap_smul (Localization.AtPrime q) a y).symm
  unfold completedLocalMap
  rw [h1, h2, localizedModule_map_smul_id_apply]

/-- **Depth of the completed localized cokernel.** If the image of `f_j` lies outside `p'`,
the module `((Q_q)^∧)_{p'}` attached to `Q = M^{⊕ r}/M` has depth at least that of
`((M_q)^∧)_{p'}`. -/
theorem depth_completedLocal_le_cokernel [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] {r : ℕ} (f : Fin r → A)
    (j : Fin r)
    (hj : algebraMap (Localization.AtPrime q) (AdicCompletion
      (I.map (algebraMap A (Localization.AtPrime q))) (Localization.AtPrime q))
      (algebraMap A (Localization.AtPrime q) (f j)) ∉ p') :
    Module.depth (Localization.AtPrime p') (maximalIdeal (Localization.AtPrime p'))
        (LocalizedModule p'.primeCompl
          (AdicCompletion (I.map (algebraMap A (Localization.AtPrime q)))
            (LocalizedModule q.primeCompl M))) ≤
      Module.depth (Localization.AtPrime p') (maximalIdeal (Localization.AtPrime p'))
        (LocalizedModule p'.primeCompl
          (AdicCompletion (I.map (algebraMap A (Localization.AtPrime q)))
            (LocalizedModule q.primeCompl
              ((Fin r → M) ⧸ LinearMap.range (generatorMap M f))))) := by
  have : Module.Finite (AdicCompletion (I.map (algebraMap A (Localization.AtPrime q)))
      (Localization.AtPrime q)) (AdicCompletion (I.map (algebraMap A (Localization.AtPrime q)))
        (LocalizedModule q.primeCompl M)) :=
    Module.Finite.adicCompletion_of_finite_quotient_smul_top (Ideal.fg_of_isNoetherianRing _) _
      inferInstance
  refine depth_le_depth_of_decomposition _
    (fun i => completedLocalMap q I p' (LinearMap.single A (fun _ : {i // i ≠ j} => M) i))
    (fun i => completedLocalMap q I p' (LinearMap.proj i))
    (fun i k => ?_) ?_
    (completedLocalMap q I p' (cokernelToPi f j))
    (completedLocalMap q I p' (cokernelOfPi f j))
    _ (IsLocalization.map_units _ (⟨_, hj⟩ : p'.primeCompl)) (fun z => ?_) (fun y => ?_)
  · rw [← completedLocalMap_comp, proj_comp_single]
    split_ifs
    · exact completedLocalMap_id q I p'
    · exact completedLocalMap_zero q I p'
  · simp_rw [← completedLocalMap_comp]
    rw [← completedLocalMap_sum, sum_single_comp_proj, completedLocalMap_id]
  · rw [← LinearMap.comp_apply, ← completedLocalMap_comp, cokernelToPi_comp_cokernelOfPi,
      completedLocalMap_smul_id_apply]
  · rw [← LinearMap.comp_apply, ← completedLocalMap_comp, cokernelOfPi_comp_cokernelToPi,
      completedLocalMap_smul_id_apply]

end CompletedDepth

/-! ### The cokernel situation -/

/-- **The cokernel of a generator map is again a bootstrap situation.** Let `f₁, …, f_r`
generate `I^m`. The finite module `Q = M^{⊕ r}/M`, the cokernel of `x ↦ (f₁x, …, f_rx)`, together
with the ring, ideal, locus, bounds and dualizing complex of `S`, satisfies the assumptions of
the bootstrap situation: away from `V(I)` some `f_j` is a unit and `Q` becomes isomorphic to
`M^{⊕ (r - 1)}`, which has depth at least that of `M`, after localization as well as after
completion of a localization at a point of `T`. This is the observation made in the proof of
Stacks Tag 0EIE. -/
def BootstrapSituation.cokernel (S : BootstrapSituation.{u, v, w}) {r : ℕ} (f : Fin r → S.A)
    (m : ℕ) (hf : Ideal.span (Set.range f) = S.I ^ m) : BootstrapSituation.{u, v, w} where
  A := S.A
  commRing := S.commRing
  isNoetherianRing := S.isNoetherianRing
  I := S.I
  M := (Fin r → S.M) ⧸ LinearMap.range (generatorMap S.M f)
  addCommGroup := inferInstance
  module := inferInstance
  finite := inferInstance
  T := S.T
  subset_adicLocus := S.subset_adicLocus
  stableUnderSpecialization := S.stableUnderSpecialization
  s := S.s
  d := S.d
  dualizing := S.dualizing
  cohomologicalDimension_le := S.cohomologicalDimension_le
  depth_or_depth_add_dimension := by
    intro p r' q hpr hrq hp hr hrT hq
    obtain ⟨j, hj⟩ := exists_generator_not_mem (RingHom.id S.A) hf p.asIdeal (by
      rw [Ideal.map_id]
      exact fun h => hp h)
    have hle := depth_localizedModule_le_cokernel (M := S.M) f p.asIdeal j hj
    rcases S.depth_or_depth_add_dimension p r' q hpr hrq hp hr hrT hq with h | h
    · exact Or.inl (le_trans h (enatToEInt_mono hle))
    · exact Or.inr (lt_of_lt_of_le h (add_le_add_left (enatToEInt_mono hle) _))
  completedLocalDepth := by
    intro q hq
    dsimp only
    intro p' hp' hspec
    obtain ⟨j, hj⟩ := exists_generator_not_mem
      ((algebraMap (Localization.AtPrime q.asIdeal)
        (AdicCompletion (S.I.map (algebraMap S.A (Localization.AtPrime q.asIdeal)))
          (Localization.AtPrime q.asIdeal))).comp
        (algebraMap S.A (Localization.AtPrime q.asIdeal))) hf p'.asIdeal (by
          rw [← Ideal.map_map]
          exact hp')
    have hle := depth_completedLocal_le_cokernel q.asIdeal S.I p'.asIdeal (M := S.M) f j hj
    exact lt_of_lt_of_le (S.completedLocalDepth q hq p' hp' hspec) (enatToEInt_mono hle)

section CokernelProjections

variable (S : BootstrapSituation.{u, v, w}) {r : ℕ} (f : Fin r → S.A) (m : ℕ)
  (hf : Ideal.span (Set.range f) = S.I ^ m)

/-- The ring of the cokernel situation is that of `S`. -/
theorem BootstrapSituation.cokernel_A : (S.cokernel f m hf).A = S.A := rfl

/-- The ideal of the cokernel situation is that of `S`. -/
theorem BootstrapSituation.cokernel_I : (S.cokernel f m hf).I = S.I := rfl

/-- The module of the cokernel situation is `M^{⊕ r}/M`. -/
theorem BootstrapSituation.cokernel_M :
    (S.cokernel f m hf).M = ((Fin r → S.M) ⧸ LinearMap.range (generatorMap S.M f)) := rfl

/-- The locus of the cokernel situation is that of `S`. -/
theorem BootstrapSituation.cokernel_T : (S.cokernel f m hf).T = S.T := rfl

/-- The depth bound of the cokernel situation is that of `S`. -/
theorem BootstrapSituation.cokernel_s : (S.cokernel f m hf).s = S.s := rfl

/-- The dimension bound of the cokernel situation is that of `S`. -/
theorem BootstrapSituation.cokernel_d : (S.cokernel f m hf).d = S.d := rfl

end CokernelProjections

end Stacks.Algebraization

end
