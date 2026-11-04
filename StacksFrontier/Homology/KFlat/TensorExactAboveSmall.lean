module

public import StacksFrontier.Homology.KFlat.TensorExactAbove
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The bounded-tensor criterion tested on modules of the universe of the ring

Let `R : Type u` and let `C` be a cochain complex of flat `R`-modules, its terms in any universe.
Suppose that for every `R`-module `M` *in the universe `u` of `R`* the termwise tensor product
`C ⊗_R M` has no cohomology in degrees `> m`.  Then the same holds for `R`-modules `M` in every
universe.  Consequently `C` is K-flat and every derived extension of scalars is computed on it
termwise (`TotalDerivedExtensionScalars.comparison_isIso_of_isZero_homology_tensorComplex_small`).

## The proof

Fix a degree `k > m` and write `d₁ : C^{k-1} → C^k`, `d₂ : C^k → C^{k+1}`.

* Exactness of `C ⊗ M` at `k` for all `u`-small `M` makes `Im(d₂) ⊗ M → C^{k+1} ⊗ M` injective
  for those `M`, and flatness is detected on modules in the universe of the ring
  (`Module.Flat.iff_lTensor_preserves_injective_linearMap'`), so `Q = C^{k+1} / Im(d₂)` is flat
  (`StacksDraft.TorAmplitude.flat_quotient_of_rTensor_subtype_injective_small`).
* A short exact sequence `0 → I → B → Q → 0` with `Q` flat stays left exact after tensoring with
  *any* module (`StacksDraft.TorAmplitude.rTensor_injective_of_flat_quotient`), by a four-lemma
  chase against a free presentation of the module.
* `M = R` gives exactness of `C` itself at `k`.  With `d₂ = ι ∘ d₂'`, `d₂'` the corestriction onto
  `Im(d₂)` and `ι` its inclusion, right exactness of the tensor product makes
  `C^{k-1} ⊗ M → C^k ⊗ M → Im(d₂) ⊗ M` exact, and `ι ⊗ M` is injective by the previous point.

## Main results

* `StacksDraft.TorAmplitude.rTensor_injective_of_flat_quotient`
* `StacksDraft.TorAmplitude.flat_quotient_of_rTensor_subtype_injective_small`
* `CochainComplex.KFlat.rTensor_exact_of_rTensor_exact_small` — exactness of `C ⊗ M` at `k` for
  every module from that for `u`-small modules.
* `CochainComplex.KFlat.isZero_homology_tensorComplex_of_small` — **the universe reduction**.
* `CochainComplex.KFlat.kFlat_of_isZero_homology_tensorComplex_small` and
  `...TotalDerivedExtensionScalars.comparison_isIso_of_isZero_homology_tensorComplex_small`
  — the K-flatness and the termwise computation of derived extension of scalars, under the
  `u`-small hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w w' wR wA

namespace StacksDraft.TorAmplitude

/-- **Tensoring a short exact sequence with flat cokernel with any module is left exact**: if
`0 → A → B → Q → 0` is exact and `Q` is flat, then `A ⊗ M → B ⊗ M` is injective for every
module `M`.  This is the Tor-free form of `Tor₁(Q, M) = 0`: present `M` as a quotient of the free
module `R^{(M)}` and chase. -/
@[ega "0 6.1.2" "partial",
  ega "0 6.7.4" "partial",
  ega "IV 2.1.8" "(i)",
  sga "1 IV 1.1" "(i)",
  sga "3 III 4.6.4" "more general"]
theorem rTensor_injective_of_flat_quotient {R : Type u} [CommRing R] {A B Q : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup Q] [Module R A] [Module R B] [Module R Q]
    [Module.Flat R Q] {ι : A →ₗ[R] B} {π : B →ₗ[R] Q} (hι : Function.Injective ι)
    (hexact : Function.Exact ι π) (hπ : Function.Surjective π)
    (M : Type*) [AddCommGroup M] [Module R M] :
    Function.Injective (ι.rTensor M) := by
  let p : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have hp : Function.Surjective p := fun x ↦ ⟨Finsupp.single x 1, by simp [p]⟩
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (LinearMap.exact_subtype_ker_map p) hp hexact hπ
    (Module.Flat.rTensor_preserves_injective_linearMap _ (LinearMap.ker p).injective_subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap ι hι)

/-- **A quotient of a flat module is flat as soon as the inclusion stays injective after
tensoring with every module in the universe of the ring.**  Flatness is detected by injective
maps between modules in that universe. -/
theorem flat_quotient_of_rTensor_subtype_injective_small {R : Type u} [CommRing R] {D : Type w}
    [AddCommGroup D] [Module R D] (Z : Submodule R D) [Module.Flat R D]
    (hinj : ∀ (M : Type u) [AddCommGroup M] [Module R M],
      Function.Injective (LinearMap.rTensor M Z.subtype)) :
    Module.Flat R (D ⧸ Z) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap'.{u}]
  intro N N' _ _ _ _ α hα
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (LinearMap.exact_subtype_mkQ Z) (Submodule.mkQ_surjective Z)
    (LinearMap.exact_map_mkQ_range α) (Submodule.mkQ_surjective (LinearMap.range α))
    (hinj (N' ⧸ LinearMap.range α)) (Module.Flat.lTensor_preserves_injective_linearMap α hα)

end StacksDraft.TorAmplitude

namespace CochainComplex.KFlat

variable {R : Type u} [CommRing R]

/-- **Exactness of `C ⊗ M` at a degree, for every module `M`, from exactness for the modules in
the universe of the ring**, for a complex `C` of flat modules.  See the module documentation. -/
theorem rTensor_exact_of_rTensor_exact_small (C : CochainComplex (ModuleCat.{v} R) ℤ)
    [∀ i, Module.Flat R (C.X i)] (k : ℤ)
    (hk : ∀ (M : Type u) [AddCommGroup M] [Module R M],
      Function.Exact (LinearMap.rTensor M (C.d (k - 1) k).hom)
        (LinearMap.rTensor M (C.d k (k + 1)).hom))
    (M : Type w) [AddCommGroup M] [Module R M] :
    Function.Exact (LinearMap.rTensor M (C.d (k - 1) k).hom)
      (LinearMap.rTensor M (C.d k (k + 1)).hom) := by
  set d₁ := (C.d (k - 1) k).hom with hd₁
  set d₂ := (C.d k (k + 1)).hom with hd₂
  have hd : d₂ ∘ₗ d₁ = 0 := by
    rw [hd₁, hd₂, ← ModuleCat.hom_comp, C.d_comp_d, ModuleCat.hom_zero]
  -- `C^{k+1} / Im(d₂)` is flat.
  have hQ : Module.Flat R ((C.X (k + 1) : Type v) ⧸ LinearMap.range d₂) :=
    StacksDraft.TorAmplitude.flat_quotient_of_rTensor_subtype_injective_small
      (LinearMap.range d₂) fun N _ _ ↦
        StacksDraft.TorAmplitude.Termwise.rTensor_range_subtype_injective_of_exact d₁ d₂ hd N
          (hk N)
  -- `C` is exact at `k`.
  have hC : Function.Exact d₁ d₂ :=
    (Function.Exact.iff_of_ladder_linearEquiv (e₁ := TensorProduct.rid R _)
      (e₂ := TensorProduct.rid R _) (e₃ := TensorProduct.rid R _)
      (f₁₂ := LinearMap.rTensor R d₁) (f₂₃ := LinearMap.rTensor R d₂)
      (g₁₂ := d₁) (g₂₃ := d₂)
      (by ext; simp) (by ext; simp)).2 (hk R)
  -- Factor `d₂` through its range.
  let ι := (LinearMap.range d₂).subtype
  let d₂' := d₂.rangeRestrict
  have hfac : ι ∘ₗ d₂' = d₂ := LinearMap.subtype_comp_codRestrict _ _ _
  have hC' : Function.Exact d₁ d₂' := fun y ↦
    (Submodule.coe_eq_zero (x := d₂' y)).symm.trans (hC y)
  have hR : Function.Exact (LinearMap.rTensor M d₁) (LinearMap.rTensor M d₂') :=
    rTensor_exact M hC' d₂.surjective_rangeRestrict
  have hι : Function.Injective (LinearMap.rTensor M ι) :=
    StacksDraft.TorAmplitude.rTensor_injective_of_flat_quotient
      (LinearMap.range d₂).injective_subtype (LinearMap.exact_subtype_mkQ _)
      (Submodule.mkQ_surjective _) M
  have hcomp : LinearMap.rTensor M d₂ = LinearMap.rTensor M ι ∘ₗ LinearMap.rTensor M d₂' := by
    rw [← LinearMap.rTensor_comp, hfac]
  intro y
  rw [hcomp, LinearMap.comp_apply, map_eq_zero_iff _ hι]
  exact hR y

/-- Vanishing of the cohomology of `C ⊗ M` at `k` is exactness of the termwise tensored
differentials around `k`. -/
private theorem isZero_homology_tensorComplex_iff_exact
    (C : CochainComplex (ModuleCat.{v} R) ℤ) (k : ℤ) (M : ModuleCat.{w} R) :
    IsZero ((StacksDraft.TorAmplitude.tensorComplex C M).homology k) ↔
      Function.Exact (LinearMap.rTensor M (C.d (k - 1) k).hom)
        (LinearMap.rTensor M (C.d k (k + 1)).hom) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (k - 1) k (k + 1) (by simp) (by simp),
    ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
  exact Iff.rfl

/-- **The universe reduction of the bounded-tensor criterion.**  Let `C` be a complex of flat
`R`-modules, `R : Type u`, such that for every `R`-module `M` in the universe `u` the termwise
tensor product `C ⊗_R M` has no cohomology in degrees `> m`.  Then `C ⊗_R M` has no cohomology in
degrees `> m` for every `R`-module `M`, in any universe. -/
theorem isZero_homology_tensorComplex_of_small (C : CochainComplex (ModuleCat.{v} R) ℤ)
    [∀ i, Module.Flat R (C.X i)] (m : ℤ)
    (hC : ∀ (M : ModuleCat.{u} R) (k : ℤ), m < k →
      IsZero ((StacksDraft.TorAmplitude.tensorComplex C M).homology k))
    (M : ModuleCat.{w} R) (k : ℤ) (hk : m < k) :
    IsZero ((StacksDraft.TorAmplitude.tensorComplex C M).homology k) := by
  refine (isZero_homology_tensorComplex_iff_exact C k M).2
    (rTensor_exact_of_rTensor_exact_small C k (fun N _ _ ↦ ?_) M)
  exact (isZero_homology_tensorComplex_iff_exact C k (ModuleCat.of R N)).1 (hC _ k hk)

/-- **K-flatness from vanishing of the cohomology of `C ⊗ M` in high degrees, tested on modules
in the universe of the ring.** -/
theorem kFlat_of_isZero_homology_tensorComplex_small
    (C : CochainComplex (ModuleCat.{max u v} R) ℤ) [∀ i, Module.Flat R (C.X i)] (m : ℤ)
    (hC : ∀ (M : ModuleCat.{u} R) (k : ℤ), m < k →
      IsZero ((StacksDraft.TorAmplitude.tensorComplex C M).homology k)) :
    C.KFlat :=
  kFlat_of_isZero_homology_tensorComplex C m fun M k hk ↦
    isZero_homology_tensorComplex_of_small C m hC M k hk

end CochainComplex.KFlat

namespace CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars

/-- **Derived extension of scalars is computed termwise** on a complex `C` of flat `R`-modules
such that, for every `R`-module `M` in the universe of `R`, the termwise tensor product
`C ⊗_R M` has no cohomology in degrees `> m`. -/
theorem comparison_isIso_of_isZero_homology_tensorComplex_small
    {R : Type u} {A : Type w} [CommRing R] [CommRing A] {f : R →+* A}
    [HasDerivedCategory.{wR} (ModuleCat.{max v u w} R)]
    [HasDerivedCategory.{wA} (ModuleCat.{max v u w} A)]
    (D : TotalDerivedExtensionScalars.{u, v, w, wR, wA} f)
    (C : CochainComplex (ModuleCat.{max v u w} R) ℤ) [∀ i, Module.Flat R (C.X i)] (m : ℤ)
    (hC : ∀ (M : ModuleCat.{u} R) (k : ℤ), m < k →
      IsZero ((StacksDraft.TorAmplitude.tensorComplex C M).homology k)) :
    IsIso (D.comparison.app C) :=
  comparison_isIso_of_isZero_homology_tensorComplex D C m fun M k hk ↦
    CochainComplex.KFlat.isZero_homology_tensorComplex_of_small C m hC M k hk

end CochainComplex.DerivedExtensionScalars.TotalDerivedExtensionScalars
