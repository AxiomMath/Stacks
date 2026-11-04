module

public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.CechExact

/-!
# The kernel of the Čech localization of a quotient map

Let `A` be a commutative ring, `f₁, …, f_r ∈ A`, let `M` be an `A`-module and let `J ⊆ A` be an
ideal. The quotient map `q : M ⟶ M/JM` has kernel `J • M`, and the same is true after Čech
localization: the kernel of the induced map `M_{∏ i ∈ s, f i} ⟶ (M/JM)_{∏ i ∈ s, f i}` is `J`
times the localization, and likewise degreewise on the terms of the extended alternating Čech
complex.

## Main results

* `Stacks.LocalCohomology.ker_cechModMap_mkQ`: the kernel of the Čech localization of
  `M ⟶ M/JM` at the index set `s` is `J` times `M_{∏ i ∈ s, f i}`.
* `Stacks.LocalCohomology.ker_cechTermMap_mkQ`: the same statement on the degree-`p` term of the
  extended alternating Čech complex.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
-/

@[expose] public noncomputable section

universe v u

namespace Stacks.LocalCohomology

/-! ### Fractions whose numerator lies in `J • M` -/

section Localization

variable {R : Type*} [CommRing R] {S : Submonoid R} {M : Type*} [AddCommGroup M] [Module R M]

/-- Two fractions with the same denominator add by adding their numerators. -/
theorem mk_add_mk_self (y₁ y₂ : M) (b : S) :
    LocalizedModule.mk (y₁ + y₂) b =
      LocalizedModule.mk y₁ b + LocalizedModule.mk y₂ b := by
  rw [LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]

/-- A fraction whose numerator lies in `J • M` lies in `J` times the localization of `M`. -/
theorem mk_mem_smul_top (J : Ideal R) (y : M) (hy : y ∈ J • (⊤ : Submodule R M)) (b : S) :
    LocalizedModule.mk y b ∈ J • (⊤ : Submodule R (LocalizedModule S M)) := by
  refine Submodule.smul_induction_on hy (fun a ha z _ => ?_) fun y₁ y₂ h₁ h₂ => ?_
  · rw [← LocalizedModule.smul'_mk]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [mk_add_mk_self]
    exact Submodule.add_mem _ h₁ h₂

end Localization

/-! ### `J • ⊤` in a finite direct sum -/

section DirectSum

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι] [Fintype ι]
  {X : ι → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)]

/-- Membership in `J` times the whole of a finite direct sum is a componentwise condition. -/
theorem mem_smul_top_directSum (J : Ideal R) (x : DirectSum ι X) :
    x ∈ J • (⊤ : Submodule R (DirectSum ι X)) ↔
      ∀ t, x t ∈ J • (⊤ : Submodule R (X t)) := by
  refine ⟨fun hx t => ?_, fun hx => ?_⟩
  · exact Submodule.mem_comap.1
      (Submodule.smul_top_le_comap_smul_top J (DirectSum.component R ι X t) hx)
  · rw [← DirectSum.sum_univ_of x]
    refine Submodule.sum_mem _ fun t _ => ?_
    exact Submodule.mem_comap.1
      (Submodule.smul_top_le_comap_smul_top J (DirectSum.lof R ι X t) (hx t))

end DirectSum

/-! ### The kernel of the localized quotient map -/

section Main

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-- The kernel of the Čech localization of the quotient map `M ⟶ M/JM` is `J` times the
localization. -/
theorem ker_cechModMap_mkQ (M : ModuleCat.{max u v} R) (J : Ideal R) (s : Finset (Fin r)) :
    LinearMap.ker (cechModMap f
        (ModuleCat.ofHom (Submodule.mkQ (J • (⊤ : Submodule R M)))) s) =
      J • (⊤ : Submodule R (Cech.cechMod f (M : Type (max u v)) s)) := by
  refine le_antisymm (fun x hx => ?_) ?_
  · induction x using LocalizedModule.induction_on with
    | h m b =>
      rw [LinearMap.mem_ker, cechModMap_mk] at hx
      replace hx : LocalizedModule.mk
          (Submodule.mkQ (J • (⊤ : Submodule R M)) m) b = 0 := hx
      rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hx
      obtain ⟨c, hc⟩ := hx
      have hmem : (c : R) • m ∈ J • (⊤ : Submodule R M) := by
        rw [← Submodule.ker_mkQ (J • (⊤ : Submodule R M)), LinearMap.mem_ker, map_smul]
        simpa [Submonoid.smul_def, smul_smul] using hc
      rw [← LocalizedModule.mk_cancel_common_left c b m, Submonoid.smul_def]
      exact mk_mem_smul_top J _ hmem _
  · rw [Submodule.smul_le]
    intro a ha x _
    rw [LinearMap.mem_ker]
    induction x using LocalizedModule.induction_on with
    | h m b =>
      have h0 : (ModuleCat.ofHom (Submodule.mkQ (J • (⊤ : Submodule R M)))) (a • m) = 0 := by
        show Submodule.mkQ (J • (⊤ : Submodule R M)) (a • m) = 0
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact Submodule.smul_mem_smul ha Submodule.mem_top
      rw [LocalizedModule.smul'_mk, cechModMap_mk, h0, LocalizedModule.zero_mk]

/-- The kernel of the map induced by the quotient map `M ⟶ M/JM` on the degree-`p` term of the
extended alternating Čech complex is `J` times that term. -/
theorem ker_cechTermMap_mkQ (M : ModuleCat.{max u v} R) (J : Ideal R) (p : ℕ) :
    LinearMap.ker (cechTermMap f
        (ModuleCat.ofHom (Submodule.mkQ (J • (⊤ : Submodule R M)))) p) =
      J • (⊤ : Submodule R (Cech.cechTerm f (M : Type (max u v)) p)) := by
  ext x
  simp only [LinearMap.mem_ker, mem_smul_top_directSum, ← ker_cechModMap_mkQ f M J,
    DirectSum.ext_iff]
  refine forall_congr' fun t => ?_
  rw [cechTermMap_apply]
  rfl

end Main

end Stacks.LocalCohomology

end
