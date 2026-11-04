module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AlternatingAffineIntersections
public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Product
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DerivedSupportInvertsAugmentation
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedFractionMap
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Sections
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A fraction class vanishing on an affine scheme

Let `Y` be an affine scheme, `f₁, …, f_c ∈ Γ(Y, 𝒪_Y)` with `c ≥ 1`, and `ℱ` a quasi-coherent
`𝒪_Y`-module. The class map of [Stacks, Tag 0G7Q] carries a global section `s` of `ℱ` to the class
of the fraction `s / (f₁ ⋯ f_c)` in the cokernel of the last differential of the extended
alternating Čech complex. This file shows that this class vanishes on global sections only if

`(f₁ ⋯ f_c)^n s ∈ (f₁^{n+1}, …, f_c^{n+1}) Γ(Y, ℱ)` for some `n`,

the converse being the easy half of the description of the top local cohomology of [Stacks,
Tag 0G7R]. It also records that global sections are right exact on quasi-coherent modules over an
affine scheme, and that a section over a principal open `D(g)` becomes a global section after
multiplication by a power of `g` ([Stacks, Tag 01P7]).

## Main results

* `Stacks.Perfect.SupportedFraction.exists_app_eq_of_cokernelπ_app_eq_zero`: on an affine
  scheme, a global section of the target of a map of quasi-coherent modules which vanishes in the
  cokernel comes from a global section of the source.
* `Stacks.Perfect.SupportedFraction.exists_prod_pow_smul_mem_of_cokernelπ_fractionHom_eq_zero`:
  the statement above.

## References

* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7R](https://stacks.math.columbia.edu/tag/0G7R)
* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.SupportedFraction

variable {Y : Scheme.{u}}

/-! ### Quasi-coherence of the terms of the extended alternating Čech complex -/

/-- The direct image of the restriction of a quasi-coherent module to a principal intersection is
quasi-coherent. -/
theorem isQuasicoherent_restrictedModule {c : ℕ} (f : Fin c → Γ(Y, ⊤)) (F : Y.Modules)
    [F.IsQuasicoherent] (p : ℕ) (s : CechCochains.OrdIndex (I := Fin c) p) :
    (restrictedModule f F p s).IsQuasicoherent := by
  unfold Stacks.Perfect.ExtendedAlternatingCech.restrictedModule
  rw [Stacks.Perfect.CechDerivedSupport.equationsOpen_eq_basicOpen_prod]
  let j := (Y.basicOpen (∏ k, f (s.1 k))).ι
  have : ((Scheme.Modules.pullback j).obj F).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent
        (Y.basicOpen (∏ k, f (s.1 k))).toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback j).app F) inferInstance
  infer_instance

/-- **The positive-degree terms of the extended alternating Čech complex of a quasi-coherent
module are quasi-coherent.** -/
theorem isQuasicoherent_prodTerm {c : ℕ} (f : Fin c → Γ(Y, ⊤)) (F : Y.Modules)
    [F.IsQuasicoherent] (p : ℕ) : (prodTerm f F p).IsQuasicoherent := by
  let G : ULift.{u} (CechCochains.OrdIndex (I := Fin c) p) → Y.Modules :=
    fun s => restrictedModule f F p s.down
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (Pi.reindex Equiv.ulift (fun s => restrictedModule f F p s))
    (Stacks.AlgebraicGeometry.MeromorphicQuasicoherent.isQuasicoherent_pi G
      fun s => isQuasicoherent_restrictedModule f F p s.down)

/-- **Every term of the extended alternating Čech complex of a quasi-coherent module is
quasi-coherent.** -/
theorem isQuasicoherent_term {c : ℕ} (f : Fin c → Γ(Y, ⊤)) (F : Y.Modules) [F.IsQuasicoherent]
    (n : ℕ) : (term f F n).IsQuasicoherent := by
  cases n with
  | zero => exact inferInstanceAs F.IsQuasicoherent
  | succ p => exact isQuasicoherent_prodTerm f F p

/-! ### Sections over a principal open of an affine scheme -/

section Localization

variable [IsAffine Y] (F : Y.Modules) [F.IsQuasicoherent]

/-- Over an open equal to the principal open of a global function `g` of an affine scheme, every
section of a quasi-coherent module becomes the restriction of a global section after
multiplication by a power of `g`. -/
theorem exists_pow_smul_eq_res {U : Y.Opens} {g : Γ(Y, ⊤)} (hU : U = Y.basicOpen g)
    (a : Γ(F, U)) :
    ∃ (k : ℕ) (m : Γ(F, ⊤)), Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op g ^ k • a =
      F.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op m := by
  subst hU
  let : Module Γ(Y, ⊤) Γ(F, Y.basicOpen g) :=
    Module.compHom Γ(F, Y.basicOpen g) (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom
  have hloc := isLocalizedModule_restriction_basicOpen_of_qcqs F
    (isAffineOpen_top Y).isCompact (isAffineOpen_top Y).isQuasiSeparated g
  obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers g)
    (Scheme.Modules.restrictionLinearMap F (homOfLE (Y.basicOpen_le g))) a
  refine ⟨k, m, ?_⟩
  rwa [← map_pow]

/-- Over an open equal to the principal open of a global function `g` of an affine scheme, a
global section of a quasi-coherent module restricting to zero is killed by a power of `g`. -/
theorem exists_pow_smul_eq_zero_of_res_eq_zero {U : Y.Opens} {g : Γ(Y, ⊤)}
    (hU : U = Y.basicOpen g) {m : Γ(F, ⊤)}
    (hm : F.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op m = 0) : ∃ t : ℕ, g ^ t • m = 0 := by
  subst hU
  let : Module Γ(Y, ⊤) Γ(F, Y.basicOpen g) :=
    Module.compHom Γ(F, Y.basicOpen g) (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom
  have hloc := isLocalizedModule_restriction_basicOpen_of_qcqs F
    (isAffineOpen_top Y).isCompact (isAffineOpen_top Y).isQuasiSeparated g
  obtain ⟨⟨_, t, rfl⟩, ht⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers g)
    (f := Scheme.Modules.restrictionLinearMap F (homOfLE (Y.basicOpen_le g))) (x₁ := m) (x₂ := 0)
    (hm.trans (map_zero _).symm)
  refine ⟨t, ?_⟩
  rwa [smul_zero] at ht

end Localization

/-- Restricting a global scalar multiple of a section is multiplying the restriction by the
restricted scalar. -/
theorem res_smul_res (F : Y.Modules) {W V : Y.Opens} (hWV : W ≤ V) (r : Γ(Y, ⊤))
    (x : Γ(F, V)) :
    F.presheaf.map (homOfLE hWV).op (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op r • x) =
      Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op r • F.presheaf.map (homOfLE hWV).op x := by
  rw [Scheme.Modules.map_smul, ringMap_collapse]

/-- The principal intersection attached to a tuple, over the whole scheme, is the principal open
of the product of the corresponding equations. -/
theorem inter_top_eq_basicOpen {c p : ℕ} (f : Fin c → Γ(Y, ⊤))
    (q : CechCochains.OrdIndex (I := Fin c) p) :
    CechCochains.inter (fun i => (⊤ : Y.Opens) ⊓ Y.basicOpen (f i)) q.1 =
      Y.basicOpen (∏ k, f (q.1 k)) := by
  rw [← Stacks.Perfect.CechDerivedSupport.equationsOpen_eq_basicOpen_prod]
  simp only [CechCochains.inter, top_inf_eq, equationsOpen]

/-! ### Right exactness of global sections on an affine scheme -/

/-- **Global sections are right exact on quasi-coherent modules over an affine scheme.** A global
section of the target of a map of quasi-coherent modules which vanishes in the cokernel is the
image of a global section of the source. -/
@[ega "III 1.2.5" "partial"]
theorem exists_app_eq_of_cokernelπ_app_eq_zero [IsAffine Y] {M N : Y.Modules}
    [hM : M.IsQuasicoherent] [hN : N.IsQuasicoherent] (φ : M ⟶ N) {σ : Γ(N, ⊤)}
    (h : (cokernel.π φ).app ⊤ σ = 0) : ∃ τ : Γ(M, ⊤), φ.app ⊤ τ = σ := by
  have hC : (cokernel φ).IsQuasicoherent :=
    Stacks.Cech.isQuasicoherent_cokernel_of_isQuasicoherent Y φ hM hN
  have hK : (kernel (cokernel.π φ)).IsQuasicoherent :=
    Stacks.Cech.isQuasicoherent_kernel_of_isQuasicoherent Y _ hN hC
  obtain ⟨κ, hκ⟩ := (Stacks.AlgebraicGeometry.QcohLimits.exact_app_kernel (cokernel.π φ) ⊤ σ).1 h
  obtain ⟨τ, hτ⟩ := Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen Y
    (Abelian.factorThruImage φ) ⊤ (isAffineOpen_top Y) κ
  refine ⟨τ, ?_⟩
  have hfac : φ.app ⊤ τ =
      (kernel.ι (cokernel.π φ)).app ⊤ ((Abelian.factorThruImage φ).app ⊤ τ) := by
    conv_lhs => rw [← Abelian.image.fac φ]
    rfl
  rw [hfac]
  exact (congrArg _ hτ).trans hκ

/-! ### Clearing the denominators -/

/-- If `P = f_j q_j` for every `j` and `P^t (P^S s - ∑_j (-1)^j f_j^{S+1} x_j) = 0`, then
`P^{t+S} s ∈ (f_1^{t+S+1}, …, f_n^{t+S+1}) M`. -/
private theorem pow_add_smul_mem_of_pow_smul_sub_sum_eq_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {n : ℕ} (f q : Fin n → R) {P : R} (hP : ∀ j, P = f j * q j)
    {s : M} (x : Fin n → M) {t S : ℕ}
    (ht : P ^ t • (P ^ S • s - ∑ j : Fin n, ((-1 : ℤ) ^ (j : ℕ)) • f j ^ (S + 1) • x j) = 0) :
    P ^ (t + S) • s ∈ (Ideal.span (Set.range fun j => f j ^ (t + S + 1)) • ⊤ : Submodule R M) := by
  rw [smul_sub, sub_eq_zero, ← mul_smul, ← pow_add, Finset.smul_sum] at ht
  rw [ht]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [smul_comm (P ^ t) ((-1 : ℤ) ^ (j : ℕ)), hP j, mul_pow, mul_smul,
    smul_comm (q j ^ t) (f j ^ (S + 1)), ← mul_smul (f j ^ t), ← pow_add,
    show t + (S + 1) = t + S + 1 by omega]
  exact Submodule.smul_of_tower_mem _ _
    (Submodule.smul_mem_smul (Ideal.subset_span ⟨j, rfl⟩) trivial)

/-- If `q^k a` is the restriction of a global section `m` over `V`, `P = r q` and `k ≤ S`, then
`P^{S+1}` times the restriction of `a` to `W ≤ V` is the restriction of `r^{S+1} q^{S+1-k} m`. -/
private theorem pow_succ_smul_res_eq_res (F : Y.Modules) {W V : Y.Opens} (hWV : W ≤ V)
    {P r q : Γ(Y, ⊤)} (hP : P = r * q) {a : Γ(F, V)} {m : Γ(F, ⊤)} {k S : ℕ}
    (hk : Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op q ^ k • a =
      F.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m) (hkS : k ≤ S) :
    Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op P ^ (S + 1) •
        F.presheaf.map (homOfLE hWV).op a =
      F.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (r ^ (S + 1) • q ^ (S + 1 - k) • m) := by
  have e₁ : Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op P ^ (S + 1) =
      Y.presheaf.map (homOfLE hWV).op
        (Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op P ^ (S + 1)) := by
    rw [map_pow, ringMap_collapse]
  have e₂ : Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op q ^ (S + 1) • a =
      Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op q ^ (S + 1 - k) •
        F.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m := by
    rw [← hk, ← mul_smul, ← pow_add, Nat.sub_add_cancel (Nat.le_succ_of_le hkS)]
  have e₃ : Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op P ^ (S + 1) • a =
      F.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (r ^ (S + 1) • q ^ (S + 1 - k) • m) := by
    rw [hP, map_mul, mul_pow, mul_smul, e₂, ← map_pow, ← map_pow,
      ← Scheme.Modules.map_smul, ← Scheme.Modules.map_smul]
  rw [e₁, ← Scheme.Modules.map_smul, e₃, collapse2]

/-- Multiplying the top fraction `s / (f₁ ⋯ f_c)` by `(f₁ ⋯ f_c)^{S+1}` gives the restriction of
`(f₁ ⋯ f_c)^S s`. -/
private theorem prod_pow_succ_smul_fractionCochain_topIndex (F : Y.Modules) {c : ℕ}
    (f : Fin (c + 1) → Γ(Y, ⊤)) (s : Γ(F, ⊤)) (S : ℕ) :
    Y.presheaf.map (homOfLE (le_top : CechCochains.inter
        (fun i => (⊤ : Y.Opens) ⊓ Y.basicOpen (f i)) (topIndex c).1 ≤ ⊤)).op (∏ k, f k) ^ (S + 1) •
        fractionCochain f F c ⊤ s (topIndex c) =
      F.presheaf.map (homOfLE (le_top : CechCochains.inter
        (fun i => (⊤ : Y.Opens) ⊓ Y.basicOpen (f i)) (topIndex c).1 ≤ ⊤)).op
        ((∏ k, f k) ^ S • s) := by
  rw [pow_succ, mul_smul, show Y.presheaf.map (homOfLE (le_top : CechCochains.inter
      (fun i => (⊤ : Y.Opens) ⊓ Y.basicOpen (f i)) (topIndex c).1 ≤ ⊤)).op (∏ k, f k) =
      Y.presheaf.map (homOfLE (le_top : CechCochains.inter
        (fun i => (⊤ : Y.Opens) ⊓ Y.basicOpen (f i)) (topIndex c).1 ≤ ⊤)).op
        (∏ k, f ((topIndex c).1 k)) from rfl,
    prodEquations_smul_fractionCochain f F c ⊤ s (topIndex c), ← map_pow,
    ← Scheme.Modules.map_smul]
  rfl

section Clearing

variable [IsAffine Y] (F : Y.Modules) [F.IsQuasicoherent]

/-- **A single equation.** If the fraction `s / f` is the restriction of a global section `τ`,
then `f^t s = f^{t+1} τ` for some `t`. -/
theorem exists_prod_pow_smul_mem_one (f : Fin 1 → Γ(Y, ⊤)) (s τ : Γ(F, ⊤))
    (hτ : (difZero f F).app ⊤ τ = (fractionHom f F 0).app ⊤ s) :
    ∃ n : ℕ, (∏ j, f j) ^ n • s ∈
      (Ideal.span (Set.range fun j => f j ^ (n + 1)) • ⊤ : Submodule Γ(Y, ⊤) Γ(F, ⊤)) := by
  have h1 := congrArg (fun x => secIso f F 0 ⊤ x (topIndex 0)) hτ
  simp only [secIso_difZero, fractionHom_secIso] at h1
  have h2 := congrArg (fun x => Y.presheaf.map (homOfLE (show
      CechCochains.inter (fun i => (⊤ : Y.Opens) ⊓ Y.basicOpen (f i)) (topIndex 0).1 ≤ ⊤ from
        le_top)).op (∏ k, f ((topIndex 0).1 k)) • x) h1
  simp only [prodEquations_smul_fractionCochain] at h2
  rw [← Scheme.Modules.map_smul] at h2
  have hP : (∏ k, f ((topIndex 0).1 k)) = f 0 := by
    rw [Fin.prod_univ_one]
    rfl
  rw [hP] at h2
  have h3 : F.presheaf.map (homOfLE (le_top : CechCochains.inter
      (fun i => (⊤ : Y.Opens) ⊓ Y.basicOpen (f i)) (topIndex 0).1 ≤ ⊤)).op (f 0 • τ - s) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.2 h2
  obtain ⟨t, ht⟩ := exists_pow_smul_eq_zero_of_res_eq_zero F
    ((inter_top_eq_basicOpen f (topIndex 0)).trans (by rw [hP])) h3
  refine ⟨t, ?_⟩
  have hs : (∏ j, f j) ^ t • s = f 0 ^ (t + 1) • τ := by
    rw [smul_sub, sub_eq_zero] at ht
    rw [Fin.prod_univ_one, pow_succ, mul_smul, ← ht]
  rw [hs]
  exact Submodule.smul_mem_smul (Ideal.subset_span ⟨0, rfl⟩) trivial

/-- **At least two equations.** If the fraction `s / (f₁ ⋯ f_c)` is the image of a global cochain
under the last Čech differential, then `(f₁ ⋯ f_c)^n s ∈ (f₁^{n+1}, …, f_c^{n+1}) Γ(Y, ℱ)` for
some `n`. -/
theorem exists_prod_pow_smul_mem_succ {e : ℕ} (f : Fin (e + 2) → Γ(Y, ⊤)) (s : Γ(F, ⊤))
    (τ : Γ(prodTerm f F e, ⊤))
    (hτ : (difSucc f F e).app ⊤ τ = (fractionHom f F (e + 1)).app ⊤ s) :
    ∃ n : ℕ, (∏ j, f j) ^ n • s ∈
      (Ideal.span (Set.range fun j => f j ^ (n + 1)) • ⊤ : Submodule Γ(Y, ⊤) Γ(F, ⊤)) := by
  classical
  set a := secIso f F e ⊤ τ with ha
  set U : Y.Opens :=
    CechCochains.inter (fun i => (⊤ : Y.Opens) ⊓ Y.basicOpen (f i)) (topIndex (e + 1)).1
  set P : Γ(Y, ⊤) := ∏ k, f k
  set Pj : Fin (e + 2) → Γ(Y, ⊤) := fun j => ∏ k, f (j.succAbove k)
  have hU : U = Y.basicOpen P := inter_top_eq_basicOpen f (topIndex (e + 1))
  have hUj : ∀ j, CechCochains.inter (fun i => (⊤ : Y.Opens) ⊓ Y.basicOpen (f i))
      (faceIndex e j).1 = Y.basicOpen (Pj j) := fun j => inter_top_eq_basicOpen f (faceIndex e j)
  choose k m hkm using fun j => exists_pow_smul_eq_res F (hUj j) (a (faceIndex e j))
  set S : ℕ := ∑ j, k j
  have hkS : ∀ j, k j ≤ S := fun j =>
    Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hPj : ∀ j, P = f j * Pj j := fun j => Fin.prod_univ_succAbove f j
  set w : Fin (e + 2) → Γ(F, ⊤) := fun j => f j ^ (S + 1) • Pj j ^ (S + 1 - k j) • m j
  have hE := congrArg (fun x => secIso f F (e + 1) ⊤ x (topIndex (e + 1))) hτ
  simp only [secIso_difSucc, fractionHom_secIso, ordD_apply] at hE
  rw [← ha] at hE
  have hface : ∀ j : Fin (e + 2),
      Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op P ^ (S + 1) •
          CechCochains.restr (Scheme.Modules.presheaf F)
            (CechCochains.inter_le_omit (fun i => (⊤ : Y.Opens) ⊓ Y.basicOpen (f i))
              (topIndex (e + 1)).1 j)
            (a ⟨(topIndex (e + 1)).1 ∘ j.succAbove,
              CechCochains.strictMono_omit (topIndex (e + 1)).2 j⟩) =
        F.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (w j) := by
    intro j
    have hUUj : U ≤ CechCochains.inter (fun i => (⊤ : Y.Opens) ⊓ Y.basicOpen (f i))
        (faceIndex e j).1 := interTop_le_interFace f ⊤ j
    show Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op P ^ (S + 1) •
        F.presheaf.map (homOfLE hUUj).op (a (faceIndex e j)) = _
    exact pow_succ_smul_res_eq_res F hUUj (hPj j) (hkm j) (hkS j)
  have htop : Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op P ^ (S + 1) •
        fractionCochain f F (e + 1) ⊤ s (topIndex (e + 1)) =
      F.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (P ^ S • s) :=
    prod_pow_succ_smul_fractionCochain_topIndex F f s S
  have hzero : F.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (P ^ S • s - ∑ j : Fin (e + 2), ((-1 : ℤ) ^ (j : ℕ)) • w j) = 0 := by
    have h := congrArg (fun x => Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op P ^ (S + 1) • x) hE
    simp only [Finset.smul_sum, smul_comm _ ((-1 : ℤ) ^ _), hface, htop] at h
    rw [map_sub, map_sum, ← h]
    simp only [map_zsmul, sub_self]
  obtain ⟨t, ht⟩ := exists_pow_smul_eq_zero_of_res_eq_zero F hU hzero
  exact ⟨t + S, pow_add_smul_mem_of_pow_smul_sub_sum_eq_zero f Pj hPj
    (fun j => Pj j ^ (S + 1 - k j) • m j) ht⟩

/-- **A fraction class vanishing on an affine scheme.** Let `Y` be affine, `f₁, …, f_c` global
functions with `c ≥ 1`, `ℱ` quasi-coherent and `s` a global section of `ℱ`. If the class of the
fraction `s / (f₁ ⋯ f_c)` in the cokernel of the last differential of the extended alternating
Čech complex vanishes on global sections, then

`(f₁ ⋯ f_c)^n s ∈ (f₁^{n+1}, …, f_c^{n+1}) Γ(Y, ℱ)` for some `n`. -/
theorem exists_prod_pow_smul_mem_of_cokernelπ_fractionHom_eq_zero {d : ℕ}
    (f : Fin (d + 1) → Γ(Y, ⊤)) (s : Γ(F, ⊤))
    (h : (cokernel.π (lastDif f F)).app ⊤ ((fractionHom f F d).app ⊤ s) = 0) :
    ∃ n : ℕ, (∏ j, f j) ^ n • s ∈
      (Ideal.span (Set.range fun j => f j ^ (n + 1)) • ⊤ : Submodule Γ(Y, ⊤) Γ(F, ⊤)) := by
  have := isQuasicoherent_term f F d
  have := isQuasicoherent_prodTerm f F d
  obtain ⟨τ, hτ⟩ := exists_app_eq_of_cokernelπ_app_eq_zero (lastDif f F) h
  cases d with
  | zero => exact exists_prod_pow_smul_mem_one F f s τ hτ
  | succ e => exact exists_prod_pow_smul_mem_succ F f s τ hτ

end Clearing

end Stacks.Perfect.SupportedFraction

end
